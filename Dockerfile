# Multi-stage Dockerfile for Mordor Web Application
# Optimized with better layer caching

# Stage 1: Build environment
FROM ocaml/opam:debian-12-ocaml-5.2 AS builder

# Install system dependencies
USER root
RUN apt-get update && apt-get install -y \
    build-essential \
    pkg-config \
    libgmp-dev \
    libffi-dev \
    libev-dev \
    libssl-dev \
    python3 \
    python3-pip \
    z3 libz3-dev \
    curl \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Switch to opam user
USER opam
WORKDIR /home/opam

# Copy only dependency files first for better caching
COPY --chown=opam:opam dune-project ./
COPY --chown=opam:opam *.opam ./

# Generate opam files if needed
RUN opam exec -- dune build || true

# Update opam and install dependencies (this layer will be cached)
RUN opam update && \
    opam install -y . --deps-only --with-test && \
    opam install -y dream yojson

# Now copy the source code (changes here won't invalidate dependency cache)
COPY --chown=opam:opam . .

# Build the project
RUN eval $(opam env) && \
    dune build @install --profile=release && \
    dune install --prefix=/home/opam/install

# Stage 2: Runtime environment
FROM debian:12-slim

# Install runtime dependencies only
RUN apt-get update && apt-get install -y \
    libgmp10 \
    libffi8 \
    libev4 \
    z3 libz3-dev \
    curl \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Create app user
RUN useradd -m -s /bin/bash mordor

# Copy built executable from builder
COPY --from=builder /home/opam/install/bin/mordor-web /usr/local/bin/mordor-web

# Make sure it's executable
RUN chmod +x /usr/local/bin/mordor-web

# Switch to app user
USER mordor
WORKDIR /home/mordor

# Expose port
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/health || exit 1

# Run the web server
CMD ["mordor-web"]

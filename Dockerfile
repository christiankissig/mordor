# Multi-stage Dockerfile for Mordor Web Application
# Fixed to ensure Z3 version consistency

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
    curl \
    ca-certificates \
    cmake \
    git \
    && rm -rf /var/lib/apt/lists/*

# Build Z3 from source to ensure version compatibility
WORKDIR /tmp
RUN git clone --depth 1 --branch z3-4.13.0 https://github.com/Z3Prover/z3.git && \
    cd z3 && \
    python3 scripts/mk_make.py --prefix=/usr/local && \
    cd build && \
    make -j$(nproc) && \
    make install && \
    ldconfig && \
    cd / && \
    rm -rf /tmp/z3

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

# Fix Landmarks stubs library
RUN eval $(opam env) && \
    LANDMARKS_DIR=$(opam var lib)/landmarks && \
    if [ -d "$LANDMARKS_DIR" ] && [ -f "$LANDMARKS_DIR/liblandmark_stubs.a" ]; then \
        cd "$LANDMARKS_DIR" && \
        ar x liblandmark_stubs.a && \
        ocamlmklib -o landmark_stubs *.o && \
        cp dlllandmark_stubs.so $(ocamlc -where)/stublibs/ && \
        rm *.o && \
        echo "Successfully fixed landmarks stubs library"; \
    fi

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
    curl \
    ca-certificates \
    python3 \
    && rm -rf /var/lib/apt/lists/*

# Copy Z3 libraries from builder stage
COPY --from=builder /usr/local/lib/libz3.so* /usr/local/lib/
COPY --from=builder /usr/local/bin/z3 /usr/local/bin/z3

# Update library cache
RUN ldconfig

# Create app user
RUN useradd -m -s /bin/bash mordor

# Copy built executable from builder
COPY --from=builder /home/opam/install/bin/mordor-web /usr/local/bin/mordor-web

# Copy frontend files from builder
COPY --from=builder --chown=mordor:mordor /home/opam/web/frontend /home/mordor/web/frontend

# Make sure executable is executable
RUN chmod +x /usr/local/bin/mordor-web

COPY --chown=mordor litmus-tests/ /home/mordor/litmus-tests/
RUN mkdir -p /home/mordor/_build/default/cli/
COPY --from=builder --chown=mordor /home/opam/install/bin/mordor \
  /home/mordor/_build/default/cli/main.exe

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

# Docker Deployment Guide for Mordor Web

## Quick Start

### Option 1: Using Docker Compose (Recommended)

```bash
# Build and start the container
docker-compose up -d

# View logs
docker-compose logs -f

# Stop the container
docker-compose down
```

The application will be available at http://localhost:8080

### Option 2: Using Docker directly

```bash
# Build the image
docker build -t mordor-web .

# Run the container
docker run -d -p 8080:8080 --name mordor-web mordor-web

# View logs
docker logs -f mordor-web

# Stop the container
docker stop mordor-web
docker rm mordor-web
```

## What the Dockerfile Does

### Multi-Stage Build

**Stage 1: Builder**
- Uses `ocaml/opam:debian-12-ocaml-5.2` base image
- Installs system dependencies (GMP, Z3, etc.)
- Installs OCaml dependencies via opam
- Builds the Mordor web application with `dune`

**Stage 2: Runtime**
- Uses minimal `debian:12-slim` base image
- Only includes runtime dependencies
- Copies the built executable from builder stage
- Results in a much smaller final image (~300MB vs ~2GB)

### Security Features

- Runs as non-root user (`mordor`)
- Minimal runtime dependencies
- Health check endpoint configured

## Configuration

### Environment Variables

You can configure the application with environment variables:

```yaml
# In docker-compose.yml
environment:
  - OCAMLRUNPARAM=b  # Backtrace on errors
  # Add more as needed
```

### Port Mapping

Change the exposed port in `docker-compose.yml`:

```yaml
ports:
  - "3000:8080"  # Maps host port 3000 to container port 8080
```

### Resource Limits

Adjust CPU and memory limits in `docker-compose.yml`:

```yaml
deploy:
  resources:
    limits:
      cpus: '4'      # Maximum 4 CPUs
      memory: 4G     # Maximum 4GB RAM
```

## Building for Production

### Optimized Build

```bash
# Build with BuildKit for better caching
DOCKER_BUILDKIT=1 docker build -t mordor-web:prod .

# Or with docker-compose
COMPOSE_DOCKER_CLI_BUILD=1 DOCKER_BUILDKIT=1 docker-compose build
```

### Multi-Architecture Build

Build for multiple platforms (e.g., for ARM servers):

```bash
# Create a builder
docker buildx create --name mybuilder --use

# Build for multiple platforms
docker buildx build --platform linux/amd64,linux/arm64 \
  -t yourusername/mordor-web:latest \
  --push .
```

## Deployment Scenarios

### Local Development

```bash
# Build and run locally
docker-compose up

# Rebuild after code changes
docker-compose up --build
```

### Production Deployment

```bash
# Build production image
docker build -t mordor-web:1.0.0 .

# Tag for registry
docker tag mordor-web:1.0.0 registry.example.com/mordor-web:1.0.0

# Push to registry
docker push registry.example.com/mordor-web:1.0.0

# Deploy on production server
docker pull registry.example.com/mordor-web:1.0.0
docker run -d -p 8080:8080 \
  --restart unless-stopped \
  --name mordor-web \
  registry.example.com/mordor-web:1.0.0
```

### Using Docker Swarm

```yaml
# docker-stack.yml
version: '3.8'
services:
  mordor-web:
    image: mordor-web:latest
    ports:
      - "8080:8080"
    deploy:
      replicas: 3
      update_config:
        parallelism: 1
        delay: 10s
      restart_policy:
        condition: on-failure
```

```bash
# Deploy stack
docker stack deploy -c docker-stack.yml mordor
```

### Using Kubernetes

Create a Kubernetes deployment:

```yaml
# k8s-deployment.yml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: mordor-web
spec:
  replicas: 3
  selector:
    matchLabels:
      app: mordor-web
  template:
    metadata:
      labels:
        app: mordor-web
    spec:
      containers:
      - name: mordor-web
        image: mordor-web:latest
        ports:
        - containerPort: 8080
        resources:
          limits:
            memory: "2Gi"
            cpu: "2"
          requests:
            memory: "512Mi"
            cpu: "500m"
---
apiVersion: v1
kind: Service
metadata:
  name: mordor-web
spec:
  selector:
    app: mordor-web
  ports:
  - port: 80
    targetPort: 8080
  type: LoadBalancer
```

```bash
kubectl apply -f k8s-deployment.yml
```

## Monitoring

### Check Health

```bash
# Using curl
curl http://localhost:8080/health

# Using docker
docker exec mordor-web curl -f http://localhost:8080/health
```

### View Logs

```bash
# Follow logs
docker-compose logs -f

# Last 100 lines
docker-compose logs --tail=100

# Specific service logs
docker logs -f mordor-web
```

### Check Resource Usage

```bash
# Container stats
docker stats mordor-web

# Detailed inspection
docker inspect mordor-web
```

## Troubleshooting

### Container Won't Start

```bash
# Check logs
docker-compose logs mordor-web

# Interactive debugging
docker run -it --rm mordor-web /bin/bash
```

### Build Failures

```bash
# Clean build (no cache)
docker-compose build --no-cache

# Check build logs
docker build --progress=plain -t mordor-web .
```

### Memory Issues

If the application needs more memory:

```yaml
# Increase limits in docker-compose.yml
deploy:
  resources:
    limits:
      memory: 4G
```

### Port Already in Use

```bash
# Find what's using port 8080
lsof -i :8080

# Use a different port
docker run -p 3000:8080 mordor-web
```

## Optimizations

### Reduce Image Size

The multi-stage build already reduces size significantly. For even smaller images:

1. Use Alpine Linux base (requires more work with dependencies)
2. Strip debug symbols from executables
3. Use `dune build --profile=release`

### Improve Build Speed

1. **Layer caching**: Copy opam files before source code
2. **BuildKit**: Use `DOCKER_BUILDKIT=1`
3. **Local cache**: Mount opam cache volume

```yaml
# docker-compose.yml
volumes:
  - opam-cache:/home/opam/.opam

volumes:
  opam-cache:
```

### Security Hardening

```dockerfile
# Add to Dockerfile
RUN apt-get update && apt-get install -y \
    curl \  # For healthcheck
    ca-certificates  # For HTTPS

# Read-only filesystem
docker run --read-only --tmpfs /tmp mordor-web
```

## Backup and Persistence

If you add data persistence later:

```yaml
# docker-compose.yml
volumes:
  - ./data:/home/mordor/data
  - mordor-cache:/home/mordor/.cache

volumes:
  mordor-cache:
```

## CI/CD Integration

### GitHub Actions

```yaml
# .github/workflows/docker.yml
name: Build Docker Image

on:
  push:
    branches: [ main ]
    tags: [ 'v*' ]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Build image
        run: docker build -t mordor-web .
      - name: Test
        run: |
          docker run -d -p 8080:8080 --name test mordor-web
          sleep 5
          curl -f http://localhost:8080/health
```

### GitLab CI

```yaml
# .gitlab-ci.yml
build:
  image: docker:latest
  services:
    - docker:dind
  script:
    - docker build -t $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA .
    - docker push $CI_REGISTRY_IMAGE:$CI_COMMIT_SHORT_SHA
```

## Questions?

- **Q: How do I update the application?**  
  A: Rebuild the image (`docker-compose build`) and restart (`docker-compose up -d`)

- **Q: Can I run multiple instances?**  
  A: Yes! Use `docker-compose up --scale mordor-web=3`

- **Q: How do I access logs?**  
  A: `docker-compose logs -f` or `docker logs -f mordor-web`

- **Q: What's the image size?**  
  A: ~300MB for the final image (thanks to multi-stage build)

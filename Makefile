# Makefile for Mordor Docker Operations

.PHONY: help build run stop logs clean restart shell health test demo

# Default target
help:
	@echo "Mordor Docker Commands:"
	@echo "  make build     - Build the Docker image"
	@echo "  make run       - Start the container"
	@echo "  make stop      - Stop the container"
	@echo "  make restart   - Restart the container"
	@echo "  make logs      - Follow container logs"
	@echo "  make shell     - Open a shell in the container"
	@echo "  make health    - Check health endpoint"
	@echo "  make test      - Run a quick test"
	@echo "  make clean     - Remove container and image"
	@echo "  make demo      - Record the web-UI demo (GIF + MP4)"
	@echo ""
	@echo "Docker Compose Commands:"
	@echo "  make up        - Start with docker-compose"
	@echo "  make down      - Stop docker-compose"
	@echo "  make rebuild   - Rebuild and restart"

# Build the Docker image
build:
	@echo "🔨 Building Mordor Web image..."
	DOCKER_BUILDKIT=1 docker build -t mordor-web:latest .
	@echo "✅ Build complete!"

# Run the container
run: build
	@echo "🚀 Starting Mordor Web..."
	docker run -d \
		--name mordor-web \
		-p 8080:8080 \
		--restart unless-stopped \
		mordor-web:latest
	@echo "✅ Mordor Web is running at http://localhost:8080"

# Stop the container
stop:
	@echo "⏹️  Stopping Mordor Web..."
	docker stop mordor-web || true
	docker rm mordor-web || true
	@echo "✅ Stopped"

# Restart the container
restart: stop run

# Follow logs
logs:
	docker logs -f mordor-web

# Open a shell in the running container
shell:
	docker exec -it mordor-web /bin/bash

# Check health
health:
	@curl -f http://localhost:8080/health && echo "\n✅ Healthy" || echo "\n❌ Unhealthy"

# Run a quick test
test: run
	@echo "🧪 Testing Mordor Web..."
	@sleep 3
	@curl -f http://localhost:8080/health && echo "✅ Health check passed" || echo "❌ Health check failed"
	@echo "🌐 Open http://localhost:8080 in your browser to test the UI"

# Clean up
clean: stop
	@echo "🧹 Cleaning up..."
	docker rmi mordor-web:latest || true
	@echo "✅ Cleaned"

# Docker Compose targets
up:
	@echo "🚀 Starting with docker-compose..."
	docker-compose up -d
	@echo "✅ Running at http://localhost:8080"

down:
	@echo "⏹️  Stopping docker-compose..."
	docker-compose down

rebuild:
	@echo "🔨 Rebuilding with docker-compose..."
	docker-compose up -d --build

# Development targets
dev:
	@echo "🔧 Starting in development mode..."
	dune exec mordor-web

dev-build:
	@echo "🔨 Building locally..."
	dune build

# Record the web-UI demo (GIF + MP4 in demo/out/); see demo/README.md
demo:
	@test -d demo/node_modules || (cd demo && npm install)
	node demo/demo.mjs

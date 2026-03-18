#!/usr/bin/env bash
# build.sh — Build the Mordor virtual appliance (mordor-appliance.ova)
#
# Prerequisites:
#   - Packer >= 1.9  (https://developer.hashicorp.com/packer/install)
#   - VirtualBox     (https://www.virtualbox.org/wiki/Downloads)
#   - Docker (on the machine running THIS script, to build the image)
#
# Usage:
#   chmod +x build.sh && ./build.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

IMAGE_NAME="mordor-web"
IMAGE_TAR="mordor-web.tar.gz"

echo "==> Step 1: Build Docker image"
docker build -t "$IMAGE_NAME" .

echo "==> Step 2: Export Docker image to tarball"
docker save "$IMAGE_NAME" | gzip > "$IMAGE_TAR"
echo "    Written: $IMAGE_TAR ($(du -sh "$IMAGE_TAR" | cut -f1))"

echo "==> Step 3: Fetch real Debian ISO checksum"
SHA256SUMS=$(curl -fsSL https://cdimage.debian.org/debian-cd/current/amd64/iso-cd/SHA256SUMS)
echo "    Available ISOs:"
echo "$SHA256SUMS" | grep netinst || true

# Match any netinst ISO for amd64
ISO_LINE=$(echo "$SHA256SUMS" | grep "netinst.iso$" | head -1)
ISO_FILE=$(echo "$ISO_LINE" | awk '{print $2}' | sed 's|^\./||')
CHECKSUM=$(echo "$ISO_LINE" | awk '{print $1}')

if [ -z "$CHECKSUM" ]; then
  echo "ERROR: Could not parse Debian ISO checksum. Raw SHA256SUMS output:"
  echo "$SHA256SUMS"
  exit 1
fi

echo "    ISO file: $ISO_FILE"
echo "    Checksum: sha256:$CHECKSUM"

# Derive the full ISO URL from the filename
ISO_URL="https://cdimage.debian.org/debian-cd/current/amd64/iso-cd/${ISO_FILE}"
echo "    ISO URL:  $ISO_URL"

echo "==> Step 4: Initialise Packer plugins"
packer init mordor.pkr.hcl

echo "==> Step 5: Build OVA"
PACKER_LOG=1 PACKER_LOG_PATH=packer.log packer build \
  -var "debian_iso_url=${ISO_URL}" \
  -var "debian_iso_checksum=sha256:${CHECKSUM}" \
  -var "mordor_image_tar=./$IMAGE_TAR" \
  mordor.pkr.hcl

echo ""
echo "==> Done! Appliance written to: mordor-appliance.ova"
echo "    Customers can import this into VirtualBox via:"
echo "    File > Import Appliance > mordor-appliance.ova"
echo "    Then start the VM — the app will be at http://localhost:8080"

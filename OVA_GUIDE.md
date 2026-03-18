# Mordor Web — Virtual Appliance Build Guide

This document covers how to build and distribute the Mordor Web application as a
VirtualBox `.ova` virtual appliance, and how end users can import and run it.

---

## Overview

The build process:
1. Compiles the Mordor Docker image from the project `Dockerfile`
2. Exports it as a tarball
3. Uses [Packer](https://developer.hashicorp.com/packer) to provision a minimal 
   Debian 12 VM, install Docker, load the image, and configure it to start 
   automatically on boot
4. Packages the result as a single `mordor-appliance.ova` file ready for 
   distribution

---

## Prerequisites (Build Machine)

| Tool | Version | Install |
|------|---------|---------|
| Docker | 20.10+ | https://docs.docker.com/get-docker/ |
| Packer | 1.9+ | https://developer.hashicorp.com/packer/install |
| VirtualBox | 7.0+ | https://www.virtualbox.org/wiki/Downloads |
| bash | Any | Pre-installed on macOS/Linux |

> **Windows users:** run the build inside WSL2 with Docker Desktop and
> VirtualBox installed on the host.

---

## File Layout

Place these files in the root of your project alongside the `Dockerfile`:

```
mordor/
├── Dockerfile
├── build_ova.sh          ← entry point
├── mordor.pkr.hcl        ← Packer build definition
├── mordor-web.service    ← systemd unit for the container
├── preseed.cfg           ← unattended Debian installer config

---

## Building the Appliance

```bash
chmod +x build_ova.sh
./build_ova.sh
```

Or, if you prefer to invoke bash explicitly:

```bash
bash build_ova.sh
```

The script will:

1. Build the Docker image from the local `Dockerfile`
2. Export it to `mordor-web.tar.gz`
3. Fetch the current Debian 12 ISO checksum automatically
4. Initialise Packer plugins (`packer init`)
5. Run the full Packer build — this typically takes **10–20 minutes** depending 
   on your internet connection and machine speed
6. Write the finished appliance to **`mordor-appliance.ova`**

### Build Variables

You can override defaults without editing the HCL file:

```bash
packer build \
  -var "memory_mb=4096" \
  -var "cpus=4" \
  -var "vm_name=mordor-v1.0" \
  mordor.pkr.hcl
```

| Variable | Default | Description |
|----------|---------|-------------|
| `vm_name` | `mordor-appliance` | VM name and output filename |
| `disk_size_mb` | `20480` | Virtual disk size in MB |
| `memory_mb` | `2048` | RAM allocated to the VM |
| `cpus` | `2` | vCPU count |
| `ssh_username` | `mordor` | VM user (used by Packer during provisioning) |
| `ssh_password` | `mordor` | VM password |

---

## Distributing the Appliance

Ship the single `mordor-appliance.ova` file to your customers. No other files
are required.

---

## End User: Importing into VirtualBox

1. Download and install [VirtualBox](https://www.virtualbox.org/wiki/Downloads)
2. Open VirtualBox and go to **File → Import Appliance**
3. Select `mordor-appliance.ova` and click **Next**
4. Review the VM settings (RAM, CPUs) and adjust if needed, then click **Finish**
5. Once imported, select the VM and click **Start**
6. Wait ~30 seconds for the VM to boot and the application to start
7. Open a browser and navigate to **http://localhost:8080**

> The application starts automatically on boot and will restart if it crashes.
> No login or manual steps are required.

### Port Forwarding

The OVA is pre-configured with the following NAT port forwards:

| Host port | Guest port | Purpose |
|-----------|------------|---------|
| `8080` | `8080` | Mordor Web UI |

If port `8080` is already in use on your machine, change it in VirtualBox under
**Settings → Network → Advanced → Port Forwarding** before starting the VM.

The SSH port is chosen by Packer, and Packer will set up a matching port
forwarding.

---

## Troubleshooting

**App not reachable at localhost:8080**
- Wait a bit longer — Docker image load on first boot can take 20–30 seconds
- Check the VM has fully booted (you should see a login prompt in the VirtualBox 
  console)
- Verify port forwarding is configured as above


**Restart the application**
```bash
sudo systemctl restart mordor-web
```

**ISO checksum error during build** 
The `build_ova.sh` script fetches the checksum live, but if the Debian mirror is 
temporarily unavailable, you can supply it manually: 

```bash 
CHECKSUM=$(curl -fsSL \
https://cdimage.debian.org/debian-cd/current/amd64/iso-cd/SHA256SUMS \
| grep "debian-12.*-amd64-netinst.iso$" \
| awk '{print $1}') packer build -var
"debian_iso_checksum=sha256:$CHECKSUM" mordor.pkr.hcl 
```

---

## Security Notes

- The default VM password is `mordor` — advise customers to change it after first login (`passwd`)
- The application runs as the unprivileged `mordor` user inside the container

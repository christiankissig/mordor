packer {
  required_plugins {
    virtualbox = {
      source  = "github.com/hashicorp/virtualbox"
      version = "~> 1"
    }
  }
}

variable "vm_name" { default = "mordor-appliance" }
variable "disk_size_mb" { default = 20480 }
variable "memory_mb" { default = 10240 }
variable "cpus" { default = 2 }
variable "ssh_username" { default = "mordor" }
variable "ssh_password" { default = "mordor" }
variable "debian_iso_url" { default = "" }
variable "debian_iso_checksum" { default = "" }
variable "mordor_image_tar" { default = "./mordor-web.tar.gz" }

source "virtualbox-iso" "mordor" {
  vm_name       = var.vm_name
  guest_os_type = "Debian_64"

  iso_url      = var.debian_iso_url
  iso_checksum = var.debian_iso_checksum

  disk_size            = var.disk_size_mb
  memory               = var.memory_mb
  cpus                 = var.cpus
  headless             = false
  hard_drive_interface = "sata"
  guest_additions_mode = "disable"

  skip_nat_mapping = false

  vboxmanage = [
    ["modifyvm", "{{.Name}}", "--nic1", "nat"],
/*  ["modifyvm", "{{.Name}}", "--nat-pf1", "ssh,tcp,,2222,,22"], # Packer
 *     will choose port */ 
    ["modifyvm", "{{.Name}}", "--nat-pf1", "mordor-web,tcp,,8080,,8080"],
  ]

  # Increase boot_wait — give VirtualBox time to POST and show the GRUB menu
  boot_wait = "25s"

  # Debian 12 netinst uses GRUB. The first entry ("Install") is already
  # highlighted. Press <tab> to get the kernel command line, append our
  # preseed options, then boot.
  boot_command = [
    "<tab><wait2>",
    " auto=true priority=critical",
    " url=http://{{ .HTTPIP }}:{{ .HTTPPort }}/preseed.cfg",
    " hostname=mordor-appliance domain=local",
    " DEBIAN_FRONTEND=noninteractive",
    " <enter><wait>"
  ]

  http_directory = "./http"

  communicator           = "ssh"
  ssh_username           = var.ssh_username
  ssh_password           = var.ssh_password
  ssh_host               = "127.0.0.1"
/* ssh_port               = 2222  # Packer will choose port */
  ssh_wait_timeout       = "45m"   # full netinst takes time
  ssh_handshake_attempts = 200

  shutdown_command = "echo '${var.ssh_password}' | sudo -S shutdown -P now"

  format           = "ovf"
  output_directory = "./output-${var.vm_name}"
}

build {
  name    = "mordor-appliance"
  sources = ["source.virtualbox-iso.mordor"]

  provisioner "file" {
    source      = var.mordor_image_tar
    destination = "/tmp/mordor-web.tar.gz"
  }

  provisioner "file" {
    source      = "./mordor-web.service"
    destination = "/tmp/mordor-web.service"
  }

  provisioner "shell" {
    inline = [
      "echo '${var.ssh_password}' | sudo -S apt-get update -qq",
      "sudo apt-get install -y -qq ca-certificates curl gnupg",
      "sudo install -m 0755 -d /etc/apt/keyrings",
      "curl -fsSL https://download.docker.com/linux/debian/gpg | sudo gpg --dearmor -o /etc/apt/keyrings/docker.gpg",
      "sudo chmod a+r /etc/apt/keyrings/docker.gpg",
      "echo \"deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/debian $(. /etc/os-release && echo $VERSION_CODENAME) stable\" | sudo tee /etc/apt/sources.list.d/docker.list > /dev/null",
      "sudo apt-get update -qq",
      "sudo apt-get install -y -qq docker-ce docker-ce-cli containerd.io",
      "sudo docker load < /tmp/mordor-web.tar.gz",
      "rm /tmp/mordor-web.tar.gz",
      "sudo mv /tmp/mordor-web.service /etc/systemd/system/mordor-web.service",
      "sudo systemctl daemon-reload",
      "sudo systemctl enable mordor-web.service",
      "sudo usermod -aG docker ${var.ssh_username}",
      "sudo apt-get clean",
      "sudo rm -rf /var/lib/apt/lists/*",
    ]
  }

  post-processor "shell-local" {
    inline = [
      "cd ./output-${var.vm_name}",
      "OVF=$(ls *.ovf | head -1)",
      "VMDK=$(ls *.vmdk | head -1)",
      "tar cvf ../${var.vm_name}.ova $OVF $VMDK",
      "echo 'OVA written to ./${var.vm_name}.ova'",
    ]
  }
}

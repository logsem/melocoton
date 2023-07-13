# Artifact

## Prerequisites

Building the artifact requires [Vagrant](https://www.vagrantup.com/)
(installation via the .deb from the website works best) and
[VirtualBox](https://www.virtualbox.org/).

## Customizing

This template support the following extension points:
- [build_artifact.sh](build_artifact.sh): Customize this in the marked
  region to prepare the data that should be put into the artifact.
- [resources/build_artifact.sh](resources/build_artifact.sh):
  Customize this with the code to build the data inside the artifact.

## Steps for building the artifact

1. Run [build_artifact.sh](build_artifact.sh) to create the artifact
   as a .tgz and .zip.
2. Run `vagrant up` to create the virtual machine. Login and password
   are `vagrant`. When editing the `Vagrantfile`, use `vagrant reload
   --provision`. To destroy the virtual machine and remove all traces
   of it, run `vagrant destroy`.
3. After the installation by `vagrant up` finishes, shutdown the
   virtual machine and reboot it to check manually that everything works.
4. Export the VM via the GUI of VirtualBox.

## TODOs

- [ ] Improve the `Vagrantfile` and make it extensible.
- [ ] Make the VM smaller.
- [x] Automatically login the user.
- [x] Somehow ensure that the user does not have to run `eval $(opam env)` in the shell
- [ ] Make autologin more robust (currently, the user is hardcoded to `vagrant`)
- [ ] Create a `Makefile` or something like that?

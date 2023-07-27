# Instructions for setup

## Linux

### Install Frama-C

```bash
# Install opam (OCaml package manager)
sudo apt install opam # or dnf, pacman, etc.

# Or you can download an opam binary, put it in the PATH
# and run it directly (no sudo required)

# Initialize opam (install an OCaml compiler)
opam init --compiler 4.14.1 # may take a while
eval $(opam env)

# Install Frama-C (including dependencies)
opam install frama-c
```

### Install CVC4

```bash
wget http://cvc4.cs.stanford.edu/downloads/builds/{x86_64-linux, win64}-opt/cvc4-1.6-{x86_64-linux, win64}-opt/
mv cvc4-1.6-{x86_64-linux, win64}-opt cvc4
```

### Install Alt-Ergo

```bash
opam install alt-ergo
```

### Install Z3

```bash
wget wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip
unzip z3-4.12.2-x64-glibc-2.31.zip
ln -s z3-4.12.2-x64-glibc-2.31/bin/z3
```

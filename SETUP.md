# Instructions for setup

Make sure your python version is >= 3.11
If you don't have python 3.11 but have conda installed, try:

```bash
conda install -c conda-forge python=3.11 
# then switch the python version and restart shell
```

## Install Frama-C

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

## Install CVC4

```bash
# The string in "{}" should be your platform. There are two options: x86_64-linux and win64.
wget http://cvc4.cs.stanford.edu/downloads/builds/{x86_64-linux,win64}-opt/cvc4-1.6-{x86_64-linux, win64}-opt/
mv cvc4-1.6-{x86_64-linux,win64}-opt cvc4 
# add cvc4 to PATH
```

## Install Alt-Ergo

```bash
opam install alt-ergo
```

## Install Z3

```bash
wget wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip
unzip z3-4.12.2-x64-glibc-2.31.zip
# add "z3-4.12.2-x64-glibc-2.31/bin/z3" to PATH or create a symlink
```

## Tell Why3 about the solvers

```bash
rm -f ~/.why3.conf

why3 config detect
```

## Install python dependencies

```bash
# Ensure python version >= 3.11
pip install -r pipeline/requirements.txt
```

## Build the tree-sitter-c library

```bash
cd pipeline/
git clone https://github.com/tree-sitter/tree-sitter-c.git tree_sitter_lib/vendor/tree-sitter-c
python3 build_parser.py
```

## Set the OpenAI API key

```bash
export OPENAI_API_KEY=<your key>
```

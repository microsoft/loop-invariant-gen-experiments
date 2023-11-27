# Loopy

## Setup

### Without Docker

#### Install Frama-C

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

#### Install CVC4

```bash
wget http://cvc4.cs.stanford.edu/downloads/builds/{x86_64-linux, win64}-opt/cvc4-1.6-{x86_64-linux, win64}-opt/
mv cvc4-1.6-{x86_64-linux, win64}-opt cvc4
```

#### Install Alt-Ergo

```bash
opam install alt-ergo
```

#### Install Z3

```bash
wget wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.2/z3-4.12.2-x64-glibc-2.31.zip
unzip z3-4.12.2-x64-glibc-2.31.zip
ln -s z3-4.12.2-x64-glibc-2.31/bin/z3
```

#### Configure Why3

```bash
rm -f ~/.why3.conf

why3 config detect
```

#### Install python dependencies

```bash
# Ensure python version >= 3.11
pip install pyyaml jinja2 openai tiktoken tree_sitter numpy
```

#### Build the tree-sitter-c library

```bash
git clone https://github.com/tree-sitter/tree-sitter-c.git tree_sitter_lib/vendor/tree-sitter-c
python3 build_parser.py
```

Depending on how you access the LLM, you can follow the steps in the LLM access section below.

### With Docker

You can use `Dockerfile` in `src` to build a docker image and run it.

You can build the docker image by running the following commands starting **from the root of this repository**:
(If you get a permission error, you may need to run the following command with `sudo`)

```bash
cd src/
docker build -t loopy --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) .
```

Once the image is built, you can run it using the following command **from the root of this repository**:
**NOTE: If you don't need to interact with the Azure OpenAI API, skip the -e CLI option**

(If you get a permission error, you may need to run the following command with `sudo`)

```bash
docker run -it --rm \
    --mount type=bind,source="$(pwd)"/data,target=/home/user/data/ \
    --mount type=bind,source="$(pwd)"/config,target=/home/user/config/ \
    --mount type=bind,source="$(pwd)"/experiments,target=/home/user/experiments/ \
    --mount type=bind,source="$(pwd)"/templates,target=/home/user/templates/ \
    --mount type=bind,source="$(pwd)"/logs,target=/home/user/logs/ \
    --user "$(id -u):$(id -g)" \
    -e OPENAI_API_KEY=<API_KEY> \
    loopy /bin/bash
```

You can run the toolchain using the following command:

```bash
python3 main.py --config-file <YAML_config_file> --max-benchmarks <max_benchmarks> [options]
```

Use `python3 main.py --help` to see the list of available options.

### LLM access

If you are using an Azure OpenAI endpoint, you need to set the following environment variables before running the toolchain:

```bash
export OPENAI_API_KEY=<your key>
```

You should now be able to run the toolchain using the following command:

```bash
python3 main.py --config-file <YAML_config_file> --max-benchmarks <max_benchmarks> [options]
```

If you are using a different endpoint, you will have to implement a wrapper class that inherits `Provider` in `llm_api_client.py`.
See the `AzureOpenAI` class for an example.

Currently we support running only the Llama-2 family of models locally.
If you are using an LLM locally on your machine or your servers, you will have to download the model and set the path to the model checkpoints and tokenizer accordingly in `llama_2.py`.

## Contributing

This project welcomes contributions and suggestions. Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide a
CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repositories using our CLA.

## Code of Conduct

This project has adopted the [Microsoft Open Source Code of
Conduct](https://opensource.microsoft.com/codeofconduct/). For more information see the [Code of
Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or contact
[opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

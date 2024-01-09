# Loopy

## Setup

### Clone the repository

```bash
git clone --recursive git@github.com:microsoft/loop-invariant-gen-experiments
```

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
# ARCH is one of {x86_64-linux, win64}
wget http://cvc4.cs.stanford.edu/downloads/builds/{ARCH}-opt/cvc4-1.6-{ARCH}-opt
mv cvc4-1.6-{ARCH}-opt cvc4
# Add cvc4 to your PATH
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
# From src/
pip install -r requirements.txt
```

#### Build the tree-sitter-c library

```bash
cd src/
python3 build_parser.py
```

Depending on how you access the LLM, you can follow the steps in the LLM access section [below](#LLM-access).

### With Docker

You can use `Dockerfile` in `src` to build a docker image and run it.

You can build the docker image by running the following commands starting **from the root of this repository**:
(If you get a permission error, you may need to run the following command with `sudo`)

```bash
cd src/
docker build -t loopy --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) .
```

Once the image is built, you can run it using the following command **from the root of this repository**:
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
    -e OPENAI_API_BASE=<API_ENDPOINT> \
    -e OPENAI_API_VERSION=<API_VERSION> \
    loopy /bin/bash
# If you don't need to interact with the Azure OpenAI API, skip the -e CLI options
```

### LLM access

If you are using an Azure OpenAI endpoint, you need to set the following environment variables before running the toolchain:

```bash
export OPENAI_API_KEY=<your key>
export OPENAI_API_BASE=<your API endpoint>
export OPENAI_API_VERSION=<your API version>
```

You should now be able to run the toolchain using the following command:

```bash
python3 main.py --config-file <YAML_config_file> --max-benchmarks <max_benchmarks> [options]
```

If you are using a different endpoint, you will have to implement a wrapper class that inherits `Provider` in `llm_api_client.py`.
See the `AzureOpenAI` class for an example.

Currently we support running only the Llama-2 family of models locally.
If you are using an LLM locally on your machine or your servers, you will have to download the model and set the path to the model checkpoints and tokenizer accordingly in `llama_2.py`.

## Usage

You can run the toolchain using the following command:

```bash
python3 main.py --config-file <YAML_config_file> --max-benchmarks <max_benchmarks> [options]
```

Use `python3 main.py --help` to see the list of available options.

The YAML configuration file contains the following fields:

```yaml
checker: <checker_name> # only frama-c is supported for now
checker_timeout: <checker_options> # timeout argument for the checker, in seconds
model: <model_name> # the LLM to use (currently gpt-4, gpt-4-32k, gpt-3.5-turbo, codellama-34b-python are supported)
benchmarks: <path_to_benchmarks_file> # this file must contain the list of benchmarks to run, one file path per line
benchmark_features: <features_of_the_benchmarks> # this string should indicate the features of the benchmarks under consideration. 
                                           # For e.g., "one_loop_one_method" describes benchmarks with a single loop and a single method.
                                           # Other possible values are "multiple_methods_no_loops", "arrays_pointers_multiple_loops", "termination_one_loop_one_method".
                                           # (If "termination" is specified, variants will be inferred. If "multiple_methods" is specified, pre-post conditions will be inferred).
debug: <debug_mode> # if true, the toolchain will print debug information
```

See [config/sample_config.yaml](config/sample_config.yaml) for an example of a configuration file.

## Dataset

The dataset of pre-processed benchmarks used in our experiments is available [here](dataset.zip).
This zip file contains benchmarks from all 4 experiments, after removing comments, and converting the assertions to ACSL assertions (for Frama-C).

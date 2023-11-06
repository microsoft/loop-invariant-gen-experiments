# Loopy

## Setup instructions

Easiest way is to pull the docker image from dockerhub and run it.

To do this, you need to have docker installed on your machine. To install docker, follow the instructions [here](https://docs.docker.com/install/).

```bash
docker pull adkamath/loopy:latest
```

You can also use `Dockerfile` in `src` to build a docker image and run it.

You can build the docker image by running the following commands starting **from the root of this repository**:
(If you get a permission error, you may need to run the following command with `sudo`)

```bash
cd src/
docker build -t loopy --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) .
```

Once the image is built, you can run it using the following command **from the root of this repository**:
**NOTE: If you don't need to interact with the OpenAI API, skip the -e CLI option**

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
python3 main.py --config-file <YAML_config_file> --model <model_name> --max-benchmarks <max_benchmarks>
```

Use `python3 main.py --help` to see the list of available options.

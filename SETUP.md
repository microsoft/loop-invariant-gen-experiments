# Instructions for setup

Easiest way is to use `src/Dockerfile` to build a docker image and run it.

To do this, you need to have docker installed on your machine. To install docker, follow the instructions [here](https://docs.docker.com/install/).

Once you have docker installed, you can build the docker image by running the following commands starting **from the root of this repository**:

```bash
cd src/
docker build -t loopy --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) .
```

Once the image is built, you can run it by running the following command **from the root of this repository**:
(If you get a permission error, you may need to run the following command with `sudo`)

```bash
docker run -it \
    --mount type=bind,source="$(pwd)"/data,target=/home/user/data/ \
    --mount type=bind,source="$(pwd)"/config,target=/home/user/config/ \
    --mount type=bind,source="$(pwd)"/experiments,target=/home/user/experiments/ \
    --mount type=bind,source="$(pwd)"/templates,target=/home/user/templates/ \
    --mount type=bind,source="$(pwd)"/logs,target=/home/user/logs/ \
    loopy /bin/bash
```

This will start a bash session inside the docker container. You can run the code by running the following command:

```bash
python3 main.py --checker <checker_name> --config-file <YAML_config_file> --model <model_name> --max-benchmarks <max_benchmarks>
```

Use `python3 main.py --help` to see the list of available options.

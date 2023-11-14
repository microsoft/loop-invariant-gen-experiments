# Loopy

## Setup instructions

Easiest way is to pull the docker image from dockerhub and run it.

To do this, you need to have docker installed on your machine. To install docker, follow the instructions at - [https://docs.docker.com/install/](https://docs.docker.com/install/).

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

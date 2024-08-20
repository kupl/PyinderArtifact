# PyinderArtifact

This repository is for the implementation of Pyinder announced in the paper 
"Towards Effective Static Type-Error Detection for Python" in ASE 2024.

### Prerequisites

We recommend the following environment for running Pyinder:
- **OS**: A Linux System with [Docker](https://docs.docker.com/get-docker/) support
- **Hardware**: x86 CPU; 32GB RAM; 50GB Storage 

Before setting up the environment, please make sure that you have [Docker](https://docs.docker.com/get-docker/) installed.

```bash
docker --version
# Docker version 20.10.13, build a224086
```

### Build Docker Image

Clone the repository:

```
https://github.com/kupl/PyinderArtifact.git
cd PyinderArtifact
```

Then, build the Docker image:

```bash
docker build -t pyinder:1.0 .
```

In this step, [Mypy](https://github.com/python/mypy), [Pytype](https://github.com/google/pytype), and [Pyright](https://github.com/microsoft/pyright) are installed, but [Pyre](https://github.com/facebook/pyre-check) is not installed due to the compatibility issue, such as linking, with Pyinder. 
You can install and run Pyre by following the instructions in the [Install Pyre](#install-pyre).

### Run Docker Container

After building the Docker image, you can run the container:

```bash
# Run docker image
docker run --name pyinder-container --memory-reservation 24G -it pyinder:1.0
```

We recommend setting the memory reservation to 24GB for the container to fully run Pyinder.

### Clone Repo of Benchmarks and Setting Configuration

When you run the container, you can download repositories of benchmarks and set the configuration:

```bash
# Inside the image;
cd ~
cd configuration
python download_repo.py
python setting_config.py
```

It takes about 30 minutes to download the repositories.
If you can see `~/typebugs`, `~/bugsinpy`, and `~/excepy` directories, the download is successful.

### Build Pyinder

You can build Pyinder by following the instructions:

```bash
cd ~
cd Pyinder/source
make
```

Don't worry about the warning messages during the build process.
However, if you see an error message `dune: No such file or directory` when running `make`,
you need to type `eval $(opam config env)` before running `make`.

### Preprocess Benchmarks

It is necessary to preprocess the [homeassistant-core](https://github.com/home-assistant/core) project before running all tools:

```bash
cd ~
python run/change_core_async.py
```

Then, you are ready to run Pyinder and other tools!

### Run Tools

#### Kick the tires

You can run all tools with specific project by `-p <project>` option:

```bash
# It will take about 30 minutes 
# to run all tools with the airflow project.
cd ~
cd run
# Run Pyinder with airflow projects
python pyinder_run.py -p airflow
# Run Mypy with airflow projects
python mypy_run.py -p airflow
# Run Pytype with airflow projects
python pytype_run.py -p airflow
# Run Pyright with airflow projects
python pyright_run.py -p airflow
```

You also run specific version of the project by `-n <number>` option:

```bash
python pyinder_run.py -p airflow -n 3831
# All tools are the same as above.
```

#### Full Evaluation

You can run all tools with all projects by following the instructions:

```bash
cd ~
cd run
python pyinder_run.py
python mypy_run.py
python pytype_run.py
python pyright_run.py
```

- Pyinder: <18 hours
- Mypy: <2 hours
- Pytype: may take more than 3 days...
- Pyright: <4 hours

#### Output

The output of each tool is stored in the `~/result/<each-tool>` directory (e.g., `~/result/pyinder`).

### Postprocess and Understanding the Results

All tools generate other warnings than type errors, so you need to filter out the type errors from the results.

## Install Pyre 
### Build Docker Image

Clone the repository:

```bash
git clone https://github.com/kupl/PyinderArtifact.git
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
docker run --name pyinder-container --memory-reservation 32G -it pyinder:1.0
```

We recommend setting the memory reservation to 32GB for the container to fully run Pyinder on the large projects.

### Clone Benchmarks and Setting Configuration

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
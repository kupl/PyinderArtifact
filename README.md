# PyinderArtifact

This repository is for the implementation of Pyinder announced in the paper 
"Towards Effective Static Type-Error Detection for Python" in ASE 2024.
Our tool, Pyinder, is a static type analysis tool for Python that is built on top of Pyre.

[Towards Effective Static Type-Error Detection for Python](https://drive.google.com/file/d/1t2J4fNyWScao9xwRcORBigKkO8dVJmsB/view?usp=sharing): Accepted Version

## Setup

### Prerequisites

We recommend the following environment for running Pyinder:
- **OS**: A Linux System with [Docker](https://docs.docker.com/get-docker/) support
- **Hardware**: x86 CPU; 64GB RAM; 50GB Storage 

(the minimum RAM requirement has been confirmed to be 32GB)

Before setting up the environment, please make sure that you have [Docker](https://docs.docker.com/get-docker/) installed.

```bash
docker --version
# Docker version 20.10.13, build a224086
```

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

## Evaluation

### Kick the tires

Before running experiments on all projects, first run a simple test to check if the tools are working properly.
We provide a simple test with the [luigi](https://github.com/spotify/luigi) project:

```bash
# It will take about 30 minutes 
# to run all tools with the luigi project.
cd ~
cd run
# Run tools with luigi projects
python pyinder_run.py -p luigi
python mypy_run.py -p luigi
python pytype_run.py -p luigi
python pyright_run.py -p luigi
```

---
<details>
<summary>Click to see the output</summary>

You can see the output of each tool in the console like this:

```bash
# luigi-1836 is analyzed... Finished process in 77.26377391815186 seconds.
# luigi-4 is analyzed... Finished process in 85.76695346832275 seconds.
# luigi-14 is analyzed... Finished process in 74.57044434547424 seconds.
```

The result of each tool is stored in the `~/result/<each-tool>/<luigi-proejct>/result.json` directory (e.g., `~/result/pyinder/luigi-1836/result.json`).
</details>

---
Next, post-process the results to collect the type errors and check the results:

```bash
cd ~
cd run

# Change the result log file to json file
python pyinder_change_json.py
python mypy_change_json.py
python pytype_change_json.py

# Filter out the type errors from the results
python filter_error.py

# Run cloc to check the per kloc results
cd ~
cd eval
python cloc.py
```

---
<details>
<summary>Click to see the output</summary>

When you run `*_change_json.py`, you can see the output that shows the success on luigi projects:

```bash
airflow-3831 is analyzed... Failed
...
luigi-1836 is analyzed... Done!
...
luigi-4 is analyzed... Done!
luigi-14 is analyzed... Done!
...
sympy-44 is analyzed... Failed
```

After running `python filter_error.py`, you can see the filtered results in the `~/result/<each-tool>/<luigi-project>/filter_error.json` directory (e.g., `~/result/pyinder/luigi-1836/filter_error.json`).

The command `python cloc.py` makes the `~/cloc` directory that contains the results of cloc.
</details>

---
Finally, you can see the results by following these steps:

```bash
cd ~
cd eval
python check_alarm.py # show the number of alarms by each tool
python check_correct.py # show the number of detecting type errors by each tool
python check_time.py # show the time taken by each tool
```

---
<details>
<summary>Click to see the output</summary>

> Note: The results can be slightly different from the paper because the tools and [typeshed](https://github.com/python/typeshed) can be updated.

The command `python check_alarm.py` shows the number of alarms by each tool:

```bash
Project             Pyinder   Mypy      Pyre      Pytype    Pyright
airflow-3831        N/A       N/A       N/A       N/A       N/A  
luigi-1836          82        85        N/A       0         144
...
luigi-4             104       117       N/A       0         179
luigi-14            79        75        N/A       0         138
...
sympy-44            N/A       N/A       N/A       N/A       N/A
Total               265       277       0         0         461
Per 1k LOC          6.73      7.04      N/A       0.0       11.71
```

The command `python check_correct.py` shows the number of detecting type errors by each tool:

```bash
Project             Pyinder   Mypy      Pyre      Pytype    Pyright
airflow-3831        E         E         E         E         E
...
luigi-1836          O         O         E         X         O
...
luigi-4             X         X         E         X         X
luigi-14            O         X         E         X         O
...
sympy-44            E         E         E         E         E
Correct             2         1         0         0         2
```

The command `python check_time.py` shows the time taken by each tool:

```bash
Project             Pyinder   Mypy      Pyre      Pytype    Pyright
airflow-3831        N/A       N/A       N/A       N/A       N/A  
...
luigi-1836          77.26     6.64      N/A       27.55     8.8
...
luigi-4             85.77     4.69      N/A       149.27    10.04
luigi-14            74.57     4.21      N/A       546.52    8.55
...
sympy-44            N/A       N/A       N/A       N/A       N/A
Total               237.6     15.54     0         723.34    27.39
Per 1k LOC          6.04      0.39      N/A       18.38     0.7
```
</details>

---
Then, you can see the results in the console or check the csv files in the `~/eval` directory.
- `alarm_result.csv`: the number of alarms by each tool
- `correct_result.csv`: the number of detecting type errors by each tool
- `time_result.csv`: the time taken by each tool

### Full Evaluation

You can run all tools with all projects by following the instructions:

```bash
cd ~
cd run
python pyinder_run.py
python mypy_run.py
python pytype_run.py
python pyright_run.py
```

When we ran full evaluation on our machine (2x Intel(R) Xeon(R) Silver 4214, 128GB), the time was measured as follows:
- Pyinder: about 12 hours
- Mypy: about 2 hours
- Pytype: about 5 days
- Pyright: about 3 hours

Even if you skip specific tools, you can see the results by [following these steps](#postprocess-and-understanding-the-results).

#### Output

The output of each tool is stored in the `~/result/<each-tool>` directory (e.g., `~/result/pyinder/airflow-3831`).

#### Other Options

You can run all tools with specific project by `-p <project>` option:

```bash
python pyinder_run.py -p luigi
# Other tools are the same as above.
```

You also run specific version of the project by `-n <number>` option:

```bash
python pyinder_run.py -p luigi -n 1836
# Other tools are the same as above.
```

### Postprocess and Understanding the Results

All tools generate other warnings than type errors, so you need to filter out the type errors from the results.
At first, you have to change result log file to json file of each tool:

```bash
cd ~
cd run
# Change the result log file to json file
python pyinder_change_json.py
python mypy_change_json.py
python pytype_change_json.py
```

It makes json files named `result_.json` in the `~/result/<each-tool>` directory (e.g., `~/result/pyinder/airflow-3831/result_.json`).
(Pyright does not need to change the result log file.)

Then, you can filter out the type errors from the results:

```bash
cd ~
cd run
python filter_error.py
```

You can see the filtered results in the `~/result/<each-tool>` directory (e.g., `~/result/pyinder/airflow-3831/filter_error.json`).

Before checking the results, you have to run cloc to check the per kloc results:

```bash
cd ~
cd eval
python cloc.py
```

Then, you can see the results by following these steps:

```bash
cd ~
cd eval
python check_alarm.py # show the number of alarms by each tool
python check_correct.py # show the number of detecting type errors by each tool
python check_time.py # show the time taken by each tool
```

The csv files are generated in the `~/eval` directory:
- `alarm_result.csv`: the number of alarms by each tool (Table 2)
- `correct_result.csv`: the number of detecting type errors by each tool (Figure 4)
- `time_result.csv`: the time taken by each tool (Table 2)
> Note : The results can be slightly different from the paper because the tools and [typeshed](https://github.com/python/typeshed) are updated.

Moreover, you can see the venn diagram (Figure 4) of the results by this script:

```bash
# in the eval directory
python draw_venn.py
```

It makes `result_venn.pdf` in the `~/eval` directory, and you can see the venn diagram of the results.

## Install Pyre 

Before you install [Pyre](https://github.com/facebook/pyre-check), make sure not to install Pyinder (because Pyinder is built on the top of Pyre, so it causes linking issues...)

### Installation

You can install Pyre easily:

```bash
pip install pyre-check
```

You can see detailed instructions in officiatl documents ([Installation](https://pyre-check.org/docs/installation/))

### Run Pyre

You can run Pyre in a similar way to the other tools:

```bash
cd ~
cd run
python pyre_run.py
```

### See the Results

You have to do postprocess in a similary way to the other tools:

```bash
cd ~
cd run
python pyre_change_json.py
python filter_error.py
```

Then, you can see the results:

```bash
cd ~
cd eval
python cloc.py
python check_alarm.py
python check_correct.py
python check_time.py
```

## Contact

If you have any questions, please contact us at [wonseok_oh@korea.ac.kr](mailto:wonseok_oh@korea.ac.kr)
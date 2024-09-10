We assume that you have already done the installation steps in the [README.md](./README.md) file.

## Preparing the Environment

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

### Preprocess Benchmarks

It is necessary to preprocess the [homeassistant-core](https://github.com/home-assistant/core) project before running all tools:

```bash
cd ~
python run/change_core_async.py
```

Then, you are ready to run Pyinder and other tools!

## Reproducing the Results

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
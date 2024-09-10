### Structure

```bash
run
├── change_core_async.py      # change the async keyword for old version of core project  
├── filter_error.py           # extract only the type errors from the results
├── mypy_change_json.py       # change the result log file to json file for mypy
├── mypy_run.py               # run mypy with the project
├── pyinder_change_json.py    # change the result log file to json file for Pyinder
├── pyinder_run.py            # run Pyinder with the project
├── pyre_change_json.py       # change the result log file to json file for pyre
├── pyre_run.py               # run pyre with the project
├── pyright_run.py            # run pyright with the project
├── pytype_change_json.py     # change the result log file to json file for pytype
├── pytype_run.py             # run pytype with the project
├── run.sh                    # script to run Pyinder (please use `pyinder_run.py` instead)
├── run_mypy.sh               # script to run mypy (please use `mypy_run.py` instead)
├── run_pyre.sh               # script to run pyre (please use `pyre_run.py` instead)
├── run_pyright.sh            # script to run pyright (please use `pyright_run.py` instead)
└── run_pytype.sh             # script to run pytype (please use `pytype_run.py` instead)
```

### Options

`mypy_run.py`, `pyinder_run.py`, `pyre_run.py`, and `pytype_run.py` have the option **`-p`** or **`--project`**.
The option **`-p`** or **`--project`** denotes the project name to analyze.
| Option | Description |
|:------:|:------------|
| `-p` or `--project` | Set the project name to analyze. |

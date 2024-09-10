### Structure

```bash
configuration
├── bugsinpy_repo.json                  # GitHub repositories and their commit id for bugsinpy
├── config                              # Configuration files for all benchmark projects
│   ├── bugsinpy                        # Configuration files for bugsinpy
│   │   ├── ansible-1
│   │   │   ├── .pyre_configuration     # Configuration file for Pyinder and pyre
│   │   │   ├── mypy.ini                # Configuration file for mypy
│   │   │   ├── pyrightconfig.json      # Configuration file for pyright
│   │   │   └── pytype.cfg              # Configuration file for pytype
│   │   ├── ansible-2
│   │   │   ├── ...
│   │   ├── ...
|   ├── excepy                          # Configuration files for excepy
│   │   ├── ...
│   ├── pyinder                         # Configuration files for Pyinder
│   │   ├── ...
├── download_repo.py                    # The script to download repositories
├── excepy_repo.json                    # GitHub repositories and their commit id for excepy
├── setting_config.py                   # The script to set the configuration for evaluation
└── typebugs_repo.json                  # GitHub repositories and their commit id for typebugs
```

### Options

`download_repo.py` and `setting_config.py` have the option **`--project`**.
The option **`--project`** denotes the project name to analyze.
| Option | Description |
|:------:|:------------|
| `--project` | Set the project name to analyze. |

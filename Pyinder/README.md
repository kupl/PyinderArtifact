### Structure

```bash
Pyinder
├── client
│   ├── pyre.py              # Command line interface for Pyinder
│   ├── ...
├── source
│   ├── analysis             # Analysis module for Pyinder
│   │   ├── ...                
│   ├── ...
│   ├── command
│   │   ├── mineCommand.ml   # Start point of Pyinder
│   │   ├── ...
│   └── ...
├── ...
```

We provide a brief description of the core parts of Pyinder.
`pyre.py` is the command line interface for Pyinder.
`mineCommand.ml` is the start point of Pyinder to run the analysis.
`analysis` contains the analysis module for Pyinder.

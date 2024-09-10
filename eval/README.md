### Structure

```bash
eval
├── check_alarm.py      # show the number of alarms by each tool
├── check_correct.py    # show the number of detecting type errors by each tool
├── check_time.py       # show the time taken by each tool
├── cloc.py             # run cloc to check the per kloc results
└── draw_venn.py        # draw the venn diagram of the results
```

### Options

`check_alarm.py`, `check_correct.py`, and `check_time.py` have the option **`-p`** or **`--project`**.
The option **`-p`** or **`--project`** denotes the project name to analyze.
| Option | Description |
|:------:|:------------|
| `-p` or `--project` | Set the project name to analyze. |

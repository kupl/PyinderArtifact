import json
import argparse
from pathlib import Path
import numpy as np
import pandas as pd

HOME_PATH = Path.home()

target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
    "airflow-14686",
    "beets-3360",
    "core-8065",
    "core-21734",
    "core-29829",
    "core-32222",
    "core-32318",
    "core-40034",
    "kivy-6954",
    "luigi-1836",
    "pandas-17609",
    "pandas-21540",
    "pandas-22378",
    "pandas-22804",
    "pandas-24572",
    "pandas-28412",
    "pandas-36950",
    "pandas-37547",
    "pandas-38431",
    "pandas-39028-1",
    "pandas-41915",
    "requests-3179",
    "requests-3390",
    "requests-4723",
    "salt-33908",
    "salt-38947",
    "salt-52624",
    "salt-53394",
    "salt-54240",
    "salt-54785",
    "salt-56381",
    "sanic-1334",
    "scikitlearn-7259",
    "scikitlearn-8973",
    "scikitlearn-12603",
    "Zappa-388",
    "ansible-1",
    "keras-34",
    "keras-39",
    "luigi-4",
    "luigi-14",
    "pandas-49",
    "pandas-57",
    "pandas-158",
    "scrapy-1",
    "scrapy-2",
    "spacy-5",
    "matplotlib-3",
    "matplotlib-7",
    "matplotlib-8",
    "matplotlib-10",
    "numpy-8",
    "Pillow-14",
    "Pillow-15",
    "scipy-5",
    "sympy-5",
    "sympy-6",
    "sympy-36",
    "sympy-37",
    "sympy-40",
    "sympy-42",
    "sympy-43",
    "sympy-44",
]

RESULT_PATH = HOME_PATH / "result"
CLOC_PATH = HOME_PATH / "cloc"
pyinder_path = RESULT_PATH / "pyinder"
mypy_path = RESULT_PATH / "mypy"
pyre_path = RESULT_PATH / "pyre"
pytype_path = RESULT_PATH / "pytype"
pyright_path = RESULT_PATH / "pyright"

def run(project, num):
    pyinder_alarms = 0
    mypy_alarms = 0
    pyre_alarms = 0
    pytype_alarms = 0
    pyright_alarms = 0

    pyinder_cloc = 0
    mypy_cloc = 0
    pyre_cloc = 0
    pytype_cloc = 0
    pyright_cloc = 0

    # check if cloc exists
    if not CLOC_PATH.exists():
        print("No cloc result found. Please run cloc.py first!")
        exit(-1)

    # check if path exists
    if not pyinder_path.exists():
        print("The result of Pyinder is not found")
        pyinder_exists = False

    if not mypy_path.exists():
        print("The result of Mypy is not found")
        mypy_exists = False

    if not pyre_path.exists():
        print("The result of Pyre is not found")
        pyre_exists = False

    if not pytype_path.exists():
        print("The result of Pytype is not found")
        pytype_exists = False


    if not pyright_path.exists():
        print("The result of Pyright is not found")
        pyright_exists = False

    print("{:<20}".format("Project"), end="")

    print("{:<10}".format("Pyinder"), end="")
    print("{:<10}".format("Mypy"), end="")
    print("{:<10}".format("Pyre"), end="")
    print("{:<10}".format("Pytype"), end="")
    print("{:<10}".format("Pyright"), end="")

    print()

    for target_project in target_projects:
        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in target_project :
                    continue

        print("{:<20}".format(target_project), end="")
        try:
            with open(pyinder_path / target_project / "filter_result.json", "r") as f:
                pyinder = json.load(f)
        except FileNotFoundError:
            pyinder = None

        try:
            with open(mypy_path / target_project / "filter_result.json", "r") as f:
                mypy = json.load(f)
        except FileNotFoundError:
            mypy = None

        try:
            with open(pyre_path / target_project / "filter_result.json", "r") as f:
                pyre = json.load(f)
        except FileNotFoundError:
            pyre = None

        try:
            with open(pytype_path / target_project / "filter_result.json", "r") as f:
                pytype = json.load(f)
        except FileNotFoundError:
            pytype = None

        try:
            with open(pyright_path / target_project / "filter_result.json", "r") as f:
                pyright = json.load(f)
        except FileNotFoundError:
            pyright = None

        with open(CLOC_PATH / f"{target_project}.json", "r") as f:
            cloc = json.load(f)["SUM"]["code"]

        if pyinder:
            print("{:<10}".format(len(pyinder)), end="")
            pyinder_alarms += len(pyinder)
            pyinder_cloc += cloc
        else:
            print("{:<10}".format("N/A"), end="")

        if mypy:
            print("{:<10}".format(len(mypy)), end="")
            mypy_alarms += len(mypy)
            mypy_cloc += cloc
        else:
            print("{:<10}".format("N/A"), end="")

        if pyre:
            print("{:<10}".format(len(pyre)), end="")
            pyre_alarms += len(pyre)
            pyre_cloc += cloc
        else:
            print("{:<10}".format("N/A"), end="")
        
        if pytype:
            print("{:<10}".format(len(pytype)), end="")
            pytype_alarms += len(pytype)
            pytype_cloc += cloc
        else:
            print("{:<10}".format("N/A"), end="")
        
        if pyright:
            print("{:<10}".format(len(pyright)), end="")
            pyright_alarms += len(pyright)
            pyright_cloc += cloc
        else:
            print("{:<10}".format("N/A"), end="")

        print()

    print("{:<20}".format("Total"), end="")
    print("{:<10}".format(pyinder_alarms), end="")
    print("{:<10}".format(mypy_alarms), end="")
    print("{:<10}".format(pyre_alarms), end="")
    print("{:<10}".format(pytype_alarms), end="")
    print("{:<10}".format(pyright_alarms), end="")
    print()

    pyinder_per_cloc = round(pyinder_alarms / pyinder_cloc / 1000, 2) if pyinder_cloc != 0 else "N/A"
    mypy_per_cloc = round(mypy_alarms / mypy_cloc / 1000, 2) if mypy_cloc != 0 else "N/A"
    pyre_per_cloc = round(pyre_alarms / pyre_cloc / 1000, 2) if pyre_cloc != 0 else "N/A"
    pytype_per_cloc = round(pytype_alarms / pytype_cloc / 1000, 2) if pytype_cloc != 0 else "N/A"
    pyright_per_cloc = round(pyright_alarms / pyright_cloc / 1000, 2) if pyright_cloc != 0 else "N/A"

    print("{:<20}".format("Per 1k LOC"), end="")
    print("{:<10}".format(pyinder_per_cloc), end="")
    print("{:<10}".format(mypy_per_cloc), end="")
    print("{:<10}".format(pyre_per_cloc), end="")
    print("{:<10}".format(pytype_per_cloc), end="")
    print("{:<10}".format(pyright_per_cloc), end="")

    print()

    total_numpy = np.array([pyinder_per_cloc, mypy_per_cloc, pyre_per_cloc, pytype_per_cloc, pyright_per_cloc])
    pd.DataFrame([total_numpy], columns=["Pyinder", "Mypy", "Pyre", "Pytype", "Pyright"]).to_csv("alarm_result.csv", index=False)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    #parser.add_argument("-s", "--src_dir", dest="src_dir", action="store", required=True, type=Path) 
    parser.add_argument("-p", "--project", action="store", default=None, type=str) 
    parser.add_argument("-n", "--num", action="store", default=None, type=str) 

    args = parser.parse_args()

    run(args.project, args.num)
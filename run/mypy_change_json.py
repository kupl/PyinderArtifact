import sys
import os
import subprocess
import getopt
import json
import ast
from pathlib import Path

target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
    "airflow-14513",
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
    "pandas-20938",
    "pandas-21540",
    "pandas-22378",
    "pandas-22804",
    "pandas-24572",
    "pandas-28412",
    "pandas-30532",
    "pandas-36950",
    "pandas-37547",
    "pandas-38431",
    "pandas-39028-1",
    "pandas-41915",
    "rasa-8704",
    "requests-3179",
    "requests-3368",
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
    "sanic-2008",
    "scikitlearn-7259",
    "scikitlearn-8973",
    "scikitlearn-12603",
    "Zappa-388",
]

bugsinpy_projects = [
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
    "youtubedl-11",
    "youtubedl-16",
]

excepy_projects = [
    "matplotlib-3",
    "matplotlib-7",
    "matplotlib-8",
    "matplotlib-10",
    "numpy-8",
    "Pillow-14",
    "Pillow-15",
    "requests-1",
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


RESULT_PATH = Path.home() / "result" / "mypy"

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run(skip) :
    for target_project in target_projects :
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = RESULT_PATH / target_project
            result_file = result_path / 'result.json'
            result_file2 = result_path / 'result_.json'

            with open(result_file, 'r') as f :
                a = ast.literal_eval(f.read())

                lines = a.split('\n')
                
                error_lines = []

                for line in lines :
                    split_line = line.split(":")

                    if len(split_line) < 3 :
                        continue

                    if split_line[2].strip() == "error" :
                        error = {
                            'file' : split_line[0],
                            'line' : int(split_line[1]),
                            'error' : split_line[3]
                        }

                        error_lines.append(error)

                with open(result_file2, 'w') as f2 :
                    json.dump(error_lines, f2, indent=4)

            print('Done!')
        except Exception as e :
            print('Failed')


def bugsinpy_run(skip) :
    for target_project in bugsinpy_projects :
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = RESULT_PATH / target_project
            result_file = result_path / 'result.json'
            result_file2 = result_path / 'result_.json'

            with open(result_file, 'r') as f :
                a = ast.literal_eval(f.read())

                lines = a.split('\n')
                
                error_lines = []

                for line in lines :
                    split_line = line.split(":")

                    if len(split_line) < 3 :
                        continue

                    if split_line[2].strip() == "error" :
                        error = {
                            'file' : split_line[0],
                            'line' : int(split_line[1]),
                            'error' : split_line[3]
                        }

                        error_lines.append(error)

                with open(result_file2, 'w') as f2 :
                    json.dump(error_lines, f2, indent=4)

            print('Done!')
        except Exception as e :
            print('Failed')

def excepy_run(skip) :
    for target_project in excepy_projects :
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = RESULT_PATH / target_project
            result_file = result_path / 'result.json'
            result_file2 = result_path / 'result_.json'

            with open(result_file, 'r') as f :
                a = ast.literal_eval(f.read())

                lines = a.split('\n')
                
                error_lines = []

                for line in lines :
                    split_line = line.split(":")

                    if len(split_line) < 3 :
                        continue

                    if split_line[2].strip() == "error" :
                        error = {
                            'file' : split_line[0],
                            'line' : int(split_line[1]),
                            'error' : split_line[3]
                        }

                        error_lines.append(error)

                with open(result_file2, 'w') as f2 :
                    json.dump(error_lines, f2, indent=4)

            print('Done!')
        except Exception as e :
            print('Failed')

def main(argv) :
    skip = False
    try:
        # :가 붙으면 인수를 가지는 옵션
	    opts, args = getopt.getopt(argv, "hs:", ["skip="])
    except getopt.GetoptError:
	    print ('mypy_change_json.py --skip(or -s) <True/False>')
	    sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print ('mypy_change_json.py --skip(or -s) <True/False>')
            sys.exit()
        elif opt in ("-s", "--skip"):
            skip = bool(arg)

    run(skip)
    bugsinpy_run(skip)
    excepy_run(skip)

if __name__ == "__main__" :
    main(sys.argv[1:])
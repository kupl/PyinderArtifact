import sys
import os
import subprocess
import getopt
import json
import ast
from pprint import pprint
from pathlib import Path

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
    "Zappa-388"
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
]

excepy_projects = [
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

CONFIG_PATH = Path.home() / "configuration" / "config"
RESULT_PATH = Path.home() / "result" / "pytype"
# make directory for result
if not os.path.exists(RESULT_PATH):
    RESULT_PATH.mkdir(parents=True)

def filter_file(path) :
    if '/tests/' in path :
        return True

    if '/test' in path :
        return True

    if 'test/' in path :
        return True

    if 'tests/' in path :
        return True

    return False

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run(skip) :
    for target_project in target_projects + bugsinpy_projects + excepy_projects : 
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = RESULT_PATH / target_project
            result_file = result_path + '/result.json'
            result_file2 = result_path + '/result_.json'

            with open(result_file, 'r') as f :
                a = ast.literal_eval(f.read())

                lines = a.split('\n')
                
                error_lines = []

                for line in lines :
                    if not line.startswith('File') :
                        continue

                    split_line = line.split("\"")

                    if len(split_line) < 3 :
                        continue

                    file = split_line[1]

                    if filter_file(file) :
                        continue

                    other_split = split_line[2].split(",")

                    if len(other_split) < 3 :
                        continue

                    try :
                        line = int(other_split[1].strip().split()[1])
                        msg = other_split[-1].strip()#.split(":")[1].strip()
                    except Exception as e:
                        continue
                    op = msg.split("[")[-1][:-1]
                    op_msg = msg.split("[")[0].strip()

                    error = {
                        'file' : file,
                        'line' : line,
                        'error' : op_msg,
                        'op' : op,
                    }

                    error_lines.append(error)

                with open(result_file2, 'w') as f2 :
                    json.dump(error_lines, f2, indent=4)

            print('Done!')
        except Exception as e :
            print('Skip')




def main(argv) :
    skip = False
    try:
        # :가 붙으면 인수를 가지는 옵션
	    opts, args = getopt.getopt(argv, "hs:", ["skip="])
    except getopt.GetoptError:
	    print ('pytype_change_json.py --skip(or -s) <True/False>')
	    sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print ('pytype_change_json.py --skip(or -s) <True/False>')
            sys.exit()
        elif opt in ("-s", "--skip"):
            skip = bool(arg)

    run(skip)
    #bugsinpy_run(skip)
    #excepy_run(skip)

if __name__ == "__main__" :
    main(sys.argv[1:])
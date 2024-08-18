import sys
import os
import subprocess
import argparse
import json
import shutil
import time
import ast
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
    "spacy-5"
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
RESULT_PATH = Path.home() / "result" / "pyright"
# make directory for result
if not os.path.exists(RESULT_PATH):
    RESULT_PATH.mkdir(parents=True)

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run(skip, project, num) :
    for target_project in target_projects :
        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in target_projects :
                    continue

        print(target_project + ' is analyzed... ', end='', flush=True)

        result_path = RESULT_PATH / target_project
        result_file = result_path / 'result.json'
        check_directory_and_make_directory(result_path)

        benchmark_path = Path.home() / 'typebugs' / target_project

        # print(benchmark_path)

        if skip and os.path.isfile(result_file) :
            print('Skip!')
            continue


        #command = 'PYTHONPATH="/home/wonseok/Pyinder/..:$PYTHONPATH" python -m Pyinder.client.pyre -n --output=json mine'
        command = './run_pyright.sh {}'.format(benchmark_path)

        with open(os.devnull) as DEVNULL:
            result = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=os.getcwd())
            timeStarted = time.time()  
            out, err = result.communicate()
            timeDelta = time.time() - timeStarted  

            print("Finished process in "+str(timeDelta)+" seconds.")

        a = ast.literal_eval(out.decode('utf-8'))

        with open(result_file, 'w+') as f :
            json.dump(a, f, indent=4)

def bugsinpy_run(skip, project, num) :
    for target_project in bugsinpy_projects :
        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in bugsinpy_projects :
                    continue


        print(target_project + ' is analyzed... ', end='', flush=True)

        result_path = RESULT_PATH / target_project
        result_file = result_path / 'result.json'
        check_directory_and_make_directory(result_path)

        benchmark_path = Path.home() / 'bugsinpy' / target_project

        # print(benchmark_path)

        if skip and os.path.isfile(result_file) :
            print('Skip!')
            continue


        #command = 'PYTHONPATH="/home/wonseok/Pyinder/..:$PYTHONPATH" python -m Pyinder.client.pyre -n --output=json mine'
        command = './run_pyright.sh {}'.format(benchmark_path)

        with open(os.devnull) as DEVNULL:
            result = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=os.getcwd())
            timeStarted = time.time()  
            out, err = result.communicate()
            timeDelta = time.time() - timeStarted  

            print("Finished process in "+str(timeDelta)+" seconds.")

        a = ast.literal_eval(out.decode('utf-8'))

        with open(result_file, 'w+') as f :
            json.dump(a, f, indent=4)

def excepy_run(skip, project, num) :
    for target_project in excepy_projects :
        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in excepy_projects :
                    continue


        print(target_project + ' is analyzed... ', end='', flush=True)

        project_name = target_project.split('-')[0]

        result_path = RESULT_PATH / target_project
        result_file = result_path / 'result.json'
        check_directory_and_make_directory(result_path)

        benchmark_path = Path.home() / 'excepy' / target_project

        # print(benchmark_path)

        if skip and os.path.isfile(result_file) :
            print('Skip!')
            continue


        #command = 'PYTHONPATH="/home/wonseok/Pyinder/..:$PYTHONPATH" python -m Pyinder.client.pyre -n --output=json mine'
        command = './run_pyright.sh {}'.format(benchmark_path)

        with open(os.devnull) as DEVNULL:
            result = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=os.getcwd())
            timeStarted = time.time()  
            out, err = result.communicate()
            timeDelta = time.time() - timeStarted  

            print("Finished process in "+str(timeDelta)+" seconds.")

        a = ast.literal_eval(out.decode('utf-8'))

        with open(result_file, 'w+') as f :
            json.dump(a, f, indent=4)


def main(argv) :
    parser = argparse.ArgumentParser()
    #parser.add_argument("-s", "--src_dir", dest="src_dir", action="store", required=True, type=Path) 
    parser.add_argument("-p", "--project", action="store", default=None, type=str) 
    parser.add_argument("-n", "--num", action="store", default=None, type=str) 
    parser.add_argument("-s", "--skip", action="store", default=False, type=bool)

    args = parser.parse_args()

    run(args.skip, args.project, args.num)
    bugsinpy_run(args.skip, args.project, args.num)
    excepy_run(args.skip, args.project, args.num)

if __name__ == "__main__" :
    main(sys.argv[1:])
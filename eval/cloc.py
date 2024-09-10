# pylint:disable=invalid-name
"""Utilities that collect statistics"""
from __future__ import annotations
from glob import glob
import os
import subprocess
from pathlib import Path

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

CLOC_PATH = HOME_PATH / "cloc"

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def typebugs_run() :
    for typebugs in target_projects:

        check_directory_and_make_directory(CLOC_PATH)
        benchmark_path = HOME_PATH / "typebugs" / typebugs

        for project_path in glob(str(benchmark_path)) :
            #print(project_path)
            print(project_path.split('/')[-1], "is analyzed... ", end="")

            command = 'cloc %s --fullpath --by-file --include-lang=Python --not-match-d=".*(/test_|_test|_test_|/test|/tests_|_tests|_tests_|/tests).*" --not-match-f=".*(/test_|_test|_test_|/tests_|_tests|_tests_).*" --json --out=%s' \
            % (project_path, str(CLOC_PATH) + "/" + project_path.split('/')[-1] + ".json")
            result = subprocess.run(command, stdout=subprocess.PIPE, shell=True)

            print("Done!")

def bugsinpy_run() :
    for bugsinpy in bugsinpy_projects :

        check_directory_and_make_directory(CLOC_PATH)
        benchmark_path = HOME_PATH / "bugsinpy" / bugsinpy

        for project_path in glob(str(benchmark_path)) :
            #print(project_path)
            print(project_path.split('/')[-1], "is analyzed... ", end="")

            command = 'cloc %s --fullpath --by-file --include-lang=Python --not-match-d=".*(/test_|_test|_test_|/test|/tests_|_tests|_tests_|/tests).*" --not-match-f=".*(/test_|_test|_test_|/tests_|_tests|_tests_).*" --json --out=%s' \
            % (project_path, str(CLOC_PATH) + "/" + project_path.split('/')[-1] + ".json")
            result = subprocess.run(command, stdout=subprocess.PIPE, shell=True)

            print("Done!")

def excepy_run() :
    for excepy in excepy_projects :

        check_directory_and_make_directory(CLOC_PATH)
        benchmark_path = HOME_PATH / "excepy" / excepy

        for project_path in glob(str(benchmark_path)) :
            #print(project_path)
            print(project_path.split('/')[-1], "is analyzed... ", end="")

            command = 'cloc %s --fullpath --by-file --include-lang=Python --not-match-d=".*(/test_|_test|_test_|/test|/tests_|_tests|_tests_|/tests).*" --not-match-f=".*(/test_|_test|_test_|/tests_|_tests|_tests_).*" --json --out=%s' \
            % (project_path, str(CLOC_PATH) + "/" + project_path.split('/')[-1] + ".json")
            result = subprocess.run(command, stdout=subprocess.PIPE, shell=True)

            print("Done!")

if __name__ == "__main__" :
    typebugs_run()
    bugsinpy_run()
    excepy_run()

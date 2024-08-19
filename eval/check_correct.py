import json
from pathlib import Path
import argparse
import numpy as np
import pandas as pd

HOME_PATH = Path.home()

target_projects = [
    ("airflow-3831", "contrib/operators/dataflow_operator.py", 362),
    ("airflow-4674", "settings.py", 226),
    ("airflow-5686", "hooks/http_hook.py", 62),
    ("airflow-6036", "gcp/hooks/dataflow.py", 138),
    ("airflow-8151", "models/dag.py", 1519),
    ("airflow-14686", "providers/elasticsearch/log/es_task_handler.py", 186),
    ("beets-3360", "beetsplug/thumbnails.py", 227),
    ("core-8065", "helpers/entity_component.py", 241),
    ("core-21734", "components/sensor/dsmr.py", 354),
    ("core-29829", "components/input_text/__init__", 203),
    ("core-32222", "components/unifi/device_tracker.py", 204),
    ("core-32318", "components/alexa/capabilities.py", 675),
    ("core-40034", "helpers/condition.py", 659),
    ("kivy-6954", "network/urlrequest.py", 359),
    ("luigi-1836", "contrib/pig.py", 149),
    ("pandas-17609", "util/_decorators.py", 245),
    ("pandas-21540", "io/json/normalize.py", 262),
    ("pandas-22378", "core/ops.py", 115),
    ("pandas-22804", "io/json/normalize.py", 189),
    ("pandas-24572", "io/formats/html.py", 291),
    ("pandas-28412", "core/series.py", 2733),
    ("pandas-36950", "core/frame.py", 7409),
    ("pandas-37547", "core/reshape/merge.py", 1250),
    ("pandas-38431", "io/parsers.py", 1434),
    ("pandas-39028-1", "core/aggregation.py", 485),
    ("pandas-41915", "core/indexes/multi.py", 3623),
    ("requests-3179", "models.py", 795),
    ("requests-3390", "utils.py", 753),
    ("requests-4723", "utils.py", 640),
    ("salt-33908", "utils/__init__.py", 2355),
    ("salt-38947", "client/ssh/shell.py", 176),
    ("salt-52624", "cli/batch.py", 88),
    ("salt-53394", "utils/http.py", 108),
    ("salt-54240", "cloud/clouds/ec2.py", 1227),
    ("salt-54785", "modules/state.py", 1637),
    ("salt-56381", "state.py", 2218),
    ("sanic-1334", "sanic/blueprints.py", 57),
    ("scikitlearn-7259", "gaussian_process/kernels.py", 1207),
    ("scikitlearn-8973", "linear_model/coordinate_descent.py", 1153),
    ("scikitlearn-12603", "gaussian_process/kernels.py", 1488),
    ("Zappa-388", "wsgi.py", 95),
    ("ansible-1", "lib/ansible/galaxy/collection.py", 442),
    ("keras-34", "engine/training.py", 2207),
    ("keras-39", "utils/generic_utils", 330),
    ("luigi-4", "contrib/redshift.py", 356),
    ("luigi-14", "scheduler.py", 208),
    ("pandas-49", "core/strings.py", 782),
    ("pandas-57", "core/indexes/numeric.py", 232),
    ("pandas-158", "core/common.py", 231),
    ("scrapy-1", "spidermiddlewares/offsite.py", 58),
    ("scrapy-2", "utils/datatypes.py", 318),
    ("spacy-5", "language.py", 1106),
    ("matplotlib-3", "matplotlib/backends/backend_svg.py", 89),
    ("matplotlib-7", "matplotlib/lib/matplotlib/lines.py", 60),
    ("matplotlib-8", "matplotlib/lib/matplotlib/gridspec.py", 4),
    ("matplotlib-10", "matplotlib/lib/matplotlib/offsetbox.py", 478),
    ("numpy-8", "numpy/numpy/polynomial/_polybase.py", 350),
    ("Pillow-14", "src/PIL/Image.py", 437),
    ("Pillow-15", "PIL/ImageMorph.py", 175),
    ("scipy-5", "scipy/io/mmio.py", 259),
    ("sympy-5", "sympy/simplify/simplify.py", 211),
    ("sympy-6", "integrals/meijerint.py", 1803),
    ("sympy-36", "sympy/series/order.py", 445),
    ("sympy-37", "sympy/functions/elementary/piecewise.py", 1200),
    ("sympy-40", "core/expr.py", 879),
    ("sympy-42", "sympy/sympy/core/expr.py", 130),
    ("sympy-43", "sympy/integrals/manualintegrate.py", 743),
    ("sympy-44", "sympy/sympy/core/basic.py", 1519),
]

RESULT_PATH = HOME_PATH / "result"
pyinder_path = RESULT_PATH / "pyinder"
mypy_path = RESULT_PATH / "mypy"
pyre_path = RESULT_PATH / "pyre"
pytype_path = RESULT_PATH / "pytype"
pyright_path = RESULT_PATH / "pyright"


def run(check_project, num):
    ours_correct = 0
    mypy_correct = 0
    pyre_correct = 0
    pytype_correct = 0
    pyright_correct = 0

    total_result = []

    pyinder_exists = True
    mypy_exists = True
    pyre_exists = True
    pytype_exists = True
    pyright_exists = True

    

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

    for project, file, line in target_projects:
        if check_project :
            if num :
                if project != "{}-{}".format(check_project, num) :
                    continue 
            else :
                if check_project not in project :
                    continue
        if file:
            print("{:<20}".format(project), end="")
            try:
                with open(pyinder_path / project / "filter_result.json", "r") as f:
                    result = json.load(f)
            except FileNotFoundError:
                result = None
            
            try:
                with open(mypy_path / project / "filter_result.json", "r") as f:
                    mypy = json.load(f)
            except FileNotFoundError:
                mypy = None

            try:
                with open(pyre_path / project / "filter_result.json", "r") as f:
                    pyre = json.load(f)
            except FileNotFoundError:
                pyre = None

            try:
                with open(pytype_path / project / "filter_result.json", "r") as f:
                    pytype = json.load(f)
            except FileNotFoundError:
                pytype = None

            try:
                with open(pyright_path / project / "filter_result.json", "r") as f:
                    pyright = json.load(f)
            except FileNotFoundError:
                pyright = None

            project_result = [project]
            our_find = False

            if not pyinder_exists:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            elif result is None:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            else:
                if result:
                    for our_error in result:
                        if project == "pandas-158":
                            # No correct
                            break

                        if file in our_error["file"] and line == our_error["line"]:
                            print("{:<10}".format("O"), end="")
                            our_find = True
                            ours_correct += 1
                            break
                
                if not our_find:
                    project_result.append("X")
                    print("{:<10}".format("X"), end="")
                else:
                    project_result.append("O")

            if not mypy_exists:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            elif mypy is None:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            else:
                mypy_find = False
                for mypy_error in mypy:
                    if project == "core-29829":
                        # No correct
                        break

                    if project == "salt-53394":
                        # No correct
                        break

                    if project == "Pillow-15":
                        # No correct
                        break

                    if file in mypy_error["file"] and line == mypy_error["line"]:
                        print("{:<10}".format("O"), end="")
                        mypy_find = True
                        mypy_correct += 1
                        break

                if not mypy_find:
                    project_result.append("X")
                    print("{:<10}".format("X"), end="")
                else:
                    project_result.append("O")

            if not pyre_exists:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            elif pyre is None:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            else:
                pyre_find = False
                for pyre_error in pyre:
                    if project == "Pillow-15":
                        # No correct
                        break

                    if file in pyre_error["file"] and line == pyre_error["line"]:
                        print("{:<10}".format("O"), end="")
                        pyre_find = True
                        pyre_correct += 1
                        break

                if not pyre_find:
                    project_result.append("X")
                    print("{:<10}".format("X"), end="")
                else:
                    project_result.append("O")

            if not pytype_exists:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            elif pytype is None:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            else:
                pytype_find = False
                for pytype_error in pytype:
                    if file in pytype_error["file"] and line == pytype_error["line"]:
                        print("{:<10}".format("O"), end="")
                        pytype_find = True
                        pytype_correct += 1
                        break

                if not pytype_find:
                    project_result.append("X")
                    print("{:<10}".format("X"), end="")
                else:
                    project_result.append("O")

            if not pyright_exists:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            elif pyright is None:
                project_result.append("E")
                print("{:<10}".format("E"), end="")
            else:
                pyright_find = False
                for pyright_error in pyright:
                    pyright_line = pyright_error["line"] + 1
                    if project == "salt-33908":
                        pyright_line += 1
                    if project == "Pillow-15":
                        # No correct
                        break
                    if project == "salt-53394":
                        # No correct
                        break
                    if project == "requests-3390":
                        # No correct
                        break

                    if file in pyright_error["file"] and line == pyright_line:
                        print("{:<10}".format("O"), end="")
                        pyright_find = True
                        pyright_correct += 1
                        break

                if not pyright_find:
                    project_result.append("X")
                    print("{:<10}".format("X"), end="")
                else:
                    project_result.append("O")
        else:
            project_result = [project, "X", "X", "X", "X", "X"]
            print("{:<20} X X X X ".format(project), end="")
        print()

        total_result.append(project_result)

    print("{:<20}".format("Correct"), end="")
    print("{:<10}".format(ours_correct), end="")
    print("{:<10}".format(mypy_correct), end="")
    print("{:<10}".format(pyre_correct), end="")
    print("{:<10}".format(pytype_correct), end="")
    print("{:<10}".format(pyright_correct), end="")

    print()

    total_numpy = np.array(total_result)
    pd.DataFrame(total_numpy, columns=["Project", "Pyinder", "Mypy", "Pyre", "Pytype", "Pyright"]).to_csv("correct_result.csv", index=False)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    #parser.add_argument("-s", "--src_dir", dest="src_dir", action="store", required=True, type=Path) 
    parser.add_argument("-p", "--project", action="store", default=None, type=str) 
    parser.add_argument("-n", "--num", action="store", default=None, type=str) 

    args = parser.parse_args()

    run(args.project, args.num)
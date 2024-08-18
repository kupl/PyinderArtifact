import json
from pathlib import Path
# import numpy as np
# import pandas as pd

target_projects = [
    ("airflow-3831", "dataflow_operator.py", 362),
    ("airflow-4674", "settings.py", 226),
    ("airflow-5686", "hooks/http_hook.py", 62),
    ("airflow-6036", "airflow/gcp/hooks/dataflow.py", 138),
    ("airflow-8151", "models/dag.py", 1519),
    # ("airflow-14513", "kubernetes/pod_launcher.py", 143),
    ("airflow-14686", "log/es_task_handler.py", 186),
    ("beets-3360", "beetsplug/thumbnails.py", 227),
    ("core-8065", "helpers/entity_component.py", 241),
    ("core-21734", "components/sensor/dsmr.py", 354),
    ("core-29829", "input_text/__init__", 124),
    ("core-32222", "components/unifi/device_tracker.py", 209),
    ("core-32318", "alexa/capabilities.py", 476),
    ("core-40034", "homeassistant/helpers/condition.py", 659),
    ("kivy-6954", "network/urlrequest.py", 359),
    ("luigi-1836", "contrib/pig.py", 149),
    ("pandas-17609", "pandas/util/_decorators.py", 245),
    ("pandas-21540", "io/json/normalize.py", 262),
    ("pandas-22378", "pandas/core/ops.py", 115),
    ("pandas-22804", "io/json/normalize.py", 185),
    ("pandas-24572", "pandas/io/formats/html.py", 294),
    ("pandas-28412", "pandas/core/series.py", 2733),
    ("pandas-36950", "pandas/core/frame.py", 7409),
    ("pandas-37547", "pandas/core/reshape/merge.py", 1250),
    ("pandas-38431", "pandas/io/parsers.py", 1438),
    ("pandas-39028-1", "pandas/core/aggregation.py", 485),
    ("pandas-41915", "indexes/multi.py", 3623),
    ("requests-3179", "requests/models.py", 795),
    ("requests-3390", "requests/utils.py", 754),
    ("requests-4723", "requests/utils.py", 640),
    ("salt-33908", "salt/utils/__init__.py", 2355),
    ("salt-38947", "client/ssh/shell.py", 176),
    ("salt-52624", "salt/cli/batch.py", 88),
    ("salt-53394", "salt/utils/http.py", 108),
    ("salt-54240", "salt/cloud/clouds/ec2.py", 1227),
    ("salt-54785", "salt/modules/state.py", 1637),
    ("salt-56381", "salt/state.py", 2221),
    ("sanic-1334", "sanic/blueprints.py", 57),
    # ("sanic-2008", "sanic/static.py", 44),
    ("scikitlearn-7259", "sklearn/gaussian_process/kernels.py", 1207),
    ("scikitlearn-8973", "linear_model/coordinate_descent.py", 1153),
    ("scikitlearn-12603", "sklearn/gaussian_process/kernels.py", 1488),
    ("Zappa-388", "zappa/wsgi.py", 95),
    ("ansible-1", "ansible/galaxy/collection.py", 442),
    ("keras-34", "keras/engine/training.py", 2207),
    ("keras-39", "utils/generic_utils", 330),
    ("luigi-4", "luigi/contrib/redshift.py", 356),
    ("luigi-14", "luigi/scheduler.py", 208),
    ("pandas-49", "pandas/core/strings.py", 781),
    ("pandas-57", "pandas/core/indexes/numeric.py", 232),
    ("pandas-158", "pandas/core/common.py", 231),
    ("scrapy-1", "spidermiddlewares/offsite.py", 58),
    ("scrapy-2", "utils/datatypes.py", 318),
    ("spacy-5", "language.py", 1106),
    # ("youtubedl-11", "youtube_dl/utils.py", 3524),
    # ("youtubedl-16", "utils.py", 2675),
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
    ("sympy-36", "sympy/series/order.py", 446),
    ("sympy-37", "sympy/functions/elementary/piecewise.py", 1200),
    ("sympy-40", "core/expr.py", 879),
    ("sympy-42", "sympy/sympy/core/expr.py", 130),
    ("sympy-43", "sympy/integrals/manualintegrate.py", 743),
    ("sympy-44", "sympy/sympy/core/basic.py", 1519),
]

result_path = Path("/home/wonseok/pyinder_run/pyre_0523")
mypy_path = Path("/home/wonseok/pyinder_run/mypy")
pyre_path = Path("/home/wonseok/pyinder_run/real_pyre_result_0419")
pytype_path = Path("/home/wonseok/pyinder_run/pytype")
pyright_path = Path("/home/wonseok/pyinder_run/pyright")


l8_path = Path("/home/wonseok/pyinder_run/pyre")

def run():

    my_path = result_path

    ours_correct = 0
    mypy_correct = 0
    pyre_correct = 0
    pytype_correct = 0
    pyright_correct = 0

    total_result = []

    for project, file, line in target_projects:
        
        if file:
            print("{:<20} ".format(project), end="")
            with open(my_path / project / "result_.json", "r") as f:
                result = json.load(f)
            with open(mypy_path / project / "result_.json", "r") as f:
                mypy = json.load(f)
            with open(pyre_path / project / "result_.json", "r") as f:
                pyre = json.load(f)
            with open(pytype_path / project / "result_.json", "r") as f:
                pytype = json.load(f)
            with open(pyright_path / project / "result.json", "r") as f:
                pyright = json.load(f)["generalDiagnostics"]
            project_result = [project]
            our_find = False
            if result:
                for our_error in result:
                    if project == "pandas-158":
                        # No correct
                        break

                    if file in our_error["path"] and line == our_error["line"]:
                        print("O ", end="")
                        our_find = True
                        ours_correct += 1
                        break

            if not our_find:
                project_result.append("X")
                print("X ", end="")
            else:
                project_result.append("O")

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
                    print("O ", end="")
                    mypy_find = True
                    mypy_correct += 1
                    break

            if not mypy_find:
                project_result.append("X")
                print("X ", end="")
            else:
                project_result.append("O")

            pyre_find = False
            for pyre_error in pyre:
                if project == "Pillow-15":
                    # No correct
                    break

                if file in pyre_error["path"] and line == pyre_error["line"]:
                    print("O ", end="")
                    pyre_find = True
                    pyre_correct += 1
                    break

            if not pyre_find:
                project_result.append("X")
                print("X ", end="")
            else:
                project_result.append("O")

            pytype_find = False
            for pytype_error in pytype:
                if file in pytype_error["file"] and line == pytype_error["line"]:
                    print("O ", end="")
                    pytype_find = True
                    pytype_correct += 1
                    break

            if not pytype_find:
                project_result.append("X")
                print("X ", end="")
            else:
                project_result.append("O")

            pyright_find = False
            for pyright_error in pyright:
                pyright_line = pyright_error["range"]["start"]["line"] + 1
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
                    print("O ", end="")
                    pyright_find = True
                    pyright_correct += 1
                    break

            if not pyright_find:
                project_result.append("X")
                print("X ", end="")
            else:
                project_result.append("O")
        else:
            project_result = [project, "X", "X", "X", "X", "X"]
            print("{:<20} X X X X ".format(project), end="")
        print()

        # print(project_result)

        total_result.append(project_result)
    print(len(target_projects))
    print(f"{ours_correct} ({round(ours_correct / len(target_projects) * 100)}), \
        {mypy_correct} ({round(mypy_correct / len(target_projects) * 100)}), \
        {pyre_correct} ({round(pyre_correct / len(target_projects) * 100)}), \
        {pytype_correct} ({round(pytype_correct / len(target_projects) * 100)}), \
        {pyright_correct} ({round(pyright_correct / len(target_projects) * 100)})")

    # a = np.array(total_result)

    # pd.DataFrame(a, columns=["Project", "Ours", "Mypy", "Pyre", "Pytype", "Pyright"]).to_csv("csv/result.csv", index=False)

if __name__ == "__main__":
    run()
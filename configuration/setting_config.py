from pathlib import Path
import json
import os
import argparse

HOME_PATH = Path.home()

typebugs = """airflow-3831         
airflow-4674         
airflow-5686         
airflow-6036         
airflow-8151         
airflow-14686        
beets-3360           
core-8065            
core-21734           
core-29829           
core-32222           
core-32318           
core-40034           
kivy-6954            
luigi-1836           
pandas-17609         
pandas-21540         
pandas-22378         
pandas-22804         
pandas-24572         
pandas-28412         
pandas-36950         
pandas-37547         
pandas-38431         
pandas-39028-1       
pandas-41915         
requests-3179        
requests-3390        
requests-4723        
salt-33908           
salt-38947           
salt-52624           
salt-53394           
salt-54240           
salt-54785           
salt-56381           
sanic-1334           
scikitlearn-7259     
scikitlearn-8973     
scikitlearn-12603    
Zappa-388 
"""

bugsinpy = """ansible-1  
keras-34   
keras-39   
luigi-4    
luigi-14   
pandas-49  
pandas-57  
pandas-158 
scrapy-1   
scrapy-2   
spacy-5    
"""

excepy = """matplotlib-3  
matplotlib-7  
matplotlib-8  
matplotlib-10 
numpy-8       
Pillow-14     
Pillow-15     
scipy-5       
sympy-5       
sympy-6       
sympy-36      
sympy-37      
sympy-40      
sympy-42      
sympy-43      
sympy-44      
"""

def mypy_config_change(path, file_content, prj):
    mypy_content = file_content.split("\n")
    new_mypy_content = []
    for line in mypy_content:
        if "files =" in line:
            src_paths = line[8:]
            divide_paths = src_paths.split()
            new_src_paths = ""
            for divide_path in divide_paths:
                idx = divide_path.find(prj)
                new_path = path + divide_path[idx+len(prj):]
                new_src_paths += new_path + " "

            new_src_paths = new_src_paths.strip()
            new_mypy_content.append(f"files = {new_src_paths}")
        else:
            new_mypy_content.append(line)

    return "\n".join(new_mypy_content)

def pytype_config_change(path, file_content, prj):
    pytype_content = file_content.split("\n")
    new_pytype_content = []
    for line in pytype_content:
        if "inputs = " in line:
            src_paths = line[9:]
            divide_paths = src_paths.split()
            new_src_paths = ""
            for divide_path in divide_paths:
                idx = divide_path.find(prj)
                new_path = path + divide_path[idx+len(prj):]
                new_src_paths += new_path + " "

            new_src_paths = new_src_paths.strip()
            new_pytype_content.append(f"inputs = {new_src_paths}")
                
        elif "pythonpath = " in line:
            idx = line.rfind(prj)
            src_path = line[idx+len(prj):]
            new_pytype_content.append(f"pythonpath = {path}{src_path}")
        elif "**" in line:
            pass
        else:
            new_pytype_content.append(line)
    
    

    return "\n".join(new_pytype_content)

def pyright_config_change(path, file_content, prj):
    lines = file_content["include"]
    new_contents = []
    for line in lines:
        idx = line.rfind(prj)
        src_path = line[idx+len(prj):]
        new_contents.append(f".{src_path}")
    file_content["include"] = new_contents
    if "requests" in prj:
        file_content["typeshedPath"] = str(HOME_PATH / "Pyinder/stubs/typeshed/typeshed-without-requests")
    elif "Pillow" in prj:
        file_content["typeshedPath"] = str(HOME_PATH / "Pyinder/stubs/typeshed/typeshed-without-Pillow")

    return file_content

def pyre_config_change(path, file_content, prj):

    file_content["search_path"] = [path]
    new_source_directories = []
    for source_directory in file_content["source_directories"]:
        source_directory["root"] = path
        new_source_directories.append(source_directory)

    file_content["source_directories"] = new_source_directories
    if "requests" in prj:
        file_content["typeshed"] = str(HOME_PATH / "Pyinder/stubs/typeshed/typeshed-without-requests")
    elif "Pillow" in prj:
        file_content["typeshed"] = str(HOME_PATH / "Pyinder/stubs/typeshed/typeshed-without-Pillow")
    else:
        file_content["typeshed"] = str(HOME_PATH / "Pyinder/stubs/typeshed/typeshed-master")

    return file_content

def run():
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", type=str, default=None)
    args = ap.parse_args()
    target = args.project

    config_path = HOME_PATH / "configuration" / "config"

    typebugs_list = typebugs.split()
    for prj in typebugs_list:
        if target and target not in prj:
            continue

        path = HOME_PATH / "typebugs" / prj

        mypy_config = config_path / "typebugs" / prj / "mypy.ini"
        pytype_config = config_path / "typebugs" / prj / "pytype.cfg"
        pyright_config = config_path / "typebugs" / prj / "pyrightconfig.json"
        pyre_config = config_path / "typebugs" / prj / ".pyre_configuration"

        with open(mypy_config, "r") as f:
            mypy_content = f.read()
        with open(pytype_config, "r") as f:
            pytype_content = f.read()
        with open(pyright_config, "r") as f:
            pyright_content = json.load(f)
        with open(pyre_config, "r") as f:
            pyre_content = json.load(f)

        new_mypy_content = mypy_config_change(str(path), mypy_content, prj)
        new_pytype_content = pytype_config_change(str(path), pytype_content, prj)
        new_pyright_content = pyright_config_change(str(path), pyright_content, prj)
        new_pyre_content = pyre_config_change(str(path), pyre_content, prj)

        save_path = Path("config") / "typebugs"
        save_path.mkdir(exist_ok=True)
        save_path = save_path / prj
        save_path.mkdir(exist_ok=True)


        benchmark_path = HOME_PATH / "typebugs" / prj

        with open(save_path / "mypy.ini", "w") as f:
            f.write(new_mypy_content)
        with open(save_path / "pytype.cfg", "w") as f:
            f.write(new_pytype_content)
        with open(benchmark_path / "pyrightconfig.json", "w") as f:
            json.dump(new_pyright_content, f, indent=4)
        with open(save_path / ".pyre_configuration", "w") as f:
            json.dump(new_pyre_content, f, indent=4)

    bugsinpy_list = bugsinpy.split()
    for prj in bugsinpy_list:
        if target and target not in prj:
            continue

        path = HOME_PATH / "bugsinpy" / prj

        mypy_config = config_path / "bugsinpy" / prj / "mypy.ini"
        pytype_config = config_path / "bugsinpy" / prj / "pytype.cfg"
        pyright_config = config_path / "bugsinpy" / prj / "pyrightconfig.json"
        pyre_config = config_path / "bugsinpy" / prj / ".pyre_configuration"

        with open(mypy_config, "r") as f:
            mypy_content = f.read()
        with open(pytype_config, "r") as f:
            pytype_content = f.read()
        with open(pyright_config, "r") as f:
            pyright_content = json.load(f)
        with open(pyre_config, "r") as f:
            pyre_content = json.load(f)

        new_mypy_content = mypy_config_change(str(path), mypy_content, prj)
        new_pytype_content = pytype_config_change(str(path), pytype_content, prj)
        new_pyright_content = pyright_config_change(str(path), pyright_content, prj)
        new_pyre_content = pyre_config_change(str(path), pyre_content, prj)

        save_path = Path("config") / "bugsinpy"
        save_path.mkdir(exist_ok=True)
        save_path = save_path / prj
        save_path.mkdir(exist_ok=True)

        benchmark_path = HOME_PATH / "bugsinpy" / prj

        with open(save_path / "mypy.ini", "w") as f:
            f.write(new_mypy_content)
        with open(save_path / "pytype.cfg", "w") as f:
            f.write(new_pytype_content)
        with open(benchmark_path / "pyrightconfig.json", "w") as f:
            json.dump(new_pyright_content, f, indent=4)
        with open(save_path / ".pyre_configuration", "w") as f:
            json.dump(new_pyre_content, f, indent=4)
    
    excepy_list = excepy.split()
    for prj in excepy_list:
        if target and target not in prj:
            continue
        
        path = HOME_PATH / "excepy" / prj

        mypy_config = config_path / "excepy" / prj / "mypy.ini"
        pytype_config = config_path / "excepy" / prj / "pytype.cfg"
        pyright_config = config_path / "excepy" / prj / "pyrightconfig.json"
        pyre_config = config_path / "excepy" / prj / ".pyre_configuration"

        with open(mypy_config, "r") as f:
            mypy_content = f.read()
        with open(pytype_config, "r") as f:
            pytype_content = f.read()
        with open(pyright_config, "r") as f:
            pyright_content = json.load(f)
        with open(pyre_config, "r") as f:
            pyre_content = json.load(f)

        new_mypy_content = mypy_config_change(str(path), mypy_content, prj)
        new_pytype_content = pytype_config_change(str(path), pytype_content, prj)
        new_pyright_content = pyright_config_change(str(path), pyright_content, prj)
        new_pyre_content = pyre_config_change(str(path), pyre_content, prj)

        save_path = Path("config") / "excepy"
        save_path.mkdir(exist_ok=True)
        save_path = save_path / prj
        save_path.mkdir(exist_ok=True)

        benchmark_path = HOME_PATH / "excepy" / prj

        with open(save_path / "mypy.ini", "w") as f:
            f.write(new_mypy_content)
        with open(save_path / "pytype.cfg", "w") as f:
            f.write(new_pytype_content)
        with open(benchmark_path / "pyrightconfig.json", "w") as f:
            json.dump(new_pyright_content, f, indent=4)
        with open(save_path / ".pyre_configuration", "w") as f:
            json.dump(new_pyre_content, f, indent=4)


if __name__ == "__main__":
    run()
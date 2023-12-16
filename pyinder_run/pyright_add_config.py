import sys
import os
import subprocess
import getopt
import json
from pprint import pprint

target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
    "airflow-14686",
    "beets-3360",
    "core-8065",
    "core-29829",
    "core-32222",
    "core-32318",
    "core-38605",
    "core-40034",
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
    "pandas-39028-2",
    "rasa-8704",
    "requests-3179",
    "requests-3368",
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
]

bugsinpy_projects = [
    "ansible-1",
    "keras-34",
    "keras-39",
    "luigi-4",
    "luigi-14",
    "luigi-22",
    "luigi-25",
    "pandas-49",
    "pandas-57",
    "pandas-158",
    "scrapy-2",
    "scrapy-20",
    "scrapy-30",
    "spacy-5",
    "tqdm-3",
    "youtubedl-16",
]

excepy_projects = [
    "cpython-6",
    "matplotlib-3",
    "matplotlib-7",
    "matplotlib-8",
    "matplotlib-10",
    "numpy-8",
    "Pillow-14",
    "Pillow-15",
    "Pillow-16",
    "Pillow-17",
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
    "sympy-45",
    "sympy-48",
    "sympy-49",
    "sympy-60",
]



home_path = '/home/wonseok'
pyre_config = home_path + '/pyinder_run/config'

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in target_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)

        benchmark_path = home_path + '/benchmark/' + target_project
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyright_path = pyre_config + "/" + target_project + '/pyrightconfig.json'

        with open(pyright_path, 'r') as pyright_f :
            pyright_configuration = json.loads(pyright_f.read())

        r = dict() 
        find_exclude = False
        for k, v in pyright_configuration.items() :
            if "typeshedPath" in k :
                continue
            if "exclude" in k :
                find_exclude = True
            if "include" in k :
                lines = v[0].split('/')
                relative = './' + '/'.join(lines[lines.index(target_project)+1:])

                r[k] = [relative]
            else :    
                r[k] = v
        
        if not find_exclude :
            r["exclude"] = ["**/*_test.py","**/test_*.py","**/tests", "**/benchmarks"]

        pyright_configuration = r

        # cfg_f = open(cfg_path, 'r')
        """ pyright_configuration = {
                    "include": [
                        benchmark_path + "/"
                    ],
                    "typeshedPath": "/home/wonseok/Pyinder/stubs/typeshed/typeshed-master",
                    "reportUndefinedVariable": "warning",
                    "strictListInference": True,
                    "strictDictInference": True,
                    "strictSetInference": True,
                    "reportMissingModuleSource": False,
                    "reportMissingImports": False,
                    "reportWildcardImportFromLibrary": False,
                    "reportPrivateImportUsage": False,
                    "reportTypedDictNotRequiredAccess": False,
                    "reportUnusedCoroutine": False,
                    "reportUnboundVariable": False
                } """
        
        with open(benchmark_path + "/pyrightconfig.json", 'w+') as pyright_f :
            pyright_f.write(json.dumps(pyright_configuration, indent=4))


        print("Done!")
        
def bugsinpy_run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in bugsinpy_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)

        benchmark_path = home_path + '/BugsInPy/benchmark/' + target_project
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyright_path = pyre_config + "/" + target_project + '/pyrightconfig.json'

        with open(pyright_path, 'r') as pyright_f :
            pyright_configuration = json.loads(pyright_f.read())


        r = dict() 
        find_exclude = False
        for k, v in pyright_configuration.items() :
            if "typeshedPath" in k :
                continue
            if "exclude" in k :
                find_exclude = True
            if "include" in k :
                lines = v[0].split('/')
                relative = './' + '/'.join(lines[lines.index(target_project)+1:])

                r[k] = [relative]
            else :    
                r[k] = v
        
        if not find_exclude :
            r["exclude"] = ["**/*_test.py","**/test_*.py","**/tests","**/benchmarks"]


        pyright_configuration = r
        
        # cfg_f = open(cfg_path, 'r')
        """ pyright_configuration = {
                    "include": [
                        benchmark_path + "/"
                    ],
                    "typeshedPath": "/home/wonseok/Pyinder/stubs/typeshed/typeshed-master",
                    "reportUndefinedVariable": "warning",
                    "strictListInference": True,
                    "strictDictInference": True,
                    "strictSetInference": True,
                    "reportMissingModuleSource": False,
                    "reportMissingImports": False,
                    "reportWildcardImportFromLibrary": False,
                    "reportPrivateImportUsage": False,
                    "reportTypedDictNotRequiredAccess": False,
                    "reportUnusedCoroutine": False,
                    "reportUnboundVariable": False
                } """
        
        with open(benchmark_path + "/pyrightconfig.json", 'w+') as pyright_f :
            pyright_f.write(json.dumps(pyright_configuration, indent=4))

        print("Done!")


def excepy_run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in excepy_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)
        
        project_name = target_project.split('-')[0]

        benchmark_path = home_path + '/ExcePy_Present/data/' + project_name + "/" + target_project
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyright_path = pyre_config + "/" + target_project + '/pyrightconfig.json'

        with open(pyright_path, 'r') as pyright_f :
            pyright_configuration = json.loads(pyright_f.read())
            
        r = dict() 
        find_exclude = False
        for k, v in pyright_configuration.items() :
            if "typeshedPath" in k :
                continue
            if "exclude" in k :
                find_exclude = True
            if "include" in k :
                lines = v[0].split('/')
                relative = './' + '/'.join(lines[lines.index(target_project)+1:])

                r[k] = [relative]
            else :    
                r[k] = v
        
        if not find_exclude :
            r["exclude"] = ["**/*_test.py","**/test_*.py","**/tests","**/benchmarks"]


        pyright_configuration = r
        
        # cfg_f = open(cfg_path, 'r')
        """ pyright_configuration = {
                    "include": [
                        benchmark_path + "/"
                    ],
                    "typeshedPath": "/home/wonseok/Pyinder/stubs/typeshed/typeshed-master",
                    "reportUndefinedVariable": "warning",
                    "strictListInference": True,
                    "strictDictInference": True,
                    "strictSetInference": True,
                    "reportMissingModuleSource": False,
                    "reportMissingImports": False,
                    "reportWildcardImportFromLibrary": False,
                    "reportPrivateImportUsage": False,
                    "reportTypedDictNotRequiredAccess": False,
                    "reportUnusedCoroutine": False,
                    "reportUnboundVariable": False
                } """
        
        with open(benchmark_path + "/pyrightconfig.json", 'w+') as pyright_f :
            pyright_f.write(json.dumps(pyright_configuration, indent=4))

        print("Done!")


def main(argv) :
    run()
    bugsinpy_run()
    excepy_run()

if __name__ == "__main__" :
    main(sys.argv[1:])
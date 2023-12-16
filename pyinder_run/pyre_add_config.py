import sys
import os
import subprocess
import getopt
import json

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
    "Pillow-4",
    "Pillow-7",
    "Pillow-15",
    "Pillow-16",
    "Pillow-17",
    "pytest-2",
    "requests-1",
    "requests-3",
    "scipy-5",
    "sympy-5",
    "sympy-6",
    "sympy-36",
    "sympy-48",
    "sympy-49",
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
        cfg_path = benchmark_path + '/pytype.cfg'
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyre_path = pyre_config + "/" + target_project + '/.pyre_configuration'
        config_path = pyre_config + "/" + target_project + '/.config'

        cfg_f = open(cfg_path, 'r')
        flag = False
        for l in cfg_f.readlines() :
            if flag and l.strip() :
                subdirectory = '/'.join(l.strip().split('/')[:-1])[2:]
                # if delete this, then just check specific folder
                subdirectory = subdirectory.split('/')[0]

                filename = l.strip().split('/')[-1]
                pyre_configuration = {
                    "search_path" : [
                        benchmark_path
                    ],
                    "source_directories" : [
                        {"root" : benchmark_path, "subdirectory" : subdirectory}
                    ],
                    "strict" : True,
                    "taint_models_path": ".",
                    "typeshed": "/home/wonseok/Pyinder/stubs/typeshed/typeshed-master"
                }
                
                taint_config = {
                    "sources": [],
                    "sinks": [],
                    "features": [],
                    "rules": []
                }

                with open(pyre_path, 'w+') as pyre_f :
                    pyre_f.write(json.dumps(pyre_configuration, indent=4))

                with open(config_path, 'w+') as pyre_c :
                    pyre_c.write(json.dumps(taint_config, indent=4))

                flag = False
            if 'inputs' in l :
                flag = True
        cfg_f.close()

        print("Done!")
        
def bugsinpy_run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in bugsinpy_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)

        benchmark_path = home_path + '/BugsInPy/benchmark/' + target_project
        cfg_path = benchmark_path + '/pytype.cfg'
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyre_path = pyre_config + "/" + target_project + '/.pyre_configuration'
        config_path = pyre_config + "/" + target_project + '/.config'

        cfg_f = open(cfg_path, 'r')
        flag = False
        for l in cfg_f.readlines() :
            if flag and l.strip() :
                subdirectory = '/'.join(l.strip().split('/')[:-1])[2:]
                # if delete this, then just check specific folder
                subdirectory = subdirectory.split('/')[0]

                filename = l.strip().split('/')[-1]
                pyre_configuration = {
                    "search_path" : [
                        benchmark_path
                    ],
                    "source_directories" : [
                        {"root" : benchmark_path, "subdirectory" : subdirectory}
                    ],
                    "strict" : True,
                    "taint_models_path": ".",
                    "typeshed": "/home/wonseok/Pyinder/stubs/typeshed/typeshed-master"
                }
                
                taint_config = {
                    "sources": [],
                    "sinks": [],
                    "features": [],
                    "rules": []
                }

                with open(pyre_path, 'w+') as pyre_f :
                    pyre_f.write(json.dumps(pyre_configuration, indent=4))

                with open(config_path, 'w+') as pyre_c :
                    pyre_c.write(json.dumps(taint_config, indent=4))

                flag = False
            if 'inputs' in l :
                flag = True
        cfg_f.close()

        print("Done!")

def excepy_run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in excepy_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)
        
        project_name = target_project.split('-')[0]

        benchmark_path = home_path + '/ExcePy_Present/data/' + project_name + "/" + target_project
        # cfg_path = benchmark_path + '/pytype.cfg'
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyre_path = pyre_config + "/" + target_project + '/.pyre_configuration'
        config_path = pyre_config + "/" + target_project + '/.config'

        # cfg_f = open(cfg_path, 'r')
        pyre_configuration = {
            "search_path" : [
                benchmark_path
            ],
            "source_directories" : [
                {"root" : benchmark_path, "subdirectory" : ""}
            ],
            "strict" : True,
            "taint_models_path": ".",
            "typeshed": "/home/wonseok/Pyinder/stubs/typeshed/typeshed-master"
        }
        
        taint_config = {
            "sources": [],
            "sinks": [],
            "features": [],
            "rules": []
        }
        
        with open(pyre_path, 'w+') as pyre_f :
            pyre_f.write(json.dumps(pyre_configuration, indent=4))

        with open(config_path, 'w+') as pyre_c :
            pyre_c.write(json.dumps(taint_config, indent=4))


        print("Done!")

def main(argv) :
    #run()
    #bugsinpy_run()
    excepy_run()

if __name__ == "__main__" :
    main(sys.argv[1:])
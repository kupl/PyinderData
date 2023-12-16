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
    "pandas-41915",
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
        # cfg_path = benchmark_path + '/pytype.cfg'
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pytype_path = pyre_config + "/" + target_project + '/pytype.cfg'

        cfg_f = open(pytype_path, 'r')
        l_list = []
        flag = False
        del_dot = False
        for l in cfg_f.readlines() :
            cand_l = l
            if flag :
                subdirectory = '/'.join(l.strip().split('/')[:-1])[2:]
                # if delete this, then just check specific folder
                subdirectory = subdirectory.split('/')[0]


                include = benchmark_path + '/' + subdirectory

                cand_l = 'inputs = ' + include + '\n'
                subdirectory = include

                flag = False
            if 'inputs' in l :
                if '= /' in l :
                    subdirectory = l.strip().split('=')[1].strip()
                    cand_l = l
                else :
                    flag = True
                    cand_l = ''
            
            if 'jobs' in l :
                cand_l = ''

            if del_dot and '.' == l.strip() :
                cand_l = ''

            if 'pythonpath' in l :
                cand_l = 'pythonpath = ' + subdirectory + '\n'
                del_dot = True

            l_list.append(cand_l)
        cfg_f.close()


        with open(pytype_path, 'w+') as pyright_f :
            pyright_f.write(''.join(l_list))

        print("Done!")
        
def bugsinpy_run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in bugsinpy_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)

        benchmark_path = home_path + '/BugsInPy/benchmark/' + target_project
        # cfg_path = benchmark_path + '/pytype.cfg'
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pytype_path = pyre_config + "/" + target_project + '/pytype.cfg'

        cfg_f = open(pytype_path, 'r')
        l_list = []
        flag = False
        del_dot = False
        for l in cfg_f.readlines() :
            cand_l = l
            if flag :
                subdirectory = '/'.join(l.strip().split('/')[:-1])[2:]
                # if delete this, then just check specific folder
                subdirectory = subdirectory.split('/')[0]


                include = benchmark_path + '/' + subdirectory

                cand_l = 'inputs = ' + include + '\n'
                subdirectory = include

                flag = False
            if 'inputs' in l :
                if '= /' in l :
                    subdirectory = l.strip().split('=')[1].strip()
                    cand_l = l
                else :
                    flag = True
                    cand_l = ''
            
            if 'jobs' in l :
                cand_l = ''

            if del_dot and '.' == l.strip() :
                cand_l = ''

            if 'pythonpath' in l :
                cand_l = 'pythonpath = ' + subdirectory + '\n'
                del_dot = True

            l_list.append(cand_l)
        cfg_f.close()


        with open(pytype_path, 'w+') as pyright_f :
            pyright_f.write(''.join(l_list))

        print("Done!")

def excepy_run() :
    check_directory_and_make_directory(pyre_config)
    for target_project in excepy_projects :
        print(target_project + ' is analyzed... ', end='', flush=True)

        benchmark_path = home_path + '/benchmark/' + target_project
        cfg_path = pyre_config + "/" + target_project + '/pyrightconfig.json'
        check_directory_and_make_directory(pyre_config + "/" + target_project)
        pyre_path = pyre_config + "/" + target_project + '/pytype.cfg'

        with open(cfg_path, 'r') as cfg_f :
            cfg = json.load(cfg_f)
        file = cfg['include'][0]
        flag = False
        mypy_configuration = [
            "[pytype]",
 
            "# Space-separated list of files or directories to exclude.",
            "exclude =",
            "    **/*_test.py",
            "    **/test_*.py",
            "    **/tests",
 
            "# Space-separated list of files or directories to process.",
            "inputs = {}".format(file),
 
            "# Keep going past errors to analyze as many files as possible.",
            "keep_going = True",
 
            "platform = linux",
 
            "# number of CPUs on the host system.",
 
            "# All pytype output goes here.",
            "output = .pytype",
 
            "# Python version (major.minor) of the target code.",
            "python_version = 3.9",
 
            "# Comma or space separated list of error names to ignore.",
            "disable =",
            "    pyi-error",
            "    import-error",
 
            "# Don't report errors.",
            "report_errors = True",
 
            "strict-primitive-comparisons = True",
        ]

        with open(pyre_path, 'w+') as pyre_f :
            pyre_f.write('\n'.join(mypy_configuration))

        cfg_f.close()

        print("Done!")

def main(argv) :
    #run()
    #bugsinpy_run()
    excepy_run()

if __name__ == "__main__" :
    main(sys.argv[1:])
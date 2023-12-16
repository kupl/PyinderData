import sys
import os
import subprocess
import getopt
import json
import ast

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
    "pandas-41915",
    "rasa-8704",
    "requests-3179",
    "requests-3368",
    "salt-33908",
    "salt-38947",
    "salt-50958",
    "salt-52624",
    "salt-53394",
    "salt-54240",
    "salt-54785",
    "salt-56094",
    "salt-56381",
    "sanic-1334",
    "scikitlearn-7259",
    "scikitlearn-8973",
    "scikitlearn-12603",
    "Zappa-388",
]

""" target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-14686",
    "core-8065",
    "core-29829",
    "core-32318",
    "core-38605",
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
    "rasa-8704",
    "requests-3179",
    "salt-33908",
    "salt-54240",
    "salt-54785",
    "salt-56381",
    "sanic-1334",
    "scikitlearn-7259",
    "scikitlearn-8973",
] """

bugsinpy_projects = [
    "ansible-1",
    "keras-34",
    "keras-39",
    "luigi-3",
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
    "tornado-7",
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

pyinder_run_path = '/home/wonseok/pyinder_run'
pyre_path = pyinder_run_path + '/mypy'

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run(skip) :
    check_directory_and_make_directory(pyre_path)
    for target_project in target_projects :
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = pyre_path + '/' + target_project
            result_file = result_path + '/result.json'
            result_file2 = result_path + '/result_.json'

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
            print(e)
            print('Skip')


def bugsinpy_run(skip) :
    check_directory_and_make_directory(pyre_path)
    for target_project in bugsinpy_projects :
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = pyre_path + '/' + target_project
            result_file = result_path + '/result.json'
            result_file2 = result_path + '/result_.json'

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
            print(e)
            print('Skip')

def excepy_run(skip) :
    check_directory_and_make_directory(pyre_path)
    for target_project in excepy_projects :
        try :
            print(target_project + ' is analyzed... ', end='', flush=True)

            result_path = pyre_path + '/' + target_project
            result_file = result_path + '/result.json'
            result_file2 = result_path + '/result_.json'

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
            print(e)
            print('Skip')

def main(argv) :
    skip = False
    try:
        # :가 붙으면 인수를 가지는 옵션
	    opts, args = getopt.getopt(argv, "hs:", ["skip="])
    except getopt.GetoptError:
	    print ('pyre_test.py --skip(or -s) <True/False>')
	    sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print ('pyre_test.py --skip(or -s) <True/False>')
            sys.exit()
        elif opt in ("-s", "--skip"):
            skip = bool(arg)

    run(skip)
    bugsinpy_run(skip)
    excepy_run(skip)

if __name__ == "__main__" :
    main(sys.argv[1:])
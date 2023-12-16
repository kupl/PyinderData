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
    "airflow-14686",
    "beets-3360",
    "core-8065",
    "core-29829",
    "core-32222",
    "core-32318",
    "core-38605",
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
    "Zaapa-388",
]

pyinder_run_path = '/home/wonseok/pyinder_run'
pyre_path = pyinder_run_path + '/pyre'

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run(bench) :
    run_path = pyinder_run_path + '/pyre/' + bench + "/result.json"

    if os.path.isfile(run_path) :
        with open(run_path, 'r') as f :
            error = json.loads(json.load(f))

            pprint(error)

    print('Done!')
        


def main(argv) :
    bench = ""
    try:
        # :가 붙으면 인수를 가지는 옵션
	    opts, args = getopt.getopt(argv, "hb:", ["bench="])
    except getopt.GetoptError:
	    print ('pyre_print.py --bench(or -b) <name>')
	    sys.exit(2)

    for opt, arg in opts:
        if opt == '-h':
            print ('pyre_print.py --bench(or -b) <name>')
            sys.exit()
        elif opt in ("-b", "--bench"):
            bench = arg

    run(bench)

if __name__ == "__main__" :
    main(sys.argv[1:])
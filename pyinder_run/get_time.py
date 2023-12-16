import sys
import os
import subprocess
import argparse
import json
import shutil
import time
import ast

target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
    "airflow-14686",
    "core-8065",
    "core-29829",
    "core-32222",
    "core-32318",
    "core-40034",
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
pyright_path = pyinder_run_path + '/pyright'


def run(skip, project, num) :
    file_name = "mypy_231210.log"
    total_time = 0
    with open(file_name, 'r') as f :
        for t in f.readlines() :
            tt = t.split()
            prj = tt[0]

            if prj not in target_projects + bugsinpy_projects + excepy_projects :
                continue

            time = int(round(float(tt[-2])))

            print("{:<20} {:<4}".format(prj, time))
            total_time += time

    print(len(target_projects + bugsinpy_projects + excepy_projects))
    print(total_time / 75)

def main(argv) :
    parser = argparse.ArgumentParser()
    #parser.add_argument("-s", "--src_dir", dest="src_dir", action="store", required=True, type=Path) 
    parser.add_argument("-p", "--project", action="store", default=None, type=str) 
    parser.add_argument("-n", "--num", action="store", default=None, type=str) 
    parser.add_argument("-s", "--skip", action="store", default=False, type=bool)

    args = parser.parse_args()

    run(args.skip, args.project, args.num)
    #bugsinpy_run(args.skip, args.project, args.num)
    #excepy_run(args.skip, args.project, args.num)

if __name__ == "__main__" :
    main(sys.argv[1:])
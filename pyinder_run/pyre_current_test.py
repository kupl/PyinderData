import sys
import os
import subprocess
import argparse
import json
import shutil
import time

target_projects = [
    "airflow",
    "ansible",
    "beets",
    "core",
    "keras",
    "luigi",
    "pandas",
    "rasa",
    "requests",
    "salt",
    "sanic",
    "scikitlearn",
    "scrapy",
    "spacy",
    "tornado",
]

pyinder_run_path = '/home/wonseok/pyinder_run/current'
pyre_path = pyinder_run_path + '/pyre'

def check_directory_and_make_directory(path) :
    if os.path.exists(path) :
        return

    os.mkdir(path)

def run(skip, project, num) :
    check_directory_and_make_directory(pyre_path)
    for target_project in target_projects :
        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in target_project :
                    continue

        print(target_project + ' is analyzed... ', end='', flush=True)

        config_path = pyinder_run_path + '/config/' + target_project
        result_path = pyre_path + '/' + target_project
        result_file = result_path + '/result.json'
        check_directory_and_make_directory(result_path)

        if skip and os.path.isfile(result_file) :
            print('Skip!')
            continue
        if os.path.isdir('/home/wonseok/benchmark/{}/pyinder_analysis'.format(target_project)) :
            shutil.rmtree('/home/wonseok/benchmark/{}/pyinder_analysis'.format(target_project)) 

        #command = 'PYTHONPATH="/home/wonseok/Pyinder/..:$PYTHONPATH" python -m Pyinder.client.pyre -n --output=json mine'
        command = './run.sh {}'.format(config_path)

        with open(os.devnull) as DEVNULL:
            result = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=os.getcwd())
            timeStarted = time.time()  
            out, err = result.communicate()
            timeDelta = time.time() - timeStarted  

            print("Finished process in "+str(timeDelta)+" seconds.")


        with open(result_file, 'w+') as f :
            json.dump(out.decode('utf-8'), f)
        

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
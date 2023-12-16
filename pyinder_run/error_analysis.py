import sys
import os
import subprocess
import getopt
import json
import ast
import argparse
import itertools
from pathlib import Path
from pprint import pprint

import pickle

'''
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
'''

op_list = []

import operator
import inspect

for op in (inspect.getmembers(operator)) :
    if "__" in op[0] :
        op_list.append(op[0])

real_oper = [
    "__lt__",
    "__le__",
    "__eq__",
    "__ne__",
    "__gt__",
    "__ge__",
    "__add__",
    "__sub__",
    "__mul__",
    "__truediv__",
    "__floordiv__",
    "__mod__",
    "__divmod__",
    "__pow__",
    "__lshift__",
    "__rshift__",
    "__and__",
    "__xor__",
    "__or__",
    "__iadd__",
    "__isub__",
    "__imul__",
    "__itruediv__",
    "__ifloordiv__",
    "__imod__",
    "__ipow__",
    "__ilshift__",
    "__irshift__",
    "__iand__",
    "__ixor__",
    "__ior__",
    "__neg__",
    "__pos__"
]


op_list.append("__iter__")
op_list.append("__next__")
op_list.append("__contains__")
op_list.append("__len__")

primitive_type = ("int", "str", "bytes", "bool", "float", "list", "dict", "tuple", "set")

pyinder_op_msg = set([])
pyright_op_msg = set([])
none_msg = set([])
for op in op_list :
    for p in primitive_type :
        msg = "In call `{}.{}".format(p, op)
        pyinder_op_msg.add(msg)
        

    #     if p in ("list", "dict", "tuple", "set") :
    #         pyinder_op_msg.add("`{}` has no attribute `{}`".format(p.capitalize(), op))
    #         pyinder_op_msg.add("`{}` has no attribute `{}`".format("typing."+p.capitalize(), op))

    #         pyinder_op_msg.add(("Item `{}` of".format(p.capitalize()), "has no attribute `{}`".format(op)))
    #         pyinder_op_msg.add(("Item `{}` of".format("typing."+p.capitalize()), "has no attribute `{}`".format(op)))
    #     else :
    #         pyinder_op_msg.add("`{}` has no attribute `{}`".format(p, op))
    #         pyinder_op_msg.add(("Item `{}` of".format(p), "has no attribute `{}`".format(op)))

    # pyinder_op_msg.add(("Item `None` of", "has no attribute `{}`".format(op)))
    # # pyinder_op_msg.add(("Item `object` of", "has no attribute `{}`".format(op)))

    

    # pyinder_op_msg.add("`None` has no attribute `{}`".format(op))
    # # pyinder_op_msg.add("`object` has no attribute `{}`".format(op))

    # pyinder_op_msg.add("Optional type has no attribute `{}`".format(op))
    # pyinder_op_msg.add("`Optional` has no attribute `{}`".format(op))

    # pyinder_op_msg.add("`None` is not a function")
    # pyinder_op_msg.add((": `Optional", "is not a function"))
    # pyinder_op_msg.add((": `typing.Optional", "is not a function"))
    # # pyinder_op_msg.add("`object` is not a function")

    none_msg.add(("Item `None` of", "has no attribute `{}`".format(op)))
    

    none_msg.add("`None` has no attribute `{}`".format(op))
    

    none_msg.add("Optional type has no attribute `{}`".format(op))
    none_msg.add("`Optional` has no attribute `{}`".format(op))

    #none_msg.add("`None` is not a function")
    #none_msg.add((": `Optional", "is not a function"))
    #none_msg.add((": `typing.Optional", "is not a function"))

    #print(op)
    pyinder_op_msg.add("has no attribute `{}`".format(op))
    # pyinder_op_msg.add("is not a function")
    pyright_op_msg.add("\"{}\" is not present".format(op))
    pyright_op_msg.add("\"{}\" method not defined".format(op))
    


pyinder_op_msg.add("In call `len`")
pyinder_op_msg.add("In call `sorted`")
pyinder_op_msg.add("In call `min`")
pyinder_op_msg.add("In call `max`")
pyinder_op_msg.add("In call `isinstance`")
pyinder_op_msg.add("In call `zip.__new__`,")
pyinder_op_msg.add("In call `map.__new__`,")
pyinder_op_msg.add("In call `filter.__init__`,")

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

run_path = Path('/home/wonseok/pyinder_run')
pyre_path = run_path / 'pyre_231209'
pyre_without_dummy = run_path / 'pyre_231123_no_filter'

benchmark_path = Path('/home/wonseok/benchmark')

def split_typ(typ) :
    typ_list = []
    left = 0
    right = 0
    before = 0
    for i, c in enumerate(typ) :
        if c == '[' :
            left += 1
        elif c == ']' :
            right += 1

        if left == right and c == "," :
            typ_list.append(typ[before:i])
            before = i+1
            
    typ_list.append(typ[before:])

    return typ_list

def change_type_without_union(typ, default) :
    origin = typ
    typ = typ.split('[')[0]

    typ = typ.lower()
    typ = typ.strip()
    if typ.startswith("typing.") :
        typ = typ.split('.')[1]
    
    

    #print(typ)

    if typ in primitive_type :
        return typ
    elif typ in ("optional", "none") :
        return "None"
    elif typ == 'unknown' :
        return "Unknown"
    else :
        return default

def union_change_type(typ, default) :
    origin = typ


    typ = '['.join(typ.split('[')[1:])[:-1]

    
    
    t_cand = split_typ(typ)

    # print(t_cand)

    real = set([])

    for t in t_cand :
        mod_t = change_type_without_union(t, default)
        if mod_t == "Unknown" :
            continue

        real.add(mod_t)

    #print(origin, t_cand, real)

    return real
    

def change_type(typ, default) :
    if isinstance(typ, tuple) :
        return typ
    origin = typ
    typ = typ.split('[')[0]

    typ = typ.lower()
    typ = typ.strip()
    if typ.startswith("typing.") :
        typ = typ.split('.')[1]
    
    if typ in primitive_type :
        return typ
    elif typ in ("optional", "none") :
        return "None"
    elif typ == 'union' :
        t_set = union_change_type(origin, default)
        return ("Union", t_set)
    elif typ == 'unknown' :
        return "Unknown"
    else :

        return default

def inner_to_list(attributes, default="Complex") :
    errors = []
    
    for (obj, attr, e) in attributes :
        #print("attr", attr)

        lower = change_type(attr, default)

        errors.append((lower, obj, e))

    return errors

def attribute_to_list(attributes, default="Complex") :
    operand_errors = []
    attr_errors = []
    
    for (obj, attr, e) in attributes :
        if attr in real_oper :
            if obj == "None" :
                operand_errors.append((obj, attr, e))
            
            else :
                if "has no attribute" in e['description'] :
                    obj = change_type(obj, default)
                    attr_errors.append((obj, attr, e))
                    continue

                other_typ = e['description'].split('`')[-2]

                obj = change_type(obj, default)
                other_typ = change_type(other_typ, default)


                operand_errors.append((obj, other_typ, e))
        else :
            lower = change_type(obj, default)

            attr_errors.append((lower, attr, e))

    return operand_errors, attr_errors

def filter_file(path) :
    if '/tests/' in path :
        return True

    if '/test' in path :
        return True

    if 'test/' in path :
        return True

    if 'tests/' in path :
        return True

    return False

def sort_error(result) :
    new_result = dict()
    for k, v in result.items() :
        error_list = sorted(v['errors'], key=lambda x: (x['line'], x['column'], x['stop_line'], x['stop_column']))
        v['errors'] = error_list

        new_result[k] = v

    return new_result

def pyre_analysis(result) :
    result_dict = dict() # file -> { error_summary : ... / error_list : [ ... ]}

    test = dict()

    equal_error_dict = dict()

    for error in result :
        path = '/'.join(error['path'].split('/')[5:])

        if filter_file(path) :
            continue

        error_summary = result_dict.get(path, dict())
        
        error_list = error_summary.get('errors', [])

        error_info = {
            'file' : path,
            'line' : error['line'], 
            'stop_line' : error['stop_line'], 
            'column' : error['column'],
            'stop_column' : error['stop_column'],
            'description' : error['description'],
            'name' : error['name'],
        }
        
        equal_key = (error['name'], error['description'])
        equal_error_dict[equal_key] = equal_error_dict.get(equal_key, 0) + 1

        test_key = (error['line'], error['stop_line'], error['column'], error['stop_column'])
        test[test_key] = test.get(test_key, 0) + 1

        if test[test_key] == 1 :
            error_list.append(error_info)
            error_summary['errors'] = error_list
            error_summary['num'] = error_summary.get('num', 0) + 1

            result_dict[path] = error_summary

    dup = 0
    real = 0
    for k, v in test.items() :
        dup += v
        real += 1

    #print(dup, real)
    one = []
    two = []
    three = []
    for k, v in equal_error_dict.items() :
        if v == 1 : one.append(k)
        elif v == 2 : two.append(k)
        else : three.append(k)

    #print(len(one) + len(two) + len(three))

    one_result_dict = dict()

    for k, v in result_dict.items() :
        unique_error = list(filter(lambda e : (e['name'], e['description']) in one, v['errors']))

        one_result_dict[k] = {
            "num" : v["num"],
            "errors" : unique_error
        }
   
    #one_result_dict = dict(filter(lambda e : (e[1]['name'], e[1]['description']) in one, result_dict.items()))

    #print(one_result_dict)

    return sort_error(result_dict)

def is_equal_error_on_pyre(left, right) :
    return (
        left['line'] == right['line'] and
        left['stop_line'] == right['stop_line'] and
        left['column'] == right['column'] and
        left['stop_column'] == right['stop_column']
    )

def divide_none(errors) :
    def check_attribute(e) :
        if "`Union`" in e['description'] :
            return False

        if "has no attribute" in e['description'] :
            info = e['description'].split('`')
            attr = info[-2]
            
            return True, "None", attr

        return False, None, None

        if "In call" in e['description'] :
            split = e['description'].split('`')[1]
            info = split.split('.')
            
            if len(info) == 2 :
                return True, info[0], info[1]
            else :
                typ = e['description'].split('`')[-2]
                return True, info[0], typ

        return False, None, None

    def check_call(e) :
        if "`Union`" in e['description'] :
            return False

        if "is not a function" in e['description'] and not ("`typing.Union`" in e['description']):
            return True

        return False
    
    attrs = []
    call = []
    operand = []

    for e in errors :
        flag, obj, attr = check_attribute(e)
        if flag :
            attrs.append((obj, attr, e))
        elif check_call(e) :
            call.append(e)
        else :
            if "`not in`" in e['description'] or "`in`" in e['description'] :
                attrs.append(("None", "__iter__", e))
            else :
                operand.append(e)

    oper, attr = attribute_to_list(attrs, default="None")

    operand.extend(oper)
    attr_error = attr

    return attr_error, call, operand

def divide_errors(errors) :
    def check_attribute(e) :
        if "`Union`" in e['description'] :
            return False

        for m in pyinder_op_msg :
            if isinstance(m, tuple) :
                if all(sub_m in e['description'] for sub_m in m) :
                    return True
            elif m in e['description'] and not ("`typing.Union`" in e['description']):
                #print(e['description'])
                if "has no attribute" in e['description'] :
                    info = e['description'].split('`')
                    obj_type = info[1]
                    attr = info[-2]

                    if obj_type == attr :
                        #print(e['description'])
                        obj_type = "Unknown"

                    return True, obj_type, attr

                if "In call" in e['description'] :
                    split = e['description'].split('`')[1]
                    info = split.split('.')
                    
                    if len(info) == 2 :
                        return True, info[0], info[1]
                    else :
                        typ = e['description'].split('`')[-2]
                        return True, info[0], typ

        return False, None, None

    def check_call(e) :
        if "is not a function" in e['description']:
            typ = e['description'].split('`')[1]
            typ = change_type(typ, "Complex")

            if typ == "None" :
                return True

            if typ in primitive_type :
                return True

        return False
        # if "`Union`" in e['description'] :
        #     return False

        # for m in pyinder_op_msg :
        #     if isinstance(m, tuple) :
        #         if all(sub_m in e['description'] for sub_m in m) :
        #             return True
        #     elif m in e['description'] and not ("`typing.Union`" in e['description']):
        #         #print(e['description'])
        #         if "is not a function" in e['description'] :
        #             return True

        # return False
        
    def check_none(e) :
        for m in none_msg :
            if isinstance(m, tuple) :
                if all(sub_m in e['description'] for sub_m in m) :
                    return True
            elif m in e['description'] :
                return True

        if 'Unsupported operand' in e['name'] and "None" in e['description'] :
            return True

        return False

    def check_arguments(e) :
        if "Too many arguments" in e['description'] and "object.__init__" not in e['description'] :
            return True

        if "Missing argument" in e['description'] and "__init__" not in e['description'] :
            return True

        return False

    operand = []
    attributes = []
    inner = []
    none = []
    call = []
    arguments = []

    for e in errors :
        flag, obj, attr = check_attribute(e)

        if check_none(e) :
            none.append(e)

        elif check_call(e) :
            call.append(e)
        
        elif flag :
            if "__" in attr :
                attributes.append((obj, attr, e))
            else :
                inner.append((obj, attr, e))

        elif check_arguments(e) :
            arguments.append(e)

        elif 'Unsupported operand' in e['name'] :
            if "`not in`" in e['description'] or "`in`" in e['description'] :
                typ = e['description'].split('`')[-2]
                origin = typ

                typ = change_type(typ, "Complex")

                if "None" == typ :
                    none.append(e)
                else :
                    #print("HMM?", origin, typ)
                    attributes.append((typ, "__iter__", e))
            else :
                split = e['description'].split('`')
                typ1, typ2 = split[-4], split[-2]
                typ1 = change_type(typ1, "Complex")
                typ2 = change_type(typ2, "Complex")

                operand.append((typ1, typ2, e))

        else :
            print(e)

    return operand, attributes, inner, none, call, arguments

def get_error_types_pyinder(errors) :
    def check_primitive_call(e) :
        if "`Union`" in e['description'] :
            return False

        for m in pyinder_op_msg :
            if isinstance(m, tuple) :
                if all(sub_m in e['description'] for sub_m in m) :
                    return True
            elif m in e['description'] and not ("`typing.Union`" in e['description']):

                if "In call `sorted`" == m or "In call `len`" == m :
                    typ = e['description'].split('`')[-2].split('[')[0]
                    lower = typ.lower()

                    if lower in ("str", "list", "dict", "tuple", "set") :
                        return False
                    elif "dict" in lower :
                        return False

                elif "In call `min`" == m or "In call `max`" == m :
                    typ = e['description'].split('`')[-2].split('[')[0]
                    lower = typ.lower()

                    if lower == "dict_keys" or lower == "dict_values" :
                        return False

                #print(e['description'])
                return True
        '''
        

        for p in primitive_type :
            msg = "In call `{}".format(p)
            if msg in e['description'] :

                return True
        '''
        return False

    def check_none(e) :
        for m in none_msg :
            if isinstance(m, tuple) :
                if all(sub_m in e['description'] for sub_m in m) :
                    return True
            elif m in e['description'] :
                if "In call `sorted`" == m or "In call `len`" == m :
                    typ = e['description'].split('`')[-2].split('[')[0]
                    lower = typ.lower()

                    if lower in ("str", "list", "dict", "tuple", "set") :
                        return False
                    elif "dict" in lower :
                        return False

                elif "In call `min`" == m or "In call `max`" == m :
                    typ = e['description'].split('`')[-2].split('[')[0]
                    lower = typ.lower()

                    if lower == "dict_keys" or lower == "dict_values" :
                        return False

                return True

        if 'Unsupported operand' in e['name'] and "None" in e['description'] :
            return True

        return False

    def arguments(e) :
        if "Too many arguments" in e['description'] and "object.__init__" not in e['description'] :
            return True
    
        if "Unexpected keyword" in e['description'] and "object.__init__" not in e['description'] :
            return True

        if "Missing argument" in e['description'] and "__init__" not in e['description'] :
            return True

        return False

    def call_error(e) :
        if "is not a function" in e['description']:
            typ = e['description'].split('`')[1]
            typ = change_type(typ, "Complex")

            if typ == "None" :
                return True

            if typ in primitive_type :
                return True

        return False

    true_type_error = [e for e in errors if (not check_none(e)) and ('Unsupported operand' in e['name'] or check_primitive_call(e) or arguments(e) or call_error(e))]
    none_error = [e for e in errors if check_none(e)]
    incompatible = [e for e in errors if  "Incompatible parameter type" in e['name'] and not check_primitive_call(e)]
    awaitable = [e for e in errors if e['name'] == "Incompatible awaitable type"]
    attributes = [e for e in errors if "Undefined attribute" in e['name'] and not check_primitive_call(e) and not check_none(e)]

    return true_type_error, none_error, incompatible, awaitable, attributes

def print_only_pyinder(errors) :
    true_type_error, none_error, incompatible, awaitable, attributes = get_error_types_pyinder(errors)

    l_e, l_t, l_n, l_i, l_await, l_attr, l_other = ( \
        len(errors), \
        len(true_type_error), \
        len(none_error), \
        len(incompatible), \
        len(awaitable), \
        len(attributes), \
        len(true_type_error) + len(none_error) + len(incompatible) + len(awaitable) + len(attributes))

    #assert l_other <= l_e

    def get_per(f) :
        return "({:2}%)".format( round(f * 100) )

    print('{:<10}{:<5}{:<10}{:<5}{:<10}'.format(
        l_e, 
        l_t, get_per(l_t/l_e),
        l_n, get_per(l_n/l_e)),
        end='', flush=True)

def print_pyinder(errors) :
    true_type_error, none_error, incompatible, awaitable, attributes = get_error_types_pyinder(errors)

    l_e, l_t, l_n, l_i, l_await, l_attr, l_other = ( \
        len(errors), \
        len(true_type_error), \
        len(none_error), \
        len(incompatible), \
        len(awaitable), \
        len(attributes), \
        len(true_type_error) + len(none_error) + len(incompatible) + len(awaitable) + len(attributes))

    #assert l_other <= l_e

    def get_per(f) :
        return "({:2}%)".format( round(f * 100) )

    print('{:<10}{:<5}{:<10}{:<5}{:<10}{:<5}{:<10}{:<5}{:<10}{:<5}{:<10}{:<10}'.format(
        l_e, 
        l_t, get_per(l_t/l_e),
        l_n, get_per(l_n/l_e),
        l_i, get_per(l_i/l_e),
        l_await, get_per(l_await/l_e),
        l_attr, get_per(l_attr/l_e),
        l_e - l_other), 
        end='', flush=True)


def to_list(error_json) :
    error_list = []
    for k, v in error_json.items() :
        for e in v['errors'] :
            error_list.append(e)

    return error_list


class ErrorVisitor(ast.NodeVisitor) :
    def __init__(self, error_list) :
        self.all_errors = []
        self.error_list = error_list

        self.func_error_list = []

    def get_func_errors(self, lineno, end_lineno) :
        return list(filter(lambda e : lineno <= e['line'] and e['stop_line'] <= end_lineno, self.error_list))

    def visit_ClassDef(self, node) :
        self.iter_visit(node.body)

        return [], False

    def visit_FunctionDef(self, node) :
        if not self.func_error_list :
            
            self.func_error_list = self.get_func_errors(node.lineno, node.end_lineno)

            e, f = self.iter_visit(node.body)

            self.func_error_list = []

            self.all_errors += e

        return [], False

    def visit_AsyncFunctionDef(self, node) :
        if not self.func_error_list :
            self.func_error_list = self.get_func_errors(node.lineno, node.end_lineno)

            e, f = self.iter_visit(node.body)

            self.func_error_list = []

            self.all_errors += e

        return [], False


    def iter_visit(self, node_list) :
        total_e = []
        for n in node_list :
            e, f = self.visit(n)

            total_e += e
            if f is True and self.func_error_list :
                
                return total_e, True

        return total_e, False

    def generic_visit(self, node) :
        
        if isinstance(node, (ast.Module, ast.Interactive)) :
            return self.iter_visit(node.body)

        if isinstance(node, ast.Expression) :
            return self.visit(node.body)


        e = self.get_error(node.lineno, node.end_lineno)

        if e and self.func_error_list :
            return [e[0]], True

        if isinstance(node, (ast.For, ast.AsyncFor)) :
            e = self.get_error(node.target.lineno, node.target.end_lineno, no_branch=True)

            if e and self.func_error_list :
                return [e[0]], True

            e = self.get_error(node.iter.lineno, node.iter.end_lineno, no_branch=True)

            if e and self.func_error_list :
                return [e[0]], True

            n1, e1 = self.iter_visit(node.body)
            n2, e2 = self.iter_visit(node.orelse)

            if e1 and e2 :
                return n1+n2, True

            e = n1+n2
        
        elif isinstance(node, (ast.While, ast.If)) :
            e = self.get_error(node.test.lineno, node.test.end_lineno, no_branch=True)

            if e and self.func_error_list :
                return [e[0]], True


            n1, e1 = self.iter_visit(node.body)
            n2, e2 = self.iter_visit(node.orelse)

            if e1 and e2 :
                return n1+n2, True

            e = n1+n2

        elif isinstance(node, (ast.Try)) :

            n1, e1 = self.iter_visit(node.body)
            n2, e2 = self.iter_visit(node.handlers)
            n3, e3 = self.iter_visit(node.orelse)
            n4, e4 = self.iter_visit(node.finalbody)

            if e1 and e2 and e3 and e4 :
                return n1+n2+n3+n4, True

            e = n1+n2+n3+n4

        elif isinstance(node, (ast.With, ast.AsyncWith)) :
            n1, e1 = self.iter_visit(node.body)

            if e1 :
                return n1, True

            e = n1
        
        else :
            e = self.get_error(node.lineno, node.end_lineno, no_branch=True)
            
            if e and self.func_error_list :
                return [e[0]], True

        return e, False



    def start(self, node) :
        self.visit(node)

        return self.all_errors

    def get_error(self, lineno, end_lineno, no_branch=False) :
        return list(filter(lambda e : 
        lineno <= e['line'] and e['stop_line'] <= end_lineno if no_branch else lineno == e['line'] and e['stop_line'] <= end_lineno, 
        self.func_error_list))

def run(project, num, detail) :
    total_pyinder_alarm = 0
    total_pyright_alarm = 0

    project_alarm = dict()

    operand_errors = []

    attr_none_errors = [] 
    call_none_errors = []
    operand_none_errors = []

    none_errors = []
    attr_errors = []
    inner_errors = []
    call_errors = []
    argument_errors = []

    for target_project in target_projects + bugsinpy_projects + excepy_projects :
        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in target_project :
                    continue

        

        pyre_json = pyre_path / target_project / 'result_.json'
        pyre_without_dummy_json = pyre_without_dummy / target_project / 'result_.json'
        src_path = benchmark_path / target_project
        #pyright_annotated_path_json = pyright_annotated_path / target_project / 'result.json'

        try :
            with open(pyre_json, 'r') as f :
                pyre_result = pyre_analysis(json.load(f))

            # with open(pyre_without_dummy_json, 'r') as f :
            #    pyre_without_dummy_result = pyre_analysis(json.load(f))

            #with open(pyright_annotated_path_json, 'r') as f : 
            #    pyright_annotated_result = pyright_analysis(json.load(f))

        except Exception as e:
            print(e)
            continue

        origin_len = 0
        total_e = []

        dummy_len = 0
        total_dummy_e = []
        total_errors = []

        

        for file, error in pyre_result.items() :
            errors, none, _, _, _ = get_error_types_pyinder(error['errors'])

            errors = errors + none

            for e in errors :
                e['project'] = target_project 

            total_errors.extend(errors)

            origin_len += len(errors)

            error_visitor = ErrorVisitor(errors)
            # e = error_visitor.start(ast.parse((src_path / file).read_text()))

            # total_e += e

        """ for file, error in pyre_without_dummy_result.items() :
            errors, none_errors, _, _, _ = get_error_types_pyinder(error['errors'])

            errors = errors + none_errors
            dummy_len += len(errors)

            error_visitor = ErrorVisitor(errors)
            # e = error_visitor.start(ast.parse((src_path / file).read_text()))

            # total_dummy_e += e """

        operand, attributes, inner, none, call, arguments = divide_errors(total_errors)

        operand_errors.extend(operand)

        oper_attr, userdefine = attribute_to_list(attributes)

        operand_errors.extend(oper_attr)
        attr_errors.extend(userdefine)

        inner_error = inner_to_list(inner)

        """ attr_analysis = dict()
    
        for (obj, attr) in inner_error :
            obj_dict = attr_analysis.get(attr, {})
            obj_dict[obj] = obj_dict.get(obj, 0) + 1
            attr_analysis[attr] = obj_dict

        pprint(attr_analysis) """

        inner_errors.extend(inner_error)

        attr_none_error, call_none, operand_none = divide_none(none)

        attr_none_errors.extend(attr_none_error)
        call_none_errors.extend(call_none)
        operand_none_errors.extend(operand_none)

        # pprint(operand_errors)

        none_errors.extend(none)
        call_errors.extend(call)
        argument_errors.extend(arguments)

        # attr_analysis = dict()
    
        # for (obj, attr) in attr_errors :
        #     obj_dict = attr_analysis.get(attr, {})
        #     obj_dict[obj] = obj_dict.get(obj, 0) + 1
        #     attr_analysis[attr] = obj_dict

        # for (obj, attr) in attr_none_errors :
        #     obj_dict = attr_analysis.get(attr, {})
        #     obj_dict[obj] = obj_dict.get(obj, 0) + 1
        #     attr_analysis[attr] = obj_dict

        # pprint(attr_analysis)

        # attr_analysis = dict()
        # for (obj, attr) in inner_errors :
        #     obj_dict = attr_analysis.get(attr, {})
        #     obj_dict[obj] = obj_dict.get(obj, 0) + 1
        #     attr_analysis[attr] = obj_dict

        # pprint(attr_analysis)

        # type_dict = dict()
        # for (t1, t2) in operand_errors :
        #     type_dict[t1] = type_dict.get(t1, 0) + 1
        #     type_dict[t2] = type_dict.get(t2, 0) + 1

        # pprint(type_dict)

        # print(len(operand + attributes + inner + none + call + arguments))
        # print(len(total_errors))

        assert len(operand + attributes + inner + none + call + arguments) == len(total_errors)

        print("{:20}{:<6}{:<6}{:<6}{:<6}{:<6}{:<6}{:20}".format(
            target_project,
                len(operand_errors),
                len(attr_errors),
                len(inner_errors),
                len(call_errors),
                len(argument_errors),
                len(none_errors),
                str((len(attr_none_errors), len(call_none_errors), len(operand_none_errors)))
            )
        )

        

    print("{:20}{:<6}{:<6}{:<6}{:<6}{:<6}{:<6}".format(
            "Total",
            len(operand_errors + operand_none_errors),
            len(attr_errors + attr_none_errors),
            len(inner_errors),
            len(call_errors + call_none_errors),
            len(argument_errors),
            len(none_errors)
        )
    )

    all_none_errors = operand_none_errors + attr_none_errors + call_none_errors

    other_errors = operand_errors + attr_errors + inner_errors + call_errors + argument_errors

    with open('excepy_errors.pkl', 'wb') as f :
        pickle.dump(all_none_errors + other_errors, f)

    # with open('other_errors.pkl', 'wb') as f :
    #    pickle.dump(other_errors, f)

    attr_analysis = dict()
    
    for (obj, attr, e) in attr_errors :
        obj_dict = attr_analysis.get(attr, {})
        if isinstance(obj, tuple) :
            for o in obj[1] :
                obj_dict[o] = obj_dict.get(o, 0) + 1
        else :
            obj_dict[obj] = obj_dict.get(obj, 0) + 1
        attr_analysis[attr] = obj_dict

    for (obj, attr, e) in attr_none_errors :
        obj_dict = attr_analysis.get(attr, {})
        if isinstance(obj, tuple) :
            for o in obj[1] :
                obj_dict[o] = obj_dict.get(o, 0) + 1
        else :
            obj_dict[obj] = obj_dict.get(obj, 0) + 1
        attr_analysis[attr] = obj_dict

    attr_list = []
    for k, v in attr_analysis.items() :
        attr_list.append((k, v, sum(v.values())))

    # extract top 3
    attr_list = list(sorted(attr_list, key=lambda x : x[2], reverse=True))

    attr_list, others = attr_list[:3], attr_list[3:]

    attr_analysis = dict()
    for (k, v, s) in attr_list :
        attr_analysis[k] = v
        print(k, s)

    other_n = 0
    for (k, v, s) in others :
        other_n += s

    print(other_n)

    pprint(attr_analysis)

    inner_analysis = dict()
    for (obj, attr, e) in inner_errors :
        obj_dict = inner_analysis.get(attr, {})
        if isinstance(obj, tuple) :
            for o in obj[1] :
                obj_dict[o] = obj_dict.get(o, 0) + 1
        else :
            obj_dict[obj] = obj_dict.get(obj, 0) + 1
        inner_analysis[attr] = obj_dict

    pprint(inner_analysis)

    type_dict = dict()
    for (t1, t2, e) in operand_errors :
        if isinstance(t1, tuple) :
            for t in t1[1] :
                type_dict[t] = type_dict.get(t, 0) + 1
        else :
            type_dict[t1] = type_dict.get(t1, 0) + 1

        if isinstance(t2, tuple) :
            for t in t2[1] :
                type_dict[t] = type_dict.get(t, 0) + 1
        else :
            type_dict[t2] = type_dict.get(t2, 0) + 1

    type_dict['None'] = type_dict.get('None', 0) + len(operand_none_errors)

    pprint(type_dict)

    # Analysis Operator


        # print(target_project, origin_len, "=>", len(total_e))

        # print(
        #     round(1 - (len(total_e) / len(total_dummy_e)), 2), 
        #     round(1 - (origin_len / dummy_len), 2)
        # )

    


def main(argv) :
    parser = argparse.ArgumentParser()
    #parser.add_argument("-s", "--src_dir", dest="src_dir", action="store", required=True, type=Path) 
    parser.add_argument("-p", "--project", action="store", default=None, type=str) 
    parser.add_argument("-n", "--num", action="store", default=None, type=str) 
    parser.add_argument("-d", "--detail", action="store", default=False, type=bool) 

    args = parser.parse_args()

    run(args.project, args.num, args.detail)

if __name__ == "__main__" :
    main(sys.argv[1:])
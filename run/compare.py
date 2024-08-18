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
    "Zappa-388",
]
'''

op_list = []

import operator
import inspect

for op in (inspect.getmembers(operator)) :
    if "__" in op[0] :
        op_list.append(op[0])

print(op_list)

op_list.append("__iter__")
op_list.append("__next__")
op_list.append("__contains__")
op_list.append("__len__")

primitive_type = ("int", "str", "bytes", "bool", "float", "list", "dict", "tuple", "set")

pyinder_op_msg = set([])
pyright_op_msg = set([])
mypy_op_msg = set([])
pytype_op_msg = set([])
pytype_op = set([])
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

    """ none_msg.add(("Item `None` of", "has no attribute `{}`".format(op)))
    

    none_msg.add("`None` has no attribute `{}`".format(op))
    

    none_msg.add("Optional type has no attribute `{}`".format(op))
    none_msg.add("`Optional` has no attribute `{}`".format(op))

    none_msg.add("`None` is not a function")
    none_msg.add((": `Optional", "is not a function"))
    none_msg.add((": `typing.Optional", "is not a function")) """

    #print(op)
    pyinder_op_msg.add("has no attribute `{}`".format(op))
    pyinder_op_msg.add("is not a function")
    pyright_op_msg.add("\"{}\" is not present".format(op))
    pyright_op_msg.add("\"{}\" method not defined".format(op))

    mypy_op_msg.add("has no attribute \"{}\"".format(op))

    pytype_op_msg.add("No attribute '{}'".format(op))

pyinder_op_msg.add("In call `len`")
pyinder_op_msg.add("In call `sorted`")
pyinder_op_msg.add("In call `min`")
pyinder_op_msg.add("In call `max`")
pyinder_op_msg.add("In call `set")
pyinder_op_msg.add("In call `isinstance`")
pyinder_op_msg.add("In call `zip.__new__`,")
pyinder_op_msg.add("In call `map.__new__`,")
pyinder_op_msg.add("In call `filter.__init__`,")
pyinder_op_msg.add("Unexpected keyword argument")
pyinder_op_msg.add("`str` has no attribute `decode`")
pyinder_op_msg.add("`bytes` has no attribute `encode`")
# pyinder_op_msg.add("Missing argument")
# pyinder_op_msg.add("Too many arguments")

pyright_op_msg.add("in function \"len\"")
pyright_op_msg.add("in function \"sorted\"")
pyright_op_msg.add("in function \"min\"")
pyright_op_msg.add("in function \"max\"")
pyright_op_msg.add("in function \"set\"")
pyright_op_msg.add("in function \"isinstance\"")
pyright_op_msg.add("in function \"zip\"")
pyright_op_msg.add("in function \"map\"")
pyright_op_msg.add("in function \"filter\"")
pyright_op_msg.add("Function accepts too many positional parameters")
pyright_op_msg.add("Arguments missing for parameters")
pyright_op_msg.add("No parameter named")
pyright_op_msg.add("Cannot access member \"decode\" for type \"str\"")
pyright_op_msg.add("Cannot access member \"encode\" for type \"bytes\"")

mypy_op_msg.add("not callable")
mypy_op_msg.add("Unsupported operand types")
mypy_op_msg.add("Missing positional argument")
mypy_op_msg.add("Unexpected keyword argument")
mypy_op_msg.add("\"len\" has incompatible type")
mypy_op_msg.add("\"sorted\" has incompatible type")
mypy_op_msg.add("\"min\" has incompatible type")
mypy_op_msg.add("\"max\" has incompatible type")
mypy_op_msg.add("is not indexable")
mypy_op_msg.add("Unsupported target for indexed assignment")
mypy_op_msg.add("Too many arguments")
mypy_op_msg.add("Unsupported right operand type")
mypy_op_msg.add("Unsupported left operand type")
mypy_op_msg.add("No overload variant")
mypy_op_msg.add("incompatible with supertype")

pytype_op_msg.add("Built-in function")
pytype_op.add("unsupported-operands")
pytype_op.add("missing-parameter")
pytype_op.add("wrong-arg-count")
pytype_op.add("wrong-keyword-args")
pytype_op.add("wrong-arg-types")
pytype_op.add("not-callable")
pytype_op.add("bad-return-type")

target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
    "airflow-14513",
    "airflow-14686",
    "beets-3360",
    "core-8065",
    "core-21734",
    "core-29829",
    "core-32222",
    "core-32318",
    "core-40034",
    "kivy-6954",
    "luigi-1836",
    "pandas-17609",
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
    "requests-3390",
    "requests-4723",
    "salt-33908",
    "salt-38947",
    "salt-52624",
    "salt-53394",
    "salt-54240",
    "salt-54785",
    "salt-56381",
    "sanic-1334",
    "sanic-2008",
    "scikitlearn-7259",
    "scikitlearn-8973",
    "scikitlearn-12603",
    "Zappa-388",
    "ansible-1",
    "keras-34",
    "keras-39",
    "luigi-4",
    "luigi-14",
    "pandas-49",
    "pandas-57",
    "pandas-158",
    "scrapy-2",
    "scrapy-20",
    "scrapy-30",
    "spacy-5",
    "tqdm-3",
    "youtubedl-16",
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

# new
target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
    # "airflow-14513",
    "airflow-14686",
    "beets-3360",
    "core-8065",
    "core-21734",
    "core-29829",
    "core-32222",
    "core-32318",
    "core-40034",
    "kivy-6954",
    "luigi-1836",
    "pandas-17609",
    "pandas-21540",
    "pandas-22378",
    "pandas-22804",
    "pandas-24572",
    "pandas-28412",
    # "pandas-30532",
    "pandas-36950",
    "pandas-37547",
    "pandas-38431",
    "pandas-39028-1",
    "pandas-41915",
    # "rasa-8704",
    "requests-3179",
    "requests-3390",
    "requests-4723",
    "salt-33908",
    "salt-38947",
    "salt-52624",
    "salt-53394",
    "salt-54240",
    "salt-54785",
    "salt-56381",
    "sanic-1334",
    # "sanic-2008",
    "scikitlearn-7259",
    "scikitlearn-8973",
    "scikitlearn-12603",
    "Zappa-388",
    "ansible-1",
    "keras-34",
    "keras-39",
    "luigi-4",
    "luigi-14",
    "pandas-49",
    "pandas-57",
    "pandas-158",
    "scrapy-1",
    "scrapy-2",
    "spacy-5",
    # "tqdm-3",
    #"youtubedl-11",
    #"youtubedl-16",
    "matplotlib-3",
    "matplotlib-7",
    "matplotlib-8",
    "matplotlib-10",
    "numpy-8",
    "Pillow-14",
    "Pillow-15",
    "scipy-5",
    "sympy-5",
    "sympy-6",
    "sympy-36",
    "sympy-37",
    "sympy-40",
    "sympy-42",
    "sympy-43",
    "sympy-44",
]

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
    elif typ == 'unknown' :
        return "Unknown"
    else :

        return default

run_path = Path('/home/wonseok/pyinder_run')
pyre_path = run_path / 'pyre' # 'pyre_0516' 
pyre_not_known_path = run_path / 'pyre_231211_no_filter'
pyre_without_dummy_path = run_path / 'important_stats/pyre_0523_no_dict' # 'important_stats/pyre_no_filter_0515'
pyre_without_score = run_path / 'important_stats/pyre_value_0523' # 'pyre_no_repeat'
real_pyre_path = run_path / 'real_pyre_result_0419'
pyright_path = run_path / 'pyright'
mypy_path = run_path / 'mypy'
pytype_path = run_path / 'pytype'
pyright_annotated_path = run_path / 'pyright_annotated'

def filter_file(path) :
    if '/tests/' in path :
        return True

    if '/test' in path :
        return True

    if 'test/' in path :
        return True

    if 'tests/' in path :
        return True

    if 'sympy' in path :
        if 'miscellaneous' in path :
            return True

        if 'benchmarks' in path :
            return True

        if 'rubi' in path :
            return True

        if 'rubi' in path :
            return True

        if 'hyperexpand' in path :
            return True

    if 'cpython' in path :
        if 'etree' in path :
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

def pyright_analysis(result) :
    result_dict = dict() # file -> { error_summary : ... / error_list : [ ... ]}

    for error in result["generalDiagnostics"] :
        if error['severity'] != 'error' :
            continue

        
        try :
            path = '/'.join(error['file'].split('/')[5:])
        except :
            path = '/'.join(error['uri']["_filePath"].split('/')[5:])

        if filter_file(path) :
            continue

        error_summary = result_dict.get(path, dict())
        error_summary['num'] = error_summary.get('num', 0) + 1
        error_list = error_summary.get('errors', [])

        error_info = {
            'file' : path,
            'line' : error['range']['start']['line'], 
            'stop_line' : error['range']['end']['line'], 
            'column' : error['range']['start']['character'],
            'stop_column' : error['range']['end']['character'],
            'description' : error['message'],
            'name' : error['rule'] if "rule" in error else "other",
        } 
        error_list.append(error_info)

        error_summary['errors'] = error_list

        result_dict[path] = error_summary


    return sort_error(result_dict)

def is_equal_error(left, right) :
    return (
        left['line'] == right['line']+1 and
        left['stop_line'] == right['stop_line']+1 and
        left['column'] == right['column'] and
        left['stop_column'] == right['stop_column']
    )

def is_equal_error_on_pyre(left, right) :
    return (
        left['line'] == right['line'] and
        left['stop_line'] == right['stop_line'] and
        left['column'] == right['column'] and
        left['stop_column'] == right['stop_column']
    )


def get_error_types_pyinder(errors) :
    def check_primitive_call(e) :
        if "`Union`" in e['description'] :
            return False

        for m in pyinder_op_msg :
            if isinstance(m, tuple) :
                if all(sub_m in e['description'] for sub_m in m) :
                    return True
            elif m in e['description'] and not ("`typing.Union`" in e['description']):

                #return True

                # if "In call `sorted`" == m or "In call `len`" == m :
                #     typ = e['description'].split('`')[-2].split('[')[0]
                #     lower = typ.lower()

                #     if lower in ("str", "list", "dict", "tuple", "set") :
                #         return False
                #     elif "dict" in lower :
                #         return False

                # elif "In call `min`" == m or "In call `max`" == m :
                #     typ = e['description'].split('`')[-2].split('[')[0]
                #     lower = typ.lower()

                #     if lower == "dict_keys" or lower == "dict_values" :
                #         return False

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
                # if "In call `sorted`" == m or "In call `len`" == m :
                #     typ = e['description'].split('`')[-2].split('[')[0]
                #     lower = typ.lower()

                #     if lower in ("str", "list", "dict", "tuple", "set") :
                #         return False
                #     elif "dict" in lower :
                #         return False

                # elif "In call `min`" == m or "In call `max`" == m :
                #     typ = e['description'].split('`')[-2].split('[')[0]
                #     lower = typ.lower()

                #     if lower == "dict_keys" or lower == "dict_values" :
                #         return False

                return True

        if 'Unsupported operand' in e['name'] and "None" in e['description'] :
            return True

        return False

    def arguments(e) :
        if "Too many arguments" in e['description'] : # and "object.__init__" not in e['description'] :
            return True

        if "Missing argument" in e['description'] : # and "__init__" not in e['description'] :
            return True

        return False

    """ def call_error(e) :
        if "is not a function" in e['description']:
            typ = e['description'].split('`')[1]
            typ = change_type(typ, "Complex")

            if typ == "None" :
                return True

            if typ in primitive_type :
                return True

        return False """
    
    true_type_error = [e for e in errors if (not check_none(e)) and ('Unsupported operand' in e['name'] or check_primitive_call(e) or arguments(e))]
    none_error = [e for e in errors if check_none(e)]
    incompatible = [e for e in errors if  ("Incompatible parameter type" in e['name'] or "Incompatible return type" in e['name']) and not check_primitive_call(e)]
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

    if l_e == 0 :
        l_e = 1

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


def get_error_types_pyright(errors) :
    def return_desc(e) :
        if 'other_description' in e :
            desc = e['other_description']
        else :
            desc = e['description']

        return desc

    def check_type_error(e) :
        desc = return_desc(e)

        for m in pyright_op_msg :
            if m in desc :
                return True

        # if "Argument missing for parameter" in desc :
        #    return True

        # if "in function \"__getitem__\"" in desc :
        #    return True

        # if "in function \"__setitem__\"" in desc and not "assigned to parameter \"__v\"" in desc :
        #    return True

        return False

    def return_name(e) :
        if 'other_name' in e :
            desc = e['other_name']
        else :
            desc = e['name']

        return desc

    def check_none(e) :
        if "reportOptional" in return_name(e) and \
            "reportOptionalMemberAccess" not in return_name(e) and \
            "reportOptionalIterable" not in return_name(e):
            return True

        return False

 


    #def check_none_member(e) :
    #    if "reportOptionalMemberAccess" in return_name(e):
    #        return True
    #
    #    return False

    true_type_error = [e for e in errors if ('not supported for' in return_desc(e) or check_type_error(e)) and not check_none(e)]
    none_error = [e for e in errors if (check_none(e))]

    # pprint(true_type_error)
    # exit()

    incompatible = [e for e in errors if ("Argument of type" in return_desc(e) or "cannot be assigned to return type" in return_desc(e)) and not check_none(e) ]

    awaitable = [e for e in errors if 'is not awaitable' in return_desc(e) and not check_none(e)]
    attributes = [
        e for e in errors if ("method not defined on type" in return_desc(e) or "Cannot access member" in return_desc(e) or "is not a known member of" in return_desc(e))
        and not check_none(e)
    ]

    return true_type_error, none_error, incompatible, awaitable, attributes

def print_only_pyright(errors) :
    true_type_error, none_error, incompatible, awaitable, attributes = get_error_types_pyright(errors)

    l_e, l_t, l_n, l_i, l_await, l_attr, l_other = ( \
        len(errors), \
        len(true_type_error), \
        len(none_error), \
        len(incompatible), \
        len(awaitable), \
        len(attributes), \
        len(true_type_error) + len(incompatible) + len(awaitable) + len(attributes))

    def get_per(f) :
        return "({:2}%)".format( round(f * 100) )

    if l_e == 0 :
        l_e = 1

    print('{:<10}{:<5}{:<10}{:<5}{:<10}'.format(
        l_e, 
        l_t, get_per(l_t/l_e),
        l_n, get_per(l_n/l_e)), 
        end='', flush=True)

def print_pyright(errors) :
    true_type_error, none_error, incompatible, awaitable, attributes = get_error_types_pyright(errors)

    l_e, l_t, l_n, l_i, l_await, l_attr, l_other = ( \
        len(errors), \
        len(true_type_error), \
        len(none_error), \
        len(incompatible), \
        len(awaitable), \
        len(attributes), \
        len(true_type_error) + len(incompatible) + len(awaitable) + len(attributes))

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

def get_error_types_mypy(errors) :
    def return_desc(e) :
        return e['error'].strip()

    def check_type_error(e) :
        desc = return_desc(e)

        if '[arg-type]' in desc:
            return True
    
        if 'has incompatible type' in desc:
            return True
        
        if 'return value type' in desc:
            return True
        
        if '[operator]' in desc:
            return True

        for m in mypy_op_msg :
            if m in desc :
                return True

        return False

    #def check_none_member(e) :
    #    if "reportOptionalMemberAccess" in return_name(e):
    #        return True
    #
    #    return False

    true_type_error = [e for e in errors if check_type_error(e)]

    return true_type_error



def get_error_types_pytype(errors) :
    def return_desc(e) :
        return e['error'].strip()

    def check_type_error(e) :
        desc = return_desc(e)

        for m in pytype_op_msg :
            if m in desc :
                return True

        for m in pytype_op :
            if m in e['op'] :
                return True

        return False

    #def check_none_member(e) :
    #    if "reportOptionalMemberAccess" in return_name(e):
    #        return True
    #
    #    return False

    true_type_error = [e for e in errors if check_type_error(e)]

    return true_type_error

def to_list(error_json) :
    error_list = []
    for k, v in error_json.items() :
        for e in v['errors'] :
            error_list.append(e)

    return error_list

def to_list(error_json) :
    error_list = []
    for k, v in error_json.items() :
        for e in v['errors'] :
            error_list.append(e)

    return error_list



def compare(left, right) :
    compare_dict = dict()

    for k, v in left.items() :
        left_errors = v['errors']
        right_errors = right.get(k, dict()).get('errors', [])

        inter_errors = []
        only_left_errors = []
        only_right_errors = []
        specific_errors = []
        checked_right_errors = []
        for left_error in left_errors :
            is_find = False
            for i, right_error in enumerate(right_errors) :
                if is_equal_error(left_error, right_error) :
                    checked_right_errors.append(i)
                    left_error['other_description'] = right_error['description']
                    left_error['other_name'] = right_error['name']
                    inter_errors.append(left_error)
                    is_find = True

            if not is_find :
                only_left_errors.append(left_error)

        for i, right_error in enumerate(right_errors) :
            if i in checked_right_errors :
                continue

        
            only_right_errors.append(right_error)

            
        compare_dict[k] = {
            'left': only_left_errors,
            'right': only_right_errors,
            'inter': inter_errors,
        }

    right_only = { k : right[k] for k in set(right) - set(left) }

    for k, v in right_only.items() :
        errors = []
        specific = []

        for e in v['errors'] : 
            errors.append(e)

        compare_dict[k] = {
            'left' : [],
            'right' : errors,
            'inter' : []
        }


    return compare_dict


def compare_pyre(prev, next) :
    remain = []

    for n in next :
        is_find = False
        for p in prev :
            if is_equal_error_on_pyre(p, n) :
                is_find = True
                break

        if not is_find :
            remain.append(n)

    return remain

def run(project, num, detail) :

    #print('{:<20}{:<10}{:<15}{:<15}{:<15}{:<15}{:<15}{:<10}{:<10}{:<15}{:<15}{:<15}{:<15}{:<15}{:<10}'.format("Benchmark", "Pyinder", "Operator", "None", "Parameter", "Await", "Attrs", "Other", "Pyright", "Operator", "None", "Parameter", "Await", "Attrs", "Other"))

    print(len(target_projects))

    print('{:<20}{:<10}{:<15}{:<15}{:<10}{:<15}{:<15}{:<10}{:<15}{:<15}'.format("Benchmark", "Pyinder", "Operator", "None", "W/O Dummy", "Operator", "None", "Pyright", "Operator", "None"))

    total_pyinder_alarm = 0
    total_pyright_alarm = 0

    all_pyright = []
    all_pyinder = []
    filter_pyinder = []

    project_alarm = dict()
    baseline_alarm = dict()
    noscore_alarm = dict()
    real_pyre_alarm = dict()
    pyright_alarm = dict()
    mypy_alarm = dict()
    pytype_alarm = dict()
    kloc = dict()
    project_num = dict()

    project_set = set([])
    for target_project in target_projects :
        # if not ("sympy" in target_project) :
        #    continue

        if project :
            if num :
                if target_project != "{}-{}".format(project, num) :
                    continue 
            else :
                if project not in target_project :
                    continue

        """ if "youtube" not in target_project:
            continue """

        

        pyre_json = pyre_path / target_project / 'result_.json'
        pyre_not_known_json = pyre_not_known_path / target_project / 'result_.json' 
        pyre_without_dummy_json = pyre_without_dummy_path / target_project / 'result_.json'
        pyre_without_score_json = pyre_without_score / target_project / 'result_.json'
        real_pyre_json = real_pyre_path / target_project / 'result_.json'
        pyright_json = pyright_path / target_project / 'result.json'

        mypy_json = mypy_path / target_project / 'result_.json'
        pytype_json = pytype_path / target_project / 'result_.json'
        #pyright_annotated_path_json = pyright_annotated_path / target_project / 'result.json'

        try :
            with open(pyre_json, 'r') as f :
                pyre_result = pyre_analysis(json.load(f))

            try:
                with open(pyre_not_known_json, 'r') as f :
                    pyre_not_known_result = pyre_analysis(json.load(f))
            except :
                pyre_not_known_result = {}

            try :
                with open(pyre_without_dummy_json, 'r') as f :
                    pyre_without_dummy_result = pyre_analysis(json.load(f))
            except :
                pyre_without_dummy_result = {}
            
            try:
                with open(pyre_without_score_json, 'r') as f :
                    pyre_without_score_result = pyre_analysis(json.load(f))
            except :
                pyre_without_score_result = {}

            try :
                with open(real_pyre_json, 'r') as f :
                    real_pyre_result = pyre_analysis(json.load(f))
            except :
                real_pyre_result = {}

            try :
                with open(pyright_json, 'r') as f :
                    pyright_result = pyright_analysis(json.load(f))
            except Exception as e:
                print(e)
                pyright_result = {}

            try :
                with open(mypy_json, 'r') as f :
                    mypy_result = json.load(f)
                    new_list = []

                    for e in mypy_result :
                        if filter_file(e['file']) :
                            continue

                        new_list.append(e)

                    mypy_result = new_list
            except :
                mypy_result = None

            try :
                with open(pytype_json, 'r') as f :
                    pytype_result = json.load(f)
            except :
                pytype_result = []

            #with open(pyright_annotated_path_json, 'r') as f : 
            #    pyright_annotated_result = pyright_analysis(json.load(f))

            with open(Path('/home/wonseok/pyinder_test/cloc') / (target_project + '.json')) as f :
                cloc_result = json.load(f)["SUM"]["code"]
        except Exception as e:
            print(e)
            continue

        project_set.add(target_project.split('-')[0])

        total_pyinder = 0
        total_pyright = 0
        total_specific = 0
        total_inter = 0

        compare_dict = compare(pyre_result, pyright_result)

        pyinder_list = []
        pyright_list = []
        inter_list = []

        for k, v in compare_dict.items() :
            left = v['left']
            right = v['right']
            inter = v['inter']

            pyinder_list.extend(left+inter)
            pyright_list.extend(right+inter)
            inter_list.extend(inter)

            total_pyinder += len(left) + len(inter)
            total_pyright += len(right) + len(inter)
            total_inter += len(inter)

        print('{:<20}'.format(target_project), end='', flush=True)
        
        pyinder_list = to_list(pyre_result)
        pyinder_not_known_list = to_list(pyre_not_known_result)
        pyinder_without_dummy_list = to_list(pyre_without_dummy_result)
        pyinder_without_score_list = to_list(pyre_without_score_result)
        real_pyre_list = to_list(real_pyre_result)
        pyright_list = to_list(pyright_result)
        mypy_list = mypy_result
        pytype_list = pytype_result

        

        #pyright_annotated_list = to_list(pyright_annotated_result)

        print_only_pyinder(pyinder_list)
        print_only_pyinder(pyinder_without_dummy_list)

        print_only_pyright(pyright_list)
        #print_only_pyright(pyright_annotated_list)
        
        #print_pyinder(pyinder_list)
        #print_pyright(pyright_list)

        

        total_pyinder_alarm += total_pyinder
        total_pyright_alarm += total_pyright

        total_pyinder = 0
        total_pyright = 0

        if detail :
            pyinder_true_type_error, pyinder_none_error, pyinder_incompatible, pyinder_awaitable, pyinder_attributes = get_error_types_pyinder(pyinder_list)

            without_dummy_true_type_error, without_dummy_none_error, without_dummy_incompatibale, without_dummy_awaitable, without_dummy_attributes = get_error_types_pyinder(pyinder_without_dummy_list)

            pyright_true_type_error, none_error, pyright_incompatible, pyright_awaitable, pyright_attributes = get_error_types_pyright(pyright_list)

            print("{:<5} vs {:<5} ( {:<2.0%} )".format(len(pyinder_true_type_error), len(pyright_true_type_error), round((len(pyinder_true_type_error) / len(pyright_true_type_error)) - 1, 2)), end="", flush=True)
            
            print()

            '''
            new_pyright_true_type_error = []
            for v in pyright_true_type_error :
                if 'other_description' in v :
                    continue
                
                new_pyright_true_type_error.append(v)
            '''
            """ file_dict = dict()
            for v in pyinder_true_type_error :
                flag = True
                for w in without_dummy_true_type_error :
                    if is_equal_error_on_pyre(v, w) :
                        flag = False
                        break

                if flag:
                    pprint(v)
                    file_dict[v['file']] = file_dict.get(v['file'], 0) + 1

            pprint(file_dict, sort_dicts=False)

            exit() """

            pprint(pyinder_true_type_error + pyinder_none_error + pyinder_incompatible)

            file_dict = dict()
            for v in pyinder_true_type_error + pyinder_none_error + pyinder_incompatible :
                file_dict[v['file']] = file_dict.get(v['file'], 0) + 1

            file_dict = dict(sorted(file_dict.items() , key=lambda x : x[1]))
            pprint(file_dict, sort_dicts=False)
            print(sum(file_dict.values()))

            print("HMM")
            print(len(pyinder_incompatible), len(pyinder_awaitable), len(pyinder_attributes))
            print(len(without_dummy_incompatibale), len(without_dummy_awaitable), len(without_dummy_attributes))

            exit()


            '''
            print()
            pyinder_true_type_error, none_error, pyinder_incompatible, pyinder_awaitable, pyinder_attributes = get_error_types_pyinder(inter_list)

            pyright_true_type_error, none_error, pyright_incompatible, pyright_awaitable, pyright_attributes = get_error_types_pyright(inter_list)
            print(len(pyinder_true_type_error), len(pyinder_incompatible), len(pyinder_awaitable), len(pyinder_attributes))
            print(len(pyright_true_type_error), len(pyright_incompatible), len(pyright_awaitable), len(pyright_attributes))

            #pprint(pyright_true_type_error)
            for e in pyright_true_type_error :
                if e not in pyinder_true_type_error :
                    pprint(e)
            #for e in pyinder_true_type_error :
            #    if e not in pyright_true_type_error :
            #        pprint(e)
            '''
        pyinder_true_type_error, pyinder_none_error, pyinder_incompatible, pyinder_awaitable, pyinder_attributes = get_error_types_pyinder(pyinder_list)
        # not_known_true_type_error, not_known_none_error,_,_, _ = get_error_types_pyinder(pyinder_not_known_list)
        without_dummy_true_type_error, without_dummy_none_error, without_dummy_incompatible, _, without_dummy_attributes = get_error_types_pyinder(pyinder_without_dummy_list)
        without_score_true_type_error, without_score_none_error, without_score_incompatible, _, _ = get_error_types_pyinder(pyinder_without_score_list)

        real_pyre_true_type_error, real_pyre_none_error, real_pyre_incompatible, _, _ = get_error_types_pyinder(real_pyre_list)

        pyright_true_type_error, pyright_none_error, pyright_incompatible, pyright_awaitable, pyright_attributes = get_error_types_pyright(pyright_list)

        if mypy_list :
            if len(mypy_list) == 1 and mypy_list[0]["error"].strip() == "invalid syntax" :
                mypy_list = None
            else :
                mypy_true_type_error = get_error_types_mypy(mypy_list)
        else :
            mypy_true_type_error = mypy_list
        
        #pyright_annotated_true_type_error, pyright_annotated_none_error, pyright_annotated_incompatible, #pyright_annotated_awaitable, pyright_annotated_attributes = get_error_types_pyright(pyright_annotated_list)
        pytype_true_type_error = get_error_types_pytype(pytype_list)

        pyinder_errors = pyinder_true_type_error + pyinder_none_error + pyinder_incompatible
        pyright_errors = pyright_true_type_error + pyright_none_error + pyright_incompatible
        real_pyre_errors = real_pyre_true_type_error + real_pyre_none_error + real_pyre_incompatible
        without_dummy_errors = without_dummy_true_type_error + without_dummy_none_error + without_dummy_incompatible
        without_score_errors = without_score_true_type_error + without_score_none_error + without_score_incompatible

        diff = compare_pyre(pyinder_errors, without_dummy_errors)
        # dict_diff = compare_pyre(without_score_errors, pyinder_errors)
        # diff = compare_pyre(diff, dict_diff)
        
        """ diff = compare_pyre(pyinder_errors, real_pyre_errors)
        print(diff, " ", end="") """

        pyinder_line = dict()
        pyright_line = dict()

        for v in pyinder_errors :
            pyinder_line[v['line']] = True

        for v in pyright_errors :
            pyright_line[v['line']] = True

        common_errors = 0

        for k, v in pyinder_line.items() :
            if (k-1) in pyright_line :
                common_errors += 1

        # print(len(pyinder_line), len(pyright_line), common_errors)

        project_name = target_project.split('-')[0]

        kloc[project_name] = (kloc.get(project_name, 0) + cloc_result / 1000) 

        error_dict = project_alarm.get(project_name, dict())
        error_dict['type_error'] = error_dict.get('type_error', 0) + len(pyinder_true_type_error) + len(pyinder_incompatible)
        error_dict['none_error'] = error_dict.get('none_error', 0) + len(pyinder_none_error)
        project_alarm[project_name] = error_dict 

        error_dict = baseline_alarm.get(project_name, dict())
        error_dict['type_error'] = error_dict.get('type_error', 0) + len(without_dummy_true_type_error) + len(without_dummy_incompatible)
        error_dict['none_error'] = error_dict.get('none_error', 0) + len(without_dummy_none_error)
        baseline_alarm[project_name] = error_dict 
        

        error_dict = noscore_alarm.get(project_name, dict())
        error_dict['type_error'] = error_dict.get('type_error', 0) + len(without_score_true_type_error) + len(without_score_incompatible)
        error_dict['none_error'] = error_dict.get('none_error', 0) + len(without_score_none_error)
        noscore_alarm[project_name] = error_dict 

        error_dict = real_pyre_alarm.get(project_name, dict())
        error_dict['type_error'] = error_dict.get('type_error', 0) + len(real_pyre_true_type_error) + len(real_pyre_incompatible)
        error_dict['none_error'] = error_dict.get('none_error', 0) + len(real_pyre_none_error)
        real_pyre_alarm[project_name] = error_dict

        error_dict = pyright_alarm.get(project_name, dict())
        error_dict['type_error'] = error_dict.get('type_error', 0) + len(pyright_true_type_error) + len(pyright_incompatible)
        error_dict['none_error'] = error_dict.get('none_error', 0) + len(pyright_none_error)

        for p in pyright_true_type_error + pyright_none_error + pyright_incompatible :
            p['project'] = target_project
            all_pyright.append(p)

        for p in pyinder_true_type_error + pyinder_none_error + pyinder_incompatible :
            p['project'] = target_project
            all_pyinder.append(p)

        for d in diff:
            d['project'] = target_project
            filter_pyinder.append(d)
        

        pyright_alarm[project_name] = error_dict 

        error_dict = mypy_alarm.get(project_name, dict())
        if mypy_list is not None :
            error_dict['type_error'] = error_dict.get('type_error', 0) + len(mypy_true_type_error)
            error_dict['none_error'] = error_dict.get('none_error', 0)
            error_dict['num'] = error_dict.get('num', 0) + 1
        mypy_alarm[project_name] = error_dict 

        error_dict = pytype_alarm.get(project_name, dict())
        error_dict['type_error'] = error_dict.get('type_error', 0) + len(pytype_true_type_error)
        error_dict['none_error'] = error_dict.get('none_error', 0)
        error_dict['num'] = error_dict.get('num', 0) + 1
        pytype_alarm[project_name] = error_dict

        project_num[project_name] = project_num.get(project_name, 0) + 1

        without = len(without_dummy_true_type_error) + len(without_dummy_none_error) + len(without_dummy_incompatible)

        print("{:<5}{:<5}{:<5}{:<5}{:<5}{:<5}{:<5}{:<5}{:<5}{:<5}".format(
                round(cloc_result / 1000),
                len(mypy_true_type_error) if mypy_list is not None else -1,
                len(pytype_true_type_error),
                round((len(real_pyre_errors))),
                round((len(pyright_errors))),
                round((len(pyinder_errors))),
                round((len(pyinder_errors)) / cloc_result*1000, 2),
                len(without_score_errors),
                round(without, 2),
                
                round((1 - (len(pyinder_errors) / max(without, 1))) * 100),
                #round((len(pyright_annotated_true_type_error) + len(pyright_annotated_none_error)), 2),
            ))
        #print()
        """
        # print_errors_of_file
        if detail :
            for k, v in pyre_result.items() :
                pyre_num = v['num']
                pyright_num = pyright_result.get(k, dict()).get('num', 0)

                total_pyinder += pyre_num
                total_pyright += pyright_num
                print('{:<10}{:<10}{}'.format(pyre_num, pyright_num, k))

            pyright_only = { k : pyright_result[k] for k in set(pyright_result) - set(pyre_result) }

            for k, v in pyright_only.items() :
                pyright_num = v['num']
                total_pyright += pyright_num
                print('{:<10}{:<10}{}'.format(0, pyright_num, k))
        """

    total_kloc = 0
    total_project_alarm = 0
    total_baseline_alarm = 0
    total_noscore_alarm = 0
    total_real_pyre_alarm = 0
    total_pyright_alarm = 0
    total_mypy_alarm = 0
    total_pytype_alarm = 0

    per_bench_baseline_alarm = 0
    per_bench_noscore_alarm = 0
    per_bench_real_pyre_alarm = 0
    per_bench_pyright_alarm = 0
    per_bench_mypy_alarm = 0
    per_bench_pytype_alarm = 0
    per_bench_pyinder_alarm = 0

    print ("{:<20}{:<8}{:<8}{:<8}{:<8}{:<8}{:<8}{:<8}".format(
        "Project",
        "KLOC",
        "N Filter",
        "N Score",
        "Mypy",
        "Pyre",
        "Pyright",
        "Pyinder",
    ))

    sorted_set = sorted(project_set)
    for p in sorted_set :
        print ("{:<20}{:<8}{:<8}{:<8}{:<8}{:<8}{:<8}{:<8}{:<8} ... {:<6} {:<6}".format(
            p,
            round((kloc[p]) / project_num[p]),
            round((baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error']) / project_num[p]),
            round((noscore_alarm[p]['type_error'] + noscore_alarm[p]['none_error'])),
            round((pytype_alarm[p]['type_error'])),
            round((mypy_alarm[p].get('type_error', 0))),
            round((real_pyre_alarm[p]['type_error'] + real_pyre_alarm[p]['none_error'])),
            round((pyright_alarm[p]['type_error'] + pyright_alarm[p]['none_error'])),
            round((project_alarm[p]['type_error'] + project_alarm[p]['none_error']) / project_num[p]),
            round((1 -(noscore_alarm[p]['type_error'] + noscore_alarm[p]['none_error']) / max(baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error'], 1)) * 100, 2),
            round((1 -(project_alarm[p]['type_error'] + project_alarm[p]['none_error']) / max(baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error'], 1)) * 100, 2),
        ))
        total_kloc += kloc[p]
        
        total_baseline_alarm += (baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error'])
        total_noscore_alarm += (noscore_alarm[p]['type_error'] + noscore_alarm[p]['none_error'])
        total_project_alarm += (project_alarm[p]['type_error'] + project_alarm[p]['none_error'])
        total_real_pyre_alarm += (real_pyre_alarm[p]['type_error'] + real_pyre_alarm[p]['none_error'])
        total_pyright_alarm += (pyright_alarm[p]['type_error'] + pyright_alarm[p]['none_error'])
        total_mypy_alarm += (mypy_alarm[p].get('type_error', 0))
        total_pytype_alarm += (pytype_alarm[p]['type_error'])

        per_bench_baseline_alarm += (baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error']) / project_num[p]
        per_bench_noscore_alarm += (noscore_alarm[p]['type_error'] + noscore_alarm[p]['none_error']) / project_num[p]
        per_bench_real_pyre_alarm += (real_pyre_alarm[p]['type_error'] + real_pyre_alarm[p]['none_error']) / project_num[p]
        per_bench_pyright_alarm += (pyright_alarm[p]['type_error'] + pyright_alarm[p]['none_error']) / project_num[p]
        per_bench_mypy_alarm += (mypy_alarm[p].get('type_error', 0)) / project_num[p]
        per_bench_pytype_alarm += (pytype_alarm[p]['type_error']) / project_num[p]
        per_bench_pyinder_alarm += (project_alarm[p]['type_error'] + project_alarm[p]['none_error']) / project_num[p]


    print(
        round(total_kloc, 2),
        round(total_baseline_alarm, 2),
        round(total_noscore_alarm, 2),
        round(total_mypy_alarm, 2),
        round(total_pytype_alarm, 2),
        round(total_real_pyre_alarm, 2),
        round(total_pyright_alarm, 2),
        round(total_project_alarm, 2),
        round((1 - total_noscore_alarm / total_baseline_alarm) * 100, 2),
        round((1 - total_project_alarm / total_baseline_alarm) * 100, 2),
    )

    print(
        round(per_bench_baseline_alarm / len(project_set), 2),
        round(per_bench_noscore_alarm / len(project_set), 2),
        round(per_bench_mypy_alarm / len(project_set), 2),
        round(per_bench_pytype_alarm / len(project_set), 2),
        round(per_bench_real_pyre_alarm / len(project_set), 2),
        round(per_bench_pyright_alarm / len(project_set), 2),
        round(per_bench_pyinder_alarm / len(project_set), 2),
    )

    with open("pyright_data.pickle", "wb") as fw :
        pickle.dump(all_pyright, fw) 

    with open("pyinder_data.pickle", "wb") as fw :
        pickle.dump(all_pyinder, fw)

    with open("pyinder_filter_data.pickle", "wb") as fw:
        pickle.dump(filter_pyinder, fw)

    print(len(filter_pyinder))


    """ for p in project_set :
        print(
            p, 
            round((kloc[p]) / project_num[p]),
            round((project_alarm[p]['type_error'] + project_alarm[p]['none_error']) / project_num[p]),
            round((baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error']) / project_num[p]),

            100 - (round((project_alarm[p]['type_error'] + project_alarm[p]['none_error']) / project_num[p]) / round((baseline_alarm[p]['type_error'] + baseline_alarm[p]['none_error']) / project_num[p])) * 100,

            round((noscore_alarm[p]['type_error'] + noscore_alarm[p]['none_error']) / project_num[p])
        ) """

    """ for p in project_set :
        print(
            p, 
            round((project_alarm[p]['type_error'] + project_alarm[p]['none_error']) / project_num[p]),
            round(project_alarm[p]['none_error'] / (project_alarm[p]['none_error'] + project_alarm[p]['type_error']) * 100), 
            round((pyright_alarm[p]['type_error'] + pyright_alarm[p]['none_error']) / project_num[p]),
            round(pyright_alarm[p]['none_error'] / (pyright_alarm[p]['none_error'] + pyright_alarm[p]['type_error']) * 100)
        ) """
    # print('{:<10}{:<10}{:<5}'.format(round(total_pyinder_alarm / 14), round(total_pyright_alarm / 14), round(total_pyinder_alarm/total_pyright_alarm - 1, 4) * 100))

        




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
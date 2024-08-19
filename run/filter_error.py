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

HOME_PATH = Path.home()
RESULT_PATH = HOME_PATH / 'result'

op_list = []

import operator
import inspect

for op in (inspect.getmembers(operator)) :
    if "__" in op[0] :
        op_list.append(op[0])

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
pyright_op_msg.add("Argument missing for parameter")
pyright_op_msg.add("No parameter named")
pyright_op_msg.add("Cannot access member \"decode\" for type \"str\"")
pyright_op_msg.add("Cannot access member \"encode\" for type \"bytes\"")
pyright_op_msg.add("No overloads for")

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
mypy_op_msg.add("gets multiple values for keyword argument")

pytype_op_msg.add("Built-in function")
pytype_op.add("unsupported-operands")
pytype_op.add("missing-parameter")
pytype_op.add("wrong-arg-count")
pytype_op.add("wrong-keyword-args")
pytype_op.add("wrong-arg-types")
pytype_op.add("not-callable")
pytype_op.add("bad-return-type")


# new
target_projects = [
    "airflow-3831",
    "airflow-4674",
    "airflow-5686",
    "airflow-6036",
    "airflow-8151",
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
    "pandas-36950",
    "pandas-37547",
    "pandas-38431",
    "pandas-39028-1",
    "pandas-41915",
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
            "reportOptionalMemberAccess" not in return_name(e) :
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
    # print('{:<20}{:<10}{:<15}{:<15}{:<10}{:<15}{:<15}{:<10}{:<15}{:<15}'.format("Benchmark", "Pyinder", "Operator", "None", "W/O Dummy", "Operator", "None", "Pyright", "Operator", "None"))

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

        

        pyinder_json = RESULT_PATH / "pyinder" / target_project / 'result_.json'
        pyre_json = RESULT_PATH / "pyre" / target_project / 'result_.json'
        pyright_json = RESULT_PATH / "pyright" / target_project / 'result.json'
        mypy_json = RESULT_PATH / "mypy" / target_project / 'result_.json'
        pytype_json = RESULT_PATH / "pytype" / target_project / 'result.json_'
        #pyright_annotated_path_json = pyright_annotated_path / target_project / 'result.json'

        try :
            with open(pyinder_json, 'r') as f :
                pyinder_result = pyre_analysis(json.load(f))

            try :
                with open(pyre_json, 'r') as f :
                    pyre_result = pyre_analysis(json.load(f))
            except :
                pyre_result = {}

            try :
                with open(pyright_json, 'r') as f :
                    pyright_result = pyright_analysis(json.load(f))
            except Exception as e:
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

        except Exception as e:
            continue

        project_set.add(target_project.split('-')[0])

        total_pyinder = 0
        total_pyright = 0
        total_specific = 0
        total_inter = 0
        
        pyinder_list = to_list(pyinder_result)
        pyre_list = to_list(pyre_result)
        pyright_list = to_list(pyright_result)
        mypy_list = mypy_result
        pytype_list = pytype_result


        

        total_pyinder_alarm += total_pyinder
        total_pyright_alarm += total_pyright

        total_pyinder = 0
        total_pyright = 0

        pyinder_true_type_error, pyinder_none_error, pyinder_incompatible, pyinder_awaitable, pyinder_attributes = get_error_types_pyinder(pyinder_list)
        pyre_true_type_error, pyre_none_error, pyre_incompatible, _, _ = get_error_types_pyinder(pyre_list)
        pyright_true_type_error, pyright_none_error, pyright_incompatible, pyright_awaitable, pyright_attributes = get_error_types_pyright(pyright_list)

        if mypy_list :
            mypy_true_type_error = get_error_types_mypy(mypy_list)
        else :
            mypy_true_type_error = mypy_list
        
        #pyright_annotated_true_type_error, pyright_annotated_none_error, pyright_annotated_incompatible, #pyright_annotated_awaitable, pyright_annotated_attributes = get_error_types_pyright(pyright_annotated_list)
        pytype_true_type_error = get_error_types_pytype(pytype_list)

        pyinder_errors = pyinder_true_type_error + pyinder_none_error + pyinder_incompatible
        pyright_errors = pyright_true_type_error + pyright_none_error + pyright_incompatible
        pyre_errors = pyre_true_type_error + pyre_none_error + pyre_incompatible

        # print(len(pyinder_line), len(pyright_line), common_errors)

        if (RESULT_PATH / "pyinder" / target_project).exists() :
            with open(RESULT_PATH / "pyinder" / target_project / "filter_result.json", 'w') as f :
                json.dump(pyinder_errors, f, indent=4)
                

        if (RESULT_PATH / "pyright" / target_project).exists() :
            with open(RESULT_PATH / "pyright" / target_project / "filter_result.json", 'w') as f :
                json.dump(pyright_errors, f, indent=4)

        if (RESULT_PATH / "pyre" / target_project).exists() :
            with open(RESULT_PATH / "pyre" / target_project / "filter_result.json", 'w') as f :
                json.dump(pyre_errors, f, indent=4)
        
        if (RESULT_PATH / "mypy" / target_project).exists() :
            with open(RESULT_PATH / "mypy" / target_project / "filter_result.json", 'w') as f :
                json.dump(mypy_true_type_error, f, indent=4)

        if (RESULT_PATH / "pytype" / target_project).exists() :
            with open(RESULT_PATH / "pytype" / target_project / "filter_result.json", 'w') as f :
                json.dump(pytype_true_type_error, f, indent=4)


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
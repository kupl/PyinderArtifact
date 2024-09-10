import ast
from pathlib import Path
from pprint import pprint
import json

class ArgInfo() :
    def __init__(self, argument) :
        self.make_argument(argument)

    def __repr__(self) :
        return f"ArgInfo({self.args}, {self.defaults}, {self.vararg}, {self.kwarg})"

    def make_argument(self, argument) :
        args = argument.args
        defaults = argument.defaults
        
        self.args = args[:(len(defaults))]
        self.defaults = args[-(len(defaults)):]
        self.vararg = argument.vararg is not None
        self.kwarg = argument.kwarg is not None
        

class StubVisitor(ast.NodeVisitor):
    def __init__(self, filename):
        self.file_name = filename
        self.cur_class = filename
        self.stubs = dict()

    def visit_ClassDef(self, node):
        
        prev_class = self.cur_class
        self.cur_class = self.cur_class + "." + node.name

        attributes = []
        properties = []

        for body in node.body :
            if isinstance(body, ast.AnnAssign) and isinstance(body.target, ast.Name):
                attributes.append(body.target.id)

            if isinstance(body, (ast.FunctionDef, ast.AsyncFunctionDef)) and "property" in body.decorator_list :
                properties.append(body.name)

        cur_class_dict = self.stubs.get(self.cur_class, {})
        class_attributes_info = cur_class_dict.get("attributes", [])
        class_attributes_info.extend(attributes)
        cur_class_dict["attributes"] = class_attributes_info

        class_properties_info = cur_class_dict.get("properties", [])
        class_properties_info.extend(properties)
        cur_class_dict["properties"] = class_properties_info

        self.stubs[self.cur_class] = cur_class_dict


        self.generic_visit(node)

        self.stubs[self.cur_class]["method"] = self.stubs[self.cur_class].get("method", [])

        self.cur_class = prev_class

    def visit_FunctionDef(self, node):
        if self.cur_class == self.file_name:
            self.generic_visit(node)
        else :
            argument = node.args
            args = [arg.arg for arg in argument.args][1:]
            defaults = argument.defaults
            
            default_index = len(args) - len(defaults)

            posargs = args[:default_index]
            defaults = args[default_index:]
            vararg = argument.vararg is not None
            kwarg = argument.kwarg is not None
        
            arg_info = ArgInfo(node.args)
            method_info = {
                "posargs" : posargs, 
                "defaults" : defaults, 
                "vararg" : vararg,
                "kwarg" : kwarg
            }

            cur_class_dict = self.stubs.get(self.cur_class, {})
            class_method_info = cur_class_dict.get("method", [])
            method_dict = {"name": node.name, "info": method_info}
            class_method_info.append(method_dict)
            cur_class_dict["method"] = class_method_info

            self.stubs[self.cur_class] = cur_class_dict
            self.generic_visit(node)

    def start(self, node) :
        self.visit(node)

        return self.stubs


def main() :
    stubs = Path('.')
    stub_info = {}
    for stub in stubs.rglob('*.pyi'):
        with open(stub) as f:
            tree = ast.parse(f.read())

        #print(stub)
        visitor = StubVisitor(str(stub.parent).replace('/', '.') + "." + stub.stem)
        file_stub_info = visitor.start(tree)

        stub_info.update(file_stub_info)
        #pprint(stub_info)
        #print(ast.dump(tree, indent=4))

        #exit()

    stub_list = []
    for key, value in stub_info.items() :
        new_dict = {"name": key, "info": value}
        stub_list.append(new_dict)

    with open('stub_info.json', 'w') as f:
        json.dump(stub_list, f, indent=4)

if __name__ == '__main__':
    main()
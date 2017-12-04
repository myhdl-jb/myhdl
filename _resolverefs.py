from __future__ import absolute_import, print_function
import ast
from types import FunctionType

from myhdl._util import _flatten
from myhdl._enum import EnumType
from myhdl._Signal import SignalType
from myhdl import ExtractHierarchyError

from myhdl._structured import Array, StructType


class _error:
    pass
_error.NameCollision = " Top Level Signal Name: {} conflicts with generated Signal Name for Interface Member: {}"


class Data():
    pass


def _resolveRefs(symdict, arg):
    #     print(symdict, arg)
    gens = _flatten(arg)
    data = Data()
    data.symdict = symdict
    v = _AttrRefTransformer(data)
    for gen in gens:
        v.visit(gen.ast)
    return data.objlist

# TODO: Refactor this into two separate nodetransformers, since _resolveRefs
# needs only the names, not the objects


def _suffixer(name, used_names):
    # jb 26-07-2015 QaD hack to undo the renaming ...
    # added a check on the expansion of interface names instead
    # which raises an error
    # the renaming would defer the 'problem' until the user checks the generated code
    # or integrates the code in his V*-project
    #     suffixed_names = (name+'_renamed{0}'.format(i) for i in itertools.count())
    #     new_names = itertools.chain([name], suffixed_names)
    #     return next(s for s in new_names if s not in used_names)
    return name


class _AttrRefTransformer(ast.NodeTransformer):

    def __init__(self, data):
        #         if hasattr(data, 'name'):
        #             print('_AttrRefTransformer: ', data.name)
        #         logjbinspect( data, '_AttrRefTransformer', True)
        self.data = data
        self.data.objlist = []
#         self.myhdl_types = (EnumType, SignalType, Array, Struct)
        self.myhdl_types = (EnumType, SignalType)
        self.name_map = {}

    def visit_Attribute(self, node):
        self.generic_visit(node)
        reserved = ('next', 'posedge', 'negedge', 'max', 'min', 'val', 'signed')
        if node.attr in reserved:
            return node

        # Don't handle subscripts for now.
        if not isinstance(node.value, ast.Name):
            return node
        # Don't handle locals
        if node.value.id not in self.data.symdict:
            return node
        obj = self.data.symdict[node.value.id]
        # Don't handle enums and functions, handle signals as long as it is a new attribute
        if isinstance(obj, (EnumType, FunctionType)):
            return node

        elif isinstance(obj, SignalType):
            if hasattr(SignalType, node.attr):
                return node
            attrobj = getattr(obj, node.attr)
            orig_name = node.value.id + '.' + node.attr

# TODO: may have to resolve down ...
        elif isinstance(obj, Array):
#             print(obj, node.attr)
            return node

# TODO: must resolve down
        elif isinstance(obj, StructType):
            #             print(obj, node.attr)
            attrobj = getattr(obj, node.attr)
            orig_name = node.value.id + '.' + node.attr
            if orig_name not in self.name_map:
                #                 print('resolverefs {}'.format(orig_name), end=' ')
                #                 print('not in self.name_map')
                if self.data.symdict.has_key(orig_name):
                    raise ValueError('self.data.symdict.haskey(orig_name)')
                self.name_map[orig_name] = orig_name

        else:
            #             return node
            #             print('_AttrRefTransformer:', obj, node.attr)
            attrobj = getattr(obj, node.attr)
            orig_name = node.value.id + '.' + node.attr

        if orig_name not in self.name_map:
            if node.value.id != 'self':
                if node.attr[0] != '_':
                    base_name = node.value.id + '_' + node.attr
                else:
                    base_name = node.value.id + node.attr
            else:
                base_name = node.attr
            if self.data.symdict.has_key(base_name):
                raise ExtractHierarchyError(_error.NameCollision.format(base_name, orig_name))
            result = _suffixer(base_name, self.data.symdict)
            self.name_map[orig_name] = result

        new_name = self.name_map[orig_name]
        self.data.symdict[new_name] = attrobj
        self.data.objlist.append(new_name)
#         print( orig_name, new_name, attrobj )

        new_node = ast.Name(id=new_name, ctx=node.value.ctx)
        return ast.copy_location(new_node, node)

    def visit_FunctionDef(self, node):
        nodes = _flatten(node.body, node.args)
        for n in nodes:
            self.visit(n)
        return node

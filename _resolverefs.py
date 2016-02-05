from __future__ import absolute_import
import ast
from types import FunctionType

from myhdl._util import _flatten
from myhdl._enum import EnumType
from myhdl._Signal import SignalType
from myhdl import ExtractHierarchyError

from myhdl._structured import Array, StructType

from myhdl.tracejbdef import TRACEJBDEFS
if TRACEJBDEFS['_resolverefs']:
    from myhdl.tracejb import tracejb, logjb, tracejbdedent, logjbinspect
else:
    def tracejb( a, b = None):
        pass
    def logjb(a, b = None, c = False):
        pass
    def tracejbdedent():
        pass
    def logjbinspect(a, b= None, c=None):
        pass


class _error:
    pass
_error.NameCollision = " Top Level Signal Name: {} conflicts with generated Signal Name for Interface Member: {}"



class Data():
    pass


def _resolveRefs(symdict, arg):
    logjb( arg, '_resolveRefs: arg')
    gens = _flatten(arg)
    data = Data()
    data.symdict = symdict
    v = _AttrRefTransformer(data)
    for gen in gens:
        v.visit(gen.ast)
    return data.objlist

#TODO: Refactor this into two separate nodetransformers, since _resolveRefs
#needs only the names, not the objects

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
#         logjbinspect( data, '_AttrRefTransformer', True)
        self.data = data
        self.data.objlist = []
#         self.myhdl_types = (EnumType, SignalType, Array, Struct)
        self.myhdl_types = (EnumType, SignalType)
        self.name_map = {}

    def visit_Attribute(self, node):
        tracejb( '_AttrRefTransformer: visit_Attribute')
        logjbinspect( node, 'node', True)
        self.generic_visit(node)
        reserved = ('next',  'posedge',  'negedge',  'max',  'min',  'val',  'signed')
        if node.attr in reserved:
            tracejbdedent()
            return node

        #Don't handle subscripts for now.
        if not isinstance(node.value, ast.Name):
            tracejbdedent()
            return node
        # Don't handle locals
        if node.value.id not in self.data.symdict:
            tracejbdedent()
            return node
        obj = self.data.symdict[node.value.id]
#         logjb( vars( obj ), 'vars( obj )')
        #Don't handle enums and functions, handle signals as long as it is a new attribute
        if isinstance(obj, (EnumType, FunctionType)):
            tracejbdedent()
            return node

        elif isinstance(obj, SignalType):
            if hasattr(SignalType, node.attr):
                tracejbdedent()
                return node

#TODO: may have to resolve down ...
        elif isinstance(obj, Array):
            logjb(  obj, 'is Array')
            tracejbdedent()
            return node

#TODO: must resolve down
        elif isinstance(obj, StructType):
            logjb(  node, 'is StructType, returning node')
            logjb(repr(obj))
            attrobj = getattr(obj, node.attr)
            orig_name = node.value.id + '.' + node.attr
            logjb( '{} {} {}'.format( obj, orig_name, isinstance(obj, StructType)) , 'after getattr')
            if orig_name not in self.name_map:
                logjb(orig_name , 'orig_name', True)
                logjb( self.data.symdict.has_key(orig_name), 'self.data.symdict.haskey(orig_name)')
                if self.data.symdict.has_key(orig_name):
                    raise ValueError('self.data.symdict.haskey(orig_name)')
                logjb( orig_name , 'self.name_map[orig_name]')
                self.name_map[orig_name] = orig_name

        else:
            attrobj = getattr(obj, node.attr)
            orig_name = node.value.id + '.' + node.attr
            if orig_name not in self.name_map:
                logjb(orig_name , 'orig_name', True)
                if node.value.id != 'self':
                    if node.attr[0] != '_':
                        base_name = node.value.id + '_' + node.attr
                    else:
                        base_name = node.value.id + node.attr
                else:
                    base_name = node.attr
                logjb(base_name , 'base_name', True)
                logjb( self.data.symdict.has_key(base_name), 'self.data.symdict.haskey(base_name)')
                if self.data.symdict.has_key(base_name):
                    raise ExtractHierarchyError( _error.NameCollision.format(base_name, orig_name))
                result = _suffixer(base_name, self.data.symdict)
                logjb( result , 'self.name_map[orig_name]')
                self.name_map[orig_name] = result

        new_name = self.name_map[orig_name]
        self.data.symdict[new_name] = attrobj
        self.data.objlist.append(new_name)

        new_node = ast.Name(id=new_name, ctx=node.value.ctx)
        tracejbdedent()
        return ast.copy_location(new_node, node)

    def visit_FunctionDef(self, node):
        nodes = _flatten(node.body, node.args)
        for n in nodes:
            self.visit(n)
        return node

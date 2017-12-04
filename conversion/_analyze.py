#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2013 Jan Decaluwe
#
#  The myhdl library is free software; you can redistribute it and/or
#  modify it under the terms of the GNU Lesser General Public License as
#  published by the Free Software Foundation; either version 2.1 of the
#  License, or (at your option) any later version.
#
#  This library is distributed in the hope that it will be useful, but
#  WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#  Lesser General Public License for more details.
#
#  You should have received a copy of the GNU Lesser General Public
#  License along with this library; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

""" MyHDL conversion analysis module.

"""
from __future__ import absolute_import, print_function

import sys
import inspect
# import compiler
# from compiler import ast as astNode
from types import FunctionType, MethodType
import re
import ast
from itertools import chain
from collections import defaultdict, namedtuple, OrderedDict

import myhdl
# from myhdl import *
from myhdl import ConversionError
from myhdl._always_comb import _AlwaysComb
from myhdl._always_seq import _AlwaysSeq
from myhdl._always import _Always
from myhdl.conversion._misc import (_error, _access, _kind,
                                    _ConversionMixin, _Label, _genUniqueSuffix,
                                    _get_argnames)
from myhdl._extractHierarchy import _isMem, _getMemInfo, _UserCode
from myhdl._Signal import _Signal, _WaiterList
from myhdl._ShadowSignal import _ShadowSignal, _SliceSignal, _IndexSignal, _CloneSignal, _TristateDriver, _ReverseSignal
from myhdl._util import _isTupleOfInts, _dedent, _flatten, _makeAST
from myhdl._resolverefs import _AttrRefTransformer
from myhdl._compat import builtins, integer_types, PY2
from myhdl._misc import m1Dinfo
from myhdl._structured import Array, StructType

from myhdl.tracejb import Tracing

trace = Tracing(False, source='_analyze')

myhdlObjects = myhdl.__dict__.values()
builtinObjects = builtins.__dict__.values()

_enumTypeSet = set()


# def _makeName(n, prefixes, namedict):
def _makeName(n, prefixes):
    # trim empty prefixes
    prefixes = [p for p in prefixes if p]
    if len(prefixes) > 1:
        #        name = '_' + '_'.join(prefixes[1:]) + '_' + n
        name = '_'.join(prefixes[1:]) + '_' + n
    else:
        name = n
    if '[' in name or ']' in name:
        name = "\\" + name + ' '
    return name


def _analyzeSigs(hierarchy, hdl='Verilog'):
    trace.push(False, '_analyzeSigs')
    curlevel = 0
    siglist = []
    memlist = []
    prefixes = []

#     openp, closep = '[', ']'
#     if hdl == 'VHDL':
    openp, closep = ('(', ')') if hdl == 'VHDL' else ('[', ']')

    for inst in hierarchy:
        level = inst.level
        name = inst.name
        sigdict = inst.sigdict
        memdict = inst.memdict
#         namedict = dict(chain(sigdict.items(), memdict.items()))
#         trace.print(inst.argdict)
        delta = curlevel - level
        curlevel = level
        assert delta >= -1
        if delta > -1:  # same or higher level
            prefixes = prefixes[:curlevel - 1]
#         # skip processing and prefixing in context without signals
#         if not (sigdict or memdict):
#             prefixes.append("")
#             continue
        prefixes.append(name)
        trace.print(prefixes)
        for n, s in sigdict.items():
            trace.print('_analyzeSigs level {}: {} {} {}'.format(level, s._name, n, repr(s)))
            if s._name is not None:
                #                 if s._namelevel >= level:
                #                     #                     trace.print(s._namelevel, level, s._name, _makeName(n, prefixes, namedict))
                #                     #                     s._name = _makeName(n, prefixes, namedict)
                #                     #                     trace.print(s._namelevel, level, s._name, _makeName(n, prefixes))
                #                     s._name = _makeName(n, prefixes,)
                trace.print(' skipping')
                continue

            if isinstance(s, (_SliceSignal, _IndexSignal, _CloneSignal, _ReverseSignal)):
                #                 trace.print('_analyzeSigs {} skipping {}'.format(level, repr(s)))
                trace.print(' skipping ShadowSignals')
                continue


#             s._name = _makeName(n, prefixes, namedict)
            s._name = _makeName(n, prefixes)
            s._namelevel = level
            if not s._nrbits:
                raise ConversionError(_error.UndefinedBitWidth, s._name)
            # slice signals
            # this goes only one level deep???!!!
            for sl in s._slicesigs:
                sl._setName(hdl)
#                 trace.print(sl._name, sl._slicesigs)
#                 if sl._slicesigs:
#                     for ssl in s._slicesigs:
#                         ssl._setName(hdl)
#                         trace.print(ssl._name, ssl._slicesigs)
#                     siglist.append(sl)
            trace.print(' ', s._name)
            siglist.append(s)

        # list of signals
        for n, m in memdict.items():
            if m.name is not None:
                continue
#             m.name = _makeName(n, prefixes, namedict)
            m.name = _makeName(n, prefixes)
            trace.print('_analyzeSigs level {}: {} {} {}'.format(level, m.name, n, repr(m)))
            if isinstance(m.mem, (Array, StructType)):
                m.mem._name = m.name
#             print(m)
            memlist.append(m)
#             trace.print('_analyzeSigs {} {} {} memlist.append({})'.format(level, prefixes, n, repr(m)))



    # handle the case where a named signal appears in a list also by giving
    # priority to the list and marking the signals as unused

    # tracing
    for m in memlist:
        if not m._used:
            continue
        # m is a m1D list
        trace.push(message="expanding {}".format(m.name))
        expandsignalnames(m.mem, m.name, 0, 0, openp, closep)
        trace.pop()

    trace.pop()
    return siglist, memlist


def expandsignalnames(memobj, name, memindex, level, openp, closep):
    trace.print(repr(memobj), name, memindex, level)
    if isinstance(memobj, (list, Array)):
        if isinstance(memobj[0], (list, Array)):
            for i, mmm in enumerate(memobj):
                nextname = '{}{}{}{}' .format(name, openp, i, closep)
                expandsignalnames(mmm, nextname, memindex, level, openp, closep)
        else:
            # lowest (= last) level of m1D
            if isinstance(memobj, list):
                elobj = memobj[0]
            else:
                elobj = memobj.element
            for i, s in enumerate(memobj):
                makesname(i, s, name, elobj, openp, closep)
        memindex += 1

    elif isinstance(memobj, StructType):
        vargs = vars(memobj)
        for key in vargs:
            obj = vargs[key]
            if isinstance(obj, _Signal):
                makesname(None, obj, name, obj, key, None)

            elif isinstance(obj, StructType):
                nextname = ''.join((name, '.', key))
                obj._name = nextname
                expandsignalnames(obj, nextname, memindex, 0, openp, closep)

            elif isinstance(obj, Array):
                nextname = ''.join((name, '.', key))
                obj._name = nextname
                expandsignalnames(obj, nextname, memindex, level + 1, openp, closep)

    else:
        raise ValueError("Unhandled obj: {}".format(repr(obj)))


def makesname(i, s, signame, elobj, openp, closep):
    if i is None:
        s._name = "%s.%s" % (signame, openp)
    else:
        s._name = "%s%s%s%s" % (signame, openp, i, closep)
    s._used = False
    if isinstance(elobj, _Signal):
        #             if s._inList:
        #                 raise ConversionError(_error.SignalInMultipleLists, s._name)
        s._inList = True
        if not s._nrbits:
            raise ConversionError(_error.UndefinedBitWidth, s._name)
        if type(s.val) != type(elobj.val):
            raise ConversionError(_error.InconsistentType, s._name)
        if s._nrbits != elobj._nrbits:
            raise ConversionError(_error.InconsistentBitWidth, '{} <> {}'.format(repr(s), repr(elobj)))


def _analyzeGens(top, absnames):
    trace.push(message='_analyzeGens')
    genlist = []
    for g in top:
        if isinstance(g, _UserCode):
            tree = g
        elif isinstance(g, (_AlwaysComb, _AlwaysSeq, _Always)):
            f = g.func
            tree = g.ast
            tree.symdict = f.__globals__.copy()

            tree.callstack = []
            # handle free variables
            tree.nonlocaldict = {}
            if f.__code__.co_freevars:
                for n, c in zip(f.__code__.co_freevars, f.__closure__):
                    obj = c.cell_contents
                    tree.symdict[n] = obj
                    # currently, only intbv as automatic nonlocals (until
                    # Python 3.0)
                    if isinstance(obj, myhdl.intbv):
                        tree.nonlocaldict[n] = obj
#             tree.name = absnames.get(id(g), str(_Label("BLOCK"))).upper()
            tree.name = absnames.get(id(g), str(_Label("BLOCK")))
            v = _AttrRefTransformer(tree)
            v.visit(tree)
            v = _FirstPassVisitor(tree)
            v.visit(tree)
            if isinstance(g, _AlwaysComb):
                trace.push(message='_AnalyzeAlwaysCombVisitor')
                v = _AnalyzeAlwaysCombVisitor(tree, g.senslist)
            elif isinstance(g, _AlwaysSeq):
                trace.push(message='_AnalyzeAlwaysSeqVisitor')
                v = _AnalyzeAlwaysSeqVisitor(
                    tree, g.senslist, g.reset, g.sigregs, g.varregs)
            else:
                trace.push(message='_AnalyzeAlwaysDecoVisitor')
                v = _AnalyzeAlwaysDecoVisitor(tree, g.senslist)
            v.visit(tree)
            trace.pop()
        else:  # @instance
            trace.push(message='@instance')
            f = g.gen.gi_frame
            tree = g.ast
            tree.symdict = f.f_globals.copy()
            tree.symdict.update(f.f_locals)
            tree.nonlocaldict = {}
            tree.callstack = []
#             tree.name = absnames.get(id(g), str(_Label("BLOCK"))).upper()
            tree.name = absnames.get(id(g), str(_Label("BLOCK")))
            v = _AttrRefTransformer(tree)
            v.visit(tree)
            v = _FirstPassVisitor(tree)
            v.visit(tree)
            v = _AnalyzeBlockVisitor(tree)
            v.visit(tree)
            trace.pop()

        genlist.append(tree)
    trace.pop()
    return genlist


class _FirstPassVisitor(ast.NodeVisitor, _ConversionMixin):

    """First pass visitor.

    Prune unsupported contructs, and add some useful attributes.

    """

    def __init__(self, tree):
        self.tree = tree
        self.toplevel = True

    def visit_Tuple(self, node):
        if isinstance(node.ctx, ast.Store):
            self.raiseError(node, _error.NotSupported, "tuple assignment")

    def visit_Repr(self, node):
        self.raiseError(node, _error.NotSupported, "backquote")

    def visit_ClassDef(self, node):
        self.raiseError(node, _error.NotSupported, "class statement")

    def visit_Dict(self, node):
        self.raiseError(node, _error.NotSupported, "dictionary")

    def visit_BinOp(self, node):
        if isinstance(node.op, ast.Div):
            self.raiseError(
                node, _error.NotSupported, "true division - consider '//'")

    def visit_Ellipsis(self, node):
        self.raiseError(node, _error.NotSupported, "ellipsis")

    def visit_Exec(self, node):
        self.raiseError(node, _error.NotSupported, "exec statement")

    def visitExpression(self, node, *args):
        self.raiseError(node, _error.NotSupported, "Expression node")

    def visit_ImportFrom(self, node):
        self.raiseError(node, _error.NotSupported, "from statement")

    def visit_Global(self, node):
        self.raiseError(node, _error.NotSupported, "global statement")

    def visit_Import(self, node):
        self.raiseError(node, _error.NotSupported, "import statement")

    def visit_Lambda(self, node):
        self.raiseError(node, _error.NotSupported, "lambda statement")

    def visit_ListComp(self, node):
        if len(node.generators) > 1:
            self.raiseError(
                node, _error.NotSupported, "multiple for statements in list comprehension")
        if node.generators[0].ifs:
            self.raiseError(
                node, _error.NotSupported, "if statement in list comprehension")
        self.generic_visit(node)

    def visit_List(self, node):
        self.raiseError(node, _error.NotSupported, "list")

    def visitSliceObj(self, node):
        self.raiseError(node, _error.NotSupported, "slice object")

    # All try blocks from python 3.3+
    def visit_Try(self, node):
        self.raiseError(node, _error.NotSupported, "try statement")

    # Legacy try blocks
    def visit_TryExcept(self, node):
        self.raiseError(node, _error.NotSupported, "try-except statement")

    def visit_TryFinally(self, node):
        self.raiseError(node, _error.NotSupported, "try-finally statement")

    def visit_Assign(self, node):
        if len(node.targets) > 1:
            self.raiseError(node, _error.NotSupported, "multiple assignments")
#         trace.print('visit_Assign', node.targets[0])
        self.visit(node.targets[0])
#         trace.print('visit_Assign', node.value)
        self.visit(node.value)

    def visit_Call(self, node):
        # ast.Call signature changed in python 3.5
        # http://greentreesnakes.readthedocs.org/en/latest/nodes.html#Call
        if sys.version_info >= (3, 5):
            starargs = any(isinstance(arg, ast.Starred) for arg in node.args)
            kwargs = any(kw.arg is None for kw in node.keywords)
        else:
            starargs = node.starargs is not None
            kwargs = node.kwargs is not None

        if starargs:
            self.raiseError(
                node, _error.NotSupported, "extra positional arguments")
        if kwargs:
            self.raiseError(node, _error.NotSupported, "extra named arguments")
        self.generic_visit(node)

    def visit_Compare(self, node):
        if len(node.ops) != 1:
            self.raiseError(node, _error.NotSupported, "chained comparison")
        self.generic_visit(node)

    def visit_FunctionDef(self, node):
        if node.args.vararg or node.args.kwarg:
            self.raiseError(
                node, _error.NotSupported, "extra positional or named arguments")
        if not self.toplevel:
            self.raiseError(
                node, _error.NotSupported, "embedded function definition")
        self.toplevel = False
        node.argnames = _get_argnames(node)
        # don't visit decorator lists - they can support more than other calls
        # put official docstrings aside for separate processing
        node.doc = None
        if node.body and isinstance(node.body[0], ast.Expr) and \
                isinstance(node.body[0].value, ast.Str):
            node.doc = node.body[0].value.s
            node.body = node.body[1:]
        self.visitList(node.body)

    def flattenIf(self, node, tests, else_, co):
        """ Flatten if-then-else as in compiler package."""
        if node:
            if len(node) == 1 and \
                    isinstance(node[0], ast.If) and \
                    node[0].body[0].col_offset == co:  # ugly hack to detect separate else clause
                elifnode = node[0]
                tests.append((elifnode.test, elifnode.body))
                self.flattenIf(elifnode.orelse, tests, else_, co)
            else:
                else_[:] = node

    def visit_If(self, node):
        node.ignore = False
        if not node.orelse:
            test = node.test
            if isinstance(test, ast.Name):
                if test.id == '__debug__':
                    node.ignore = True
                    return  # skip
        self.generic_visit(node)

        # add fields that match old compiler package
        tests = [(node.test, node.body)]
        else_ = []
        self.flattenIf(node.orelse, tests, else_, node.body[0].col_offset)
        node.tests = tests
        node.else_ = else_

    def visit_Print(self, node):
        if node.dest is not None:
            self.raiseError(
                node, _error.NotSupported, "printing to a file with >> syntax")
        if not node.nl:
            self.raiseError(
                node, _error.NotSupported, "printing without newline")


def getNrBits(obj):
    if hasattr(obj, '_nrbits'):
        return obj._nrbits
    return None


def hasType(obj, theType):
    if isinstance(obj, theType):
        return True
    if isinstance(obj, _Signal):
        if isinstance(obj._val, theType):
            return True
    return False


class ReferenceStack(list):

    def push(self):
        self.append(set())

    def add(self, item):
        self[-1].add(item)

    def __contains__(self, item):
        for s in self:
            if item in s:
                return True
        return False


class _Ram(object):
    __slots__ = ['elObj', 'depth']


class _Rom(object):
    __slots__ = ['rom']

    def __init__(self, rom):
        self.rom = rom


re_str = re.compile(r"[^%]+")
re_ConvSpec = re.compile(
    r"%(?P<justified>[-]?)(?P<width>[0-9]*)(?P<conv>[sd])")


class ConvSpec(object):

    def __init__(self, **kwargs):
        self.justified = "RIGHT"
        self.width = 0
        self.conv = str
        if kwargs['justified'] == '-':
            self.justified = "LEFT"
        if kwargs['width']:
            self.width = int(kwargs['width'])
        if kwargs['conv'] == 'd':
            self.conv = int


defaultConvSpec = ConvSpec(**re_ConvSpec.match(r"%s").groupdict())


def _getNritems(obj):
    """Return the number of items in an objects' type"""
    trace.print('_getNritems', repr(obj))
#     logjbinspect(obj, 'obj', True)
    if isinstance(obj, _Signal):
        obj = obj._init
    if isinstance(obj, myhdl.intbv):
        return obj._max - obj._min
    elif isinstance(obj, myhdl.EnumItemType):
        return len(obj._type)
    else:
        raise TypeError("Unexpected type, missing final \'else:\'?")


class _AnalyzeVisitor(ast.NodeVisitor, _ConversionMixin):

    def __init__(self, tree):
        tree.sigdict = OrderedDict()  # {}
        tree.vardict = OrderedDict()  # {}
        tree.inputs = set()
        tree.outputs = set()
        # hack for assigned mems
        tree.outmems = set()
        tree.argnames = []
        tree.kind = None
        tree.hasYield = 0
        tree.hasRom = False
        tree.hasLos = False
        tree.hasPrint = False
        self.tree = tree
        self.labelStack = []
        self.refStack = ReferenceStack()
        self.globalRefs = set()
        self.access = _access.INPUT
        self.kind = _kind.NORMAL

    def visit_BinOp(self, node):
        trace.push(message='visit_BinOp')
        self.visit(node.left)
        self.visit(node.right)
        node.obj = int(-1)
        trace.pop()

    def visit_BoolOp(self, node):
        trace.push(message='visit_BoolOp')
        for n in node.values:
            self.visit(n)
        for n in node.values:
            if not hasType(n.obj, bool):
                self.raiseError(
                    node, _error.NotSupported, "non-boolean argument in logical operator: '{}'. Possibly Signal(intbv(0)) in stead of Signal(bool(0))".format(n.obj))
        node.obj = bool()
        trace.pop()

    def visit_UnaryOp(self, node):
        self.visit(node.operand)
        op = node.op
        node.obj = node.operand.obj
        if isinstance(op, ast.Not):
            node.obj = bool()
        elif isinstance(op, ast.UAdd):
            node.obj = int(-1)
        elif isinstance(op, ast.USub):
            node.obj = int(-1)

    def visit_Attribute(self, node):
        trace.push(message='visit_Attribute')
        if isinstance(node.ctx, ast.Store):
            self.setAttr(node)
        else:
            self.getAttr(node)

        if node.attr == 'next':
            if isinstance(node.value, ast.Name):
                n = node.value.id
                obj = node.value.obj
                if isinstance(obj, _Signal) and isinstance(obj._init, myhdl.modbv):
                    if not obj._init._hasFullRange():
                        self.raiseError(node, _error.ModbvRange, n)
        trace.pop()

    def setAttr(self, node):
        trace.push(message='setAttr')
        trace.print(node, node.attr, node.value)
        if node.attr != 'next':
            self.raiseError(node, _error.NotSupported, "attribute assignment, forgotten '.next'?")
        self.tree.kind = _kind.TASK
        # self.access = _access.OUTPUT
        self.visit(node.value)
        # self.access = _access.INPUT
        trace.pop()

    def getAttr(self, node):
        trace.push(None, 'getAttr')
        self.visit(node.value)
        node.obj = None
        if isinstance(node.value, ast.Name):
            n = node.value.id
            if (n not in self.tree.vardict) and (n not in self.tree.symdict):
                raise AssertionError("attribute target: %s" % n)

        obj = node.value.obj
#         trace.print('_analyze: _AnalyzeVisitor: getAttr:', repr(obj), node.attr)
        if isinstance(obj, _Signal):
            trace.print(repr(obj), node.attr)
            if node.attr == 'posedge':
                node.obj = obj.posedge
            elif node.attr == 'negedge':
                node.obj = obj.negedge
            elif node.attr in ('val', 'next'):
                node.obj = obj.val
            # adding intbv attrs
            elif node.attr == 'min':
                node.obj = obj.min
            elif node.attr == 'max':
                node.obj = obj.max
            elif node.attr == 'signed':
                node.obj = myhdl.intbv.signed
            elif node.attr == 'unsigned':
                node.obj = myhdl.intbv.unsigned
            else:
                trace.print('Not handled? ', repr(node), repr(node.value), repr(obj), node.attr)
                trace.print('vars(node)', vars(node))
                trace.print('vars(node.value)', vars(node.value))
#                 node.obj = obj.val

        elif isinstance(obj, (myhdl.intbv)):
            if node.attr == 'min':
                node.obj = obj.min
            elif node.attr == 'max':
                node.obj = obj.max
            elif node.attr == 'signed':
                node.obj = myhdl.intbv.signed
            elif node.attr == 'unsigned':
                node.obj = myhdl.intbv.unsigned

        elif isinstance(obj, myhdl.EnumType):
            assert hasattr(obj, node.attr), node.attr
            node.obj = getattr(obj, node.attr)
            if obj not in _enumTypeSet:
                obj._setName(n)
                _enumTypeSet.add(obj)

        elif isinstance(obj, Array):
            trace.print(repr(obj))
            node.obj = obj.element

        elif isinstance(obj, StructType):
            trace.print(repr(obj))
            vargs = vars(obj)
            for k in vargs:
                if node.attr == k:
                    node.obj = vargs[k]

        elif isinstance(obj, list):
            _, _, _, node.obj = m1Dinfo(obj)

#         # 7jun16 jb
#         if isinstance(obj, tuple):
#             node.obj = getattr(obj, node.attr)
#             trace.print(node.obj)

        else:
            # assume it is an indexed class
            trace.print(repr(getattr(obj, node.attr)))
            node.obj = getattr(obj, node.attr)

        trace.print('result node.obj:', repr(node.obj))

        if node.obj is None:  # attribute lookup failed
            self.raiseError(node, _error.UnsupportedAttribute, node.attr)

        trace.pop()

    def visit_Assign(self, node):
        trace.push(message='visit_Assign')
        target, value = node.targets[0], node.value
        trace.print('target: {} value: {}'.format(target, value))

        self.access = _access.OUTPUT
        trace.push(None, 'lhs')
        self.visit(target)
        trace.pop()

        trace.push(None, 'rhs')
        self.access = _access.INPUT
        # set attribute to detect a top-level rhs
        value.isRhs = True
        if isinstance(target, ast.Name):
            node.kind = _kind.DECLARATION
            self.kind = _kind.DECLARATION
            self.visit(value)
            self.kind = _kind.NORMAL
            n = target.id
            if n in self.tree.sigdict:
                self.raiseError(node, _error.ShadowingVar)
            obj = self.getObj(value)
            if obj is None:
                self.raiseError(node, _error.TypeInfer, n)

            if isinstance(obj, myhdl.intbv):
                if len(obj) == 0:
                    self.raiseError(node, _error.IntbvBitWidth, n)

            if isinstance(obj, myhdl.modbv):
                if not obj._hasFullRange():
                    self.raiseError(node, _error.ModbvRange, n)

            if n in self.tree.vardict:
                # this fix
                #                 if isinstance(obj, _Signal):
                #                     obj = obj._val

                curObj = self.tree.vardict[n]
                if isinstance(obj, type(curObj)):
                    pass
                elif isinstance(curObj, type(obj)):
                    self.tree.vardict[n] = obj
                else:
                    self.raiseError(node, _error.TypeMismatch, n)
                if getNrBits(obj) != getNrBits(curObj):
                    self.raiseError(node, _error.NrBitsMismatch, n)
            else:
                self.tree.vardict[n] = obj

        else:
            self.visit(value)

        trace.pop()
        trace.print('finished')
        trace.pop()

    def visit_AugAssign(self, node):
        # declare node as an rhs for type inference optimization
        node.isRhs = True
        self.access = _access.INOUT
        self.visit(node.target)
        self.access = _access.INPUT
        self.visit(node.value)

    def visit_Break(self, node):
        self.labelStack[-2].isActive = True

    def visit_Call(self, node):
        trace.push(None, 'visit_Call')
        trace.print('node.args', node.args, self.access)
        self.visit(node.func)
        f = self.getObj(node.func)
        node.obj = None

        if f is print:
            self.visit_Print(node)
            return

#         trace.print('setting self.access to UNKNOWN - 1')
        self.access = _access.UNKNOWN
        for arg in node.args:
            self.visit(arg)
        for kw in node.keywords:
            self.visit(kw)
#         trace.print('setting self.access to INPUT - 1')
        self.access = _access.INPUT
        argsAreInputs = True
        if type(f) is type and issubclass(f, myhdl.intbv):
            node.obj = self.getVal(node)
        elif f is myhdl.concat:
            node.obj = self.getVal(node)
        elif f is len:
            #             trace.print('setting self.access to UNKNOWN - 2')
            #             self.access = _access.UNKNOWN #6jun16 jb
            node.obj = int(0)  # XXX
        elif f is bool:
            node.obj = bool()
        elif f in _flatten(integer_types, ord):
            node.obj = int(-1)
# #         elif f in (posedge , negedge):
# #             node.obj = _EdgeDetector()
        elif f is myhdl.delay:
            node.obj = myhdl.delay(0)
        # ## suprize: identity comparison on unbound methods doesn't work in python 2.5??
        elif f == myhdl.intbv.signed:
            node.obj = int(-1)
        elif f == myhdl.intbv.unsigned:
            node.obj = int(1)
        elif f in myhdlObjects:
            pass
        elif f in builtinObjects:
            pass
#         elif type(f) is FunctionType:
        elif isinstance(f, FunctionType):
            trace.push(None, 'FunctionType')
            argsAreInputs = False
            tree = _makeAST(f)
            fname = f.__name__
            trace.print(fname)
#             tree.name = _Label(fname)
            tree.name = fname
            tree.symdict = f.__globals__.copy()
#             logjb( tree.symdict, 'tree.symdict')
            tree.nonlocaldict = {}
            if fname in self.tree.callstack:
                self.raiseError(node, _error.NotSupported, "Recursive call")
            tree.callstack = self.tree.callstack[:]
            tree.callstack.append(fname)
            # handle free variables
            if f.__code__.co_freevars:
                for n, c in zip(f.__code__.co_freevars, f.__closure__):
                    obj = c.cell_contents
                    if not isinstance(obj, (integer_types, _Signal)):
                        self.raiseError(node, _error.FreeVarTypeError, n)
                    tree.symdict[n] = obj
#                     logjb( tree.symdict, 'tree.symdict')
            v = _FirstPassVisitor(tree)
            v.visit(tree)
            v = _AnalyzeFuncVisitor(tree, node.args, node.keywords)
            v.visit(tree)
            node.obj = tree.returnObj
            node.tree = tree
            tree.argnames = argnames = _get_argnames(tree.body[0])
            # extend argument list with keyword arguments on the correct
            # position
            node.args.extend([None] * len(node.keywords))
            for kw in node.keywords:
                node.args[argnames.index(kw.arg)] = kw.value
            for n, arg in zip(argnames, node.args):
                if n in tree.outputs:
                    self.access = _access.OUTPUT
                    self.visit(arg)
                    self.access = _access.INPUT
                if n in tree.inputs:
                    self.visit(arg)
            trace.pop()
        elif type(f) is MethodType:
            #             self.raiseError(
            #                 node, _error.NotSupported, "method call: '%s'" % f.__name__)
            trace.push(None, 'MethodType')
            argsAreInputs = False
            tree = _makeAST(f)
            trace.print(tree, vars(tree))
            trace.print('body', vars(tree.body[0]))
            fname = f.__name__
#             tree.name = _Label(fname)
            tree.name = fname
            trace.print('tree.name', fname)
            tree.symdict = f.__globals__.copy()
#             logjb( tree.symdict, 'tree.symdict')
            tree.nonlocaldict = {}
            if fname in self.tree.callstack:
                self.raiseError(node, _error.NotSupported, "Recursive call")
            tree.callstack = self.tree.callstack[:]
            tree.callstack.append(fname)
            # handle free variables
            if f.__code__.co_freevars:
                for n, c in zip(f.__code__.co_freevars, f.__closure__):
                    obj = c.cell_contents
                    if not isinstance(obj, (integer_types, _Signal)):
                        self.raiseError(node, _error.FreeVarTypeError, n)
                    tree.symdict[n] = obj
                    trace.print('tree.symdict', tree.symdict)
            v = _FirstPassVisitor(tree)
            v.visit(tree)
            v = _AnalyzeFuncVisitor(tree, node.args, node.keywords)
            v.visit(tree)
            node.obj = tree.returnObj
            node.tree = tree
            tree.argnames = argnames = _get_argnames(tree.body[0])
            # extend argument list with keyword arguments on the correct
            # position
            node.args.extend([None] * len(node.keywords))
            for kw in node.keywords:
                node.args[argnames.index(kw.arg)] = kw.value
            for n, arg in zip(argnames, node.args):
                if n in tree.outputs:
                    self.access = _access.OUTPUT
                    self.visit(arg)
                    self.access = _access.INPUT
                if n in tree.inputs:
                    self.visit(arg)
            trace.pop()
        else:
            debug_info = [e for e in ast.iter_fields(node.func)]
            raise AssertionError("Unexpected callable %s, you probably have use a non convertible math-function?" % str(debug_info))
        if argsAreInputs:
            for arg in node.args:
                self.visit(arg)

        trace.pop()

    def visit_Compare(self, node):
        node.obj = bool()
        for n in [node.left] + node.comparators:
            self.visit(n)
        op, arg = node.ops[0], node.comparators[0]
# #         node.expr.target = self.getObj(arg)
# #         arg.target = self.getObj(node.expr)
        # detect specialized case for the test
        if isinstance(op, ast.Eq) and isinstance(node.left, ast.Name):
            # check wether it can be a case
            val = arg.obj
            if isinstance(val, bool):
                val = int(val)  # cast bool to int first
            if isinstance(val, (myhdl.EnumItemType, integer_types)):
                node.case = (node.left, val)
            # check whether it can be part of an edge check
            n = node.left.id
            if n in self.tree.sigdict:
                sig = self.tree.sigdict[n]
                v = self.getValue(arg)
                if v is not None:
                    if v == 0:
                        node.edge = sig.negedge
                    elif v == 1:
                        node.edge = sig.posedge

    def visit_Num(self, node):
        n = node.n
        # assign to value attribute for backwards compatibility
        node.value = n
        if n in (0, 1):
            node.obj = bool(n)
        elif isinstance(n, int):
            node.obj = n
        else:
            node.obj = None

    def visit_Str(self, node):
        node.obj = node.s

    def visit_Continue(self, node):
        self.labelStack[-1].isActive = True

    def visit_For(self, node):
        trace.push(None, 'visit_Call')
        node.breakLabel = _Label("BREAK")
        node.loopLabel = _Label("LOOP")
        self.labelStack.append(node.breakLabel)
        self.labelStack.append(node.loopLabel)
        self.refStack.push()
        self.visit(node.target)
        var = node.target.id
        self.tree.vardict[var] = int(-1)

        cf = node.iter
        self.visit(cf)
        self.require(
            node, isinstance(cf, ast.Call), "Expected (down)range call")
        f = self.getObj(cf.func)
        self.require(
            node, f in (range, myhdl.downrange), "Expected (down)range call")

        for stmt in node.body:
            self.visit(stmt)

        self.refStack.pop()
        self.require(node, not node.orelse, "for-else not supported")
        self.labelStack.pop()
        self.labelStack.pop()
        trace.pop()

    def visit_FunctionDef(self, node):
        raise AssertionError("subclass must implement this")

    def visit_If(self, node):
        if node.ignore:
            return
        trace.push(message='visit_If')
        for test, suite in node.tests:
            self.visit(test)
            self.refStack.push()
            self.visitList(suite)
            self.refStack.pop()
        if node.else_:
            trace.push(message='node.else_')
            self.refStack.push()
            self.visitList(node.else_)
            self.refStack.pop()
            trace.pop()
        # check whether the if can be mapped to a (parallel) case
        node.isCase = node.isFullCase = False
        test1 = node.tests[0][0]
        if not hasattr(test1, 'case'):
            trace.pop()
            return
        var1, item1 = test1.case
        # don't infer a case if there's no elsif test
        if not node.tests[1:]:
            trace.pop()
            return
        choices = set()
        choices.add(item1)

        for test, suite in node.tests[1:]:
            if not hasattr(test, 'case'):
                trace.pop()
                return
            var, item = test.case
            if var.id != var1.id or type(item) is not type(item1):
                trace.pop()
                return
            if item in choices:
                trace.pop()
                return
            choices.add(item)
        # we got here, so it must be a state machine?
        # or at least a ROM
        node.isCase = True
        node.caseVar = var1
        node.caseItem = item1
        trace.print(len(choices))
        for ch in choices:
            trace.print(ch)
            # if (len(choices) == _getNritems(var1.obj)) or node.else_  :
        if node.else_:
            node.isFullCase = True
        elif (len(choices) == _getNritems(var1.obj)):
            node.isFullCase = True
        else:
            # emit a warning
            pass
        trace.print('IsCase: {}, IsFullCase: {}'.format(node.isCase, node.isFullCase))

        trace.pop()

    def visit_IfExp(self, node):
        self.visit(node.test)
        self.visit(node.body)
        self.visit(node.orelse)
#         self.refStack.push()
#         self.visitList(node.else_)
#         self.refStack.pop()

    def visit_ListComp(self, node):
        mem = node.obj = _Ram()
        self.kind = _kind.DECLARATION
        try:
            self.visit(node.elt)
        except ConversionError as e:
            if e.kind == _error.UnboundLocal:
                pass
            else:
                raise
        self.kind = _kind.NORMAL
        mem.elObj = self.getObj(node.elt)
        if not isinstance(mem.elObj, myhdl.intbv) or not len(mem.elObj) > 0:
            self.raiseError(node, _error.UnsupportedListComp)
        cf = node.generators[0].iter
        self.visit(cf)
        if not isinstance(cf, ast.Call):
            self.raiseError(node, _error.UnsupportedListComp)
        f = self.getObj(cf.func)
        if f is not range or len(cf.args) != 1:
            self.raiseError(node, _error.UnsupportedListComp)
        mem.depth = cf.args[0].obj

    def visit_NameConstant(self, node):
        node.obj = node.value

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Store):
            self.setName(node)
        else:
            self.getName(node)

    def setName(self, node):
        # XXX INOUT access in Store context, unlike with compiler
        # XXX check whether ast context is correct
        n = node.id
        trace.print('setName', n, node)

        if self.access == _access.INOUT:  # augmented assign
            if n in self.tree.sigdict:
                sig = self.tree.sigdict[n]
                if isinstance(sig, _Signal):
                    self.raiseError(node, _error.NotSupported, "Augmented signal assignment")

            if n in self.tree.vardict:
                obj = self.tree.vardict[n]
                # upgrade bool to int for augmented assignments
                if isinstance(obj, bool):
                    obj = int(-1)
                    self.tree.vardict[n] = obj
                node.obj = obj
        else:
            if n in ("__verilog__", "__vhdl__"):
                self.raiseError(node, _error.NotSupported, "%s in generator function" % n)
            if n in self.globalRefs:
                self.raiseError(node, _error.UnboundLocal, n)
            self.refStack.add(n)

    def getName(self, node):
        trace.push(False, 'getName')
        n = node.id
        node.obj = None
        if n not in self.refStack:
            if (n in self.tree.vardict) and (n not in self.tree.nonlocaldict):
                self.raiseError(node, _error.UnboundLocal, n)
            self.globalRefs.add(n)

        if n in self.tree.sigdict:
            node.obj = sig = self.tree.sigdict[n]
            # mark shadow signal as driven only when they are seen somewhere
            if isinstance(sig, _ShadowSignal):
                sig.driven = 'wire'
            # mark tristate signal as driven if its driver is seen somewhere
            if isinstance(sig, _TristateDriver):
                sig._sig.driven = 'wire'
            if not isinstance(sig, _Signal):
                pass
            else:
                if sig._type is bool:
                    node.edge = sig.posedge

            if self.access == _access.INPUT:
                self.tree.inputs.add(n)
            elif self.access == _access.OUTPUT:
                self.tree.kind = _kind.TASK
                if n in self.tree.outputs:
                    node.kind = _kind.REG
                self.tree.outputs.add(n)
            elif self.access == _access.UNKNOWN:
                pass
            else:
                self.raiseError(node, _error.NotSupported, "Augmented signal assignment")
            trace.print('sigdict', n, repr(node.obj), self.access)

        if n in self.tree.vardict:
            obj = self.tree.vardict[n]
            if self.access == _access.INOUT:  # probably dead code
                # upgrade bool to int for augmented assignments
                if isinstance(obj, bool):
                    obj = int(-1)
                    self.tree.vardict[n] = obj
            node.obj = obj
            trace.print('vardict', n, repr(node.obj), self.access)

        elif n in self.tree.symdict:
            node.obj = self.tree.symdict[n]
            trace.print('symdict', n, repr(node.obj), _isMem(node.obj), self.access)
            if _isTupleOfInts(node.obj):
                node.obj = _Rom(node.obj)
                self.tree.hasRom = True

            elif _isMem(node.obj):
                m = _getMemInfo(node.obj)
                if self.access == _access.INPUT:
                    m._read = True
                    if not isinstance(node.obj, list):
                        node.obj._read = True
                elif self.access == _access.OUTPUT:
                    m.driven = 'reg'
                    self.tree.outmems.add(n)
                elif self.access == _access.UNKNOWN:
                    pass
                else:
                    assert False, "unexpected mem access %s %s" % (n, self.access)
                self.tree.hasLos = True
                trace.print(repr(m))

            elif isinstance(node.obj, int):
                node.value = node.obj

            else:
                trace.print('symdict unhandled', n, repr(node.obj))

            if n in self.tree.nonlocaldict:
                # hack: put nonlocal intbv's in the vardict
                self.tree.vardict[n] = node.obj
                trace.print('hack: put nonlocal intbv\'s in the vardict', node.obj)

        elif n in builtins.__dict__:
            node.obj = builtins.__dict__[n]
            trace.print('builtins', n, repr(node.obj), self.access)

        else:
            self.raiseError(node, _error.UnboundLocal, n)
        trace.pop()

    def visit_Return(self, node):
        self.raiseError(node, _error.NotSupported, "return statement")

    def visit_Print(self, node):
        self.tree.hasPrint = True
        f = []
        nr = 0
        a = []

        if PY2 and isinstance(node, ast.Print):
            node_args = node.values
        else:
            node_args = node.args

        for n in node_args:
            if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Mod) and \
               isinstance(n.left, ast.Str):
                if isinstance(n.right, ast.Tuple):
                    a.extend(n.right.elts)
                else:
                    a.append(n.right)
                s = n.left.s
                while s:
                    if not s:
                        break
                    if s[:2] == "%%":
                        f.append("%")
                        s = s[2:]
                        continue
                    m = re_ConvSpec.match(s)
                    if m:
                        c = ConvSpec(**m.groupdict())
                        if c.justified != "RIGHT":
                            self.raiseError(node, _error.UnsupportedFormatString,
                                            "format justification specification: %s" % s)
                        if c.width != 0:
                            self.raiseError(node, _error.UnsupportedFormatString,
                                            "format width specification: %s" % s)
                        f.append(c)
                        s = s[m.end():]
                        nr += 1
                        continue
                    m = re_str.match(s)
                    if m:
                        f.append(s[:m.end()])
                        s = s[m.end():]
                        continue
                    self.raiseError(
                        node, _error.UnsupportedFormatString, "%s" % s)
            else:
                f.append(defaultConvSpec)
                a.append(n)
                nr += 1
            f.append(" ")
        # remove last single space if it exists
        if f:
            f.pop()
        node.format = f
        node.args = a
        if len(node.args) < nr:
            self.raiseError(node, _error.FormatString, "not enough arguments")
        if len(node.args) > nr:
            self.raiseError(node, _error.FormatString, "too many arguments")
        self.generic_visit(node)

    def visit_Subscript(self, node):
        if isinstance(node.slice, ast.Slice):
            self.accessSlice(node)
        else:
            self.accessIndex(node)

    def accessSlice(self, node):
        trace.push(message='accessSlice')
        trace.print(repr(node))
        self.visit(node.value)
        node.obj = self.getObj(node.value)
        trace.print(repr(node), repr(node.obj))
        self.access = _access.INPUT
        lower, upper = node.slice.lower, node.slice.upper
        if lower:
            self.visit(lower)
        if upper:
            self.visit(upper)
        if isinstance(node.obj, myhdl.intbv):
            if self.kind == _kind.DECLARATION:
                self.require(lower, "Expected leftmost index")
                leftind = self.getVal(lower)
                if upper:
                    rightind = self.getVal(upper)
                else:
                    rightind = 0
                node.obj = node.obj[leftind:rightind]
        elif isinstance(node.obj, Array):
            if lower:
                leftind = self.getVal(lower)
            else:
                leftind = 0

            if upper:
                rightind = self.getVal(upper)
            else:
                rightind = node.obj.shape[0]
            node.obj = node.obj[leftind:rightind]
        trace.pop()

    def accessIndex(self, node):
        trace.push(message='accessIndex')
        trace.print(self.access)
        self.visit(node.value)
        self.access = _access.INPUT
        self.visit(node.slice.value)

        if isinstance(node.value.obj, _Ram):
            if isinstance(node.ctx, ast.Store):
                self.raiseError(node, _error.ListElementAssign)
            else:
                node.obj = node.value.obj.elObj
        elif _isMem(node.value.obj) or isinstance(node.value.obj, list):
            node.obj = node.value.obj[0]

        elif isinstance(node.value.obj, Array):
            node.obj = node.value.obj[0]
#             node.obj = node.value.obj.element

        elif isinstance(node.value.obj, _Rom):
            node.obj = int(-1)
        elif isinstance(node.value.obj, myhdl.intbv):
            node.obj = bool()
        else:
            node.obj = bool()  # XXX default
        trace.print(node, node.value, repr(node.value.obj), repr(node.obj))
        trace.pop()

    def visit_Tuple(self, node):
        self.generic_visit(node)

    def visit_While(self, node):
        node.breakLabel = _Label("BREAK")
        node.loopLabel = _Label("LOOP")
        self.labelStack.append(node.breakLabel)
        self.labelStack.append(node.loopLabel)
        self.visit(node.test)
        self.refStack.push()
        for n in node.body:
            self.visit(n)
        self.refStack.pop()
        y = node.body[0]
        if isinstance(y, ast.Expr):
            y = y.value
        if node.test.obj == True and \
           isinstance(y, ast.Yield) and \
           not self.tree.hasYield > 1 and \
           not isinstance(self.getObj(y.value), myhdl.delay):
            node.kind = _kind.ALWAYS
            self.tree.senslist = y.senslist
        self.require(node, not node.orelse, "while-else not supported")
        self.labelStack.pop()
        self.labelStack.pop()

    def visit_Yield(self, node, *args):
        self.tree.hasYield += 1
        n = node.value
        self.visit(n)
        senslist = []
        if isinstance(n, ast.Tuple):
            for n in n.elts:
                if not isinstance(n.obj, (_Signal, _WaiterList)):
                    self.raiseError(node, _error.UnsupportedYield)
                senslist.append(n.obj)
        elif isinstance(n.obj, (_Signal, _WaiterList, myhdl.delay)):
            senslist = [n.obj]
        elif _isMem(n.obj):
            senslist = n.obj
        else:
            self.raiseError(node, _error.UnsupportedYield)
        node.senslist = senslist


class _AnalyzeBlockVisitor(_AnalyzeVisitor):

    def __init__(self, tree):
        _AnalyzeVisitor.__init__(self, tree)
        for n, v in self.tree.symdict.items():
            if isinstance(v, _Signal):
                self.tree.sigdict[n] = v

    def visit_FunctionDef(self, node):
        self.refStack.push()
        for n in node.body:
            self.visit(n)
        self.tree.kind = _kind.ALWAYS
        for n in node.body[:-1]:
            if not self.getKind(n) == _kind.DECLARATION:
                self.tree.kind = _kind.INITIAL
                break
        if self.tree.kind == _kind.ALWAYS:
            w = node.body[-1]
            if not self.getKind(w) == _kind.ALWAYS:
                self.tree.kind = _kind.INITIAL
        self.refStack.pop()

    def visit_Module(self, node):
        trace.push(message='visit_Module')
        trace.print('node, node.body:', node, node.body)
        for t in node.body:
            trace.print(t.name)
        self.generic_visit(node)
        for n in self.tree.outputs:
            s = self.tree.sigdict[n]
            trace.print('n, s:', repr(n), repr(s))
            for item in self.tree.sigdict.keys():
                trace.print(repr(item), repr(self.tree.sigdict[item]), id(self.tree.sigdict[item]))
            if s.driven:
                var2 = [x for x in globals().values() if id(x) == id(self.tree.sigdict[item])]
                self.raiseError(node, _error.SigMultipleDriven, '{} {} <> {}'.format(n, self.tree.inputs, var2))
            s.driven = "reg"
        for n in self.tree.inputs:
            s = self.tree.sigdict[n]
            s._markRead()
        trace.print('Closing.')
        trace.pop()

    def visit_Return(self, node):
        # ## value should be None
        if node.value is None:
            pass
        elif isinstance(node.value, ast.Name) and node.value.id == "None":
            pass
        else:
            self.raiseError(
                node, _error.NotSupported, "return value other than None")


class _AnalyzeAlwaysCombVisitor(_AnalyzeBlockVisitor):

    def __init__(self, tree, senslist):
        _AnalyzeBlockVisitor.__init__(self, tree)
        self.tree.senslist = senslist

    def visit_FunctionDef(self, node):
        self.refStack.push()
        for n in node.body:
            self.visit(n)
        self.tree.kind = _kind.SIMPLE_ALWAYS_COMB
        for n in node.body:
            if isinstance(n, ast.Expr) and isinstance(n.value, ast.Str):
                continue  # skip doc strings
            if isinstance(n, ast.Assign) and \
               isinstance(n.targets[0], ast.Attribute) and \
               self.getKind(n.targets[0].value) != _kind.REG:
                pass
            else:
                self.tree.kind = _kind.ALWAYS_COMB
                return
        # rom access is expanded into a case statement in addition
        # to any always_comb that contains a list of signals
        # if self.tree.hasRom or self.tree.hasLos:
        if self.tree.hasRom:
            self.tree.kind = _kind.ALWAYS_COMB
        self.refStack.pop()

    def visit_Module(self, node):
        _AnalyzeBlockVisitor.visit_Module(self, node)
        if self.tree.kind == _kind.SIMPLE_ALWAYS_COMB:
            trace.print('_kind.SIMPLE_ALWAYS_COMB:', node, self.tree.outputs)
            for n in self.tree.outputs:
                s = self.tree.sigdict[n]
                s.driven = "wire"
            for n in self.tree.outmems:
                m = _getMemInfo(self.tree.symdict[n])
                m.driven = "wire"


class _AnalyzeAlwaysSeqVisitor(_AnalyzeBlockVisitor):

    def __init__(self, tree, senslist, reset, sigregs, varregs):
        _AnalyzeBlockVisitor.__init__(self, tree)
        self.tree.senslist = senslist
        self.tree.reset = reset
        self.tree.sigregs = sigregs
        self.tree.varregs = varregs

    def visit_FunctionDef(self, node):
        trace.push(message='_AnalyzeAlwaysSeqVisitor visit_FunctionDef <{}>'.format(node.name))
        trace.print(vars(node))
        self.refStack.push()
        for n in node.body:
            self.visit(n)
        self.tree.kind = _kind.ALWAYS_SEQ
        self.refStack.pop()
        trace.pop()


class _AnalyzeAlwaysDecoVisitor(_AnalyzeBlockVisitor):

    def __init__(self, tree, senslist):
        _AnalyzeBlockVisitor.__init__(self, tree)
        self.tree.senslist = senslist

    def visit_FunctionDef(self, node):
        self.refStack.push()
        for n in node.body:
            self.visit(n)
        self.tree.kind = _kind.ALWAYS_DECO
        self.refStack.pop()


class _AnalyzeFuncVisitor(_AnalyzeVisitor):

    def __init__(self, tree, args, keywords):
        _AnalyzeVisitor.__init__(self, tree)
        self.args = args
        self.keywords = keywords
        self.tree.hasReturn = False
        self.tree.returnObj = None

    def visit_FunctionDef(self, node):
        self.refStack.push()
        argnames = _get_argnames(node)
        for i, arg in enumerate(self.args):
            n = argnames[i]
            self.tree.symdict[n] = self.getObj(arg)
            self.tree.argnames.append(n)
        for kw in self.keywords:
            n = kw.arg
            self.tree.symdict[n] = self.getObj(kw.value)
            self.tree.argnames.append(n)
        for n, v in self.tree.symdict.items():
            if isinstance(v, (_Signal, myhdl.intbv)):
                self.tree.sigdict[n] = v
        for stmt in node.body:
            self.visit(stmt)
        self.refStack.pop()
        if self.tree.hasYield:
            self.raiseError(node, _error.NotSupported,
                            "call to a generator function")
        if self.tree.kind == _kind.TASK:
            if self.tree.returnObj is not None:
                self.raiseError(node, _error.NotSupported,
                                "function with side effects and return value")
        else:
            if self.tree.returnObj is None:
                self.raiseError(node, _error.NotSupported,
                                "pure function without return value")

    def visit_Return(self, node):
        self.kind = _kind.DECLARATION
        if node.value is not None:
            self.visit(node.value)
        self.kind = _kind.NORMAL
        if node.value is None:
            obj = None
        elif isinstance(node.value, ast.Name) and node.value.id == 'None':
            obj = None
        elif node.value.obj is not None:
            obj = node.value.obj
        else:
            self.raiseError(node, _error.ReturnTypeInfer)
        if isinstance(obj, myhdl.intbv) and len(obj) == 0:
            self.raiseError(node, _error.ReturnIntbvBitWidth)
        if self.tree.hasReturn:
            returnObj = self.tree.returnObj
            if isinstance(obj, type(returnObj)):
                pass
            elif isinstance(returnObj, type(obj)):
                self.tree.returnObj = obj
            else:
                self.raiseError(node, _error.ReturnTypeMismatch)
            if getNrBits(obj) != getNrBits(returnObj):
                self.raiseError(node, _error.ReturnNrBitsMismatch)
        else:
            self.tree.returnObj = obj
            self.tree.hasReturn = True


ismethod = inspect.ismethod
# inspect doc is wrong: ismethod checks both bound and unbound methods


def isboundmethod(m):
    return ismethod(m) and m.__self__ is not None


# a local function to drill down to the last interface
def expandinterface(v, name, obj):
    trace.print(v, name, obj)
    for attr, attrobj in vars(obj).items():
        if isinstance(attrobj, _Signal):
            #                     signame = attrobj._name
            #                     if not signame:
            #                         signame = name + '_' + attr
            #                         attrobj._name = signame
            #                     signame = name + '_' + attr
            signame = name + attr
            attrobj._name = signame
            # check if already in
#                     if v.fullargdict.has_key(signame):
#                         raise ConversionError(_error.NameCollision, signame)
            v.argdict[signame] = attrobj
            v.argnames.append(signame)
        elif isinstance(attrobj, myhdl.EnumType):
            pass
        elif hasattr(attrobj, '__dict__'):
                    # can assume is yet another interface ...
            expandinterface(v, name + '_' + attr, attrobj)


def _analyzeTopFunc(top_inst, func, *args, **kwargs):
    trace.push(False, '_analyzeTopFunc')
    trace.print('_analyzeTopFunc')
    tree = _makeAST(func)
    v = _AnalyzeTopFuncVisitor(func, tree, *args, **kwargs)
    v.visit(tree)

    # collect the interface objects if any
    objs = []
    for name, obj in v.fullargdict.items():
        if not isinstance(obj, _Signal):
            objs.append((name, obj))

    # now expand the interface objects
    for name, obj in objs:
        if isinstance(obj, (StructType, Array)):
            # do not expand StructTypes or Arrays
            # toVHDL will handle this
            v.argdict[name] = obj
            v.argnames.append(name)
        elif hasattr(obj, '__dict__'):
            # must be an interface object (probably ...?)
            expandinterface(v, name, obj)

    trace.pop()
    return v


class _AnalyzeTopFuncVisitor(_AnalyzeVisitor):

    def __init__(self, func, tree, *args, **kwargs):
        self.func = func
        self.tree = tree
        self.args = args
        self.kwargs = kwargs
        self.name = None
        self.fullargdict = {}
        self.argdict = {}
        self.argnames = []

    def visit_FunctionDef(self, node):
        self.name = node.name
        self.argnames = _get_argnames(node)
        if isboundmethod(self.func):
            if not self.argnames[0] == 'self':
                self.raiseError(node, _error.NotSupported,
                                "first method argument name other than 'self'")
            # skip self
            self.argnames = self.argnames[1:]
        i = -1
        for i, arg in enumerate(self.args):
            n = self.argnames[i]
            self.fullargdict[n] = arg
            if isinstance(arg, _Signal):
                self.argdict[n] = arg
#             if _isMem(arg):
#                 if isinstance(arg, StructType):
#                     pass
#                 else:
#                     self.raiseError(node, _error.ListAsPort, n)
#                 self.raiseError(node, _error.ListAsPort, n)

        for n in self.argnames[i + 1:]:
            if n in self.kwargs:
                arg = self.kwargs[n]
                self.fullargdict[n] = arg
                if isinstance(arg, _Signal):
                    self.argdict[n] = arg
                if _isMem(arg):
                    self.raiseError(node, _error.ListAsPort, n)
        self.argnames = [n for n in self.argnames if n in self.argdict]

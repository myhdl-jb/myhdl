#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2008 Jan Decaluwe
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

""" myhdl _extractHierarchy module.

"""
from __future__ import absolute_import, print_function


import sys
import inspect
import collections

# from inspect import currentframe, getframeinfo, getouterframes
# import re
import string
# from types import GeneratorType
# import linecache

from myhdl import ExtractHierarchyError, ToVerilogError, ToVHDLError
from myhdl._Signal import _Signal, _isListOfSigs
from myhdl._util import _isGenFunc, _flatten, _genfunc
from myhdl._misc import _isGenSeq, m1Dinfo
from myhdl._resolverefs import _resolveRefs
from myhdl._getcellvars import _getCellVars

from myhdl._structured import StructType, Array

from myhdl.tracejb import Tracing

trace = Tracing(False, source='_extractHierarchy')
_profileFunc = None


class _error:
    pass
_error.NoInstances = "No instances found"
_error.InconsistentHierarchy = "Inconsistent hierarchy - are all instances returned ?"
_error.InconsistentToplevel = "Inconsistent top level %s for %s - should be 1"


class _Instance(object):
    __slots__ = ['level', 'obj', 'subs', 'sigdict',
                 'memdict', 'name', 'func', 'argdict', 'objdict']

    def __init__(self, level, obj, subs, sigdict, memdict, func, argdict, objdict=None):
        self.level = level
        self.obj = obj
        self.subs = subs
        self.sigdict = sigdict
        self.memdict = memdict
        self.func = func
        self.argdict = argdict
        if objdict:
            self.objdict = objdict

    def __repr__(self):
        #         lines = ['_Instance\n\tlevel: {}'.format(self.level)]
        #         for entry in [self.obj, self.subs, self.sigdict, self.memdict, self.func]:
        #             sublines = []
        #             for item in self.obj:
        #                 sublines.append('\t\t{}'.format(item))
        #             lines.extend( '\{}'.format(sublines))

        return '_Instance\n\tlevel: {}\n\tobj: {}\n\tsubs: {}\n\tsigdict: {}\n\tmemdict: {}\n\tfunc: {}\n\targdict: {}' \
            .format(self.level, self.obj, self.subs, self.sigdict, self.memdict, self.func, self.argdict)

_memInfoMap = collections.OrderedDict()  # {}


class _MemInfo(object):
    __slots__ = ['mem', 'name', 'elObj', 'depth', '_used', '_driven',
                 '_read', 'levels', '_sizes', '_typedef', 'usagecount']

    def __init__(self, mem, levels, sizes, totalelements, element):
        self.mem = mem
#         trace.print('_MemInfo', repr(mem))
        self.name = None
        self.depth = totalelements
        self.elObj = element
        self.levels = levels
        self._sizes = sizes
        self._used = False
        self._driven = None
        self._read = None
        self._typedef = None
        self.usagecount = 1

    def __repr__(self):
        return "_MemInfo: {}, {} of {}, used: {}, driven: {}, read: {}".format(self.name, self.depth,
                                                                               repr(self.elObj), self._used, self._driven, self._read)

    # support for the 'driven' attribute
    @property
    def driven(self):
        #         if isinstance(self.mem, (Array, StructType)):
        #             return self.mem.driven
        #         else:
        #             return self._driven
        return self._driven

    @driven.setter
    def driven(self, val):
        if not val in ("reg", "wire", True):
            raise ValueError(
                'Expected value "reg", "wire", or True, got "%s"' % val)
        self._driven = val


def _getMemInfo(mem):
    return _memInfoMap[id(mem)]


def _makeMemInfo(mem, levels, sizes, totalelements, element):
    key = id(mem)
    if key not in _memInfoMap:
        #         trace.print( '_makeMemInfo', key, mem, levels, sizes, totalelements, element )
        _memInfoMap[key] = _MemInfo(mem, levels, sizes, totalelements, element)
    return _memInfoMap[key]


def _isMem(mem):
    return id(mem) in _memInfoMap

_userCodeMap = {'verilog': {},
                'vhdl': {}
                }


class _UserCode(object):
    __slots__ = ['code', 'namespace', 'funcname',
                 'func', 'sourcefile', 'sourceline']

    def __init__(self, code, namespace, funcname, func, sourcefile, sourceline):
        self.code = code
        self.namespace = namespace
        self.sourcefile = sourcefile
        self.func = func
        self.funcname = funcname
        self.sourceline = sourceline

    def __str__(self):
        try:
            code = self._interpolate()
        except:
            type, value, tb = sys.exc_info()
            info = "in file %s, function %s starting on line %s:\n    " % \
                   (self.sourcefile, self.funcname, self.sourceline)
            msg = "%s: %s" % (type, value)
            self.raiseError(msg, info)
        code = "\n%s\n" % code
        return code

    def _interpolate(self):
        return string.Template(self.code).substitute(self.namespace)


class _UserCodeDepr(_UserCode):

    def _interpolate(self):
        return self.code % self.namespace


class _UserVerilogCode(_UserCode):

    def raiseError(self, msg, info):
        raise ToVerilogError("Error in user defined Verilog code", msg, info)


class _UserVhdlCode(_UserCode):

    def raiseError(self, msg, info):
        raise ToVHDLError("Error in user defined VHDL code", msg, info)


class _UserVerilogCodeDepr(_UserVerilogCode, _UserCodeDepr):
    pass


class _UserVhdlCodeDepr(_UserVhdlCode, _UserCodeDepr):
    pass


class _UserVerilogInstance(_UserVerilogCode):

    def __str__(self):
        args = inspect.getargspec(self.func)[0]
        s = "%s %s(" % (self.funcname, self.code)
        sep = ''
        for arg in args:
            if arg in self.namespace and isinstance(self.namespace[arg], _Signal):
                signame = self.namespace[arg]._name
                s += sep
                sep = ','
                s += "\n    .%s(%s)" % (arg, signame)
        s += "\n);\n\n"
        return s


class _UserVhdlInstance(_UserVhdlCode):

    def __str__(self):
        args = inspect.getargspec(self.func)[0]
        s = "%s: entity work.%s(MyHDL)\n" % (self.code, self.funcname)
        s += "    port map ("
        sep = ''
        for arg in args:
            if arg in self.namespace and isinstance(self.namespace[arg], _Signal):
                signame = self.namespace[arg]._name
                s += sep
                sep = ','
                s += "\n        %s=>%s" % (arg, signame)
        s += "\n    );\n\n"
        return s


def _addUserCode(specs, arg, funcname, func, frame):
    classMap = {
        '__verilog__': _UserVerilogCodeDepr,
        '__vhdl__': _UserVhdlCodeDepr,
        'verilog_code': _UserVerilogCode,
        'vhdl_code': _UserVhdlCode,
        'verilog_instance': _UserVerilogInstance,
        'vhdl_instance': _UserVhdlInstance,

    }
    namespace = frame.f_globals.copy()
    namespace.update(frame.f_locals)
    sourcefile = inspect.getsourcefile(frame)
    sourceline = inspect.getsourcelines(frame)[1]
    for hdl in _userCodeMap:
        oldspec = "__%s__" % hdl
        codespec = "%s_code" % hdl
        instancespec = "%s_instance" % hdl
        spec = None
        # XXX add warning logic
        if instancespec in specs:
            spec = instancespec
        elif codespec in specs:
            spec = codespec
        elif oldspec in specs:
            spec = oldspec
        if spec:
            assert id(arg) not in _userCodeMap[hdl]
            code = specs[spec]
            _userCodeMap[hdl][id(arg)] = classMap[spec](
                code, namespace, funcname, func, sourcefile, sourceline)


class _CallFuncVisitor(object):

    def __init__(self):
        self.linemap = {}

    def visitAssign(self, node):
        if isinstance(node.expr, ast.CallFunc):
            self.lineno = None
            self.visit(node.expr)
            self.linemap[self.lineno] = node.lineno

    def visitName(self, node):
        self.lineno = node.lineno


class _HierExtr(object):

    def __init__(self, name, dut, *args, **kwargs):

        def _nDname(top, name, obj):
            ''' a local (recursive) subroutine '''
            names[id(obj)] = name
            absnames[id(obj)] = '{}_{}'.format(top, name)
#             trace.print('{}_{}'.format(top, name))
            if isinstance(obj, (tuple, list)):
                for i, item in enumerate(obj):
                    _nDname(top, '{}{}'.format(name, i), item)

        global _profileFunc
        _memInfoMap.clear()
        for hdl in _userCodeMap:
            _userCodeMap[hdl].clear()
        self.skipNames = ('always_comb', 'instance',
                          'always_seq', '_always_seq_decorator',
                          'always', '_always_decorator',
                          'instances',
                          'processes', 'posedge', 'negedge')
        self.skip = 0
        self.hierarchy = hierarchy = []
        self.absnames = absnames = collections.OrderedDict()  # {}
        self.level = 0

        _profileFunc = self.extractor
        sys.setprofile(_profileFunc)
        _top = dut(*args, **kwargs)
        sys.setprofile(None)
        if not hierarchy:
            raise ExtractHierarchyError(_error.NoInstances)
        self.top = _top

        # streamline hierarchy
        hierarchy.reverse()
        # walk the hierarchy to define relative and absolute names
        names = {}  # collections.OrderedDict() #{}

        top_inst = hierarchy[0]
        obj, subs = top_inst.obj, top_inst.subs
        names[id(obj)] = name
        absnames[id(obj)] = name
        if not top_inst.level == 1:
            raise ExtractHierarchyError(
                _error.InconsistentToplevel % (top_inst.level, name))
        for inst in hierarchy:
            #             trace.print(repr(inst))
            obj, subs = inst.obj, inst.subs
            if id(obj) not in names:
                raise ExtractHierarchyError(_error.InconsistentHierarchy)
            inst.name = names[id(obj)]
            tn = absnames[id(obj)]
            for sn, so in subs:
                sns = sn[:-3] if sn[-3:] == 'rtl' else sn
                _nDname(tn, sns, so)

    def extractor(self, frame, event, arg):
        if event == "call":
            funcname = frame.f_code.co_name
            # skip certain functions
            if funcname in self.skipNames:
                self.skip += 1
            if not self.skip:
                self.level += 1

        elif event == "return":
            trace.push(False, '_HierExtr: return')
            funcname = frame.f_code.co_name
            func = frame.f_globals.get(funcname)
            if func is None:
                # Didn't find a func in the global space, try the local "self"
                # argument and see if it has a method called *funcname*
                obj = frame.f_locals.get('self')
                if hasattr(obj, funcname):
                    func = getattr(obj, funcname)

            if not self.skip:
                isGenSeq = _isGenSeq(arg)
                if isGenSeq:
                    specs = {}  # collections.OrderedDict() #{}
                    for hdl in _userCodeMap:
                        spec = "__%s__" % hdl
                        if spec in frame.f_locals and frame.f_locals[spec]:
                            specs[spec] = frame.f_locals[spec]
                        spec = "%s_code" % hdl
                        if func and hasattr(func, spec) and getattr(func, spec):
                            specs[spec] = getattr(func, spec)
                        spec = "%s_instance" % hdl
                        if func and hasattr(func, spec) and getattr(func, spec):
                            specs[spec] = getattr(func, spec)
                    if specs:
                        _addUserCode(specs, arg, funcname, func, frame)
                # building hierarchy only makes sense if there are generators
                if isGenSeq and arg:
                    sigdict = {}  # collections.OrderedDict() #{}
                    memdict = {}  # collections.OrderedDict() #{}
                    argdict = {}  # collections.OrderedDict() #{}
                    if func:
                        arglist = inspect.getargspec(func).args
                    else:
                        arglist = []
                    symdict = frame.f_globals.copy()
                    symdict.update(frame.f_locals)
                    cellvars = []
                    # All nested functions will be in co_consts
                    if func:
                        local_gens = []
                        consts = func.__code__.co_consts
                        for item in _flatten(arg):
                            genfunc = _genfunc(item)
                            if genfunc.__code__ in consts:
                                local_gens.append(item)
                        if local_gens:
                            cellvarlist = _getCellVars(symdict, local_gens)
                            cellvars.extend(cellvarlist)
                            # TODO: must re-work this to let 'interfaces' work
                            # as before
                            objlist = _resolveRefs(symdict, local_gens)
                            cellvars.extend(objlist)

                    # the last one passing by is the top module ...
#                     for n, v in nsymdict.items():
                    for n, v in symdict.items():
                        # extract signals and memories
                        # also keep track of whether they are used in generators
                        # only include objects that are used in generators
                        # #                             if not n in cellvars:
                        # #                                 continue
                        if isinstance(v, _Signal):
                            trace.print('level {} Signal {} {}, used: {}, driven: {}, read: {}'.format(self.level, n, repr(v),
                                                                                                       v._used, v._driven, v._read))
                            sigdict[n] = v
                            if n in cellvars:
                                v._markUsed()

                        elif isinstance(v, list):
                            trace.print('level {} list {} {}'.format(self.level, n, v))
                            if len(v) > 0:
                                levels, sizes, totalelements, element = m1Dinfo(v)
                                if isinstance(element, (_Signal, Array, StructType)):
                                    m = _makeMemInfo(v, levels, sizes, totalelements, element)
                                    memdict[n] = m
                                    if n in cellvars:
                                        m._used = True

                                    if isinstance(element, (Array)):
                                        if isinstance(v[0], list):
                                            raise ValueError('don\'t handle nested lists', repr(v))
                                        else:
                                            # instantiate every element separately
                                            for i, a in enumerate(v):
                                                m = _makeMemInfo(a, len(a.shape), a.shape, a.size, element)
                                                m.name = n + '({})'.format(str(i))
                                                memdict[m.name] = m
                                                trace.print('\t', m.name, m)
#                                                 for item in m.mem:
#                                                     trace.print('\t', m._driven)
                                                if m.name in cellvars:
                                                    m._used = True
#                                 else:
#                                     trace.print(repr(element))

                        elif isinstance(v, Array):
                            # only enter 'top' Arrays, i.e. not Arrays that are
                            # a member of StructType(s)
                            trace.print('level {} Array {} {}'.format(self.level, n, repr(v)))
                            if '.' not in n:
                                # we have all information handy in the Array
                                # object
                                m = _makeMemInfo(v, v.levels, v.shape, v.size, v.element)
                                memdict[n] = m
                                if n in cellvars:
                                    m._used = True
                                    m._driven = v.driven

                        elif isinstance(v, StructType):
                            trace.print('_HierExtr {} StructType {} {}'.format(self.level, n, v))
                            # only enter 'top' StructTypes, i.e. not the nested
                            # StructType(s)
                            if '.' not in n:
                                # should also be entered in the memdict
                                m = _makeMemInfo(v, 1, 1, 1, v)
                                memdict[n] = m
                                if n in cellvars:
                                    m._used = True
                                    m._driven = v.driven

                        # save any other variable in argdict
                        if (n in arglist) and (n not in sigdict) and (n not in memdict):
                            argdict[n] = v

                    subs = []
                    for n, sub in frame.f_locals.items():
                        for elt in _inferArgs(arg):
                            if elt is sub:
                                subs.append((n, sub))

                    inst = _Instance(self.level, arg, subs, sigdict, memdict, func, argdict)
                    self.hierarchy.append(inst)

                self.level -= 1

            if funcname in self.skipNames:
                self.skip -= 1
            trace.pop()


def _inferArgs(arg):
    #     tracejb('_inferArgs')
    c = [arg]
    if isinstance(arg, (tuple, list)):
        c += list(arg)
#     logjb( c, arg )
#     tracejbdedent()
    return c

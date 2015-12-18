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
from __future__ import absolute_import


import sys
import inspect
from inspect import currentframe, getframeinfo, getouterframes
import re
import string
from types import GeneratorType
import linecache

from myhdl import ExtractHierarchyError, ToVerilogError, ToVHDLError
from myhdl._Signal import _Signal, _isListOfSigs
from myhdl._util import _isGenFunc, _flatten, _genfunc
from myhdl._misc import _isGenSeq, m1Dinfo
from myhdl._resolverefs import _resolveRefs
from myhdl._getcellvars import _getCellVars

from myhdl._structured import StructType


# tracing the poor man's way
TRACING_JB = True
if TRACING_JB:
    from myhdl.tracejb import tracejb, logjb, tracejbdedent, logjbinspect
else:
    def tracejb( a, b = None):
        pass
    def logjb(a, b = None, c = False):
        pass
    def tracejbdedent():
        pass
    def logjbinspect(a, b= None):
        pass

_profileFunc = None

class _error:
    pass
_error.NoInstances = "No instances found"
_error.InconsistentHierarchy = "Inconsistent hierarchy - are all instances returned ?"
_error.InconsistentToplevel = "Inconsistent top level %s for %s - should be 1"


class _Instance(object):
    __slots__ = ['level', 'obj', 'subs', 'sigdict', 'memdict', 'name', 'func', 'argdict', 'objdict']
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


_memInfoMap = {}

class _MemInfo(object):
    __slots__ = ['mem', 'name', 'elObj', 'depth', '_used', '_driven', '_read', 'levels', '_sizes', '_typedef']
    def __init__(self, mem, levels, sizes, totalelements, element):
        self.mem = mem
        self.name = None
        self.depth = totalelements
        self.elObj = element
        self.levels = levels
        self._sizes = sizes
        self._used = False
        self._driven = None
        self._read = None
        self._typedef = None


def _getMemInfo(mem):
    return _memInfoMap[id(mem)]

def _makeMemInfo(mem, levels, sizes, totalelements, element):
    key = id(mem)
    if key not in _memInfoMap:
        _memInfoMap[key] = _MemInfo(mem, levels, sizes, totalelements, element)
    return _memInfoMap[key]

def _isMem(mem):
    return id(mem) in _memInfoMap

_userCodeMap = {'verilog' : {},
                'vhdl' : {}
               }

class _UserCode(object):
    __slots__ = ['code', 'namespace', 'funcname', 'func', 'sourcefile', 'sourceline']
    def __init__(self, code, namespace, funcname, func, sourcefile, sourceline):
        self.code = code
        self.namespace = namespace
        self.sourcefile = sourcefile
        self.func = func
        self.funcname = funcname
        self.sourceline = sourceline

    def __str__(self):
        try:
            code =  self._interpolate()
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
                '__verilog__' : _UserVerilogCodeDepr,
                '__vhdl__' :_UserVhdlCodeDepr,
                'verilog_code' : _UserVerilogCode,
                'vhdl_code' :_UserVhdlCode,
                'verilog_instance' : _UserVerilogInstance,
                'vhdl_instance' :_UserVhdlInstance,

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
            _userCodeMap[hdl][id(arg)] = classMap[spec](code, namespace, funcname, func, sourcefile, sourceline)


class _CallFuncVisitor(object):

    def __init__(self):
        self.linemap = {}

    def visitAssign(self, node):
#         tracejb('_CallFuncVisitor: ' + 'visitAssign')
        if isinstance(node.expr, ast.CallFunc):
            self.lineno = None
            self.visit(node.expr)
            self.linemap[self.lineno] = node.lineno
#         tracejbdedent()

    def visitName(self, node):
#         tracejb('_CallFuncVisitor: ' + 'visitName')
        self.lineno = node.lineno
#         tracejbdedent()



class _HierExtr(object):

    def __init__(self, name, dut, *args, **kwargs):

        # a local (recursive) subroutine
        def _nDname(top, name, obj):
                names[id(obj)] = name
                absnames[id(obj)] = "%s_%s" % (top, name)
                if isinstance(obj, (tuple, list)):
                    for i, item in enumerate(obj):
                        _nDname(top, '{}{}'.format(name, i), item)


        tracejb( name , '_HierExtr: __init__')
        logjb(dut, 'dut')
        logjb(args, 'args')
        logjb(kwargs, 'kwargs')
        global _profileFunc
        _memInfoMap.clear()
        for hdl in _userCodeMap:
            _userCodeMap[hdl].clear()
        self.skipNames = ('always_comb', 'instance', \
                          'always_seq', '_always_seq_decorator', \
                          'always', '_always_decorator', \
                          'instances', \
                          'processes', 'posedge', 'negedge')
        self.skip = 0
        self.hierarchy = hierarchy = []
        self.absnames = absnames = {}
        self.level = 0

        logjb('Start extraction ===========================')
        _profileFunc = self.extractor
        sys.setprofile(_profileFunc)
        _top = dut(*args, **kwargs)
        logjb('End extraction? ===========================')
        sys.setprofile(None)
        if not hierarchy:
            raise ExtractHierarchyError(_error.NoInstances)

        tracejb( hierarchy, "hierarchy" )
        logjb( _top , "top")
        self.top = _top

        # streamline hierarchy
        logjb( hierarchy , "start reversing hierarchy")
        hierarchy.reverse()
        logjb( hierarchy , "reversed hierarchy")
        # walk the hierarchy to define relative and absolute names
        names = {}
        logjb(names , "names {}")
        top_inst = hierarchy[0]
        obj, subs = top_inst.obj, top_inst.subs
        names[id(obj)] = name
        absnames[id(obj)] = name
        logjb( name, 'added name')
        logjb(names , "names (1) ")
        if not top_inst.level == 1:
            logjbinspect(top_inst, 'top_inst', True)
            raise ExtractHierarchyError(_error.InconsistentToplevel % (top_inst.level, name))
        for inst in hierarchy:
            tracejb( inst , "next inst" )
            obj, subs = inst.obj, inst.subs
            logjb( obj , 'obj', True)
            logjb( id(obj) , "id(obj)")
            tracejb('subs')
            for item in subs:
                logjb(item)
            tracejbdedent()
            if id(obj) not in names:
                logjb(names , " id(obj) not found in names")
                logjbinspect( obj , 'obj', True)
                logjbinspect( id(obj) , 'id(obj)', True)
                raise ExtractHierarchyError(_error.InconsistentHierarchy)
            inst.name = names[id(obj)]
            logjb(names[id(obj)], "inst.name")
            tn = absnames[id(obj)]
            logjb( tn, "absnames[id(obj)]")
            tracejb( subs, "next subs" )
            for sn, so in subs:
                _nDname(tn, sn, so)
            tracejbdedent()
            tracejbdedent()
        tracejbdedent()
        tracejbdedent()


            

    def extractor(self, frame, event, arg): 
        if event == "call":
            funcname = frame.f_code.co_name
#             logjb(funcname , 'funcname')
            # skip certain functions
            if funcname in self.skipNames:
                self.skip +=1
            if not self.skip:
                self.level += 1

        elif event == "return":
            funcname = frame.f_code.co_name
            func = frame.f_globals.get(funcname)
            if func is None:
                logjb('func is None?')
                # Didn't find a func in the global space, try the local "self"
                # argument and see if it has a method called *funcname*
                obj = frame.f_locals.get('self')
                if hasattr(obj, funcname):
                    logjb(obj, 'obj', True)
                    logjb( funcname, 'funcname')
                    func = getattr(obj, funcname)

            if not self.skip:
                isGenSeq = _isGenSeq(arg)
                if isGenSeq:
                    logjb( arg, 'extractor isGenSeq')
                    specs = {}
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
                    logjb( arg, 'isGenSeq and arg')
                    sigdict = {}
                    memdict = {}
                    argdict = {}
                    if func:
                        arglist = inspect.getargspec(func).args
                    else:
                        arglist = []
                    logjb( arglist, 'arglist')
                    symdict = frame.f_globals.copy()
                    symdict.update(frame.f_locals)
                    cellvars = []

                    #All nested functions will be in co_consts
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
                            objlist = _resolveRefs(symdict, local_gens)
                            cellvars.extend(objlist)
                                                        
                    #for dict in (frame.f_globals, frame.f_locals):
#                     print( symdict )
                    for n, v in symdict.items():
                        # extract signals and memories
                        # also keep track of whether they are used in generators
                        # only include objects that are used in generators
##                             if not n in cellvars:
##                                 continue
#                         logjb( n, 'n', True)
#                         logjb( v, 'v')
                        if isinstance(v, _Signal):
                            logjb( 'is _Signal')
                            sigdict[n] = v
                            if n in cellvars:
                                v._markUsed()
#                         elif _isListOfSigs(v):
#                             m = _makeMemInfo(v)
#                             memdict[n] = m
#                             if n in cellvars:
#                                 m._used = True

                        elif isinstance(v, list):
                            if len(v) > 0:
                                logjb( 'is _list')
#                                 logjb( n, 'n', True)
#                                 logjb( v, 'v')
                                levels, sizes, totalelements, element = m1Dinfo( v )
                                if isinstance(element, _Signal):
                                    m = _makeMemInfo(v, levels, sizes, totalelements, element ) 
                                    logjb( m, 'm')
                                    memdict[n] = m
                                    if n in cellvars:
                                        m._used = True
                                
                        elif isinstance(v,  Array):
                            logjb( 'is _Array')
#                             logjb( n, 'n', True)
#                             logjb( v, 'v')
                            # we have all information handy in the Array object
                            m = _makeMemInfo(v, v.levels, v._sizes, v.totalelements, v.element ) 
                            logjb( m, 'm')
                            memdict[n] = m
                            if n in cellvars:
                                m._used = True
                                
                        elif isinstance(v, StructType):       
                            logjb(vars(v), 'Struct ...')   
                            logjb(dir(v), 'Struct ...')  
                            logjb( v.__class__.__name__ , 'v.__class__') 
                            # should also be entered in the memdict   
                            m = _makeMemInfo(v, 1, 1, 1, v ) 
                            logjb( m, 'm')
                            memdict[n] = m
                            if n in cellvars:
                                m._used = True
                            
                        # save any other variable in argdict
                        if (n in arglist) : #and (n not in sigdict) and (n not in memdict):
                            logjb( n, 'stored in argdict[n]', True)
#                             logjb( v, 'value')
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

#         else:
#             tracejb( 'no action', '_HierExtr extractor')


def _inferArgs(arg):
#     tracejb('_inferArgs')
    c = [arg]
    if isinstance(arg, (tuple, list)):
        c += list(arg)
#     logjb( c, arg )
#     tracejbdedent()
    return c

from myhdl._array import Array

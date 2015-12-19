#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2009 Jan Decaluwe
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

#  You should have received a copy of the GNU Lesser General Public
#  License along with this library; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

""" Module with the always_comb function. """
from __future__ import absolute_import

import sys
import inspect
from types import FunctionType
import re
import ast

from myhdl import AlwaysCombError
from myhdl._Signal import _Signal, _isListOfSigs
from myhdl._util import _isGenFunc, _dedent
from myhdl._Waiter import _Waiter, _SignalWaiter, _SignalTupleWaiter
from myhdl._instance import _Instantiator
from myhdl._always import _Always
from myhdl._resolverefs import _AttrRefTransformer
from myhdl._visitors import _SigNameVisitor

from myhdl._misc import m1Dinfo
from myhdl._structured import Array, StructType


# # tracing the poor man's way
from myhdl.tracejb import tracejb, logjb, tracejbdedent


class _error:
    pass
_error.ArgType = "always_comb argument should be a classic function"
_error.NrOfArgs = "always_comb argument should be a function without arguments"
_error.Scope = "always_comb argument should be a local function"
_error.SignalAsInout = "signal (%s) used as inout in always_comb function argument"
_error.EmbeddedFunction = "embedded functions in always_comb function argument not supported"
_error.EmptySensitivityList= "sensitivity list is empty"

def always_comb(func):
#     tracejb('always_comb')
    if not isinstance( func, FunctionType):
        raise AlwaysCombError(_error.ArgType)
    if _isGenFunc(func):
        raise AlwaysCombError(_error.ArgType)
    if func.__code__.co_argcount > 0:
        raise AlwaysCombError(_error.NrOfArgs)
    c = _AlwaysComb(func)
    return c


# class _AlwaysComb(_Instantiator):
class _AlwaysComb(_Always):

#     def __init__(self, func, symdict):
#         self.func = func
#         self.symdict = symdict
#         s = inspect.getsource(func)
#         # remove decorators
#         s = re.sub(r"@.*", "", s)
#         s = s.lstrip()
#         tree = compiler.parse(s)
#         v = _SigNameVisitor(symdict)
#         compiler.walk(tree, v)
#         self.inputs = v.inputs
#         self.outputs = v.outputs
#         senslist = []
#         for n in self.inputs:
#             s = self.symdict[n]
#             if isinstance(s, Signal):
#                 senslist.append(s)
#             else: # list of sigs
#                 senslist.extend(s)
#         self.senslist = tuple(senslist)
#         self.gen = self.genfunc()
#         if len(self.senslist) == 0:
#             raise AlwaysCombError(_error.EmptySensitivityList)
#         if len(self.senslist) == 1:
#             W = _SignalWaiter
#         else:
#             W = _SignalTupleWaiter
#         self.waiter = W(self.gen)

#     def __init__(self, func, symdict):      
    def __init__(self, func):      
        def senslistexpand( senslist, reg ):
            if isinstance(reg, StructType):
                refs = vars( reg )
                for k in refs:
                    if isinstance(refs[k], _Signal):
                        senslist.append( refs[k] )
                    elif isinstance(refs[k], (list, Array)):
                        senslistexpand(senslist, refs[k])
                    else:
                        pass
            else:
                if isinstance(reg[0], (list, Array)):
                    for r in reg:
                        senslistexpand( senslist, r )
                else:
                    # lowest (= last) level of m1D
                    if isinstance(reg[0], StructType):
                        print( reg )
                        for rr in reg:
                            senslistexpand( senslist, rr)
                    else:
                        # list or Array
                        senslist.extend(reg)

#         logjb( '_AlwaysComb' )                          
#         self.func = func
#         self.symdict = symdict
        senslist = []
        super(_AlwaysComb, self).__init__(func, senslist)

        s = inspect.getsource(func)
        s = _dedent(s)
        tree = ast.parse(s)
        # print ast.dump(tree)
        v = _AttrRefTransformer(self)
        v.visit(tree)
        v = _SigNameVisitor(self.symdict)
        v.visit(tree)
        self.inputs = v.results['input']
        self.outputs = v.results['output']

#         inouts = v.results['inout'] | self.inputs.intersection(self.outputs)
#         if inouts:
#             raise AlwaysCombError(_error.SignalAsInout % inouts)

        if v.results['embedded_func']:
            raise AlwaysCombError(_error.EmbeddedFunction)

#         logjb( self.inputs, 'self.inputs')
        for n in self.inputs:
#             logjb( n, 'n in self.inputs')
            s = self.symdict[n]
            if isinstance(s, _Signal):
                senslist.append(s)
            elif isinstance( s, (list, Array)):
                # list or Array of sigs
                senslistexpand( senslist, s)
            elif isinstance(s, StructType):
                logjb( s, 'is StructType')
                senslistexpand( senslist, s)
            elif _isListOfSigs(s):
                senslist.extend(s)
            else :
                pass
#         logjb( senslist, 'senslist')
        self.senslist = tuple(senslist)
        self.gen = self.genfunc()
        if len(self.senslist) == 0:
            raise AlwaysCombError(_error.EmptySensitivityList)

    def genfunc(self):
        senslist = self.senslist
        if len(senslist) == 1:
            senslist = senslist[0]
        func = self.func
        while 1:
            func()
            yield senslist





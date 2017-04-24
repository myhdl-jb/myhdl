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
from __future__ import absolute_import, print_function

import sys
import inspect
from types import FunctionType
import re
import ast

from myhdl import AlwaysCombError
from myhdl._Signal import _Signal, _isListOfSigs
from myhdl._intbv import intbv
from myhdl._util import _isGenFunc, _dedent
from myhdl._Waiter import _Waiter, _SignalWaiter, _SignalTupleWaiter
from myhdl._instance import _Instantiator
from myhdl._always import _Always
from myhdl._resolverefs import _AttrRefTransformer
from myhdl._visitors import _SigNameVisitor

from myhdl._structured import Array, StructType


class _error:
    pass
_error.ArgType = "always_comb argument should be a classic function"
_error.NrOfArgs = "always_comb argument should be a function without arguments"
_error.Scope = "always_comb argument should be a local function"
_error.SignalAsInout = "signal (%s) used as inout in always_comb function argument"
_error.EmbeddedFunction = "embedded functions in always_comb function argument not supported"
_error.EmptySensitivityList = "sensitivity list is empty"


def always_comb(func):
    if not isinstance(func, FunctionType):
        raise AlwaysCombError(_error.ArgType)
    if _isGenFunc(func):
        raise AlwaysCombError(_error.ArgType)
    if func.__code__.co_argcount > 0:
        raise AlwaysCombError(_error.NrOfArgs)
    c = _AlwaysComb(func)
    return c


# class _AlwaysComb(_Instantiator):
class _AlwaysComb(_Always):

    def __init__(self, func):

        def senslistexpand(senslist, reg):
            #             print(repr(reg))
            if isinstance(reg, _Signal):
                senslist.append(reg)
            elif isinstance(reg, StructType):
                #                 print('senslistexpand StructType', repr(reg))
                refs = vars(reg)
                for k in refs:
                    if isinstance(refs[k], _Signal):
                        senslist.append(refs[k])
                    elif isinstance(refs[k], (list, Array)):
                        senslistexpand(senslist, refs[k])
                    elif isinstance(refs[k], StructType):
                        senslistexpand(senslist, refs[k])
                    else:
                        #                         print('senslistexpand passing {}?'.format(k))
                        pass
            elif isinstance(reg, (list, Array)):
                if isinstance(reg[0], (list, Array)):
                    for r in reg:
                        senslistexpand(senslist, r)
                else:
                    if isinstance(reg[0], StructType):
                        for rr in reg:
                            senslistexpand(senslist, rr)
                    elif isinstance(reg[0], _Signal):
                        senslist.extend(reg)
#                     elif isinstance(reg, Array):
#                         senslist.extend(reg._array)
#                     elif isinstance(reg, list):
#                         senslist.extend(reg)

#         self.func = func
#         self.symdict = symdict
        senslist = []
        super(_AlwaysComb, self).__init__(func, senslist)
#         print('_AlwaysComb', senslist)
        s = inspect.getsource(func)
        s = _dedent(s)
        tree = ast.parse(s)
#         print(ast.dump(tree))
#         for item in ast.dump(tree).split():
#             print(item)
        v = _AttrRefTransformer(self)
        v.visit(tree)
#         print(ast.dump(tree))
#         for item in ast.dump(tree).split():
#             print(item)
        v = _SigNameVisitor(self.symdict)
        v.visit(tree)
#         print(ast.dump(tree))
#         for item in ast.dump(tree).split():
#             print(item)
        self.inputs = v.results['input']
        self.outputs = v.results['output']
#         print(v.results)
#         print('inputs:', self.inputs)
#         print('outputs:', self.outputs)
#         inouts = v.results['inout'] | self.inputs.intersection(self.outputs)
#         if inouts:
#             raise AlwaysCombError(_error.SignalAsInout % inouts)

        if v.results['embedded_func']:
            raise AlwaysCombError(_error.EmbeddedFunction)
#         print(self.inputs)
#         print('2', self.senslist)
        for n in self.inputs:
            s = self.symdict[n]
#             print(n,s)
#             print(n, s, isinstance(s, StructType), isinstance(s, (list, Array)))
            senslistexpand(senslist, s)
#             if isinstance(s, _Signal):
#                 senslist.append(s)
#             elif isinstance(s, list):
# #                 print(repr(s))
#                 # list or Array of sigs
#                 senslistexpand(senslist, s)
#             elif isinstance(s, Array):
#                 # Array of sigs
#                 if not isinstance(s.element, intbv):
#                     senslistexpand(senslist, s)
#             elif isinstance(s, StructType):
#                 senslistexpand(senslist, s)
#             elif _isListOfSigs(s):
#                 senslist.extend(s)
#             else :
# #                 print('_always_comb', n)
#                 pass
#         print('3', self.senslist)
        self.senslist = tuple(senslist)
#         print('4', self.senslist)
        self.gen = self.genfunc()
#         for item in self.senslist:
#             print(item._name, repr(item))
#         print()
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

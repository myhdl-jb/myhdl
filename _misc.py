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

""" MyHDL miscellaneous public objects.

This module provides the following public myhdl objects:
instances -- function that returns instances in a generator function
downrange -- function that returns a downward range

"""
from __future__ import absolute_import


# import sys
import inspect

from myhdl._Cosimulation import Cosimulation
from myhdl._instance import _Instantiator

# tracing the poor man's way
from myhdl.tracejbdef import TRACEJBDEFS
if TRACEJBDEFS['_miscmain']:
    from myhdl.tracejb import tracejb, logjb, tracejbdedent, logjbinspect
else:
    def tracejb( a, b = None):
        pass
    def logjb(a, b = None, c = False):
        pass
    def tracejbdedent():
        pass
    def logjbinspect(a, b= None, c = False):
        pass
    def tracenode( a = None, b = None):
        pass


def _isGenSeq(obj):
    if isinstance(obj, (Cosimulation, _Instantiator)):
        return True
#     if not isinstance(obj, (Array, list, tuple, set)):
    if not isinstance(obj, (list, tuple, set)):
        return False
    for e in obj:
        if not _isGenSeq(e):
            return False
    return True


def collectrtl( l, dst):
    for item in l:
        if _isGenSeq(item):
            dst.append(item)
        elif isinstance(item, (tuple, list)):
            dst.append( collectrtl(item, dst))
        else:
            if hasattr(item, 'rtl'):
                dst.append(item.rtl())
    return dst
 
def rtlinstances():
#     pass
    ''' search for the rtl in 'class' modules '''
    f = inspect.currentframe()
    d = inspect.getouterframes(f)[1][0].f_locals
    l = []
    for v in d.values():
        if _isGenSeq(v):
            l.append(v)
        elif isinstance(v, (tuple, list)):
            print(v)
            ll = []
            l.append( collectrtl(v, ll))
        else:
            print(repr(v))
            if hasattr(v, 'rtl'):
                l.append(v.rtl())
    return l


def instances():
    f = inspect.currentframe()
    d = inspect.getouterframes(f)[1][0].f_locals
    l = []
    for v in d.values():
        if _isGenSeq(v):
#             print(v)
            l.append(v)
    return l

def downrange(start, stop=0, step=1):
    """ Return a downward range. """
    return range(start-1, stop-1, -step)


def m1Dinfo( l ):
    ''' determine the properties of a (multi-dimensiomnal) list '''
    if len(l):
        element = l[0]
        totalelements = len(l)
        levels = 1
        sizes = [len(l)]
        while isinstance(element, list):
            sizes.append(len(element))
            totalelements *= len(element)
            element = element[0]
            levels += 1
        return levels, sizes, totalelements, element
    else:
        return None, None, None, None

# class rtlinstance(object):
#     def __init__(self, f):
#         self.f = f
# 
#     def __get__(self, obj, objtype):
#         """Support instance methods."""
#         import functools
#         return functools.partial(self.__call__, obj)
#      
#     def __call__(self, *args, **kwargs):
#         print( "Entering {}".format(self.f.__name__))
#         self.f(*args, **kwargs)
# def rtlinstance(f):
#     def new_f(*args):
#         print( "Entering {} of class {}".format(f.__name__, f.__class__.__name__))
#         return f(*args)
#     return new_f


# from myhdl._structured import Array

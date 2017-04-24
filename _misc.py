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
from __future__ import absolute_import, print_function


# import sys
import inspect

from myhdl._Cosimulation import Cosimulation
from myhdl._instance import _Instantiator


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


def collectrtl(dvalues, dst):
    print('collectrtl', dvalues)
    for item in dvalues:
        print(repr(item))
        if _isGenSeq(item):
            print('_isGenSeq', repr(item))
            dst.append(item)
#         elif isinstance(item, (tuple, list)):
# #             dst.append( collectrtl(item, dst))
#             print('tuple or list', item)
#             ll = []
#             dst.extend( collectrtl(item, ll))
#         else:
#             if hasattr(item, 'rtl'):
#                 print(repr(item))
#                 dst.append(item.rtl())
    return dst


def checkrtl(v):
    ''' replace 'class' by their 'rtl()' '''
    if isinstance(v, (tuple, list)):
        for item in v:
            checkrtl(item)
    elif hasattr(v, 'rtl'):
        v = v.rtl()
        checkrtl(v)


def rtlinstances():
    #     pass
    ''' search for the rtl in 'class' modules '''
    f = inspect.currentframe()
    d = inspect.getouterframes(f)[1][0].f_locals
    l = []
    dvalues = d.values()
    print('d.values()', dvalues)
    # replace 'class' by their 'rtl()'
    for v in dvalues:
        if not _isGenSeq(v):
            print('rtlinstances not _isGenSeq', v)
            for item in inspect.getmembers(v):
                if not item[0].startswith('__') and not item[0].endswith('__'):
                    print('\t', item)
            print()
#             checkrtl(v)
#             if hasattr(v, 'rtl'):
#                 v = v.rtl()
    # now get the generators
    for v in dvalues:
        if _isGenSeq(v):
            print('rtlinstances _isGenSeq', v)
            l.append(v)
    return l


def instances():
    f = inspect.currentframe()
    d = inspect.getouterframes(f)[1][0].f_locals
    l = []
    dvalues = d.values()
#     print('d.values()', dvalues)
    for v in dvalues:
        #         print(repr(v))
        if _isGenSeq(v):
            l.append(v)
#         elif isinstance(v, dict):
#             for key in v.keys():
#                 dv = v[key]
#                 print(key, repr(dv))
#                 for vdv in dv:
#                     if _isGenSeq(vdv):
#                         print(repr(vdv), vdv.__class__.__name__)
#                         l.append(vdv)

    return l


def downrange(start, stop=0, step=1):
    """ Return a downward range. """
    return range(start - 1, stop - 1, -step)


def m1Dinfo(l):
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
        return levels, tuple(sizes), totalelements, element
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

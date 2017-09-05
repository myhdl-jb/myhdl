'''
Created on 26 Aug 2015

@author: Josy
'''
#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2016 Jan Decaluwe
#  Enhanced 2015-2017 Josy Boelen
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

from __future__ import absolute_import
from __future__ import print_function

import copy

# from myhdl import concat
from myhdl import bin as myhdlbin
from myhdl._intbv import intbv
from myhdl._Signal import Signal, _Signal
from myhdl._simulator import _siglist
from myhdl._compat import integer_types
from myhdl._ShadowSignal import ConcatSignal, _ShadowSignal
from myhdl._misc import m1Dinfo
from myhdl._enum import EnumItemType

from myhdl.tracejb import Tracing

trace = Tracing(False, source='_structured')

# helper function


def setnext(obj, value):
    '''
        a local function to do the work, recursively
        handles both Array and StructType
    '''
    if isinstance(obj, (list, Array)):
        # recurse
        if isinstance(value, integer_types):
            for i, item in enumerate(obj):
                setnext(item, value)
        else:
            for i, item in enumerate(obj):
                setnext(item, value[i])
    elif isinstance(obj, StructType):
        if isinstance(value, StructType):
            # assume the objects are of the same type ...
            dests = vars(obj)
            srcs = vars(value)
            for key in dests:
                setnext(dests[key], srcs[key])
        else:
            # the values are a collection of integers...
            # use the sequencelist to enumerate the value
            idx = 0
            for key in obj.sequencelist:
                if hasattr(obj, key):
                    setnext(vars(obj)[key], value[idx])
                    idx += 1

    elif isinstance(obj, _Signal):
        if isinstance(value, _Signal):
            obj._setNextVal(value.val)
        else:
            obj._setNextVal(value)


class Array(object):
    '''
    array(shape , dtype )
        shape:  1.: a tuple of int's specifying the dimensions,
                    starting with the highest (in the order you will index them)
                2.: a  [(regular) multi-dimensional] list of either 'integer' or 'boolean' values
        dtype: intbv()  - intbv(0)[W:] or intbv(0, min = x, max = y) style
               bool()
               or either encapsulated in a Signal, e.g.: Signal( intbv(0, min = -8, max = 8))
    '''

    __slots__ = ('_array', '_next', '_init', '_val', '_name', '_dtype', '_nrbits',
                 '_driven', '_read', '_isshadow', '_used', '_initialised', '_isSignal',
                 'element', 'levels', 'shape', 'sizes', 'size', '_setNextVal', 'attributes',
                 )

    def __init__(self, shape, dtype, vector=None, attributes=None):
        '''
        build the object
            note that the default initialisation is supplied with dtype itself
        '''
        # first choice:
        #    -  use a flattened list, this makes some operations like summing all the elements together easier
        #         but this will show in the converted V* code (which is OK, just perhaps not that beautiful)
        #    -  build a true hierarchical list
        #        may be a bit more work, here and in the conversion (will produce nicer V* code?)
        #        we may still have to produce a flattened list (eventually?)
        # try hierarchical at first
        # encapsulating a 'traditional' list only beautifies the creation
        # but still falls back to a multidimensional list
        # so we have to build a recursive class

        self._name = None
        self._driven = False
        self._read = False
        self._used = False
        self.shape = None
        self._array = None
        self._initialised = False
        self._isSignal = False
        self.size = 0
        self._isshadow = False
        self.attributes = attributes
        if isinstance(shape, list) and isinstance(dtype, Array):
            # wrapping a slice of an Array (a slice is a 'naked' list)
            # can copy a few attributes
            self._dtype = dtype._dtype
            self._isSignal = dtype._isSignal
            self.element = dtype.element
            self._driven = dtype._driven
            self._isshadow = dtype._isshadow
            self._name = dtype._name  # ? wonder, wonder ?
            # dtype refers to the parent Array and thus hasn't got the sizes,
            # levels, ... information, so 'inspect' the shape
            self.levels, self.shape, self.size, _ = m1Dinfo(shape)
            self._array = shape  # this does not create new elements

        else:
            if isinstance(shape, Array) and isinstance(dtype, _Signal):
                # create an Array from SliceShadows
                # or replace the signals in the given Array with SliceShadow
                # break out to a function
                shape.toArray(dtype)

            elif isinstance(shape, (Array, list)):
                # an initialised list
                # element remembers what the caller gave us
                # get the info
                self.levels, self.shape, self.size, self.element = m1Dinfo(shape)
                if dtype is not None:
                    # element remembers what the caller gave us
                    self.element = dtype
                    self._isSignal = isinstance(dtype, _Signal)
                    if self._isSignal:
                        self._dtype = dtype._val
                    else:
                        self._dtype = dtype

                    self._initialised = True
                    if len(self.shape) == 1:
                        a = []
                        for i in range(self.shape[0]):
                            if self._isSignal:
                                if isinstance(self._dtype, intbv):
                                    a.append(Signal(intbv(shape[i], min=self._dtype._min, max=self._dtype._max)))
                                elif isinstance(self._dtype, bool):
                                    a.append(Signal(bool(shape[i])))
                                else:
                                    pass
                            else:
                                if isinstance(self._dtype, intbv):
                                    a.append(intbv(shape[i], min=self._dtype._min, max=self._dtype._max))
                                elif isinstance(self._dtype, bool):
                                    a.append(bool(shape[i]))
                                else:
                                    # a structured object?
                                    # as it already is in a list we can use
                                    # that 'element' no need to 'copy'
                                    a.append(shape[i])
                        self._array = a
                    else:
                        a = []
                        for i in range(self.shape[0]):
                            a.append(Array(shape[i], dtype))
                        self._array = a
                else:
                    # 'Array from LoS'
                    # assume we have received a list of Signals, possibly
                    # shadowslices of a vector
                    # or a list of other objects
                    if isinstance(self.element, _Signal):
                        self._dtype = self.element._val
                        self._isSignal = True
                    elif isinstance(self.element, StructType):
                        trace.print('Array from List Of StructTypes', shape)
                        self._dtype = self.element
                    self._array = shape  # this doesn't create new elements

            elif isinstance(shape, tuple):
                if isinstance(dtype, Array):
                    # instantiating an Array of Array
                    # we will handle this by extending the source Array
                    # make a new list of the sizes
                    nsizes = []
                    for dim in shape:
                        nsizes.append(dim)
                    for dim in dtype.shape:
                        nsizes.append(dim)
                    # we now have a new Array descriptor
                    narray = Array(tuple(nsizes), dtype.element)
                    # copy over
                    self.element = narray.element
                    self._dtype = narray._dtype
                    self._isSignal = narray._isSignal
                    self._array = narray._array
                    self.shape = narray.shape
                    self.levels = narray.levels
                    self.size = narray.size
                    self._driven = narray._driven

                else:
                    # element remembers what the caller gave us
                    self.element = dtype
                    self._isSignal = isinstance(dtype, _Signal)
                    if self._isSignal:
                        self._dtype = dtype._val
                    else:
                        self._dtype = dtype

                    if vector is None:
                        # all elements will be initialised to the value
                        # specified in 'dtype'
                        self.levels = len(shape)
                        self.shape = shape
                        if len(self.shape) == 1:
                            a = []
                            for _ in range(self.shape[0]):
                                if self._isSignal:
                                    if isinstance(self._dtype, intbv):
                                        a.append(
                                            Signal(intbv(dtype._val, min=self._dtype._min, max=self._dtype._max)))
                                    elif isinstance(self._dtype, bool):
                                        a.append(Signal(bool(dtype._val)))
                                    elif isinstance(self._dtype, EnumItemType):
                                        a.append(Signal(self._dtype))

                                else:
                                    if isinstance(self._dtype, intbv):
                                        a.append(
                                            intbv(dtype._val, min=self._dtype._min, max=self._dtype._max))
                                    elif isinstance(self._dtype, bool):
                                        a.append(bool(dtype))
                                    elif isinstance(self._dtype, StructType):
                                        # a StructType object
                                        a.append(dtype.copy())
                                    elif isinstance(self._dtype, list):
                                        pass
                                    else:
                                        # an interface
                                        obj = copy.deepcopy(self._dtype)
                                        # deepcopy drops the Signals ...
                                        # so mop it up
                                        srcvars = vars(self._dtype)
                                        for var in srcvars:
                                            if isinstance(srcvars[var], _Signal):
                                                obj.__setattr__(
                                                    var, Signal(srcvars[var]._val))
                                        a.append(obj)

                            self._array = a
                        elif isinstance(self.shape, tuple):
                            a = []
                            for _ in range(self.shape[0]):
                                a.append(Array(shape[1:], dtype))
                            self._array = a

                        self.size = 1
                        for dim in self.shape:
                            self.size *= dim
                    else:
                        # we have a (large) Signal(intbv()) to cut into pieces
                        # dtype can be:
                        #    integer: specifies the width, each element will be unsigned
                        #    tuple of (min, max)
                        #    intbv()
                        #    bool()
                        #    Signal(intbv())
                        # as we will only use this to derive the width and the signedness
                        if isinstance(dtype, (int, long)):
                            pass
                        elif isinstance(dtype, (list, tuple)):
                            pass
                        elif isinstance(dtype, intbv):
                            pass
                        elif isinstance(dtype, bool):
                            pass
                        elif isinstance(dtype, _Signal):
                            if isinstance(dtype._val, intbv):
                                pass
                            elif isinstance(dtype._val, bool):
                                pass
                            else:
                                pass
                        else:
                            raise ValueError(
                                "cannot infer width and signedness")

                        self.levels = len(shape)
                        self.shape = shape
                        if len(self.shape) == 1:
                            a = []
                            for _ in range(self.shape[0]):
                                pass
                        else:
                            # hand down
                            pass

            else:
                raise ValueError(
                    "Shape: {} of array is undefined".format(shape))

            self._nrbits = (self.size * self.element._nrbits) \
                if not isinstance(self.element, bool) else self.size

    def _update(self):
        def collectwaiters(obj, waiterlist):
            ''' a local recursive function to collect the 'waiters' '''
            if isinstance(obj[0], (list, Array)):
                for item in obj:
                    collectwaiters(item, waiterlist)
            else:
                for item in obj:
                    waiterlist.extend(item._update())

        # delegate to Signal
        # collect the waiters for all Signals in the current Array
        waiterlist = []
        collectwaiters(self, waiterlist)
        return waiterlist

    def initial(self, targetlanguage):
        ''' return the initialiser '''
        if targetlanguage == 'vhdl':
            if isinstance(self._dtype, intbv):
                pass
            elif isinstance(self._dtype, bool):
                pass
            elif isinstance(self._dtype, StructType):
                pass
            return '[array init: tbd]'
        else:
            return '[array init: tbd]'

#     # representation
#     def __str__(self):
#         if self._name:
#             return self._name
#         else:
#             return repr(self._array)

    def __repr__(self):
        rval = "{}Array{} of {}". format('Shadow ' if self._isshadow else '',
                                         self.shape, repr(self.element))
        if self._name:
            return self._name + ': ' + rval
        else:
            return rval

    def ref(self):
        ''' return a nice reference name for the object '''
        if isinstance(self.element, _Signal):
            obj = self.element._val
        else:
            obj = self.element

        if isinstance(obj, intbv):  # self.elObj._nrbits is not None:
            basetype = '{}{}'.format(
                's' if obj._min < 0 else 'u', self.element._nrbits)
        elif isinstance(obj, bool):
            basetype = 'b'
        elif isinstance(obj, StructType):
            basetype = obj.ref()
        else:
            raise AssertionError

        for _, dim in enumerate(reversed(self.shape)):
            basetype = 'a{}_{}'.format(dim, basetype)
        return basetype

    # length
    # same behaviour as for multi-dimensional lists
    def __len__(self):
        return len(self._array)

    @property
    def nbits(self):
#         return self.element._nrbits * self.size
        return self.element.nbits * self.size

    # get
    def __getitem__(self, *args, **kwargs):
        #         trace.print('__getitem__:', repr(self))
        #         trace.print(args, repr(self._array))
        item = self._array.__getitem__(*args, **kwargs)
#         trace.print('item:', repr(item))
        if isinstance(item, list):
            #             trace.print('{}: __getitem__ should never return a list?'.format(self._name))
            return Array(item, self)
        else:
            return item

    def __getslice__(self, *args, **kwargs):
        sliver = self._array.__getslice__(*args, **kwargs)
#         trace.print('sliver', sliver)
        if isinstance(sliver, list):
            return Array(sliver, self)
        else:
            #             trace.print('__getslice__ should always return a list?')
            return sliver

    # set ?
    def __setitem__(self, *args, **kwargs):
        raise TypeError("Array object doesn't support item assignment, have you forgotten a .next?")

    def __setslice__(self, *args, **kwargs):
        raise TypeError("Array object doesn't support slice assignment, have you forgotten a .next?")

    # concatenate
    # will be tricky as we have to account for multiple dimensions!
    def __add__(self, other):
        if isinstance(self, Array):
            #             trace.print( self.shape)
            if not isinstance(other, Array):
                if isinstance(other, (_Signal, StructType)):
                    # a Signal or a StructType
                    if self.element._nrbits == other._nrbits:
                        self._array.append(other)
                        self.shape[0] += 1
                        self._nrbits += self.element._nrbits
                    else:
                        raise ValueError('Number of bits dont\'t match {} {}' .format(
                            self.element._nrbits, other._nrbits))
            else:
                if self.element._nrbits == other.element._nrbits:
                    pass
                else:
                    raise ValueError('Number of bits dont\'t match {} {}' .format(
                        self.element._nrbits, other.element._nrbits))
        else:
            pass

        return self

    def __radd__(self, other):
        if isinstance(self, Array):
            if not isinstance(other, Array):
                if isinstance(other, (_Signal, StructType)):
                    # a Signal or a StructType
                    if self.element._nrbits == other._nrbits:
                        self._array.insert(0, other)
                        self.shape[0] += 1
                        self._nrbits += self.element._nrbits
                    else:
                        raise ValueError('Number of bits dont\'t match {} {}'
                                         .format(self.element._nrbits, other._nrbits))
                else:
                    # must be an int??
                    newsig = self.element.copy()
                    newsig._val._val = other
                    self._array.insert(0, newsig)
                    self.shape[0] += 1
                    self._nrbits += self.element._nrbits
            else:
                if self.element._nrbits == other.element._nrbits:
                    pass
                else:
                    raise ValueError('Number of bits dont\'t match {} {}'
                                     .format(self.element._nrbits, other.element._nrbits))
        else:
            pass

        return self

    # support for the 'val' attribute
    @property
    def val(self):
        ''' produce a multi-dimensional list of the value of the elements '''
        def getvals(obj, rval):
            ''' a recursive routine '''
            if isinstance(obj[0], (list, Array)):
                for item in obj:
                    rrval = []
                    getvals(item, rrval)
                    rval.append(rrval)
            else:
                if isinstance(self.element, _Signal):
                    for item in obj:
                        # this will work for both intbv and bool
                        # what about fixbv?
                        rval.append(int(item.val))
                elif isinstance(self.element, StructType):
                    for item in obj:
                        rval.append(item.val)

        rval = []
        getvals(self, rval)
        return rval

    # support for the 'next' attribute
    @property
    def next(self):
        # this is only a placeholder?
        pass

    @next.setter
    def next(self, val):
        #         trace.print(self, ' <- ', val)
        if isinstance(val, Array):
            self._setNextVal(val._array)
            _siglist.append(self)
        elif isinstance(val, list):
            self._setNextVal(val)
            _siglist.append(self)
        elif isinstance(val, tuple):
            # assume only one level of depth for now
            idxl = 0
            idxh = 0
            for subval in val:
                if isinstance(subval, Array):
                    #                     trace.print('Array', repr(subval))
                    idxh += len(subval)
                    dst = self[idxl:idxh]
                    setnext(dst, subval._array)
                    idxl = idxh
                    _siglist.append(dst)
                elif isinstance(subval, _Signal):
                    # Signal or SructType
                    setnext(self[idxh], subval)
                    idxh += 1
                    idxl = idxh
                elif isinstance(subval, integer_types):
                    # must infer size ...
                    raise ValueError('Array .next: don\'t handle integer in tuple')
                elif isinstance(subval, tuple):
                    raise ValueError('Array .next: don\'t handle tuple(s) in tuple')
                else:
                    raise ValueError('Array .next: Tuple: not handled: {}'.format(repr(subval)))
            _siglist.append(self)
        elif isinstance(val, integer_types):
            # setting all elements to the same value
            # mostly used to set everything to 0
            # it will auto-recurse ...?
            # this will simulate. but take extra work for the conversion
            # as we may need a nested (others => (others => ...))
            for ele in self._array:
                ele._setNextVal(val)

    def _setNextVal(self, val):
        setnext(self, val)

    # support for the 'driven' attribute
    @property
    def driven(self):
        def ldriven(obj):
            ''' a local function to do the work, recursively '''
            if isinstance(self.element, intbv):
                return False
            if isinstance(obj[0], (list, Array)):
                for item in obj:
                    if ldriven(item):
                        return True
            else:
                # lowest level
                for item in obj:
                    if item.driven:
                        return True
                return False

#         trace.print('Array.driven:', self._name, self._driven, ldriven(self))
        return self._driven or ldriven(self)

    @driven.setter
    def driven(self, val):
        if not val in ("reg", "wire", True):
            raise ValueError(
                'Expected value "reg", "wire", or True, got "%s"' % val)
        self._driven = val

    # support for the 'read' attribute
    @property
    def read(self):
        return self._read

    @read.setter
    def read(self, val):
        if not val in (True,):
            raise ValueError('Expected value True, got "%s"' % val)
        self._markRead()

    def _markRead(self):
        self._read = True

    # 'used' attribute
    def _markUsed(self):
        self._used = True

    # support for the 'isshadow' attribute
    @property
    def isshadow(self):
        #         def lisshadow(obj):
        #             ''' a local function to do the work, recursively '''
        #             if isinstance(obj[0], (list, Array)):
        #                 for item in obj:
        #                     if lisshadow(item):
        #                         return True
        #             else:
        #                 # lowest level
        #                 for item in obj:
        #                     if item._isshadow:
        #                         return True
        #                 return False
        #
        #         trace.print('Array.isshadow:', self._name, self._isshadow, lisshadow(self))
        #         return self._isshadow or lisshadow(self)
        return self._isshadow

    ### use call interface for shadow signals ###
    def __call__(self, start=None, end=None, stride=None, left=None, right=None, signed=False):
        ''' build a new Array
            making it from (possibly) sliced signals
        '''
        # need a local recursive function
        def makenext(obj, top):
            ''' a local function to do the work, recursively '''
            if isinstance(obj[0], (list, Array)):
                for item in obj:
                    lower = []
                    makenext(item, lower)
                    top.append(lower)
            else:
                # lowest level
                for sig in obj:
                    if isinstance(sig, _Signal):
                        # forward to _Signal (sig must be a Signal!)
                        top.append(sig(left, right, signed))
                    else:
                        # a StructType?
                        top.append(sig())

#         trace.print('Calling {} with {}, {}, {}, {}, {}, {}'.format(repr(self), start, end, stride, left, right, signed))
        if isinstance(self.element, _Signal):
            #             trace.print(repr(self))
            top = []
            if stride is not None:
                if start is not None:
                    if end is not None:
                        makenext(self[start:end:stride], top)
                    else:
                        makenext(self[start::stride], top)
                else:
                    if end is not None:
                        makenext(self[:end:stride], top)
                    else:
                        makenext(self[::stride], top)
            else:
                if start is not None:
                    if end is not None:
                        makenext(self[start:end], top)
                    else:
                        makenext(self[start:], top)
                else:
                    if end is not None:
                        makenext(self[:end], top)
                    else:
                        makenext(self, top)

            r = Array(top, None)
            r._isshadow = True
#             trace.print(repr(r))
            return r
        else:
            if start is None and left is None:
                top = []
                makenext(self, top)
                r = Array(top, None)
                r._isshadow = True
#                 trace.print(repr(r))
                return r
            else:
                raise ValueError('Can only slice Signals (for now) <> {}'.format(repr(self.element)))


    def reshape(self, shape):
        ''' returns a Shadow Array '''
        def product(shape):
            if len(shape) == 1:
                return shape[0]
            else:
                return shape[0] * product(shape[1:])
        todo = product(shape)
        assert self.size == todo, '{}.reshape({}) doesn\'t match the total number size'


    def transform(self, shape, width, BIGENDIAN=False):
        ''' returns a Shadow Array '''
        # the general solution is to first make a large intbv
        # and then 'slice' this according the required new shape
        # all other approaches are at best cumbersome?
        if isinstance(self._dtype, intbv):
            newarray = Array(shape, Signal(intbv(0)[width:]))
            intermediate = self.tointbv(BIGENDIAN)
            newarray.fromintbv(intermediate)
            return newarray
        else:
            raise ValueError('{}: Can only transform Array of intbv'.format(repr(self)))

    def fromintbv(self, vector, BIGENDIAN=False):
        ''' replace the elements of an Array by SliceSignals from an intbv '''
        # this the start
        trace.push(message='Array.fromintbv')
        trace.print('start:', repr(self))
        assert len(vector) == self.nbits, '{}.fromintbv() needs same number of bits for source {} and destination{}' \
                                            .format(repr(self), len(vector), self.nbits)
        self._fromintbv(vector, self.nbits if BIGENDIAN else 0, BIGENDIAN)
        trace.print('end:', repr(self))
        trace.pop()
        return self

    def _fromintbv(self, vector, idx=0, BIGENDIAN=False):
        ''' 
            replace the elements of an Array by SliceSignals
            this is the function doing the work
            and that is called by StructType too
        '''
        # a local function
        def _toA(a, _o, _be):
            ''' a local recursive function '''
            if _be:
                if len(a.shape) == 1:
                    if isinstance(a.element, _Signal):
                        for i in range(a.shape[0]):
                            a._array[i] = vector(_o, _o - len(a._dtype))
                            _o -= len(a._dtype)
                    elif isinstance(a.element, StructType):
                        for i in range(a.shape[0]):
                            a._array[i]._fromintbv(vector, _o, True)
                            trace.print(repr(a._array[i]))
                            _o -= a.element.nbits

                else:
                    for i in range(a.shape[0]):
                        _toA(a[i], _o, True)

            else:
                if len(a.shape) == 1:
                    if isinstance(a.element, _Signal):
                        for i in range(a.shape[0]):
                            a._array[i] = vector(_o + len(a._dtype), _o)
                            _o += len(a._dtype)
                    elif isinstance(a.element, StructType):
                        for i in range(a.shape[0]):
                            a._array[i]._fromintbv(vector, _o, False)
                            trace.print(repr(a._array[i]))
                            _o += a.element.nbits

                else:
                    for i in range(a.shape[0]):
                        _toA(a[i], _o, False)

        # we delegate the work to a recursive function
        trace.print(idx)
        _toA(self, idx, BIGENDIAN)
        self._isshadow = True

    def toVHDL(self):
        ''' 
            emit the VHDL code
            to assign the shadowsignals
        '''
        lines = []

        def _tovhdl(a, name):
            ''' a local recursive function '''
            if len(a.shape) == 1:
                if isinstance(a.element, _Signal):
                    for i in range(a.shape[0]):
                        lines.append(a._array[i].toVHDL())
                elif isinstance(a.element, StructType):
                    for i in range(a.shape[0]):
                        lines.extend(a._array[i].toVHDL())

            else:
                for i in range(a.shape[0]):
                    _tovhdl(a[i], '{}({})'.format(name, i))

        if not self._isshadow:
            raise ValueError('Cannot emit VHDL code for non-shadowed Array')

        #
#         trace.print('Emitting Array Shadow VHDL code for {}\n\t{}\n\t{}'.format(self._name, repr(self), self))
        _tovhdl(self, self._name)
        return lines

    def tointbv(self, BIGENDIAN=False):
        ''' concatenates all elements '''
        def collect(obj, _h):
            ''' a local recursive function '''
            if len(obj.shape) == 1:
                if isinstance(obj.element, _Signal):
                    for i in range(obj.shape[0]):
                        _h.append(obj[i])
                elif isinstance(obj.element, StructType):
                    for i in range(obj.shape[0]):
                        _h.extend(obj.tointbv())
                else:
                    pass
            else:
                for i in range(obj.shape[0]):
                    collect(obj[i], _h)

#         harvest = []
#         collect(self, harvest)
#         val = 0
#         for hh in reversed(harvest):
#             # hh must be a signal
#             val += (val << hh._nrbits) + hh._val
#         return Signal(intbv(val, _nrbits=self.element._nrbits * len(harvest))
        if self.size > 1:
            harvest = []
            collect(self, harvest)
            if not BIGENDIAN:
                return ConcatSignal(*reversed(harvest))
            else:
                return ConcatSignal(*harvest)
        else:
            return self

    def copy(self):
        ''' return a new instance '''
        return Array(self.shape, self.element)


class StructType(object):
    ''' a base class
        makes sure we can discriminate between our 'Struct' type and the 'interface' type
        provides the methods
    '''

    def __init__(self, *args):
        '''
            create the object, depending on the arguments
            decl, vector
            None, None : member/attributes will be added later
            tuple of tuples, None:  add the member/attributes as described in the list
            tuple of tuples, Signal(intbv()[w:]) : add the member/attributes,
                                              but using Slice- and Index-Shadow signals when appropriate
        '''
        self._nrbits = 0
        self.sequencelist = None
        self.reversedirections = []
        self._driven = False
        self._read = False
        self._name = None
        self._isshadow = False

        if args and len(args) > 2:
            self._nrbits = 0
            self.__class__.__name__ = args[0]
            self.sequencelist = args[1]
            for i, key in enumerate(args[1]):
                setattr(self, key, args[2 + i])
                self._nrbits += args[2 + i].nbits

    @property
    def nbits(self):
        if self._nrbits == 0:
            # work out
            if self.sequencelist:
                objlist = []
                for description in self.sequencelist:
                    # skip over 'not present' members
                    if hasattr(self, description):
                        objlist.append(getattr(self, description))
            else:
                objlist = [vars(self)[key] for key in vars(self).keys()]

            lnrbits = 0
            for item in objlist:
                if item is None:
                    continue
                if isinstance(item, _Signal):
                    lnrbits += len(item)
                elif isinstance(item, (Array, StructType)):
                    lnrbits += item.nbits

            self._nrbits = lnrbits
        # always defined
        return self._nrbits

    def tointbv(self):
        ''' returns a Signal of the concatenated bits '''
        self._tisigs = []

        def collect(obj):
            ''' using a local routine to do the work '''

            if obj.sequencelist:
                objlist = []
                for description in obj.sequencelist:
                    # skip over 'not present' members
                    if hasattr(obj, description):
                        objlist.append(getattr(obj, description))
            else:
                objlist = [vars(obj)[key] for key in vars(obj).keys()]

            for item in objlist:
                #                 trace.print(repr(item))
                # must nest structured types
                if isinstance(item, StructType):
                    #                     trace.print('calling StructType.tointbv()', item)
                    ati = item.tointbv()
#                     trace.print(repr(ati))
                    self._tisigs.append(ati)
#                     self._tisigs.extend(collect(item))
                elif isinstance(item, Array):
                    #                     trace.print('calling Array.tointbv()', item)
                    ati = item.tointbv()
#                     trace.print(repr(ati))
                    self._tisigs.append(ati)
#                     trace.print('called Array.tointbv()')

                elif isinstance(item, _Signal):
                    self._tisigs.append(item)
                elif isinstance(item, (int, long, str)):
                    pass
                else:
                    pass
#             trace.print('collecting', self._tisigs)

#         trace.print('StructType: tointbv', repr(self))
        collect(self)
#         trace.print('collected', self._tisigs)
        return ConcatSignal(*reversed(self._tisigs))

    def fromintbv(self, vector, BIGENDIAN=False):
        ''' split a (large) intbv into a StructType '''
        trace.push(message='StructType: fromintbv')
        trace.print('start: {} {}'.format(repr(self), repr(vector)))
        if self.sequencelist is None:
            raise ValueError('Need a sequencelist to correctly assign StructType members\n{}'.format(repr(self)))

        assert len(vector) == self._nrbits, '{}.fromintbv() needs same number of bits for source and destination'.format(repr(self))

        self._fromintbv(vector, self.nrbits - 1 if BIGENDIAN else 0, BIGENDIAN)

        trace.print('end:', repr(self))
        trace.pop()

    def _fromintbv(self, vector, idx=0, BIGENDIAN=False):
        ''' split a (large) intbv into a StructType '''
        if BIGENDIAN:
            for key in self.sequencelist:
                if hasattr(self, key):
                    obj = vars(self)[key]
                    if isinstance(obj, _Signal):
                        if isinstance(obj._val, intbv):
                            # take care of unsigned/signed
                            vars(self)[key] = vector(idx, idx - obj._nrbits)
                            idx -= obj._nrbits
                            trace.print(repr(vars(self)[key]))
                        else:
                            # a bool
                            vars(self)[key] = vector(idx)
                            idx += 1

                    elif isinstance(obj, Array):
                        #                     trace.print('StructType.fromintbv(): Array', key, repr(obj), obj.nbits)
                        obj._fromintbv(vector, idx, True)
                        idx -= obj.nbits

                    elif isinstance(obj, StructType):
                        #                     trace.print('StructType.fromintbv(): StructType', key, repr(obj), obj.nbits)
                        obj._fromintbv(vector, idx, True)
                        idx -= obj.nbits

                    elif isinstance(obj, integer_types):
                        pass

                    else:
                        pass
        else:
            for key in self.sequencelist:
                if hasattr(self, key):
                    obj = vars(self)[key]
                    if isinstance(obj, _Signal):
                        if isinstance(obj._val, intbv):
                            # take care of unsigned/signed
                            vars(self)[key] = vector(idx + obj._nrbits, idx)
                            idx += obj._nrbits
                            trace.print(repr(vars(self)[key]))
                        else:
                            # a bool
                            vars(self)[key] = vector(idx)
                            idx += 1

                    elif isinstance(obj, Array):
                        #                     trace.print('StructType.fromintbv(): Array', key, repr(obj), obj.nbits)
                        obj._fromintbv(vector, idx, False)
                        idx += obj.nbits

                    elif isinstance(obj, StructType):
                        #                     trace.print('StructType.fromintbv(): StructType', key, repr(obj), obj.nbits)
                        obj._fromintbv(vector, idx, False)
                        idx += obj.nbits

                    elif isinstance(obj, integer_types):
                        pass

                    else:
                        pass

        self._isshadow = True

    def toVHDL(self):
        ''' 
            emit the VHDL code
            to assign the shadowsignals
        '''
#         if not self._isshadow:
#             raise ValueError('Cannot emit VHDL code for non-shadowed StructType {}'.format(self._name))

        lines = []
        if self._isshadow:
            #         trace.print('Emitting StructType Shadow VHDL code for {}'.format(self._name))
            for key in self.sequencelist:
                if hasattr(self, key):
                    obj = vars(self)[key]
                    if isinstance(obj, _Signal):
                        lines.append(obj.toVHDL())
                    elif isinstance(obj, (Array, StructType)):
                        lines.extend(obj.toVHDL())

        return lines

    def __repr__(self):
#         if self._isshadow:
#             rval = 'Shadow of StructType {} {}'.format(self.__class__.__name__, vars(self))
#         else:
#             rval = 'StructType {} {}'.format(self.__class__.__name__, vars(self))
        rval = '{}StructType {} {}'.format('Shadow of ' if self._isshadow else '',
                                           self.__class__.__name__, vars(self))
        if self._name is None:
            return rval
        else:
            return self._name + ': ' + rval

    def copy(self):
        ''' return a new object '''
        # we build a new object
        nobj = StructType()
        # inherit the class name
        nobj.__class__ = self.__class__
        srcvars = vars(self)
        for var in srcvars:
            obj = srcvars[var]
            if isinstance(obj, _Signal):
                nobj.__setattr__(var, Signal(obj._val))
            elif isinstance(obj, (StructType, Array)):
                nobj.__setattr__(var, obj.copy())
            elif isinstance(obj, list):
                # List of anything
                # presumably Signal, Array, StructType
                # but anything goes?
                if len(obj) and isinstance(obj[0], (_Signal, Array, StructType)):
                    siglist = []
                    for sig in obj:
                        siglist.append(sig.copy())
                    nobj.__setattr__(var, siglist)
                else:
                    nobj.__setattr__(var, copy.deepcopy(obj))
            else:
                # fall back for others
                nobj.__setattr__(var, copy.deepcopy(obj))

        return nobj

    def ref(self):
        ''' returns a condensed name representing the contents of the StructType, starting with the __class__ name'''
        trace.print(repr(self))
        retval = 'r_{}'.format(self.__class__.__name__)
        # should be in order of the sequencelist, if any
        if self.sequencelist:
            for key in self.sequencelist:
                trace.print(repr(key))
                if hasattr(self, key):
                    obj = vars(self)[key]
                    if isinstance(obj, _Signal):
                        if isinstance(obj._val, intbv):
                            retval = ''.join(
                                (retval, '_{}{}'.format('s' if obj._min < 0 else 'u', obj._nrbits)))
                        else:
                            retval = ''.join((retval, '_b'))

                    elif isinstance(obj, Array):
                        retval = ''.join((retval, '_', obj.ref()))

                    elif isinstance(obj, StructType):
                        retval = ''.join((retval, '_', obj.ref(), '_j'))

                    elif isinstance(obj, integer_types):
                        pass

                    else:
                        retval = ''.join((retval, '_n'))
                else:
                    retval = ''.join((retval, '_n'))

        else:
            for key in vars(self).keys():
                obj = vars(self)[key]
                if isinstance(obj, _Signal):
                    if isinstance(obj._val, intbv):
                        retval += '_{}{}'.format('s' if obj._min <
                                                 0 else 'u', obj._nrbits)
                    else:
                        retval += '_b'

                elif isinstance(obj, Array):
                    retval += '_' + obj.ref()

                elif isinstance(obj, StructType):
                    retval += '_' + obj.ref() + '_j'

                elif isinstance(obj, integer_types):
                    pass

                else:
                    pass

        return retval

    def _setNextVal(self, val):
        refs = vars(self)
        if isinstance(val, StructType):
            vargs = vars(val)
            for key in refs:
                dst = refs[key]
                if isinstance(dst, _Signal):
                    src = vargs[key]
                    if key in self.reversedirections:
                        src._setNextVal(dst._val)
                    else:
                        if isinstance(src, _Signal):
                            dst._setNextVal(src._val)
                        else:
                            dst._setNextVal(src)
                elif isinstance(dst, (Array, StructType)):
                    dst._setNextVal(vargs[key])
        elif isinstance(val, tuple):
            if self.sequencelist is None:
                raise ValueError('Need a well defined order of assignments -> sequencelist')
            else:
                # handle the each entry in the sequencelist
                # first do a few checks
                assert len(self.sequencelist) == len(val), \
                    'Number of elements in aggregate  tuple don\'t match StructType'
                idx = 0
                for key in self.sequencelist:
                    # do not process the 'None' in the tuple
                    if val[idx] is not None:
                        obj = vars(self)[key]
                        obj._setNextVal(val[idx])
                    idx += 1

        elif isinstance(val, integer_types):
            pass

    ### use call interface for shadow signals ###
    def __call__(self):
        ''' build a new StructType
            but from ShadowSignals
        '''
        # copy the StructType
        top = self.copy()
        # replace the Signals, Arrays, StructTypes by ShadowSignals
        refs = vars(self)
        for key in refs:
            src = refs[key]
            if isinstance(src, (_Signal, Array, StructType)):
                top.__setattr__(key, src())
#             elif isinstance(src, list):
#                 # List of anything
#                 # presumably Signal, Array, StructType
#                 # but anything goes?
#                 siglist = []
#                 for sig in src:
#                     if isinstance(sig, (_Signal, Array, StructType)):
#                         siglist.append(sig())
#                 if siglist:
#                     top.__setattr__(key, siglist)
#
#             else:
#                 top.__setattr__(key, src)
        top._driven = True
        top._isshadow = True
        return top

    def _update(self):
        ''' collect the waiters for all object in the current StructType 
            eventually delegating to Signal
        '''
        waiters = []
        refs = vars(self)
        for key in refs:
            obj = refs[key]
            if isinstance(obj, (_Signal, StructType, Array)):
                waiters.extend(obj._update())
            elif isinstance(obj, list):
                for lobj in obj:
                    if isinstance(lobj, (_Signal, Array, StructType)):
                        waiters.extend(lobj._update())

        return waiters

    def initial(self, targetlanguage):
        ''' return the initialiser '''
        refs = vars(self)
        inits = []
        for key in refs:
            obj = refs[key]
            if targetlanguage == 'vhdl':
                if isinstance(obj, _Signal):
                    if isinstance(obj._val, bool):
                        inits.append("%s => '%s', " %
                                     (key, 1 if obj._val else 0))
                    elif isinstance(obj._val, intbv):
                        if obj._val:
                            inits.append("%s => \"%s\", " %
                                         (key, myhdlbin(obj._val, obj._nrbits)))
                        else:
                            inits.append("%s => (others => '0'), " % key)
                    elif isinstance(obj._val, EnumItemType):
                        inits.append("%s => %s, " % (key, obj._val))
                elif isinstance(obj, StructType):
                    # one down
                    inits.append(
                        '{} => ( {} ), '.format(key, obj.initial(targetlanguage)))
                elif isinstance(obj, Array):
                    inits.append(
                        '{} => {}, '.format(key, obj.initial(targetlanguage)))
            else:
                raise ValueError('Structures are not supported in Verilog, support for SystemVerilog is pending')

        rstr = ''.join(inits)
        return rstr[:-2]

    # support for the 'next' attribute
    @property
    def next(self):
        #         # must drill down into the list ?
        #         _siglist.append(self)
        #         return self._next
        # this is only a placeholder?
        pass

    @next.setter
    def next(self, val):
        self._setNextVal(val)
        _siglist.append(self)

    # support for the 'driven' attribute
    @property
    def driven(self):
        refs = vars(self)
        for key in refs:
            obj = refs[key]
            if isinstance(obj, _Signal):
                if obj.driven:
                    return True
            elif isinstance(obj, (Array, StructType)):
                if obj.driven:
                    return True
        return False
    #         return self._driven

    @driven.setter
    def driven(self, val):
        if not val in ("reg", "wire", True):
            raise ValueError(
                'Expected value "reg", "wire", or True, got "%s"' % val)
        self._driven = val

    # support for the 'isshadow' attribute
    @property
    def isshadow(self):
        refs = vars(self)
        for key in refs:
            obj = refs[key]
            if isinstance(obj, _ShadowSignal):
                return True
            elif isinstance(obj, (Array, StructType)):
                if obj.isshadow:
                    return True
        return False


if __name__ == '__main__':
    import random

    def main():
        print('====Exercising StructType ====')

        class Newclass(StructType):
            ''' a new class derived from Dynclass '''

            def __init__(self):
                # must init the superclass
                super(Newclass, self).__init__()
                # add members
                self.a = Signal(intbv(6)[4:])
                self.b = Signal(bool(False))
                self.c = Signal(bool(True))
                self.d = Signal(intbv(3, min=-4, max=15))

        nc = Newclass()

        print('nc: {}' .format(nc))

    #     for item in inspect.getmembers( nc):
    #         print( item )
    #     print( '================')
        print('nc.a: ', repr(nc.a))
        print('nc.b: ', repr(nc.b))
        print('nc.c: ', repr(nc.c))
        print('nc.d: ', repr(nc.d))
        print('nc: intbv: ', hex(nc.tointbv()))

        print('nc._nrbits: ', nc._nrbits)
        print('nc.ref(): {}'.format(nc.ref()))
        print('================')

        class Newclass2(StructType):
            ''' another new class derived from Dynclass '''

            def __init__(self):
                # must init the superclass
                super(Newclass2, self).__init__()
                # add members
                self.nc = Newclass()
                self.e = Signal(intbv(10)[4:])

        nc2 = Newclass2()

        print('nc2: {}' .format(nc2))
    #     for item in inspect.getmembers( nc2):
    #         print( item )
    #     print( '================')

        print('nc2: intbv: ', hex(nc2.tointbv()))
        print('nc2.nc.a: ', repr(nc2.nc.a))
        print('nc2.ref(): {}'.format(nc2.ref()))
        print('================')

        class Newclass3(StructType):
            ''' another new class derived from Dynclass '''

            def __init__(self):
                # must init the superclass
                super(Newclass3, self).__init__()
                self.nc2 = nc2
                self.f = Signal(intbv(10)[4:])
                self.r = Array((2, 2), Signal(intbv(0)[4:]))
                self.nca = Array((2, 2), nc)

        nc3 = Newclass3()

        print('nc3: {}' .format(nc3))
        print('nc3.nc2.nc.c: {}'.format(repr(nc3.nc2.nc.c)))
        print('nc3.r: {}'.format(repr(nc3.r)))
        print('nc3.nca: {}'.format(repr(nc3.nca)))
        print('cc3.ref(): {}'.format(nc3.ref()))
        print('================')
        nc4 = nc3.copy()
        print('nc4: {}' .format(nc4))
        print('================')

        print('====Exercising Aray ====')
        print('= intbv =====')
        a0 = Array((6, 5, 4, 3), intbv(0)[8:])
        print(a0)
        print(repr(a0))
        print('== Indexing=====')
        print(repr(a0[0]))
        print(repr(a0[1][0]))
        print(repr(a0[2][1][0]))
        print(repr(a0[3][2][1][0]))
        print(repr(a0[3][2][1][:2]))
        print('== Slicing ==')
        print(repr(a0[1:3]))
        print(repr(a0[1][1:3]))
        print('a0.ref(): {}'.format(a0.ref()))

        print('= intbv signed =====')
        a1 = Array((4, 3, 2), intbv(0, min=-128, max=128))
        print(a1)
        print(repr(a1))
        print('a1.ref(): {}'.format(a1.ref()))

        print('= initialised intbv =====')
        ll = [
            [[1 + i + j * 2 + k * 3 * 2 for i in range(2)] for j in range(3)] for k in range(4)]
        print(ll)
        b = Array(ll, intbv(0)[8:])
        print(b)
        print(repr(b))

        print('= bool =====')
        b = Array((3, 3), bool(0))
        print(repr(b))

        print('= initialised bool =====')
        bl = [[random.randint(0, 1) for _ in range(2)] for __ in range(4)]
        print(bl)
        b1 = Array(bl, bool(0))
        print(repr(b1))

    main()

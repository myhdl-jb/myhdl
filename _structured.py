'''
Created on 26 Aug 2015

@author: Josy
'''
#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2016 Jan Decaluwe
#  Enhanced 2015-2016 Josy Boelen
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

from myhdl import bin as myhdlbin
from myhdl._intbv import intbv
from myhdl._Signal import Signal, _Signal
from myhdl._simulator import _siglist
from myhdl._compat import integer_types
from myhdl._ShadowSignal import ConcatSignal
from myhdl._misc import m1Dinfo
from myhdl._enum import EnumItemType


class Array( object ):
    '''
    array(shape , dtype )
        shape:  1.: a tuple of int's specifying the dimensions,
                    starting with the highest (in the order you will index them)
                2.: a  [(regular) multi-dimensional] list of either 'integer' or 'boolean' values
        dtype: intbv()  - intbv(0)[W:] or intbv(0, min = x, max = y) style
               bool()
               or either encapsulated in a Signal, e.g.: Signal( intbv(0, min = -8, max = 8))
    '''

#     __slots__ = ('_array', '_next', '_init', '_val', '_name', '_dtype',
#                  '_driven', '_read',
#                  'element', 'levels', '_sizes', 'sizes' , 'totalelements', '_setNextVal'
#             )

    def __init__(self, shape, dtype, vector=None):
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
        self._sizes = None
        self._array = None
        self._initialised = False
        self._nrbits = 0
        if isinstance(shape, list) and isinstance(dtype, Array):
            # wrapping a slice of an Array (a slice is a 'naked' list)
            # can copy a few attributes
            self._dtype = dtype._dtype
            self._isSignal = dtype._isSignal
            self.element = dtype.element
            # dtype refers to the parent Array and thus hasn't got the sizes, levels, ... information, so 'inspect' the shape
            self.levels, self._sizes, self.totalelements, _ = m1Dinfo( shape )
            self._array = shape # this doesn't create new elements

        else:
            if isinstance(shape, Array) and isinstance(dtype, _Signal):
                # create an Array from SliceShadows 
                # or replace the signals in the given Array with SliceShadow
                # break out to a function
                shape.toArray( dtype )

            elif isinstance(shape, list):
                # an initialised list
                # element remembers what the caller gave us
                self.element = dtype
                self._isSignal = isinstance(dtype, _Signal)
                if self._isSignal:
                    self._dtype = dtype._val
                else:     
                    self._dtype = dtype

                self._initialised = True
                # get the info
                self.levels, self._sizes, self.totalelements, _ = m1Dinfo( shape )
                if dtype is not None:
                    if len(self._sizes) == 1:
                        a = []
                        for i in range(self._sizes[0]):
                            if self._isSignal:
                                if isinstance(self._dtype, intbv):
                                    a.append( Signal( intbv( shape[i], min = self._dtype._min, max = self._dtype._max )))
                                elif isinstance(self._dtype, bool):
                                    a.append( Signal( bool( shape[i] )))
                                else:
                                    pass
                            else:
                                if isinstance(self._dtype, intbv):
                                    a.append( intbv(shape[i], min = self._dtype._min, max = self._dtype._max ))
                                elif isinstance(self._dtype, bool):
                                    a.append( bool(shape[i]) )
                                else:
                                    # a structured object?
                                    a.append( shape[i] ) # as it already is in a list we can use that 'element' no need to 'copy'
                        self._array = a
                    elif isinstance(self._sizes, list):
                        a = []
                        for i in range( self._sizes[0]) :
                            a.append( Array( shape[i], dtype ))
                        self._array = a
                else:
                    # 'Array from LoS'
                    # assume we have received a list of valid Signals, possibly shadowslices of a vector
                    self.levels, self._sizes, self.totalelements, self.element = m1Dinfo( shape )
                    self._dtype = self.element._val
                    assert isinstance(self.element, _Signal)
                    self._isSignal = True 
                    self._array = shape # this doesn't create new elements
                    

            elif isinstance(shape, tuple):
                if isinstance(dtype, Array):
                    # instantiating an Array of Array
                    # we will handle this by extending the source Array
                    # make a new list of the sizes
                    nsizes = []
                    for size in shape:
                        nsizes.append(size)
                    for size in dtype._sizes:
                        nsizes.append(size)
                    # we now have a new Array descriptor
                    narray = Array( tuple(nsizes), dtype.element)
                    # copy over
                    self.element = narray.element
                    self._dtype = narray._dtype
                    self._isSignal = narray._isSignal
                    self._array = narray._array
                    self._sizes = narray._sizes
                    self.levels = narray.levels
                    self.totalelements = narray.totalelements

                else:
                    # element remembers what the caller gave us
                    self.element = dtype
                    self._isSignal = isinstance(dtype, _Signal)
                    if self._isSignal:
                        self._dtype = dtype._val
                    else:     
                        self._dtype = dtype

                    if vector is None:
                        # all elements will be initialised to the value specified in 'dtype'
                        self.levels = len(shape)
                        self._sizes = shape
                        if len(self._sizes) == 1:
                            a = []
                            for _ in range(self._sizes[0]):
                                if self._isSignal:
                                    if isinstance(self._dtype, intbv):
                                        a.append( Signal( intbv( dtype._val, min = self._dtype._min, max = self._dtype._max )))
                                    elif isinstance(self._dtype, bool):
                                        a.append( Signal( bool( dtype._val )))
                                    elif isinstance(self._dtype, EnumItemType):
                                        a.append( Signal( self._dtype ))

                                else:
                                    if isinstance(self._dtype, intbv):
                                        a.append( intbv( dtype._val, min = self._dtype._min, max = self._dtype._max ))
                                    elif isinstance(self._dtype, bool):
                                        a.append( bool( dtype) )
                                    elif isinstance(self._dtype, StructType):
                                        # a StructType object
                                        a.append( dtype.copy() ) 
                                    else:
                                        # an interface
                                        obj = copy.deepcopy( self._dtype )
                                        # deepcopy drops the Signals ...
                                        # so mop it up
                                        srcvars = vars(self._dtype)
                                        for var in srcvars:
                                            if isinstance(srcvars[var], _Signal):
                                                obj.__setattr__( var , Signal( srcvars[var]._val))
                                        a.append( obj )

                            self._array = a
                        elif isinstance(self._sizes, tuple):
                            a = []
                            for _ in range( self._sizes[0]) :
                                a.append( Array( shape[1:], dtype ))
                            self._array = a

                        self.totalelements = 1
                        for size in self._sizes:
                            self.totalelements *= size
                    else:
                        # we have a (large) Signal(intbv()) to cut into pieces
                        # dtype can be:
                        #    integer: specifies the width, each element will be unsigned
                        #    tuple of (min, max)
                        #    intbv()
                        #    bool()
                        #    Signal(intbv())
                        # as we will only use this to derive the width and the signedness
                        issigned = False
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
                            raise ValueError("cannot infer width and signedness")
    
                        self.levels = len(shape)
                        self._sizes = shape
                        if len(self._sizes) == 1:
                            a = []
                            for _ in range(self._sizes[0]):
                                pass
                        else:
                            # hand down
                            pass
    
            else:
                raise ValueError("Shape: {} of array is undefined".format( shape ))

            self._nrbits = (self.totalelements * self.element._nrbits) if not isinstance(self.element, bool) else self.totalelements



    def _update(self):
        def collectwaiters(obj , waiterlist ):
            ''' a local recursive function to collect the 'waiters' '''
            if isinstance(obj[0], (list, Array)):
                for item in obj:
                    collectwaiters(item, waiterlist)
            else:
                for item in obj:
                    waiterlist.extend( item._update() )

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

    # representation
    def __str__(self):
        if self._name:
            return self._name
        else:
            return repr(self._array)

    def __repr__(self):
        return "Array{} of {}". format(self._sizes, repr(self.element) )

    def ref(self):
        ''' return a nice reference name for the object '''
        if isinstance(self.element, _Signal):
            obj = self.element._val
        else:
            obj = self.element

        if isinstance(obj, intbv): #self.elObj._nrbits is not None:
            basetype = '{}{}'.format( 's' if obj._min < 0 else 'u', self.element._nrbits)
        elif isinstance( obj, bool):
            basetype = 'b'
        elif isinstance(obj, StructType):
            basetype = obj.ref()
        else:
            raise AssertionError

        for _, size in  enumerate( reversed( self._sizes )):
            basetype = '{}_{}'.format( size, basetype)
        return basetype

    # length
    def __len__(self):
        return self.totalelements

    # get
    def __getitem__(self, *args, **kwargs):
        item =  self._array.__getitem__(*args, **kwargs)
        if isinstance( item, list):
            print( '__getitem__ should never return a list?')

        return item

    def __getslice__(self, *args, **kwargs):
        sliver = self._array.__getslice__( *args , **kwargs)
        if isinstance( sliver, list):
            return Array(sliver, self)
        else:
            print( '__getslice__ should always return a list?')
            return sliver

    # set ?
    def __setitem__(self, *args, **kwargs):
        raise TypeError("Array object doesn't support item/slice assignment")

    def __setslice__(self, *args, **kwargs):
        raise TypeError("Array object doesn't support item/slice assignment")

    # concatenate
    # will be tricky as we have to account for multiple dimensions!
    def __add__(self, other):
#         print( 'StructType: __add__\n{} \n{}'.format( repr(self), repr(other)))
        if isinstance(self, Array):
#             print( self._sizes)
            if not isinstance(other, Array):
                if isinstance(other, (_Signal, StructType)):
                    # a Signal or a StructType
                    if self.element._nrbits == other._nrbits:
                        self._array.append(other)
                        self._sizes[0] += 1
                        self._nrbits += self.element._nrbits
#                         print( self._array )
                    else:
                        raise  ValueError( 'Number of bits dont\'t match {} {}' .format( self.element._nrbits, other._nrbits) )
            else:
                if self.element._nrbits == other.element._nrbits:
                    pass
                else:
                    raise  ValueError( 'Number of bits dont\'t match {} {}' .format( self.element._nrbits, other.element._nrbits) )
        else:
            pass

        return self

    def __radd__(self, other):
#         print( 'StructType: __radd__\n{} \n{}'.format( repr(self), repr(other)))
        if isinstance(self, Array):
#             print( self._sizes)
            if not isinstance(other, Array):
                if isinstance(other, (_Signal, StructType)):
                    # a Signal or a StructType
                    if self.element._nrbits == other._nrbits:
                        self._array.insert(0, other)
                        self._sizes[0] += 1
                        self._nrbits += self.element._nrbits
#                         print( self._array )
                    else:
                        raise  ValueError( 'Number of bits dont\'t match {} {}' \
                                           .format( self.element._nrbits, other._nrbits) )
                else:
                    # must be an int??
                    newsig = self.element.copy()
                    newsig._val._val = other
                    self._array.insert(0, newsig)
                    self._sizes[0] += 1
                    self._nrbits += self.element._nrbits
#                     print( self._array )
            else:
                if self.element._nrbits == other.element._nrbits:
                    pass
                else:
                    raise  ValueError( 'Number of bits dont\'t match {} {}' \
                                       .format( self.element._nrbits, other.element._nrbits) )
        else:
            pass

        return self
    

    # support for the 'val' attribute
    @property
    def val(self):
        return self._array

    # support for the 'next' attribute
    @property
    def next(self):
        # this is only a placeholder?
        pass

    @next.setter
    def next(self, val):
        if isinstance(val, Array ):
            val = val._array
            self._setNextVal(val)
            _siglist.append(self)
        elif isinstance(val, list):
            self._setNextVal(val)
            _siglist.append(self)

    def _setNextVal(self, val):

        def setnext( obj, value):
            ''' a local function to do the work, recursively '''        
            if isinstance(obj[0], (list, Array)):
                for i, item in enumerate( obj ):
                    setnext( item, value[i] )
            else:
                if isinstance(value[0], _Signal):
                    for i, s  in enumerate( obj ):
                        s._setNextVal( value[i].val )
                else:
                    for i, s  in enumerate( obj ):
                        s._setNextVal( value[i] )  

        setnext( self, val )
 
    # support for the 'driven' attribute
    @property
    def driven(self):
        return self._driven

    @driven.setter
    def driven(self, val):
        if not val  in ("reg", "wire", True):
            raise ValueError('Expected value "reg", "wire", or True, got "%s"' % val)
        self._driven = val

    # support for the 'read' attribute
    @property
    def read(self):
        return self._read

    @read.setter
    def read(self, val):
        if not val in (True, ):
            raise ValueError('Expected value True, got "%s"' % val)
        self._markRead()

    def _markRead(self):
        self._read = True

    # 'used' attribute
    def _markUsed(self):
        self._used = True

    def toArray(self, vector):
        ''' replace the elements of an Array by SliceSignals '''
        # a local function
        def _toA( a, v):
            ''' a local recursive function '''
            if len(a._sizes) == 1:
                for i in range(a._sizes[0]):
                    a._array[i] = v(len(a._dtype),0)
            else:
                for i in range(a._sizes[0]):
                    _toA( a[i], v)

        _toA(self, vector)

    def tointbv(self):
        ''' concatenates all elements '''
        def collect( obj , harvest ):
            ''' a local recursive function '''
            if len(obj._sizes) == 1:
                if isinstance(obj.element, _Signal):
                    for i in range(obj._sizes[0]):
                        harvest.extend(obj[i])
                elif isinstance(obj.element, StructType):
                    for i in range(obj._sizes[0]):
                        collect(obj, harvest)
            else:
                for i in range(obj._sizes[0]):
                    collect( obj[i], harvest)

        harvest = []
        return ConcatSignal(  *reversed( collect( self , harvest ) ) )        


    def copy(self):
        ''' return a new instance '''
        return Array( self._sizes , self.element)



class StructType( object ):
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
        self._driven = False
        self._read = False
        self._name = None
        
        if args and len(args) > 2:
#             print( 'combining objects into a StructType' )
            self.__class__.__name__ = args[0]
            self.sequencelist = args[1]
            for i, key in enumerate( args[1] ):
#                 print( key )
                setattr(self, key, args[2+i])
                self._nrbits += args[2+i]._nrbits 
                  
#             print(repr( self ))
            
    def __len__(self):
        return self._nrbits

    # accessible

    def tointbv(self):
        ''' returns a Signal of the concatenated bits '''
        def collect( obj ):
            ''' using a local routine to do the work '''
            sigs = []

            if obj.sequencelist:
                objlist = []
                for description in obj.sequencelist:
                    # skip over 'not present' members
                    if hasattr(obj, description):
                        objlist.append(getattr(obj, description) )
            else:
                objlist = [ vars(obj)[key] for key in vars(obj).keys()  ]

            for item in objlist:
                # must nest structured types
                if isinstance( item, StructType ):
                    sigs.extend( collect( item ))
                elif isinstance(item, Array):
                    sigs.extend( item.tointbv() )
                elif isinstance(item, _Signal):
                    sigs.append( item  )
                elif isinstance(item, (int, long)):
                    pass
                else:
                    pass

            return sigs

        siglist = collect( self )
        return ConcatSignal(  *reversed( siglist  ) )

    def toStructType(self, vector):
        ''' split a (large) intbv into a StructType '''
        if self.sequencelist is None:
            raise ValueError( 'Need a sequencelist to correctly assign StructType members')

        idx = 0
        for key in self.sequencelist:
            if hasattr(self, key):
                obj = vars(self)[key]
                if isinstance(obj , _Signal):
                    if isinstance(obj._val, intbv):
                        # take care of unsigned/signed
                        vars(self)[key] = vector(idx + obj._nrbits, idx)
                        idx += obj._nrbits
                    else:
                        # a bool
                        vars(self)[key] = vector(idx)
                        idx += 1

                elif isinstance(obj, Array):
                    obj.toArray(vector( idx + obj._nrbits, idx))
                    idx +=  obj._nrbits

                elif isinstance(obj, StructType):
                    obj.toStructType(vector( idx + obj._nrbits, idx))
                    idx +=  obj._nrbits

                elif isinstance(obj, integer_types):
                    pass

                else:
                    pass
    
    def __repr__(self):
        return 'StructType {} {}'.format( self.__class__.__name__, vars( self ))


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
                nobj.__setattr__( var , Signal( obj._val))
            elif isinstance(obj, (StructType, Array)):
                nobj.__setattr__( var, obj.copy() )
            else:
                nobj.__setattr__( var , copy.deepcopy(obj))

        return nobj


    def ref(self):
        ''' returns a condensed name representing the contents of the struct, starting with the __class__ name'''
        retval = 'r_{}'.format(self.__class__.__name__)
        # should be in order of the sequencelist, if any
        if self.sequencelist:
            for key in self.sequencelist:
                if hasattr(self, key):
                    obj = vars(self)[key]
                    if isinstance(obj , _Signal):
                        if isinstance(obj._val, intbv):
                            retval = ''.join((retval, '_{}{}'.format( 's' if obj._min < 0 else 'u', obj._nrbits )))
                        else:
                            retval = ''.join((retval, '_b'))

                    elif isinstance(obj, Array):
                        retval = ''.join((retval, '_', obj.ref()))

                    elif isinstance(obj, StructType):
                        retval = ''.join((retval, '_',  obj.ref(), '_j'))

                    elif isinstance(obj, integer_types):
                        pass

                    else:
                        retval = ''.join((retval, '_n'))
                else:
                    retval = ''.join((retval, '_n'))

        else:
            for key in  vars( self ).keys():
                obj = vars( self )[key]
                if isinstance(obj , _Signal):
                        if isinstance(obj._val, intbv):
                            retval+= '_{}{}'.format( 's' if obj._min < 0 else 'u', obj._nrbits )
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
        refs = vars( self )
        vargs = vars( val )
        for key in refs:
            dst = refs[key]
            if isinstance( dst, _Signal):
                src = vargs[key]
                if isinstance(src, _Signal):
                    dst._setNextVal( src._val)
                else:
                    dst._setNextVal(src) 


    def _update(self):
        ''' collect the waiters for all object in the current StructType 
            eventually delegating to Signal
        '''
        waiters = []
        refs = vars(self)
        for key in refs:
            obj = refs[key]
            if isinstance( obj, (_Signal, StructType, Array)):
                waiters.extend( obj._update() )
        return waiters


    def initial(self, targetlanguage):
        ''' return the initialiser '''
        refs = vars( self )
        inits = []
        for key in refs:
            obj = refs[key]
            if targetlanguage == 'vhdl':
                if isinstance( obj, _Signal):
                    if isinstance(obj._val, bool):
                        inits.append("%s => '%s', " % (key,  1 if obj._val else 0))
                    elif isinstance(obj._val, intbv):
                        inits.append("%s => \"%s\", " % (key, myhdlbin(obj._val, obj._nrbits)))
                    elif isinstance(obj._val, EnumItemType):
                        inits.append("%s => %s, " % (key, obj._val))
                elif isinstance(obj, StructType):
                    # one down 
                    inits.append( '{} => ( {} ), '.format(key, obj.initial()))
                elif isinstance(obj, Array):
                    inits.append('{} => {}, '.format(key, obj.initial(targetlanguage)))
            else:
                pass
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
        return self._driven

    @driven.setter
    def driven(self, val):
        if not val  in ("reg", "wire", True):
            raise ValueError('Expected value "reg", "wire", or True, got "%s"' % val)
        self._driven = val



if __name__ == '__main__':
    import random

    print( '====Exercising StructType ====')
    class Newclass( StructType ):
        ''' a new class derived from Dynclass '''
        def __init__(self):
            # must init the superclass
            super(Newclass, self).__init__()
            # add members
            self.a = Signal(intbv(6)[4:])
            self.b = Signal(bool( False))
            self.c = Signal(bool( True))
            self.d = Signal(intbv(3, min=-4, max=15))

    nc = Newclass()

    print( 'nc: {}' .format( nc ))

#     for item in inspect.getmembers( nc):
#         print( item )
#     print( '================')
    print( 'nc.a: ', repr(nc.a) )
    print( 'nc.b: ', repr(nc.b) )
    print( 'nc.c: ', repr(nc.c) )
    print( 'nc.d: ', repr(nc.d) )
    print( 'nc: intbv: ', hex(nc.tointbv()))

    print( 'nc._nrbits: ', nc._nrbits )
    print( 'nc.ref(): {}'.format( nc.ref()) )
    print( '================')
    class Newclass2( StructType ):
        ''' another new class derived from Dynclass '''
        def __init__(self):
            # must init the superclass
            super(Newclass2, self).__init__()
            # add members
            self.nc = Newclass()
            self.e =  Signal(intbv(10)[4:])

    nc2 = Newclass2()

    print( 'nc2: {}' .format( nc2 ))
#     for item in inspect.getmembers( nc2):
#         print( item )
#     print( '================')

    print( 'nc2: intbv: ', hex(nc2.tointbv()))
    print( 'nc2.nc.a: ', repr(nc2.nc.a))
    print( 'nc2.ref(): {}'.format( nc2.ref()) )
    print( '================')

    class Newclass3( StructType ):
        ''' another new class derived from Dynclass '''
        def __init__(self):
            # must init the superclass
            super(Newclass3, self).__init__()
            self.nc2 =  nc2
            self.f =  Signal(intbv(10)[4:])
            self.r = Array((2,2), Signal( intbv(0)[4:]))
            self.nca = Array((2,2), nc)

    nc3 = Newclass3()

    print( 'nc3: {}' .format( nc3 ))
    print( 'nc3.nc2.nc.c: {}'.format( repr( nc3.nc2.nc.c)))
    print( 'nc3.r: {}'.format( repr( nc3.r)))
    print( 'nc3.nca: {}'.format( repr( nc3.nca)))
    print( 'cc3.ref(): {}'.format( nc3.ref()) )
    print( '================')
    nc4 = nc3.copy()
    print( 'nc4: {}' .format( nc4 ))
    print( '================')    


    print( '====Exercising Aray ====')
    print( '= intbv =====')
    a0 = Array( (6,5,4,3), intbv(0)[8:])
    print( a0 )
    print( repr(a0) )
    print( '== Indexing=====')
    print( repr(a0[0]))
    print( repr(a0[1][0]))
    print( repr(a0[2][1][0]))
    print( repr(a0[3][2][1][0]))
    print( repr(a0[3][2][1][:2]))
    print( '== Slicing ==')
    print( repr(a0[1:3]))
    print( repr(a0[1][1:3]))
    print( 'a0.ref(): {}'.format( a0.ref()) )

    print( '= intbv signed =====')
    a1 = Array( (4,3,2), intbv(0, min = -128, max =128))
    print( a1 )
    print( repr( a1 ))
    print( 'a1.ref(): {}'.format( a1.ref()) )

    print( '= initialised intbv =====')
    ll = [[[  1 + i + j * 2 + k * 3 * 2 for i in range(2)] for j in range(3)] for k in range(4)]
    print( ll )
    b = Array( ll, intbv(0)[8:])
    print( b )
    print( repr(b) )
    
    print( '= bool =====')
    b = Array( (3,3), bool(0))
    print( repr(b) )
    
    print( '= initialised bool =====')
    bl = [[ random.randint(0,1) for _ in range(2)] for __ in range(4)]
    print( bl )
    b1 = Array( bl, bool(0) )
    print( repr( b1 ) )
    

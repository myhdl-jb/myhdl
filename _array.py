'''
Created on 31 Jul 2015

@author: Josy
'''
#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2015 Jan Decaluwe
#  Copyright (C) 2015 Josy Boelen
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

# import copy

from myhdl._intbv import intbv
from myhdl._Signal import Signal, _Signal
from myhdl._simulator import _siglist

from myhdl._structured import StructType
from myhdl._misc import m1Dinfo


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
        if isinstance(dtype, Array):
            # wrapping a slice of an Array (a slice is a 'naked' list)
            # can copy a few attributes
            self._dtype = dtype._dtype
            self._isSignal = dtype._isSignal
            self.element = dtype.element
            # dtype refers to the parent Array and thus hasn't got the sizes, levels, ... information, so 'inspect' the shape
            self.levels, self._sizes, self.totalelements, _ = m1Dinfo( shape )
            self._array = shape # this doesn't create new elements

        else:
            # element remembers what the caller gave us
            self.element = dtype
            self._isSignal = isinstance(dtype, _Signal)
            if self._isSignal:
                self._dtype = dtype._val
            else:     
                self._dtype = dtype

            if isinstance(shape, list):
                # an initialised list
                # get the info
                self.levels, self._sizes, self.totalelements, _ = m1Dinfo( shape )
                if len(self._sizes) == 1:
                    a = []
                    for i in range(self._sizes[0]):
                        if self._isSignal:
                            if isinstance(self._dtype, intbv):
#                                 a.append( Signal( intbv( shape[i])[self._nrbits:] ))
                                a.append( Signal( intbv( shape[i], min = self._dtype._min, max = self._dtype._max )))
                            elif isinstance(self._dtype, bool):
                                a.append( Signal( bool( shape[i] )))
                            else:
                                pass
                        else:
                            if isinstance(self._dtype, intbv):
#                                 a.append( intbv(shape[i])[self._nrbits:]  )
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
            elif isinstance(shape, tuple):
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
                                else:
                                    pass

                            else:
                                if isinstance(self._dtype, intbv):
                                    a.append( intbv( dtype._val, min = self._dtype._min, max = self._dtype._max ))
                                elif isinstance(self._dtype, bool):
                                    a.append( bool( dtype._val) )
                                else:
                                    # a StructType object?
                                    a.append( dtype.copy() ) 

                        self._array = a
                    elif isinstance(self._sizes, tuple):
                        a = []
                        for _ in range( self._sizes[0]) :
                            a.append( Array( shape[1:], dtype ))
                        self._array = a

                    self.totalelements = 1
                    for l in self._sizes:
                        self.totalelements *= l
                else:
                    # we have a (large) Signal(intbv()) to cut into pieces
                    # dtype can be:
                    #    integer: specifies the width, each element will beunsigned
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





    def _update(self):
        def collectwaiters(a , w ):
            if isinstance(a[0], (list, Array)):
                for item in a:
                    collectwaiters(item, w)
            else:
                for s in a:
                    w.extend( s._update() )

        # delegate to Signal
        # collect the waiters for all Signals in the current Array
        w = []
        collectwaiters(self, w)
        return w



    # representation
    def __str__(self):
        if self._name:
            return self._name
        else:
            return repr(self._array)

    def __repr__(self):
        return "Array{}({})". format(self._sizes, repr(self._array) )

    def ref(self):
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
            o = basetype
            basetype = 'a{}_{}'.format( size, o)
        return basetype
    
    
    # length
    def __len__(self):
        return len(self._array)

    # get
    def __getitem__(self, *args, **kwargs):
        r =  self._array.__getitem__(*args, **kwargs)
        if isinstance( r, list):
            print( '__getitem__ should never return a list?')
            return r
        else:
            return r

    def __getslice__(self, *args, **kwargs):
        r =  self._array.__getslice__( *args , **kwargs)
        if isinstance( r, list):
            a =  Array(r, self)
            return a
        else:
            print( '__getslice__ should always return a list?')
            return r

    # set ?
    def __setitem__(self, *args, **kwargs):
        raise TypeError("Array object doesn't support item/slice assignment")

    def __setslice__(self, *args, **kwargs):
        raise TypeError("Array object doesn't support item/slice assignment")


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

        def setnext( a, v):        
            if isinstance(a[0], (list, Array)):
                for i, ia in enumerate( a ):
                    setnext( ia, v[i] )
            else:
                if isinstance(v[0], _Signal):
                    for i, s  in enumerate( a ):
                        s._setNextVal( v[i].val )
                else:
                    for i, s  in enumerate( a ):
                        s._setNextVal( v[i] )  

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


    def copy(self):
        ''' return a new instance '''
        return Array( self._sizes , self.element)


if __name__ == '__main__':
    import random
 
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
    
    print( '= intbv signed =====')
    a1 = Array( (4,3,2), intbv(0, min = -128, max =128))
    print( a1 )
    print( repr( a1 ))
    
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
    
    
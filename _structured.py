'''
Created on 26 Aug 2015

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

import collections
import copy
import math

from myhdl._intbv import intbv
from myhdl._Signal import Signal, _Signal
# from myhdl._simulator import _signals, _siglist, _futureEvents, now
from myhdl._simulator import _siglist
from myhdl._compat import integer_types
from myhdl._ShadowSignal import ConcatSignal
from myhdl._misc import m1Dinfo


def widthr( v ):
    if v < 0:
        #using signed numbers requires double
        tv = -v * 2
    else :
        # unsigned
        tv = v

    if tv < 2:
        raise ValueError("Need at least 2")

    exp = math.ceil( math.log(tv,2) )
    if math.pow(2, exp) == tv :
        exp += 1

    return int(exp)



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
                                    a.append( bool( dtype) )
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



class StructType( object ):
    ''' a base class 
        makes sure we can discriminate between our 'Struct' type and the 'interface' type
        provides the methods
    '''
    
    def __init__(self, decl = None, vector = None):
        '''
            create the object, depending on the arguments
            decl, vector
            None, None : member/attributes will be added later
            tuple of tuples, None:  add the member/attributes as described in the list
            tuple of tuples, Signal(intbv()[w:]) : add the member/attributes,
                                              but using Slice- and Index-Shadow signals when appropriate
        '''
        # need to preserve the order
        self.__dict__ = collections.OrderedDict()
        self._nrbits = 0
        if vector is None:
            if decl:
                for member in decl:
                    self.addmember( member[0], member[1] )
        else:
            # we have a 'large' 'unsigned' Signal that is used to connect e.g. Qsys (or IP-Integrator) modules
            # we will create ShadowSignals
            # must have declarations
            if decl is None:
                raise ValueError("Need declaration-list to convert/map vector into structure")
            idx = 0
            for member in decl:
                name = member[0]
                dtype = member[1]
                if isinstance(dtype, _Signal):
                    # take a shadow
                    if isinstance(dtype._val, myhdl.intbv):
                        # SliceShadowSignal
                        nrbits = dtype._nrbits
                        issigned = dtype._min < 0
                        self.__dict__[name] = vector(idx + nrbits, idx, issigned)
                    elif isinstance(dtype._val, bool):
                        # IndexedShadowSignal
                        nrbits = 1
                        self.__dict__[name] = vector(idx)
                    else:
                        raise ValueError("Unhandled Signal type")
                    idx += nrbits

                elif isinstance(dtype, StructType):
                    # this may get tricky
                    pass
                elif isinstance(dtype, myhdl.Array):
                    # this may be tricky too
                    pass
                else:
                    # any other (int, long, intbv, string )
                    self.addmember( name, dtype )

            # remember the tally
            self._nrbits = idx

    # accessible
    def addmember(self, name, obj):
        ''' method to add attributes '''
        value = None
        if isinstance(obj, _Signal):
            self.__dict__[name] = obj
            self._nrbits += obj._nrbits

        elif isinstance(obj, myhdl.Array):
            self.__dict__[name] = obj.copy()
            self._nrbits += obj.totalelements * obj.element._nrbits

        elif isinstance(obj, StructType):
            # we build a new object
            srcvars = vars(obj )
            value = StructType()
            for var in srcvars:
                obj = srcvars[var]
#                 print( var, repr(obj))
                value.addmember(var, obj)
#             print( value )
            # add the bitsize of the newly created attribute
            self._nrbits += obj._nrbits
            self.__dict__[name] = value

        elif isinstance(obj, myhdl.intbv):
            pass

        elif isinstance(obj, bool):
            pass

        elif isinstance(obj, (int,long)):
            pass

        else:
            raise ValueError('Can\'t handle {}:{}' .format( name, obj ))


    def tointbv(self):
        ''' returns a Signal of the concatenated bits '''
        def collect( dc ):
            ''' using a local routine to do the work '''
            sigs = []
            for item in vars( dc ):
                # must nest structured types
                val = dc.__dict__[item]
                if isinstance(val, (int, long)):
                    pass
                elif isinstance( val, StructType ):
#                     sigs.extend( val.tointbv() )
                    sigs.extend( collect( val ))
                elif isinstance(val, myhdl.Array):
                    pass
                elif isinstance(val._val, ( bool, myhdl.intbv )):
                    sigs.append( val  )
            return sigs

        return myhdl.ConcatSignal(  *reversed( collect( self ) ) )

    def __repr__(self):
#         retval = 'StructType('
#         for item in vars( self ):
#             retval += '\'{}\': {}, '.format(item, repr(self.__dict__[item]))
# 
#         retval += ' nrbits: {})'.format(self._nrbits)
#         return retval
        return 'StructType {} {}'.format( self.__class__.__name__, vars( self ))

    def copy(self):
        ''' return a new object '''
        # we build a new object
        srcvars = vars(self)
        obj = StructType()
        for var in srcvars:
            obj.addmember(var, srcvars[var])

        return obj


    def ref(self):
        ''' returns a condensed name representing the contents of the struct, excluding the name!'''
#         refs = vars( self )
#         keys = refs.keys() # keys are sorted in order of declaration
#         r = self.__class__.__name__
        retval = 'r'
        for key in  vars( self ).keys():
            s = vars( self )[key]
            if isinstance(s , _Signal):
                retval+= '_{}{}'.format( 's' if s._min < 0 else 'u', s._nrbits )

            elif isinstance(s, (Array, StructType)):
                retval += s.ref()

            elif isinstance(s, integer_types):
                pass

            else:
                pass
        return retval


    def _setNextVal(self, val):
        refs = vars( self )
        vargs = vars( val )
        for k in refs:
            if isinstance( refs[k], _Signal):
                refs[k]._setNextVal( vargs[k]._val) 
    

    def _update(self):
        # delegate to Signal
        # collect the waiters for all Signals in the current StructType
        w = []
        refs = vars(self)
        for k in refs:
            if isinstance( refs[k], (_Signal, StructType, Array)):
                w.extend( refs[k]._update() )
        return w


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




if __name__ == '__main__':
    import random

    import myhdl
#   
# #     class myobj( StructType ):
# #         def __init__(self, width):
# # #             self.WIDTH_PIXEL = width
# #             self.b = Signal( intbv(0)[width:])
# #             self.g = Signal( intbv(0)[width:])
# #             self.r = Signal( intbv(0)[width:])
# # 
# #                     
# #         def torecord(self, v):
# #             ''' we 'reformat' a vector into an interface/record '''
# # #             trWIDTH_PIXEL = self.WIDTH_PIXEL
# #             trWIDTH_PIXEL = len(self.r)
# #             @myhdl.always_comb
# #             def torecord():
# #                 lv = v
# #                 self.b.next  = lv[(0+1) * trWIDTH_PIXEL : 0 * trWIDTH_PIXEL]
# #                 self.g.next  = lv[(1+1) * trWIDTH_PIXEL : 1 * trWIDTH_PIXEL]
# #                 self.g.next  = lv[(2+1) * trWIDTH_PIXEL : 2 * trWIDTH_PIXEL]
# # 
# #             return torecord            
# #         
# # #         def setrgb(self, values):
# # #             @myhdl.always_comb
# # #             def setrgb():
# # #                 self.b.next = values[0]
# # #                 self.g.next = values[1]
# # #                 self.r.next = values[2]
# # #             return setrgb
# #         
# #         
# #     m = myobj(10)
#     m = StructType( 'rgb')
#     m.addmember( ('b', 1, 8) )
#     m.addmember( ('g', 2, 8) )
#     m.addmember( ('r', Signal( intbv(3)[8:])) )
#     print( m )
#     print( repr(m.b) )
#     print( repr( m ))
#     print( dir(m))
#     print( vars(m))
#     print( isinstance(m, StructType))
#     print( m.ref() )
#     
#     m2 = StructType( 'rgb2' , (  ('b', 11, 8),  ('g', 22, 8),  ('r', 33, 8) ))
#     print( m2 )
#     print( m2.ref() )
# #     print( m._traceSignals())
# #     s = m.setrgb((1,2,3))
# #     print( m )


    print( '====Exercising StructType ====')
    class Newclass( StructType ):
        ''' a new class derived from Dynclass '''
        def __init__(self):
            # must init the superclass
            super(Newclass, self).__init__()
            # add members
            self.addmember('a', myhdl.Signal(myhdl.intbv(6)[4:]))
            self.addmember('b', myhdl.Signal(bool( False)))
            self.addmember('c', myhdl.Signal(bool( True)))
            self.addmember('d', myhdl.Signal(myhdl.intbv(3, min=-4, max=15)))

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

    class Newclass2( StructType ):
        ''' another new class derived from Dynclass '''
        def __init__(self):
            # must init the superclass
            super(Newclass2, self).__init__()
            # add members
            self.addmember('nc', nc)
            self.addmember('e', myhdl.Signal(myhdl.intbv(10)[4:]))

    nc2 = Newclass2()

    print( 'nc2: {}' .format( nc2 ))
#     for item in inspect.getmembers( nc2):
#         print( item )
#     print( '================')

    print( 'nc2: intbv: ', hex(nc2.tointbv()))
    print( 'nc2.nc.a: ', repr(nc2.nc.a))
    print( 'nc2.ref(): {}'.format( nc2.ref()) )

    class Newclass3( StructType ):
        ''' another new class derived from Dynclass '''
        def __init__(self):
            # must init the superclass
            super(Newclass3, self).__init__( decl = (('nc2', nc2),
                                                     ('f', myhdl.Signal(myhdl.intbv(10)[4:])),
                                                     ('r', myhdl.Array((2,2), myhdl.Signal( myhdl.intbv(0)[4:]))),
                                                     ('nca', myhdl.Array((2,2), nc))
                                                    )
                                           )

    nc3 = Newclass3()

    print( 'nc3: {}' .format( nc3 ))
    print( 'nc3.nc2.nc.c: {}'.format( repr( nc3.nc2.nc.c)))
    print( 'nc3.r: {}'.format( repr( nc3.r)))
    print( 'nc3.nca: {}'.format( repr( nc3.nca)))
    print( 'cc3.ref(): {}'.format( nc3.ref()) )

    nc4 = nc3.copy()
    print( 'nc4: {}' .format( nc4 ))
    
    # an alternate way
    lv1 = myhdl.Signal( myhdl.intbv(0)[8:])
    dc1 = StructType(decl=(('g', myhdl.Signal(myhdl.intbv(10)[4:])), ('h', myhdl.Signal(myhdl.intbv(10)[4:]))), vector=lv1)
    print( 'dc1: {}' .format( dc1 ))
    print( 'dc1.g: {}'.format( repr(dc1.g) ))
    print( 'dc1.ref(): {}'.format( dc1.ref()) )


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
    

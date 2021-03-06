#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2011 Jan Decaluwe
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

""" Module that provides the Signal class and related objects.

This module provides the following objects:

Signal -- class to model hardware signals
posedge -- callable to model a rising edge on a signal in a yield statement
negedge -- callable to model a falling edge on a signal in a yield statement

"""
from __future__ import absolute_import
from __future__ import print_function

from inspect import currentframe, getouterframes
from copy import copy, deepcopy
import operator

from myhdl._compat import integer_types, string_types, long
from myhdl import _simulator as sim
from myhdl._simulator import _signals, _siglist, _futureEvents, now
from myhdl._intbv import intbv
from myhdl._bin import bin
# from myhdl._enum import EnumType

_schedule = _futureEvents.append


def _isListOfSigs(obj):
    """ Check if obj is a non-empty list of signals. """
    if isinstance(obj, list) and len(obj) > 0:
        for e in obj:
            if not isinstance(e, _Signal):
                return False
        return True
    else:
        return False


class _WaiterList(list):

    def purge(self):
        if self:
            self[:] = [w for w in self if not w.hasRun]


class _PosedgeWaiterList(_WaiterList):

    def __init__(self, sig):
        self.sig = sig

    def _toVerilog(self):
        return "posedge %s" % self.sig._name

    def _toVHDL(self):
        return "rising_edge(%s)" % self.sig._name


class _NegedgeWaiterList(_WaiterList):

    def __init__(self, sig):
        self.sig = sig

    def _toVerilog(self):
        return "negedge %s" % self.sig._name

    def _toVHDL(self):
        return "falling_edge(%s)" % self.sig._name


def posedge(sig):
    """ Return a posedge trigger object """
    return sig.posedge


def negedge(sig):
    """ Return a negedge trigger object """
    return sig.negedge

# signal factory function


def Signal(val=None, delay=None):
    """ Return a new _Signal (default or delay 0) or DelayedSignal """
    if delay is not None:
        if delay < 0:
            raise TypeError("Signal: delay should be >= 0")
        return _DelayedSignal(val, delay)
    else:
        return _Signal(val)


class _Signal(object):

    """ _Signal class.

    Properties:
    val -- current value (read-only)
    next -- next value (read-write)

    """

    __slots__ = ('_next', '_val', '_min', '_max', '_type', '_init',
                 '_eventWaiters', '_posedgeWaiters', '_negedgeWaiters',
                 '_code', '_tracing', '_nrbits', '_checkVal',
                 '_setNextVal', '_copyVal2Next', '_printVcd',
                 '_driven', '_read', '_name', '_used', '_inList',
                 '_waiter', 'toVHDL', 'toVerilog', '_slicesigs',
                 '_suppresswarning', '_namelevel', '_attribute'
                 )

    def __init__(self, val=None):
        """ Construct a signal.

        val -- initial value

        """
#         print('Signal', repr(val))
        self._init = deepcopy(val)
        self._val = deepcopy(val)
        self._next = deepcopy(val)
        self._min = self._max = None
        self._name = self._read = self._driven = None
        self._namelevel = -1
        self._used = False
        self._inList = False
        self._nrbits = 0
        self._attribute = None
        self._printVcd = self._printVcdStr
        self._suppresswarning = False
        if isinstance(val, bool):
            self._type = bool
            self._setNextVal = self._setNextBool
            self._printVcd = self._printVcdBit
            self._nrbits = 1
        elif isinstance(val, integer_types):
            self._type = integer_types
            self._setNextVal = self._setNextInt
        elif isinstance(val, intbv):
            self._type = intbv
            self._min = val._min
            self._max = val._max
            self._nrbits = val._nrbits
            self._setNextVal = self._setNextIntbv
            if self._nrbits:
                self._printVcd = self._printVcdVec
            else:
                self._printVcd = self._printVcdHex
#         elif val in ('Open', 'Low', 'High'):
#             if val == 'Open':
#                 pass
#             elif val == 'Low':
#                 self._type = bool
#                 self._val = 0
#                 self._printVcd = self._printVcdBit
#                 self._nrbits = 1
#             elif val == 'High':
#                 self._type = bool
#                 self._val = 1
#                 self._printVcd = self._printVcdBit
#                 self._nrbits = 1

#         elif isinstance(val, _Signal):
#             self._type = val._type
#             #differentiate between bool, intbv and others
#             if self._type == bool:
#                 self._setNextVal = self._setNextBool
#                 self._printVcd = self._printVcdBit
#                 self._nrbits = 1
#             elif self._type == intbv:
#                 self._min = val._min
#                 self._max = val._max
#                 self._nrbits = val._nrbits
#                 self._setNextVal = self._setNextIntbv
#                 if self._nrbits:
#                     self._printVcd = self._printVcdVec
#                 else:
#                     self._printVcd = self._printVcdHex
#             else:
#                 # others
#                 raise ValueError( "Don't handle {}".format( val._type ))
        else:
            self._type = type(val)
            if isinstance(val, EnumItemType):
                self._setNextVal = self._setNextNonmutable
                # let's print it in hex or decimal?
                self._printVcd = self._printVcdEnum
            else:
                self._setNextVal = self._setNextMutable
            if hasattr(val, '_nrbits'):
                self._nrbits = val._nrbits
        self._eventWaiters = _WaiterList()
        self._posedgeWaiters = _PosedgeWaiterList(self)
        self._negedgeWaiters = _NegedgeWaiterList(self)
        self._code = ""
        self._slicesigs = []
        self._tracing = 0
        _signals.append(self)
#         tracejbdedent()

    def _clear(self):
        del self._eventWaiters[:]
        del self._posedgeWaiters[:]
        del self._negedgeWaiters[:]
        self._val = deepcopy(self._init)
        self._next = deepcopy(self._init)
        self._name = self._read = self._driven = None
        self._suppresswarning = False
        for s in self._slicesigs:
            s._clear()

    def _update(self):
        val, next = self._val, self._next
        if val != next:
            waiters = self._eventWaiters[:]
            del self._eventWaiters[:]
            if not val and next:
                waiters.extend(self._posedgeWaiters[:])
                del self._posedgeWaiters[:]
            elif not next and val:
                waiters.extend(self._negedgeWaiters[:])
                del self._negedgeWaiters[:]
            if next is None:
                self._val = None
            elif isinstance(val, intbv):
                self._val._val = next._val
            elif isinstance(val, (integer_types, EnumItemType)):
                self._val = next
            else:
                self._val = deepcopy(next)
            if self._tracing:
                self._printVcd()
            return waiters
        else:
            return []

    # support for the 'val' attribute
    @property
    def val(self):
        return self._val

    # support for the 'next' attribute
    @property
    def next(self):
        #        if self._next is self._val:
        #            self._next = deepcopy(self._val)
        _siglist.append(self)
        return self._next

    @next.setter
    def next(self, val):
        if isinstance(val, _Signal):
            val = val._val
        self._setNextVal(val)
        _siglist.append(self)

    # support for the 'posedge' attribute
    @property
    def posedge(self):
        return self._posedgeWaiters

    # support for the 'negedge' attribute
    @property
    def negedge(self):
        return self._negedgeWaiters

    # support for the 'min' and 'max' attribute
    @property
    def max(self):
        return self._max

    @property
    def min(self):
        return self._min

    # support for the 'driven' attribute
    @property
    def driven(self):
        return self._driven

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

    # set next methods
    def _setNextBool(self, val):
        if isinstance(val, intbv):
            val = val._val
        if not val in (0, 1):
            raise ValueError(
                "Expected boolean value, got %s (%s), did you forget the ':' in a Signal(intbv()[WIDTH:] declaration?" % (repr(val), type(val)))
        self._next = val

    def _setNextInt(self, val):
        if isinstance(val, intbv):
            val = val._val
        elif not isinstance(val, (integer_types, intbv)):
            raise TypeError("Expected int or intbv, got %s" % type(val))
        self._next = val

    def _setNextIntbv(self, val):
        if isinstance(val, integer_types):
            lval = val

        elif isinstance(val, intbv):
            lval = val._val

        elif isinstance(val, string_types):
            mval = val.replace('_', '')
            lval = long(mval, 2)

        elif isinstance(val, tuple):
            # tuple assignment in  stead of 'concat'
            #             print('Signal: Tuple Assignment')
            lval = 0
            for v in val:
                if isinstance(v, integer_types):
                    lval <<= 1
                    lval += 1 if v else 0
                elif isinstance(v, intbv):
                    lval <<= len(v)
                    lval += v
                elif isinstance(v, string_types):
                    mval = v.replace('_', '')
                    lval <<= len(mval)
                    lval += long(mval, 2)
                elif isinstance(v, _Signal):
                    if isinstance(v._val, intbv):
                        lval <<= len(v)
                        lval += v
                    else:
                        # bool
                        lval <<= 1
                        lval += 1 if v else 0

#         elif not isinstance(val, integer_types):

        elif isinstance(val, EnumItemType):
            lval = int(val)

        else:
            raise TypeError("Expected int or intbv, got %s" % type(val))
        self._next._val = lval
#         self._next._handleBounds(self)
        self._next._handleBounds()

    def _setNextNonmutable(self, val):
#         if not isinstance(val, self._type):
#             raise TypeError("Expected %s, got %s" % (self._type, type(val)))
#         self._next = val
        if isinstance(val, self._type):
            self._next = val
        elif isinstance(val, intbv):
            # do some hocuspocus
            self._next = self._type.make(val)
        else:
            raise TypeError("Expected %s, got %s" % (self._type, type(val)))

    def _setNextMutable(self, val):
        if not isinstance(val, self._type):
            raise TypeError("Expected %s, got %s" % (self._type, type(val)))
        self._next = deepcopy(val)

    # vcd print methods
    def _printVcdStr(self):
        print("s%s %s" % (str(self._val), self._code), file=sim._tf)

    def _printVcdHex(self):
        if self._val is None:
            print("sz %s" % self._code, file=sim._tf)
        else:
            print("s%s %s" % (hex(self._val), self._code), file=sim._tf)

    def _printVcdBit(self):
        if self._val is None:
            print("z%s" % self._code, file=sim._tf)
        else:
            print("%d%s" % (self._val, self._code), file=sim._tf)

    def _printVcdEnum(self):
        print("s%s %s" % (str(self._val), self._code), file=sim._tf)

    def _printVcdVec(self):
        if self._val is None:
            print("b%s %s" % ('z' * self._nrbits, self._code), file=sim._tf)
        else:
            print("b%s %s" %
                  (bin(self._val, self._nrbits), self._code), file=sim._tf)

    ### use call interface for shadow signals ###
    def __call__(self, left=None, right=None, signed=False, reverse=False):
        if left is None:
            if reverse:
                s = _ReverseSignal(self)
            else:
                s = _CloneSignal(self)
        else:
            if right is None:
                s = _IndexSignal(self, left)
            else:
                s = _SliceSignal(self, left, right, signed)
        self._slicesigs.append(s)
        return s

    ### operators for which delegation to current value is appropriate ###

    def __hash__(self):
        raise TypeError("Signals are unhashable")

    def __bool__(self):
        return bool(self._val)

    __nonzero__ = __bool__

    # length
    def __len__(self):
        return self._nrbits
        # return len(self._val)

    @property
    def nbits(self):
        return self._nrbits

    @property
    def signed(self):
        return self._min is not None and self._min < 0

    # indexing and slicing methods

    def __getitem__(self, key):
        return self._val[key]

    # integer-like methods

    def __add__(self, other):
        if isinstance(other, _Signal):
            return self._val + other._val
        else:
            return self._val + other

    def __radd__(self, other):
        return other + self._val

    def __sub__(self, other):
        if isinstance(other, _Signal):
            return self._val - other._val
        else:
            return self._val - other

    def __rsub__(self, other):
        return other - self._val

    def __mul__(self, other):
        if isinstance(other, _Signal):
            return self._val * other._val
        else:
            return self._val * other

    def __rmul__(self, other):
        return other * self._val

    def __truediv__(self, other):
        if isinstance(other, _Signal):
            return self._val / other._val
        else:
            return self._val / other

    def __rtruediv__(self, other):
        return other / self._val

    def __floordiv__(self, other):
        if isinstance(other, _Signal):
            return self._val // other._val
        else:
            return self._val // other

    def __rfloordiv__(self, other):
        return other // self._val

    def __mod__(self, other):
        if isinstance(other, _Signal):
            return self._val % other._val
        else:
            return self._val % other

    def __rmod__(self, other):
        return other % self._val

    # XXX divmod

    def __pow__(self, other):
        if isinstance(other, _Signal):
            return self._val ** other._val
        else:
            return self._val ** other

    def __rpow__(self, other):
        return other ** self._val

    def __lshift__(self, other):
        if isinstance(other, _Signal):
            return self._val << other._val
        else:
            return self._val << other

    def __rlshift__(self, other):
        return other << self._val

    def __rshift__(self, other):
        if isinstance(other, _Signal):
            return self._val >> other._val
        else:
            return self._val >> other

    def __rrshift__(self, other):
        return other >> self._val

    def __and__(self, other):
        if isinstance(other, _Signal):
            return self._val & other._val
        else:
            return self._val & other

    def __rand__(self, other):
        return other & self._val

    def __or__(self, other):
        if isinstance(other, _Signal):
            return self._val | other._val
        else:
            return self._val | other

    def __ror__(self, other):
        return other | self._val

    def __xor__(self, other):
        if isinstance(other, _Signal):
            return self._val ^ other._val
        else:
            return self._val ^ other

    def __rxor__(self, other):
        return other ^ self._val

    def __neg__(self):
        return -self._val

    def __pos__(self):
        return +self._val

    def __abs__(self):
        return abs(self._val)

    def __invert__(self):
        return ~self._val

    # conversions

    def __int__(self):
        return int(self._val)

    def __long__(self):
        return long(self._val)

    def __float__(self):
        return float(self._val)

    def __oct__(self):
        return oct(self._val)

    def __hex__(self):
        return hex(self._val)

    def __index__(self):
        return int(self._val)

    # comparisons
    def __eq__(self, other):
        return self.val == other

    def __ne__(self, other):
        return self.val != other

    def __lt__(self, other):
        return self.val < other

    def __le__(self, other):
        return self.val <= other

    def __gt__(self, other):
        return self.val > other

    def __ge__(self, other):
        return self.val >= other

    # method lookup delegation
    def __getattr__(self, attr):
        return getattr(self._val, attr)

    # representation
    def __str__(self):
        #         print('Signal.__str__()', end='')
        if self._name:
            return self._name
        else:
            return str(self._val)

    def __repr__(self):
        if self._name:
            return "{}: Signal({})".format(self._name, repr(self._val))
        else:
            return "Signal({})".format(repr(self._val))

    def _toVerilog(self):
        return self._name

    # augmented assignment not supported
    def _augm(self):
        raise TypeError("Signal object doesn't support augmented assignment")

    __iadd__ = __isub__ = __imul__ = __ipow__ = __imod__ = _augm
    __ior__ = __iand__ = __ixor__ = __irshift__ = __ilshift__ = _augm
    __itruediv__ = __ifloordiv__ = _augm

    # index and slice assignment not supported
    def __setitem__(self, key, val):
        raise TypeError("Signal object doesn't support item/slice assignment")

    # continues assignment support
    def assign(self, sig):

        self.driven = "wire"

        def genFunc():
            while 1:
                self.next = sig._val
                yield sig

        self._waiter = _SignalWaiter(genFunc())

        def toVHDL():
            print('Signal toVHDL', self.sig)
            return "%s <= %s;" % (self._name, sig._name)

        def toVerilog():
            return "assign %s = %s;" % (self._name, sig._name)

        self.toVHDL = toVHDL
        self.toVerilog = toVerilog

    # copy, deepcopy hooks
    def __copy__(self):
        return Signal(self._val)

    def __deepcopy__(self, visit):
        return Signal(self._val)

    # jb's (debatable?) extensions
    def copy(self, extendbits=None):
        #         print(extendbits)
        if extendbits is None:
            return Signal(self._val)
        else:
            if isinstance(self._val, bool):
                raise ValueError('Cannot extendbits of \'bool\' Signal')
            elif isinstance(extendbits, _Signal):
                #                 print('caught', repr(extendbits), len(extendbits))
                if self._min < 0:
                    return Signal(intbv(0, min=int(self._val._min * (2 ** len(extendbits))),
                                        max=int(self._val._max * (2 ** len(extendbits)))))
                else:
                    return Signal(intbv(0, min=int(extendbits._val._min * (2 ** len(self))),
                                        max=int(extendbits._val._max * (2 ** len(self)))))

            elif isinstance(extendbits, intbv):
                #                 print('caught', repr(extendbits), len(extendbits))
                if self._min < 0:
                    return Signal(intbv(0, min=int(self._val._min * (2 ** len(extendbits))),
                                        max=int(self._val._max * (2 ** len(extendbits)))))
                else:
                    return Signal(intbv(0, min=int(extendbits._min * (2 ** len(self))),
                                        max=int(extendbits._max * (2 ** len(self)))))

            elif isinstance(extendbits, int):
                return Signal(intbv(0, min=int(self._val._min * (2 ** extendbits)),
                                    max=int(self._val._max * (2 ** extendbits))))
            else:
                raise ValueError('Signal.copy(extendbits=None) expects \'int\' or \'Signal(intbv())\' as argument ')

    def suppressWarning(self):
        self._suppresswarning = True


class _DelayedSignal(_Signal):

    __slots__ = ('_nextZ', '_delay', '_timeStamp',
                 )

    def __init__(self, val=None, delay=1):
        """ Construct a new DelayedSignal.

        Automatically invoked through the Signal new method.
        val -- initial value
        delay -- non-zero delay value
        """
        _Signal.__init__(self, val)
        self._nextZ = val
        self._delay = delay
        self._timeStamp = 0

    def _update(self):
        if self._next != self._nextZ:
            self._timeStamp = sim._time
        self._nextZ = self._next
        t = sim._time + self._delay
        _schedule((t, _SignalWrap(self, self._next, self._timeStamp)))
        return []

    def _apply(self, next, timeStamp):
        val = self._val
        if timeStamp == self._timeStamp and val != next:
            waiters = self._eventWaiters[:]
            del self._eventWaiters[:]
            if not val and next:
                waiters.extend(self._posedgeWaiters[:])
                del self._posedgeWaiters[:]
            elif not next and val:
                waiters.extend(self._negedgeWaiters[:])
                del self._negedgeWaiters[:]
            self._val = copy(next)
            if self._tracing:
                self._printVcd()
            return waiters
        else:
            return []

    # support for the 'delay' attribute
    @property
    def delay(self):
        return self._delay

    @delay.setter
    def delay(self, delay):
        self._delay = delay


class _SignalWrap(object):

    def __init__(self, sig, next, timeStamp):
        self.sig = sig
        self.next = next
        self.timeStamp = timeStamp

    def apply(self):
        return self.sig._apply(self.next, self.timeStamp)


# for export
SignalType = _Signal

# avoid circular imports

from myhdl._ShadowSignal import _SliceSignal, _IndexSignal, _CloneSignal, _ReverseSignal
from myhdl._Waiter import _SignalWaiter
from myhdl._enum import EnumItemType
# from myhdl._enum import EnumType

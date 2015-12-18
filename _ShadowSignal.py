#  This file is part of the myhdl library, a Python package for using
#  Python as a Hardware Description Language.
#
#  Copyright (C) 2003-2015 Jan Decaluwe
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

""" Module that provides the ShadowSignal classes


"""
from __future__ import absolute_import

import warnings
from copy import deepcopy

from myhdl._compat import long
from myhdl._Signal import _Signal
from myhdl._Waiter import _SignalWaiter, _SignalTupleWaiter
from myhdl._intbv import intbv
from myhdl._simulator import _siglist
from myhdl._bin import bin


# # tracing the poor man's way
# from myhdl.tracejb import tracejb, logjb, tracejbdedent, logjbinspect


# shadow signals


class _ShadowSignal(_Signal):

    __slots__ = ('_waiter', )

    def __init__(self, val):
        _Signal.__init__(self, val)
        # self._driven = True # set this in conversion analyzer

    # remove next attribute assignment
    @_Signal.next.setter
    def next(self, val):
        raise AttributeError("ShadowSignals are readonly")



class _SliceSignal(_ShadowSignal):

    __slots__ = ('_sig', '_left', '_right')

    def __init__(self, sig, left , right, signed ):
        ### XXX error checks
        if not signed:
            _ShadowSignal.__init__(self, sig[left:right])
        else:
            if sig[left-1]:
                val = -(2**(left - right) - sig[left:right])
            else:
                val = sig[left:right]
            _ShadowSignal.__init__(self, intbv( val , min = -2**(left - right - 1), max = 2**(left - right -1)) )

        self._sig = sig
        self._left = left
        self._right = right
#         if right is None:
#             gen = self._genfuncIndex()
#         else:
        gen = self._genfuncSlice()
        self._waiter = _SignalWaiter(gen)



    def _genfuncSlice(self):
#         tracejb('_ShadowSignal: _SliceSignal: _genfuncSlice')
#         logjbinspect(self._sig, 'self._sig', True)
        sig, left, right = self._sig, self._left, self._right
        set_next = _Signal.next.fset
#         tracejbdedent()
        while 1:
            set_next(self, sig[left:right])
            yield sig


    def _setName(self, hdl):
#         tracejb(hdl, '_ShadowSignal: _SliceSignal: _setName')
#         logjb( self._sig , 'self._sig')
#         logjbinspect(self._sig)
        if hdl == 'Verilog':
            self._name = "%s[%s-1:%s]" % (self._sig._name, self._left, self._right)
        else:
            if self._sig._min < 0:
                self._name = "unsigned( %s( %s-1 downto %s ))" % (self._sig._name, self._left, self._right)
            else:
                self._name = "%s(%s-1 downto %s)" % (self._sig._name, self._left, self._right)
#                self._name = " normalise( %s(%s-1 downto %s) )" % (self._sig._name, self._left, self._right)
#         logjb( self._name, 'self._name')
#         tracejbdedent()

    def _markRead(self):
        self._read = True
        self._sig._read = True

    def _markUsed(self):
        self._used = True
        self._sig._used = True


    def toVerilog(self):
        return "assign %s = %s[%s-1:%s];" % (self._name, self._sig._name, self._left, self._right)

    def toVHDL(self):
#         tracejb('_ShadowSignal: _SliceSignal: toVHDL')
#         tracejbdedent()
        return "    %s <= %s(%s-1 downto %s);" % (self._name, self._sig._name, self._left, self._right)
#        return "%s <= normalise( %s(%s-1 downto %s) );" % (self._name, self._sig._name, self._left, self._right)


class _IndexSignal(_ShadowSignal):

    __slots__ = ('_sig', '_left', '_right')

    def __init__(self, sig, left):
        _ShadowSignal.__init__(self, sig[left])
        self._sig = sig
        self._left = left
        self._right = None
        gen = self._genfuncIndex()
        self._waiter = _SignalWaiter(gen)

    def _genfuncIndex(self):
        sig, index = self._sig, self._left
        set_next = _Signal.next.fset
        while 1:
            set_next(self, sig[index])
            yield sig


    def _setName(self, hdl):
#         tracejb(hdl, '_ShadowSignal: _IndexSignal: _setName')
#         logjb( self._sig , 'self._sig')
#         logjbinspect(self._sig)
        if hdl == 'Verilog':
            self._name = "%s[%s]" % (self._sig._name, self._left)
        else:
            self._name = "%s(%s)" % (self._sig._name, self._left)
#         logjb( self._name, 'self._name')
#         tracejbdedent()

    def _markRead(self):
        self._read = True
        self._sig._read = True

    def _markUsed(self):
        self._used = True
        self._sig._used = True


    def toVerilog(self):
        return "assign %s = %s[%s];" % (self._name, self._sig._name, self._left)


    def toVHDL(self):
#         tracejb('_ShadowSignal: _IndexSignal: toVHDL')
#         tracejbdedent()
        return "    %s <= %s(%s);" % (self._name, self._sig._name, self._left)


class _CloneSignal(_ShadowSignal):

    __slots__ = ('_sig', '_left', '_right')

    def __init__(self, sig):
        ### XXX error checks
        # a 'clone'
        _ShadowSignal.__init__(self, sig.val)
        self._sig = sig
        self._left = None
        self._right = None
        gen = self._genfuncClone()
        self._waiter = _SignalWaiter(gen)
        self._driven = 'wire'

    def _genfuncClone(self):
        sig = self._sig
        set_next = _Signal.next.fset
        while 1:
            set_next(self, sig)
            yield sig

    def _setName(self, hdl):
#         tracejb(hdl, '_ShadowSignal: _CloneSignal: _setName')
#         logjb( self._sig , 'self._sig')
#         logjbinspect(self._sig)
        if hdl == 'Verilog':
            self._name = "%s" % (self._sig._name)
        else:
            self._name = "%s" % (self._sig._name)
            
#         logjb( self._name, 'self._name')
#         tracejbdedent()

    def _markRead(self):
        self._read = True
        self._sig._read = True

    def _markUsed(self):
        self._used = True
        self._sig._used = True


    def toVerilog(self):
        return "assign %s = %s;" % (self._name, self._sig._name)

    def toVHDL(self):
#         tracejb('_ShadowSignal: _SliceSignal: toVHDL')
#         tracejbdedent()
        return "    %s <= %s;" % (self._name, self._sig._name)



class ConcatSignal(_ShadowSignal):

    __slots__ = ('_args', '_sigargs', '_initval')

    def __init__(self, *args):
        assert len(args) >= 2
        self._args = args
        self._sigargs = sigargs = []

        nrbits = 0
        val = 0
        for a in args:
            if isinstance(a, intbv):
                w = a._nrbits
                v = a._val
            elif isinstance(a, _Signal):
#                 a._read = True
                sigargs.append(a)
                w = a._nrbits
                if isinstance(a._val, intbv):
                    v = a._val._val
                else:
                    v = a._val
            elif isinstance(a, bool):
                w = 1
                v = a
            elif isinstance(a, str):
                w = len(a)
                v = long(a, 2)
            else:
                raise TypeError("ConcatSignal: inappropriate argument type: %s" \
                                % type(a))
            a._read = True
            nrbits += w
            val = val << w | v & (long(1) << w)-1
            
        self._initval = val
        ini = intbv(val)[nrbits:]
        _ShadowSignal.__init__(self, ini)
        self._driven = 'wire'
        gen = self.genfunc()
        self._waiter = _SignalTupleWaiter(gen)

    def genfunc(self):
        set_next = _Signal.next.fset
        args = self._args
        sigargs = self._sigargs
        nrbits = self._nrbits
        newval = intbv(self._initval)[nrbits:]
        while 1:
            hi = nrbits
            for a in args:
                if isinstance(a, bool):
                    w = 1
                else:
                    w = len(a)
                lo = hi - w
                # note: 'a in sigargs' is equivalence check, not identity
                if isinstance(a, _Signal):
                    if isinstance(a._val, intbv):
                        newval[hi:lo] = a[w:]
                    else:
                        newval[hi:lo] = a
                hi = lo
            set_next(self, newval)
            yield sigargs

    def _markRead(self):
#         tracejb( 'ConcatSignal _markRead')
        self._read = True
        for s in self._sigargs:
#             logjbinspect( s , 's', True)
            s._markRead()
#         tracejbdedent()

    def _markUsed(self):
#         tracejb( 'ConcatSignal _markUsed')
        self._used = True
        for s in self._sigargs:
#             logjbinspect( s , 's', True)
            s._markUsed()
#         tracejbdedent()

    def toVHDL(self):
#         tracejb('_ShadowSignal->ConcatSignal->toVHDL')
        lines = []
        ini = intbv(self._initval)[self._nrbits:]
        hi = self._nrbits
        for a in self._args:
#             logjbinspect(a, 'a', True)
            if isinstance(a, bool):
                w = 1
            else:
                w = len(a)
            lo = hi - w
            if w == 1:
                if isinstance(a, _Signal):
                    if a._type == bool: # isinstance(a._type , bool): <- doesn't work
                        lines.append("    %s(%s) <= %s;" % (self._name, lo, a._name))
                    else:
                        lines.append("    %s(%s) <= %s(0);" % (self._name, lo, a._name))
                else:
                    lines.append("    %s(%s) <= '%s';" % (self._name, lo, bin(ini[lo])))
            else:
                if isinstance(a, _Signal):
#                     logjbinspect(a, 'a', True)
                    lines.append("    %s(%s-1 downto %s) <= %s;" % (self._name, hi, lo, a._name))
                else:
                    lines.append('    %s(%s-1 downto %s) <= "%s";' % (self._name, hi, lo, bin(ini[hi:lo],w)))
            hi = lo
#         logjb( lines, 'lines')
#         tracejbdedent()
        return "\n".join(lines)

    def toVerilog(self):
        lines = []
        ini = intbv(self._initval)[self._nrbits:]
        hi = self._nrbits
        for a in self._args:
            if isinstance(a, bool):
                w = 1
            else:
                w = len(a)
            lo = hi - w
            if w == 1:
                if isinstance(a, _Signal):
                    if a._type == bool:
                        lines.append("assign %s[%s] = %s;" % (self._name, lo, a._name))
                    else:
                        lines.append("assign %s[%s] = %s[0];" % (self._name, lo, a._name))
                else:
                    lines.append("assign %s[%s] = 'b%s;" % (self._name, lo, bin(ini[lo])))
            else:
                if isinstance(a, _Signal):
                    lines.append("assign %s[%s-1:%s] = %s;" % (self._name, hi, lo, a._name))
                else:
                    lines.append("assign %s[%s-1:%s] = 'b%s;" % (self._name, hi, lo, bin(ini[hi:lo],w)))
            hi = lo
        return "\n".join(lines)


# Tristate signal


class BusContentionWarning(UserWarning):
    pass

warnings.filterwarnings('always', r".*", BusContentionWarning)

# def Tristate(val, delay=None):
#     """ Return a new Tristate(default or delay 0) or DelayedTristate """
#     if delay is not None:
#         if delay < 0:
#             raise TypeError("Signal: delay should be >= 0")
#         return _DelayedTristate(val, delay)
#     else:
#         return _Tristate(val)


def TristateSignal(val):
    return _TristateSignal(val)


class _TristateSignal(_ShadowSignal):

    __slots__ = ('_drivers', '_orival' )

    def __init__(self, val):
        self._drivers = []
        # construct normally to set type / size info right
        _ShadowSignal.__init__(self, val)
        self._orival = deepcopy(val) # keep for drivers
        # reset signal values to None
        self._next = self._val = self._init = None
        self._waiter = _SignalTupleWaiter(self._resolve())
        
    def driver(self):
        d = _TristateDriver(self)
        self._drivers.append(d)
        return d

    def _resolve(self):
        # set_next = _ShadowSignal._set_next
        senslist = self._drivers
        while 1:
            yield senslist
            res = None
            for d in senslist:
                if res is None:
                    res = d._val
                elif d._val is not None:
                    warnings.warn("Bus contention", category=BusContentionWarning)
                    res = None
                    break
            self._next = res
            _siglist.append(self)


    def toVerilog(self):
        lines = []
        for d in self._drivers:
            if d._driven:
                lines.append("assign %s = %s;" % (self._name, d._name))
        return "\n".join(lines)

    def toVHDL(self):
        lines = []
        for d in self._drivers:
            if d._driven:
                lines.append("%s <= %s;" % (self._name, d._name))
        return "\n".join(lines)



class _TristateDriver(_Signal):

    __slots__ = ('_sig',)

    def __init__(self, sig):
        _Signal.__init__(self, sig._orival)
        # reset signal values to None
        self._next = self._val = self._init = None
        self._sig = sig

    @_Signal.next.setter
    def next(self, val):
        if isinstance(val, _Signal):
            val = val._val
        if val is None:
            self._next = None
        else:
            # restore original value to cater for intbv handler
            self._next = self._sig._orival
            self._setNextVal(val)
        _siglist.append(self)

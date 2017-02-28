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

""" Module that implements enum.

"""
from __future__ import absolute_import


from myhdl._bin import bin
from myhdl._Signal import _Signal
from myhdl._compat import string_types


class EnumType(object):

    def __init__(self):
        raise TypeError("class EnumType is only intended for type checking on subclasses")


class EnumItemType(object):

    def __init__(self):
        raise TypeError("class EnumItemType is only intended for type checking on subclasses")

supported_encodings = ("binary", "one_hot", "one_cold", "user")


def enum(*names, **kwargs):

    # args = args
    encoding = kwargs.get('encoding', None)
    if encoding is not None and encoding not in supported_encodings:
        raise ValueError("Unsupported enum encoding: %s\n    Supported encodings: %s" %
                         (encoding, supported_encodings))
    codedict = {}
    i = 0
    if encoding == "user":
        lnames = []
        # expect tuples
        maxval = 0
        for t in names:
            maxval = max(maxval, t[1])
        nrbits = len(bin(maxval))
        for t in names:
            codedict[t[0]] = t[1]
            lnames.append(t[0])

    else:
        lnames = names
        if encoding in ("one_hot", "one_cold"):
            nrbits = len(names)
        else:  # binary as default
            nrbits = len(bin(len(names) - 1))

        for name in names:
            if not isinstance(name, string_types):
                raise TypeError()
            if name in codedict:
                raise ValueError("enum literals should be unique")
            if encoding == "one_hot":
                code = bin(1 << i, nrbits)
            elif encoding == "one_cold":
                code = bin(~(1 << i), nrbits)
            else:  # binary as default
                code = bin(i, nrbits)
            if len(code) > nrbits:
                code = code[-nrbits:]
            codedict[name] = code
            i += 1

    class EnumItem(EnumItemType):

        def __init__(self, index, name, val, type):
            self._index = index
            self._name = name
            self._val = val
            self._nrbits = type._nrbits
            self._nritems = type._nritems
            self._type = type

        def __hash__(self):
            return hash((self._type, self._index))

        def __repr__(self):
            return self._name

        __str__ = __repr__

        def __int__(self):
            return int(self._val, 2)

        def __hex__(self):
            return hex(int(self._val, 2))

        def _toVerilog(self, dontcare=False):
            val = self._val
            if dontcare:
                if encoding == "one_hot":
                    val = val.replace('0', '?')
                elif encoding == "one_cold":
                    val = val.replace('1', '?')
            return "%d'b%s" % (self._nrbits, val)

        def _toVHDL(self):
            return self._name

        def __copy__(self):
            return self

        def __deepcopy__(self, memo=None):
            return self

        def _notImplementedCompare(self, other):
            raise NotImplementedError

        __le__ = __ge__ = __lt__ = __gt__ = _notImplementedCompare

        def __eq__(self, other):
            # other can be a signal
            # or an integer
            if isinstance(other, _Signal):
                other = other._val
            if not isinstance(other, EnumItemType) or type(self) is not type(other):
                raise TypeError("Type mismatch in enum item comparison")

            return self is other

#             elif isinstance( other, int ):
#                 other = other.val
#                 return int(self) is other

        def __ne__(self, other):
            if isinstance(other, _Signal):
                other = other._val
            if not isinstance(other, EnumItemType) or type(self) is not type(other):
                raise TypeError("Type mismatch in enum item comparison")
            return self is not other

#         # 29-05-2014 jb
#         def __add__(self, other):
#             print "1" , self, other
#             if isinstance(other, EnumItemType):
#                 return int(self._val) + int(other._val)
#             else:
#                 return int(self._val) + other
#
#         def __radd__(self, other):
#             print "2", self, other , self._val
#             if isinstance(other, EnumItemType):
#                 return int(self._val) + int(other._val)
#             else:
#                 return int(self._val) + other

    class Enum(EnumType):

        def __init__(self, lnames, codedict, nrbits, encoding):
            self.__dict__['_names'] = lnames
            self.__dict__['_nrbits'] = nrbits
            self.__dict__['_nritems'] = len(names)
            self.__dict__['_codedict'] = codedict
            self.__dict__['_encoding'] = encoding
            self.__dict__['_name'] = None
#             self._names = names
#             self._nrbits = nrbits
#             self._nritems = len(names)
#             self._codedict = codedict
#             self._encoding = encoding
#             self._name = None
            for index, name in enumerate(lnames):
                val = codedict[name]
                self.__dict__[name] = EnumItem(index, name, val, self)

        def __setattr__(self, attr, val):
            raise AttributeError("Cannot assign to enum attributes")

        def __len__(self):
            return len(self._names)

        def __repr__(self):
            return "<Enum: %s>" % ", ".join(names)

        __str__ = __repr__

        def __eq__(self, other):
            if (    self.__dict__['_nritems']  != other.__dict__['_nritems']) \
                    or (self.__dict__['_names']    != other.__dict__['_names']) \
                    or (self.__dict__['_nrbits']   != other.__dict__['_nrbits']) \
                    or (self.__dict__['_encoding'] != other.__dict__['_encoding']):
                return False
            return True

        def _setName(self, name):
            #             typename = "t_enum_%s" % name
            typename = "e_%s" % name
            self.__dict__['_name'] = typename

        _toVHDL = __str__

        def _toVHDL(self):
            if self._encoding == 'user':
                return "-- User encoded enum are not usable\n"
            typename = self.__dict__['_name']
            vstr = "    type %s is (\n        " % typename
            vstr += ",\n        ".join(self._names)
            vstr += "\n        );"
            if self._encoding is not None:
                codes = " ".join([self._codedict[name] for name in self._names])
                vstr += '\nattribute enum_encoding of %s: type is "%s";' % (typename, codes)
            return vstr

    return Enum(lnames, codedict, nrbits, encoding)

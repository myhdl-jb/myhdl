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
#
#  You should have received a copy of the GNU Lesser General Public
#  License along with this library; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA

""" myhdl toVHDL conversion module.

"""
from __future__ import absolute_import
from __future__ import print_function


import sys
import math
import os
import re

import inspect
from datetime import datetime
# import compiler
# from compiler import ast as astNode
import ast
from types import GeneratorType
import warnings
from copy import copy
import string

import myhdl
from myhdl import intbv, EnumItemType, EnumType, modbv, delay, posedge, negedge, concat, now, downrange, bin
from myhdl import ToVHDLError, ToVHDLWarning
from myhdl._extractHierarchy import (_HierExtr, _isMem, _getMemInfo,
                                     _UserVhdlCode, _userCodeMap)

from myhdl._instance import _Instantiator
from myhdl.conversion._misc import (_error, _kind, _context,
                                    _ConversionMixin, _Label, _genUniqueSuffix, _isConstant)
from myhdl.conversion._analyze import (_analyzeSigs, _analyzeGens, _analyzeTopFunc,
                                       _Ram, _Rom, _enumTypeSet)
from myhdl._Signal import _Signal, _WaiterList
from myhdl.conversion._toVHDLPackage import _package
# from myhdl._util import  _flatten
from myhdl._compat import integer_types, class_types, StringIO
from myhdl._ShadowSignal import _TristateSignal, _TristateDriver
from myhdl._misc import m1Dinfo
from myhdl._structured import Array, StructType
# from myhdl._ShadowSignal import ConcatSignal


from myhdl.tracejb import Tracing

trace = Tracing(False, source='_toVHDL')

_version = myhdl.__version__.replace('.', '')
_shortversion = _version.replace('dev', '')
_converting = 0
_profileFunc = None
_enumPortTypeSet = set()


def natural_key(string_):
    """
        a helper routine to 'improve' the sort
        See http://www.codinghorror.com/blog/archives/001018.html
    """
    return [int(s) if s.isdigit() else s for s in re.split(r'(\d+)', string_)]


def _checkArgs(arglist):
    for arg in arglist:
        if not isinstance(arg, (GeneratorType, _Instantiator, _UserVhdlCode)):
            raise ToVHDLError(_error.ArgType, arg)


def _flatten(*args):
    arglist = []
    for arg in args:
        trace.print(arg)
        if id(arg) in _userCodeMap['vhdl']:
            arglist.append(_userCodeMap['vhdl'][id(arg)])
        elif isinstance(arg, (list, tuple, set)):
            for item in arg:
                arglist.extend(_flatten(item))
        else:
            arglist.append(arg)
    return arglist


def _makeDoc(doc, indent=''):
    if doc is None:
        return ''
    doc = inspect.cleandoc(doc)
#     trace.print(doc)
    pre = '\n' + indent + '-- '
#     doc = '-- ' + doc
    doc = '\n' + doc
    doc = doc.replace('\n', pre)
    return doc


class _ToVHDLConvertor(object):

    __slots__ = ("name",
                 "standard",
                 "directory",
                 "component_declarations",
                 "header",
                 "no_myhdl_header",
                 "no_myhdl_package",
                 "library",
                 "use_clauses",
                 "architecture",
                 "std_logic_ports",
                 "no_initial_values"
                 )

    def __init__(self):
        self.name = None
        self.standard = '2008'
        self.directory = None
        self.component_declarations = None
        self.header = ''
        self.no_myhdl_header = False
        self.no_myhdl_package = True
        self.library = "work"
        self.use_clauses = None
        self.architecture = "MyHDL"
        self.std_logic_ports = False
        self.no_initial_values = False

    def __call__(self, func, *args, **kwargs):
        global _converting
        if _converting:
            #             trace.print('executing {}'.format(func))
            return func(*args, **kwargs)  # skip
        else:
            #             trace.print('clean start {}'.format(func))
            # clean start
            sys.setprofile(None)
        from myhdl import _traceSignals
        if _traceSignals._tracing:
            raise ToVHDLError("Cannot use toVHDL while tracing signals")
        if not callable(func):
            raise ToVHDLError(_error.FirstArgType, "got %s" % type(func))

        _converting = 1
        if self.name is None:
            name = func.__name__
        else:
            name = str(self.name)

        print('Calling toVHDL for {}'.format(name))

        # 1 Hierarchy
        try:
            h = _HierExtr(name, func, *args, **kwargs)
        finally:
            _converting = 0

        trace.push(message='h.hierarchy')
        for item in h.hierarchy:
            trace.print('\t', repr(item))
        trace.print()
        trace.pop()

#         trace.push(message='h.absnames')
#         for item in h.absnames:
#             trace.print('\t', item)
#         trace.print()
#         trace.pop()

        if self.directory is None:
            directory = ''
        else:
            directory = self.directory
        compDecls = self.component_declarations
        useClauses = self.use_clauses

        vpath = os.path.join(directory, name + ".vhd")
        tpath = os.path.join(directory, name + ".tmp")
        vfile = open(tpath, 'w')
        ppath = os.path.join(directory, "pck_myhdl_%s.vhd" % _shortversion)
        pfile = None
#        # write MyHDL package always during development, as it may change
#        pfile = None
#        if not os.path.isfile(ppath):
#            pfile = open(ppath, 'w')
        if not self.no_myhdl_package:
            pfile = open(ppath, 'w')

        ### initialise properly ###
        _genUniqueSuffix.reset()
        _enumTypeSet.clear()
        _enumPortTypeSet.clear()

        # 2 Analyse Generators
        arglist = _flatten(h.top)
        _checkArgs(arglist)
        genlist = _analyzeGens(arglist, h.absnames)
        trace.print('Analysed Generators')
        trace.print('genlist', genlist)

        # 3 analyse the signals
        siglist, memlist = _analyzeSigs(h.hierarchy, hdl='VHDL')
#         trace.print('siglist', siglist)
#         trace.print('memlist', memlist)
        trace.print('Analysed Signals')
        trace.print('siglist')
        for sig in siglist:
            trace.print('\t', repr(sig))
        trace.print('memlist')
        for mem in memlist:
            trace.print('\t', repr(mem))

        # 4 Annotate the types
        trace.push(None, message='_annotateTypes')
        _annotateTypes(genlist)
        trace.pop()

        # 5 infer interface
        top_inst = h.hierarchy[0]
        intf = _analyzeTopFunc(top_inst, func, *args, **kwargs)
        intf.name = name
        # sanity checks on interface
        for portname in intf.argnames:
            port = intf.argdict[portname]
            if isinstance(port, StructType):
                pass
            else:
                if port._name is None:
                    raise ToVHDLError(_error.ShadowingSignal, portname)
#             if port._inList:
#                 raise ToVHDLError(_error.PortInList, portname)
            # add enum types to port-related set
                if isinstance(port._val, EnumItemType):
                    obj = port._val._type
                    if obj in _enumTypeSet:
                        _enumTypeSet.remove(obj)
                        _enumPortTypeSet.add(obj)
                    else:
                        assert obj in _enumPortTypeSet

        doc = _makeDoc(inspect.getdoc(func))

        needPck = len(_enumPortTypeSet) > 0
        lib = self.library
        arch = self.architecture
        stdLogicPorts = self.std_logic_ports

        # anything to tidy up?
        self._convert_filter(h, intf, siglist, memlist, genlist)

        # write the MyHDL package, if required
        if pfile:
            _writeFileHeader(pfile, ppath)
            print(_package, file=pfile)
            pfile.close()

        # from here start writing to the output file
        _writeFileHeader(vfile, vpath)
        if needPck:
            _writeCustomPackage(vfile, intf)
        _writeModuleHeader(vfile, intf, needPck, lib, arch,
                           useClauses, doc, stdLogicPorts, siglist, self.standard)
        _writeTypeDefs(vfile, memlist)
        _writeFuncDecls(vfile)
        _writeConstants(vfile, memlist)
        _writeSigDecls(vfile, intf, siglist, memlist)
        _writeCompDecls(vfile, compDecls)
#         trace.print('genlist', genlist)
        # gthe converted 'generators'
        _convertGens(genlist, siglist, memlist, vfile)
        _writeModuleFooter(vfile, arch)

        vfile.close()
        # tbfile.close()

        # postedit the .vhd file
        dummyprefixes = [name + '_', name.lower() + '_']
#         trace.print(dummyprefixes)
#         if len( suppressedWarnings ) > 0:
        fi = open(tpath, 'r')
        fo = open(vpath, 'w')
        # edit ...
        # read the temporary VHDL file
        filines = fi.read().split('\n')
        # split into lines
        for line in filines:
            skip = False
            for sw in suppressedWarnings:
                if sw._name in line:
                    skip = True
                    break
            if not skip:
                # ideally should do this while giving the names
                #                 line = re.sub('\b{}\{}'.format(dummyprefixes[0], dummyprefixes[1]), '', line)
                for dp in dummyprefixes:
                    line = line.replace(dp, '')
                fo.write(line + '\n')

        # selectively write the lines to the output

        fi.close()
        os.remove(tpath)
        fo.close()
#         else:
#             if os.path.exists( vpath ):
#                 os.remove( vpath )
#             os.rename( tpath, vpath )

        ### clean-up properly ###
        self._cleanup(siglist)

        return h.top

    def _cleanup(self, siglist):
        # clean up signal names
        for sig in siglist:
            sig._clear()
#             sig._name = None
#             sig._driven = False
#             sig._read = False

        # clean up attributes
        self.name = None
        self.component_declarations = None
        self.header = ''
        self.no_myhdl_header = False
        self.no_myhdl_package = False
        self.architecture = "MyHDL"
        self.std_logic_ports = False

    def _convert_filter(self, h, intf, siglist, memlist, genlist):
        # intended to be a entry point for other uses:
        #  code checking, optimizations, etc
        pass
#         # print a lot
#         for l in (siglist, memlist, genlist):
#             print(str(l))
#             for item in l:
#                 print('\t', item)


# expose as global object
toVHDL = _ToVHDLConvertor()

myhdl_header = """\
-- File: $filename
-- Generated by MyHDL $version
-- BEWARE: peppered with Array, StructType,
--         advanced ShadowSignal functionality, and more
--         by Josy Boelen (josyb)
--
-- Date: $date
"""


def _writeFileHeader(f, fn):
    mvars = dict(filename=fn,
                 version=myhdl.__version__,
                 date=datetime.today().ctime()
                 )
    if toVHDL.header:
        print(string.Template(toVHDL.header).substitute(mvars), file=f)
    if not toVHDL.no_myhdl_header:
        print(string.Template(myhdl_header).substitute(mvars), file=f)
    print(file=f)


def _writeCustomPackage(f, intf):
    print(file=f)
    print("package pck_%s is" % intf.name, file=f)
    print(file=f)
    print("attribute enum_encoding: string;", file=f)
    print(file=f)
    sortedList = list(_enumPortTypeSet)
    sortedList.sort(key=lambda x: x._name)
    for t in sortedList:
        print("    %s" % t._toVHDL(), file=f)
    print(file=f)
    print("end package pck_%s;" % intf.name, file=f)
    print(file=f)


portConversions = []
suppressedWarnings = []
constantlist = []


def _writeModuleHeader(f, intf, needPck, lib, arch, useClauses, doc, stdLogicPorts, siglist, standard):
    print('-- synthesis VHDL_2008\n\n', file=f)
    print("library IEEE;", file=f)
    print("\tuse IEEE.std_logic_1164.all;", file=f)
    print("\tuse IEEE.numeric_std.all;", file=f)
    print("\tuse std.textio.all;", file=f)
    print(file=f)
    if lib != "work":
        print("library %s;" % lib, file=f)
    if useClauses is not None:
        f.write(useClauses)
        f.write("\n")
    else:
        print("\tuse %s.pck_myhdl_%s.all;" % (lib, _shortversion), file=f)
    print(file=f)
    if needPck:
        print("\tuse %s.pck_%s.all;" % (lib, intf.name), file=f)
        print(file=f)
    print("entity %s is" % intf.name, file=f)
    del portConversions[:]
    del suppressedWarnings[:]
    del constantlist[:]
    pl = []
    if intf.argnames:
        f.write("\tport (")
        for portname in intf.argnames:
            port = intf.argdict[portname]
            if isinstance(port, (StructType, Array)):
                trace.print(portname)
                # expand the structure
                # and add assignments
                # taking care of unsigned <> std_logic_vector conversions
                #                 expandStructType(c, stdLogicPorts, pl, portname, port)
                expandStructuredPort(stdLogicPorts, pl, portname, port)
            else:
                # must be a Signal
                # change name to convert to std_logic, or
                # make sure signal name is equal to its port name
                convertPort = False
                if stdLogicPorts and port._type is intbv:
                    port._name = portname + "_num"
                    convertPort = True
                    # 03-01-2016 expanding a StructType obj does miss out on
                    # some port signals
                    port._used = True
                    for sl in port._slicesigs:
                        sl._setName('VHDL')
                else:
                    port._name = portname

                r = _getRangeString(port)
                pt = st = _getTypeString(port)
                if convertPort:
                    pt = "std_logic_vector"
                    if port.driven:
                        pl.append("\n\t\t%s : out %s%s;" % (portname, pt, r))
                        portConversions.append(
                            "\t%s <= %s(%s);" % (portname, pt, port._name))
                        # mark corresponding signal as read
                        for s in siglist:
                            if s._name == port._name:
                                s._read = True
                                break
                    else:
                        if not port._read and not port._suppresswarning:
                            warnings.warn(
                                "%s: %s" % (_error.UnusedPort, portname), category=ToVHDLWarning)

                        pl.append("\n\t\t%s : in %s%s;" % (portname, pt, r))
                        if convertPort:
                            portConversions.append(
                                "\t%s <= %s(%s);" % (port._name, st, portname))
                            port.driven = True
                else:
                    if port._driven:
                        if port._read:
                            if standard == '2008':
                                pl.append("\n\t\t%s : out %s%s;" %
                                          (portname, pt, r))
                            else:
                                pl.append("\n\t\t%s : inout %s%s;" %
                                          (portname, pt, r))
                                if not isinstance(port, _TristateSignal):
                                    warnings.warn(
                                        "%s: %s" % (_error.OutputPortRead, portname), category=ToVHDLWarning)
                        else:
                            pl.append("\n\t\t%s : out %s%s;" %
                                      (portname, pt, r))
                        if convertPort:
                            portConversions.append(
                                "\t%s <= %s(%s);" % (portname, pt, port._name))
                            port._read = True
                    else:
                        if not port._read and not port._suppresswarning:
                            warnings.warn(
                                "%s: %s" % (_error.UnusedPort, portname), category=ToVHDLWarning)

                        pl.append("\n\t\t%s : in %s%s;" % (portname, pt, r))
                        if convertPort:
                            portConversions.append(
                                "\t%s <= %s(%s);" % (port._name, st, portname))
                            port._driven = True

        sl = sortalign(pl, sort=False, port=True)
        fsl = ''.join((sl))
        f.write(fsl[:-1])
        f.write("\n\t\t);\n")
    print("end entity %s;\n" % intf.name, file=f)
    print(doc, file=f)
    print(file=f)
    print("architecture %s of %s is" % (arch, intf.name), file=f)
    print(file=f)


def addStructuredPortEntry(stdLogicPorts, pl, portname, portsig):
    trace.print('addStructuredPortEntry', stdLogicPorts, pl, portname, portsig)
    r = _getRangeString(portsig)
    pt = st = _getTypeString(portsig)
    if stdLogicPorts:
        if isinstance(portsig._val, intbv):
            pt = 'std_logic_vector'
    if portsig._driven:
        if portsig.read:
            pl.append("\n\t\t%s : inout %s%s;" % (portname, pt, r))
            warnings.warn("%s: %s" % (_error.OutputPortRead, portname), category=ToVHDLWarning)
        else:
            pl.append("\n\t\t%s : out %s%s;" % (portname, pt, r))
        if isinstance(portsig._val, intbv):
            portConversions.append("\t%s <= %s(%s);" % (portname, pt, portsig._name))
        else:
            portConversions.append("\t%s <= %s;" % (portname, portsig._name))
        portsig._read = True
    elif portsig.read:
        pl.append("\n\t\t%s : in %s%s;" % (portname, pt, r))
        if isinstance(portsig._val, intbv):
            portConversions.append("\t%s <= %s(%s);" % (portsig._name, st, portname))
        else:
            portConversions.append("\t%s <= %s;" % (portsig._name, portname))
        portsig._driven = True
    else:
        # silently discard neither driven nor read members
        trace.print('neither driven nor read?')
        pass


def expandStructuredPort(stdLogicPorts, pl, name, obj):
    trace.print('expanding', name, repr(obj))
    if isinstance(obj, StructType):
        for attr, attrobj in vars(obj).items():
            if isinstance(attrobj, _Signal):
                addStructuredPortEntry(stdLogicPorts, pl, ''.join((name, attr)), attrobj)
            elif isinstance(attrobj, StructType):
                trace.print('Expanding', name, attr)
                expandStructuredPort(stdLogicPorts, pl, name + attr, attrobj)
            # else EnumItemType, int, str, ...
    elif isinstance(obj, Array):
        name += '_'
        if isinstance(obj[0], Array):
            # go down
            for i in len(obj):
                expandStructuredPort(stdLogicPorts, pl, name + str(i), obj[i])
        else:
            # lowest level of array
            if isinstance(obj.element, StructType):
                for i in len(obj):
                    expandStructuredPort(
                        stdLogicPorts, pl, name + str(i), obj[i])
            else:
                # Signal
                for i in len(obj):
                    addStructuredPortEntry(
                        stdLogicPorts, pl, ''.join((name, str(i))), obj[i])
        # not yet
        raise ToVHDLError("Don't do Arrays", obj)
        # need to add a type declaration to a package


def _writeFuncDecls(f):
    return


def _writeConstants(f, memlist):
    f.write("\n")
    cl = []

    for m in memlist:
        if not m._used:
            continue
        if m.driven or not m._read:
            continue
        # not driven, but _read
        # drill down into the list
        cl.append("    constant {} : {} := ( {} );\n" .format(
            m.name, m._typedef, expandconstant(m.mem)))
        constantlist.append(m.name)
    for l in sortalign(cl, sort=True):
        f.write(l)
    f.write("\n")


def expandconstant(c):
    if isinstance(c, StructType):
        pass
    elif isinstance(c[0], (list, Array)):
        size = c.shape[0] if isinstance(c, Array) else len(c)
        s = ''
        for i in range(size):
            s = ''.join((s, '(', expandconstant(c[i]), ')'))
            if i != size - 1:
                s = ''.join((s, ',\n'))
        return s
    else:
        # lowest (= last) level of m1D
        size = c.shape[0] if isinstance(c, Array) else len(c)
        s = ''
        if isinstance(c[0], StructType):
            pass
        elif isinstance(c[0]._val, bool):
            for i in range(size):
                s = ''.join((s, '{}, '.format('\'1\'' if c[i] else '\'0\'')))
        else:
            # intbv
            for i in range(size):
                s = ''.join((s, ' to_{}signed( {}, {} ){}'.format(
                    '' if c[i]._min < 0 else 'un', c[i], c[i]._nrbits, ', ')))
        return s[:-2]


def expandarray(c):
    if isinstance(c[0], (list, Array)):
        size = c.shape[0] if isinstance(c, Array) else len(c)
        s = ''
        for i in range(size):
            s = ''.join((s, '(', expandarray(c[i]), ')'))
            if i != size - 1:
                s = ''.join((s, ',\n'))
        return s
    else:
        # lowest (= last) level of m1D
        size = c.shape[0] if isinstance(c, Array) else len(c)
        s = ''
        if isinstance(c[0], StructType):
            for i in range(size):
                s = ''.join((s, '{}, '.format(c[i].initial())))
        elif isinstance(c[0]._val, bool):
            if size > 1:
                for i in range(size):
                    s = ''.join(
                        (s, '{}, '.format('\'1\'' if c[i]._val else '\'0\'')))
            else:
                s = ''.join((s, '{}, '.format('"1"' if c[0]._val else '"0"')))
        else:
            # intbv
            for i in range(size):
                if c[i]._val:
                    s = ''.join(
                        (s, 'b"{}", '.format(bin(c[i]._val, c[i]._nrbits, True))))
                else:
                    s = ''.join((s, '(others => \'0\'), '))

# TODO:  cut long lines

        # remove trailing ', '
        return s[:-2]


class _typedef(object):

    def __init__(self):
        self.names = []
        self.basetypes = []
        self.VHDLcodes = []

    def clear(self):
        self.names = []
        self.basetypes = []
        self.VHDLcodes = []

    def add(self, name, basetypes, VHDLcode):
        if name not in self.names:
            self.names.append(name)
            self.basetypes.append(basetypes)
            self.VHDLcodes.append(VHDLcode)

    def write(self, f):
        # first 'sort'
        nrtd = len(self.names)
        idx = 0
        while idx < nrtd:
            bt = self.basetypes[idx]
            if bt is not None:
                if bt in self.names[idx + 1:]:
                    btidx = self.names.index(bt)
                    self.names.insert(idx, self.names.pop(btidx))
                    self.basetypes.insert(idx, self.basetypes.pop(btidx))
                    self.VHDLcodes.insert(idx, self.VHDLcodes.pop(btidx))
                    # stay at this index and test whether this name now has a
                    # 'predecessor'
                else:
                    idx += 1

            else:
                idx += 1

        # then write
        for i, l in enumerate(self.VHDLcodes):
            f.write(l)


def addstructuredtypedef(obj):
    ''' adds the typedefs for a StructType
        possibly descending down
    '''
    basetype = None
    if isinstance(obj, StructType):
        refs = vars(obj)
        for key in refs:
            if isinstance(refs[key], (StructType, Array)):
                basetype = addstructuredtypedef(refs[key])
        # all lower structured types are now defined
#         rname = '\\' + obj.ref() + '\\'
        rname = obj.ref()
        lines = "\ttype {} is record\n".format(rname)
        # follow the sequencelist if any
        if hasattr(obj, 'sequencelist')and obj.sequencelist:
            refs = []
            for key in obj.sequencelist:
                if hasattr(obj, key):
                    refs.append(key)

        else:
            refs = vars(obj)

        entries = []
        for key in refs:
            mobj = vars(obj)[key]
            if isinstance(mobj, _Signal):
                entries.append(
                    "\t\t{} : {}{};\n".format(key, _getTypeString(mobj), _getRangeString(mobj)))
            elif isinstance(mobj, Array):
                #                 trace.print(mobj.ref())
                entries.append("\t\t{} : {};\n".format(key, mobj.ref()))  # ##
            elif isinstance(mobj, StructType):
                #                 entries.append( "        {} : \\{}\\;\n".format(key, mobj.ref()))
                entries.append("\t\t{} : {};\n".format(key, mobj.ref()))

        # align-format the contents
#         for line in sortalign(entries, sort=False):
#             lines += line
        lines += ''.join((sortalign(entries, sort=False)))
        lines += "\tend record ;\n\n"
        typedefs.add(rname, None, lines)
        basetype = rname

    elif isinstance(obj, Array):
        if isinstance(obj.element, StructType):
            p = basetype = addstructuredtypedef(obj.element)
        else:
            if isinstance(obj.element, _Signal):
                mobj = obj.element._val
            else:
                mobj = obj.element

            if isinstance(mobj, intbv):  # m.elObj._nrbits is not None:
                basetype = '{}{}'.format(
                    _getTypeString(obj.element)[0], obj.element._nrbits)
            elif isinstance(mobj, bool):  # mobj._type == bool :
                basetype = 'b'
            else:
                raise AssertionError
            p = '{}{}'.format(
                _getTypeString(obj.element), _getRangeString(obj.element))

        for _, size in enumerate(reversed(obj.shape)):
            o = basetype
            basetype = 'a{}_{}'.format(size, o)
            typedefs.add(
                basetype, o, "\ttype {} is array(0 to {}-1) of {};\n" .format(basetype, size, p))
            # next level if any
            p = basetype
    return basetype


def _writeTypeDefs(f, memlist):
    f.write("\n")
    # write the enums
    sortedList = list(_enumTypeSet)
    sortedList.sort(key=lambda x: x._name)
    enumused = []
    for t in sortedList:
        if t._name not in enumused:
            enumused.append(t._name)
            tt = "%s\n" % t._toVHDL()
            f.write(tt)
    f.write("\n")
    # then write the structured types
    for m in memlist:
        if not m._used or m.usagecount == 0:
            continue
        # infer attributes for the case of named signals in a list
        trace.print('inferring {:30} {:4} {:4} {}'.format(m.name, m._driven, m._read, repr(m.mem)))
        trace.push(message='inferattrs')
        inferattrs(m, m.mem)
        trace.pop()
        trace.print('\tinferred: driven: {:4} read: {:4}'.format(m._driven, m._read))
        if m.depth == 1 and isinstance(m.elObj, StructType):
                # a 'single' StructType
            basetype = addstructuredtypedef(m.elObj)
        elif isinstance(m.mem, Array):
            basetype = addstructuredtypedef(m.mem)

        else:
            # it is a (multi-dimensional) list
            if isinstance(m.elObj, StructType):
                p = basetype = m.elObj.ref()
            elif isinstance(m.elObj, Array):
                p = basetype = m.elObj.ref()
            else:
                if isinstance(m.elObj, _Signal):
                    mobj = m.elObj._val
                else:
                    mobj = m.elObj

                if isinstance(mobj, intbv):  # m.elObj._nrbits is not None:
                    basetype = '{}{}'.format(
                        _getTypeString(m.elObj)[0], m.elObj._nrbits)
                elif isinstance(mobj, bool):  # mobj._type == bool :
                    basetype = 'b'
                else:
                    raise AssertionError
                p = '{}{}'.format(_getTypeString(m.elObj), _getRangeString(m.elObj))

            for _, size in enumerate(reversed(m._sizes)):
                o = basetype
                basetype = 'a{}_{}'.format(size, o)
                typedefs.add(basetype, o, "    type {} is array(0 to {}-1) of {};\n" .format(basetype, size, p))
                # next level if any
                p = basetype

        m._typedef = basetype

    typedefs.write(f)
    f.write("\n")


constwires = []
typedefs = _typedef()
functiondefs = []


def _writeSigDecls(f, intf, siglist, memlist):
    del constwires[:]
    typedefs.clear()
    del functiondefs[:]
    sl = []
    for s in siglist:
        if s._name in intf.argnames:
            continue

        if not s._used:
            continue

        r = _getRangeString(s)
        p = _getTypeString(s)
        if s._driven or s._read:
            if not toVHDL.no_initial_values:
                if isinstance(s._val, bool):
                    sl.append("    signal %s : %s%s := '%s';" %
                              (s._name, p, r, 1 if s._val else 0))
                elif isinstance(s._val, intbv):
                    if s._val:
                        sl.append("    signal %s : %s%s := b\"%s\";" %
                                  (s._name, p, r, bin(s._val, s._nrbits, True)))
                    else:
                        # all zeros
                        sl.append(
                            "    signal %s : %s%s := (others => '0');" % (s._name, p, r))
                elif isinstance(s._val, EnumItemType):
                    sl.append("    signal %s : %s%s := %s;" %
                              (s._name, p, r, s._val))
            else:
                sl.append("    signal %s : %s%s;" % (s._name, p, r))

            if s._driven:
                if not s._read and not isinstance(s, _TristateDriver):
                    if not s._suppresswarning:
                        warnings.warn(
                            "%s: %s" % (_error.UnreadSignal, s._name), category=ToVHDLWarning)
                    else:
                        suppressedWarnings.append(s)

            elif s._read:
                warnings.warn(
                    "%s: %s" % (_error.UndrivenSignal, s._name), category=ToVHDLWarning)
                constwires.append(s)

        else:
            pass

    trace.print('_writeSigDecls', memlist)
    for m in memlist:
        if not m._used or m.usagecount == 0:
            continue

        if not m.driven:
            continue

        if not m._read:
            continue

        # left to process
        if isinstance(m.mem, Array):
            if m.mem._initialised or not toVHDL.no_initial_values:
                sl.append("    signal {} : {} := ({});" .format(
                    m.name, m._typedef, expandarray(m.mem)))
            else:
                sl.append("    signal {} : {};" .format(m.name, m._typedef))
        elif isinstance(m.mem, list):
            # assuming it is is a single list
            # try to shortcut the initialisation
            #             tval = m.mem[0]
            #             for i, sig in enumerate(m.mem):
            #                 if sig._val != tval:
            #                     break
            #             if i == len(m.mem) - 1:
            #                 if tval._min < 0:
            #                     rval =  'to_signed( {}, {} )'.format( tval._val, tval._nrbits)
            #                 else :
            #                     rval =  'to_unsigned( {}, {} )'.format( tval._val, tval._nrbits)
            #
            #                 sl.append("    signal {} : {} := (others => {});" .format(m.name, m._typedef, rval))
            #             else:
                # the full works
            if not toVHDL.no_initial_values:
                sl.append("    signal {} : {} := ({});" .format(
                    m.name, m._typedef, expandarray(m.mem)))
            else:
                sl.append("    signal {} : {};" .format(m.name, m._typedef))

        elif isinstance(m.mem, StructType):
            if not toVHDL.no_initial_values:
                sl.append("    signal {} : {} := ({});" .format(
                    m.name, m._typedef, m.mem.initial('vhdl')))
            else:
                sl.append("    signal {} : {};" .format(m.name, m._typedef))
        else:
            pass

    for l in sortalign(sl, sort=True):
        print(l, file=f)
    print(file=f)


def sortalign(sl, sort=False, port=False):

    # align the colons
    maxpos = 0
    for l in sl:
        if ':' in l:
            t = l.find(':')
            maxpos = t if t > maxpos else maxpos

    if maxpos:
        for i, l in enumerate(sl):
            if ':' in l:
                p = l.find(':')
                b, c, e = l.partition(':')
                sl[i] = b + ' ' * (maxpos - p) + c + e

    # align after 'in', 'out' or 'inout'
    if port:
        portdirections = (': in', ': out', ': inout')
        maxpos = 0
        for l in sl:
            for tst in portdirections:
                if tst in l:
                    t = l.find(tst) + len(tst)
                    maxpos = t if t > maxpos else maxpos
                    continue
        if maxpos:
            for i, l in enumerate(sl):
                for tst in portdirections:
                    if tst in l:
                        p = l.find(tst)
                        b, c, e = l.partition(tst)
                        sl[i] = b + c + ' ' * (maxpos - p - len(tst)) + e

    # align then :=' if any
    maxpos = 0
    for l in sl:
        if ':=' in l:
            t = l.find(':=')
            maxpos = t if t > maxpos else maxpos
    if maxpos:
        for i, l in enumerate(sl):
            if ':=' in l:
                p = l.find(':=')
                b, c, e = l.partition(':=')
                sl[i] = b + ' ' * (maxpos - p) + c + e

    if sort:
        # sort the signals
        return sorted(sl, key=natural_key)
    else:
        return sl


def inferattrs(m, mem, level=0):
    trace.print('{} {} {}'.format(level, m, mem))
    level += 1
    if isinstance(mem, StructType):
        refs = vars(mem)
        for k in refs:
            s = refs[k]
            if isinstance(s, _Signal):
                if not m._driven and s._driven:
                    m._driven = s._driven
                if not m._read and s._read:
                    m._read = s._read
            elif isinstance(s, (Array, StructType)):
                # it may be another StructType
                # or an Array
                inferattrs(m, s, level)
            else:
                pass

    elif isinstance(mem[0], (list, Array)):
        for mmm in mem:
            #             trace.print(m, mmm, level)
            inferattrs(m, mmm, level)

    else:
        # lowest (= last) level of m1D
        #         trace.print(repr(m), hasattr(m, 'driven'))
        for s in mem:
            #             trace.print('\t', repr(s), hasattr(s, 'driven'), s.driven)
            if hasattr(m, 'driven') and hasattr(s, 'driven'):
                if not m.driven and s.driven:
                    m._driven = s.driven
                if not m._read and s._read:
                    m._read = s._read
                trace.print('{} testing {} driven: {} read: {} -> {} {}'.format('\t' * level, s, s.driven, s._read, m.driven, m._read))


def _writeCompDecls(f, compDecls):
    if compDecls is not None:
        print(compDecls, file=f)


def _writeModuleFooter(f, arch):
    print("\nend architecture %s;" % arch, file=f)


def _getRangeString(s):
    if isinstance(s, _Signal):
        if isinstance(s._val, EnumItemType):
            return ''
        elif s._type is bool:
            return ''
        elif s._nrbits is not None:
            ls = getattr(s, 'lenStr', False)
            if ls:
                msb = ls + '-1'
            else:
                msb = s._nrbits - 1
            return "(%s downto 0)" % msb
        else:
            raise AssertionError
    elif isinstance(s, intbv):
        if s._nrbits is not None:
            ls = getattr(s, 'lenStr', False)
            if ls:
                msb = ls + '-1'
            else:
                msb = s._nrbits - 1
            return "(%s downto 0)" % msb
        else:
            raise AssertionError


def _getTypeString(s):
    if isinstance(s, StructType):
        #         r = s.__class__.__name__
        r = s.ref()

    elif isinstance(s, _Signal):
        if isinstance(s._val, EnumItemType):
            r = s._val._type._name
        elif s._type is bool:
            r = "std_logic"
        else:
            if s._min is not None and s._min < 0:
                r = "signed"
            else:
                r = 'unsigned'
    elif isinstance(s, intbv):
        if s._min is not None and s._min < 0:
            r = "signed"
        else:
            r = 'unsigned'

    return r


def _convertGens(genlist, siglist, memlist, vfile):
    trace.push(message='_convertGens')
    blockBuf = StringIO()
    funcBuf = StringIO()
    for tree in genlist:
        if isinstance(tree, _UserVhdlCode):
            blockBuf.write(str(tree))
            continue
        if tree.kind == _kind.ALWAYS:
            trace.push(message='_ConvertAlwaysVisitor')
            Visitor = _ConvertAlwaysVisitor
        elif tree.kind == _kind.INITIAL:
            trace.push(message='_ConvertInitialVisitor')
            Visitor = _ConvertInitialVisitor
        elif tree.kind == _kind.SIMPLE_ALWAYS_COMB:
            trace.push(message='_ConvertSimpleAlwaysCombVisitor')
            Visitor = _ConvertSimpleAlwaysCombVisitor
        elif tree.kind == _kind.ALWAYS_DECO:
            trace.push(message='_ConvertAlwaysDecoVisitor')
            Visitor = _ConvertAlwaysDecoVisitor
        elif tree.kind == _kind.ALWAYS_SEQ:
            trace.push(message='_ConvertAlwaysSeqVisitor')
            Visitor = _ConvertAlwaysSeqVisitor
        else:  # ALWAYS_COMB
            trace.push(message='_ConvertAlwaysCombVisitor')
            Visitor = _ConvertAlwaysCombVisitor
        v = Visitor(tree, blockBuf, funcBuf)
        v.visit(tree)
        trace.pop()

    vfile.write(funcBuf.getvalue())
    funcBuf.close()
    print("begin", file=vfile)
    print(file=vfile)
    for st in portConversions:
        print(st, file=vfile)
    print(file=vfile)
    for s in constwires:
        if s._type is bool:
            c = int(s._val)
            pre, suf = "'", "'"
        elif s._type is intbv:
            c = int(s._val)
            w = len(s)
            assert w != 0
            if s._min < 0:
                pre, suf = "to_signed(", ", %s)" % w
            else:
                pre, suf = "to_unsigned(", ", %s)" % w
        else:
            raise ToVHDLError("Unexpected type for constant signal", s._name)
        print("%s <= %s%s%s;" % (s._name, pre, c, suf), file=vfile)
    print(file=vfile)
    # shadow signal assignments
    for s in siglist:
        #         trace.print(s._name, repr(s), s)
        if hasattr(s, 'toVHDL'):
            if s._read:
                if s._name is None:
                    trace.print('signal target name missing for {}'.format(repr(s)))
#                 if isinstance(s, ConcatSignal):
#                     trace.print('_convertGens is ConcatSignal: ', repr(s))
#                     r = '    {} <= ({});'.format(s._name, s.elements('VHDL'))
#                 else:
#                     r = s.toVHDL()
                r = s.toVHDL()
                print(r, file=vfile)
#             else:
#                 trace.print('not read', repr(s))
    # hack for shadow-signals in a list etc
    for m in memlist:
        #         if isinstance(m.mem, (Array, StructType)):
        #             if m.mem.isshadow:
        #                 trace.print(m.mem._name)
        if m._read:
            if isinstance(m.mem, Array):
                trace.print('_convertGens, Array', m.mem._name, m.mem, m.mem.isshadow)
                if m.mem.isshadow:
                    r = '\n'.join(m.mem.toVHDL())
                    print(r, file=vfile)
            elif isinstance(m.mem, StructType):
                trace.print('_convertGens, StructType', m.mem._name, m.mem, m.mem.isshadow)
                if m.mem.isshadow:
                    r = '\n'.join(m.mem.toVHDL())
                    print(r, file=vfile)
            else:
                # a list
                # possibly of Array or StructType !
                trace.print(m.mem)
                for s in m.mem:
                    trace.print(s)
                    if isinstance(s, (Array, StructType)):
                        if s.isshadow:
                            r = '\n'.join(s.toVHDL())
                            print(r, file=vfile)
                    else:
                        if hasattr(s, 'toVHDL'):
                            #                         trace.print('toVHDL hasattr', repr(s))
                            r = s.toVHDL()
                            print(r, file=vfile)
    print(file=vfile)
    vfile.write(blockBuf.getvalue())
    blockBuf.close()
    trace.pop()


opmap = {
    ast.Add: '+',
    ast.Sub: '-',
    ast.Mult: '*',
    ast.Div: '/',
    ast.Mod: 'mod',
    ast.Pow: '**',
    ast.LShift: 'shift_left',
    ast.RShift: 'shift_right',
    ast.BitOr: 'or',
    ast.BitAnd: 'and',
    ast.BitXor: 'xor',
    ast.FloorDiv: '/',
    ast.Invert: 'not ',
    ast.Not: 'not ',
    ast.UAdd: '+',
    ast.USub: '-',
    ast.Eq: '=',
    ast.Gt: '>',
    ast.GtE: '>=',
    ast.Lt: '<',
    ast.LtE: '<=',
    ast.NotEq: '/=',
    ast.And: 'and',
    ast.Or: 'or',
}


class _ConvertVisitor(ast.NodeVisitor, _ConversionMixin):

    def __init__(self, tree, buf):
        #         trace.print( '_ConvertVisitor', tree.name)
        #         trace.print('\n_ConvertVisitor {}'.format(tree))
        self.tree = tree
        self.buf = buf
        self.returnLabel = tree.name
        self.ind = '    '
        self.SigAss = False
        self.isLhs = False
        self.labelStack = []
        self.context = None
        self.astinfo = None
        self.line = ''
        self.funcBuf = None

    def write(self, arg):
        self.buf.write("%s" % arg)
        self.line += "%s" % arg

    def writeline(self, nr=1):
        for _ in range(nr):
            self.buf.write("\n")
        self.buf.write("%s" % self.ind)
        self.line = "%s" % self.ind

    def writeDoc(self, node):
        assert hasattr(node, 'doc')
        doc = _makeDoc(node.doc, self.ind)
        trace.print('<', doc, '>')
        self.write(doc)
        self.writeline()

    def IntRepr(self, obj):
        if obj >= 0:
            s = "%s" % int(obj)
        else:
            s = "(- %s)" % abs(int(obj))
        return s

    def BitRepr(self, item, var):
        return 'b"%s"' % bin(item, len(var), True)

    def inferCast(self, vhd, ori):
        trace.print('inferCast', repr(vhd), repr(ori),)
        pre, suf = "", ""
        if isinstance(vhd, vhd_int):
            if isinstance(ori, vhd_array):
                pass
            elif not isinstance(ori, vhd_int):
                pre, suf = "to_integer(", ")"
        elif isinstance(vhd, vhd_unsigned):
            if isinstance(ori, vhd_unsigned):
                if vhd.size != ori.size:
                    pre, suf = "resize(", ", %s)" % vhd.size
            elif isinstance(ori, vhd_signed):
                if vhd.size != ori.size:
                    # note the order of resizing and casting here (otherwise
                    # bug!)
                    pre, suf = "resize(unsigned(", "), %s)" % vhd.size
                else:
                    pre, suf = "unsigned(", ")"
            elif isinstance(ori, vhd_array):
                pass
            else:
                #                 trace.print('?')
                pre, suf = "to_unsigned(", ", %s)" % vhd.size
        elif isinstance(vhd, vhd_signed):
            if isinstance(ori, vhd_signed):
                if vhd.size != ori.size:
                    pre, suf = "resize(", ", %s)" % vhd.size
            elif isinstance(ori, vhd_unsigned):
                if vhd.size != ori.size:
                    # I think this should be the order of resizing and casting
                    # here
                    pre, suf = "signed(resize(", ", %s))" % vhd.size
                else:
                    pre, suf = "signed(", ")"
            elif isinstance(ori, vhd_array):
                #                 trace.print('inferCast: vhd_array', vhd, ori)
                pass
            else:
                pre, suf = "to_signed(", ", %s)" % vhd.size
        elif isinstance(vhd, vhd_boolean):
            if not isinstance(ori, vhd_boolean):
                pre, suf = "bool(", ")"
# pre, suf = "(", " = '1')" # purer VHDL? but fails several 'conversion
# tests'
        elif isinstance(vhd, vhd_std_logic):
            if not isinstance(ori, vhd_std_logic):
                if isinstance(ori, vhd_unsigned):
                    pre, suf = "", "(0)"
                else:
                    pre, suf = "stdl(", ")"
        elif isinstance(vhd, vhd_string):
            if isinstance(ori, vhd_enum):
                pre, suf = "%s'image(" % ori._type._name, ")"
        elif isinstance(vhd, vhd_enum):
            if not isinstance(ori, vhd_enum):
                pre, suf = "%s'pos(" % vhd._type._name, ")"
        elif isinstance(vhd, vhd_array):
            trace.print('vhd_array', repr(vhd))
            if isinstance(vhd.vhdtype, vhd_unsigned):
                pass
            elif isinstance(vhd.vhdtype, vhd_signed):
                pass
            pass
#             if isinstance(ori, vhd_array):
#                 # may have to do some casting ...
#                 trace.print('may have to so some casting ...', ori, vhd)
#                 pass
#             else:
#                 trace.print('may have to so some extra casting ...', ori, vhd)

        trace.print(pre, suf)
        return pre, suf

    def writeIntSize(self, n):
        # write size for large integers (beyond 32 bits signed)
        # with some safety margin
        if n >= 2 ** 30:
            size = int(math.ceil(math.log(n + 1, 2))) + 1  # sign bit!
            self.write("%s'sd" % size)

    def writeDeclaration(self, obj, name, kind="", dir="", endchar=";", constr=True):
        if isinstance(obj, EnumItemType):
            tipe = obj._type._name

        elif isinstance(obj, _Ram):
            tipe = "t_array_%s" % name
            elt = inferVhdlObj(obj.elObj).toStr(True)
            self.write("type %s is array(0 to %s-1) of %s;" %
                       (tipe, obj.depth, elt))
            self.writeline()

        elif isinstance(obj, Array):
            # make the type
            #             if isinstance(obj.element, bool) :
            #                 basetype = 'b'
            #             elif obj.element._nrbits is not None:
            #                 basetype = '{}{}'.format(_getTypeString(obj.element)[0],  obj.element._nrbits)
            #             else:
            #                 raise AssertionError
            p = '{}{}'.format(
                _getTypeString(obj.element), _getRangeString(obj.element))
            if isinstance(obj.element, bool):
                basetype = 'b'
            elif obj.element._nrbits is not None:
                basetype = '{}{}'.format(
                    _getTypeString(obj.element)[0], obj.element._nrbits)
            else:
                raise AssertionError

            for _, size in enumerate(reversed(obj.shape)):
                o = basetype
                basetype = 'a{}_{}'.format(size, 0)
#                 if basetype not in typedefs:
#                     self.write("type {} is array(0 to {}-1) of {};" .format(basetype, size, p))
                typedefs.add(
                    basetype, basetype, "type {} is array(0 to {}-1) of {};" .format(basetype, size, p))
                # next level if any
                p = basetype
            tipe = basetype

        else:
            vhd = inferVhdlObj(obj)
            if isinstance(vhd, vhd_enum):
                tipe = obj._val._type._name
            else:
                tipe = vhd.toStr(constr)

        if kind:
            kind += " "
        if dir:
            dir += " "
        self.write("%s%s: %s%s%s" % (kind, name, dir, tipe, endchar))

    def writeDeclarations(self):
        if self.tree.hasPrint:
            self.writeline()
            self.write("variable L: line;")
        for name, obj in self.tree.vardict.items():
            if isinstance(obj, _loopInt):
                continue  # hack for loop vars
            self.writeline()
            self.writeDeclaration(obj, name, kind="variable")

    def indent(self):
        self.ind += ' ' * 4

    def dedent(self):
        self.ind = self.ind[:-4]

    def visit_BinOp(self, node):
        trace.push(message='visit_BinOp')
        trace.print(node)
        if isinstance(node.op, (ast.LShift, ast.RShift)):
            self.shiftOp(node)
        elif isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            #             if isinstance(node.op, ast.BitXor):
                #                 trace = True
            #                 trace.print('visit_BinOp', node.left, node.right)
            self.BitOp(node)
        elif isinstance(node.op, ast.Mod) and (self.context == _context.PRINT):
            self.visit(node.left)
            self.write(", ")
            self.visit(node.right)
        else:
            self.BinOp(node)
        trace.pop()

    def inferBinaryOpCast(self, node, left, right, op):
        ns, os = node.vhd.size, node.vhdOri.size
        trace.print(node, ns, os)
        ds = ns - os
        if ds > 0:
            if isinstance(left.vhd, vhd_vector) and isinstance(right.vhd, vhd_vector):
                if isinstance(op, (ast.Add, ast.Sub)):
                    left.vhd.size = ns
                    # in general, resize right also
                    # for a simple name, resizing is not necessary
                    if not isinstance(right, ast.Name):
                        right.vhd.size = ns
                    node.vhdOri.size = ns
                elif isinstance(op, ast.Mod):
                    right.vhd.size = ns
                    node.vhdOri.size = ns
                elif isinstance(op, ast.FloorDiv):
                    left.vhd.size = ns
                    node.vhdOri.size = ns
                elif isinstance(op, ast.Mult):
                    left.vhd.size += ds
                    node.vhdOri.size = ns
                else:
                    raise AssertionError("unexpected op %s" % op)
            elif isinstance(left.vhd, vhd_vector) and isinstance(right.vhd, vhd_int):
                if isinstance(op, (ast.Add, ast.Sub, ast.Mod, ast.FloorDiv)):
                    left.vhd.size = ns
                    node.vhdOri.size = ns
                elif isinstance(op, ast.Mult):
                    left.vhd.size += ds
                    node.vhdOri.size = 2 * left.vhd.size
                else:
                    raise AssertionError("unexpected op %s" % op)
            elif isinstance(left.vhd, vhd_int) and isinstance(right.vhd, vhd_vector):
                if isinstance(op, (ast.Add, ast.Sub, ast.Mod, ast.FloorDiv)):
                    right.vhd.size = ns
                    node.vhdOri.size = ns
                elif isinstance(op, ast.Mult):
                    node.vhdOri.size = 2 * right.vhd.size
                else:
                    raise AssertionError("unexpected op %s" % op)
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        if pre == "":
            pre, suf = "(", ")"
        return pre, suf

    def BinOp(self, node):
        trace.push(message='BinOp')
        trace.print(node)
        #         trace.print('BinOp', node.op, node.left, node.right)
        if isinstance(node.left.vhd, vhd_array) or isinstance(node.right.vhd, vhd_array):
            operator = '&'
        else:
            operator = opmap[type(node.op)]
        pre, suf = self.inferBinaryOpCast(node, node.left, node.right, node.op)
        self.write(pre)
        self.visit(node.left)
        self.write(" %s " % operator)
        self.visit(node.right)
        self.write(suf)
        trace.pop()

    def inferShiftOpCast(self, node, left, right, op):
        ns, os = node.vhd.size, node.vhdOri.size
        ds = ns - os
        if ds > 0:
            if isinstance(node.left.vhd, vhd_vector):
                left.vhd.size = ns
                node.vhdOri.size = ns
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        return pre, suf

    def shiftOp(self, node):
        pre, suf = self.inferShiftOpCast(node, node.left, node.right, node.op)
        self.write(pre)
        self.write("%s(" % opmap[type(node.op)])
        self.visit(node.left)
        self.write(", ")
        self.visit(node.right)
        self.write(")")
        self.write(suf)

    def BitOp(self, node):
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        self.write(pre)
        self.write("(")
        self.visit(node.left)
        self.write(" %s " % opmap[type(node.op)])
        self.visit(node.right)
        self.write(")")
        self.write(suf)

    def visit_BoolOp(self, node):
        if isinstance(node.vhd, vhd_std_logic):
            self.write("stdl")
        self.write("(")
        self.visit(node.values[0])
        for n in node.values[1:]:
            self.write(" %s " % opmap[type(node.op)])
            self.visit(n)
        self.write(")")

    def visit_UnaryOp(self, node):

        # in python3 a negative Num is represented as an USub of a positive Num
        # Fix: restore python2 behavior by a shortcut: invert value of Num, inherit
        # vhdl type from UnaryOp node, and visit the modified operand
        if isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Num):
            node.operand.n = -node.operand.n
            node.operand.vhd = node.vhd
            self.visit(node.operand)
            return

        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        self.write(pre)
        self.write("(")
        self.write(opmap[type(node.op)])
        self.visit(node.operand)
        self.write(")")
        self.write(suf)

    def visit_Attribute(self, node):
        trace.push(message='visit_Attribute')
        trace.print('{}'.format(node))
        if isinstance(node.ctx, ast.Store):
            self.setAttr(node)
        else:
            self.getAttr(node)
        if node.attr in ('next', 'posedge', 'negedge'):
            pass
        else:
            trace.print('? {}'.format(node.attr))
            if not isinstance(node.value.obj, EnumType):
                if hasattr(node.value, 'id'):
                    self.write('{}.{}'.format(node.value.id, node.attr))
                else:
                    self.write('.{}'.format(node.attr))
        trace.pop()

    def setAttr(self, node):
        self.SigAss = True
        if isinstance(node.value, ast.Subscript):
            self.SigAss = 'Killroy'
            self.visit(node.value)

        else:
            assert node.attr == 'next'
            if isinstance(node.value, ast.Name):
                sig = self.tree.symdict[node.value.id]
                if hasattr(sig, '_name'):
                    self.SigAss = sig._name
            self.visit(node.value)
            node.obj = self.getObj(node.value)

    def getAttr(self, node):
        if isinstance(node.value, ast.Subscript):
            self.setAttr(node)
            return

        if isinstance(node.value, ast.Attribute):
            self.visit(node.value)
        else:
            assert isinstance(node.value, ast.Name), node.value
            n = node.value.id
            if n in self.tree.symdict:
                obj = self.tree.symdict[n]
            elif n in self.tree.vardict:
                obj = self.tree.vardict[n]
            else:
                raise AssertionError("object not found")

            if isinstance(obj, _Signal):
                if node.attr == 'next':
                    sig = self.tree.symdict[node.value.id]
                    self.SigAss = obj._name
                    self.visit(node.value)
                elif node.attr == 'posedge':
                    self.write("rising_edge(")
                    self.visit(node.value)
                    self.write(")")
                elif node.attr == 'negedge':
                    self.write("falling_edge(")
                    self.visit(node.value)
                    self.write(")")
                elif node.attr == 'val':
                    pre, suf = self.inferCast(node.vhd, node.vhdOri)
                    self.write(pre)
                    self.visit(node.value)
                    self.write(suf)

            elif isinstance(obj, StructType):
                #                 trace.print('getAttr, skipping StructType')
                pass

            if isinstance(obj, (_Signal, intbv)):
                if node.attr in ('min', 'max'):
                    self.write("%s" % node.obj)

            if isinstance(obj, EnumType):
                assert hasattr(obj, node.attr)
                e = getattr(obj, node.attr)
                self.write(e._toVHDL())

    def visit_Assert(self, node):
        # XXX
        self.write("assert ")
        self.visit(node.test)
        self.indent()
        self.writeline()
        self.write('report "*** AssertionError ***"')
        self.writeline()
        self.write("severity error;")
        self.dedent()

    def visit_Assign(self, node):
        trace.push(message='visit_Assign')
        lhs = node.targets[0]
        rhs = node.value
        self.context = _context.ASSIGNMENT

        # shortcut for expansion of ROM in case statement
        if isinstance(node.value, ast.Subscript) and \
                isinstance(node.value.slice, ast.Index) and \
                isinstance(node.value.value.obj, _Rom):
            rom = node.value.value.obj.rom
            self.write("case ")
            self.visit(node.value.slice)
            self.write(" is")
            self.indent()
            size = lhs.vhd.size
            for i, n in enumerate(rom):
                self.writeline()
                if i == len(rom) - 1:
                    self.write("when others => ")
                else:
                    self.write("when %s => " % i)
                self.visit(lhs)
                if self.SigAss:
                    self.write(' <= ')
                    self.SigAss = False
                else:
                    self.write(' := ')
                if isinstance(lhs.vhd, vhd_std_logic):
                    self.write("'%s';" % n)
                elif isinstance(lhs.vhd, vhd_int):
                    self.write("%s;" % n)
                else:
                    self.write('b"%s";' % bin(n, size, True))
            self.dedent()
            self.writeline()
            self.write("end case;")
            trace.pop()
            return

        elif isinstance(node.value, ast.ListComp):
            # skip list comprehension assigns for now
            trace.pop()
            return

        # default behavior
        convOpen, convClose = "", ""
        if isinstance(lhs.vhd, vhd_type):
            rhs.vhd = lhs.vhd
        self.isLhs = True
#         trace.push(message='visit_Assign visit(lhs)')
        self.visit(lhs)
#         trace.pop()
        self.isLhs = False
#         trace.push(message='assign')
        if self.SigAss:
            if isinstance(lhs.value, ast.Name):
                sig = self.tree.symdict[lhs.value.id]
                trace.print('sig', sig)
            self.write(' <= ')
            self.SigAss = False
        else:
            self.write(' := ')
#         trace.pop()
        self.write(convOpen)
        # node.expr.target = obj = self.getObj(node.nodes[0])
#         trace.push(message='visit_Assign visit(rhs)')
        trace.print('rhs', rhs)
        self.visit(rhs)
#         trace.pop()
        self.write(convClose)
        self.write(';')
        self.context = None
        trace.pop()

    def visit_AugAssign(self, node):
        # XXX apparently no signed context required for augmented assigns
        left, op, right = node.target, node.op, node.value
        isFunc = False
        pre, suf = "", ""
        if isinstance(op, (ast.Add, ast.Sub, ast.Mult, ast.Mod, ast.FloorDiv)):
            pre, suf = self.inferBinaryOpCast(node, left, right, op)
        elif isinstance(op, (ast.LShift, ast.RShift)):
            isFunc = True
            pre, suf = self.inferShiftOpCast(node, left, right, op)
        self.visit(left)
        self.write(" := ")
        self.write(pre)
        if isFunc:
            self.write("%s(" % opmap[type(op)])
        self.visit(left)
        if isFunc:
            self.write(", ")
        else:
            self.write(" %s " % opmap[type(op)])
        self.visit(right)
        if isFunc:
            self.write(")")
        self.write(suf)
        self.write(";")

    def visit_Break(self, node):
        self.write("exit;")

    def visit_Call(self, node):
        trace.push(message='visit_Call')
        fn = node.func
        # assert isinstance(fn, astNode.Name)
        f = self.getObj(fn)
        if f is print:
            self.visit_Print(node)
            trace.pop()
            return

        fname = ''
        pre, suf = '', ''
        opening, closing = '(', ')'
        sep = ", "
        if f is bool:
            opening, closing = '', ''
            arg = node.args[0]
            arg.vhd = node.vhd
        elif f is len:
            val = self.getVal(node)
            self.require(node, val is not None, "cannot calculate len")
            self.write(repr(val))
            trace.pop()
            return

        elif f is now:
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            self.write(pre)
            self.write("(now / 1 ns)")
            self.write(suf)
            trace.pop()
            return

        elif f is ord:
            opening, closing = '', ''
            if isinstance(node.args[0], ast.Str):
                if len(node.args[0].s) > 1:
                    self.raiseError(
                        node, _error.UnsupportedType, "Strings with length > 1")
                else:
                    node.args[0].s = ord(node.args[0].s)
        elif f in integer_types:
            opening, closing = '', ''
            # convert number argument to integer
            if isinstance(node.args[0], ast.Num):
                node.args[0].n = int(node.args[0].n)
        elif inspect.isclass(f) and issubclass(f, intbv):
            pre, post = "", ""
            arg = node.args[0]
            if isinstance(node.vhd, vhd_unsigned):
                pre, post = "to_unsigned(", ", %s)" % node.vhd.size
            elif isinstance(node.vhd, vhd_signed):
                pre, post = "to_signed(", ", %s)" % node.vhd.size
            self.write(pre)
            self.visit(arg)
            self.write(post)
            trace.pop()
            return

        elif f == intbv.signed:  # note equality comparison
            # this call comes from a getattr
            arg = fn.value
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            opening, closing = '', ''
            if isinstance(arg.vhd, vhd_unsigned):
                opening, closing = "signed(", ")"
            self.write(pre)
            self.write(opening)
            self.visit(arg)
            self.write(closing)
            self.write(suf)
            trace.pop()
            return

        elif f == intbv.unsigned:
            arg = fn.value
#             pre, suf = self.inferCast(node.vhd, node.vhdOri)
            opening, closing = '', ''
            if isinstance(arg.vhd, vhd_signed):
                opening, closing = "unsigned(", ")"
            self.write(pre)
            self.write(opening)
            self.visit(arg)
            self.write(closing)
            self.write(suf)
            trace.pop()
            return

        elif (type(f) in class_types) and issubclass(f, Exception):
            self.write(f.__name__)
        elif f in (posedge, negedge):
            opening, closing = ' ', ''
            self.write(f.__name__)
        elif f is delay:
            self.visit(node.args[0])
            self.write(" * 1 ns")
            trace.pop()
            return

        elif f is concat:
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            opening, closing = "unsigned'(", ")"
            sep = " & "
        elif hasattr(node, 'tree'):
            pre, suf = self.inferCast(node.vhd, node.tree.vhd)
            fname = node.tree.name
        else:
            #             trace.print(repr(f))
            self.write(f.__name__)

#         trace.print(fname, node.args)
        if node.args:
            self.write(pre)
            # TODO rewrite making use of fname variable
            self.write(fname)
            self.write(opening)
            self.visit(node.args[0])
            for arg in node.args[1:]:
                self.write(sep)
                self.visit(arg)
            self.write(closing)
            self.write(suf)
        else:
            self.write(fname)

        if hasattr(node, 'tree'):
            if node.tree.kind == _kind.TASK:
                Visitor = _ConvertTaskVisitor
            else:
                Visitor = _ConvertFunctionVisitor

            v = Visitor(node.tree, self.funcBuf)
            v.visit(node.tree)
        trace.pop()

    def visit_Compare(self, node):
        trace.push(message='visit_Compare')
        n = node.vhd
        ns = node.vhd.size
        pre, suf = "(", ")"
        if isinstance(n, vhd_std_logic):
            pre = "stdl("
        elif isinstance(n, vhd_unsigned):
            pre, suf = "to_unsigned(", ", %s)" % ns
        elif isinstance(n, vhd_signed):
            pre, suf = "to_signed(", ", %s)" % ns
        self.write(pre)
        self.visit(node.left)
        op, right = node.ops[0], node.comparators[0]
        self.write(" %s " % opmap[type(op)])
        self.visit(right)
        self.write(suf)
        trace.pop()

    def visit_Num(self, node):
        trace.print('visit_Num', node)
        n = node.n
        if isinstance(node.vhd, vhd_std_logic):
            self.write("'%s'" % n)
        elif isinstance(node.vhd, vhd_boolean):
            self.write("%s" % bool(n))
        # elif isinstance(node.vhd, (vhd_unsigned, vhd_signed)):
        #    self.write('"%s"' % bin(n, node.vhd.size))
        elif isinstance(node.vhd, vhd_unsigned):
            if abs(n) < 2 ** 31:
                self.write("to_unsigned(%s, %s)" % (n, node.vhd.size))
            else:
                self.write('unsigned\'(b"%s")' % bin(n, node.vhd.size, True))
        elif isinstance(node.vhd, vhd_signed):
            if abs(n) < 2 ** 31:
                self.write("to_signed(%s, %s)" % (n, node.vhd.size))
            else:
                self.write('signed\'(b"%s")' % bin(n, node.vhd.size, True))
        elif isinstance(node.vhd, vhd_array):
            trace.print('Gotcha!')
            # forward to the Array itself to do the work ...
            # although we have all info
            if n != 0:
                raise ValueError('Conversion only handles setting Array to 0')
            for _ in range(len(node.vhd.shape)):
                self.write('(others => ')
#             self.write('(others => \'0\'){}'.format(')' * len(node.vhd.shape)))
            self.write('to_unsigned(0, {}){}'.format(node.vhd.vhdtype.size, ')' * len(node.vhd.shape)))
        elif isinstance(node.vhd, vhd_structtype):
            self.write('ToDO: Setting StructType')
        else:
            if n < 0:
                self.write("(")
            self.write(n)
            if n < 0:
                self.write(")")

    def visit_Str(self, node):
        typemark = 'string'
        if isinstance(node.vhd, vhd_unsigned):
            typemark = 'unsigned'
        self.write("%s'(\"%s\")" % (typemark, node.s))

    def visit_Continue(self, node, *args):
        self.write("next;")

    def visit_Expr(self, node):
        expr = node.value
        # docstrings on unofficial places
        if isinstance(expr, ast.Str):
            doc = _makeDoc(expr.s, self.ind)
            self.write(doc)
            return
        # skip extra semicolons
        if isinstance(expr, ast.Num):
            return
        self.visit(expr)
        # ugly hack to detect an orphan "task" call
        if isinstance(expr, ast.Call) and hasattr(expr, 'tree'):
            self.write(';')

    def visit_IfExp(self, node):
        # propagate the node's vhd attribute
        node.body.vhd = node.orelse.vhd = node.vhd
        self.write('tern_op(')
        self.write('cond => ')
        self.visit(node.test)
        self.write(', if_true => ')
        self.visit(node.body)
        self.write(', if_false => ')
        self.visit(node.orelse)
        self.write(')')

    def visit_For(self, node):
        trace.push(message='visit_For')
        self.labelStack.append(node.breakLabel)
        self.labelStack.append(node.loopLabel)
        var = node.target.id
        cf = node.iter
        f = self.getObj(cf.func)
        args = cf.args
        assert len(args) <= 3
        self.require(node, len(args) < 3, "explicit step not supported")
        if f is range:
            cmp = '<'
            op = 'to'
            oneoff = ''
            if len(args) == 1:
                start, stop, step = None, args[0], None
            elif len(args) == 2:
                start, stop, step = args[0], args[1], None
            else:
                start, stop, step = args
        else:  # downrange
            cmp = '>='
            op = 'downto'
            if len(args) == 1:
                start, stop, step = args[0], None, None
            elif len(args) == 2:
                start, stop, step = args[0], args[1], None
            else:
                start, stop, step = args
        assert step is None
# #        if node.breakLabel.isActive:
# #             self.write("begin: %s" % node.breakLabel)
# #             self.writeline()
# #         if node.loopLabel.isActive:
# #             self.write("%s: " % node.loopLabel)
        self.write("for %s in " % var)
        if start is None:
            self.write("0")
        else:
            self.visit(start)
            if f is downrange:
                self.write("-1")
        self.write(" %s " % op)
        if stop is None:
            self.write("0")
        else:
            self.visit(stop)
            if f is range:
                self.write("-1")
        self.write(" loop")
        self.indent()
        self.visit_stmt(node.body)
        self.dedent()
        self.writeline()
        self.write("end loop;")
# #         if node.breakLabel.isActive:
# #             self.writeline()
# #             self.write("end")
        self.labelStack.pop()
        self.labelStack.pop()
        trace.pop()

    def visit_FunctionDef(self, node):
        raise AssertionError("To be implemented in subclass")

    def visit_If(self, node):
        if node.ignore:
            return

        trace.push(message='visit_If')
        # only map to VHDL case if it's a full case
        if node.isCase and not node.isFullCase:
            warnings.warn('Open Case \'{}\' will be implemented in if/elsif chain'.format(self.tree.symdict[node.caseVar.id]), category=ToVHDLWarning)
        if node.isFullCase:
            self.mapToCase(node)
        else:
            self.mapToIf(node)
        trace.pop()

    def mapToCase(self, node):
        var = node.caseVar
        obj = self.getObj(var)
        self.write("case ")
        self.visit(var)
        self.write(" is")
        self.indent()
        for i, (test, suite) in enumerate(node.tests):
            self.writeline()
            item = test.case[1]
            if isinstance(item, EnumItemType):
                itemRepr = item._toVHDL()
            elif hasattr(obj, '_nrbits'):
                itemRepr = self.BitRepr(item, obj)
            else:
                itemRepr = i
            comment = ""
            # potentially use default clause for last test
            if (i == len(node.tests) - 1) and not node.else_:
                #                 self.write("when others")
                #                 comment = " -- %s" % itemRepr
                self.write("when ")
                self.write(itemRepr)
            else:
                self.write("when ")
                self.write(itemRepr)
            self.write(" =>%s" % comment)
            self.indent()
            self.visit_stmt(suite)
            self.dedent()
        if node.else_:
            self.writeline()
            self.write("when others =>")
            self.indent()
            self.visit_stmt(node.else_)
            self.dedent()
        self.dedent()
        self.writeline()
        self.write("end case;")

    def mapToIf(self, node):
        first = True
        for test, suite in node.tests:
            if first:
                ifstring = "if "
                first = False
            else:
                ifstring = "elsif "
                self.writeline()
            self.write(ifstring)
            self.visit(test)
            self.write(" then")
            self.indent()
            self.visit_stmt(suite)
            self.dedent()
        if node.else_:
            self.writeline()
            edges = self.getEdge(node)
            if edges is not None:
                edgeTests = [e._toVHDL() for e in edges]
                self.write("elsif ")
                self.write(" or ".join(edgeTests))
                self.write(" then")
            else:
                self.write("else")
            self.indent()
            self.visit_stmt(node.else_)
            self.dedent()
        self.writeline()
        self.write("end if;")

    def visit_ListComp(self, node):
        pass  # do nothing

    def visit_Module(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def visit_NameConstant(self, node):
        node.id = str(node.value)
        self.getName(node)

    def visit_Name(self, node):
        trace.print('visit_Name')
        if isinstance(node.ctx, ast.Store):
            self.setName(node)
        else:
            self.getName(node)

    def setName(self, node):
        self.write(node.id)

    def getName(self, node):
        n = node.id
        trace.print('getName', n)
        if n == 'False':
            if isinstance(node.vhd, vhd_std_logic):
                s = "'0'"
            else:
                s = "False"

        elif n == 'True':
            if isinstance(node.vhd, vhd_std_logic):
                s = "'1'"
            else:
                s = "True"

        elif n == 'None':
            if isinstance(node.vhd, vhd_std_logic):
                s = "'Z'"
            else:
                assert hasattr(node.vhd, 'size')
                s = '"%s"' % ('Z' * node.vhd.size)

        elif n in self.tree.vardict:
            s = n
            obj = self.tree.vardict[n]
            ori = inferVhdlObj(obj)
            pre, suf = self.inferCast(node.vhd, ori)
            s = "%s%s%s" % (pre, s, suf)

        elif n in self.tree.argnames:
            assert n in self.tree.symdict
            obj = self.tree.symdict[n]
            vhd = inferVhdlObj(obj)
            if isinstance(vhd, vhd_std_logic) and isinstance(node.vhd, vhd_boolean):
                s = "(%s = '1')" % n
            else:
                s = n

        elif n in self.tree.symdict:
            trace.print('{} in self.tree.symdict'.format(n))
            obj = self.tree.symdict[n]
            s = n
            if isinstance(obj, bool):
                if isinstance(node.vhd, vhd_std_logic):
                    s = "'%s'" % int(obj)
                else:
                    s = "%s" % obj
            elif isinstance(obj, integer_types):
                trace.print('{} is int'.format(obj))
                if isinstance(node.vhd, vhd_int):
                    #                     trace.print('self.tree.symdict, integer_types', n, type(node.vhd), node.vhd)
                    s = self.IntRepr(obj)
                elif isinstance(node.vhd, vhd_boolean):
                    s = "%s" % bool(obj)
                elif isinstance(node.vhd, vhd_std_logic):
                    s = "'%s'" % int(obj)
                elif isinstance(node.vhd, vhd_unsigned):
                    if abs(obj) < 2 ** 31:
                        s = "to_unsigned(%s, %s)" % (obj, node.vhd.size)
                    else:
                        s = 'unsigned\'(b"%s")' % bin(obj, node.vhd.size, True)
                elif isinstance(node.vhd, vhd_signed):
                    if abs(obj) < 2 ** 31:
                        s = "to_signed(%s, %s)" % (obj, node.vhd.size)
                    else:
                        s = 'signed\'(b"%s")' % bin(obj, node.vhd.size, True)
#                 else:
#                     # jb 14-03-2017 what are you doing?
#                     s = "'{}'".format(obj)

            elif isinstance(obj, _Signal):
                s = str(obj)
                ori = inferVhdlObj(obj)
                pre, suf = self.inferCast(node.vhd, ori)
                s = "%s%s%s" % (pre, s, suf)

            elif _isMem(obj):
                m = _getMemInfo(obj)
                assert m.name
                trace.print('_isMem', repr(obj), m.name)
                s = m.name

            elif isinstance(obj, EnumItemType):
                s = obj._toVHDL()

            elif (type(obj) in class_types) and issubclass(obj, Exception):
                s = n

            elif isinstance(obj, list):
                s = n
#                 self.raiseError(node, _error.UnsupportedType, "%s, %s" % (n, type(obj)))

            # jb 14-03-2017 what are you doing?
            elif isinstance(obj, str):
                trace.print('str', obj)
                s = "'{}'".format(obj)

            # dead code?
            # the _isMem test is...
            elif isinstance(obj, Array):
                s = obj._name

            elif isinstance(obj, StructType):
                #                 trace.print(n, repr(obj))
                s = obj._name

            elif isinstance(obj, dict):
                #                 trace.print('obj is dict', obj, s, n)
                pass
                # access the dict object

            else:
                self.raiseError(node, _error.UnsupportedType, "%s, %s, %s" % (n, type(obj), repr(obj)))
        else:
            raise AssertionError("name ref: %s" % n)
        self.write(s)

    def visit_Pass(self, node):
        self.write("null;")

    def visit_Print(self, node):
        argnr = 0
        for s in node.format:
            if isinstance(s, str):
                self.write('write(L, string\'("%s"));' % s)
            else:
                a = node.args[argnr]
                argnr += 1
                if s.conv is int:
                    a.vhd = vhd_int()
                else:
                    if isinstance(a.vhdOri, vhd_vector):
                        a.vhd = vhd_int()
                    elif isinstance(a.vhdOri, vhd_std_logic):
                        a.vhd = vhd_boolean()
                    elif isinstance(a.vhdOri, vhd_enum):
                        a.vhd = vhd_string()
                self.write("write(L, ")
                self.context = _context.PRINT
                self.visit(a)
                self.context = None
                if s.justified == 'LEFT':
                    self.write(", justified=>LEFT")
                if s.width:
                    self.write(", field=>%s" % s.width)
                self.write(")")
                self.write(';')
            self.writeline()
        self.write("writeline(output, L);")

    def visit_Raise(self, node):
        self.write('assert False report "End of Simulation" severity Failure;')

    def visit_Return(self, node):
        pass

    def visit_Subscript(self, node):
        #         trace.print('visit_Subscript {}'.format(node))
        if isinstance(node.slice, ast.Slice):
            self.accessSlice(node)
        else:
            self.accessIndex(node)

    def accessSlice(self, node):
        if isinstance(node.value, ast.Call) and \
           node.value.func.obj in (intbv, modbv) and \
           _isConstant(node.value.args[0], self.tree.symdict):
            c = self.getVal(node)._val
            pre, post = "", ""
            if isinstance(node.obj, Array):
                #                 trace.print('accessSlice on Array')
                pass
            if node.vhd.size <= 30:
                if isinstance(node.vhd, vhd_unsigned):
                    pre, post = "to_unsigned(", ", %s)" % node.vhd.size
                elif isinstance(node.vhd, vhd_signed):
                    pre, post = "to_signed(", ", %s)" % node.vhd.size
            else:
                if isinstance(node.vhd, vhd_unsigned):
                    pre, post = "unsigned'(", ")"
                    c = 'b"%s"' % bin(c, node.vhd.size, True)
                elif isinstance(node.vhd, vhd_signed):
                    pre, post = "signed'(", ")"
                    c = 'b"%s"' % bin(c, node.vhd.size, True)
            self.write(pre)
            self.write("%s" % c)
            self.write(post)
            return
#
# #         logjb( node.vhd, 'node.vhd', True)
# #         logjb( node.vhdOri, 'node.vhdOri')
#         pre, suf = '', ''
#         if not isinstance(node.obj, Array):
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        if isinstance(node.value.vhd, vhd_signed) and isinstance(node.ctx, ast.Load):
            if not isinstance(node.obj, Array):
                pre = pre + "unsigned("
                suf = ")" + suf
        self.write(pre)
        # this brings us to self.visit_Name, onto self.getName where the cast
        # is enforced in case of numeric_ports == False
        self.visit(node.value)
        lower, upper = node.slice.lower, node.slice.upper
        if isinstance(node.obj, Array):
            if lower is None and upper is None:
                self.write(suf)
                return
            # an array is specified (0 to n)
            self.write("(")
            if lower is None:
                self.write("0")
            else:
                self.visit(lower)
            self.write(" to ")
            if upper is None:
                # unfortunately .shape[0] is the 'sliced' size
                self.write(
                    "{}". format(self.getVal(node.slice.lower) + node.obj.shape[0]))
            else:
                self.visit(upper)

            self.write(" - 1)")
            self.write(suf)

        else:
            # special shortcut case for [:] slice
            if lower is None and upper is None:
                self.write(suf)
                return

            self.write("(")

            if lower is None:
                self.write("%s" % node.obj._nrbits)
            else:
                self.visit(lower)

            self.write("-1 downto ")

            if upper is None:
                self.write("0")
            else:
                self.visit(upper)

            self.write(")")
            self.write(suf)

    def accessIndex(self, node):
        trace.push(message='accessIndex')
        trace.print(repr(node))
        #         pre, suf = '', ''
        #         if not isinstance(node.value, Array):
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        self.write(pre)
        # if we are accessing an element out of a list of constants we can
        # short-circuit here
        if isinstance(node.value.obj, (list)) and isinstance(node.value.obj[0], int):
            trace.print(repr(node.value.obj), repr(node.slice.value), vars(node.slice.value))
            if hasattr(node.slice.value, 'value'):
                self.write(
                    '({:-d})'.format(node.value.obj[node.slice.value.value]))
            else:
                self.write('({})'.format(node.slice.value.id))
#         elif isinstance(node.value.obj, Array):
#             self.write( "<jb>")
        else:
            # this will eventually give us the name, but possibly with an
            # 'unsigned' cast ...
            self.visit(node.value)
            self.write("(")
            # assert len(node.subs) == 1
            self.visit(node.slice.value)
            self.write(")")
        self.write(suf)
        trace.pop()

    def visit_stmt(self, body):
        trace.push(message='visit_stmt')
        for stmt in body:
            self.writeline()
            self.visit(stmt)
            # ugly hack to detect an orphan "task" call
            if isinstance(stmt, ast.Call) and hasattr(stmt, 'tree'):
                self.write(';')
        trace.pop()

    def visit_Tuple(self, node):
        #         assert self.context != None, 'self.context is None'
        if self.context == _context.PRINT:
            sep = ", "
            tpl = node.elts
            self.visit(tpl[0])
            for elt in tpl[1:]:
                self.write(sep)
                self.visit(elt)
        elif self.context == _context.ASSIGNMENT:
            trace.push(message='visit_Tuple')
            trace.print('Assigning a tuple?', node, node.elts)
            self.write('(')
            for i, elt in enumerate(node.elts):
                trace.print(repr(elt))
                self.visit(elt)
                if i < len(node.elts) - 1:
                    self.write(', ')
            self.write(')')
            trace.pop()
        else:
            raise ValueError('self.context is None')

    def visit_While(self, node):
        self.labelStack.append(node.breakLabel)
        self.labelStack.append(node.loopLabel)
        self.write("while ")
        self.visit(node.test)
        self.write(" loop")
        self.indent()
        self.visit_stmt(node.body)
        self.dedent()
        self.writeline()
        self.write("end loop")
        self.write(";")
        self.labelStack.pop()
        self.labelStack.pop()

    def visit_Yield(self, node):
        self.write("wait ")
        yieldObj = self.getObj(node.value)
        if isinstance(yieldObj, delay):
            self.write("for ")
        elif isinstance(yieldObj, _WaiterList):
            self.write("until ")
        else:
            self.write("on ")
        self.context = _context.YIELD
        self.visit(node.value)
        self.context = _context.UNKNOWN
        self.write(";")

    def manageEdges(self, ifnode, senslist):
        """ Helper method to convert MyHDL style template into VHDL style"""
        first = senslist[0]
        if isinstance(first, _WaiterList):
            bt = _WaiterList
        elif isinstance(first, _Signal):
            bt = _Signal
        elif isinstance(first, delay):
            bt = delay
        assert bt
        for e in senslist:
            if not isinstance(e, bt):
                self.raiseError(ifnode, "base type error in sensitivity list")
        if len(senslist) >= 2 and bt == _WaiterList:
            # ifnode = node.code.nodes[0]
            assert isinstance(ifnode, ast.If)
            asyncEdges = []
            for test, _ in ifnode.tests:
                e = self.getEdge(test)
                if e is None:
                    self.raiseError(ifnode, "No proper edge value test")
                asyncEdges.append(e)
            if not ifnode.else_:
                self.raiseError(ifnode, "No separate else clause found")
            edges = []
            for s in senslist:
                for e in asyncEdges:
                    if s is e:
                        break
                else:
                    edges.append(s)
            ifnode.edge = edges
            senslist = [s.sig for s in senslist]
        return senslist


class _ConvertAlwaysVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf

    def visit_FunctionDef(self, node):
        self.writeDoc(node)
        w = node.body[-1]
        y = w.body[0]
        if isinstance(y, ast.Expr):
            y = y.value
        assert isinstance(y, ast.Yield)
        senslist = y.senslist
        senslist = self.manageEdges(w.body[1], senslist)
        singleEdge = (len(senslist) == 1) and isinstance(
            senslist[0], _WaiterList)
        self.write("%s: process (" % self.tree.name)
        if singleEdge:
            self.write(senslist[0].sig)
        else:
            for e in senslist[:-1]:
                self.write(e)
                self.write(', ')
            self.write(senslist[-1])
        self.write(") is")
        self.indent()
        self.indent()
        self.writeDeclarations()
        self.dedent()
        self.writeline()
        self.write("begin")
        self.indent()
        if singleEdge:
            self.writeline()
            self.write("if %s then" % senslist[0]._toVHDL())
            self.indent()
        # assert isinstance(w.body, ast.stmt)
        for stmt in w.body[1:]:
            self.writeline()
            self.visit(stmt)
        self.dedent()
        if singleEdge:
            self.writeline()
            self.write("end if;")
            self.dedent()
        self.writeline()
        self.write("end process %s;" % self.tree.name)
        self.dedent()
        self.writeline(2)


class _ConvertInitialVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf

    def visit_FunctionDef(self, node):
        #         # strip MYHDLnnn_
        #         _, __, tname = self.tree.name.partition( '_')
        #         if tname not in functiondefs:
        #             functiondefs.append(tname)
        self.writeDoc(node)
        self.write("%s: process is" % self.tree.name)
        self.indent()
#             self.write("%s: process is" % tname)
        self.indent()
        self.writeDeclarations()
        self.dedent()
        self.writeline()
        self.write("begin")
        self.indent()
        self.visit_stmt(node.body)
        self.writeline()
        self.write("wait;")
        self.dedent()
        self.writeline()
        self.write("end process %s;" % self.tree.name)
        self.dedent()
#             self.write("end process %s;" % tname)
        self.writeline(2)


class _ConvertAlwaysCombVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf

    def visit_FunctionDef(self, node):
        # a local function works nicely too
        def compressSensitivityList(senslist):
            ''' reduce spelled out list items like [*name*(0), *name*(1), ..., *name*(n)] to just *name*
                but then also remove .attr in records
            '''
            r = []
            for item in senslist:
                #                 trace.print( repr( item._name ))
                if item._name is not None:
                    # split off the base name (before the index ()
                    # and/or weed the .attr
                    name, _, _ = item._name.split('(', 1)[0].partition('.')
                    if name not in r:
                        # note that the list now contains names and not
                        # Signals, but we are interested in the strings anyway
                        # ...
                        r.append(name)

            return r

        self.writeDoc(node)
#         trace.print(self.tree.name)
#         trace.print(self.tree.senslist)
        senslist = compressSensitivityList(self.tree.senslist)
#         trace.print('> ', senslist)
        if toVHDL.standard == '2008':
            self.write("%s: process ( all ) is" % self.tree.name)
        else:
            self.write("%s: process (" % self.tree.name)
            if len(senslist) > 0:
                for e in senslist[:-1]:
                    if e not in constantlist:
                        self.write(e)
                        self.write(', ')
                self.write(senslist[-1])
            else:
                pass
            self.write(") is")
        self.indent()
        self.indent()
        self.writeDeclarations()
        self.dedent()
        self.writeline()
        self.write("begin")
        self.indent()
        self.visit_stmt(node.body)
        self.dedent()
        self.writeline()
        self.write("end process %s;" % self.tree.name)
        self.dedent()
        self.writeline(2)


class _ConvertSimpleAlwaysCombVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf

    def visit_Attribute(self, node):
        if isinstance(node.ctx, ast.Store):
            self.SigAss = True
            if isinstance(node.value, ast.Name):
                sig = self.tree.symdict[node.value.id]
                self.SigAss = sig._name
            self.visit(node.value)
        else:
            self.getAttr(node)

    def visit_FunctionDef(self, node, *args):
        trace.print(node)
        self.writeDoc(node)
        self.visit_stmt(node.body)
        self.writeline(2)


class _ConvertAlwaysDecoVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf

    def visit_FunctionDef(self, node, *args):
        self.writeDoc(node)
        assert self.tree.senslist
        senslist = self.tree.senslist
        senslist = self.manageEdges(node.body[-1], senslist)
        singleEdge = (len(senslist) == 1) and isinstance(
            senslist[0], _WaiterList)
        if toVHDL.standard == '2008':
            self.write("%s: process ( all ) is" % self.tree.name)
        else:
            self.write("%s: process (" % self.tree.name)
            if singleEdge:
                self.write(senslist[0].sig)
            else:
                for e in senslist[:-1]:
                    self.write(e)
                    self.write(', ')
                self.write(senslist[-1])
            self.write(") is")
        self.indent()
        self.indent()
        self.writeDeclarations()
        self.dedent()
        self.writeline()
        self.write("begin")
        self.indent()
        if singleEdge:
            self.writeline()
            self.write("if %s then" % senslist[0]._toVHDL())
            self.indent()
        self.visit_stmt(node.body)
        self.dedent()
        if singleEdge:
            self.writeline()
            self.write("end if;")
            self.dedent()
        self.writeline()
        self.write("end process %s;" % self.tree.name)
        self.dedent()
        self.writeline(2)


def _convertInitVal(reg, init):
    pre, suf = '', ''
    if isinstance(reg, _Signal):
        tipe = reg._type
    else:
        assert isinstance(reg, intbv)
        tipe = intbv
    if tipe is bool:
        v = "'1'" if init else "'0'"
    elif tipe is intbv:
        vhd_tipe = 'unsigned'
        if reg._min is not None and reg._min < 0:
            vhd_tipe = 'signed'
        if abs(init) < 2 ** 31:
            v = '%sto_%s(%s, %s)%s' % (pre, vhd_tipe, init, len(reg), suf)
        else:
            #             v = '%s%s\'"%s"%s' % (pre, vhd_tipe, bin(init, len(reg)), suf)
            v = '%sb"%s"%s' % (pre, bin(init, len(reg), True), suf)
    else:
        assert isinstance(init, EnumItemType)
        v = init._toVHDL()
    return v


class _ConvertAlwaysSeqVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf

    def visit_FunctionDef(self, node, *args):
        trace.push(message='visit_FunctionDef')
        self.writeDoc(node)
        assert self.tree.senslist
        senslist = self.tree.senslist
        edge = senslist[0]
        reset = self.tree.reset
        async = reset is not None and reset.async
        sigregs = self.tree.sigregs
        varregs = self.tree.varregs
        self.write("%s: process (" % self.tree.name)
        self.write(edge.sig)
        if async:
            self.write(', ')
            self.write(reset)
        self.write(") is")
        self.indent()
        self.indent()
        self.writeDeclarations()
        self.dedent()
        self.writeline()
        self.write("begin")
        self.indent()
        if not async:
            self.writeline()
            self.write("if %s then" % edge._toVHDL())
            self.indent()
        if reset is not None:
            self.writeline()
            self.write("if (%s = '%s') then" % (reset, int(reset.active)))
            self.indent()
            for s in sigregs:
                self.writeline()
                self.write("%s <= %s;" % (s, _convertInitVal(s, s._init)))
            for v in varregs:
                n, reg, init = v
                self.writeline()
                self.write("%s := %s;" % (n, _convertInitVal(reg, init)))
            self.dedent()
            self.writeline()
            if async:
                self.write("elsif %s then" % edge._toVHDL())
            else:
                self.write("else")
            self.indent()
        self.visit_stmt(node.body)
        self.dedent()
        if reset is not None:
            self.writeline()
            self.write("end if;")
            self.dedent()
        if not async:
            self.writeline()
            self.write("end if;")
            self.dedent()
        self.writeline()
        self.write("end process %s;" % self.tree.name)
        self.dedent()
        self.writeline(2)
        trace.pop()


class _ConvertFunctionVisitor(_ConvertVisitor):

    def __init__(self, tree, funcBuf):
        _ConvertVisitor.__init__(self, tree, funcBuf)
        self.returnObj = tree.returnObj
        self.returnLabel = _Label("RETURN")

    def writeOutputDeclaration(self):
        self.write(self.tree.vhd.toStr(constr=False))

    def writeInputDeclarations(self):
        endchar = ""
        for name in self.tree.argnames:
            self.write(endchar)
            endchar = ";"
            obj = self.tree.symdict[name]
            self.writeline()
            self.writeDeclaration(
                obj, name, dir="in", constr=False, endchar="")

    def visit_FunctionDef(self, node):
        if self.tree.name not in functiondefs:
            functiondefs.append(self.tree.name)
            self.write("\tfunction %s" % self.tree.name)
            if self.tree.argnames:
                self.write("(")
                self.indent()
                self.writeInputDeclarations()
                self.write(")")
#             if True:
#                 self.write('(')
#                 self.indent()
#                 self.writeInputDeclarations()
#                 self.writeline()
#                 self.write(") ")
            self.write(" return ")
            self.writeOutputDeclaration()
            self.write(" is")
            self.writeDeclarations()
            self.dedent()
            self.writeline()
            self.write("begin")
            self.indent()
            self.visit_stmt(node.body)
            self.dedent()
            self.writeline()
            self.write("end function %s;" % self.tree.name)
            self.writeline(2)

    def visit_Return(self, node):
        self.write("return ")
        node.value.vhd = self.tree.vhd
        self.visit(node.value)
        self.write(";")


class _ConvertTaskVisitor(_ConvertVisitor):

    def __init__(self, tree, funcBuf):
        _ConvertVisitor.__init__(self, tree, funcBuf)
        self.returnLabel = _Label("RETURN")

    def writeInterfaceDeclarations(self):
        endchar = ""
        for name in self.tree.argnames:
            self.write(endchar)
            endchar = ";"
            obj = self.tree.symdict[name]
            moutput = name in self.tree.outputs
            minput = name in self.tree.inputs
            inout = minput and moutput
            direction = (inout and "inout") or (moutput and "out") or "in"
            self.writeline()
            self.writeDeclaration(
                obj, name, dir=direction, constr=False, endchar="")

    def visit_FunctionDef(self, node):
        self.write("procedure %s" % self.tree.name)
        if self.tree.argnames:
            self.write("(")
            self.indent()
            self.writeInterfaceDeclarations()
            self.write(")")
        self.write(" is")
        self.writeDeclarations()
        self.dedent()
        self.writeline()
        self.write("begin")
        self.indent()
        self.visit_stmt(node.body)
        self.dedent()
        self.writeline()
        self.write("end procedure %s;" % self.tree.name)
        self.writeline(2)


# type inference


class vhd_type(object):

    def __init__(self, size=0):
        self.size = size

    def __repr__(self):
        return "%s(%s)" % (type(self).__name__, self.size)


class vhd_string(vhd_type):
    pass


class vhd_enum(vhd_type):

    def __init__(self, tipe, size=None):
        #         tracejb( "vhd_enum: init" )
        self._type = tipe
        # 26-05-2014 jb need a size
        self.size = size

    def toStr(self, constr=True):
        r = self._type.__dict__['_name']
        return r


class vhd_std_logic(vhd_type):

    def __init__(self, size=0):
        vhd_type.__init__(self)
        self.size = 1

    def toStr(self, constr=True):
        return 'std_logic'


class vhd_boolean(vhd_type):

    def __init__(self, size=0):
        vhd_type.__init__(self)
        self.size = 1

    def toStr(self, constr=True):
        return 'boolean'


class vhd_vector(vhd_type):

    def __init__(self, size=0, lenStr=False):
        vhd_type.__init__(self, size)
        self.lenStr = lenStr


class vhd_unsigned(vhd_vector):

    def toStr(self, constr=True):
        if constr:
            ls = self.lenStr
            if ls:
                return "unsigned(%s-1 downto 0)" % ls
            else:
                return "unsigned(%s downto 0)" % (self.size - 1)
        else:
            return "unsigned"


class vhd_signed(vhd_vector):

    def toStr(self, constr=True):
        if constr:
            ls = self.lenStr
            if ls:
                return "signed(%s-1 downto 0)" % ls
            else:
                return "signed(%s downto 0)" % (self.size - 1)
        else:
            return "signed"


class vhd_int(vhd_type):

    def toStr(self, constr=True):
        return "integer"


class vhd_nat(vhd_int):

    def toStr(self, constr=True):
        return "natural"


class vhd_array(vhd_type):

    def __init__(self, shape, vhdtype):
        vhd_type.__init__(self)
        self.shape = shape
        self.vhdtype = vhdtype

    def to_Str(self):
        return 'Array'

    def __repr__(self):
        return 'vhd_array {} of {}'.format(self.shape, self.vhdtype)


class vhd_structtype(vhd_type):
    def __init__(self):
        vhd_type.__init__(self)

    def to_Str(self):
        return 'StructType'

    def __repr__(self):
        return 'vhd_structtype'


class _loopInt(int):
    pass


def maxType(o1, o2):
    s1 = s2 = 0
    if isinstance(o1, vhd_type):
        s1 = o1.size
    if isinstance(o2, vhd_type):
        s2 = o2.size
    s = max(s1, s2)
    if isinstance(o1, vhd_signed) or isinstance(o2, vhd_signed):
        return vhd_signed(s)
    elif isinstance(o1, vhd_unsigned) or isinstance(o2, vhd_unsigned):
        return vhd_unsigned(s)
    elif isinstance(o1, vhd_std_logic) or isinstance(o2, vhd_std_logic):
        return vhd_std_logic()
    elif isinstance(o1, vhd_int) or isinstance(o2, vhd_int):
        return vhd_int()
    else:
        return None


def inferVhdlObj(obj, attr=None):
    vhd = None
#     trace.print(sys._getframe().f_back.f_code.co_name)

    if (isinstance(obj, _Signal) and isinstance(obj._val, intbv)) or isinstance(obj, intbv):
        ls = getattr(obj, 'lenStr', False)
        if obj.min is None or obj.min < 0:
            vhd = vhd_signed(size=len(obj), lenStr=ls)
        else:
            vhd = vhd_unsigned(size=len(obj), lenStr=ls)
    elif (isinstance(obj, _Signal) and isinstance(obj._val, bool)) or isinstance(obj, bool):
        vhd = vhd_std_logic()
    elif (isinstance(obj, _Signal) and isinstance(obj._val, EnumItemType)) or isinstance(obj, EnumItemType):
        if isinstance(obj, _Signal):
            tipe = obj._val._type
        else:
            tipe = obj._type
        vhd = vhd_enum(tipe, obj._nrbits)

    elif isinstance(obj, integer_types):
        if obj >= 0:
            vhd = vhd_nat()
        else:
            vhd = vhd_int()

    elif isinstance(obj, EnumType):
        vhd = vhd_enum(None)

    elif isinstance(obj, (list, Array)):
        trace.print('inferVhdlObj: list/Array: {}, attr: {}'.format(repr(obj), attr))
        #         trace.print('inferring', obj)
        if isinstance(obj, list):
            #             trace.print(obj)
            _, shape, _, element = m1Dinfo(obj)
        else:
            element = obj.element
            shape = obj.shape

        if isinstance(element, _Signal):
            if isinstance(element._val, intbv):
                ls = getattr(element, 'lenStr', False)
                if element.min is not None and element.min < 0:
                    vhd = vhd_array(shape, vhd_signed(size=len(element), lenStr=ls))
                else:
                    vhd = vhd_array(shape, vhd_unsigned(size=len(element), lenStr=ls))
            elif isinstance(element._val, bool):
                vhd = vhd_array(shape, vhd_std_logic())
            else:
                pass

        else:
            # defaulting?
            trace.print('Not handling {}, {}'.format(obj, element))
            pass
        trace.print('inferVhdlObj returning: {}'.format(repr(vhd)))

    elif isinstance(obj, StructType):
        trace.print('inferVhdlObj: StructType: {}, attr: {}'.format(repr(obj), repr(attr)))
        # need the member name?
        if attr is not None:
            refs = vars(obj)
            element = refs[attr]
            if isinstance(element, _Signal) and isinstance(element._val, intbv):
                ls = getattr(element, 'lenStr', False)
                if element.min is not None and element.min < 0:
                    vhd = vhd_signed(size=len(element), lenStr=ls)
                else:
                    vhd = vhd_unsigned(size=len(element), lenStr=ls)
            elif isinstance(element, _Signal) and isinstance(element._val, bool):
                vhd = vhd_std_logic()
            else:
                # defaulting?
                trace.print('inferVhdlObj, StructType: defaulting {}'.format(element))
                pass
        else:
            trace.print('inferVhdlObj, StructType: attr is None {}'.format(obj))
            pass
        trace.print('inferVhdlObj returning: {}'.format(repr(vhd)))

    return vhd


def maybeNegative(vhd):
    if isinstance(vhd, vhd_signed):
        return True
    if isinstance(vhd, vhd_int) and not isinstance(vhd, vhd_nat):
        return True
    return False


class _AnnotateTypesVisitor(ast.NodeVisitor, _ConversionMixin):

    def __init__(self, tree):
        trace.print('_AnnotateTypesVisitor {}'.format(tree))
        self.tree = tree
        trace.print(ast.dump(tree))

    def visit_FunctionDef(self, node):
        trace.push(message='visit_FunctionDef <{}>'.format(node.name))

        # don't visit arguments and decorators
        for stmt in node.body:
            self.visit(stmt)
        trace.print()
        trace.pop()

    # a placeholder to follow the AST
    def visit_Assign(self, node):
        trace.push(message='visit_Assign')
        trace.print('{}'.format(node))
        self.generic_visit(node)
        trace.pop()

    def visit_Attribute(self, node):
        trace.push(message='visit_Attribute')
        trace.print('{} {}'.format(node, node.attr))
        if hasattr(node, 'starget'):
            trace.print('already has starget chain?: {} <> {}'.format(node.starget, node.attr))
            if node.starget[1] is not None:
                node.value.starget = node.starget
            else:
                node.value.starget = (node.starget[0], node.attr)
        else:
            # if node.attr in ('next',) and isinstance(node.value.obj,
            # StructType):
            if node.attr in ('next',):
                # start a target chain
                trace.print('starting starget chain: {}'.format(repr(node.value.obj)))
                node.value.starget = (node.value.obj, None)
            else:
                trace.print('continuing starget chain: {} {}'.format(node.attr, node.obj))
                node.value.attr = node.attr
                node.value.starget = (node.obj, node.attr)

        self.generic_visit(node)
        node.vhd = copy(node.value.vhd)
        node.vhdOri = copy(node.vhd)
        trace.print()
        trace.pop()

    def visit_Assert(self, node):
        trace.push(message='visit_Assert')
        trace.print('{}'.format(node))
        self.visit(node.test)
        node.test.vhd = vhd_boolean()
        trace.pop()

    def visit_AugAssign(self, node):
        trace.push(message='visit_AugAssign')
        trace.print('{}'.format(node))
        self.visit(node.target)
        self.visit(node.value)
        if isinstance(node.op, (ast.BitOr, ast.BitAnd, ast.BitXor)):
            node.value.vhd = copy(node.target.vhd)
            node.vhdOri = copy(node.target.vhd)
        elif isinstance(node.op, (ast.RShift, ast.LShift)):
            node.value.vhd = vhd_int()
            node.vhdOri = copy(node.target.vhd)
        else:
            node.left, node.right = node.target, node.value
            self.inferBinOpType(node)

        node.vhd = copy(node.target.vhd)
        trace.pop()

    def visit_Call(self, node):
        trace.push(message='visit_Call')
        trace.print(node)
        fn = node.func
        # assert isinstance(fn, astNode.Name)
        f = self.getObj(fn)
        node.vhd = inferVhdlObj(node.obj)
        self.generic_visit(node)
        if f is concat:
            s = 0
            for a in node.args:
                trace.print('concat', a)
            for a in node.args:
                if isinstance(a, ast.Str):
                    a.vhd = vhd_unsigned(a.vhd.size)
                elif isinstance(a.vhd, vhd_signed):
                    a.vhd = vhd_unsigned(a.vhd.size)
                s += a.vhd.size
            node.vhd = vhd_unsigned(s)
        elif f is bool:
            node.vhd = vhd_boolean()
        elif f in _flatten(integer_types, ord):
            node.vhd = vhd_int()
            node.args[0].vhd = vhd_int()
        elif f in (intbv, modbv):
            node.vhd = vhd_int()
        elif f is len:
            node.vhd = vhd_int()
        elif f is now:
            node.vhd = vhd_nat()
        elif f == intbv.signed:  # note equality comparison
            # this comes from a getattr
            node.vhd = vhd_signed(fn.value.vhd.size)
        elif hasattr(node, 'tree'):
            trace.push(message='_AnnotateTypesVisitor')
            v = _AnnotateTypesVisitor(node.tree)
            v.visit(node.tree)
            node.vhd = node.tree.vhd = inferVhdlObj(node.tree.returnObj)
            trace.pop()
        else:
            #             trace.print('Unhandled visit_Call {}: {} {} {}, {}'.format(node, fn, f, node.obj, node.vhd))
            pass
        node.vhdOri = copy(node.vhd)
        trace.pop()

    def visit_Compare(self, node):
        trace.push(message='visit_Compare')
        trace.print('{}'.format(node))
        node.vhd = vhd_boolean()
        self.generic_visit(node)
        left, _, right = node.left, node.ops[0], node.comparators[0]
        if isinstance(left.vhd, vhd_std_logic) or isinstance(right.vhd, vhd_std_logic):
            left.vhd = right.vhd = vhd_std_logic()
        elif isinstance(left.vhd, vhd_unsigned) and maybeNegative(right.vhd):
            left.vhd = vhd_signed(left.vhd.size + 1)
        elif maybeNegative(left.vhd) and isinstance(right.vhd, vhd_unsigned):
            right.vhd = vhd_signed(right.vhd.size + 1)
        node.vhdOri = copy(node.vhd)
        trace.pop()

    def visit_Str(self, node):
        trace.print('visit_Attribute {}'.format(node))
        node.vhd = vhd_string()
        node.vhdOri = copy(node.vhd)

    def visit_Num(self, node):
        trace.print('visit_Num {}'.format(node))
        if node.n < 0:
            node.vhd = vhd_int()
        else:
            node.vhd = vhd_nat()
        node.vhdOri = copy(node.vhd)

    def visit_For(self, node):
        trace.push(message='visit_For')
        trace.print('{}'.format(node))
        var = node.target.id
        # make it possible to detect loop variable
        self.tree.vardict[var] = _loopInt(-1)
        self.generic_visit(node)
        trace.pop()

    def visit_NameConstant(self, node):
        trace.print('visit_NameConstant {}'.format(node))
        node.vhd = inferVhdlObj(node.value)
        node.vhdOri = copy(node.vhd)

    def visit_Name(self, node):
        trace.push(message='visit_Name')
        trace.print('{}'.format(node))
        # is a terminal
        if node.id in self.tree.vardict:
            node.obj = self.tree.vardict[node.id]
#         if hasattr(node, 'starget'):
#             node.vhd = inferVhdlObj(node.starget)
#         else:
#             node.vhd = inferVhdlObj(node.obj)
        node.vhd = inferVhdlObj(node.starget[0] if hasattr(node, 'starget') else node.obj)
#         node.vhd = inferVhdlObj(node.obj)
        node.vhdOri = copy(node.vhd)
        trace.pop()

    def visit_BinOp(self, node):
        trace.push(message='visit_BinOp')
        trace.print('{}'.format(node))
        self.generic_visit(node)
#         if isinstance(node.op, ast.BitXor):
#             trace.print('visit_BinOp', repr(node.left), repr(node.op), repr(node.right))

        if isinstance(node.op, (ast.LShift, ast.RShift)):
            self.inferShiftType(node)
        elif isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            self.inferBitOpType(node)
        # format string
        elif isinstance(node.op, ast.Mod) and isinstance(node.left, ast.Str):
            pass
        else:
            self.inferBinOpType(node)
        trace.pop()

    def inferShiftType(self, node):
        trace.print('inferShiftType {}'.format(node))
        node.vhd = copy(node.left.vhd)
        node.right.vhd = vhd_nat()
        node.vhdOri = copy(node.vhd)

    def inferBitOpType(self, node):
        trace.print('inferBitOpType {}'.format(node))
        obj = maxType(node.left.vhd, node.right.vhd)
        node.vhd = node.left.vhd = node.right.vhd = obj
        node.vhdOri = copy(node.vhd)

    def inferBinOpType(self, node):
        trace.print('inferBinOpType {}'.format(node))
        left, op, right = node.left, node.op, node.right
#         trace.print( 'inferBinOpType 1', left.vhd, right.vhd)
        if isinstance(left.vhd, (vhd_boolean, vhd_std_logic)):
            left.vhd = vhd_unsigned(1)

        if isinstance(right.vhd, (vhd_boolean, vhd_std_logic)):
            right.vhd = vhd_unsigned(1)

        if isinstance(right.vhd, vhd_unsigned):
            if maybeNegative(left.vhd) or \
               (isinstance(op, ast.Sub) and not hasattr(node, 'isRhs')):
                right.vhd = vhd_signed(right.vhd.size + 1)

        if isinstance(left.vhd, vhd_unsigned):
            if maybeNegative(right.vhd) or \
               (isinstance(op, ast.Sub) and not hasattr(node, 'isRhs')):
                left.vhd = vhd_signed(left.vhd.size + 1)

        l, r = left.vhd, right.vhd
#         trace.print( 'inferBinOpType 2 {} {}\n {} {}'.format( left.vhd, repr(left), right.vhd, repr(right)))
#         ls = l.size
#         rs = r.size
#         trace.print( 'inferBinOpType 3', shape, r.size)
        if isinstance(r, vhd_vector) and isinstance(l, vhd_vector):
            if isinstance(op, (ast.Add, ast.Sub)):
                s = max(l.size, r.size)
            elif isinstance(op, ast.Mod):
                s = r.size
            elif isinstance(op, ast.FloorDiv):
                s = l.size
            elif isinstance(op, ast.Mult):
                s = l.size + r.size
            else:
                raise AssertionError("unexpected op %s" % op)
        elif isinstance(l, vhd_vector) and isinstance(r, vhd_int):
            if isinstance(op, (ast.Add, ast.Sub, ast.Mod, ast.FloorDiv)):
                s = l.size
            elif isinstance(op, ast.Mult):
                s = 2 * l.size
            else:
                raise AssertionError("unexpected op %s" % op)
        elif isinstance(l, vhd_int) and isinstance(r, vhd_vector):
            if isinstance(op, (ast.Add, ast.Sub, ast.Mod, ast.FloorDiv)):
                s = r.size
            elif isinstance(op, ast.Mult):
                s = 2 * r.size
            else:
                raise AssertionError("unexpected op %s" % op)

        if isinstance(l, vhd_int) and isinstance(r, (vhd_int, vhd_enum)):
            if isinstance(r, vhd_int):
                node.vhd = vhd_int()
            else:
                node.vhd = vhd_enum(r._type._name, r.size)
        elif isinstance(l, (vhd_signed, vhd_int)) and isinstance(r, (vhd_signed, vhd_int)):
            node.vhd = vhd_signed(s)
        elif isinstance(l, (vhd_unsigned, vhd_int)) and isinstance(r, (vhd_unsigned, vhd_int)):
            node.vhd = vhd_unsigned(s)
        elif isinstance(l, vhd_array) or isinstance(r, vhd_array):
            trace.print('inferBinOpType: Array', l, r)
            node.vhd = vhd_array(0, 0)
        else:
            node.vhd = vhd_int()

        node.vhdOri = copy(node.vhd)

    def visit_BoolOp(self, node):
        trace.push(message='visit_Attribute')
        trace.print('{}'.format(node))
        self.generic_visit(node)
        for n in node.values:
            n.vhd = vhd_boolean()
        node.vhd = vhd_boolean()
        node.vhdOri = copy(node.vhd)
        trace.pop()

    def visit_If(self, node):
        trace.push(message='visit_If')
        trace.print('{}'.format(node))
        if node.ignore:
            return
        self.generic_visit(node)
        for test, _ in node.tests:
            test.vhd = vhd_boolean()

        trace.pop()

    def visit_IfExp(self, node):
        trace.push(message='visit_IfExp')
        trace.print('{}'.format(node))
        self.generic_visit(node)  # this will visit the 3 ast.Name objects
        node.test.vhd = vhd_boolean()
        trace.pop()

    def visit_ListComp(self, node):
        pass  # do nothing

    def visit_Subscript(self, node):
        trace.print('visit_Subscript {}'.format(node))
        #         for item in inspect.getmembers( node ):
        #             if not item[0].startswith('__') and not item[0].endswith('__') :
        #                 trace.print( '    ', item )
        if isinstance(node.slice, ast.Slice):
            self.accessSlice(node)
        else:
            self.accessIndex(node)

    def accessSlice(self, node):
        trace.push(message='accessSlice')
        trace.print(node.lineno)
        trace.print(node, repr(node.obj))
        self.generic_visit(node)
#         trace.print(node, node.obj)
        if isinstance(node.obj, intbv) or (isinstance(node.obj, _Signal) and isinstance(node.obj._val, intbv)):
            lower = node.value.vhd.size
            t = type(node.value.vhd)
            # node.expr.vhd = vhd_unsigned(node.expr.vhd.size)
            if node.slice.lower:
                node.slice.lower.vhd = vhd_int()
                lower = self.getVal(node.slice.lower)
            upper = 0

            if node.slice.upper:
                node.slice.upper.vhd = vhd_int()
                upper = self.getVal(node.slice.upper)

            if isinstance(node.ctx, ast.Store):
                node.vhd = t(lower - upper)
            else:
                node.vhd = vhd_unsigned(lower - upper)

        elif isinstance(node.obj, Array):
            #             node.vhd = None
            trace.print('accessSlice Array:', repr(node.obj))
            #             trace.print(repr(node.value))
            #             upper = node.value.vhd.size
            #             t = type(node.value.vhd)
            #             trace.print(upper, t)
            upper = node.obj.shape[0]

            if node.slice.upper:
                node.slice.upper.vhd = vhd_int()
                upper = self.getVal(node.slice.upper)
#                 trace.print('upper: ', upper)

            lower = 0
            if node.slice.lower:
                node.slice.lower.vhd = vhd_int()
                lower = self.getVal(node.slice.lower)
#                 trace.print('lower: ', lower)

            if isinstance(node.ctx, ast.Store):
                #                 trace.print('ast.Store')
                pass
            else:
                #                 trace.print('upper, lower', upper, lower)
                node.vhd = vhd_array((upper - lower), node.obj.element)
#             if isinstance(node.obj._dtype, bool):
#                 node.vhd = vhd_std_logic()
#             elif isinstance(node.obj._dtype, intbv):
#                 node.vhd = vhd_unsigned(node.obj._nrbits)
#             else:
#                 trace.print( "???")

        node.vhdOri = copy(node.vhd)
        trace.pop()

    def accessIndex(self, node):
        trace.push(message='accessIndex')
        trace.print(node.lineno)
        trace.print('vars: {}'.format(vars(node)))
        if hasattr(node, 'starget'):
            trace.print('starget:', repr(node.starget))
        #         trace.print('accessIndex 1 {}'.format(node))
        self.generic_visit(node)
        node.vhd = vhd_std_logic()  # XXX default
        node.slice.value.vhd = vhd_int()
        obj = node.value.obj
        if isinstance(obj, list):
            assert len(obj)
            _, _, _, element = m1Dinfo(obj)
            node.vhd = inferVhdlObj(element)

        elif isinstance(obj, Array):
            if isinstance(obj.element, StructType):
                trace.print('accessIndex 2 {}'.format(node))
                # there may be an attribute involved
                if hasattr(node, 'starget'):
                    node.vhd = inferVhdlObj(obj.element, node.starget[1])
                else:
                    node.vhd = inferVhdlObj(obj.element)
            else:
                node.vhd = inferVhdlObj(obj.element)

        elif isinstance(obj, _Ram):
            node.vhd = inferVhdlObj(obj.elObj)

        elif isinstance(obj, _Rom):
            node.vhd = vhd_int()

        elif isinstance(obj, intbv):
            node.vhd = vhd_std_logic()

        else:
            trace.print('accessIndex: noaction')
            pass

        node.vhdOri = copy(node.vhd)
        trace.pop()

    def visit_UnaryOp(self, node):
        trace.push(message='visit_UnaryOp')
        trace.print('{}'.format(node))
        self.visit(node.operand)
        node.vhd = copy(node.operand.vhd)
        if isinstance(node.op, ast.Not):
            # postpone this optimization until initial values are written
            #            if isinstance(node.operand.vhd, vhd_std_logic):
            #                node.vhd = vhd_std_logic()
            #            else:
            #                node.vhd = node.operand.vhd = vhd_boolean()
            node.vhd = node.operand.vhd = vhd_boolean()
        elif isinstance(node.op, ast.USub):
            if isinstance(node.vhd, vhd_unsigned):
                node.vhd = vhd_signed(node.vhd.size + 1)
            elif isinstance(node.vhd, vhd_nat):
                node.vhd = vhd_int()
        node.vhdOri = copy(node.vhd)
        trace.pop()

    def visit_While(self, node):
        trace.push(message='visit_While')
        trace.print('{}'.format(node))
        self.generic_visit(node)
        node.test.vhd = vhd_boolean()
        trace.pop()


def _annotateTypes(genlist):
    for tree in genlist:
        if isinstance(tree, _UserVhdlCode):
            continue
        v = _AnnotateTypesVisitor(tree)
        v.visit(tree)

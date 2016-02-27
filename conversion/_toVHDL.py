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

import inspect
from datetime import datetime
#import compiler
#from compiler import ast as astNode
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
from myhdl.conversion._misc import (_error,_kind,_context,
                                    _ConversionMixin, _Label, _genUniqueSuffix, _isConstant)
from myhdl.conversion._analyze import (_analyzeSigs, _analyzeGens, _analyzeTopFunc,
                                       _Ram, _Rom, _enumTypeSet)
from myhdl._Signal import _Signal,_WaiterList
from myhdl.conversion._toVHDLPackage import _package
# from myhdl._util import  _flatten
from myhdl._compat import integer_types, class_types, StringIO
from myhdl._ShadowSignal import _TristateSignal, _TristateDriver
from myhdl._misc import m1Dinfo
from myhdl._structured import Array, StructType


_version = myhdl.__version__.replace('.','')
_shortversion = _version.replace('dev','')
_converting = 0
_profileFunc = None
_enumPortTypeSet = set()

def _checkArgs(arglist):
    for arg in arglist:
        if not isinstance(arg, (GeneratorType, _Instantiator, _UserVhdlCode)):
            raise ToVHDLError(_error.ArgType, arg)

def _flatten(*args):
    arglist = []
    for arg in args:
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
    pre = '\n' + indent + '-- '
    doc = '-- ' + doc
    doc = doc.replace('\n', pre)
    return doc


class _ToVHDLConvertor(object):

    __slots__ = ("name",
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
#         tracejb( __name__ )
        self.name = None
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
#         tracejb('_ToVHDLConvertor call' )
        global _converting
        if _converting:
            return func(*args, **kwargs) # skip
        else:
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
        try:
            h = _HierExtr(name, func, *args, **kwargs)
        finally:
            _converting = 0

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

        ### initialize properly ###
        _genUniqueSuffix.reset()
        _enumTypeSet.clear()
        _enumPortTypeSet.clear()

        arglist = _flatten(h.top)
        _checkArgs(arglist)
        genlist = _analyzeGens(arglist, h.absnames)
        siglist, memlist = _analyzeSigs(h.hierarchy, hdl='VHDL')
        _annotateTypes(genlist)
        ### infer interface
        top_inst = h.hierarchy[0]
        intf = _analyzeTopFunc(top_inst, func, *args, **kwargs)
        intf.name = name
        # sanity checks on interface
        for portname in intf.argnames:
            s = intf.argdict[portname]
            if  isinstance(s, StructType):
                pass
            else :
                if s._name is None:
                    raise ToVHDLError(_error.ShadowingSignal, portname)
#             if s._inList:
#                 raise ToVHDLError(_error.PortInList, portname)
            # add enum types to port-related set
                if isinstance(s._val, EnumItemType):
                    obj = s._val._type
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

        self._convert_filter(h, intf, siglist, memlist, genlist)

        if pfile:
            _writeFileHeader(pfile, ppath)
            print(_package, file=pfile)
            pfile.close()

        _writeFileHeader(vfile, vpath)
        if needPck:
            _writeCustomPackage(vfile, intf)
        _writeModuleHeader(vfile, intf, needPck, lib, arch, useClauses, doc, stdLogicPorts)
        _writeTypeDefs(vfile, memlist)
        _writeFuncDecls(vfile)
        _writeConstants(vfile, memlist)
        _writeSigDecls(vfile, intf, siglist, memlist)
        _writeCompDecls(vfile, compDecls)
        _convertGens(genlist, siglist, memlist, vfile)
        _writeModuleFooter(vfile, arch)

        vfile.close()
        # tbfile.close()

        # postedit the .vhd file
        if len( suppressedWarnings ) > 0:
            fi = open( tpath, 'r')
            fo = open( vpath, 'w')
            # edit ...
            # read the temporary VHDL file
            filines = fi.read().split('\n')
            # split into lines
            for line in filines:
                skip = False
                for sw in suppressedWarnings:
                    if sw._name in line:
                        skip = True
                        break;
                if not skip:
                    fo.write( line + '\n' )
                    
            # selectively write the lines to the output
            
            fi.close()
            os.remove(tpath)
            fo.close()
        else:
            if os.path.exists( vpath ):
                os.remove( vpath )
            os.rename( tpath, vpath )

        ### clean-up properly ###
        self._cleanup(siglist)
        
#         tracejbdedent()
        return h.top

    def _cleanup(self, siglist):
#         tracejb( "_ToVHDLConvertor: _cleanup" )
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
#         tracejbdedent()


    def _convert_filter(self, h, intf, siglist, memlist, genlist):
#         tracejb( "_ToVHDLConvertor: _convert_filter" )
        # intended to be a entry point for other uses:
        #  code checking, optimizations, etc
#         logjbinspect(h, 'h', True)
#         logjbinspect(intf, 'intf', True)
#         logjbinspect(siglist, 'siglist', True)
#         logjbinspect(memlist, 'memlist', True)
#         logjbinspect(genlist, 'genlist', True)
#         tracejbdedent()
        pass


toVHDL = _ToVHDLConvertor()

myhdl_header = """\
-- File: $filename
-- Generated by MyHDL $version
-- Date: $date
"""

def _writeFileHeader(f, fn):
#     tracejb("_ToVHDLConvertor: " + '_writeFileHeader')
    mvars = dict(filename=fn,
                version=myhdl.__version__,
                date=datetime.today().ctime()
                )
    if toVHDL.header:
        print(string.Template(toVHDL.header).substitute(mvars), file=f)
    if not toVHDL.no_myhdl_header:
        print(string.Template(myhdl_header).substitute(mvars), file=f)
    print(file=f)
#     tracejbdedent()


def _writeCustomPackage(f, intf):
#     tracejb("_ToVHDLConvertor: " + '_writeCustomPackage')
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

def _writeModuleHeader(f, intf, needPck, lib, arch, useClauses, doc, stdLogicPorts):
    print("library IEEE;", file=f)
    print("    use IEEE.std_logic_1164.all;", file=f)
    print("    use IEEE.numeric_std.all;", file=f)
    print("    use std.textio.all;", file=f)
    print(file=f)
    if lib != "work":
        print("library %s;" % lib, file=f)
    if useClauses is not None:
        f.write(useClauses)
        f.write("\n")
    else:
        print("    use %s.pck_myhdl_%s.all;" % (lib, _shortversion), file=f)
    print(file=f)
    if needPck:
        print("    use %s.pck_%s.all;" % (lib, intf.name), file=f)
        print(file=f)
    print("entity %s is" % intf.name, file=f)
    del portConversions[:]
    pl = []
    if intf.argnames:
        f.write("    port (")
        c = ''
        for portname in intf.argnames:
            s = intf.argdict[portname]
            if isinstance(s, StructType):
                # expand the structure
                # and add assignments
                # taking care of unsigned <> std_logic_vector conversions
                expandStructType(c, stdLogicPorts, pl, portname, s)
            else:
                pl.append("%s" % c)
                c = ';'
                # change name to convert to std_logic, or
                # make sure signal name is equal to its port name
                convertPort = False
                if stdLogicPorts and s._type is intbv:
                    s._name = portname + "_num"
                    convertPort = True
                    s._used = True  # 03-01-2016 expanding a StructType obj does miss out on some port signals
                    for sl in s._slicesigs:
                        sl._setName( 'VHDL' )
                else:
                    s._name = portname

                r = _getRangeString(s)
                pt = st = _getTypeString(s)
                if convertPort:
                    pt = "std_logic_vector"
                if s._driven:
                    if s._read :
                        pl.append("\n        %s : inout %s%s" % (portname, pt, r))
                        if not isinstance(s, _TristateSignal):
                            warnings.warn("%s: %s" % (_error.OutputPortRead, portname),
                                          category=ToVHDLWarning
                                          )
                    else:
                        pl.append("\n        %s : out %s%s" % (portname, pt, r))
                    if convertPort:
                        portConversions.append("    %s <= %s(%s);" % (portname, pt, s._name))
                        s._read = True
                else:
                    if not s._read and not s._suppresswarning:
                        warnings.warn("%s: %s" % (_error.UnusedPort, portname),
                                      category=ToVHDLWarning
                                      )
    
                    pl.append("\n        %s : in %s%s" % (portname, pt, r))
                    if convertPort:
                        portConversions.append("    %s <= %s(%s);" % (s._name, st, portname))
                        s._driven = True

        for l in sortalign( pl , sort = False, port = True):
            f.write( l )
        f.write("\n        );\n")
    print("end entity %s;" % intf.name, file=f)
    print(doc, file=f)
    print(file=f)
    print("architecture %s of %s is" % (arch, intf.name), file=f)
    print(file=f)

expandlevel = 2
def expandStructType(c, stdLogicPorts, pl, name, obj):
    for attr, attrobj in vars(obj).items():
        if isinstance(attrobj, _Signal):
            pl.append("%s" % c)
            c = ';'
            convertPort = False
            portname = ''.join((name, attr))
            r = _getRangeString(attrobj)
            pt = st = _getTypeString(attrobj)
            if stdLogicPorts:
                convertPort = True
                if isinstance(attrobj._val, intbv):
                    pt = 'std_logic_vector'
            if attrobj._driven:
                if attrobj.read:
                    pl.append("\n        %s : inout %s%s" % (portname, pt, r))
                    warnings.warn("%s: %s" % (_error.OutputPortRead, portname),
                                  category=ToVHDLWarning
                                  )
                else:
                    pl.append("\n        %s : out %s%s" % (portname, pt, r))
                if convertPort:
                    if isinstance(attrobj._val, intbv):
                        portConversions.append("    %s <= %s(%s);" % (portname, pt, attrobj._name))
                    else:
                        portConversions.append("    %s <= %s;" % (portname, attrobj._name))

                    attrobj._read = True
            elif attrobj.read:
                pl.append("\n        %s : in %s%s" % (portname, pt, r))
                if convertPort:
                    if isinstance(attrobj._val, intbv):
                        portConversions.append("    %s <= %s(%s);" % (attrobj._name, st, portname))
                    else:
                        portConversions.append("    %s <= %s;" % (attrobj._name, portname))
                    attrobj._driven = True
            else:
                # silently discard neither driven nor read members
                pass

        elif isinstance(attrobj, myhdl.EnumType):
            pass
        elif isinstance(attrobj, StructType):
            if expandlevel > 1:
                # can assume is yet another interface ...
#                 expandStructType(c, stdLogicPorts, pl, name + '_' + attr, attrobj)
                expandStructType(c, stdLogicPorts, pl, name + attr, attrobj)
            else :
                pass


def _writeFuncDecls(f):
    return

def _writeConstants(f, memlist):
    f.write("\n")
    cl = []
   
    for m in memlist:
        if not m._used:
            continue
        if m._driven or not m._read:
            continue
        # drill down into the list
        cl.append( "    constant {} : {} := ( {} );\n" .format(m.name, m._typedef, expandconstant( m.mem )))
        
    for l in sortalign( cl, sort = True ):
        f.write( l )        
    f.write("\n")

def expandconstant( c  ):
    if isinstance(c, StructType):
        pass
    elif isinstance(c[0], (list, Array)):
        size = c._sizes[0] if isinstance(c, Array) else len( c )
        s = ''
        for i in range( size ):
            s = ''.join((s, '(', expandconstant(c[i]), ')'))
            if i != size - 1:
                s = ''.join((s, ',\n' ))
        return s
    else:
        # lowest (= last) level of m1D
        size = c._sizes[0] if isinstance(c, Array) else len( c )
        s = ''
        if isinstance(c[0], StructType):
            pass
        elif isinstance(c[0]._val, bool):
            for i in range( size ):
                s = ''.join((s, '{}, '.format('\'1\'' if c[i] else '\'0\'' )))
        else:
            # intbv
            for i in range( size ):
                s = ''.join((s, ' to_{}signed( {}, {} ){}'.format( '' if c[i]._min < 0 else 'un', c[i], c[i]._nrbits, ', ' ) ))
        return s[:-2]

def expandarray( c  ):
    if isinstance(c[0], (list, Array)):
        size = c._sizes[0] if isinstance(c, Array) else len( c )
        s = ''
        for i in range( size ):
            s = ''.join((s, '(', expandarray(c[i]), ')'))
            if i != size - 1:
                s = ''.join((s, ',\n' ))
        return s
    else:
        # lowest (= last) level of m1D
        size = c._sizes[0] if isinstance(c, Array) else len( c )
        s = ''
        if isinstance(c[0], StructType):
            pass
        elif isinstance(c[0]._val, bool):
            for i in range( size ):
                s = ''.join((s, '{}, '.format('\'1\'' if c[i]._val else '\'0\'' )))
        else:
            # intbv
            for i in range( size ):
                s = ''.join((s, 'b"{}", '.format(bin(c[i]._val, c[i]._nrbits, True))))

#TODO:  cut long lines
        
        # remove trailing ', '
        return s[:-2]
     
class _typedef( object ):
    def __init__(self ):
        self.names = []
        self.basetypes = []
        self.VHDLcodes = []
    
    def clear(self):
        self.names = []
        self.basetypes = []
        self.VHDLcodes = []
    
    def add(self, name, basetypes, VHDLcode):
        if name not in self.names:
            self.names.append( name )
            self.basetypes.append( basetypes )
            self.VHDLcodes.append( VHDLcode )
            
    def write(self, f):
        # first 'sort' 
        nrtd = len(self.names)
        idx = 0
        while idx < nrtd:
            bt = self.basetypes[idx]
            if bt is not None:
                if bt in self.names[idx+1:]:
                    btidx = self.names.index( bt )
                    self.names.insert( idx , self.names.pop( btidx ))
                    self.basetypes.insert( idx , self.basetypes.pop( btidx ))
                    self.VHDLcodes.insert( idx , self.VHDLcodes.pop( btidx ))
                    # stay at this index and test whether this name now has a 'predecessor'
                else:
                    idx += 1

            else:
                idx += 1

        # then write
        for i,l in enumerate( self.VHDLcodes ):
            f.write(l)
        
        
def addstructuredtypedef( obj ):
    ''' adds the typedefs for a StructType
        possibly descending down 
    '''
    basetype = None
    if isinstance( obj, StructType):
        refs = vars(obj)
        for key in refs:
            if isinstance(refs[key], (StructType, Array)):
                basetype = addstructuredtypedef(refs[key])
        # all lower structured types are now defined
#         rname = '\\' + obj.ref() + '\\'
        rname = obj.ref()
        lines = "    type {} is record\n".format( rname )
        # follow the sequencelist if any
        if hasattr(obj, 'sequencelist')and obj.sequencelist:
            refs = []
            for key in obj.sequencelist:
                if hasattr(obj, key):
                    refs.append( key )

        else:
            refs = vars(obj)

        entries = []
        for key in refs:
            mobj = vars(obj)[key]
            if isinstance(mobj , _Signal):
                entries.append( "        {} : {}{};\n".format(key, _getTypeString(mobj), _getRangeString(mobj) ))
            elif isinstance( mobj,  Array):
#                 print(mobj.ref())
                entries.append( "        {} : a{};\n".format(key, mobj.ref())) ###
            elif isinstance( mobj, StructType):
#                 entries.append( "        {} : \\{}\\;\n".format(key, mobj.ref()))
                entries.append( "        {} : {};\n".format(key, mobj.ref()))

        # align-format the contents
        for l in sortalign( entries, sort = False):
            lines += l
        lines += "    end record ;\n\n"
        typedefs.add( rname, None, lines)
        basetype = rname

    elif isinstance(obj, Array):
        if isinstance(obj.element, StructType):
            p = basetype = addstructuredtypedef(obj.element)
        else:
            if isinstance(obj.element, _Signal):
                mobj = obj.element._val
            else:
                mobj = obj.element
                
            if isinstance(mobj, intbv): #m.elObj._nrbits is not None:
                basetype = '{}{}'.format(_getTypeString(obj.element)[0], obj.element._nrbits)
            elif isinstance( mobj, bool): #mobj._type == bool :
                basetype = 'b'
            else:
                raise AssertionError
            p = '{}{}'.format( _getTypeString(obj.element), _getRangeString(obj.element))

        for _, size in  enumerate( reversed( obj._sizes )):
            o = basetype
            basetype = 'a{}_{}'.format( size, o)
            typedefs.add( basetype, o, "    type {} is array(0 to {}-1) of {};\n" .format(basetype, size, p))
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
            enumused.append( t._name )
            tt = "%s\n" % t._toVHDL()
            f.write( tt )
    f.write("\n")
    # then write the structured types
    for m in memlist:
        if not m._used or m.usagecount == 0:
            continue
        # infer attributes for the case of named signals in a list
#         print('inferring {:30} {:4} {:4} {}'.format( m.name, m._driven, m._read, repr(m.mem ) ))
        inferattrs( m, m.mem)
#         print('inferattrs: {:4} {:4}'.format( m._driven, m._read ))
        if m.depth == 1 and isinstance(m.elObj, StructType):
                # a 'single' StructType
            basetype = addstructuredtypedef(m.elObj)
        elif isinstance(m.mem, Array):
            basetype = addstructuredtypedef(m.mem)
            
        else:
            # it is a (multi-dimensional) list
            if isinstance(m.elObj, StructType):
                p = basetype = m.elObj.ref()
            else:
                if isinstance(m.elObj, _Signal):
                    mobj = m.elObj._val
                else:
                    mobj = m.elObj
                    
                if isinstance(mobj, intbv): #m.elObj._nrbits is not None:
                    basetype = '{}{}'.format(_getTypeString(m.elObj)[0], m.elObj._nrbits)
                elif isinstance( mobj, bool): #mobj._type == bool :
                    basetype = 'b'
                else:
                    raise AssertionError
                p = '{}{}'.format( _getTypeString(m.elObj), _getRangeString(m.elObj))
                
            for _, size in  enumerate( reversed( m._sizes )):
                o = basetype
                basetype = 'a{}_{}'.format( size, o)
                typedefs.add( basetype, o, "    type {} is array(0 to {}-1) of {};\n" .format(basetype, size, p))
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
        if not s._used:
            continue
        if s._name in intf.argnames:
            continue
        r = _getRangeString(s)
        p = _getTypeString(s)
        if s._driven or s._read:
            if not toVHDL.no_initial_values: 
                if isinstance(s._val, bool):
                    sl.append("    signal %s : %s%s := '%s';" % (s._name, p, r, 1 if s._val else 0))
                elif isinstance(s._val, intbv):
                    sl.append("    signal %s : %s%s := b\"%s\";" % (s._name, p, r, bin(s._val, s._nrbits, True)))
                elif isinstance(s._val, EnumItemType):
                    sl.append("    signal %s : %s%s := %s;" % (s._name, p, r, s._val))
            else:
                sl.append("    signal %s : %s%s;" % (s._name, p, r))
                
                
            if s._driven:
                if not s._read and not isinstance(s, _TristateDriver):
                    if not s._suppresswarning:
                        warnings.warn("%s: %s" % (_error.UnreadSignal, s._name),
                                      category=ToVHDLWarning
                                      )
                    else:
                        suppressedWarnings.append( s )
                
            elif s._read:
                warnings.warn("%s: %s" % (_error.UndrivenSignal, s._name),
                              category=ToVHDLWarning
                              )
                constwires.append(s)


    for m in memlist:
        if not m._used or m.usagecount == 0:
            continue

        if not m._driven:
            continue
        
        if not m._read:
            continue
            

        if isinstance(m.mem, Array):
            if m.mem._initialised:
                sl.append("    signal {} : {} := ({});" .format(m.name, m._typedef, expandarray(m.mem)))
            else:
                sl.append("    signal {} : {};" .format(m.name, m._typedef ))
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
                sl.append("    signal {} : {} := ({});" .format(m.name, m._typedef, expandarray(m.mem)))
            else:
                sl.append("    signal {} : {};" .format(m.name, m._typedef))
                
        elif isinstance(m.mem, StructType):
            if not toVHDL.no_initial_values: 
                sl.append("    signal {} : {} := ({});" .format(m.name, m._typedef, m.mem.initial('vhdl') ))
            else:
                sl.append("    signal {} : {};" .format(m.name, m._typedef ))
        else:
            pass
      

    for l in sortalign( sl , sort = True ):
        print( l , file = f)
    print(file=f)


def sortalign( sl , sort = False, port = False):
    # align the colons  
    maxpos = 0    
    for l in sl:
        if ':' in l:
            t = l.find(':')
            maxpos = t if t > maxpos else maxpos

    if maxpos:
        for i,l in enumerate( sl ):
            if ':' in l:
                p = l.find(':')
                b, c, e = l.partition(':')
                sl[i] =  b + ' ' * (maxpos - p) + c + e 

    # align after 'in', 'out' or 'inout'
    if port:
        portdirections = ( ': in', ': out', ': inout')
        maxpos = 0
        for l in sl:
            for tst in portdirections:
                if tst in l:
                    t = l.find(tst) + len(tst)
                    maxpos = t if t > maxpos else maxpos
                    continue
        if maxpos:
            for i,l in enumerate( sl ):
                for tst in portdirections:
                    if tst in l:
                        p = l.find(tst)
                        b, c, e = l.partition(tst)
                        sl[i] =  b + c + ' ' * (maxpos - p - len(tst)) + e 
          
    # align then :=' if any
    maxpos = 0
    for l in sl:
        if ':=' in l:
            t = l.find( ':=' )
            maxpos = t if t > maxpos else maxpos
    if maxpos:
        for i,l in enumerate( sl ):
            if ':=' in l:
                p = l.find( ':=' )
                b, c, e = l.partition(':=')
                sl[i] =  b + ' ' * (maxpos - p) + c + e            

    if sort:
        # sort the signals
        return sorted( sl )
    else:
        return sl


def inferattrs( m, mem):
#     print( m.name , mem)
    if isinstance(mem, StructType):
#         md, mr =  m._driven, m._read,
#         print( "StructType" , mem._driven, mem._read)
        refs = vars( mem )
        for k in refs:
            s = refs[k]
            if isinstance(s, _Signal):
#                 print(s._name, s._driven, s._read)
#                 print('inferring Signal', k, repr( s ) , s._driven, s._read)
                if not m._driven and s._driven:
                    m._driven = s._driven
                if not m._read and s._read:
                    m._read = s._read
#                 # only consider a StructType signal if at least one of its members
#                 # is both driven and read
#                 if not m._driven or not m._read:
#                     if s._driven and s._read:
#                         m._driven = s._driven
#                         m._read = s._read
            elif isinstance(s, (Array, StructType)):
                # it may be another StructType
                # or an Array
#                 print(' inferring nested Array or StructType', repr( s ) , s._driven, s._read)
                inferattrs(m, s)
            else:
#                 print( 'inferring ?', k, repr( s ))
                pass
#         print( 'inferattrs {:39}, {:4}, {:4}  returned {:4}, {:4}' .format( m.name,  md, mr, m._driven, m._read))
            
    elif isinstance(mem[0], list):
        for mmm in mem:
            inferattrs(m, mmm )
    else:
        # lowest (= last) level of m1D
        for s in mem:
#             print( 'inferring' , s, s._driven, s._read)
            if hasattr(m, '_driven') and hasattr(s, '_driven'):
                if not m._driven and s._driven:
                    m._driven = s._driven
                if not m._read and s._read:
                    m._read = s._read
             


def _writeCompDecls(f,  compDecls):
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
                msb = s._nrbits-1
            return "(%s downto 0)" %  msb
        else:
            raise AssertionError
    elif isinstance(s, intbv):
        if s._nrbits is not None:
            ls = getattr(s, 'lenStr', False)
            if ls:
                msb = ls + '-1'
            else:
                msb = s._nrbits-1
            return "(%s downto 0)" %  msb
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
            r =  "std_logic"
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
    blockBuf = StringIO()
    funcBuf = StringIO()
    for tree in genlist:
        if isinstance(tree, _UserVhdlCode):
            blockBuf.write(str(tree))
            continue
        if tree.kind == _kind.ALWAYS:
            Visitor = _ConvertAlwaysVisitor
        elif tree.kind == _kind.INITIAL:
            Visitor = _ConvertInitialVisitor
        elif tree.kind == _kind.SIMPLE_ALWAYS_COMB:
            Visitor = _ConvertSimpleAlwaysCombVisitor
        elif tree.kind == _kind.ALWAYS_DECO:
            Visitor = _ConvertAlwaysDecoVisitor
        elif tree.kind == _kind.ALWAYS_SEQ:
            Visitor = _ConvertAlwaysSeqVisitor
        else: # ALWAYS_COMB
            Visitor = _ConvertAlwaysCombVisitor
        v = Visitor(tree, blockBuf, funcBuf)
        v.visit(tree)
    vfile.write(funcBuf.getvalue()); funcBuf.close()
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
        if hasattr(s, 'toVHDL') and s._read:
            r =  s.toVHDL()
            print(r, file=vfile)
    # hack for slice signals in a list
    for m in memlist:
        if m._read:
            if isinstance(m.mem, StructType):
                pass
            else:
                for s in m.mem:
                    if hasattr(s, 'toVHDL'):
                        r =  s.toVHDL()
                        print(r, file=vfile)
    print(file=vfile)
    vfile.write(blockBuf.getvalue()); blockBuf.close()


opmap = {
    ast.Add      : '+',
    ast.Sub      : '-',
    ast.Mult     : '*',
    ast.Div      : '/',
    ast.Mod      : 'mod',
    ast.Pow      : '**',
    ast.LShift   : 'shift_left',
    ast.RShift   : 'shift_right',
    ast.BitOr    : 'or',
    ast.BitAnd   : 'and',
    ast.BitXor   : 'xor',
    ast.FloorDiv : '/',
    ast.Invert   : 'not ',
    ast.Not      : 'not ',
    ast.UAdd     : '+',
    ast.USub     : '-',
    ast.Eq       : '=',
    ast.Gt       : '>',
    ast.GtE      : '>=',
    ast.Lt       : '<',
    ast.LtE      : '<=',
    ast.NotEq    : '/=',
    ast.And      : 'and',
    ast.Or       : 'or',
}


class _ConvertVisitor(ast.NodeVisitor, _ConversionMixin):

    def __init__(self, tree, buf):
#         tracejb( "_ConvertVisitor : __init__" )
#         print( '_ConvertVisitor', tree.name)
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
#         tracejbdedent()

    def write(self, arg):
#         tracejb( "_ConvertVisitor: write" )
        self.buf.write("%s" % arg)
        self.line += "%s" % arg
#         tracejbdedent()

    def writeline(self, nr=1):
#         tracejb( "_ConvertVisitor: writeline" )
        for _ in range(nr):
            self.buf.write("\n")
        self.buf.write("%s" % self.ind)
        self.line = "%s" % self.ind
#         tracejbdedent()

    def writeDoc(self, node):
#         tracejb( "_ConvertVisitor: writeDoc" )
        assert hasattr(node, 'doc')
        doc = _makeDoc(node.doc, self.ind)
        self.write(doc)
        self.writeline()
#         tracejbdedent()

    def IntRepr(self, obj):
        if obj >= 0:
            s = "%s" % int(obj)
        else:
            s = "(- %s)" % abs(int(obj))
        return s


    def BitRepr(self, item, var):
        return 'b"%s"' % bin(item, len(var), True)


    def inferCast(self, vhd, ori):
#         print('inferCast', vhd, ori)
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
                    # note the order of resizing and casting here (otherwise bug!)
                    pre, suf = "resize(unsigned(", "), %s)" % vhd.size
                else:
                    pre, suf = "unsigned(", ")"
            elif isinstance(ori, vhd_array):
                pass
            else:
#                 print('?')
                pre, suf = "to_unsigned(", ", %s)" % vhd.size
        elif isinstance(vhd, vhd_signed):
            if isinstance(ori, vhd_signed):
                if vhd.size != ori.size:
                    pre, suf = "resize(", ", %s)" % vhd.size
            elif isinstance(ori, vhd_unsigned):
                if vhd.size != ori.size:
                    # I think this should be the order of resizing and casting here
                    pre, suf = "signed(resize(", ", %s))" % vhd.size
                else:
                    pre, suf = "signed(", ")"
            elif isinstance(ori, vhd_array):
#                 print('inferCast', vhd, ori)
                pass
            else:
                pre, suf = "to_signed(", ", %s)" % vhd.size
        elif isinstance(vhd, vhd_boolean):
            if not isinstance(ori, vhd_boolean):
                pre, suf = "bool(", ")"
#                 pre, suf = "(", " = '1')" # purer VHDL? but fails several 'conversion tests'
        elif isinstance(vhd, vhd_std_logic):
            if not isinstance(ori, vhd_std_logic):
                if isinstance(ori, vhd_unsigned) :
                    pre, suf = "", "(0)"
                else:
                    pre, suf = "stdl(", ")"
        elif isinstance(vhd, vhd_string):
            if isinstance(ori, vhd_enum):
                pre, suf = "%s'image(" % ori._type._name, ")"
        elif isinstance(vhd, vhd_enum):
            if not isinstance(ori, vhd_enum):
                pre, suf = "%s'pos(" % vhd._type._name, ")"
        return pre, suf


    def writeIntSize(self, n):
        # write size for large integers (beyond 32 bits signed)
        # with some safety margin
        if n >= 2**30:
            size = int(math.ceil(math.log(n+1,2))) + 1  # sign bit!
            self.write("%s'sd" % size)

    def writeDeclaration(self, obj, name, kind="", dir="", endchar=";", constr=True):
        if isinstance(obj, EnumItemType):
            tipe = obj._type._name
            
        elif isinstance(obj, _Ram):
            tipe = "t_array_%s" % name
            elt = inferVhdlObj(obj.elObj).toStr(True)
            self.write("type %s is array(0 to %s-1) of %s;" % (tipe, obj.depth, elt))
            self.writeline()
            
        elif isinstance(obj, Array):
            # make the type
            if isinstance(obj.element, bool) :
                basetype = 'b'
            elif obj.element._nrbits is not None:
                basetype = '{}{}'.format(_getTypeString(obj.element)[0],  obj.element._nrbits)
            else:
                raise AssertionError
            p = '{}{}'.format( _getTypeString(obj.element), _getRangeString(obj.element))
            if isinstance(obj.element, bool) :
                basetype = 'b'
            elif obj.element._nrbits is not None:
                basetype = '{}{}'.format(_getTypeString(obj.element)[0], obj.element._nrbits)
            else:
                raise AssertionError            
            
            for _, size in  enumerate( reversed( obj._sizes )):
                o = basetype
                basetype = 'a{}_{}'.format( size, 0)
#                 if basetype not in typedefs:
#                     self.write("type {} is array(0 to {}-1) of {};" .format(basetype, size, p))
                typedefs.add(basetype, 0, basetype, "type {} is array(0 to {}-1) of {};" .format(basetype, size, p))
                # next level if any
                p = basetype
            tipe = basetype
            
        else:
            vhd = inferVhdlObj(obj)
            if isinstance(vhd, vhd_enum):
                tipe = obj._val._type._name
            else:
                tipe = vhd.toStr(constr)
                
        if kind: kind += " "
        if dir: dir += " "
        self.write("%s%s: %s%s%s" % (kind, name, dir, tipe, endchar))

    def writeDeclarations(self):
        if self.tree.hasPrint:
            self.writeline()
            self.write("variable L: line;")
        for name, obj in self.tree.vardict.items():
            if isinstance(obj, _loopInt):
                continue # hack for loop vars
            self.writeline()
            self.writeDeclaration(obj, name, kind="variable")

    def indent(self):
        self.ind += ' ' * 4

    def dedent(self):
        self.ind = self.ind[:-4]

    def visit_BinOp(self, node):
        if isinstance(node.op, (ast.LShift, ast.RShift)):
            self.shiftOp(node)
        elif isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            self.BitOp(node)
        elif isinstance(node.op, ast.Mod) and (self.context == _context.PRINT):
            self.visit(node.left)
            self.write(", ")
            self.visit(node.right)
        else:
            self.BinOp(node)

    def inferBinaryOpCast(self, node, left, right, op):
        ns, os = node.vhd.size, node.vhdOri.size
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
#         print('BinOp', node.op, node.left, node.right)
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
        if isinstance(node.ctx, ast.Store):
            self.setAttr(node)
        else:
            self.getAttr(node)
        if node.attr in ('next',) :
            pass
        else:
            if not isinstance(node.value.obj, EnumType):
                if hasattr(node.value, 'id')  :
                    self.write( '{}.{}'.format( node.value.id, node.attr) )
                else:
                    self.write( '.{}'.format(node.attr))
                

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
            self.visit( node.value )
            
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
        lhs = node.targets[0]
        rhs = node.value
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
                if i == len(rom)-1:
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
            return

        elif isinstance(node.value, ast.ListComp):
            # skip list comprehension assigns for now
            return

        # default behavior
        convOpen, convClose = "", ""
        if isinstance(lhs.vhd, vhd_type):
            rhs.vhd = lhs.vhd
        self.isLhs = True
        self.visit( lhs )
        self.isLhs = False
        if self.SigAss:
            if isinstance(lhs.value, ast.Name):
                sig = self.tree.symdict[lhs.value.id]
            self.write(' <= ')
            self.SigAss = False
        else:
            self.write(' := ')
        self.write(convOpen)
        # node.expr.target = obj = self.getObj(node.nodes[0])
        self.visit(rhs)
        self.write(convClose)
        self.write(';')

    def visit_AugAssign(self, node):
        # XXX apparently no signed context required for augmented assigns
        left, op, right =  node.target, node.op, node.value
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
        fn = node.func
        # assert isinstance(fn, astNode.Name)
        f = self.getObj(fn)
        if f is print:
            self.visit_Print(node)
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
            return
        
        elif f is now:
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            self.write(pre)
            self.write("(now / 1 ns)")
            self.write(suf)
            return
        
        elif f is ord:
            opening, closing = '', ''
            if isinstance(node.args[0], ast.Str):
                if len(node.args[0].s) > 1:
                    self.raiseError(node, _error.UnsupportedType, "Strings with length > 1" )
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
            return
        
        elif f == intbv.signed: # note equality comparison
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
            return
        
        elif (type(f) in class_types) and issubclass(f, Exception):
            self.write(f.__name__)
        elif f in (posedge, negedge):
            opening, closing = ' ', ''
            self.write(f.__name__)
        elif f is delay:
            self.visit(node.args[0])
            self.write(" * 1 ns")
            return
        
        elif f is concat:
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            opening, closing =  "unsigned'(", ")"
            sep = " & "
        elif hasattr(node, 'tree'):
            pre, suf = self.inferCast(node.vhd, node.tree.vhd)
            fname = node.tree.name
        else:
#             print( repr(f) )
            self.write(f.__name__)

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
            
        if hasattr(node, 'tree'):
            if node.tree.kind == _kind.TASK:
                Visitor = _ConvertTaskVisitor
            else:
                Visitor = _ConvertFunctionVisitor
                
            v = Visitor(node.tree, self.funcBuf)
            v.visit(node.tree)

    def visit_Compare(self, node):
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

    def visit_Num(self, node):
        n = node.n
        if isinstance(node.vhd, vhd_std_logic):
            self.write("'%s'" % n)
        elif isinstance(node.vhd, vhd_boolean):
            self.write("%s" % bool(n))
        #elif isinstance(node.vhd, (vhd_unsigned, vhd_signed)):
        #    self.write('"%s"' % bin(n, node.vhd.size))
        elif isinstance(node.vhd, vhd_unsigned):
            if abs(n) < 2**31:
                self.write("to_unsigned(%s, %s)" % (n, node.vhd.size))
            else:
                self.write('unsigned\'(b"%s")' % bin(n, node.vhd.size, True))
        elif isinstance(node.vhd, vhd_signed):
            if abs(n) < 2**31:
                self.write("to_signed(%s, %s)" % (n, node.vhd.size))
            else:
                self.write('signed\'(b"%s")' % bin(n, node.vhd.size, True))
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
        else: # downrange
            cmp = '>='
            op = 'downto'
            if len(args) == 1:
                start, stop, step = args[0], None, None
            elif len(args) == 2:
                start, stop, step = args[0], args[1], None
            else:
                start, stop, step = args
        assert step is None
##        if node.breakLabel.isActive:
##             self.write("begin: %s" % node.breakLabel)
##             self.writeline()
##         if node.loopLabel.isActive:
##             self.write("%s: " % node.loopLabel)
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
##         if node.breakLabel.isActive:
##             self.writeline()
##             self.write("end")
        self.labelStack.pop()
        self.labelStack.pop()

    def visit_FunctionDef(self, node):
        raise AssertionError("To be implemented in subclass")

    def visit_If(self, node):
        if node.ignore:
            return
        # only map to VHDL case if it's a full case
        if node.isFullCase:
            self.mapToCase(node)
        else:
            self.mapToIf(node)

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
            if (i == len(node.tests)-1) and not node.else_:
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
        pass # do nothing


    def visit_Module(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def visit_NameConstant(self, node):
        node.id = str(node.value)
        self.getName(node)

    def visit_Name(self, node):
        if isinstance(node.ctx, ast.Store):
            self.setName(node)
        else:
            self.getName(node)

    def setName(self, node):
        self.write(node.id)

    def getName(self, node):
        n = node.id
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
                s = "(%s = '1')" %  n
            else:
                s = n
                
        elif n in self.tree.symdict:
            obj = self.tree.symdict[n]
            s = n
            if isinstance(obj, bool):
                if isinstance(node.vhd, vhd_std_logic):
                    s = "'%s'" % int(obj)
                else:
                    s = "%s" % obj
            elif isinstance(obj, integer_types):
                if isinstance(node.vhd, vhd_int):
                    s = self.IntRepr(obj)
                elif isinstance(node.vhd, vhd_boolean):
                    s = "%s" % bool(obj) 
                elif isinstance(node.vhd, vhd_std_logic):
                    s = "'%s'" % int(obj)
                elif isinstance(node.vhd, vhd_unsigned):
                    if abs(obj) < 2** 31:
                        s = "to_unsigned(%s, %s)" % (obj, node.vhd.size)
                    else:
                        s = 'unsigned\'(b"%s")' % bin(obj, node.vhd.size, True)
                elif isinstance(node.vhd, vhd_signed):
                    if abs(obj) < 2** 31:
                        s = "to_signed(%s, %s)" % (obj, node.vhd.size)
                    else:
                        s = 'signed\'(b"%s")' % bin(obj, node.vhd.size, True)
                            
            elif isinstance(obj, _Signal):
                s = str(obj)
                ori = inferVhdlObj(obj)
                pre, suf = self.inferCast(node.vhd, ori)
                s = "%s%s%s" % (pre, s, suf)
                
            elif _isMem(obj):
                m = _getMemInfo(obj)
                assert m.name
                s = m.name

            elif isinstance(obj, EnumItemType):
                s = obj._toVHDL()
                
            elif (type(obj) in class_types) and issubclass(obj, Exception):
                s = n
                
            elif isinstance(obj, list):
                s = n
#                 self.raiseError(node, _error.UnsupportedType, "%s, %s" % (n, type(obj)))

            # dead code?
            elif isinstance( obj, Array):
                s = obj._name

            elif isinstance( obj, StructType):
#                 print(n, repr(obj))
                s = obj._name

            elif isinstance(obj, dict):
                print('obj is dict', obj, s, n)
                # access the dict object
     
            else:
                self.raiseError(node, _error.UnsupportedType, "%s, %s" % (n, type(obj)))
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
                pass
            if node.vhd.size <= 30:
                if isinstance(node.vhd, vhd_unsigned):
                    pre, post = "to_unsigned(", ", %s)" % node.vhd.size
                elif isinstance(node.vhd, vhd_signed):
                    pre, post = "to_signed(", ", %s)" % node.vhd.size
            else:
                if isinstance(node.vhd, vhd_unsigned):
                    pre, post = "unsigned'(", ")"
                    c = 'b"%s"' % bin(c, node.vhd.size,True)
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
        self.visit(node.value) # this brings us to self.visit_Name, onto self.getName where the cast is enforced in case of numeric_ports == False
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
                self.write("{}". format( self.getVal(node.slice.lower) + node.obj._sizes[0] ))    # unfortunately ._sizes[0] is the 'sliced' size
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
#         pre, suf = '', ''
#         if not isinstance(node.value, Array):
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        self.write(pre)
        # if we are accessing an element out of a list of constants we can short-circuit here
        if isinstance(node.value.obj, (list)) and isinstance(node.value.obj[0], int):
            if hasattr(node.slice.value, 'value'):
                self.write('({:-d})'.format(node.value.obj[node.slice.value.value]))
            else:
                self.write('({})'.format(node.slice.value.id))
#         elif isinstance(node.value.obj, Array):
#             self.write( "<jb>")
        else:
            self.visit(node.value) # this will eventually give us the name, but possibly with an 'unsigned' cast ...
            self.write("(")
            #assert len(node.subs) == 1
            self.visit(node.slice.value)
            self.write(")")
        self.write(suf)

    def visit_stmt(self, body):
        for stmt in body:
            self.writeline()
            self.visit(stmt)
            # ugly hack to detect an orphan "task" call
            if isinstance(stmt, ast.Call) and hasattr(stmt, 'tree'):
                self.write(';')

    def visit_Tuple(self, node):
        assert self.context != None
        sep = ", "
        tpl = node.elts
        self.visit(tpl[0])
        for elt in tpl[1:]:
            self.write(sep)
            self.visit(elt)

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
            bt  = delay
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
        singleEdge = (len(senslist) == 1) and isinstance(senslist[0], _WaiterList)
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
#                 print( repr( item._name ))
                if item._name is not None:
                    # split off the base name (before the index ()
                    # and/or weed the .attr
                    name, _, _ = item._name.split('(',1)[0].partition('.')
                    if name not in r:
                        r.append( name ) # note that the list now contains names and not Signals, but we are interested in the strings anyway ...

            return r

        self.writeDoc(node)
#         print(self.tree.senslist)
        senslist = compressSensitivityList( self.tree.senslist )
#         print('> ', senslist)
        self.write("%s: process (" % self.tree.name)
        if len(senslist) > 0:
            for e in senslist[:-1]:
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
        singleEdge = (len(senslist) == 1) and isinstance(senslist[0], _WaiterList)
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
        if abs(init) < 2**31:
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
            self.writeDeclaration(obj, name, dir="in", constr=False, endchar="")



    def visit_FunctionDef(self, node):
        if self.tree.name not in functiondefs:
            functiondefs.append( self.tree.name )
            self.write("\tfunction %s(" % self.tree.name)
            self.indent()
            self.writeInputDeclarations()
            self.writeline()
            self.write(") return ")
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
            self.writeDeclaration(obj, name, dir=direction, constr=False, endchar="")

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
    def __init__(self, tipe, size = None):
#         tracejb( "vhd_enum: init" )
        self._type = tipe
#         logjb( tipe )
        #26-05-2014 jb need a size
        self.size = size
#         tracejbdedent()

    def toStr(self, constr = True):
#         tracejb( "vhd_enum: toStr" )
        r = self._type.__dict__['_name']
#         logjb( r )
#         tracejbdedent()
        return r

class vhd_std_logic(vhd_type):
    def __init__(self, size=0):
#         tracejb( "vhd_std_logic: init" )
        vhd_type.__init__(self)
        self.size = 1
#         tracejbdedent()

    def toStr(self, constr=True):
#         tracejb( "vhd_std_logic: toStr" )
#         tracejbdedent()
        return 'std_logic'


class vhd_boolean(vhd_type):
    def __init__(self, size=0):
#         tracejb( "vhd_boolean: init" )
#         tracejbdedent()
        vhd_type.__init__(self)
        self.size = 1

    def toStr(self, constr=True):
#         tracejb( "vhd_boolean: toStr" )
#         tracejbdedent()
        return 'boolean'


class vhd_vector(vhd_type):
    def __init__(self, size=0, lenStr=False):
        vhd_type.__init__(self, size)
        self.lenStr = lenStr


class vhd_unsigned(vhd_vector):
    def toStr(self, constr=True):
#         tracejb( "vhd_unsigned: toStr" )
#         tracejbdedent()
        if constr:
            ls = self.lenStr
            if ls:
                return "unsigned(%s-1 downto 0)" % ls
            else:
                return "unsigned(%s downto 0)" % (self.size-1)
        else:
            return "unsigned"

class vhd_signed(vhd_vector):
    def toStr(self, constr=True):
#         tracejb( "vhd_signed: toStr" )
#         tracejbdedent()
        if constr:
            ls = self.lenStr
            if ls:
                return "signed(%s-1 downto 0)" % ls
            else:
                return "signed(%s downto 0)" % (self.size-1)
        else:
            return "signed"

class vhd_int(vhd_type):
    def toStr(self, constr=True):
#         tracejb( "vhd_int: toStr" )
#         tracejbdedent()
        return "integer"

class vhd_nat(vhd_int):
    def toStr(self, constr=True):
#         tracejb( "vhd_nat: toStr" )
#         tracejbdedent()
        return "natural"

class vhd_array(vhd_type):
    def to_Str(self):
        return 'Array'
    
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


def inferVhdlObj(obj, attr = None):
    vhd = None
    if (isinstance(obj, _Signal) and isinstance(obj._val, intbv)) or \
       isinstance(obj, intbv):
        ls = getattr(obj, 'lenStr', False)
        if obj.min is None or obj.min < 0:
            vhd = vhd_signed(size=len(obj), lenStr=ls)
        else:
            vhd = vhd_unsigned(size=len(obj), lenStr=ls)
    elif (isinstance(obj, _Signal) and isinstance(obj._val, bool)) or \
         isinstance(obj, bool):
        vhd = vhd_std_logic()
    elif (isinstance(obj, _Signal) and isinstance(obj._val, EnumItemType)) or\
         isinstance(obj, EnumItemType):
        if isinstance(obj, _Signal):
            tipe = obj._val._type
        else:
            tipe = obj._type
        vhd = vhd_enum(tipe , obj._nrbits)

    elif isinstance(obj, integer_types):
        if obj >= 0:
            vhd = vhd_nat()
        else:
            vhd = vhd_int()
    elif isinstance( obj , EnumType):
        vhd = vhd_enum(None)
        
    elif isinstance(obj,(list, Array)):
        if isinstance(obj, list):
            _, _, _, element = m1Dinfo( obj )
        else:    
            element = obj.element

        if isinstance(element, _Signal):
            if  isinstance(element._val, intbv):
                ls = getattr(element, 'lenStr', False)
                if element.min is not None and element.min < 0:
                    vhd = vhd_signed(size=len(element), lenStr=ls)
                else:
                    vhd = vhd_unsigned(size=len(element), lenStr=ls)
            elif isinstance(element._val, bool):
                vhd = vhd_std_logic()
            else:
                pass
            
        else:
            # defaulting?
            pass
        
    elif isinstance(obj, StructType):
        # need the member name?
        if attr is not None:
            refs = vars( obj )
            element = refs[attr]
            if isinstance(element, _Signal) and isinstance( element._val, intbv):
                ls = getattr(element, 'lenStr', False)
                if element.min is not None and element.min < 0:
                    vhd = vhd_signed(size=len(element), lenStr=ls)
                else:
                    vhd = vhd_unsigned(size=len(element), lenStr=ls)
            elif isinstance(element, _Signal) and isinstance(element._val, bool):
                vhd = vhd_std_logic()
            else:
                # defaulting?
                pass
        else:
            pass
    
    return vhd


def maybeNegative(vhd):
    if isinstance(vhd, vhd_signed):
        return True
    if isinstance(vhd, vhd_int) and not isinstance(vhd, vhd_nat):
        return True
    return False

class _AnnotateTypesVisitor(ast.NodeVisitor, _ConversionMixin):

    def __init__(self, tree):
        self.tree = tree


    def visit_FunctionDef(self, node):
        # don't visit arguments and decorators
        for stmt in node.body:
            self.visit(stmt)

    def visit_Attribute(self, node):
# #         if node.attr in ('next',):
# #             # start a target chain
# #             node.value.target = node.value.obj
# #         else:
# #             # try copy down
# #             if hasattr(node, 'target'):
# #                 node.value.target = node.target
        if hasattr(node, 'starget'):
            node.value.starget = node.starget
        else:
#             if node.attr in ('next',) and isinstance(node.value.obj, StructType):
            if node.attr in ('next',) :
                # start a target chain
                node.value.starget = node.value.obj
            else:
                node.value.starget = node.obj
        
        self.generic_visit(node)
        node.vhd = copy(node.value.vhd)
        node.vhdOri = copy(node.vhd)

    def visit_Assert(self, node):
        self.visit(node.test)
        node.test.vhd = vhd_boolean()

    def visit_AugAssign(self, node):
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

    def visit_Call(self, node):
        fn = node.func
        # assert isinstance(fn, astNode.Name)
        f = self.getObj(fn)
        node.vhd = inferVhdlObj(node.obj)
        self.generic_visit(node)
        if f is concat:
            s = 0
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
        elif f == intbv.signed: # note equality comparison
            # this comes from a getattr
            node.vhd = vhd_signed(fn.value.vhd.size)
        elif hasattr(node, 'tree'):
            v = _AnnotateTypesVisitor(node.tree)
            v.visit(node.tree)
            node.vhd = node.tree.vhd = inferVhdlObj(node.tree.returnObj)
        node.vhdOri = copy(node.vhd)

    def visit_Compare(self, node):
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

    def visit_Str(self, node):
        node.vhd = vhd_string()
        node.vhdOri = copy(node.vhd)

    def visit_Num(self, node):
        if node.n < 0:
            node.vhd = vhd_int()
        else:
            node.vhd = vhd_nat()
        node.vhdOri = copy(node.vhd)

    def visit_For(self, node):
        var = node.target.id
        # make it possible to detect loop variable
        self.tree.vardict[var] = _loopInt(-1)
        self.generic_visit(node)
 
    def visit_NameConstant(self, node):
        node.vhd = inferVhdlObj(node.value)
        node.vhdOri = copy(node.vhd)
    
    def visit_Name(self, node):
        # is a terminal
        if node.id in self.tree.vardict:
            node.obj = self.tree.vardict[node.id]
        if hasattr(node, 'starget'):
            node.vhd = inferVhdlObj(node.starget)
        else:
            node.vhd = inferVhdlObj(node.obj)
#         node.vhd = inferVhdlObj(node.obj)
        node.vhdOri = copy(node.vhd)

    def visit_BinOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, (ast.LShift, ast.RShift)):
            self.inferShiftType(node)
        elif isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            self.inferBitOpType(node)
        elif isinstance(node.op, ast.Mod) and isinstance(node.left, ast.Str): # format string
            pass
        else:
#             print( 'visit_BinOp', repr(node.left), repr(node.op), repr(node.right))
            self.inferBinOpType(node)

    def inferShiftType(self, node):
        node.vhd = copy(node.left.vhd)
        node.right.vhd = vhd_nat()
        node.vhdOri = copy(node.vhd)

    def inferBitOpType(self, node):
        obj = maxType(node.left.vhd, node.right.vhd)
        node.vhd = node.left.vhd = node.right.vhd = obj
        node.vhdOri = copy(node.vhd)

    def inferBinOpType(self, node):
        left, op, right = node.left, node.op, node.right
#         print( 'inferBinOpType 1', left.vhd, right.vhd)
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
#         print( 'inferBinOpType 2 {} {}\n {} {}'.format( left.vhd, repr(left), right.vhd, repr(right)))
        ls = l.size
        rs = r.size
#         print( 'inferBinOpType 3', ls, rs)
        if isinstance(r, vhd_vector) and isinstance(l, vhd_vector):
            if isinstance(op, (ast.Add, ast.Sub)):
                s = max(ls, rs)
            elif isinstance(op, ast.Mod):
                s = rs
            elif isinstance(op, ast.FloorDiv):
                s = ls
            elif isinstance(op, ast.Mult):
                s = ls + rs
            else:
                raise AssertionError("unexpected op %s" % op)
        elif isinstance(l, vhd_vector) and isinstance(r, vhd_int):
            if isinstance(op, (ast.Add, ast.Sub, ast.Mod, ast.FloorDiv)):
                s = ls
            elif isinstance(op, ast.Mult):
                s = 2 * ls
            else:
                raise AssertionError("unexpected op %s" % op)
        elif isinstance(l, vhd_int) and isinstance(r, vhd_vector):
            if isinstance(op, (ast.Add, ast.Sub, ast.Mod, ast.FloorDiv)):
                s = rs
            elif isinstance(op, ast.Mult):
                s = 2 * rs
            else:
                raise AssertionError("unexpected op %s" % op)
            
        if isinstance(l, vhd_int) and isinstance(r, (vhd_int,vhd_enum)):
            if isinstance(r, vhd_int):
                node.vhd = vhd_int()
            else:
                node.vhd = vhd_enum(r._type._name,rs)
        elif isinstance(l, (vhd_signed, vhd_int)) and isinstance(r, (vhd_signed, vhd_int)):
            node.vhd = vhd_signed(s)
        elif isinstance(l, (vhd_unsigned, vhd_int)) and isinstance(r, (vhd_unsigned, vhd_int)):
            node.vhd = vhd_unsigned(s)
        elif isinstance(l, vhd_array) or isinstance(r, vhd_array):
#             print( 'Array')
            node.vhd = vhd_array(0) 
        else:
            node.vhd = vhd_int()
            
        node.vhdOri = copy(node.vhd)

    def visit_BoolOp(self, node):
        self.generic_visit(node)
        for n in node.values:
            n.vhd = vhd_boolean()
        node.vhd = vhd_boolean()
        node.vhdOri = copy(node.vhd)

    def visit_If(self, node):
        if node.ignore:
            return
        self.generic_visit(node)
        for test, _ in node.tests:
            test.vhd = vhd_boolean()

    def visit_IfExp(self, node):
        self.generic_visit(node) # this will visit the 3 ast.Name objects
        node.test.vhd = vhd_boolean()

    def visit_ListComp(self, node):
        pass # do nothing


    def visit_Subscript(self, node):
        if isinstance(node.slice, ast.Slice):
            self.accessSlice(node)
        else:
            self.accessIndex(node)

    def accessSlice(self, node):
        self.generic_visit(node)
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
                node.vhd = t(lower-upper)
            else:
                node.vhd = vhd_unsigned(lower-upper)
                
            
        elif isinstance(node.obj, Array):
#             node.vhd = None
            node.vhd = vhd_array(0)
#             if isinstance(node.obj._dtype, bool):
#                 node.vhd = vhd_std_logic()
#             elif isinstance(node.obj._dtype, intbv):
#                 node.vhd = vhd_unsigned(node.obj._nrbits)
#             else:
#                 print( "???")
        

            

        
        node.vhdOri = copy(node.vhd)

    def accessIndex(self, node):
        self.generic_visit(node)
        node.vhd = vhd_std_logic() # XXX default
        node.slice.value.vhd = vhd_int()
        obj = node.value.obj
        if isinstance(obj, list):
            assert len(obj)
            _, _, _, element = m1Dinfo( obj )
            node.vhd = inferVhdlObj(element)
            
        elif isinstance(obj, Array):
            node.vhd = inferVhdlObj(obj.element)
            
        elif isinstance(obj, _Ram):
            node.vhd = inferVhdlObj(obj.elObj)
            
        elif isinstance(obj, _Rom):
            node.vhd = vhd_int()
            
        elif isinstance(obj, intbv):
            node.vhd = vhd_std_logic()
            
        else:
            pass
        
        node.vhdOri = copy(node.vhd)
        
    def visit_UnaryOp(self, node):
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
                node.vhd = vhd_signed(node.vhd.size+1)
            elif isinstance(node.vhd, vhd_nat):
                node.vhd = vhd_int()
        node.vhdOri = copy(node.vhd)

    def visit_While(self, node):
        self.generic_visit(node)
        node.test.vhd = vhd_boolean()


def _annotateTypes(genlist):
    for tree in genlist:
        if isinstance(tree, _UserVhdlCode):
            continue
        v = _AnnotateTypesVisitor(tree)
        v.visit(tree)








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
# from myhdl._array import Array
from myhdl._structured import Array, StructType

# tracing the poor man's way
TRACING_JB = True
DO_INSPECT = False
if TRACING_JB:
    from myhdl.tracejb import tracejb, logjb, tracejbdedent, logjbinspect, tracenode
else:
    def tracejb( a, b = None):
        pass
    def logjb(a, b = None, c = False):
        pass
    def tracejbdedent():
        pass
    def logjbinspect(a, b= None, c = False):
        pass
    def tracenode( a = None, b = None):
        pass

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

    def __call__(self, func, *args, **kwargs):
#         tracejb('_ToVHDLConvertor call' )
        global _converting
        if _converting:
#             logjb('converting?')
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
            logjb( name, 'name', True)
            logjb( func, 'func')
#             for item in args:
#                 print( repr(item), end = ', ' )            
#             for item in kwargs:
#                 print( repr(item), end = ', ' )
            logjb( '_HierExtr')
            h = _HierExtr(name, func, *args, **kwargs)
        finally:
            _converting = 0

        if self.directory is None:
            directory = ''
        else:
            directory = self.directory
        compDecls = self.component_declarations
        useClauses = self.use_clauses

#         vpath = os.path.join(directory, name + ".vhd")
        vpath = os.path.join(directory, name + ".tmp")
        vfile = open(vpath, 'w')
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

#         logjb( h.top, 'h.top')
        arglist = _flatten(h.top)
#         logjb( "Flattened Top ==================================" )
#         logjb( arglist , 'arglist')
#         for arg in arglist:
#             logjbinspect( arg , 'arg in arglist', False)

        _checkArgs(arglist)
#         logjb( "Checked Args ==================================" )
#         logjb( "Analyzing Gens  ==================================" )
        genlist = _analyzeGens(arglist, h.absnames)
#         logjbinspect( genlist , 'genlist' ,True)
#         for item in genlist:
#             logjb(item)
#         logjb( "Analyzed Gens  ==================================" )
#         logjb( "Analyzing Sigs  ==================================" )
        siglist, memlist = _analyzeSigs(h.hierarchy, hdl='VHDL')
#         logjb( "Analyzed Sigs ==================================" )
        # print h.top
#         logjb( "AnnotateTypes(genlist)  ==================================" )
        _annotateTypes(genlist)
#         logjb( genlist , 'genlist' )
#         logjb( "Annotated Types ==================================" )

        ### infer interface
#         logjb( "Analyzing Top Function ==================================" )
        top_inst = h.hierarchy[0]
        intf = _analyzeTopFunc(top_inst, func, *args, **kwargs)
        intf.name = name
#         logjb( "Analyzed Top Function ==================================" )
        # sanity checks on interface
        for portname in intf.argnames:
#             logjb( portname, 'portname')
            s = intf.argdict[portname]
            if s._name is None:
                raise ToVHDLError(_error.ShadowingSignal, portname)
            if s._inList:
                raise ToVHDLError(_error.PortInList, portname)
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
            fi = open( vpath, 'r')
            npath = os.path.join(directory, name + ".vhd")
            fo = open( npath, 'w')
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
            os.remove(vpath)
            fo.close()
        else:
            npath = os.path.join(directory, name + ".vhd")
            if os.path.exists( npath ):
                os.remove( npath )
            os.rename( vpath, npath )

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
#     tracejbdedent()

portConversions = []
suppressedWarnings = []

def _writeModuleHeader(f, intf, needPck, lib, arch, useClauses, doc, stdLogicPorts):
#     tracejb("_ToVHDLConvertor: " + '_writeModuleHeader')
    print("library IEEE;", file=f)
    print("use IEEE.std_logic_1164.all;", file=f)
    print("use IEEE.numeric_std.all;", file=f)
    print("use std.textio.all;", file=f)
    print(file=f)
    if lib != "work":
        print("library %s;" % lib, file=f)
    if useClauses is not None:
        f.write(useClauses)
        f.write("\n")
    else:
        print("use %s.pck_myhdl_%s.all;" % (lib, _shortversion), file=f)
    print(file=f)
    if needPck:
        print("use %s.pck_%s.all;" % (lib, intf.name), file=f)
        print(file=f)
    print("entity %s is" % intf.name, file=f)
#     logjb( stdLogicPorts , 'stdLogicPorts')
    del portConversions[:]
    pl = []
    if intf.argnames:
        f.write("    port (")
        c = ''
        for portname in intf.argnames:
            s = intf.argdict[portname]
#             logjbinspect(s, 's', True)
#             f.write("%s" % c)
            pl.append("%s" % c)
            c = ';'
            # change name to convert to std_logic, or
            # make sure signal name is equal to its port name
            convertPort = False
            if stdLogicPorts and s._type is intbv:
                s._name = portname + "_num"
                convertPort = True
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
#                     f.write("\n        %s: inout %s%s" % (portname, pt, r))
                    pl.append("\n        %s: inout %s%s" % (portname, pt, r))
                    if not isinstance(s, _TristateSignal):
                        warnings.warn("%s: %s" % (_error.OutputPortRead, portname),
                                      category=ToVHDLWarning
                                      )
                else:
#                     f.write("\n        %s: out %s%s" % (portname, pt, r))
                    pl.append("\n        %s: out %s%s" % (portname, pt, r))
                if convertPort:
                    portConversions.append("    %s <= %s(%s);" % (portname, pt, s._name))
                    s._read = True
            else:
                if not s._read:
                    warnings.warn("%s: %s" % (_error.UnusedPort, portname),
                                  category=ToVHDLWarning
                                  )

#                 f.write("\n        %s: in %s%s" % (portname, pt, r))
                pl.append("\n        %s: in %s%s" % (portname, pt, r))
                if convertPort:
                    portConversions.append("    %s <= %s(%s);" % (s._name, st, portname))
                    s._driven = True
        for l in sortalign( pl , sort = False):
            f.write( l )
        f.write("\n        );\n")
    print("end entity %s;" % intf.name, file=f)
    print(doc, file=f)
    print(file=f)
    print("architecture %s of %s is" % (arch, intf.name), file=f)
    print(file=f)
#     tracejbdedent()


def _writeFuncDecls(f):
#     tracejb('_writeFuncDecls')
#     logjbinspect(f, 'f', True)
#     tracejbdedent()
    return
    # print >> f, package

def _writeConstants(f, memlist):
    tracejb( "_ToVHDLConvertor: _writeConstants: " )
    f.write("\n")
    cl = []
   
    for m in memlist:
        if not m._used:
            continue
        if m._driven or not m._read:
            continue
        logjb(m.name , 'm.name')
        # drill down into the list
        cl.append( "    constant {} : {} := ( {} );\n" .format(m.name, m._typedef, expandconstant( m.mem )))
        
    for l in sortalign( cl, sort = True ):
        f.write( l )        
    f.write("\n")
    tracejbdedent()

def expandconstant( c  ):
    if isinstance(c[0], (list, Array)):
        size = c._sizes[0] if isinstance(c, Array) else len( c )
        s = ''
        for i in range( size ):
            s += '( '
            s += expandconstant(c[i])
            s += ' )'
            if i != size - 1:
                s += ',\n'
        return s
    else:
        # lowest (= last) level of m1D
        size = c._sizes[0] if isinstance(c, Array) else len( c )
        s = ''
        for i in range( size ):
#             s +=  ' "{}"'.format( bin( c[i] , c[i]._nrbits ))
            if c[i]._min < 0:
                s +=  ' to_signed( {}, {} )'.format( c[i], c[i]._nrbits)
            else:
                s +=  ' to_unsigned( {}, {} )'.format( c[i], c[i]._nrbits)
            if i != size - 1:
                s += ','
        return s
     
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
#         print('typdefs.write')
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
                    # stay at this index and test wheter this name now has a 'predecessor'
                else:
                    idx += 1

            else:
                idx += 1

        # then write
        for i,l in enumerate( self.VHDLcodes ):
#             print( self.names[i], self.basetypes[i])
            f.write(l)
        
        
def _writeTypeDefs(f, memlist):
    tracejb("_ToVHDLConvertor: " +  "_writeTypeDefs: " )
    f.write("\n")
    # write the enums
    sortedList = list(_enumTypeSet)
    sortedList.sort(key=lambda x: x._name)
    enumused = []
    for t in sortedList:
        logjb( t )
#         print( t._name , end = ', ')
        if t._name not in enumused:
            enumused.append( t._name )
            tt = "%s\n" % t._toVHDL()
            f.write( tt )
#     print( enumused )
    f.write("\n")
    # then write the structured types
    for m in memlist:
        if not m._used:
            continue
        logjb( m.name, 'm', True)
        logjb( m.mem, 'm.mem')
        # infer attributes for the case of named signals in a list
        inferattrs( m, m.mem)
#         if not m._driven and not m._read:
#         if not m._driven:
#             continue
        logjb(m.name , 'm.name')
        #TODO: write all the typedefs to a set, then sort it in the right order to fulfil all dependencies
        if m.depth == 1 and isinstance(m.elObj, StructType):
                # a 'single' StructType
#                 rname = m.elObj.__class__.__name__
                rname = m.elObj.ref()
#                 if rname not in typedefs:
#                     f.write("type {} is record\n".format( rname ))
#                     refs = vars(m.elObj)
#                     for k in refs:
#                         if isinstance( refs[k], _Signal):                
#                             f.write("  {} : {}{};\n".format(k, _getTypeString(refs[k]), _getRangeString( refs[k]) ))
#                         elif isinstance( refs[k], StructType):
#                             raise ValueError( "StructType in StructType not (yet) supported")
#                         elif isinstance( refs[k], Array):
#                             raise ValueError( "Array in StructType not (yet) supported")
#                     f.write("  end record ;\n")
#                     typedefs.append( rname )
                l = "type {} is record\n".format( rname )
                refs = vars(m.elObj)
#                 rb = []
                for k in refs:
                    if isinstance( refs[k], _Signal):
#                         rb.append( repr(refs[k]))                
                        l += "  {} : {}{};\n".format(k, _getTypeString(refs[k]), _getRangeString( refs[k]) )
                    elif isinstance( refs[k], StructType):
                        raise ValueError( "StructType in StructType not (yet) supported")
                    elif isinstance( refs[k], Array):
                        raise ValueError( "Array in StructType not (yet) supported")
                l += "  end record ;\n"
                typedefs.add( rname, None, l)    
                basetype = rname
        else:
            if isinstance(m.elObj, StructType):
                p = basetype = m.elObj.ref()
#                 p =  _getTypeString(m.elObj)
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
#                 if basetype not in typedefs:
#                     typedefs.append( basetype )
#                     f.write("type {} is array(0 to {}-1) of {};\n" .format(basetype, size, p))
                typedefs.add( basetype, o, "    type {} is array(0 to {}-1) of {};\n" .format(basetype, size, p))
                # next level if any
                p = basetype
        
        m._typedef = basetype
        
    typedefs.write(f)    
    f.write("\n")
    tracejbdedent()

constwires = []
typedefs = _typedef()
functiondefs = []

def _writeSigDecls(f, intf, siglist, memlist):
    tracejb("_ToVHDLConvertor: " +  "_writeSigDecls: " )
    del constwires[:]
#     del typedefs[:]
    typedefs.clear()
    del functiondefs[:]
    sl = []
#     logjb(siglist, 'siglist')
    for s in siglist:
#         logjbinspect(s, 's', True)
        if not s._used:
            continue
        if s._name in intf.argnames:
            continue
#         logjb(s._name , 's._name')
        r = _getRangeString(s)
        p = _getTypeString(s)
        if s._driven:
            if not s._read and not isinstance(s, _TristateDriver):
                if not s._suppresswarning:
                    warnings.warn("%s: %s" % (_error.UnreadSignal, s._name),
                                  category=ToVHDLWarning
                                  )
                else:
                    suppressedWarnings.append( s )
            # the following line implements initial value assignments
            # print >> f, "%s %s%s = %s;" % (s._driven, r, s._name, int(s._val))
#             print("    signal %s : %s%s;" % (s._name, p, r), file=f)
            sl.append("    signal %s : %s%s;" % (s._name, p, r))
        elif s._read:
            # the original exception
            # raise ToVHDLError(_error.UndrivenSignal, s._name)
            # changed to a warning and a continuous assignment to a wire
            warnings.warn("%s: %s" % (_error.UndrivenSignal, s._name),
                          category=ToVHDLWarning
                          )
            constwires.append(s)
#             print("    signal %s : %s%s;" % (s._name, p, r), file=f)
            sl.append("    signal %s : %s%s;" % (s._name, p, r))
            

    for m in memlist:
        if not m._used:
            continue

        # infer attributes for the case of named signals in a list
#         inferattrs( m, m.mem)
#         if (not m._driven and not m._read) or (not m._driven and m._read):
        logjb(m.name , 'm.name', True)
#         if not m._driven and not m._read :
        if not m._driven:
            continue
        logjb(m.name , ' is driven')
#         print("    signal {} : {};" .format(m.name, m._typedef ), file=f)
        sl.append("    signal {} : {};" .format(m.name, m._typedef ))
                      

    for l in sortalign( sl , sort = True ):
        print( l , file = f)
    print(file=f)
    tracejbdedent()
    

def sortalign( sl , sort = False):
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
    if isinstance(mem, StructType):
#         print( mem )
        refs = vars( mem )
        for k in refs:
            s = refs[k]
            if isinstance(s, _Signal):
                if not m._driven and s._driven:
                    m._driven = s._driven
                if not m._read and s._read:
                    m._read = s._read
            else:
                # it may be another StructType
                # or an Array
                pass
            
    
    elif isinstance(mem[0], list):
        for mmm in mem:
            inferattrs(m, mmm )
    else:
        # lowest (= last) level of m1D
        for s in mem:
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
    tracejb("_ToVHDLConvertor: " +  "_convertGens: " )
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
        logjb( Visitor , 'Visitor')
        v = Visitor(tree, blockBuf, funcBuf)
        logjb( tree, 'tree')
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
    tracejbdedent()


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
#         logjbwr( 'line: {}' .format(self.line))
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
        tracejb( "_ConvertVisitor: IntRepr" )
        if obj >= 0:
            s = "%s" % int(obj)
        else:
            s = "(- %s)" % abs(int(obj))
        tracejbdedent()
        return s


    def BitRepr(self, item, var):
        tracejb( "_ConvertVisitor: BitRepr" )
        tracejbdedent()
        return '"%s"' % bin(item, len(var))


    def inferCast(self, vhd, ori):
        tracejb( "_ConvertVisitor: inferCast" )
        logjbinspect( vhd, 'inspect vhd', True)
        logjbinspect( ori, 'inspect ori', True)
        pre, suf = "", ""
        if isinstance(vhd, vhd_int):
            if not isinstance(ori, vhd_int):
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
            else:
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
#                 tracejb( "_ConvertVisitor: inferring cast for enum " +  vhd._type._name)
#                 print "inferring cast for enum " , vhd._type._name
                pre, suf = "%s'pos(" % vhd._type._name, ")"

        logjb( '<' + pre + '>, <' + suf + '>', 'inferred')
        tracejbdedent()
        return pre, suf


    def writeIntSize(self, n):
        tracejb( "_ConvertVisitor: writeIntSize" )
        # write size for large integers (beyond 32 bits signed)
        # with some safety margin
        if n >= 2**30:
            size = int(math.ceil(math.log(n+1,2))) + 1  # sign bit!
            self.write("%s'sd" % size)
        tracejbdedent()

    def writeDeclaration(self, obj, name, kind="", dir="", endchar=";", constr=True):
        tracejb( "_ConvertVisitor: writeDeclaration" )
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
        tracejbdedent()

    def writeDeclarations(self):
        tracejb( "_ConvertVisitor: writeDeclarations" )
        if self.tree.hasPrint:
            self.writeline()
            self.write("variable L: line;")
        for name, obj in self.tree.vardict.items():
            if isinstance(obj, _loopInt):
                continue # hack for loop vars
            self.writeline()
            self.writeDeclaration(obj, name, kind="variable")
        tracejbdedent()

    def indent(self):
        tracejb( "_ConvertVisitor: indent" )
        self.ind += ' ' * 4
        tracejbdedent()

    def dedent(self):
        tracejb( "_ConvertVisitor: dedent" )
        self.ind = self.ind[:-4]
        tracejbdedent()

    def visit_BinOp(self, node):
        tracenode( 'BinOp')
        tracejb( "_ConvertVisitor: visit_BinOp" )
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
        tracejbdedent()
        tracenode()

    def inferBinaryOpCast(self, node, left, right, op):
        tracejb( "_ConvertVisitor: inferBinaryOpCast" )
        ns, os = node.vhd.size, node.vhdOri.size
        ds = ns - os
        logjb( left.vhd, 'left' , True)
        logjb( left.vhdOri)
        logjb( right.vhd, 'right', True)
        logjb( right.vhdOri)
        logjb( ds , 'ds')
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
        logjb( (pre, suf), 'pre, suf')
        tracejbdedent()
        return pre, suf


    def BinOp(self, node):
        tracejb( "_ConvertVisitor: BinOp" )
        logjb( node.left.vhd, 'node.left.vhd', True)
        logjb( node.right.vhd, 'node.right.vhd')
        pre, suf = self.inferBinaryOpCast(node, node.left, node.right, node.op)
        self.write(pre)
        self.visit(node.left)
        self.write(" %s " % opmap[type(node.op)])
        self.visit(node.right)
        self.write(suf)
        tracejbdedent()

    def inferShiftOpCast(self, node, left, right, op):
        tracejb( "_ConvertVisitor: inferShiftOpCast" )
        logjbinspect(node, 'node', True)
        logjbinspect(left, 'left', True)
        logjbinspect(right, 'right', True)
        logjbinspect(op, 'op', True)
        ns, os = node.vhd.size, node.vhdOri.size
        ds = ns - os
        if ds > 0:
            if isinstance(node.left.vhd, vhd_vector):
                left.vhd.size = ns
                node.vhdOri.size = ns
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        tracejbdedent()
        return pre, suf


    def shiftOp(self, node):
        tracejb( "_ConvertVisitor: shiftOp" )
        pre, suf = self.inferShiftOpCast(node, node.left, node.right, node.op)
        self.write(pre)
        self.write("%s(" % opmap[type(node.op)])
        self.visit(node.left)
        self.write(", ")
        self.visit(node.right)
        self.write(")")
        self.write(suf)
        tracejbdedent()

    def BitOp(self, node):
        tracejb( "_ConvertVisitor: BitOp" )
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        self.write(pre)
        self.write("(")
        self.visit(node.left)
        self.write(" %s " % opmap[type(node.op)])
        self.visit(node.right)
        self.write(")")
        self.write(suf)
        tracejbdedent()

    def visit_BoolOp(self, node):
        tracenode( 'BoolOp')
        tracejb( "_ConvertVisitor: visit_BoolOp" )
        if isinstance(node.vhd, vhd_std_logic):
            self.write("stdl")
        self.write("(")
        self.visit(node.values[0])
        for n in node.values[1:]:
            self.write(" %s " % opmap[type(node.op)])
            self.visit(n)
        self.write(")")
        tracejbdedent()
        tracenode()

    def visit_UnaryOp(self, node):
        tracenode( 'UnaryOp')
        tracejb( "_ConvertVisitor: visit_UnaryOp" )

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
        tracejbdedent()
        tracenode()

    def visit_Attribute(self, node):
        tracenode( 'Attribute')
        tracejb( "_ConvertVisitor: visit_Attribute" )
        logjbinspect( node, 'node', True)
        if isinstance(node.ctx, ast.Store):
            self.setAttr(node)
        else:
            self.getAttr(node)
        if node.attr in ('next',) :
            pass
        else:
            logjbinspect( node, 'node after set-/get-Attr', True)
            logjbinspect(node.value, 'node.value', True)
            if not isinstance(node.value.obj, EnumType):
                if hasattr(node.value, 'id')  :
                    self.write( '{}.{}'.format( node.value.id, node.attr) )
                else:
                    self.write( '.{}'.format(node.attr))
                
        tracejbdedent()
        tracenode()

    def setAttr(self, node):
        tracejb( "_ConvertVisitor: setAttr" )
        logjbinspect(node, 'node', True)
        self.SigAss = True
        if isinstance(node.value, ast.Subscript):
            logjbinspect(node.value, 'node.value', True)
            self.SigAss = 'Killroy'
            logjb( self.SigAss, 'Killroy: self.SigAss')
            self.visit(node.value)

        else:
            assert node.attr == 'next'
            if isinstance(node.value, ast.Name):
                logjb( node.value.id, 'node.value.id')
                logjb(self.tree.symdict, 'self.tree.symdict' )
                sig = self.tree.symdict[node.value.id]
                logjbinspect( sig, 'sig', True)
                if hasattr(sig, '_name'):
                    self.SigAss = sig._name
            logjb( self.SigAss, 'self.SigAss', True)
            logjb( node.value, 'node.value')
            self.visit(node.value)
            node.obj = self.getObj(node.value)
        logjb( self.SigAss, 'self.SigAss')
        tracejbdedent()

    def getAttr(self, node):
        tracejb( "_ConvertVisitor: getAttr" )
        logjbinspect(node, 'node', True)
        if isinstance(node.value, ast.Subscript):
            self.setAttr(node)
            tracejbdedent()
            return

        if isinstance(node.value, ast.Attribute):
#             self.write( " Killroy" )
            logjbinspect( node.value, 'Killroy: node.value', True)
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
            
            logjbinspect(obj, 'obj', True)
            if isinstance(obj, _Signal):
                if node.attr == 'next':
                    sig = self.tree.symdict[node.value.id]
                    self.SigAss = obj._name
                    logjb( self.SigAss, 'self.SigAss next <-')
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
                logjbinspect(node.value, 'node.value', True)
                    
            if isinstance(obj, (_Signal, intbv)):
                if node.attr in ('min', 'max'):
                    self.write("%s" % node.obj)
                    
            if isinstance(obj, EnumType):
                assert hasattr(obj, node.attr)
                e = getattr(obj, node.attr)
                self.write(e._toVHDL())
            
        tracejbdedent()

    def visit_Assert(self, node):
        tracenode( 'Assert')
        tracejb( "_ConvertVisitor: visit_Assert" )
        # XXX
        self.write("assert ")
        self.visit(node.test)
        self.indent()
        self.writeline()
        self.write('report "*** AssertionError ***"')
        self.writeline()
        self.write("severity error;")
        self.dedent()
        tracejbdedent()
        tracenode()

    def visit_Assign(self, node):
        tracenode( 'Assign')
        tracejb( "_ConvertVisitor: visit_Assign" )
        logjbinspect(node , 'node')
        for item in inspect.getmembers(node):
            if item[0] in( 'targets', 'value'):
                logjbinspect(item[1] , 'node.' + item[0])
                for iitem in inspect.getmembers(item[1]):
                    if iitem[0] in( 'obj'):
                        logjbinspect(iitem[1] , 'node.' + item[0] + '.' + iitem[0])
        lhs = node.targets[0]
        rhs = node.value
        logjbinspect( lhs, 'lhs', True)
        for item in inspect.getmembers(lhs):
            if item[0] in( 'obj', 'value', 'vhd'):
                logjbinspect(item[1] , 'lhs.' + item[0])
                for iitem in inspect.getmembers(item[1]):
                    if iitem[0] in( 'obj'):
                        logjbinspect(iitem[1] , 'lhs.' + item[0] + '.' + iitem[0])

        logjbinspect( rhs, 'rhs', DO_INSPECT)
        for item in inspect.getmembers(rhs):
            if item[0] == 'obj':
                logjbinspect(item[1], 'rhs.obj')
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
                logjb( self.SigAss, 'self.SigAss')
                if self.SigAss:
                    self.write(' <= ')
                    self.SigAss = False
                    logjb( self.SigAss, 'self.SigAss <-')
                else:
                    logjb( 'SigAss is None?')
                    self.write(' := ')
                if isinstance(lhs.vhd, vhd_std_logic):
                    self.write("'%s';" % n)
                elif isinstance(lhs.vhd, vhd_int):
                    self.write("%s;" % n)
                else:
                    self.write('"%s";' % bin(n, size))
            self.dedent()
            self.writeline()
            self.write("end case;")
            tracejbdedent()
            tracenode()
            return

        elif isinstance(node.value, ast.ListComp):
            # skip list comprehension assigns for now
            tracejbdedent()
            tracenode()
            return

        # default behavior
        convOpen, convClose = "", ""
        logjbinspect( lhs.vhd, 'lhs.vhd')
        if isinstance(lhs.vhd, vhd_type):
            rhs.vhd = lhs.vhd
        self.isLhs = True
        self.visit( lhs )
        self.isLhs = False
        logjb( self.SigAss, 'self.SigAss')
        if self.SigAss:
            logjbinspect(lhs.value, 'lhs.value', True)
            if isinstance(lhs.value, ast.Name):
                sig = self.tree.symdict[lhs.value.id]
            self.write(' <= ')
            self.SigAss = False
        else:
            logjb( 'SigAss is None?')
            self.write(' := ')
        logjb( convOpen, 'convOpen')
        self.write(convOpen)
        # node.expr.target = obj = self.getObj(node.nodes[0])
        logjbinspect( rhs , 'rhs', True)
        self.visit(rhs)
        logjb( convClose, 'convClose')
        self.write(convClose)
        self.write(';')
        tracejbdedent()
        tracenode()

    def visit_AugAssign(self, node):
        tracenode( 'AugAssign')
        tracejb( "_ConvertVisitor: visit_AugAssign" )
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
        tracejbdedent()
        tracenode()

    def visit_Break(self, node):
        tracenode( 'Break')
        tracejb( "_ConvertVisitor: visit_Break" )
        logjbinspect(node, 'node', True)
        self.write("exit;")
        tracejbdedent()
        tracenode()

    def visit_Call(self, node):
        tracenode( 'Call')
        tracejb( "_ConvertVisitor: visit_Call" )
        fn = node.func
        logjb( fn , 'node.func', True)
        # assert isinstance(fn, astNode.Name)
        f = self.getObj(fn)
        logjb( f, 'self.getObj(fn)')

        if f is print:
            self.visit_Print(node)
            tracejbdedent()
            tracenode()
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
            tracejbdedent()
            tracenode()
            return
        
        elif f is now:
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            self.write(pre)
            self.write("(now / 1 ns)")
            self.write(suf)
            tracejbdedent()
            tracenode()
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
            tracejbdedent()
            tracenode()
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
            tracejbdedent()
            tracenode()
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
            tracejbdedent()
            tracenode()
            return
        
        elif (type(f) in class_types) and issubclass(f, Exception):
            self.write(f.__name__)
        elif f in (posedge, negedge):
            opening, closing = ' ', ''
            self.write(f.__name__)
        elif f is delay:
            self.visit(node.args[0])
            self.write(" * 1 ns")
            tracejbdedent()
            tracenode()
            return
        
        elif f is concat:
            pre, suf = self.inferCast(node.vhd, node.vhdOri)
            opening, closing =  "unsigned'(", ")"
            sep = " & "
        elif hasattr(node, 'tree'):
            pre, suf = self.inferCast(node.vhd, node.tree.vhd)
            fname = node.tree.name
        else:
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
        tracejbdedent()
        tracenode()

    def visit_Compare(self, node):
        tracenode( 'Compare')
        tracejb( "_ConvertVisitor: visit_Compare" )
        logjbinspect(node, 'node', DO_INSPECT)
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
        logjbinspect(node.left, 'node.left', DO_INSPECT)
        logjbinspect(node.left.obj, 'node.left.obj', DO_INSPECT)
        self.visit(node.left)
        op, right = node.ops[0], node.comparators[0]
        self.write(" %s " % opmap[type(op)])
        logjbinspect(right, 'right', DO_INSPECT)
        self.visit(right)
        self.write(suf)
        tracejbdedent()
        tracenode()

    def visit_Num(self, node):
        tracenode( 'Num')
        tracejb( "_ConvertVisitor: visit_Num" )
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
                self.write('unsigned\'("%s")' % bin(n, node.vhd.size))
        elif isinstance(node.vhd, vhd_signed):
            if abs(n) < 2**31:
                self.write("to_signed(%s, %s)" % (n, node.vhd.size))
            else:
                self.write('signed\'("%s")' % bin(n, node.vhd.size))
        else:
            if n < 0:
                self.write("(")
            self.write(n)
            if n < 0:
                self.write(")")
        tracejbdedent()
        tracenode()

    def visit_Str(self, node):
        tracenode( 'Str')
        tracejb( "_ConvertVisitor: visit_Str" )
        typemark = 'string'
        if isinstance(node.vhd, vhd_unsigned):
            typemark = 'unsigned'
        self.write("%s'(\"%s\")" % (typemark, node.s))
        tracejbdedent()
        tracenode()

    def visit_Continue(self, node, *args):
        tracenode( 'Continue')
        tracejb( "_ConvertVisitor: visit_Continue" )
        logjbinspect(node, 'node', DO_INSPECT)
        logjb( args )
        self.write("next;")
        tracejbdedent()
        tracenode()

    def visit_Expr(self, node):
        tracenode( 'Expr')
        tracejb( "_ConvertVisitor: visit_Expr" )
        expr = node.value
        # docstrings on unofficial places
        if isinstance(expr, ast.Str):
            doc = _makeDoc(expr.s, self.ind)
            self.write(doc)
            tracejbdedent()
            return
        # skip extra semicolons
        if isinstance(expr, ast.Num):
            tracejbdedent()
            return
        self.visit(expr)
        # ugly hack to detect an orphan "task" call
        if isinstance(expr, ast.Call) and hasattr(expr, 'tree'):
            self.write(';')
        tracejbdedent()
        tracenode()

    def visit_IfExp(self, node):
        tracenode( 'IfExpr')
        tracejb( "_ConvertVisitor: visit_IfExp" )
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
        tracejbdedent()
        tracenode()

    def visit_For(self, node):
        tracenode( 'For')
        tracejb( "_ConvertVisitor: visit_For" )
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
        tracejbdedent()
        tracenode()

    def visit_FunctionDef(self, node):
        tracenode( 'FunctionDef')
        tracenode( node.name, 'restart')
        tracejb( "_ConvertVisitor: visit_FunctionDef" )
        logjbinspect(node, 'node', DO_INSPECT)
        raise AssertionError("To be implemented in subclass")
        tracejbdedent()
        tracenode()

    def visit_If(self, node):
        tracenode( 'If')
        tracejb( "_ConvertVisitor: visit_If" )
        if node.ignore:
            tracejbdedent()
            tracenode()
            return
        # only map to VHDL case if it's a full case
        if node.isFullCase:
            self.mapToCase(node)
        else:
            self.mapToIf(node)
        tracejbdedent()
        tracenode()

    def mapToCase(self, node):
        tracejb( "_ConvertVisitor: mapToCase" )
        var = node.caseVar
        obj = self.getObj(var)
        self.write("case ")
        self.visit(var)
        self.write(" is")
        self.indent()
        for i, (test, suite) in enumerate(node.tests):
            logjb(i,'i', False)
            logjbinspect( test, 'test', True)
            logjbinspect( suite,'suite')
            self.writeline()
            item = test.case[1]
            logjbinspect(item, 'item', True)
            logjbinspect(obj, 'obj', True)
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
        tracejbdedent()

    def mapToIf(self, node):
        tracejb( "_ConvertVisitor: mapToIf" )
        first = True
        for test, suite in node.tests:
            logjb( test, 'test', True)
            logjb( suite,'suite')
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
        tracejbdedent()

    def visit_ListComp(self, node):
        tracenode( 'ListComp')
        tracejb( "_ConvertVisitor: visit_ListComp" )
        logjbinspect(node, 'node', DO_INSPECT)
        tracejbdedent()
        tracenode()
        pass # do nothing


    def visit_Module(self, node):
        tracenode( 'Module')
        tracejb( "_ConvertVisitor: visit_Module" )
        for stmt in node.body:
            self.visit(stmt)
        tracejbdedent()
        tracenode()

    def visit_NameConstant(self, node):
        tracenode( 'NameConstant')
        node.id = str(node.value)
        self.getName(node)
        tracenode()

    def visit_Name(self, node):
        tracenode( 'Name')
        tracejb( "_ConvertVisitor: visit_Name" )
        logjbinspect( node, 'node', True)
        if isinstance(node.ctx, ast.Store):
            self.setName(node)
        else:
            self.getName(node)
        tracejbdedent()
        tracenode()

    def setName(self, node):
        tracejb( "_ConvertVisitor: setName" )
        self.write(node.id)
        tracejbdedent()

    def getName(self, node):
        tracejb( "_ConvertVisitor: getName" )
        n = node.id
        logjbinspect( node , 'node', True)
        logjbinspect( node.obj , 'node.obj', True)
        logjb(n, 'node.id')
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
            logjb(obj, 'obj - self.tree.vardict[n]')
            ori = inferVhdlObj(obj)
            pre, suf = self.inferCast(node.vhd, ori)
            s = "%s%s%s" % (pre, s, suf)

        elif n in self.tree.argnames:
            assert n in self.tree.symdict
            obj = self.tree.symdict[n]
            logjbinspect(obj, 'obj - self.tree.argnames', DO_INSPECT)
            vhd = inferVhdlObj(obj)
            if isinstance(vhd, vhd_std_logic) and isinstance(node.vhd, vhd_boolean):
                s = "(%s = '1')" %  n
            else:
                s = n
                
        elif n in self.tree.symdict:
            obj = self.tree.symdict[n]
            logjbinspect(obj, 'obj - self.tree.symdict[n]', True)
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
                        s = 'unsigned\'("%s")' % bin(obj, node.vhd.size)
                elif isinstance(node.vhd, vhd_signed):
                    if abs(obj) < 2** 31:
                        s = "to_signed(%s, %s)" % (obj, node.vhd.size)
                    else:
                        s = 'signed\'("%s")' % bin(obj, node.vhd.size)
                            
            elif isinstance(obj, _Signal):
                s = str(obj)
                ori = inferVhdlObj(obj)
                pre, suf = self.inferCast(node.vhd, ori)
                s = "%s%s%s" % (pre, s, suf)
                
            elif _isMem(obj):
                m = _getMemInfo(obj)
                assert m.name
                s = m.name
                logjb(s, '_isMem(obj)')

            elif isinstance(obj, EnumItemType):
                s = obj._toVHDL()
                
            elif (type(obj) in class_types) and issubclass(obj, Exception):
                s = n
                
            elif isinstance(obj, list):
                logjbinspect(obj, 'obj is list')
                s = n
#                 self.raiseError(node, _error.UnsupportedType, "%s, %s" % (n, type(obj)))

            # dead code?
            elif isinstance( obj, Array):
                logjbinspect(obj, 'obj is Array')
                s = n
                
            else:
                self.raiseError(node, _error.UnsupportedType, "%s, %s" % (n, type(obj)))
        else:
            raise AssertionError("name ref: %s" % n)
        self.write(s)
        tracejbdedent()

    def visit_Pass(self, node):
        tracenode( 'Pass')
        tracejb( "_ConvertVisitor: visit_Pass" )
        logjbinspect(node, 'node', DO_INSPECT)
        self.write("null;")
        tracejbdedent()
        tracenode()

    def visit_Print(self, node):
        tracenode( 'Print')
        tracejb( "_ConvertVisitor: visit_Print" )
        argnr = 0
        for s in node.format:
            logjb(s, 's')
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
        tracejbdedent()
        tracenode()

    def visit_Raise(self, node):
        tracenode( 'Raise')
        tracejb( "_ConvertVisitor: visit_Raise" )
        logjbinspect(node, 'node', DO_INSPECT)
        self.write('assert False report "End of Simulation" severity Failure;')
        tracejbdedent()
        tracenode()

    def visit_Return(self, node):
        tracenode( 'Return')
        tracejb( "_ConvertVisitor: visit_Return" )
        logjbinspect(node, 'node', DO_INSPECT)
        tracejbdedent()
        tracenode()
        pass


    def visit_Subscript(self, node):
        tracenode( 'Subscript')
        tracejb( "_ConvertVisitor: visit_Subscript" )
        logjbinspect( node, 'node', DO_INSPECT)
        logjbinspect( node.obj, 'node.obj', DO_INSPECT)
        if isinstance(node.slice, ast.Slice):
            self.accessSlice(node)
        else:
            self.accessIndex(node)
        tracejbdedent()
        tracenode()

    def accessSlice(self, node):
        tracejb( "toVHDL(): _ConvertVisitor: accessSlice" )
        if isinstance(node.value, ast.Call) and \
           node.value.func.obj in (intbv, modbv) and \
           _isConstant(node.value.args[0], self.tree.symdict):
            logjb(node, 'special?')
            c = self.getVal(node)._val
            pre, post = "", ""
            if isinstance(node.obj, Array):
                logjb( node.obj, 'accessSlice isArray 1')
                
            if node.vhd.size <= 30:
                if isinstance(node.vhd, vhd_unsigned):
                    pre, post = "to_unsigned(", ", %s)" % node.vhd.size
                elif isinstance(node.vhd, vhd_signed):
                    pre, post = "to_signed(", ", %s)" % node.vhd.size
            else:
                if isinstance(node.vhd, vhd_unsigned):
                    pre, post = "unsigned'(", ")"
                    c = '"%s"' % bin(c, node.vhd.size)
                elif isinstance(node.vhd, vhd_signed):
                    pre, post = "signed'(", ")"
                    c = '"%s"' % bin(c, node.vhd.size)
            self.write(pre)
            self.write("%s" % c)
            self.write(post)
            tracejbdedent()
            return
#         
# #         logjb( node.vhd, 'node.vhd', True)
# #         logjb( node.vhdOri, 'node.vhdOri')
#         pre, suf = '', ''
#         if not isinstance(node.obj, Array):
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        if isinstance(node.value.vhd, vhd_signed) and isinstance(node.ctx, ast.Load):
            pre = pre + "unsigned("
            suf = ")" + suf
        logjb( pre + ', ' + suf, 'pre, suf augmented')
        self.write(pre)
        logjb( node.value.__class__ , 'visiting', True)
        logjb( node.value.__class__.__name__ )
        logjbinspect(node, 'node', True)
        logjbinspect(node.obj, 'node.obj', True)
        logjb('visiting node.value')
        self.visit(node.value) # this brings us to self.visit_Name, onto self.getName where the cast is enforced in case of numeric_ports == False
        logjb('returned from visiting node.value')
        lower, upper = node.slice.lower, node.slice.upper
        if isinstance(node.obj, Array):
            logjb( node.obj , 'accessSlice isArray 2')
            logjb( lower, 'lower', True)
            logjb( upper, 'upper')
            if lower is None and upper is None:
                self.write(suf)
                tracejbdedent()
                return
            # an array is specified (0 to n)
            self.write("(")
            if lower is None:
                self.write("0")
            else:
                self.visit(lower)
            self.write(" to ")
            if upper is None:
                logjb( self.getVal(node.slice.lower) + node.obj._sizes[0], 'upper is None')
                self.write("{}". format( self.getVal(node.slice.lower) + node.obj._sizes[0] ))    # unfortunately ._sizes[0] is the 'sliced' size
            else:
                self.visit(upper)
            
            self.write(" - 1)")   
            self.write(suf)

        else:
            logjbinspect( node.obj, 'node.obj', True)
            logjb( upper, 'upper', True)
            logjb( lower, 'lower')
            # special shortcut case for [:] slice
            if lower is None and upper is None:
                self.write(suf)
                tracejbdedent()
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
        tracejbdedent()

    def accessIndex(self, node):
        tracejb( "_ConvertVisitor: accessIndex" )
        logjb( node, 'node', True )
        logjb( node.value, '.value' )
        logjbinspect( node.slice.value, '.slice.value' )
#         pre, suf = '', ''
#         if not isinstance(node.value, Array):
        pre, suf = self.inferCast(node.vhd, node.vhdOri)
        logjbinspect(node.value, 'node.value')
        logjbinspect(node.value.obj, 'node.value.obj')
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
        tracejbdedent()

    def visit_stmt(self, body):
#         tracenode( 'stmt')
        tracejb( "_ConvertVisitor: visit_stmt" )
        for stmt in body:
            self.writeline()
            self.visit(stmt)
            # ugly hack to detect an orphan "task" call
            if isinstance(stmt, ast.Call) and hasattr(stmt, 'tree'):
                self.write(';')
        tracejbdedent()
#         tracenode()

    def visit_Tuple(self, node):
        tracenode( 'Tuple')
        tracejb( "_ConvertVisitor: visit_Tuple" )
        assert self.context != None
        sep = ", "
        tpl = node.elts
        self.visit(tpl[0])
        for elt in tpl[1:]:
            logjb( elt, 'elt')
            self.write(sep)
            self.visit(elt)
        tracejbdedent()
        tracenode()

    def visit_While(self, node):
        tracenode( 'While')
        tracejb( "_ConvertVisitor: visit_While" )
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
        tracejbdedent()
        tracenode()

    def visit_Yield(self, node):
        tracenode( 'Yield')
        tracejb( "_ConvertVisitor: visit_Yield" )
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
        tracejbdedent()
        tracenode()

    def manageEdges(self, ifnode, senslist):
        tracejb( "_ConvertVisitor: manageEdges" )
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
            # print ifnode
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
        tracejbdedent()
        return senslist


class _ConvertAlwaysVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf


    def visit_FunctionDef(self, node):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertAlwaysVisitor: visit_FunctionDef" )
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
        tracejbdedent()


class _ConvertInitialVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf


    def visit_FunctionDef(self, node):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertInitialVisitor: visit_FunctionDef" )
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
        tracejbdedent()


class _ConvertAlwaysCombVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf


    def visit_FunctionDef(self, node):
        # a local function works nicely too
        def compressSensitivityList(senslist):
            ''' reduce spelled out list items like [*name*(0), *name*(1), ..., *name*(n)] to just *name*'''
            print( senslist )
            r = []
            for item in senslist:
                print( repr( item._name ))
#                 if item._name is not None:
                name = item._name.split('(',1)[0]
#                 else:
#                     # it may be in a list or array
#                     name = None
                if name not in r:
                    r.append( name ) # note that the list now contains names and not Signals, but we are interested in the strings anyway ...
            return r

        tracenode( node.name, 'restart')
        tracejb( "_ConvertAlwaysCombVisitor: visit_FunctionDef" )
        self.writeDoc(node)
#         print( self.tree.senslist )
        senslist = compressSensitivityList( self.tree.senslist )
        logjb( senslist, 'compressed sensivity list')
        self.write("%s: process (" % self.tree.name)
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
        self.visit_stmt(node.body)
        self.dedent()
        self.writeline()
        self.write("end process %s;" % self.tree.name)
        self.dedent()
        self.writeline(2)
        tracejbdedent()


class _ConvertSimpleAlwaysCombVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf


    def visit_Attribute(self, node):
        tracejb( "_ConvertSimpleAlwaysCombVisitor: visit_Attribute" )
        if isinstance(node.ctx, ast.Store):
            self.SigAss = True
            if isinstance(node.value, ast.Name):
                sig = self.tree.symdict[node.value.id]
                self.SigAss = sig._name
            self.visit(node.value)
        else:
            self.getAttr(node)

        logjb( self.SigAss, 'self.SigAss')
        tracejbdedent()

    def visit_FunctionDef(self, node, *args):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertSimpleAlwaysCombVisitor: visit_FunctionDef" )
        logjbinspect(node, 'node', DO_INSPECT)
        logjb( args )
        self.writeDoc(node)
        self.visit_stmt(node.body)
        self.writeline(2)
        tracejbdedent()


class _ConvertAlwaysDecoVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf


    def visit_FunctionDef(self, node, *args):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertAlwaysDecoVisitor: visit_FunctionDef" )
        logjbinspect(node, 'node', DO_INSPECT)
        logjb( args )
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
        tracejbdedent()


def _convertInitVal(reg, init):
    tracejb( "_convertInitVal" )
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
            v = '%s%s\'"%s"%s' % (pre, vhd_tipe, bin(init, len(reg)), suf)
    else:
        assert isinstance(init, EnumItemType)
        v = init._toVHDL()
    tracejbdedent()
    return v


class _ConvertAlwaysSeqVisitor(_ConvertVisitor):

    def __init__(self, tree, blockBuf, funcBuf):
        _ConvertVisitor.__init__(self, tree, blockBuf)
        self.funcBuf = funcBuf


    def visit_FunctionDef(self, node, *args):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertAlwaysSeqVisitor: visit_FunctionDef" )
        logjbinspect(node, 'node', True)
        logjb( args )
        logjbinspect(self.tree, 'self.tree', True)
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
        tracejbdedent()


class _ConvertFunctionVisitor(_ConvertVisitor):

    def __init__(self, tree, funcBuf):
        _ConvertVisitor.__init__(self, tree, funcBuf)
        self.returnObj = tree.returnObj
        self.returnLabel = _Label("RETURN")


    def writeOutputDeclaration(self):
        tracejb( "_ConvertFunctionVisitor: writeOutputDeclaration" )
        self.write(self.tree.vhd.toStr(constr=False))
        tracejbdedent()

    def writeInputDeclarations(self):
        tracejb( "_ConvertFunctionVisitor: writeInputDeclarations" )
        endchar = ""
        for name in self.tree.argnames:
#             logjb( name, 'name')
            self.write(endchar)
            endchar = ";"
            obj = self.tree.symdict[name]
            self.writeline()
            self.writeDeclaration(obj, name, dir="in", constr=False, endchar="")
        tracejbdedent()

    def visit_FunctionDef(self, node):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertFunctionVisitor: visit_FunctionDef" )
        logjbinspect(node, 'node', True )
        logjb( self.tree.name )
        self.write("function %s(" % self.tree.name)
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
        tracejbdedent()

    def visit_Return(self, node):
        tracejb( "_ConvertFunctionVisitor: visit_Return" )
        self.write("return ")
        logjb(self.tree.vhd, 'self.tree.vhd')
        node.value.vhd = self.tree.vhd
        self.visit(node.value)
        self.write(";")
        tracejbdedent()


class _ConvertTaskVisitor(_ConvertVisitor):

    def __init__(self, tree, funcBuf):
        _ConvertVisitor.__init__(self, tree, funcBuf)
        self.returnLabel = _Label("RETURN")


    def writeInterfaceDeclarations(self):
        tracejb( "_ConvertTaskVisitor: writeInterfaceDeclarations" )
        endchar = ""
        for name in self.tree.argnames:
#             logjb( name , 'name')
            self.write(endchar)
            endchar = ";"
            obj = self.tree.symdict[name]
            moutput = name in self.tree.outputs
            minput = name in self.tree.inputs
            inout = minput and moutput
            direction = (inout and "inout") or (moutput and "out") or "in"
            self.writeline()
            self.writeDeclaration(obj, name, dir=direction, constr=False, endchar="")
        tracejbdedent()

    def visit_FunctionDef(self, node):
        tracenode( node.name, 'restart')
        tracejb( "_ConvertTaskVisitor: visit_FunctionDef" )
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
        tracejbdedent()




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


class _loopInt(int):
    pass


def maxType(o1, o2):
    tracejb( "maxType" )
    tracejbdedent()
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
    tracejb( "inferVhdlObj" )
    logjbinspect( obj , 'obj' , True)
    vhd = None
    if (isinstance(obj, _Signal) and obj._type is intbv) or \
       isinstance(obj, intbv):
        ls = getattr(obj, 'lenStr', False)
        if obj.min is None or obj.min < 0:
            vhd = vhd_signed(size=len(obj), lenStr=ls)
        else:
            vhd = vhd_unsigned(size=len(obj), lenStr=ls)
    elif (isinstance(obj, _Signal) and obj._type is bool) or \
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
            logjb( obj, 'inferring List')
            _, _, _, element = m1Dinfo( obj )
        else:    
            logjb( obj, 'inferring Array')
            element = obj.element

        if (isinstance(element, _Signal) and element._type is intbv):
            ls = getattr(element, 'lenStr', False)
            if element.min is not None and element.min < 0:
                vhd = vhd_signed(size=len(element), lenStr=ls)
            else:
                vhd = vhd_unsigned(size=len(element), lenStr=ls)
        elif (isinstance(element, _Signal) and element._type is bool):
            vhd = vhd_std_logic()
        else:
            # defaulting?
            pass
        
    elif isinstance(obj, StructType):
        logjb( obj, 'inferring StructType')
        # need the member name?
        if attr is not None:
            refs = vars( obj )
            element = refs[attr]
            if (isinstance(element, _Signal) and element._type is intbv):
                ls = getattr(element, 'lenStr', False)
                if element.min is not None and element.min < 0:
                    vhd = vhd_signed(size=len(element), lenStr=ls)
                else:
                    vhd = vhd_unsigned(size=len(element), lenStr=ls)
            elif (isinstance(element, _Signal) and element._type is bool):
                vhd = vhd_std_logic()
            else:
                # defaulting?
                pass
        else:
            pass
    
    logjbinspect( vhd, 'inferVhdlObj inferred', True)
    tracejbdedent()
    return vhd


def maybeNegative(vhd):
#     tracejb( "maybeNegative" )
#     tracejbdedent()
    if isinstance(vhd, vhd_signed):
        return True
    if isinstance(vhd, vhd_int) and not isinstance(vhd, vhd_nat):
        return True
    return False

class _AnnotateTypesVisitor(ast.NodeVisitor, _ConversionMixin):

    def __init__(self, tree):
        self.tree = tree


    def visit_FunctionDef(self, node):
        tracejb( "_AnnotateTypesVisitor: visit_FunctionDef" )
        tracenode( node.name, 'restart')
#         logjb( node.name )
        # don't visit arguments and decorators
        for stmt in node.body:
            logjbinspect( stmt, 'stmt', True)
            self.visit(stmt)
        tracejbdedent()

    def visit_Attribute(self, node):
        tracenode( 'Attribute')
        tracejb( "_AnnotateTypesVisitor: visit_Attribute" )
        logjbinspect( node, 'node', True)
        logjbinspect( node.value, 'node.value', True)
#         logjbinspect( node.value.obj, 'node.value.obj', True)
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
                logjb( 'Starting an starget chain')
                node.value.starget = node.value.obj
            else:
                node.value.starget = node.obj
        
        self.generic_visit(node)
        logjbinspect( node.value, 'node.value', True)
        node.vhd = copy(node.value.vhd)
        node.vhdOri = copy(node.vhd)
        logjbinspect( node, 'node', True)
        tracejbdedent()
        tracenode()

    def visit_Assert(self, node):
        tracenode( 'Assert')
        tracejb( "_AnnotateTypesVisitor: visit_Assert" )
        logjb( node, 'node')
        self.visit(node.test)
        node.test.vhd = vhd_boolean()
        tracejbdedent()
        tracenode()

    def visit_AugAssign(self, node):
        tracenode( 'AugAssign')
        tracejb( "_AnnotateTypesVisitor: visit_AugAssign" )
        logjb( node, 'node')
        self.visit(node.target)
        self.visit(node.value)
        logjb( node.op, 'node.op')
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
        tracejbdedent()
        tracenode()

    def visit_Call(self, node):
        tracenode( 'Call')
        tracejb( "_AnnotateTypesVisitor: visit_Call" )
        logjb( node, 'node')
        fn = node.func
        # assert isinstance(fn, astNode.Name)
        f = self.getObj(fn)
        
        logjb( f, 'visit_Call > f')
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
        logjbinspect(node.vhd, 'node.vhd', True)
        tracejbdedent()
        tracenode()

    def visit_Compare(self, node):
        tracenode( 'Compare')
        tracejb( "_AnnotateTypesVisitor: visit_Compare" )
        logjb( node, 'node')
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
        tracejbdedent()
        tracenode()

    def visit_Str(self, node):
        tracenode( 'Str')
        tracejb( "_AnnotateTypesVisitor: visit_Str" )
        logjb( node, 'node')
        node.vhd = vhd_string()
        node.vhdOri = copy(node.vhd)
        tracejbdedent()
        tracenode()

    def visit_Num(self, node):
        tracenode( 'Num')
        tracejb( "_AnnotateTypesVisitor: visit_Num" )
        logjbinspect( node, 'node', True)
        if node.n < 0:
            node.vhd = vhd_int()
        else:
            node.vhd = vhd_nat()
        node.vhdOri = copy(node.vhd)
        tracejbdedent()
        tracenode()

    def visit_For(self, node):
        tracejb( "_AnnotateTypesVisitor: visit_For" )
        tracenode( 'For')
        logjb( node, 'node')
        var = node.target.id
        # make it possible to detect loop variable
        self.tree.vardict[var] = _loopInt(-1)
        self.generic_visit(node)
        tracejbdedent()
        tracenode()

    def visit_NameConstant(self, node):
        tracenode( 'NameConstant')
        node.vhd = inferVhdlObj(node.value)
        node.vhdOri = copy(node.vhd)
        tracenode()
    
    def visit_Name(self, node):
        # is a terminal
        tracenode( 'Name')
        tracejb( "_AnnotateTypesVisitor: visit_Name" )
        logjbinspect( node, 'node', True)
        logjb( node.id, '.id')
        if node.id in self.tree.vardict:
            node.obj = self.tree.vardict[node.id]
        logjbinspect( node.obj, 'node.obj', True)        
        if hasattr(node, 'starget'):
            logjb( 'starget found')
            node.vhd = inferVhdlObj(node.starget)
        else:
            node.vhd = inferVhdlObj(node.obj)
#         node.vhd = inferVhdlObj(node.obj)
        node.vhdOri = copy(node.vhd)
        tracejbdedent()
        tracenode()

    def visit_BinOp(self, node):
        tracenode( 'BinOp')
        tracejb( "_AnnotateTypesVisitor: visit_BinOp" )
        logjb( node, 'node')
        self.generic_visit(node)
        if isinstance(node.op, (ast.LShift, ast.RShift)):
            self.inferShiftType(node)
        elif isinstance(node.op, (ast.BitAnd, ast.BitOr, ast.BitXor)):
            self.inferBitOpType(node)
        elif isinstance(node.op, ast.Mod) and isinstance(node.left, ast.Str): # format string
            pass
        else:
            self.inferBinOpType(node)
        tracejbdedent()
        tracenode()

    def inferShiftType(self, node):
        tracejb( "_AnnotateTypesVisitor: inferShiftType" )
        logjb( node, 'node')
        node.vhd = copy(node.left.vhd)
        node.right.vhd = vhd_nat()
        node.vhdOri = copy(node.vhd)
        tracejbdedent()

    def inferBitOpType(self, node):
        tracejb( "_AnnotateTypesVisitor: inferBitOpType" )
        logjb( node, 'node')
        obj = maxType(node.left.vhd, node.right.vhd)
        node.vhd = node.left.vhd = node.right.vhd = obj
        node.vhdOri = copy(node.vhd)
        tracejbdedent()

    def inferBinOpType(self, node):
        tracejb( "_AnnotateTypesVisitor: inferBinOpType" )
        logjb( node, 'node')
        logjb(node.left.vhd , 'node.left.vhd', True)
        logjb(node.right.vhd, 'node.right.vhd')
        left, op, right = node.left, node.op, node.right
        
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
                
        logjb(left.vhd , 'left.vhd', True)
        logjb(right.vhd, 'right.vhd')              
         
        l, r = left.vhd, right.vhd
        ls = l.size
        rs = r.size
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
                logjb(r._type._name)
                logjb( node.vhd )
        elif isinstance(l, (vhd_signed, vhd_int)) and isinstance(r, (vhd_signed, vhd_int)):
            node.vhd = vhd_signed(s)
        elif isinstance(l, (vhd_unsigned, vhd_int)) and isinstance(r, (vhd_unsigned, vhd_int)):
            node.vhd = vhd_unsigned(s)
        else:
            node.vhd = vhd_int()
            
        node.vhdOri = copy(node.vhd)
        logjbinspect(node.vhd, 'node.vhd', True)
        tracejbdedent()

    def visit_BoolOp(self, node):
        tracenode( 'BoolOp')
        tracejb( "_AnnotateTypesVisitor: visit_BoolOp" )
        logjb( node.values )
        self.generic_visit(node)
        for n in node.values:
            n.vhd = vhd_boolean()
        node.vhd = vhd_boolean()
        node.vhdOri = copy(node.vhd)
        tracejbdedent()
        tracenode()

    def visit_If(self, node):
        tracenode( 'If')
        tracejb( "_AnnotateTypesVisitor: visit_If" )
        logjb( node, 'node')
        if node.ignore:
            tracejbdedent()
            return
        logjb( node.test)
        self.generic_visit(node)
        for test, _ in node.tests:
            test.vhd = vhd_boolean()
        tracejbdedent()
        tracenode()

    def visit_IfExp(self, node):
        tracenode( 'IfExp')
        tracejb( "_AnnotateTypesVisitor: visit_IfExp" )
        logjb( node, 'node')
        self.generic_visit(node) # this will visit the 3 ast.Name objects
        node.test.vhd = vhd_boolean()
        logjb('returned from generic_visit')
        tracejbdedent()
        tracenode()

    def visit_ListComp(self, node):
        tracenode( 'ListComp')
        tracejb( "_AnnotateTypesVisitor: visit_ListComp" )
        logjbinspect(node, 'node', DO_INSPECT)
        tracejbdedent()
        tracenode()
        pass # do nothing


    def visit_Subscript(self, node):
        tracenode( 'Subscript')
        tracejb( "_AnnotateTypesVisitor: visit_Subscript" )
        logjb( node, 'node')
        if isinstance(node.slice, ast.Slice):
            self.accessSlice(node)
        else:
            self.accessIndex(node)
        tracejbdedent()
        tracenode()

    def accessSlice(self, node):
        tracejb( "_AnnotateTypesVisitor: accessSlice" )
        logjb( node, 'node')
        self.generic_visit(node)
        logjbinspect( node, 'node', True)
        
        if isinstance(node.obj, intbv) or (isinstance(node.obj, _Signal) and isinstance(node.obj.val, intbv)):
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
            logjb( 'isArray _AnnotateTypesVisitor: accessSlice')
            
            if isinstance(node.obj._dtype, bool):
                node.vhd = vhd_std_logic()
            elif isinstance(node.obj._dtype, intbv):
                node.vhd = vhd_unsigned(node.obj._nrbits)
            else:
                print( "???")
        

            

        
        node.vhdOri = copy(node.vhd)
        
        logjbinspect( node, 'node', True)
        logjbinspect( node.vhd, 'node.vhd', True)
        tracejbdedent()

    def accessIndex(self, node):
        tracejb( "_AnnotateTypesVisitor: accessIndex" )
        logjbinspect( node, 'node', True)
        logjbinspect( node.value, 'node.value', True)
        logjbinspect( node.value.obj, 'node.value.obj', True)
        
        self.generic_visit(node)
        
        logjbinspect( node.value.obj, 'node.value.obj after visit(node)', True)
        
        node.vhd = vhd_std_logic() # XXX default
        node.slice.value.vhd = vhd_int()
        obj = node.value.obj
        if isinstance(obj, list):
            assert len(obj)
            _, _, _, element = m1Dinfo( obj )
            node.vhd = inferVhdlObj(element)
            
        elif isinstance(obj, Array):
            logjb(obj.element, 'accessIndex isArray' )
            node.vhd = inferVhdlObj(obj.element)
            
        elif isinstance(obj, _Ram):
            node.vhd = inferVhdlObj(obj.elObj)
            
        elif isinstance(obj, _Rom):
            node.vhd = vhd_int()
            
        elif isinstance(obj, intbv):
            logjb( 'isIntbv')
            node.vhd = vhd_std_logic()
            
        else:
            logjb( 'vhd_std_logic() # XXX default')
            logjbinspect(obj, 'obj', True)

        node.vhdOri = copy(node.vhd)
        logjb(node.vhd, 'node.vhd')
        tracejbdedent()

    def visit_UnaryOp(self, node):
        tracenode( 'UnaryOp')
        tracejb( "_AnnotateTypesVisitor: visit_UnaryOp" )
        logjb( node, 'node')
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
        tracejbdedent()
        tracenode()

    def visit_While(self, node):
        tracenode( 'While')
        tracejb( "_AnnotateTypesVisitor: visit_While" )
        logjb( node, 'node')
        self.generic_visit(node)
        node.test.vhd = vhd_boolean()
        tracejbdedent()
        tracenode()


def _annotateTypes(genlist):
    tracejb( genlist, "_annotateTypes" )
#     logjb( genlist, 'genlist')
    for tree in genlist:
        logjb( tree , 'tree')
        if isinstance(tree, _UserVhdlCode):
            continue
        v = _AnnotateTypesVisitor(tree)
        v.visit(tree)
    tracejbdedent()








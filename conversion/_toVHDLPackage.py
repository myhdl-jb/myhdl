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

import myhdl

_version = myhdl.__version__.replace('.','')
_shortversion = _version.replace('dev','')

_package = """\
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package pck_myhdl_%(version)s is

    attribute enum_encoding: string;

    function stdl (arg: boolean) return std_logic;

    function stdl (arg: integer) return std_logic;

    function to_unsigned (arg: boolean; size: natural) return unsigned;

    function to_signed (arg: boolean; size: natural) return signed;

    function to_integer(arg: boolean) return integer;

    function to_integer(arg: std_logic) return integer;

    function to_unsigned (arg: std_logic; size: natural) return unsigned;

    function to_signed (arg: std_logic; size: natural) return signed;

    function bool (arg: std_logic) return boolean;

    function bool (arg: unsigned) return boolean;

    function bool (arg: signed) return boolean;

    function bool (arg: integer) return boolean;

    function "-" (arg: unsigned) return signed;

    function tern_op(cond: boolean; if_true: std_logic; if_false: std_logic) return std_logic;

    function tern_op(cond: boolean; if_true: unsigned; if_false: unsigned) return unsigned;

    function tern_op(cond: boolean; if_true: signed; if_false: signed) return signed;
   
	-- normalise a slice of the v[x ..y] to the r[n..0] form
    -- e.g v[8..1] will become r[7..0] with the original(8) into the new (7) place
    -- a v[1..8] will also become r[7..0] but  have v(8) placed into r(0)
    -- so if you deliberately (or forced by the synthesiser) have a v(1 to 8) vector this function will
    -- re-adjust the ordering with the MSB at the left side
    -- (use reverse_slv if you effectively want to swap the bits)
    -- useful to force a 'concatenation' into this
    -- normalise_slv( v : std_logic_vector)
    function normalise( v : std_logic_vector) return std_logic_vector ;
    function normalise( v : unsigned) return unsigned ;

end pck_myhdl_%(version)s;


package body pck_myhdl_%(version)s is

    function stdl (arg: boolean) return std_logic is
    begin
        if arg then
            return '1';
        else
            return '0';
        end if;
    end function stdl;

    function stdl (arg: integer) return std_logic is
    begin
        if arg /= 0 then
            return '1';
        else
            return '0';
        end if;
    end function stdl;


    function to_unsigned (arg: boolean; size: natural) return unsigned is
        variable res: unsigned(size-1 downto 0) := (others => '0');
    begin
        if arg then
            res(0):= '1';
        end if;
        return res;
    end function to_unsigned;

    function to_signed (arg: boolean; size: natural) return signed is
        variable res: signed(size-1 downto 0) := (others => '0');
    begin
        if arg then
            res(0) := '1';
        end if;
        return res;
    end function to_signed;

    function to_integer(arg: boolean) return integer is
    begin
        if arg then
            return 1;
        else
            return 0;
        end if;
    end function to_integer;

    function to_integer(arg: std_logic) return integer is
    begin
        if arg = '1' then
            return 1;
        else
            return 0;
        end if;
    end function to_integer;

    function to_unsigned (arg: std_logic; size: natural) return unsigned is
        variable res: unsigned(size-1 downto 0) := (others => '0');
    begin
        res(0):= arg;
        return res;
    end function to_unsigned;

    function to_signed (arg: std_logic; size: natural) return signed is
        variable res: signed(size-1 downto 0) := (others => '0');
    begin
        res(0) := arg;
        return res;
    end function to_signed;

    function bool (arg: std_logic) return boolean is
    begin
        return arg = '1';
    end function bool;

    function bool (arg: unsigned) return boolean is
    begin
        return arg /= 0;
    end function bool;

    function bool (arg: signed) return boolean is
    begin
        return arg /= 0;
    end function bool;

    function bool (arg: integer) return boolean is
    begin
        return arg /= 0;
    end function bool;

    function "-" (arg: unsigned) return signed is
    begin
        return - signed(resize(arg, arg'length+1));
    end function "-";

    function tern_op(cond: boolean; if_true: std_logic; if_false: std_logic) return std_logic is
    begin
        if cond then
            return if_true;
        else
            return if_false;
        end if;
    end function tern_op;

    function tern_op(cond: boolean; if_true: unsigned; if_false: unsigned) return unsigned is
    begin
        if cond then
            return if_true;
        else
            return if_false;
        end if;
    end function tern_op;

    function tern_op(cond: boolean; if_true: signed; if_false: signed) return signed is
    begin
        if cond then
            return if_true;
        else
            return if_false;
        end if;
    end function tern_op;



    function normalise( v : std_logic_vector)
        return std_logic_vector
        is
            variable r : std_logic_vector( v'range ) ;
            variable j : natural ;
        begin
            j := 0 ;
            if v'left > v'right then
                for i in v'right to v'left loop
                    r(j) := v(i) ;
                    j := j + 1 ;
                end loop ;
            else
                for i in v'right downto v'left loop
                    r(j) := v(i) ;
                    j := j + 1 ;
                end loop ;
            end if ;
            return r ;
        end function ;

    function normalise( v : unsigned)
        return unsigned
        is
        begin
            return unsigned( normalise( std_logic_vector( v )));
        end function;

    function normalise( v : signed)
        return signed
        is
        begin
            return signed( normalise( std_logic_vector( v )));
        end function;


end pck_myhdl_%(version)s;

""" % {'version' : _shortversion}

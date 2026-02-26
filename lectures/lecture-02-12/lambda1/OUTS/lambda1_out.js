// Thu Feb 12 01:34:22 PM EST 2026
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
// HX-2024-06-22:
// ATS3-XANADU/srcgen2/xats2js/srcgen1
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.

'use strict';

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
let XATSTOP0 = undefined
//
////////////////////////////////////////////////////////////////////////.
//
let XATSINT0 = (i0) => i0
let XATSINT1 = (i0) => i0
//
let XATSBTF0 = (b0) => b0
let XATSBOOL = (b0) => b0
//
let XATSFLT0 = (f0) => f0
let XATSFLT1 = (f0) => f0
/*
let XATSSFLT = (sf) => sf
let XATSDFLT = (df) => df
*/
let XATSSTR0 = (cs) => cs
let XATSSTRN = (cs) => cs
//
let XATSCNUL = (  ) => (0)
let XATSCHR1 = (  ) => (0)
//
let XATSCHR0 =
    (ch) => ch.charCodeAt(0)
let XATSCHAR =
    (ch) => ch.charCodeAt(0)
let XATSCHR2 =
    (ch) => ch.charCodeAt(0)
//
let XATSCHR3 = (ch) => {
    var c1 // current one
    c1 = ch.charCodeAt(1)
    if (c1 < 48||c1 > 55)
    {
      return c1 ; // ascii
    } else {
	var i1 = 2;
	var d1 = (c1 - 48);
	while (i1 < ch.length) {
	    c1 = ch.charCodeAt(i1);
	    if (c1===39) // SQUOTE=39
	    {
		return d1; // ascii
	    } else {
		d1 = 8*d1 + (c1 - 48)
	    }
	}
	return d1 ; // ascii code of [ch]
    }
}
//
////////////////////////////////////////////////////////////////////////.
/*
HX: this is historic:
let XATSVAR0 = () => [null]
let XATSVAR1 = (init) => [init]
let XATSFLAT = (addr) => addr[0]
*/
////////////////////////////////////////////////////////////////////////.

let XATSDAPP = (dapp) => dapp
let XATSCAPP = (_, capp) => capp
let XATSCAST = (_, args) => args[0]

////////////////////////////////////////////////////////////////////////.
//
let XATSPCON =
  (pcon, argi) => pcon[argi+1]
//
let XATSPFLT = (pflt) => pflt
let XATSPROJ = (proj) => proj
let XATSP0RJ = (p0rj) => p0rj
let XATSP1RJ = (_, p1rj) => p1rj
let XATSP1CN = (_, p1cn) => p1cn
//
////////////////////////////////////////////////////////////////////////.
//
let XATSTRCD = (knd0) => knd0
//
let XATSTUP0 = (tpl0) => tpl0
let XATSTUP1 = (knd0, tpl1) => tpl1
let XATSRCD2 = (knd0, rcd2) => rcd2
//
////////////////////////////////////////////////////////////////////////.
//
let XATSROOT = (x) => [0, x]
let XATSLPFT = (i, x) => [1+0, x, i]
let XATSLPBX = (i, x) => [1+1, x, i]
let XATSLPCN = (i, x) => [1+2, x, i+1]
//
let XATSVAR0 = (    ) => XATSROOT([null])
let XATSVAR1 = (init) => XATSROOT([init])
//
let XATSADDR = (addr) => addr // HX: no-op
let XATSFLAT = (addr) => XATS000_lvget(addr)
//
////////////////////////////////////////////////////////////////////////.
//
let XATSCTAG = (_, t) => t
//
let XATS000_inteq = (x, y) => (x===y)
let XATS000_btfeq = (x, y) => (x===y)
let XATS000_chreq = (x, y) => (x===y)
//
let XATS000_streq = (x, y) => (x == y)
//
let XATS000_ctgeq = (v, t) => (v[0] == t)
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
function
XATS2JS_optn_nil()
{
  return XATSCAPP("optn_nil", [0])
}
function
XATS2JS_optn_cons(x0)
{
  return XATSCAPP("optn_cons", [1, x0])
}
////////////////////////////////////////////////////////////////////////.
function
XATS2JS_list_nil()
{
  return XATSCAPP("list_nil", [0])
}
function
XATS2JS_list_cons(x0, xs)
{
  return XATSCAPP("list_cons", [1, x0, xs])
}
////////////////////////////////////////////////////////////////////////.
function
XATS2JS_optn_vt_nil()
{
  return XATSCAPP("optn_vt_nil", [0])
}
function
XATS2JS_optn_vt_cons(x0)
{
  return XATSCAPP("optn_vt_cons", [1, x0])
}
////////////////////////////////////////////////////////////////////////.
function
XATS2JS_list_vt_nil()
{
  return XATSCAPP("list_vt_nil", [0])
}
function
XATS2JS_list_vt_cons(x0, xs)
{
  return XATSCAPP("list_vt_cons", [1, x0, xs])
}
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.

let XATS000_cfail = function()
  {
    throw new Error("XATS000_cfail");
  }

let XATS000_patck = function(pck)
  {
    if (!pck) {
      throw new Error("XATS000_patck");
    } // end-of-[if]
  }

////////////////////////////////////////////////////////////////////////.

let XATS000_fold = (pcon) => null
let XATS000_free = (pcon) => null

////////////////////////////////////////////////////////////////////////.
//
let XATS000_dp2tr =
  (p2tr) => XATS000_lvget(p2tr)
//
let XATS000_l0azy = function(lfun)
{
  return [0, lfun]
}
let XATS000_dl0az = function(l0az)
{
  if (l0az[0] > 0) {
    l0az[0] += 1; return l0az[1]
  } else {
    let res = l0az[1]()
    l0az[0] = 0+1; l0az[1] = res; return res
  }
}
//
let XATS000_l1azy = (lfun) => lfun
let XATS000_dl1az = (l1az) => l1az(1)
//
let XATS000_assgn =
  (lval, rval) => XATS000_lvset(lval, rval)
//
////////////////////////////////////////////////////////////////////////.
//
let XATS000_ftset =
  function(tpl0, idx1, rval)
  {
    let tpl1 = tpl0.slice();
    tpl1[idx1] = rval; return tpl1
  }
//
let XATS000_lvget = function(lval)
  {
    let ctag = lval[0]
    if (ctag === 0)
      return lval[1][0]
    if (ctag === 1+0)
      return XATS000_lvget(lval[1])[lval[2]]
    if (ctag === 1+1)
      return lval[1][lval[2]]
    if (ctag === 1+2)
      return lval[1][lval[2]]
  }
//
let XATS000_lvset = function(lval, rval)
  {
    let ctag = lval[0]
    if (ctag === 0) return ( lval[1][0] = rval )
    if (ctag === 1+0)
    {
      return XATS000_lvset
	(lval[1], XATS000_ftset(XATS000_lvget(lval[1]), lval[2], rval))
    }
    if (ctag === 1+1) return ( lval[1][lval[2]] = rval )
    if (ctag === 1+2) return ( lval[1][lval[2]] = rval )
  }
//
////////////////////////////////////////////////////////////////////////.
//
let XATS000_raise = (xcon) => { throw(xcon) }
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
the end of
[ATS3-XANADU/srcgen2/xats2js/srcgen1/xshared/runtime/xats2js_js1emit.js]
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// Fri Jan 16 11:47:37 PM EST 2026
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
/*
the beg of
[ATS3-XANADU/srcgen2/xats2js/srcgen1/xshared/runtime/srcgen2_prelude.js]
*/
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Thu 05 Sep 2024 11:21:07 AM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_console_log
  (x0)
{
  return console.log(x0) // HX: void
}
//
////////////////////////////////////////////////////////////////////////.
//
const
XATS2JS_the_print_store = [] // HX: for prints?
//
const
XATS2JS_the_prout_store = [] // HX: for general output
//
const
XATS2JS_the_prerr_store = [] // HX: for reporting errors
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_the_print_store_clear
  ( /*void*/ )
{
  XATS2JS_the_print_store.length = 0; return
}
//
function
XATS2JS_the_print_store_flush
  ( /*void*/ )
{
  let cs =
  XATS2JS_the_print_store.join("")
  XATS2JS_the_print_store.length = 0; return cs
}
//
function
XATS2JS_the_prout_store_flush
  ( /*void*/ )
{
  let cs =
  XATS2JS_the_prout_store.join("")
  XATS2JS_the_prout_store.length = 0; return cs
}
//
function
XATS2JS_the_prerr_store_flush
  ( /*void*/ )
{
  let cs =
  XATS2JS_the_prerr_store.join("")
  XATS2JS_the_prerr_store.length = 0; return cs
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_xtop000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Mon 09 Sep 2024 09:31:27 AM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_g_tostr
  ( obj )
{
  return String(obj) }
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strn_sint$parse$fwork
  (rep0, work)
{
  let i0 = parseInt(rep0)
  if (!isNaN(i0)) { work(i0) }; return
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strn_dflt$parse$fwork
  (rep0, work)
{
  let f0 = parseFloat(rep0)
  if (!isNaN(f0)) { work(f0) }; return
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_gbas000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Fri Sep 20 09:05:02 AM EDT 2024
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_bool_assert$errmsg
  (cond, emsg)
{
  if (!cond) {
    throw new Error("XATS2JS_bool_assert$errmsg: emsg = " + emsg)
  } ; return // HX: void is returned!
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_gdbg000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Sun 01 Sep 2024 04:27:52 PM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_sint_neg
  ( i1 )
{
  return ( -i1 ) // HX: neg
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_sint_lt$sint
  (i1, i2)
{
  return (i1 < i2) // HX: lt
}
function
XATS2JS_sint_gt$sint
  (i1, i2)
{
  return (i1 > i2) // HX: gt
}
//
function
XATS2JS_sint_lte$sint
  (i1, i2)
{
  return (i1 <= i2) // HX: lte
}
function
XATS2JS_sint_gte$sint
  (i1, i2)
{
  return (i1 >= i2) // HX: gte
}
//
function
XATS2JS_sint_eq$sint
  (i1, i2)
{
  return (i1 === i2) // HX: equal
}
function
XATS2JS_sint_neq$sint
  (i1, i2)
{
  return (i1 !== i2) // HX: noteq
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_sint_add$sint
  (i1, i2)
{
  return (i1 + i2) // HX: add
}
//
function
XATS2JS_sint_sub$sint
  (i1, i2)
{
  return (i1 - i2) // HX: sub
}
//
function
XATS2JS_sint_mul$sint
  (i1, i2)
{
  return (i1 * i2) // HX: mul
}
//
function
XATS2JS_sint_div$sint
  (i1, i2)
{
  return Math.trunc(i1 / i2)
}
//
function
XATS2JS_sint_mod$sint
  (i1, i2)
{
  return (i1 % i2) // HX: mod
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_sint_print
  ( i0 )
{
  let cs = i0.toString()
  XATS2JS_the_print_store.push(cs); return
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
// HX-2025-09-27:
// for unsigned ints
// Sat Sep 27 12:38:38 PM EDT 2025
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_uint_print
  ( u0 )
{
  let cs = u0.toString()
  XATS2JS_the_print_store.push(cs); return
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_sint_to$uint
  ( i0 )
{
  if (i0>=0)
  {
    return i0 // i0>=0
  } else {
    throw new Error("XATS2JS_sint_to$uint: i0 = " + i0.toString())
  } // end of [if(i0>=0)]
}
function
XATS2JS_uint_to$sint
  ( u0 )
{
  if (u0>=0)
  {
    return u0 // always?
  } else {
    throw new Error("XATS2JS_uint_to$sint: u0 = " + u0.toString())
  } // end of [if(u0>=0)]
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_gint000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Sun 01 Sep 2024 05:07:38 PM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_bool_lt
  (b1, b2)
{
  return (b1 < b2) // HX: lt
}
function
XATS2JS_bool_gt
  (b1, b2)
{
  return (b1 > b2) // HX: gt
}
//
function
XATS2JS_bool_lte
  (b1, b2)
{
  return (b1 <= b2) // HX: lte
}
function
XATS2JS_bool_gte
  (b1, b2)
{
  return (b1 >= b2) // HX: gte
}
//
function
XATS2JS_bool_eq
  (b1, b2)
{
  return (b1 === b2) // HX: equal
}
function
XATS2JS_bool_neq
  (b1, b2)
{
  return (b1 !== b2) // HX: noteq
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_bool000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Sun 01 Sep 2024 05:08:01 PM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_char_lt
  (c1, c2)
{
  return (c1 < c2) // HX: lt
}
function
XATS2JS_char_gt
  (c1, c2)
{
  return (c1 > c2) // HX: gt
}
//
function
XATS2JS_char_lte
  (c1, c2)
{
  return (c1 <= c2) // HX: lte
}
function
XATS2JS_char_gte
  (c1, c2)
{
  return (c1 >= c2) // HX: gte
}
//
function
XATS2JS_char_eq
  (c1, c2)
{
  return (c1 === c2) // HX: equal
}
function
XATS2JS_char_neq
  (c1, c2)
{
  return (c1 !== c2) // HX: noteq
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_char_add$sint
  (c1, i2)
{
  let c2 = c1+i2
  return (c2%256) // HX: char=int8
}
//
function
XATS2JS_char_sub$char
  (c1, c2)
{
  return (c1 - c2) // HX: char=int8
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_char_print
  ( c0 )
{
  let cs = String.fromCharCode(c0)
  XATS2JS_the_print_store.push(cs); return
}
//
////////////////////////////////////////////////////////////////////////.
//
/*
HX-2025-01-10:
Taken from gavinz
Sun Jan 19 01:11:19 AM EST 2025
*/
function
XATS2JS_char_make_sint( i0 ) { return i0 }
//
/*
HX-2026-01-15:
Thu Jan 15 06:47:03 PM EST 2026
*/
function
XATS2JS_sint_make_char( ch ) { return ch }
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_char000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Mon 09 Sep 2024 06:14:11 PM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_neg
  ( df )
{
  return ( -df ) //HX:neg
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_abs
  ( df )
{
  if (df >= 0.0)
    return df
  else
    return (-df) //HX:abs
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_sqrt
  ( df )
{
  return Math.sqrt(  df  )
}
//
function
XATS2JS_dflt_cbrt
  ( df )
{
  return Math.cbrt(  df  )
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_lt$dflt
  (f1, f2)
{
  return (f1 < f2) // HX: lt
}
function
XATS2JS_dflt_gt$dflt
  (f1, f2)
{
  return (f1 > f2) // HX: gt
}
//
function
XATS2JS_dflt_lte$dflt
  (f1, f2)
{
  return (f1 <= f2) // HX: lte
}
function
XATS2JS_dflt_gte$dflt
  (f1, f2)
{
  return (f1 >= f2) // HX: gte
}
//
function
XATS2JS_dflt_eq$dflt
  (f1, f2)
{
  return (f1 === f2) // HX: eq
}
function
XATS2JS_dflt_neq$dflt
  (f1, f2)
{
  return (f1 !== f2) // HX: neq
}
//
/*
HX-2025-12-13:
Sat Dec 13 05:19:31 PM EST 2025
*/
//
function
XATS2JS_dflt_cmp$dflt
  (f1, f2)
{
  if (f1 < f2)
    return (-1) // lt
  else // f1 >= f2
    return (f1 > f2 ? 1 : 0)
  // HX: end-of-if( f1 < f2 )
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_add$dflt
  (f1, f2)
{
  return (f1 + f2) // HX: add
}
//
function
XATS2JS_dflt_sub$dflt
  (f1, f2)
{
  return (f1 - f2) // HX: sub
}
//
//
function
XATS2JS_dflt_mul$dflt
  (f1, f2)
{
  return (f1 * f2) // HX: mul
}
//
function
XATS2JS_dflt_div$dflt
  (f1, f2)
{
  return (f1 / f2) // HX: div
}
//
function
XATS2JS_dflt_mod$dflt
  (f1, f2)
{
  return (f1 % f2) // HX: mod
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_ceil
  ( df )
{
  return Math.ceil(df) // (1.2) = 2
}
function
XATS2JS_dflt_floor
  ( df )
{
  return Math.floor(df) // (1.2) = 1
}
function
XATS2JS_dflt_round
  ( df )
{
  // HX: (1.2) = 1 // (1.5) = 2
  return Math.round(df) // (-1.5) = 1
}
function
XATS2JS_dflt_trunc
  ( df )
{
  // HX: (1.2) = 1 // (1.9) = 1
  return Math.trunc(df) // (-1.2) = -1
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_dflt_print
  ( f0 )
{
  let cs = f0.toString()
  XATS2JS_the_print_store.push(cs); return
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_gflt000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Fri 16 Aug 2024 05:26:45 PM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strn_cmp
  (x1, x2)
{
  var df
  var i0 = 0
  var n1 = x1.length;
  var n2 = x2.length;
  var n0 =
  (n1 <= n2) ? n1 : n2;
  while (i0 < n0) {
    df =
    x1.charCodeAt(i0)
    -
    x2.charCodeAt(i0)
    if (df !== 0) return df;
    i0 = (  i0 + 1  )
  }
  return (      n1 - n2      );
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strn_length
  (cs)
{
  return cs.length // HX: field
}
function
XATS000_strn_length
  (cs)
{
  return cs.length // HX: field
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strn_get$at$raw
  (cs, i0)
{
  return cs.charCodeAt(i0) // HX: ascii
}
function
XATS000_strn_get$at$raw
  (cs, i0)
{
  return XATS2JS_strn_get$at$raw(cs, i0)
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strn_fmake_fwork
  (fwork)
{
  var cs = []
  fwork((ch) => {cs.push(ch);return})
  return String.fromCharCode.apply(null, cs)
}
//
function
XATS000_strn_fmake_fwork
  (fwork)
{
  return XATS2JS_strn_fmake_fwork(fwork)
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS000_strn_print
  ( cs )
{
  return XATS2JS_strn_print(cs)
}
function
XATS2JS_strn_print
  ( cs )
{
  XATS2JS_the_print_store.push(cs); return
}
//
////////////////////////////////////////////////////////////////////////.
//
/*
HX-2025-04-26:
Sat Apr 26 08:48:02 PM EDT 2025
*/
//
function
XATS2JS_strn_fmake_env$fwork
  (env, fwork)
{
  var cs = []
  fwork(env, (ch) => {cs.push(ch);return})
  return String.fromCharCode.apply(null, cs)
}
function
XATS2JS_strn_fmake1_env$fwork
  (env, fwork)
{
  var cs = []
  fwork(env, (ch) => {cs.push(ch);return})
  return String.fromCharCode.apply(null, cs)
}
//
function
XATS000_strn_fmake_env$fwork
  (env, fwork)
{
  return XATS2JS_strn_fmake_env$fwork(env, fwork)
}
function
XATS000_strn_fmake1_env$fwork
  (env, fwork)
{
  return XATS2JS_strn_fmake1_env$fwork(env, fwork)
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_strn000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Fri Jan  2 03:23:26 PM EST 2026
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_list_vt_foritm0$f1un
  (xs, work)
{
  let nilq1 =
    XATS2JS_list_vt_nilq1
  while (1) {
    if (nilq1(xs)) {
      break;
    } else {
      let x1 =
        XATS2JS_list_vt_head$raw1(xs)
      work(x1)
      xs = XATS2JS_list_vt_tail$raw0(xs)
    }
  }
  return // XATS2JS_list_vt_foritm0$f1un
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_list_vt_forall0$f1un
  (xs, test, free)
{
  let nilq1 =
    XATS2JS_list_vt_nilq1
  while (1) {
    if (nilq1(xs)) {
      break;
    } else {
      let x1 =
        XATS2JS_list_vt_head$raw1(xs)
      if (test(x1)) {
        xs = XATS2JS_list_vt_tail$raw0(xs)
      } else {
        xs = XATS2JS_list_vt_tail$raw0(xs)
        XATS2JS_list_vt_foritm0$f1un(xs, free); return false
      }
    }
  }
  return true // XATS2JS_list_vt_forall0$f1un
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_list000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Fri Jan  2 03:23:26 PM EST 2026
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
// HX: It is yet to be populated!
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_optn000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Fri Jan  2 03:23:26 PM EST 2026
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strm_vt_forall0$f1un
  (fxs, test)
{
  let nilq1 =
    XATS2JS_strmcon_vt_nilq1
  while (1) {
    let cxs =
      XATS2JS_lazy_vt_eval(fxs)
    if (nilq1(cxs))
    {
      break;
    } else {
      let x01 =
        XATS2JS_strmcon_vt_head$raw1(cxs)
      if (test(x01))
      {
        fxs = XATS2JS_strmcon_vt_tail$raw0(cxs)
      } else {
        fxs = XATS2JS_strmcon_vt_tail$raw0(cxs)
        XATS2JS_lazy_vt_free(fxs); return false
      }
    }
  }
  return true // XATS2JS_strm_vt_forall0$f1un(...)
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strm_vt_filter0$f1un
  (fxs, test, free)
{
  return XATS2JS_lazy_vt_make_f0un(
    () => XATS2JS_strmcon_vt_filter0$f1un(XATS2JS_lazy_vt_eval(fxs), test, free)
  )
}
//
function
XATS2JS_strmcon_vt_filter0$f1un
  (cxs, test, free)
{
  let nilq1 =
    XATS2JS_strmcon_vt_nilq1
  while (1) {
    if (nilq1(cxs))
    {
      return XATS2JS_strmcon_vt_nil()
    } else {
      let x01 = XATS2JS_strmcon_vt_head$raw1(cxs)
      let fxs = XATS2JS_strmcon_vt_tail$raw0(cxs)
      if (test(x01)) {
        return XATS2JS_strmcon_vt_cons(x01, XATS2JS_strm_vt_filter0$f1un(fxs, test, free))
      } else {
        free(x01);
        cxs = XATS2JS_lazy_vt_eval(fxs); continue;
      }
    }
  }
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_strm000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Wed Jan 14 01:17:42 PM EST 2026
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strx_vt_forall0$f1un
  (fxs, test)
{
  while (1) {
    let cxs =
      XATS2JS_lazy_vt_eval(fxs)
    let x01 =
      XATS2JS_strxcon_vt_head$raw1(cxs)
    if (test(x01))
    {
      fxs = XATS2JS_strxcon_vt_tail$raw0(cxs)
    } else {
      fxs = XATS2JS_strxcon_vt_tail$raw0(cxs)
      XATS2JS_lazy_vt_free(fxs); return false
    }
  }
  return true // XATS2JS_strx_vt_forall0$f1un(...)
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_strx_vt_filter0$f1un
  (fxs, test, free)
{
  return XATS2JS_lazy_vt_make_f0un(
    () => XATS2JS_strxcon_vt_filter0$f1un(XATS2JS_lazy_vt_eval(fxs), test, free)
  )
}
//
function
XATS2JS_strxcon_vt_filter0$f1un
  (cxs, test, free)
{
  while (1) {
    let x01 = XATS2JS_strxcon_vt_head$raw1(cxs)
    let fxs = XATS2JS_strxcon_vt_tail$raw0(cxs)
    if (test(x01)) {
      return XATS2JS_strxcon_vt_cons(x01, XATS2JS_strx_vt_filter0$f1un(fxs, test, free))
    } else {
      free(x01);
      cxs = XATS2JS_lazy_vt_eval(fxs); continue;
    }
  }
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_strx000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Mon 12 Aug 2024 09:36:59 AM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_a0rf_lget
  ( A0 )
{
  return A0[0]
}
function
XATS2JS_a0rf_lset
  (A0, x1)
{
  A0[0] = x1; return
}
//
function
XATS2JS_a0rf_make_1val
  ( x0 )
{
  return [x0] // HX: singleton
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_a1rf_lget$at
  (A0, i0)
{
  return A0[i0]
}
function
XATS2JS_a1rf_lset$at
  (A0, i0, x1)
{
  A0[i0] = x1; return
}
//
function
XATS2JS_a1rf_make_ncpy
  (n0, x0)
{
  var i0 = 0
  var A0 = new Array(n0);
  while (i0 < n0) {
    A0[i0] = x0; i0 = i0 + 1
  }
  return A0 // HX: A0=[x0, x0, ..., x0]
}
//
function
XATS2JS_a1rf_make_nfun
  (n0, fopr)
{
  var i0 = 0
  var A0 = new Array(n0);
  while (i0 < n0) {
    A0[i0] = fopr(i0); i0 = i0 + 1
  }
  return A0 // HX: A0 = [fopr(0),...,fopr(n-1)]
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_axrf000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//                                                                    //.
//                         Applied Type System                        //.
//                                                                    //.
////////////////////////////////////////////////////////////////////////.

/*
** ATS/Xanadu - Unleashing the Potential of Types!
** Copyright (C) 2024 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*/

////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
/*
Author: Hongwei Xi
Thu 15 Aug 2024 01:42:20 PM EDT
Authoremail: gmhwxiATgmailDOTcom
*/
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_a1sz_length
  ( A0 )
{
  return A0.length
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_a1sz_lget$at
  (A0, i0)
{
  return A0[i0]
}
function
XATS2JS_a1sz_lset$at
  (A0, i0, x1)
{
  A0[i0] = x1; return
}
//
////////////////////////////////////////////////////////////////////////.
/*
HX-2024-09-06:
Fri 06 Sep 2024 04:18:38 PM EDT
*/
//
function
XATS2JS_a1sz_make_none
  ( n0 )
{
  var A0 = new Array(n0)
  return A0 // HX: A0 = [?, ..., ?]
}
////////////////////////////////////////////////////////////////////////.
//
/*
HX-2024-08-15:
Thu 15 Aug 2024 01:50:45 PM EDT
*/
//
function
XATS2JS_a1sz_make_ncpy
  (n0, x0)
{
  var i0 = 0
  var A0 = new Array(n0)
  while (i0 < n0) {
    A0[i0] = x0; i0 = i0 + 1
  }
  return A0 // HX: A0 = [x0, ..., x0]
}
//
function
XATS2JS_a1sz_make_nfun
  (n0, fopr)
{
  var i0 = 0
  var A0 = new Array(n0)
  while (i0 < n0) {
    A0[i0] = fopr(i0); i0 = i0 + 1
  }
  return A0 // HX: A0 = [fopr(0),...,fopr(n-1)]
}
//
////////////////////////////////////////////////////////////////////////.
//
function
XATS2JS_a1sz_fmake_fwork
  (fwork)
{
  var A0 = []
  fwork((x0) => {A0.push(x0);return}); return A0
}
//
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// end of [ATS3/XANADU_prelude_DATS_CATS_JS_axsz000.cats]
////////////////////////////////////////////////////////////////////////.
////////////////////////////////////////////////////////////////////////.
// LCSRCsome1(lambda1.dats)@(134(line=9,offs=1)--175(line=10,offs=28))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(0;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(UN);G1Estr(T_STRN1_clsd("prelude/SATS/unsfx00.sats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats));...)))
// I1Dinclude(LCSRCsome1(lambda1.dats)@(216(line=13,offs=1)--257(line=14,offs=33)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(244(line=17,offs=1)--291(line=19,offs=28))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gbas000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(292(line=20,offs=1)--339(line=22,offs=28))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gbas001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(340(line=23,offs=1)--387(line=25,offs=28))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gbas002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas002.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(414(line=29,offs=1)--461(line=31,offs=28))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gdbg000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gdbg000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(488(line=35,offs=1)--541(line=37,offs=34))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gbas000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gbas000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(542(line=38,offs=1)--595(line=40,offs=34))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gbas001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gbas001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(767(line=51,offs=1)--807(line=51,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gxyz000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gxyz000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(854(line=56,offs=1)--894(line=56,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/unsfx00.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1038(line=65,offs=1)--1078(line=65,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gnum000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gnum000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1079(line=66,offs=1)--1119(line=66,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gord000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1120(line=67,offs=1)--1160(line=67,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gfun000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gfun000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1164(line=69,offs=1)--1204(line=69,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gseq000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1205(line=70,offs=1)--1245(line=70,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gseq001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1246(line=71,offs=1)--1286(line=71,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gseq002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq002.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1290(line=73,offs=1)--1330(line=73,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gasq000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gasq000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1331(line=74,offs=1)--1371(line=74,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gasq001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gasq001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1372(line=75,offs=1)--1412(line=75,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gasq002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gasq002.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1416(line=77,offs=1)--1456(line=77,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gmap000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gmap000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1457(line=78,offs=1)--1497(line=78,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gmap001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gmap001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1501(line=80,offs=1)--1541(line=80,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gcls000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gcls000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1542(line=81,offs=1)--1582(line=81,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gsyn000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1583(line=82,offs=1)--1623(line=82,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gsyn001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1650(line=86,offs=1)--1690(line=86,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/bool000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1691(line=87,offs=1)--1731(line=87,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/char000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/char000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1732(line=88,offs=1)--1772(line=88,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gint000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1773(line=89,offs=1)--1813(line=89,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gint001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1814(line=90,offs=1)--1854(line=90,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gflt000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gflt000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1881(line=94,offs=1)--1921(line=94,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strn000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1922(line=95,offs=1)--1962(line=95,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strn001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1989(line=99,offs=1)--2029(line=99,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axrf000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axrf000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2030(line=100,offs=1)--2070(line=100,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axrf001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axrf001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2071(line=101,offs=1)--2111(line=101,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axsz000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axsz000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2112(line=102,offs=1)--2152(line=102,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axsz001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axsz001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2153(line=103,offs=1)--2193(line=103,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/asrt000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/asrt000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2194(line=104,offs=1)--2234(line=104,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/tupl000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/tupl000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2235(line=105,offs=1)--2275(line=105,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/tupl001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/tupl001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2276(line=106,offs=1)--2316(line=106,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/tupl002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/tupl002.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2317(line=107,offs=1)--2357(line=107,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/list000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2358(line=108,offs=1)--2398(line=108,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/list001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2399(line=109,offs=1)--2439(line=109,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/list002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list002.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2440(line=110,offs=1)--2480(line=110,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/lsrt000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/lsrt000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2481(line=111,offs=1)--2521(line=111,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/optn000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/optn000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2522(line=112,offs=1)--2562(line=112,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/optn001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/optn001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2563(line=113,offs=1)--2603(line=113,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strm000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strm000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2604(line=114,offs=1)--2644(line=114,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strm001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strm001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2645(line=115,offs=1)--2685(line=115,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strx000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strx000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2686(line=116,offs=1)--2726(line=116,offs=41))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strx001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strx001.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2773(line=121,offs=1)--2818(line=121,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/gbas000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/gbas000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2822(line=123,offs=1)--2867(line=123,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/bool000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/bool000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2868(line=124,offs=1)--2913(line=124,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/char000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/char000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2917(line=126,offs=1)--2962(line=126,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/gint000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/gint000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2963(line=127,offs=1)--3008(line=127,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/gflt000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/gflt000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3012(line=129,offs=1)--3057(line=129,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/strn000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/strn000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3061(line=131,offs=1)--3106(line=131,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/axrf000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/axrf000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3107(line=132,offs=1)--3152(line=132,offs=46))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/axsz000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/axsz000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3258(line=140,offs=1)--3304(line=140,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gnum000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gnum000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3305(line=141,offs=1)--3351(line=141,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gord000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gord000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3352(line=142,offs=1)--3398(line=142,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gfun000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gfun000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3399(line=143,offs=1)--3445(line=143,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gcls000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gcls000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3446(line=144,offs=1)--3492(line=144,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gseq000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3493(line=145,offs=1)--3539(line=145,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gseq001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3540(line=146,offs=1)--3586(line=146,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gseq002_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq002_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3587(line=147,offs=1)--3633(line=147,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gasq000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gasq000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3634(line=148,offs=1)--3680(line=148,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gasq001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gasq001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3681(line=149,offs=1)--3727(line=149,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gsyn000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gsyn000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3754(line=153,offs=1)--3800(line=153,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strn000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strn000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3827(line=157,offs=1)--3873(line=157,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/axrf000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/axrf000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3874(line=158,offs=1)--3920(line=158,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/axsz000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/axsz000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3921(line=159,offs=1)--3967(line=159,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/tupl000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/tupl000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3971(line=161,offs=1)--4017(line=161,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/list000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4018(line=162,offs=1)--4064(line=162,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/list001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4065(line=163,offs=1)--4111(line=163,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/lsrt000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/lsrt000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4112(line=164,offs=1)--4158(line=164,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/optn000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/optn000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4159(line=165,offs=1)--4205(line=165,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/optn001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/optn001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4209(line=167,offs=1)--4255(line=167,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strm000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4256(line=168,offs=1)--4302(line=168,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strm001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4303(line=169,offs=1)--4349(line=169,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strm002_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm002_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4350(line=170,offs=1)--4396(line=170,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strx000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strx000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4397(line=171,offs=1)--4443(line=171,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strx001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strx001_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4614(line=182,offs=1)--4660(line=182,offs=47))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gxyz000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4989(line=190,offs=1)--4989(line=190,offs=1))
// I1Dnone1(I0Dnone1(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4989(line=190,offs=1)--4989(line=190,offs=1));D3Cnone0()))
// I1Dinclude(LCSRCsome1(lambda1.dats)@(321(line=20,offs=1)--365(line=21,offs=36)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(197(line=15,offs=1)--249(line=16,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/xtop000.dats";35));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(296(line=21,offs=1)--344(line=22,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/gbas000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gbas000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(345(line=23,offs=1)--393(line=24,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/gdbg000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gdbg000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(440(line=29,offs=1)--488(line=30,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/bool000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/bool000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(489(line=31,offs=1)--537(line=32,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/char000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/char000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(538(line=33,offs=1)--586(line=34,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/gint000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(587(line=35,offs=1)--635(line=36,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/gflt000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gflt000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(682(line=41,offs=1)--730(line=42,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/strn000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(777(line=47,offs=1)--825(line=48,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/list000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/list000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(826(line=49,offs=1)--874(line=50,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/optn000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/optn000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(901(line=54,offs=1)--949(line=55,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/strm000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strm000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(950(line=56,offs=1)--998(line=57,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/strx000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strx000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(1045(line=62,offs=1)--1093(line=63,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/axrf000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/axrf000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(1094(line=64,offs=1)--1142(line=65,offs=36))
// I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/JS/axsz000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/axsz000.dats));...)))
// LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(1398(line=73,offs=1)--1398(line=73,offs=1))
// I1Dnone1(I0Dnone1(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_JS_dats.hats)@(1398(line=73,offs=1)--1398(line=73,offs=1));D3Cnone0()))
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(566(line=34,offs=1)--609(line=35,offs=28)))
// I1VALDCL
let jsxtnm19
// LCSRCsome1(lambda1.dats)@(575(line=34,offs=10)--581(line=34,offs=16))
// I0Etapq(I0Ecst(gs_print_a1(797)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11760(line=745,offs=1)--11771(line=745,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
// T1IMPallx(gs_print_a1(797);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21002(line=1292,offs=1)--21119(line=1301,offs=4)))
// T1IMPallx(gs_print_a1(797)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6917],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a1(797);$list(@(x0[2455],T2Pvar(x0[6917])))))))
let jsxtnm17 = function (arg1) { // timp: gs_print_a1(797)
  let jsxtnm1 = arg1
  // I1CMP:start
  let jsxtnm16 // let
  { // let
    // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21049(line=1297,offs=1)--21072(line=1298,offs=15)))
    // I1VALDCL
    let jsxtnm5
    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21058(line=1298,offs=1)--21070(line=1298,offs=13))
    // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    let jsxtnm3 = function () { // timp: gs_print$beg(793)
      // I1CMP:start
      let jsxtnm2 = XATSTUP0([])
      // I1CMP:return:jsxtnm2
      return jsxtnm2
    } // endtimp(gs_print$beg(793))
    let jsxtnm4 = XATSDAPP(jsxtnm3())
    jsxtnm5 = jsxtnm4
    XATS000_patck(true)
    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21083(line=1300,offs=1)--21090(line=1300,offs=8))
    // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6917])))))
    // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
    let jsxtnm11
    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
    // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    let jsxtnm10 = function (arg1) { // timp: strn_print(1029)
      let jsxtnm6 = arg1
      // I1CMP:start
      let jsxtnm9 // let
      { // let
        // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
        // I1FUNDCL
        // XATS2JS_strn_print_2202
          // FJARGdarg($list(I1BNDcons(I1TNM(7);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(7)))))))
          // I1CMP:start
          // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
        let jsxtnm8 = XATSDAPP(XATS2JS_strn_print(jsxtnm6))
        jsxtnm9 = jsxtnm8
      } // endlet
      // I1CMP:return:jsxtnm9
      return jsxtnm9
    } // endtimp(strn_print(1029))
    jsxtnm11 = jsxtnm10
    let jsxtnm12 = XATSDAPP(jsxtnm11(jsxtnm1))
    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21100(line=1300,offs=18)--21112(line=1300,offs=30))
    // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    let jsxtnm14 = function () { // timp: gs_print$end(795)
      // I1CMP:start
      let jsxtnm13 = XATSTUP0([])
      // I1CMP:return:jsxtnm13
      return jsxtnm13
    } // endtimp(gs_print$end(795))
    let jsxtnm15 = XATSDAPP(jsxtnm14())
    jsxtnm16 = jsxtnm15
  } // endlet
  // I1CMP:return:jsxtnm16
  return jsxtnm16
} // endtimp(gs_print_a1(797))
let jsxtnm18 = XATSDAPP(jsxtnm17(XATSSTRN("Hello from [lambda1]!\n")))
jsxtnm19 = jsxtnm18
XATS000_patck(true)
// LCSRCsome1(lambda1.dats)@(653(line=39,offs=1)--673(line=39,offs=21))
// I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Csexpdef(tvar;S2Ecst(strn)))))
// LCSRCsome1(lambda1.dats)@(674(line=40,offs=1)--694(line=40,offs=21))
// I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Csexpdef(topr;S2Ecst(strn)))))
// LCSRCsome1(lambda1.dats)@(718(line=43,offs=1)--1048(line=64,offs=29))
// I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Cdatatype(D1Cdatatype(T_DATATYPE(0);$list(D1TYPnode(T_IDALP(term);$list();$optn();$list(D1TCNnode($list();T_IDALP(TMint);$list();$optn(S1Eid0(sint))),D1TCNnode($list();T_IDALP(TMbtf);$list();$optn(S1Eid0(bool))),D1TCNnode($list();T_IDALP(TMvar);$list();$optn(S1Eid0(tvar))),D1TCNnode($list();T_IDALP(TMlam);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMapp);$list();$optn(S1El1st($list(S1Eid0(term),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMopr);$list();$optn(S1El1st($list(S1Eid0(topr),S1Ea1pp(S1Eid0(list);S1El1st($list(S1Eid0(term)))))))),D1TCNnode($list();T_IDALP(TMif0);$list();$optn(S1El1st($list(S1Eid0(term),S1Eid0(term),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMfix);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(tvar),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMlet);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(term),S1Eid0(term))))))));WD1CSnone());$list(term)))))
// LCSRCsome1(lambda1.dats)@(1052(line=66,offs=1)--1081(line=66,offs=30))
// I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Csexpdef(termlst;S2Eapps(S2Ecst(list);$list(S2Ecst(term)))))))
// I1Dlocal0(LCSRCsome1(lambda1.dats)@(1126(line=71,offs=1)--1482(line=96,offs=4)))
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1135(line=73,offs=1)--1191(line=75,offs=19)))
// I1VALDCL
let jsxtnm21
let jsxtnm20 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
jsxtnm21 = jsxtnm20
XATS000_patck(true)
// I1VALDCL
let jsxtnm23
let jsxtnm22 = XATSCAPP("TMvar", [2, XATSSTRN("y")])
jsxtnm23 = jsxtnm22
XATS000_patck(true)
// I1VALDCL
let jsxtnm25
let jsxtnm24 = XATSCAPP("TMvar", [2, XATSSTRN("z")])
jsxtnm25 = jsxtnm24
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1210(line=79,offs=1)--1231(line=79,offs=22)))
// I1VALDCL
let jsxtnm27
let jsxtnm26 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm21])
jsxtnm27 = jsxtnm26
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1235(line=81,offs=1)--1268(line=81,offs=34)))
// I1VALDCL
let jsxtnm30
let jsxtnm28 = XATSCAPP("TMlam", [3, XATSSTRN("y"), jsxtnm21])
let jsxtnm29 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm28])
jsxtnm30 = jsxtnm29
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1272(line=83,offs=1)--1347(line=87,offs=35)))
// I1VALDCL
let jsxtnm37
let jsxtnm31 = XATSCAPP("TMapp", [4, jsxtnm21, jsxtnm25])
let jsxtnm32 = XATSCAPP("TMapp", [4, jsxtnm23, jsxtnm25])
let jsxtnm33 = XATSCAPP("TMapp", [4, jsxtnm31, jsxtnm32])
let jsxtnm34 = XATSCAPP("TMlam", [3, XATSSTRN("z"), jsxtnm33])
let jsxtnm35 = XATSCAPP("TMlam", [3, XATSSTRN("y"), jsxtnm34])
let jsxtnm36 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm35])
jsxtnm37 = jsxtnm36
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1351(line=89,offs=1)--1385(line=89,offs=35)))
// I1VALDCL
let jsxtnm40
let jsxtnm38 = XATSCAPP("TMlam", [3, XATSSTRN("y"), jsxtnm23])
let jsxtnm39 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm38])
jsxtnm40 = jsxtnm39
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1389(line=91,offs=1)--1424(line=91,offs=36)))
// I1VALDCL
let jsxtnm43
let jsxtnm41 = XATSCAPP("TMapp", [4, jsxtnm21, jsxtnm21])
let jsxtnm42 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm41])
jsxtnm43 = jsxtnm42
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1425(line=92,offs=1)--1475(line=94,offs=37)))
// I1VALDCL
let jsxtnm45
let jsxtnm44 = XATSCAPP("TMapp", [4, jsxtnm43, jsxtnm43])
jsxtnm45 = jsxtnm44
XATS000_patck(true)
// I1Dextern(LCSRCsome1(lambda1.dats)@(1566(line=101,offs=1)--1607(line=103,offs=28)))
// LCSRCsome1(lambda1.dats)@(1574(line=102,offs=1)--1607(line=103,offs=28))
// I1TFNDCL: term_print(5223)
// I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(1611(line=105,offs=1)--2326(line=156,offs=2)))
// I1Dimplmnt0(DIMPLone2(term_print(2664);$list())):timp
// I1Dlocal0(LCSRCsome1(lambda1.dats)@(2400(line=160,offs=1)--2489(line=164,offs=4)))
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2406(line=161,offs=1)--2437(line=161,offs=32)))
// I1VALDCL
let jsxtnm879
// LCSRCsome1(lambda1.dats)@(2425(line=161,offs=20)--2435(line=161,offs=30))
// I0Etapq(I0Ecst(term_print(2664)(LCSRCsome1(lambda1.dats)@(1580(line=103,offs=1)--1590(line=103,offs=11))));$list(T2JAG($list())))
// T1IMPallx(term_print(2664);LCSRCsome1(lambda1.dats)@(1611(line=105,offs=1)--2326(line=156,offs=2)))
// T1IMPallx(term_print(2664)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(term_print(2664);$list()))))
let jsxtnm878 = function (arg1) { // timp: term_print(2664)
  let jsxtnm71 = arg1
  // I1CMP:start
  let jsxtnm877 // let
  { // let
    // I1Dfundclist(LCSRCsome1(lambda1.dats)@(1674(line=112,offs=1)--2315(line=155,offs=2)))
    // I1FUNDCL
    function auxpr_1677(arg1)
    { // fun
      let jsxtnm72 = arg1
      // I1CMP:start
      let jsxtnm875 // let
      { // let
        // I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
        // I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term))))):timp
        let jsxtnm874 // cas
        do {
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(73);I0Pdapp(I0Pcon(TMint(32));$list(I0Pvar(int(5228))));$list(@(int(5228),I1Vp1cn(I0Pcon(TMint(32));I1Vtnm(I1TNM(73));0)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMint",0))) { // gpt
            let jsxtnm73 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(1738(line=120,offs=1)--1744(line=120,offs=7))
            // I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a3(799);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
            // T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6920],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6921],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))),@(x2[6922],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2458],T2Pvar(x0[6920])),@(x1[2459],T2Pvar(x1[6921])),@(x2[2460],T2Pvar(x2[6922])))))))
            let jsxtnm112 = function (arg1, arg2, arg3) { // timp: gs_print_a3(799)
              let jsxtnm74 = arg1
              let jsxtnm75 = arg2
              let jsxtnm76 = arg3
              // I1CMP:start
              let jsxtnm111 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
                // I1VALDCL
                let jsxtnm80
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm78 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm77 = XATSTUP0([])
                  // I1CMP:return:jsxtnm77
                  return jsxtnm77
                } // endtimp(gs_print$beg(793))
                let jsxtnm79 = XATSDAPP(jsxtnm78())
                jsxtnm80 = jsxtnm79
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6920])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm86
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm85 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm81 = arg1
                  // I1CMP:start
                  let jsxtnm84 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(82);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(82)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm83 = XATSDAPP(XATS2JS_strn_print(jsxtnm81))
                    jsxtnm84 = jsxtnm83
                  } // endlet
                  // I1CMP:return:jsxtnm84
                  return jsxtnm84
                } // endtimp(strn_print(1029))
                jsxtnm86 = jsxtnm85
                let jsxtnm87 = XATSDAPP(jsxtnm86(jsxtnm74))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm89 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm88 = XATSTUP0([])
                  // I1CMP:return:jsxtnm88
                  return jsxtnm88
                } // endtimp(gs_print$sep(794))
                let jsxtnm90 = XATSDAPP(jsxtnm89())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6921])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats)@(2286(line=96,offs=1)--2321(line=97,offs=27)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(si)))))))
                let jsxtnm96
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats)@(2309(line=97,offs=15)--2319(line=97,offs=25))
                // I0Etapq(I0Ecst(sint_print(913)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(1506(line=49,offs=1)--1516(line=49,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(sint_print(913);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3616(line=223,offs=1)--3756(line=234,offs=2)))
                // T1IMPallx(sint_print(913)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_print(913);$list()))))
                let jsxtnm95 = function (arg1) { // timp: sint_print(913)
                  let jsxtnm91 = arg1
                  // I1CMP:start
                  let jsxtnm94 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3696(line=231,offs=1)--3754(line=233,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3704(line=232,offs=1)--3754(line=233,offs=47))
                    // I1FUNDCL
                    // XATS2JS_sint_print_3707
                      // FJARGdarg($list(I1BNDcons(I1TNM(92);I0Pvar(i0(4957));$list(@(i0(4957),I1Vtnm(I1TNM(92)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm93 = XATSDAPP(XATS2JS_sint_print(jsxtnm91))
                    jsxtnm94 = jsxtnm93
                  } // endlet
                  // I1CMP:return:jsxtnm94
                  return jsxtnm94
                } // endtimp(sint_print(913))
                jsxtnm96 = jsxtnm95
                let jsxtnm97 = XATSDAPP(jsxtnm96(jsxtnm75))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm99 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm98 = XATSTUP0([])
                  // I1CMP:return:jsxtnm98
                  return jsxtnm98
                } // endtimp(gs_print$sep(794))
                let jsxtnm100 = XATSDAPP(jsxtnm99())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6922])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm106
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm105 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm101 = arg1
                  // I1CMP:start
                  let jsxtnm104 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(102);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(102)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm103 = XATSDAPP(XATS2JS_strn_print(jsxtnm101))
                    jsxtnm104 = jsxtnm103
                  } // endlet
                  // I1CMP:return:jsxtnm104
                  return jsxtnm104
                } // endtimp(strn_print(1029))
                jsxtnm106 = jsxtnm105
                let jsxtnm107 = XATSDAPP(jsxtnm106(jsxtnm76))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm109 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm108 = XATSTUP0([])
                  // I1CMP:return:jsxtnm108
                  return jsxtnm108
                } // endtimp(gs_print$end(795))
                let jsxtnm110 = XATSDAPP(jsxtnm109())
                jsxtnm111 = jsxtnm110
              } // endlet
              // I1CMP:return:jsxtnm111
              return jsxtnm111
            } // endtimp(gs_print_a3(799))
            let jsxtnm113 = XATSDAPP(jsxtnm112(XATSSTRN("TMint("), XATSP1CN("TMint", jsxtnm73[0+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm113
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(114);I0Pdapp(I0Pcon(TMbtf(33));$list(I0Pvar(btf(5229))));$list(@(btf(5229),I1Vp1cn(I0Pcon(TMbtf(33));I1Vtnm(I1TNM(114));0)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMbtf",1))) { // gpt
            let jsxtnm114 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(1781(line=123,offs=1)--1787(line=123,offs=7))
            // I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a3(799);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
            // T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6920],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6921],T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))),@(x2[6922],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2458],T2Pvar(x0[6920])),@(x1[2459],T2Pvar(x1[6921])),@(x2[2460],T2Pvar(x2[6922])))))))
            let jsxtnm163 = function (arg1, arg2, arg3) { // timp: gs_print_a3(799)
              let jsxtnm115 = arg1
              let jsxtnm116 = arg2
              let jsxtnm117 = arg3
              // I1CMP:start
              let jsxtnm162 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
                // I1VALDCL
                let jsxtnm121
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm119 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm118 = XATSTUP0([])
                  // I1CMP:return:jsxtnm118
                  return jsxtnm118
                } // endtimp(gs_print$beg(793))
                let jsxtnm120 = XATSDAPP(jsxtnm119())
                jsxtnm121 = jsxtnm120
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6920])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm127
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm126 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm122 = arg1
                  // I1CMP:start
                  let jsxtnm125 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(123);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(123)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm124 = XATSDAPP(XATS2JS_strn_print(jsxtnm122))
                    jsxtnm125 = jsxtnm124
                  } // endlet
                  // I1CMP:return:jsxtnm125
                  return jsxtnm125
                } // endtimp(strn_print(1029))
                jsxtnm127 = jsxtnm126
                let jsxtnm128 = XATSDAPP(jsxtnm127(jsxtnm115))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm130 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm129 = XATSTUP0([])
                  // I1CMP:return:jsxtnm129
                  return jsxtnm129
                } // endtimp(gs_print$sep(794))
                let jsxtnm131 = XATSDAPP(jsxtnm130())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6921])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1767(line=64,offs=1)--1804(line=65,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(bool)))))))
                let jsxtnm147
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1792(line=65,offs=17)--1802(line=65,offs=27))
                // I0Etapq(I0Ecst(bool_print(861)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/bool000.sats)@(2405(line=107,offs=1)--2415(line=107,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(bool_print(861);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/bool000.dats)@(2541(line=142,offs=1)--2638(line=148,offs=28)))
                // T1IMPallx(bool_print(861)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(bool_print(861);$list()))))
                let jsxtnm146 = function (arg1) { // timp: bool_print(861)
                  let jsxtnm132 = arg1
                  // I1CMP:start
                  let jsxtnm145 // ift
                  if (jsxtnm132) // ift
                  {
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/bool000.dats)@(2590(line=147,offs=6)--2600(line=147,offs=16))
                    // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                    // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                    // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                    let jsxtnm137 = function (arg1) { // timp: strn_print(1029)
                      let jsxtnm133 = arg1
                      // I1CMP:start
                      let jsxtnm136 // let
                      { // let
                        // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                        // I1FUNDCL
                        // XATS2JS_strn_print_2202
                          // FJARGdarg($list(I1BNDcons(I1TNM(134);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(134)))))))
                          // I1CMP:start
                          // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                        let jsxtnm135 = XATSDAPP(XATS2JS_strn_print(jsxtnm133))
                        jsxtnm136 = jsxtnm135
                      } // endlet
                      // I1CMP:return:jsxtnm136
                      return jsxtnm136
                    } // endtimp(strn_print(1029))
                    let jsxtnm138 = XATSDAPP(jsxtnm137(XATSSTRN("true")))
                    jsxtnm145 = jsxtnm138
                  } else {
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/bool000.dats)@(2616(line=148,offs=6)--2626(line=148,offs=16))
                    // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                    // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                    // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                    let jsxtnm143 = function (arg1) { // timp: strn_print(1029)
                      let jsxtnm139 = arg1
                      // I1CMP:start
                      let jsxtnm142 // let
                      { // let
                        // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                        // I1FUNDCL
                        // XATS2JS_strn_print_2202
                          // FJARGdarg($list(I1BNDcons(I1TNM(140);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(140)))))))
                          // I1CMP:start
                          // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                        let jsxtnm141 = XATSDAPP(XATS2JS_strn_print(jsxtnm139))
                        jsxtnm142 = jsxtnm141
                      } // endlet
                      // I1CMP:return:jsxtnm142
                      return jsxtnm142
                    } // endtimp(strn_print(1029))
                    let jsxtnm144 = XATSDAPP(jsxtnm143(XATSSTRN("false")))
                    jsxtnm145 = jsxtnm144
                  } // end(if)
                  // I1CMP:return:jsxtnm145
                  return jsxtnm145
                } // endtimp(bool_print(861))
                jsxtnm147 = jsxtnm146
                let jsxtnm148 = XATSDAPP(jsxtnm147(jsxtnm116))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm150 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm149 = XATSTUP0([])
                  // I1CMP:return:jsxtnm149
                  return jsxtnm149
                } // endtimp(gs_print$sep(794))
                let jsxtnm151 = XATSDAPP(jsxtnm150())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6922])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm157
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm156 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm152 = arg1
                  // I1CMP:start
                  let jsxtnm155 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(153);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(153)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm154 = XATSDAPP(XATS2JS_strn_print(jsxtnm152))
                    jsxtnm155 = jsxtnm154
                  } // endlet
                  // I1CMP:return:jsxtnm155
                  return jsxtnm155
                } // endtimp(strn_print(1029))
                jsxtnm157 = jsxtnm156
                let jsxtnm158 = XATSDAPP(jsxtnm157(jsxtnm117))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm160 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm159 = XATSTUP0([])
                  // I1CMP:return:jsxtnm159
                  return jsxtnm159
                } // endtimp(gs_print$end(795))
                let jsxtnm161 = XATSDAPP(jsxtnm160())
                jsxtnm162 = jsxtnm161
              } // endlet
              // I1CMP:return:jsxtnm162
              return jsxtnm162
            } // endtimp(gs_print_a3(799))
            let jsxtnm164 = XATSDAPP(jsxtnm163(XATSSTRN("TMbtf("), XATSP1CN("TMbtf", jsxtnm114[0+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm164
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(165);I0Pdapp(I0Pcon(TMvar(34));$list(I0Pvar(nam(5230))));$list(@(nam(5230),I1Vp1cn(I0Pcon(TMvar(34));I1Vtnm(I1TNM(165));0)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMvar",2))) { // gpt
            let jsxtnm165 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(1824(line=126,offs=1)--1830(line=126,offs=7))
            // I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a3(799);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
            // T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6920],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6921],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6922],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2458],T2Pvar(x0[6920])),@(x1[2459],T2Pvar(x1[6921])),@(x2[2460],T2Pvar(x2[6922])))))))
            let jsxtnm204 = function (arg1, arg2, arg3) { // timp: gs_print_a3(799)
              let jsxtnm166 = arg1
              let jsxtnm167 = arg2
              let jsxtnm168 = arg3
              // I1CMP:start
              let jsxtnm203 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
                // I1VALDCL
                let jsxtnm172
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm170 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm169 = XATSTUP0([])
                  // I1CMP:return:jsxtnm169
                  return jsxtnm169
                } // endtimp(gs_print$beg(793))
                let jsxtnm171 = XATSDAPP(jsxtnm170())
                jsxtnm172 = jsxtnm171
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6920])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm178
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm177 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm173 = arg1
                  // I1CMP:start
                  let jsxtnm176 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(174);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(174)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm175 = XATSDAPP(XATS2JS_strn_print(jsxtnm173))
                    jsxtnm176 = jsxtnm175
                  } // endlet
                  // I1CMP:return:jsxtnm176
                  return jsxtnm176
                } // endtimp(strn_print(1029))
                jsxtnm178 = jsxtnm177
                let jsxtnm179 = XATSDAPP(jsxtnm178(jsxtnm166))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm181 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm180 = XATSTUP0([])
                  // I1CMP:return:jsxtnm180
                  return jsxtnm180
                } // endtimp(gs_print$sep(794))
                let jsxtnm182 = XATSDAPP(jsxtnm181())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6921])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm188
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm187 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm183 = arg1
                  // I1CMP:start
                  let jsxtnm186 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(184);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(184)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm185 = XATSDAPP(XATS2JS_strn_print(jsxtnm183))
                    jsxtnm186 = jsxtnm185
                  } // endlet
                  // I1CMP:return:jsxtnm186
                  return jsxtnm186
                } // endtimp(strn_print(1029))
                jsxtnm188 = jsxtnm187
                let jsxtnm189 = XATSDAPP(jsxtnm188(jsxtnm167))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm191 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm190 = XATSTUP0([])
                  // I1CMP:return:jsxtnm190
                  return jsxtnm190
                } // endtimp(gs_print$sep(794))
                let jsxtnm192 = XATSDAPP(jsxtnm191())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6922])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm198
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm197 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm193 = arg1
                  // I1CMP:start
                  let jsxtnm196 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(194);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(194)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm195 = XATSDAPP(XATS2JS_strn_print(jsxtnm193))
                    jsxtnm196 = jsxtnm195
                  } // endlet
                  // I1CMP:return:jsxtnm196
                  return jsxtnm196
                } // endtimp(strn_print(1029))
                jsxtnm198 = jsxtnm197
                let jsxtnm199 = XATSDAPP(jsxtnm198(jsxtnm168))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm201 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm200 = XATSTUP0([])
                  // I1CMP:return:jsxtnm200
                  return jsxtnm200
                } // endtimp(gs_print$end(795))
                let jsxtnm202 = XATSDAPP(jsxtnm201())
                jsxtnm203 = jsxtnm202
              } // endlet
              // I1CMP:return:jsxtnm203
              return jsxtnm203
            } // endtimp(gs_print_a3(799))
            let jsxtnm205 = XATSDAPP(jsxtnm204(XATSSTRN("TMvar("), XATSP1CN("TMvar", jsxtnm165[0+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm205
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(206);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5231)),I0Pvar(tmx(5232))));$list(@(x01(5231),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(206));0)),@(tmx(5232),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(206));1)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMlam",3))) { // gpt
            let jsxtnm206 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(1872(line=129,offs=1)--1878(line=129,offs=7))
            // I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a5(801);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
            // T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6927],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6928],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6929],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6930],T2Pcst(term)),@(x4[6931],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2465],T2Pvar(x0[6927])),@(x1[2466],T2Pvar(x1[6928])),@(x2[2467],T2Pvar(x2[6929])),@(x3[2468],T2Pvar(x3[6930])),@(x4[2469],T2Pvar(x4[6931])))))))
            let jsxtnm262 = function (arg1, arg2, arg3, arg4, arg5) { // timp: gs_print_a5(801)
              let jsxtnm207 = arg1
              let jsxtnm208 = arg2
              let jsxtnm209 = arg3
              let jsxtnm210 = arg4
              let jsxtnm211 = arg5
              // I1CMP:start
              let jsxtnm261 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
                // I1VALDCL
                let jsxtnm215
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm213 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm212 = XATSTUP0([])
                  // I1CMP:return:jsxtnm212
                  return jsxtnm212
                } // endtimp(gs_print$beg(793))
                let jsxtnm214 = XATSDAPP(jsxtnm213())
                jsxtnm215 = jsxtnm214
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6927])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm221
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm220 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm216 = arg1
                  // I1CMP:start
                  let jsxtnm219 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(217);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(217)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm218 = XATSDAPP(XATS2JS_strn_print(jsxtnm216))
                    jsxtnm219 = jsxtnm218
                  } // endlet
                  // I1CMP:return:jsxtnm219
                  return jsxtnm219
                } // endtimp(strn_print(1029))
                jsxtnm221 = jsxtnm220
                let jsxtnm222 = XATSDAPP(jsxtnm221(jsxtnm207))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm224 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm223 = XATSTUP0([])
                  // I1CMP:return:jsxtnm223
                  return jsxtnm223
                } // endtimp(gs_print$sep(794))
                let jsxtnm225 = XATSDAPP(jsxtnm224())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6928])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm231
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm230 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm226 = arg1
                  // I1CMP:start
                  let jsxtnm229 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(227);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(227)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm228 = XATSDAPP(XATS2JS_strn_print(jsxtnm226))
                    jsxtnm229 = jsxtnm228
                  } // endlet
                  // I1CMP:return:jsxtnm229
                  return jsxtnm229
                } // endtimp(strn_print(1029))
                jsxtnm231 = jsxtnm230
                let jsxtnm232 = XATSDAPP(jsxtnm231(jsxtnm208))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm234 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm233 = XATSTUP0([])
                  // I1CMP:return:jsxtnm233
                  return jsxtnm233
                } // endtimp(gs_print$sep(794))
                let jsxtnm235 = XATSDAPP(jsxtnm234())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6929])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm241
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm240 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm236 = arg1
                  // I1CMP:start
                  let jsxtnm239 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(237);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(237)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm238 = XATSDAPP(XATS2JS_strn_print(jsxtnm236))
                    jsxtnm239 = jsxtnm238
                  } // endlet
                  // I1CMP:return:jsxtnm239
                  return jsxtnm239
                } // endtimp(strn_print(1029))
                jsxtnm241 = jsxtnm240
                let jsxtnm242 = XATSDAPP(jsxtnm241(jsxtnm209))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm244 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm243 = XATSTUP0([])
                  // I1CMP:return:jsxtnm243
                  return jsxtnm243
                } // endtimp(gs_print$sep(794))
                let jsxtnm245 = XATSDAPP(jsxtnm244())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6930])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm246
                jsxtnm246 = auxpr_1677
                let jsxtnm247 = XATSDAPP(jsxtnm246(jsxtnm210))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm249 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm248 = XATSTUP0([])
                  // I1CMP:return:jsxtnm248
                  return jsxtnm248
                } // endtimp(gs_print$sep(794))
                let jsxtnm250 = XATSDAPP(jsxtnm249())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6931])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm256
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm255 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm251 = arg1
                  // I1CMP:start
                  let jsxtnm254 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(252);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(252)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm253 = XATSDAPP(XATS2JS_strn_print(jsxtnm251))
                    jsxtnm254 = jsxtnm253
                  } // endlet
                  // I1CMP:return:jsxtnm254
                  return jsxtnm254
                } // endtimp(strn_print(1029))
                jsxtnm256 = jsxtnm255
                let jsxtnm257 = XATSDAPP(jsxtnm256(jsxtnm211))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm259 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm258 = XATSTUP0([])
                  // I1CMP:return:jsxtnm258
                  return jsxtnm258
                } // endtimp(gs_print$end(795))
                let jsxtnm260 = XATSDAPP(jsxtnm259())
                jsxtnm261 = jsxtnm260
              } // endlet
              // I1CMP:return:jsxtnm261
              return jsxtnm261
            } // endtimp(gs_print_a5(801))
            let jsxtnm263 = XATSDAPP(jsxtnm262(XATSSTRN("TMlam("), XATSP1CN("TMlam", jsxtnm206[0+1]), XATSSTRN(";"), XATSP1CN("TMlam", jsxtnm206[1+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm263
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(264);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5233)),I0Pvar(tm2(5234))));$list(@(tm1(5233),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(264));0)),@(tm2(5234),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(264));1)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMapp",4))) { // gpt
            let jsxtnm264 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(1930(line=132,offs=1)--1936(line=132,offs=7))
            // I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a5(801);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
            // T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6927],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6928],T2Pcst(term)),@(x2[6929],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6930],T2Pcst(term)),@(x4[6931],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2465],T2Pvar(x0[6927])),@(x1[2466],T2Pvar(x1[6928])),@(x2[2467],T2Pvar(x2[6929])),@(x3[2468],T2Pvar(x3[6930])),@(x4[2469],T2Pvar(x4[6931])))))))
            let jsxtnm315 = function (arg1, arg2, arg3, arg4, arg5) { // timp: gs_print_a5(801)
              let jsxtnm265 = arg1
              let jsxtnm266 = arg2
              let jsxtnm267 = arg3
              let jsxtnm268 = arg4
              let jsxtnm269 = arg5
              // I1CMP:start
              let jsxtnm314 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
                // I1VALDCL
                let jsxtnm273
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm271 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm270 = XATSTUP0([])
                  // I1CMP:return:jsxtnm270
                  return jsxtnm270
                } // endtimp(gs_print$beg(793))
                let jsxtnm272 = XATSDAPP(jsxtnm271())
                jsxtnm273 = jsxtnm272
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6927])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm279
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm278 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm274 = arg1
                  // I1CMP:start
                  let jsxtnm277 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(275);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(275)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm276 = XATSDAPP(XATS2JS_strn_print(jsxtnm274))
                    jsxtnm277 = jsxtnm276
                  } // endlet
                  // I1CMP:return:jsxtnm277
                  return jsxtnm277
                } // endtimp(strn_print(1029))
                jsxtnm279 = jsxtnm278
                let jsxtnm280 = XATSDAPP(jsxtnm279(jsxtnm265))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm282 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm281 = XATSTUP0([])
                  // I1CMP:return:jsxtnm281
                  return jsxtnm281
                } // endtimp(gs_print$sep(794))
                let jsxtnm283 = XATSDAPP(jsxtnm282())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6928])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm284
                jsxtnm284 = auxpr_1677
                let jsxtnm285 = XATSDAPP(jsxtnm284(jsxtnm266))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm287 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm286 = XATSTUP0([])
                  // I1CMP:return:jsxtnm286
                  return jsxtnm286
                } // endtimp(gs_print$sep(794))
                let jsxtnm288 = XATSDAPP(jsxtnm287())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6929])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm294
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm293 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm289 = arg1
                  // I1CMP:start
                  let jsxtnm292 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(290);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(290)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm291 = XATSDAPP(XATS2JS_strn_print(jsxtnm289))
                    jsxtnm292 = jsxtnm291
                  } // endlet
                  // I1CMP:return:jsxtnm292
                  return jsxtnm292
                } // endtimp(strn_print(1029))
                jsxtnm294 = jsxtnm293
                let jsxtnm295 = XATSDAPP(jsxtnm294(jsxtnm267))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm297 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm296 = XATSTUP0([])
                  // I1CMP:return:jsxtnm296
                  return jsxtnm296
                } // endtimp(gs_print$sep(794))
                let jsxtnm298 = XATSDAPP(jsxtnm297())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6930])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm299
                jsxtnm299 = auxpr_1677
                let jsxtnm300 = XATSDAPP(jsxtnm299(jsxtnm268))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm302 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm301 = XATSTUP0([])
                  // I1CMP:return:jsxtnm301
                  return jsxtnm301
                } // endtimp(gs_print$sep(794))
                let jsxtnm303 = XATSDAPP(jsxtnm302())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6931])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm309
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm308 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm304 = arg1
                  // I1CMP:start
                  let jsxtnm307 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(305);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(305)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm306 = XATSDAPP(XATS2JS_strn_print(jsxtnm304))
                    jsxtnm307 = jsxtnm306
                  } // endlet
                  // I1CMP:return:jsxtnm307
                  return jsxtnm307
                } // endtimp(strn_print(1029))
                jsxtnm309 = jsxtnm308
                let jsxtnm310 = XATSDAPP(jsxtnm309(jsxtnm269))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm312 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm311 = XATSTUP0([])
                  // I1CMP:return:jsxtnm311
                  return jsxtnm311
                } // endtimp(gs_print$end(795))
                let jsxtnm313 = XATSDAPP(jsxtnm312())
                jsxtnm314 = jsxtnm313
              } // endlet
              // I1CMP:return:jsxtnm314
              return jsxtnm314
            } // endtimp(gs_print_a5(801))
            let jsxtnm316 = XATSDAPP(jsxtnm315(XATSSTRN("TMapp("), XATSP1CN("TMapp", jsxtnm264[0+1]), XATSSTRN(";"), XATSP1CN("TMapp", jsxtnm264[1+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm316
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(317);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(opr(5235)),I0Pvar(tms(5236))));$list(@(opr(5235),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(317));0)),@(tms(5236),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(317));1)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMopr",5))) { // gpt
            let jsxtnm317 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(1991(line=136,offs=1)--1997(line=136,offs=7))
            // I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a5(801);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
            // T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6927],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6928],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6929],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6930],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x4[6931],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2465],T2Pvar(x0[6927])),@(x1[2466],T2Pvar(x1[6928])),@(x2[2467],T2Pvar(x2[6929])),@(x3[2468],T2Pvar(x3[6930])),@(x4[2469],T2Pvar(x4[6931])))))))
            let jsxtnm647 = function (arg1, arg2, arg3, arg4, arg5) { // timp: gs_print_a5(801)
              let jsxtnm318 = arg1
              let jsxtnm319 = arg2
              let jsxtnm320 = arg3
              let jsxtnm321 = arg4
              let jsxtnm322 = arg5
              // I1CMP:start
              let jsxtnm646 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
                // I1VALDCL
                let jsxtnm326
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm324 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm323 = XATSTUP0([])
                  // I1CMP:return:jsxtnm323
                  return jsxtnm323
                } // endtimp(gs_print$beg(793))
                let jsxtnm325 = XATSDAPP(jsxtnm324())
                jsxtnm326 = jsxtnm325
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6927])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm332
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm331 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm327 = arg1
                  // I1CMP:start
                  let jsxtnm330 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(328);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(328)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm329 = XATSDAPP(XATS2JS_strn_print(jsxtnm327))
                    jsxtnm330 = jsxtnm329
                  } // endlet
                  // I1CMP:return:jsxtnm330
                  return jsxtnm330
                } // endtimp(strn_print(1029))
                jsxtnm332 = jsxtnm331
                let jsxtnm333 = XATSDAPP(jsxtnm332(jsxtnm318))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm335 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm334 = XATSTUP0([])
                  // I1CMP:return:jsxtnm334
                  return jsxtnm334
                } // endtimp(gs_print$sep(794))
                let jsxtnm336 = XATSDAPP(jsxtnm335())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6928])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm342
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm341 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm337 = arg1
                  // I1CMP:start
                  let jsxtnm340 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(338);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(338)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm339 = XATSDAPP(XATS2JS_strn_print(jsxtnm337))
                    jsxtnm340 = jsxtnm339
                  } // endlet
                  // I1CMP:return:jsxtnm340
                  return jsxtnm340
                } // endtimp(strn_print(1029))
                jsxtnm342 = jsxtnm341
                let jsxtnm343 = XATSDAPP(jsxtnm342(jsxtnm319))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm345 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm344 = XATSTUP0([])
                  // I1CMP:return:jsxtnm344
                  return jsxtnm344
                } // endtimp(gs_print$sep(794))
                let jsxtnm346 = XATSDAPP(jsxtnm345())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6929])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm352
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm351 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm347 = arg1
                  // I1CMP:start
                  let jsxtnm350 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(348);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(348)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm349 = XATSDAPP(XATS2JS_strn_print(jsxtnm347))
                    jsxtnm350 = jsxtnm349
                  } // endlet
                  // I1CMP:return:jsxtnm350
                  return jsxtnm350
                } // endtimp(strn_print(1029))
                jsxtnm352 = jsxtnm351
                let jsxtnm353 = XATSDAPP(jsxtnm352(jsxtnm320))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm355 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm354 = XATSTUP0([])
                  // I1CMP:return:jsxtnm354
                  return jsxtnm354
                } // endtimp(gs_print$sep(794))
                let jsxtnm356 = XATSDAPP(jsxtnm355())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6930])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3531(line=203,offs=1)--3606(line=208,offs=30)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))))>;I1Dtmpsub($list(@(x0[7318],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7318])))))))))
                let jsxtnm631 = function (arg1) { // timp: g_print(39)
                  let jsxtnm357 = arg1
                  // I1CMP:start
                  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3577(line=208,offs=1)--3587(line=208,offs=11))
                  // I0Etapq(I0Ecst(gseq_print(347)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2894(line=179,offs=1)--2904(line=179,offs=11))));$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pvar(x0[7318]),T2Pnone0())))),T2JAG($list(T2Pvar(x0[7318])))))
                  // T1IMPallx(gseq_print(347);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(2803(line=154,offs=1)--2864(line=157,offs=33)))
                  // T1IMPallx(gseq_print(347)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5966],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5967],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_print(347);$list(@(xs[1057],T2Pvar(xs[5966])),@(x0[1058],T2Pvar(x0[5967])))))))
                  let jsxtnm629
                  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(2845(line=157,offs=14)--2856(line=157,offs=25))
                  // I0Etapq(I0Ecst(gseq_print0(1658)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gseq000_vt.sats)@(3950(line=241,offs=1)--3961(line=241,offs=12))));$list(T2JAG($list(T2Pvar(xs[5966]))),T2JAG($list(T2Pvar(x0[5967])))))
                  // T1IMPallx(gseq_print0(1658);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3715(line=210,offs=1)--4381(line=277,offs=7)))
                  // T1IMPallx(gseq_print0(1658)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[7785],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[7786],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_print0(1658);$list(@(xs[4149],T2Pvar(xs[7785])),@(x0[4150],T2Pvar(x0[7786])))))))
                  let jsxtnm628 = function (arg1) { // timp: gseq_print0(1658)
                    let jsxtnm358 = arg1
                    // I1CMP:start
                    let jsxtnm627 // let
                    { // let
                      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3769(line=216,offs=1)--3811(line=218,offs=21)))
                      // I1VALDCL
                      let jsxtnm367
                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3778(line=217,offs=1)--3788(line=217,offs=11))
                      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                      let jsxtnm363 = function (arg1) { // timp: strn_print(1029)
                        let jsxtnm359 = arg1
                        // I1CMP:start
                        let jsxtnm362 // let
                        { // let
                          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                          // I1FUNDCL
                          // XATS2JS_strn_print_2202
                            // FJARGdarg($list(I1BNDcons(I1TNM(360);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(360)))))))
                            // I1CMP:start
                            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                          let jsxtnm361 = XATSDAPP(XATS2JS_strn_print(jsxtnm359))
                          jsxtnm362 = jsxtnm361
                        } // endlet
                        // I1CMP:return:jsxtnm362
                        return jsxtnm362
                      } // endtimp(strn_print(1029))
                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3792(line=218,offs=2)--3800(line=218,offs=10))
                      // I0Etapq(I0Ecst(gseq$beg(340)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2390(line=130,offs=1)--2398(line=130,offs=9))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                      // T1IMPallx(gseq$beg(340);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3473(line=198,offs=1)--3527(line=201,offs=27)))
                      // T1IMPallx(gseq$beg(340)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7317],T2Pcst(term)),@(x0[7317],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$beg(340);$list(@(xs[1043],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7317])))),@(x0[1044],T2Pvar(x0[7317])))))))
                      let jsxtnm364 = function () { // timp: gseq$beg(340)
                        // I1CMP:start
                        // I1CMP:return:XATSSTRN("list(")
                        return XATSSTRN("list(")
                      } // endtimp(gseq$beg(340))
                      let jsxtnm365 = XATSDAPP(jsxtnm364())
                      let jsxtnm366 = XATSDAPP(jsxtnm363(jsxtnm365))
                      jsxtnm367 = jsxtnm366
                      XATS000_patck(true)
                      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3815(line=220,offs=1)--4326(line=272,offs=2)))
                      // I1VALDCL
                      let jsxtnm617
                      let jsxtnm616 // let
                      { // let
                        // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3927(line=234,offs=1)--3964(line=236,offs=27)))
                        // I1VALDCL
                        let jsxtnm376
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3938(line=236,offs=1)--3948(line=236,offs=11))
                        // I0Etapq(I0Ecst(gseq$prlen(344)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2565(line=148,offs=1)--2575(line=148,offs=11))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                        // T1IMPallx(gseq$prlen(344);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(1709(line=64,offs=1)--1764(line=67,offs=27)))
                        // T1IMPallx(gseq$prlen(344)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5944],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5945],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$prlen(344);$list(@(xs[1051],T2Pvar(xs[5944])),@(x0[1052],T2Pvar(x0[5945])))))))
                        let jsxtnm374 = function () { // timp: gseq$prlen(344)
                          // I1CMP:start
                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(1760(line=67,offs=23)--1761(line=67,offs=24))
                          // I0Etapq(I0Ecst(sint_neg(914)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(1585(line=55,offs=1)--1593(line=55,offs=9))));$list(T2JAG($list())))
                          // T1IMPallx(sint_neg(914);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1430(line=40,offs=1)--1565(line=51,offs=31)))
                          // T1IMPallx(sint_neg(914)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_neg(914);$list()))))
                          let jsxtnm372 = function (arg1) { // timp: sint_neg(914)
                            let jsxtnm368 = arg1
                            // I1CMP:start
                            let jsxtnm371 // let
                            { // let
                              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1506(line=48,offs=1)--1563(line=51,offs=29)))
                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1514(line=49,offs=1)--1563(line=51,offs=29))
                              // I1FUNDCL
                              // XATS2JS_sint_neg_1517
                                // FJARGdarg($list(I1BNDcons(I1TNM(369);I0Pvar(i1(4899));$list(@(i1(4899),I1Vtnm(I1TNM(369)))))))
                                // I1CMP:start
                                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_neg);G1Nlist($list())) // I1CMP:return
                              let jsxtnm370 = XATSDAPP(XATS2JS_sint_neg(jsxtnm368))
                              jsxtnm371 = jsxtnm370
                            } // endlet
                            // I1CMP:return:jsxtnm371
                            return jsxtnm371
                          } // endtimp(sint_neg(914))
                          let jsxtnm373 = XATSDAPP(jsxtnm372(XATSINT1(1)))
                          // I1CMP:return:jsxtnm373
                          return jsxtnm373
                        } // endtimp(gseq$prlen(344))
                        let jsxtnm375 = XATSDAPP(jsxtnm374())
                        jsxtnm376 = jsxtnm375
                        XATS000_patck(true)
                        // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3968(line=238,offs=1)--4093(line=246,offs=32)))
                        // I1Dimplmnt0(DIMPLone2(iforitm$work0(1435);$list(@(x0[3740],T2Pvar(x0[7786]))))):timp
                        // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4097(line=248,offs=1)--4321(line=270,offs=32)))
                        // I1Dimplmnt0(DIMPLone2(iforall$test0(1419);$list(@(x0[3724],T2Pvar(x0[7786]))))):timp
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3833(line=223,offs=5)--3835(line=223,offs=7))
                        // I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
                        // T1IMPallx(sint_gte$sint(922);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
                        // T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
                        let jsxtnm407 = function (arg1, arg2) { // timp: sint_gte$sint(922)
                          let jsxtnm401 = arg1
                          let jsxtnm402 = arg2
                          // I1CMP:start
                          let jsxtnm406 // let
                          { // let
                            // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
                            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2396(line=123,offs=1)--2460(line=125,offs=39))
                            // I1FUNDCL
                            // XATS2JS_sint_gte$sint_2399
                              // FJARGdarg($list(I1BNDcons(I1TNM(403);I0Pvar(i1(4923));$list(@(i1(4923),I1Vtnm(I1TNM(403))))),I1BNDcons(I1TNM(404);I0Pvar(i2(4924));$list(@(i2(4924),I1Vtnm(I1TNM(404)))))))
                              // I1CMP:start
                              // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_gte$sint);G1Nlist($list())) // I1CMP:return
                            let jsxtnm405 = XATSDAPP(XATS2JS_sint_gte$sint(jsxtnm401, jsxtnm402))
                            jsxtnm406 = jsxtnm405
                          } // endlet
                          // I1CMP:return:jsxtnm406
                          return jsxtnm406
                        } // endtimp(sint_gte$sint(922))
                        let jsxtnm408 = XATSDAPP(jsxtnm407(jsxtnm376, XATSINT1(0)))
                        let jsxtnm615 // ift
                        if (jsxtnm408) // ift
                        {
                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3844(line=225,offs=1)--3850(line=225,offs=7))
                          // I0Etapq(I0Ecst(g_void(21)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(1486(line=46,offs=1)--1492(line=46,offs=7))));$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))))))
                          // T1IMPallx(g_void(21);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas000.dats)@(1416(line=41,offs=1)--1455(line=43,offs=21)))
                          // T1IMPallx(g_void(21)<$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5663],T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_void(21);$list(@(a[416],T2Pvar(x0[5663])))))))
                          let jsxtnm411 = function (arg1) { // timp: g_void(21)
                            let jsxtnm409 = arg1
                            // I1CMP:start
                            let jsxtnm410 = XATSTUP0([])
                            // I1CMP:return:jsxtnm410
                            return jsxtnm410
                          } // endtimp(g_void(21))
                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3853(line=227,offs=1)--3866(line=227,offs=14))
                          // I0Etapq(I0Ecst(gseq_iforall0(1708)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gseq001_vt.sats)@(6472(line=342,offs=1)--6485(line=342,offs=14))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                          // T1IMPallx(gseq_iforall0(1708);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2821(line=159,offs=1)--2955(line=169,offs=2)))
                          // T1IMPallx(gseq_iforall0(1708)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8681],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8682],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforall0(1708);$list(@(xs[4287],T2Pvar(xs[8681])),@(x0[4288],T2Pvar(x0[8682])))))))
                          let jsxtnm512 = function (arg1) { // timp: gseq_iforall0(1708)
                            let jsxtnm412 = arg1
                            // I1CMP:start
                            let jsxtnm511 // let
                            { // let
                              // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2908(line=167,offs=1)--2953(line=168,offs=37)))
                              // I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[449],T2Pvar(x0[8682]))))):timp
                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2874(line=164,offs=3)--2886(line=164,offs=15))
                              // I0Etapq(I0Ecst(gseq_iforall(384)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3907(line=226,offs=1)--3919(line=226,offs=13))));$list(T2JAG($list(T2Pvar(xs[8681]))),T2JAG($list(T2Pvar(x0[8682])))))
                              // T1IMPallx(gseq_iforall(384);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4419(line=260,offs=1)--4718(line=286,offs=2)))
                              // T1IMPallx(gseq_iforall(384)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6012],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6013],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforall(384);$list(@(xs[1151],T2Pvar(xs[6012])),@(x0[1152],T2Pvar(x0[6013])))))))
                              let jsxtnm509 = function (arg1) { // timp: gseq_iforall(384)
                                let jsxtnm413 = arg1
                                // I1CMP:start
                                let jsxtnm508 // let
                                { // let
                                  // I1Dvardclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4486(line=267,offs=1)--4502(line=267,offs=17)))
                                  // I1VARDCL
                                  // I1CMP:start
                                  // I1CMP:return:XATSINT1(0)
                                  let jsxtnm414 = XATSVAR1(XATSINT1(0))
                                  // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4506(line=269,offs=1)--4524(line=269,offs=19)))
                                  // I1VALDCL
                                  let jsxtnm415
                                  jsxtnm415 = XATSADDR(jsxtnm414)
                                  XATS000_patck(true)
                                  // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4528(line=271,offs=1)--4713(line=284,offs=2)))
                                  // I1VALDCL
                                  let jsxtnm507
                                  let jsxtnm506 // let
                                  { // let
                                    // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                                    // I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[447],T2Pvar(x0[6013]))))):timp
                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4539(line=273,offs=1)--4550(line=273,offs=12))
                                    // I0Etapq(I0Ecst(gseq_forall(380)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3721(line=210,offs=1)--3732(line=210,offs=12))));$list(T2JAG($list(T2Pvar(xs[6012]))),T2JAG($list(T2Pvar(x0[6013])))))
                                    // T1IMPallx(gseq_forall(380);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1841(line=78,offs=1)--1904(line=81,offs=33)))
                                    // T1IMPallx(gseq_forall(380)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7367],T2Pcst(term)),@(x0[7367],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_forall(380);$list(@(xs[1143],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7367])))),@(x0[1144],T2Pvar(x0[7367])))))))
                                    let jsxtnm504
                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1889(line=81,offs=18)--1900(line=81,offs=29))
                                    // I0Etapq(I0Ecst(list_forall(1206)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(2160(line=92,offs=1)--2171(line=92,offs=12))));$list(T2JAG($list(T2Pvar(x0[7367])))))
                                    // T1IMPallx(list_forall(1206);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1591(line=53,offs=1)--1837(line=76,offs=2)))
                                    // T1IMPallx(list_forall(1206)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7366],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_forall(1206);$list(@(x0[3372],T2Pvar(x0[7366])))))))
                                    let jsxtnm503 = function (arg1) { // timp: list_forall(1206)
                                      let jsxtnm424 = arg1
                                      // I1CMP:start
                                      let jsxtnm502 // let
                                      { // let
                                        // I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1657(line=60,offs=1)--1835(line=75,offs=31)))
                                        // I1FUNDCL
                                        function loop_1660(arg1)
                                        { // fun
                                          let jsxtnm425 = arg1
                                          // I1CMP:start
                                          let jsxtnm500 // cas
                                          do {
                                            // { // cls
                                            // I1GPTpat(I1BNDcons(I1TNM(426);I0Pfree(I0Pdapp(I0Pcon(list_nil(8));$list()));$list()))
                                            if (XATS000_ctgeq(jsxtnm425, XATSCTAG("list_nil",0))) { // gpt
                                              let jsxtnm426 = jsxtnm425
                                              jsxtnm500 = XATSBOOL(true)
                                              break // cls
                                            } // gpt
                                            // } // cls
                                            // { // cls
                                            // I1GPTpat(I1BNDcons(I1TNM(427);I0Pfree(I0Pdapp(I0Pcon(list_cons(9));$list(I0Pvar(x1(2569)),I0Pvar(xs(2570)))));$list(@(x1(2569),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(427));0)),@(xs(2570),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(427));1)))))
                                            if (XATS000_ctgeq(jsxtnm425, XATSCTAG("list_cons",1))) { // gpt
                                              let jsxtnm427 = jsxtnm425
                                              let jsxtnm499 // let
                                              { // let
                                                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1761(line=71,offs=1)--1791(line=72,offs=20)))
                                                // I1VALDCL
                                                let jsxtnm496
                                                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1772(line=72,offs=1)--1783(line=72,offs=12))
                                                // I0Etapq(I0Ecst(forall$test(47)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2003(line=96,offs=1)--2014(line=96,offs=12))));$list(T2JAG($list(T2Pvar(x0[7366])))))
                                                // T1IMPallx(forall$test(47);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                                                // T1IMPallx(forall$test(47)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6012],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6013],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[447],T2Pcst(term)))))))
                                                let jsxtnm494 = function (arg1) { // timp: forall$test(47)
                                                  let jsxtnm428 = arg1
                                                  // I1CMP:start
                                                  let jsxtnm493 // let
                                                  { // let
                                                    // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4646(line=282,offs=1)--4675(line=282,offs=30)))
                                                    // I1VALDCL
                                                    let jsxtnm433
                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4659(line=282,offs=14)--4667(line=282,offs=22))
                                                    // I0Etapq(I0Ecst(p2tr_get(2280)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2573(line=124,offs=1)--2581(line=124,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                                                    // T1IMPallx(p2tr_get(2280);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(197(line=15,offs=1)--245(line=18,offs=17)))
                                                    // T1IMPallx(p2tr_get(2280)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5818],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_get(2280);$list(@(a[5620],T2Pvar(a[5818])))))))
                                                    let jsxtnm431 = function (arg1) { // timp: p2tr_get(2280)
                                                      let jsxtnm429 = arg1
                                                      // I1CMP:start
                                                      let jsxtnm430 = XATS000_dp2tr(jsxtnm429)
                                                      // I1CMP:return:jsxtnm430
                                                      return jsxtnm430
                                                    } // endtimp(p2tr_get(2280))
                                                    let jsxtnm432 = XATSDAPP(jsxtnm431(jsxtnm415))
                                                    jsxtnm433 = jsxtnm432
                                                    XATS000_patck(true)
                                                    // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4676(line=283,offs=1)--4709(line=283,offs=34)))
                                                    // I1VALDCL
                                                    let jsxtnm480
                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4685(line=283,offs=10)--4697(line=283,offs=22))
                                                    // I0Etapq(I0Ecst(iforall$test(49)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2080(line=102,offs=1)--2092(line=102,offs=13))));$list(T2JAG($list(T2Pvar(x0[6013])))))
                                                    // T1IMPallx(iforall$test(49);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2908(line=167,offs=1)--2953(line=168,offs=37)))
                                                    // T1IMPallx(iforall$test(49)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8681],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8682],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[449],T2Pcst(term)))))))
                                                    let jsxtnm478
                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2936(line=168,offs=20)--2949(line=168,offs=33))
                                                    // I0Etapq(I0Ecst(iforall$test0(1419)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas001_vt.sats)@(2570(line=145,offs=1)--2583(line=145,offs=14))));$list(T2JAG($list(T2Pvar(x0[8682])))))
                                                    // T1IMPallx(iforall$test0(1419);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4097(line=248,offs=1)--4321(line=270,offs=32)))
                                                    // T1IMPallx(iforall$test0(1419)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[7785],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[7786],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforall$test0(1419);$list(@(x0[3724],T2Pcst(term)))))))
                                                    let jsxtnm477 = function (arg1, arg2) { // timp: iforall$test0(1419)
                                                      let jsxtnm434 = arg1
                                                      let jsxtnm435 = arg2
                                                      // I1CMP:start
                                                      let jsxtnm476 // let
                                                      { // let
                                                        // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4266(line=268,offs=1)--4320(line=270,offs=31)))
                                                        // I1VALDCL
                                                        let jsxtnm453
                                                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4281(line=269,offs=7)--4282(line=269,offs=8))
                                                        // I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
                                                        // T1IMPallx(sint_gt$sint(919);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
                                                        // T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
                                                        let jsxtnm442 = function (arg1, arg2) { // timp: sint_gt$sint(919)
                                                          let jsxtnm436 = arg1
                                                          let jsxtnm437 = arg2
                                                          // I1CMP:start
                                                          let jsxtnm441 // let
                                                          { // let
                                                            // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
                                                            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1873(line=79,offs=1)--1936(line=81,offs=39))
                                                            // I1FUNDCL
                                                            // XATS2JS_sint_gt$sint_1876
                                                              // FJARGdarg($list(I1BNDcons(I1TNM(438);I0Pvar(i1(4908));$list(@(i1(4908),I1Vtnm(I1TNM(438))))),I1BNDcons(I1TNM(439);I0Pvar(i2(4909));$list(@(i2(4909),I1Vtnm(I1TNM(439)))))))
                                                              // I1CMP:start
                                                              // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_gt$sint);G1Nlist($list())) // I1CMP:return
                                                            let jsxtnm440 = XATSDAPP(XATS2JS_sint_gt$sint(jsxtnm436, jsxtnm437))
                                                            jsxtnm441 = jsxtnm440
                                                          } // endlet
                                                          // I1CMP:return:jsxtnm441
                                                          return jsxtnm441
                                                        } // endtimp(sint_gt$sint(919))
                                                        let jsxtnm443 = XATSDAPP(jsxtnm442(jsxtnm434, XATSINT1(0)))
                                                        let jsxtnm452 // ift
                                                        if (jsxtnm443) // ift
                                                        {
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4290(line=270,offs=1)--4300(line=270,offs=11))
                                                          // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                                                          // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                                                          // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                                                          let jsxtnm448 = function (arg1) { // timp: strn_print(1029)
                                                            let jsxtnm444 = arg1
                                                            // I1CMP:start
                                                            let jsxtnm447 // let
                                                            { // let
                                                              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                                                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                                                              // I1FUNDCL
                                                              // XATS2JS_strn_print_2202
                                                                // FJARGdarg($list(I1BNDcons(I1TNM(445);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(445)))))))
                                                                // I1CMP:start
                                                                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                                                              let jsxtnm446 = XATSDAPP(XATS2JS_strn_print(jsxtnm444))
                                                              jsxtnm447 = jsxtnm446
                                                            } // endlet
                                                            // I1CMP:return:jsxtnm447
                                                            return jsxtnm447
                                                          } // endtimp(strn_print(1029))
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4301(line=270,offs=12)--4309(line=270,offs=20))
                                                          // I0Etapq(I0Ecst(gseq$sep(342)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2474(line=138,offs=1)--2482(line=138,offs=9))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                                                          // T1IMPallx(gseq$sep(342);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3371(line=190,offs=1)--3421(line=193,offs=23)))
                                                          // T1IMPallx(gseq$sep(342)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7315],T2Pcst(term)),@(x0[7315],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$sep(342);$list(@(xs[1047],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7315])))),@(x0[1048],T2Pvar(x0[7315])))))))
                                                          let jsxtnm449 = function () { // timp: gseq$sep(342)
                                                            // I1CMP:start
                                                            // I1CMP:return:XATSSTRN(",")
                                                            return XATSSTRN(",")
                                                          } // endtimp(gseq$sep(342))
                                                          let jsxtnm450 = XATSDAPP(jsxtnm449())
                                                          let jsxtnm451 = XATSDAPP(jsxtnm448(jsxtnm450))
                                                          jsxtnm452 = jsxtnm451
                                                        } else {
                                                        } // end(if)
                                                        jsxtnm453 = jsxtnm452
                                                        XATS000_patck(true)
                                                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4145(line=253,offs=4)--4147(line=253,offs=6))
                                                        // I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
                                                        // T1IMPallx(sint_gte$sint(922);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
                                                        // T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
                                                        let jsxtnm460 = function (arg1, arg2) { // timp: sint_gte$sint(922)
                                                          let jsxtnm454 = arg1
                                                          let jsxtnm455 = arg2
                                                          // I1CMP:start
                                                          let jsxtnm459 // let
                                                          { // let
                                                            // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
                                                            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2396(line=123,offs=1)--2460(line=125,offs=39))
                                                            // I1FUNDCL
                                                            // XATS2JS_sint_gte$sint_2399
                                                              // FJARGdarg($list(I1BNDcons(I1TNM(456);I0Pvar(i1(4923));$list(@(i1(4923),I1Vtnm(I1TNM(456))))),I1BNDcons(I1TNM(457);I0Pvar(i2(4924));$list(@(i2(4924),I1Vtnm(I1TNM(457)))))))
                                                              // I1CMP:start
                                                              // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_gte$sint);G1Nlist($list())) // I1CMP:return
                                                            let jsxtnm458 = XATSDAPP(XATS2JS_sint_gte$sint(jsxtnm454, jsxtnm455))
                                                            jsxtnm459 = jsxtnm458
                                                          } // endlet
                                                          // I1CMP:return:jsxtnm459
                                                          return jsxtnm459
                                                        } // endtimp(sint_gte$sint(922))
                                                        let jsxtnm461 = XATSDAPP(jsxtnm460(jsxtnm434, jsxtnm376))
                                                        let jsxtnm475 // ift
                                                        if (jsxtnm461) // ift
                                                        {
                                                          let jsxtnm471 // let
                                                          { // let
                                                            // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4179(line=259,offs=1)--4220(line=261,offs=22)))
                                                            // I1VALDCL
                                                            let jsxtnm470
                                                            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4188(line=260,offs=1)--4198(line=260,offs=11))
                                                            // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                                                            // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                                                            // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                                                            let jsxtnm466 = function (arg1) { // timp: strn_print(1029)
                                                              let jsxtnm462 = arg1
                                                              // I1CMP:start
                                                              let jsxtnm465 // let
                                                              { // let
                                                                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                                                                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                                                                // I1FUNDCL
                                                                // XATS2JS_strn_print_2202
                                                                  // FJARGdarg($list(I1BNDcons(I1TNM(463);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(463)))))))
                                                                  // I1CMP:start
                                                                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                                                                let jsxtnm464 = XATSDAPP(XATS2JS_strn_print(jsxtnm462))
                                                                jsxtnm465 = jsxtnm464
                                                              } // endlet
                                                              // I1CMP:return:jsxtnm465
                                                              return jsxtnm465
                                                            } // endtimp(strn_print(1029))
                                                            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4200(line=261,offs=2)--4209(line=261,offs=11))
                                                            // I0Etapq(I0Ecst(gseq$omit(343)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2519(line=143,offs=1)--2528(line=143,offs=10))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                                                            // T1IMPallx(gseq$omit(343);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(1627(line=57,offs=1)--1682(line=60,offs=27)))
                                                            // T1IMPallx(gseq$omit(343)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5942],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5943],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$omit(343);$list(@(xs[1049],T2Pvar(xs[5942])),@(x0[1050],T2Pvar(x0[5943])))))))
                                                            let jsxtnm467 = function () { // timp: gseq$omit(343)
                                                              // I1CMP:start
                                                              // I1CMP:return:XATSSTRN("...")
                                                              return XATSSTRN("...")
                                                            } // endtimp(gseq$omit(343))
                                                            let jsxtnm468 = XATSDAPP(jsxtnm467())
                                                            let jsxtnm469 = XATSDAPP(jsxtnm466(jsxtnm468))
                                                            jsxtnm470 = jsxtnm469
                                                            XATS000_patck(true)
                                                            jsxtnm471 = XATSBOOL(false)
                                                          } // endlet
                                                          jsxtnm475 = jsxtnm471
                                                        } else {
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4233(line=265,offs=1)--4241(line=265,offs=9))
                                                          // I0Etapq(I0Ecst(g_print0(1398)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas000_vt.sats)@(2080(line=106,offs=1)--2088(line=106,offs=9))));$list(T2JAG($list(T2Pvar(x0[7786])))))
                                                          // T1IMPallx(g_print0(1398);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1589(line=56,offs=1)--1634(line=58,offs=27)))
                                                          // T1IMPallx(g_print0(1398)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8663],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(g_print0(1398);$list(@(x0[3698],T2Pvar(x0[8663])))))))
                                                          let jsxtnm473
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1623(line=58,offs=16)--1630(line=58,offs=23))
                                                          // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[8663])))))
                                                          // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                                                          // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                                                          let jsxtnm472
                                                          jsxtnm472 = auxpr_1677
                                                          jsxtnm473 = jsxtnm472
                                                          let jsxtnm474 = XATSDAPP(jsxtnm473(jsxtnm435))
                                                          jsxtnm475 = XATSBOOL(true)
                                                        } // end(if)
                                                        jsxtnm476 = jsxtnm475
                                                      } // endlet
                                                      // I1CMP:return:jsxtnm476
                                                      return jsxtnm476
                                                    } // endtimp(iforall$test0(1419))
                                                    jsxtnm478 = jsxtnm477
                                                    let jsxtnm479 = XATSDAPP(jsxtnm478(jsxtnm433, jsxtnm428))
                                                    jsxtnm480 = jsxtnm479
                                                    XATS000_patck(true)
                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4610(line=279,offs=5)--4618(line=279,offs=13))
                                                    // I0Etapq(I0Ecst(p2tr_set(2281)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2611(line=127,offs=1)--2619(line=127,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                                                    // T1IMPallx(p2tr_set(2281);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(246(line=19,offs=1)--305(line=22,offs=27)))
                                                    // T1IMPallx(p2tr_set(2281)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5819],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_set(2281);$list(@(a[5621],T2Pvar(a[5819])))))))
                                                    let jsxtnm483 = function (arg1, arg2) { // timp: p2tr_set(2281)
                                                      let jsxtnm481 = arg1
                                                      let jsxtnm482 = arg2
                                                      // I1CMP:start
                                                      XATS000_assgn(jsxtnm481, jsxtnm482)
                                                      // I1CMP:return:[]
                                                      return []
                                                    } // endtimp(p2tr_set(2281))
                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4629(line=279,offs=24)--4630(line=279,offs=25))
                                                    // I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
                                                    // T1IMPallx(sint_add$sint(925);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
                                                    // T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
                                                    let jsxtnm490 = function (arg1, arg2) { // timp: sint_add$sint(925)
                                                      let jsxtnm484 = arg1
                                                      let jsxtnm485 = arg2
                                                      // I1CMP:start
                                                      let jsxtnm489 // let
                                                      { // let
                                                        // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
                                                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2775(line=154,offs=1)--2839(line=156,offs=39))
                                                        // I1FUNDCL
                                                        // XATS2JS_sint_add$sint_2778
                                                          // FJARGdarg($list(I1BNDcons(I1TNM(486);I0Pvar(i1(4933));$list(@(i1(4933),I1Vtnm(I1TNM(486))))),I1BNDcons(I1TNM(487);I0Pvar(i2(4934));$list(@(i2(4934),I1Vtnm(I1TNM(487)))))))
                                                          // I1CMP:start
                                                          // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_add$sint);G1Nlist($list())) // I1CMP:return
                                                        let jsxtnm488 = XATSDAPP(XATS2JS_sint_add$sint(jsxtnm484, jsxtnm485))
                                                        jsxtnm489 = jsxtnm488
                                                      } // endlet
                                                      // I1CMP:return:jsxtnm489
                                                      return jsxtnm489
                                                    } // endtimp(sint_add$sint(925))
                                                    let jsxtnm491 = XATSDAPP(jsxtnm490(jsxtnm433, XATSINT1(1)))
                                                    let jsxtnm492 = XATSDAPP(jsxtnm483(jsxtnm415, jsxtnm491))
                                                    jsxtnm493 = jsxtnm480
                                                  } // endlet
                                                  // I1CMP:return:jsxtnm493
                                                  return jsxtnm493
                                                } // endtimp(forall$test(47))
                                                let jsxtnm495 = XATSDAPP(jsxtnm494(XATSP1CN("list_cons", jsxtnm427[0+1])))
                                                jsxtnm496 = jsxtnm495
                                                XATS000_patck(true)
                                                let jsxtnm498 // ift
                                                if (jsxtnm496) // ift
                                                {
                                                  let jsxtnm497 = XATSDAPP(loop_1660(XATSP1CN("list_cons", jsxtnm427[1+1])))
                                                  jsxtnm498 = jsxtnm497
                                                } else {
                                                  jsxtnm498 = XATSBOOL(false)
                                                } // end(if)
                                                jsxtnm499 = jsxtnm498
                                              } // endlet
                                              jsxtnm500 = jsxtnm499
                                              break // cls
                                            } // gpt
                                            // } // cls
                                            XATS000_cfail()
                                          } while (false) // end-of(do)
                                          // I1CMP:return:jsxtnm500
                                          return jsxtnm500
                                        } // endfun(loop_1660)
                                        let jsxtnm501 = XATSDAPP(loop_1660(jsxtnm424))
                                        jsxtnm502 = jsxtnm501
                                      } // endlet
                                      // I1CMP:return:jsxtnm502
                                      return jsxtnm502
                                    } // endtimp(list_forall(1206))
                                    jsxtnm504 = jsxtnm503
                                    let jsxtnm505 = XATSDAPP(jsxtnm504(jsxtnm413))
                                    jsxtnm506 = jsxtnm505
                                  } // endlet
                                  jsxtnm507 = jsxtnm506
                                  XATS000_patck(true)
                                  jsxtnm508 = jsxtnm507
                                } // endlet
                                // I1CMP:return:jsxtnm508
                                return jsxtnm508
                              } // endtimp(gseq_iforall(384))
                              let jsxtnm510 = XATSDAPP(jsxtnm509(jsxtnm412))
                              jsxtnm511 = jsxtnm510
                            } // endlet
                            // I1CMP:return:jsxtnm511
                            return jsxtnm511
                          } // endtimp(gseq_iforall0(1708))
                          let jsxtnm513 = XATSDAPP(jsxtnm512(jsxtnm358))
                          let jsxtnm514 = XATSDAPP(jsxtnm411(jsxtnm513))
                          jsxtnm615 = jsxtnm514
                        } else {
                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3887(line=230,offs=1)--3900(line=230,offs=14))
                          // I0Etapq(I0Ecst(gseq_iforitm0(1732)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gseq001_vt.sats)@(10830(line=584,offs=1)--10843(line=584,offs=14))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                          // T1IMPallx(gseq_iforitm0(1732);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5533(line=373,offs=1)--5667(line=383,offs=2)))
                          // T1IMPallx(gseq_iforitm0(1732)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8721],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8722],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforitm0(1732);$list(@(xs[4335],T2Pvar(xs[8721])),@(x0[4336],T2Pvar(x0[8722])))))))
                          let jsxtnm613 = function (arg1) { // timp: gseq_iforitm0(1732)
                            let jsxtnm515 = arg1
                            // I1CMP:start
                            let jsxtnm612 // let
                            { // let
                              // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5620(line=381,offs=1)--5665(line=382,offs=37)))
                              // I1Dimplmnt0(DIMPLone2(iforitm$work(53);$list(@(x0[453],T2Pvar(x0[8722]))))):timp
                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5586(line=378,offs=3)--5598(line=378,offs=15))
                              // I0Etapq(I0Ecst(gseq_iforitm(398)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(7171(line=410,offs=1)--7183(line=410,offs=13))));$list(T2JAG($list(T2Pvar(xs[8721]))),T2JAG($list(T2Pvar(x0[8722])))))
                              // T1IMPallx(gseq_iforitm(398);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7318(line=471,offs=1)--7515(line=488,offs=2)))
                              // T1IMPallx(gseq_iforitm(398)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6036],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6037],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforitm(398);$list(@(xs[1195],T2Pvar(xs[6036])),@(x0[1196],T2Pvar(x0[6037])))))))
                              let jsxtnm610 = function (arg1) { // timp: gseq_iforitm(398)
                                let jsxtnm516 = arg1
                                // I1CMP:start
                                let jsxtnm609 // let
                                { // let
                                  // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7430(line=483,offs=1)--7513(line=487,offs=36)))
                                  // I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[449],T2Pvar(x0[6037]))))):timp
                                  let jsxtnm608 // let
                                  { // let
                                    // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7377(line=478,offs=1)--7410(line=480,offs=13)))
                                    // I1VALDCL
                                    let jsxtnm607
                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7385(line=479,offs=1)--7397(line=479,offs=13))
                                    // I0Etapq(I0Ecst(gseq_iforall(384)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3907(line=226,offs=1)--3919(line=226,offs=13))));$list(T2JAG($list(T2Pvar(xs[6036]))),T2JAG($list(T2Pvar(x0[6037])))))
                                    // T1IMPallx(gseq_iforall(384);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4419(line=260,offs=1)--4718(line=286,offs=2)))
                                    // T1IMPallx(gseq_iforall(384)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6012],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6013],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforall(384);$list(@(xs[1151],T2Pvar(xs[6012])),@(x0[1152],T2Pvar(x0[6013])))))))
                                    let jsxtnm605 = function (arg1) { // timp: gseq_iforall(384)
                                      let jsxtnm522 = arg1
                                      // I1CMP:start
                                      let jsxtnm604 // let
                                      { // let
                                        // I1Dvardclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4486(line=267,offs=1)--4502(line=267,offs=17)))
                                        // I1VARDCL
                                        // I1CMP:start
                                        // I1CMP:return:XATSINT1(0)
                                        let jsxtnm523 = XATSVAR1(XATSINT1(0))
                                        // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4506(line=269,offs=1)--4524(line=269,offs=19)))
                                        // I1VALDCL
                                        let jsxtnm524
                                        jsxtnm524 = XATSADDR(jsxtnm523)
                                        XATS000_patck(true)
                                        // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4528(line=271,offs=1)--4713(line=284,offs=2)))
                                        // I1VALDCL
                                        let jsxtnm603
                                        let jsxtnm602 // let
                                        { // let
                                          // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                                          // I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[447],T2Pvar(x0[6013]))))):timp
                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4539(line=273,offs=1)--4550(line=273,offs=12))
                                          // I0Etapq(I0Ecst(gseq_forall(380)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3721(line=210,offs=1)--3732(line=210,offs=12))));$list(T2JAG($list(T2Pvar(xs[6012]))),T2JAG($list(T2Pvar(x0[6013])))))
                                          // T1IMPallx(gseq_forall(380);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1841(line=78,offs=1)--1904(line=81,offs=33)))
                                          // T1IMPallx(gseq_forall(380)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7367],T2Pcst(term)),@(x0[7367],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_forall(380);$list(@(xs[1143],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7367])))),@(x0[1144],T2Pvar(x0[7367])))))))
                                          let jsxtnm600
                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1889(line=81,offs=18)--1900(line=81,offs=29))
                                          // I0Etapq(I0Ecst(list_forall(1206)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(2160(line=92,offs=1)--2171(line=92,offs=12))));$list(T2JAG($list(T2Pvar(x0[7367])))))
                                          // T1IMPallx(list_forall(1206);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1591(line=53,offs=1)--1837(line=76,offs=2)))
                                          // T1IMPallx(list_forall(1206)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7366],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_forall(1206);$list(@(x0[3372],T2Pvar(x0[7366])))))))
                                          let jsxtnm599 = function (arg1) { // timp: list_forall(1206)
                                            let jsxtnm533 = arg1
                                            // I1CMP:start
                                            let jsxtnm598 // let
                                            { // let
                                              // I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1657(line=60,offs=1)--1835(line=75,offs=31)))
                                              // I1FUNDCL
                                              function loop_1660(arg1)
                                              { // fun
                                                let jsxtnm534 = arg1
                                                // I1CMP:start
                                                let jsxtnm596 // cas
                                                do {
                                                  // { // cls
                                                  // I1GPTpat(I1BNDcons(I1TNM(535);I0Pfree(I0Pdapp(I0Pcon(list_nil(8));$list()));$list()))
                                                  if (XATS000_ctgeq(jsxtnm534, XATSCTAG("list_nil",0))) { // gpt
                                                    let jsxtnm535 = jsxtnm534
                                                    jsxtnm596 = XATSBOOL(true)
                                                    break // cls
                                                  } // gpt
                                                  // } // cls
                                                  // { // cls
                                                  // I1GPTpat(I1BNDcons(I1TNM(536);I0Pfree(I0Pdapp(I0Pcon(list_cons(9));$list(I0Pvar(x1(2569)),I0Pvar(xs(2570)))));$list(@(x1(2569),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(536));0)),@(xs(2570),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(536));1)))))
                                                  if (XATS000_ctgeq(jsxtnm534, XATSCTAG("list_cons",1))) { // gpt
                                                    let jsxtnm536 = jsxtnm534
                                                    let jsxtnm595 // let
                                                    { // let
                                                      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1761(line=71,offs=1)--1791(line=72,offs=20)))
                                                      // I1VALDCL
                                                      let jsxtnm592
                                                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1772(line=72,offs=1)--1783(line=72,offs=12))
                                                      // I0Etapq(I0Ecst(forall$test(47)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2003(line=96,offs=1)--2014(line=96,offs=12))));$list(T2JAG($list(T2Pvar(x0[7366])))))
                                                      // T1IMPallx(forall$test(47);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                                                      // T1IMPallx(forall$test(47)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6012],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6013],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[447],T2Pcst(term)))))))
                                                      let jsxtnm590 = function (arg1) { // timp: forall$test(47)
                                                        let jsxtnm537 = arg1
                                                        // I1CMP:start
                                                        let jsxtnm589 // let
                                                        { // let
                                                          // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4646(line=282,offs=1)--4675(line=282,offs=30)))
                                                          // I1VALDCL
                                                          let jsxtnm542
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4659(line=282,offs=14)--4667(line=282,offs=22))
                                                          // I0Etapq(I0Ecst(p2tr_get(2280)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2573(line=124,offs=1)--2581(line=124,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                                                          // T1IMPallx(p2tr_get(2280);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(197(line=15,offs=1)--245(line=18,offs=17)))
                                                          // T1IMPallx(p2tr_get(2280)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5818],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_get(2280);$list(@(a[5620],T2Pvar(a[5818])))))))
                                                          let jsxtnm540 = function (arg1) { // timp: p2tr_get(2280)
                                                            let jsxtnm538 = arg1
                                                            // I1CMP:start
                                                            let jsxtnm539 = XATS000_dp2tr(jsxtnm538)
                                                            // I1CMP:return:jsxtnm539
                                                            return jsxtnm539
                                                          } // endtimp(p2tr_get(2280))
                                                          let jsxtnm541 = XATSDAPP(jsxtnm540(jsxtnm524))
                                                          jsxtnm542 = jsxtnm541
                                                          XATS000_patck(true)
                                                          // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4676(line=283,offs=1)--4709(line=283,offs=34)))
                                                          // I1VALDCL
                                                          let jsxtnm576
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4685(line=283,offs=10)--4697(line=283,offs=22))
                                                          // I0Etapq(I0Ecst(iforall$test(49)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2080(line=102,offs=1)--2092(line=102,offs=13))));$list(T2JAG($list(T2Pvar(x0[6013])))))
                                                          // T1IMPallx(iforall$test(49);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7430(line=483,offs=1)--7513(line=487,offs=36)))
                                                          // T1IMPallx(iforall$test(49)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6036],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6037],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[449],T2Pcst(term)))))))
                                                          let jsxtnm574 = function (arg1, arg2) { // timp: iforall$test(49)
                                                            let jsxtnm543 = arg1
                                                            let jsxtnm544 = arg2
                                                            // I1CMP:start
                                                            let jsxtnm573 // let
                                                            { // let
                                                              // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7469(line=486,offs=1)--7501(line=487,offs=24)))
                                                              // I1VALDCL
                                                              let jsxtnm572
                                                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7478(line=487,offs=1)--7490(line=487,offs=13))
                                                              // I0Etapq(I0Ecst(iforitm$work(53)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2418(line=130,offs=1)--2430(line=130,offs=13))));$list(T2JAG($list(T2Pvar(x0[6037])))))
                                                              // T1IMPallx(iforitm$work(53);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5620(line=381,offs=1)--5665(line=382,offs=37)))
                                                              // T1IMPallx(iforitm$work(53)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8721],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8722],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforitm$work(53);$list(@(x0[453],T2Pcst(term)))))))
                                                              let jsxtnm570
                                                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5648(line=382,offs=20)--5661(line=382,offs=33))
                                                              // I0Etapq(I0Ecst(iforitm$work0(1435)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas001_vt.sats)@(3293(line=203,offs=1)--3306(line=203,offs=14))));$list(T2JAG($list(T2Pvar(x0[8722])))))
                                                              // T1IMPallx(iforitm$work0(1435);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3968(line=238,offs=1)--4093(line=246,offs=32)))
                                                              // T1IMPallx(iforitm$work0(1435)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[7785],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[7786],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforitm$work0(1435);$list(@(x0[3740],T2Pcst(term)))))))
                                                              let jsxtnm569 = function (arg1, arg2) { // timp: iforitm$work0(1435)
                                                                let jsxtnm545 = arg1
                                                                let jsxtnm546 = arg2
                                                                // I1CMP:start
                                                                let jsxtnm568 // let
                                                                { // let
                                                                  // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4038(line=244,offs=1)--4092(line=246,offs=31)))
                                                                  // I1VALDCL
                                                                  let jsxtnm564
                                                                  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4053(line=245,offs=7)--4054(line=245,offs=8))
                                                                  // I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
                                                                  // T1IMPallx(sint_gt$sint(919);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
                                                                  // T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
                                                                  let jsxtnm553 = function (arg1, arg2) { // timp: sint_gt$sint(919)
                                                                    let jsxtnm547 = arg1
                                                                    let jsxtnm548 = arg2
                                                                    // I1CMP:start
                                                                    let jsxtnm552 // let
                                                                    { // let
                                                                      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
                                                                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1873(line=79,offs=1)--1936(line=81,offs=39))
                                                                      // I1FUNDCL
                                                                      // XATS2JS_sint_gt$sint_1876
                                                                        // FJARGdarg($list(I1BNDcons(I1TNM(549);I0Pvar(i1(4908));$list(@(i1(4908),I1Vtnm(I1TNM(549))))),I1BNDcons(I1TNM(550);I0Pvar(i2(4909));$list(@(i2(4909),I1Vtnm(I1TNM(550)))))))
                                                                        // I1CMP:start
                                                                        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_gt$sint);G1Nlist($list())) // I1CMP:return
                                                                      let jsxtnm551 = XATSDAPP(XATS2JS_sint_gt$sint(jsxtnm547, jsxtnm548))
                                                                      jsxtnm552 = jsxtnm551
                                                                    } // endlet
                                                                    // I1CMP:return:jsxtnm552
                                                                    return jsxtnm552
                                                                  } // endtimp(sint_gt$sint(919))
                                                                  let jsxtnm554 = XATSDAPP(jsxtnm553(jsxtnm545, XATSINT1(0)))
                                                                  let jsxtnm563 // ift
                                                                  if (jsxtnm554) // ift
                                                                  {
                                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4062(line=246,offs=1)--4072(line=246,offs=11))
                                                                    // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                                                                    // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                                                                    // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                                                                    let jsxtnm559 = function (arg1) { // timp: strn_print(1029)
                                                                      let jsxtnm555 = arg1
                                                                      // I1CMP:start
                                                                      let jsxtnm558 // let
                                                                      { // let
                                                                        // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                                                                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                                                                        // I1FUNDCL
                                                                        // XATS2JS_strn_print_2202
                                                                          // FJARGdarg($list(I1BNDcons(I1TNM(556);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(556)))))))
                                                                          // I1CMP:start
                                                                          // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                                                                        let jsxtnm557 = XATSDAPP(XATS2JS_strn_print(jsxtnm555))
                                                                        jsxtnm558 = jsxtnm557
                                                                      } // endlet
                                                                      // I1CMP:return:jsxtnm558
                                                                      return jsxtnm558
                                                                    } // endtimp(strn_print(1029))
                                                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4073(line=246,offs=12)--4081(line=246,offs=20))
                                                                    // I0Etapq(I0Ecst(gseq$sep(342)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2474(line=138,offs=1)--2482(line=138,offs=9))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                                                                    // T1IMPallx(gseq$sep(342);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3371(line=190,offs=1)--3421(line=193,offs=23)))
                                                                    // T1IMPallx(gseq$sep(342)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7315],T2Pcst(term)),@(x0[7315],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$sep(342);$list(@(xs[1047],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7315])))),@(x0[1048],T2Pvar(x0[7315])))))))
                                                                    let jsxtnm560 = function () { // timp: gseq$sep(342)
                                                                      // I1CMP:start
                                                                      // I1CMP:return:XATSSTRN(",")
                                                                      return XATSSTRN(",")
                                                                    } // endtimp(gseq$sep(342))
                                                                    let jsxtnm561 = XATSDAPP(jsxtnm560())
                                                                    let jsxtnm562 = XATSDAPP(jsxtnm559(jsxtnm561))
                                                                    jsxtnm563 = jsxtnm562
                                                                  } else {
                                                                  } // end(if)
                                                                  jsxtnm564 = jsxtnm563
                                                                  XATS000_patck(true)
                                                                  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4012(line=242,offs=3)--4020(line=242,offs=11))
                                                                  // I0Etapq(I0Ecst(g_print0(1398)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas000_vt.sats)@(2080(line=106,offs=1)--2088(line=106,offs=9))));$list(T2JAG($list(T2Pvar(x0[7786])))))
                                                                  // T1IMPallx(g_print0(1398);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1589(line=56,offs=1)--1634(line=58,offs=27)))
                                                                  // T1IMPallx(g_print0(1398)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8663],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(g_print0(1398);$list(@(x0[3698],T2Pvar(x0[8663])))))))
                                                                  let jsxtnm566
                                                                  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1623(line=58,offs=16)--1630(line=58,offs=23))
                                                                  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[8663])))))
                                                                  // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                                                                  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                                                                  let jsxtnm565
                                                                  jsxtnm565 = auxpr_1677
                                                                  jsxtnm566 = jsxtnm565
                                                                  let jsxtnm567 = XATSDAPP(jsxtnm566(jsxtnm546))
                                                                  jsxtnm568 = jsxtnm567
                                                                } // endlet
                                                                // I1CMP:return:jsxtnm568
                                                                return jsxtnm568
                                                              } // endtimp(iforitm$work0(1435))
                                                              jsxtnm570 = jsxtnm569
                                                              let jsxtnm571 = XATSDAPP(jsxtnm570(jsxtnm543, jsxtnm544))
                                                              jsxtnm572 = jsxtnm571
                                                              XATS000_patck(true)
                                                              jsxtnm573 = XATSBOOL(true)
                                                            } // endlet
                                                            // I1CMP:return:jsxtnm573
                                                            return jsxtnm573
                                                          } // endtimp(iforall$test(49))
                                                          let jsxtnm575 = XATSDAPP(jsxtnm574(jsxtnm542, jsxtnm537))
                                                          jsxtnm576 = jsxtnm575
                                                          XATS000_patck(true)
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4610(line=279,offs=5)--4618(line=279,offs=13))
                                                          // I0Etapq(I0Ecst(p2tr_set(2281)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2611(line=127,offs=1)--2619(line=127,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                                                          // T1IMPallx(p2tr_set(2281);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(246(line=19,offs=1)--305(line=22,offs=27)))
                                                          // T1IMPallx(p2tr_set(2281)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5819],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_set(2281);$list(@(a[5621],T2Pvar(a[5819])))))))
                                                          let jsxtnm579 = function (arg1, arg2) { // timp: p2tr_set(2281)
                                                            let jsxtnm577 = arg1
                                                            let jsxtnm578 = arg2
                                                            // I1CMP:start
                                                            XATS000_assgn(jsxtnm577, jsxtnm578)
                                                            // I1CMP:return:[]
                                                            return []
                                                          } // endtimp(p2tr_set(2281))
                                                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4629(line=279,offs=24)--4630(line=279,offs=25))
                                                          // I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
                                                          // T1IMPallx(sint_add$sint(925);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
                                                          // T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
                                                          let jsxtnm586 = function (arg1, arg2) { // timp: sint_add$sint(925)
                                                            let jsxtnm580 = arg1
                                                            let jsxtnm581 = arg2
                                                            // I1CMP:start
                                                            let jsxtnm585 // let
                                                            { // let
                                                              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
                                                              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2775(line=154,offs=1)--2839(line=156,offs=39))
                                                              // I1FUNDCL
                                                              // XATS2JS_sint_add$sint_2778
                                                                // FJARGdarg($list(I1BNDcons(I1TNM(582);I0Pvar(i1(4933));$list(@(i1(4933),I1Vtnm(I1TNM(582))))),I1BNDcons(I1TNM(583);I0Pvar(i2(4934));$list(@(i2(4934),I1Vtnm(I1TNM(583)))))))
                                                                // I1CMP:start
                                                                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_add$sint);G1Nlist($list())) // I1CMP:return
                                                              let jsxtnm584 = XATSDAPP(XATS2JS_sint_add$sint(jsxtnm580, jsxtnm581))
                                                              jsxtnm585 = jsxtnm584
                                                            } // endlet
                                                            // I1CMP:return:jsxtnm585
                                                            return jsxtnm585
                                                          } // endtimp(sint_add$sint(925))
                                                          let jsxtnm587 = XATSDAPP(jsxtnm586(jsxtnm542, XATSINT1(1)))
                                                          let jsxtnm588 = XATSDAPP(jsxtnm579(jsxtnm524, jsxtnm587))
                                                          jsxtnm589 = jsxtnm576
                                                        } // endlet
                                                        // I1CMP:return:jsxtnm589
                                                        return jsxtnm589
                                                      } // endtimp(forall$test(47))
                                                      let jsxtnm591 = XATSDAPP(jsxtnm590(XATSP1CN("list_cons", jsxtnm536[0+1])))
                                                      jsxtnm592 = jsxtnm591
                                                      XATS000_patck(true)
                                                      let jsxtnm594 // ift
                                                      if (jsxtnm592) // ift
                                                      {
                                                        let jsxtnm593 = XATSDAPP(loop_1660(XATSP1CN("list_cons", jsxtnm536[1+1])))
                                                        jsxtnm594 = jsxtnm593
                                                      } else {
                                                        jsxtnm594 = XATSBOOL(false)
                                                      } // end(if)
                                                      jsxtnm595 = jsxtnm594
                                                    } // endlet
                                                    jsxtnm596 = jsxtnm595
                                                    break // cls
                                                  } // gpt
                                                  // } // cls
                                                  XATS000_cfail()
                                                } while (false) // end-of(do)
                                                // I1CMP:return:jsxtnm596
                                                return jsxtnm596
                                              } // endfun(loop_1660)
                                              let jsxtnm597 = XATSDAPP(loop_1660(jsxtnm533))
                                              jsxtnm598 = jsxtnm597
                                            } // endlet
                                            // I1CMP:return:jsxtnm598
                                            return jsxtnm598
                                          } // endtimp(list_forall(1206))
                                          jsxtnm600 = jsxtnm599
                                          let jsxtnm601 = XATSDAPP(jsxtnm600(jsxtnm522))
                                          jsxtnm602 = jsxtnm601
                                        } // endlet
                                        jsxtnm603 = jsxtnm602
                                        XATS000_patck(true)
                                        jsxtnm604 = jsxtnm603
                                      } // endlet
                                      // I1CMP:return:jsxtnm604
                                      return jsxtnm604
                                    } // endtimp(gseq_iforall(384))
                                    let jsxtnm606 = XATSDAPP(jsxtnm605(jsxtnm516))
                                    jsxtnm607 = jsxtnm606
                                    XATS000_patck(true)
                                    jsxtnm608 = []
                                  } // endlet
                                  jsxtnm609 = jsxtnm608
                                } // endlet
                                // I1CMP:return:jsxtnm609
                                return jsxtnm609
                              } // endtimp(gseq_iforitm(398))
                              let jsxtnm611 = XATSDAPP(jsxtnm610(jsxtnm515))
                              jsxtnm612 = jsxtnm611
                            } // endlet
                            // I1CMP:return:jsxtnm612
                            return jsxtnm612
                          } // endtimp(gseq_iforitm0(1732))
                          let jsxtnm614 = XATSDAPP(jsxtnm613(jsxtnm358))
                          jsxtnm615 = jsxtnm614
                        } // end(if)
                        jsxtnm616 = jsxtnm615
                      } // endlet
                      jsxtnm617 = jsxtnm616
                      XATS000_patck(true)
                      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4330(line=274,offs=1)--4371(line=275,offs=33)))
                      // I1VALDCL
                      let jsxtnm626
                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4339(line=275,offs=1)--4349(line=275,offs=11))
                      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                      let jsxtnm622 = function (arg1) { // timp: strn_print(1029)
                        let jsxtnm618 = arg1
                        // I1CMP:start
                        let jsxtnm621 // let
                        { // let
                          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                          // I1FUNDCL
                          // XATS2JS_strn_print_2202
                            // FJARGdarg($list(I1BNDcons(I1TNM(619);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(619)))))))
                            // I1CMP:start
                            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                          let jsxtnm620 = XATSDAPP(XATS2JS_strn_print(jsxtnm618))
                          jsxtnm621 = jsxtnm620
                        } // endlet
                        // I1CMP:return:jsxtnm621
                        return jsxtnm621
                      } // endtimp(strn_print(1029))
                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4352(line=275,offs=14)--4360(line=275,offs=22))
                      // I0Etapq(I0Ecst(gseq$end(341)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2432(line=134,offs=1)--2440(line=134,offs=9))));$list(T2JAG($list(T2Pvar(xs[7785]))),T2JAG($list(T2Pvar(x0[7786])))))
                      // T1IMPallx(gseq$end(341);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3422(line=194,offs=1)--3472(line=197,offs=23)))
                      // T1IMPallx(gseq$end(341)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7316],T2Pcst(term)),@(x0[7316],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$end(341);$list(@(xs[1045],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7316])))),@(x0[1046],T2Pvar(x0[7316])))))))
                      let jsxtnm623 = function () { // timp: gseq$end(341)
                        // I1CMP:start
                        // I1CMP:return:XATSSTRN(")")
                        return XATSSTRN(")")
                      } // endtimp(gseq$end(341))
                      let jsxtnm624 = XATSDAPP(jsxtnm623())
                      let jsxtnm625 = XATSDAPP(jsxtnm622(jsxtnm624))
                      jsxtnm626 = jsxtnm625
                      XATS000_patck(true)
                      jsxtnm627 = []
                    } // endlet
                    // I1CMP:return:jsxtnm627
                    return jsxtnm627
                  } // endtimp(gseq_print0(1658))
                  jsxtnm629 = jsxtnm628
                  let jsxtnm630 = XATSDAPP(jsxtnm629(jsxtnm357))
                  // I1CMP:return:jsxtnm630
                  return jsxtnm630
                } // endtimp(g_print(39))
                let jsxtnm632 = XATSDAPP(jsxtnm631(jsxtnm321))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm634 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm633 = XATSTUP0([])
                  // I1CMP:return:jsxtnm633
                  return jsxtnm633
                } // endtimp(gs_print$sep(794))
                let jsxtnm635 = XATSDAPP(jsxtnm634())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6931])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm641
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm640 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm636 = arg1
                  // I1CMP:start
                  let jsxtnm639 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(637);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(637)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm638 = XATSDAPP(XATS2JS_strn_print(jsxtnm636))
                    jsxtnm639 = jsxtnm638
                  } // endlet
                  // I1CMP:return:jsxtnm639
                  return jsxtnm639
                } // endtimp(strn_print(1029))
                jsxtnm641 = jsxtnm640
                let jsxtnm642 = XATSDAPP(jsxtnm641(jsxtnm322))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm644 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm643 = XATSTUP0([])
                  // I1CMP:return:jsxtnm643
                  return jsxtnm643
                } // endtimp(gs_print$end(795))
                let jsxtnm645 = XATSDAPP(jsxtnm644())
                jsxtnm646 = jsxtnm645
              } // endlet
              // I1CMP:return:jsxtnm646
              return jsxtnm646
            } // endtimp(gs_print_a5(801))
            let jsxtnm648 = XATSDAPP(jsxtnm647(XATSSTRN("TMopr("), XATSP1CN("TMopr", jsxtnm317[0+1]), XATSSTRN(";"), XATSP1CN("TMopr", jsxtnm317[1+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm648
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(649);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5237)),I0Pvar(tm2(5238)),I0Pvar(tm3(5239))));$list(@(tm1(5237),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(649));0)),@(tm2(5238),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(649));1)),@(tm3(5239),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(649));2)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMif0",6))) { // gpt
            let jsxtnm649 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(2054(line=139,offs=1)--2060(line=139,offs=7))
            // I0Etapq(I0Ecst(gs_print_a7(803)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12204(line=788,offs=1)--12215(line=788,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a7(803);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22634(line=1392,offs=1)--23038(line=1414,offs=4)))
            // T1IMPallx(gs_print_a7(803)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6938],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6939],T2Pcst(term)),@(x2[6940],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6941],T2Pcst(term)),@(x4[6942],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x5[6943],T2Pcst(term)),@(x6[6944],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a7(803);$list(@(x0[2476],T2Pvar(x0[6938])),@(x1[2477],T2Pvar(x1[6939])),@(x2[2478],T2Pvar(x2[6940])),@(x3[2479],T2Pvar(x3[6941])),@(x4[2480],T2Pvar(x4[6942])),@(x5[2481],T2Pvar(x5[6943])),@(x6[2482],T2Pvar(x6[6944])))))))
            let jsxtnm717 = function (arg1, arg2, arg3, arg4, arg5, arg6, arg7) { // timp: gs_print_a7(803)
              let jsxtnm650 = arg1
              let jsxtnm651 = arg2
              let jsxtnm652 = arg3
              let jsxtnm653 = arg4
              let jsxtnm654 = arg5
              let jsxtnm655 = arg6
              let jsxtnm656 = arg7
              // I1CMP:start
              let jsxtnm716 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22762(line=1404,offs=1)--22785(line=1405,offs=15)))
                // I1VALDCL
                let jsxtnm660
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22771(line=1405,offs=1)--22783(line=1405,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm658 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm657 = XATSTUP0([])
                  // I1CMP:return:jsxtnm657
                  return jsxtnm657
                } // endtimp(gs_print$beg(793))
                let jsxtnm659 = XATSDAPP(jsxtnm658())
                jsxtnm660 = jsxtnm659
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22798(line=1407,offs=3)--22805(line=1407,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6938])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm666
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm665 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm661 = arg1
                  // I1CMP:start
                  let jsxtnm664 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(662);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(662)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm663 = XATSDAPP(XATS2JS_strn_print(jsxtnm661))
                    jsxtnm664 = jsxtnm663
                  } // endlet
                  // I1CMP:return:jsxtnm664
                  return jsxtnm664
                } // endtimp(strn_print(1029))
                jsxtnm666 = jsxtnm665
                let jsxtnm667 = XATSDAPP(jsxtnm666(jsxtnm650))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22815(line=1407,offs=20)--22827(line=1407,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm669 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm668 = XATSTUP0([])
                  // I1CMP:return:jsxtnm668
                  return jsxtnm668
                } // endtimp(gs_print$sep(794))
                let jsxtnm670 = XATSDAPP(jsxtnm669())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22832(line=1408,offs=3)--22839(line=1408,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6939])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm671
                jsxtnm671 = auxpr_1677
                let jsxtnm672 = XATSDAPP(jsxtnm671(jsxtnm651))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22849(line=1408,offs=20)--22861(line=1408,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm674 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm673 = XATSTUP0([])
                  // I1CMP:return:jsxtnm673
                  return jsxtnm673
                } // endtimp(gs_print$sep(794))
                let jsxtnm675 = XATSDAPP(jsxtnm674())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22866(line=1409,offs=3)--22873(line=1409,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6940])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm681
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm680 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm676 = arg1
                  // I1CMP:start
                  let jsxtnm679 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(677);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(677)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm678 = XATSDAPP(XATS2JS_strn_print(jsxtnm676))
                    jsxtnm679 = jsxtnm678
                  } // endlet
                  // I1CMP:return:jsxtnm679
                  return jsxtnm679
                } // endtimp(strn_print(1029))
                jsxtnm681 = jsxtnm680
                let jsxtnm682 = XATSDAPP(jsxtnm681(jsxtnm652))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22883(line=1409,offs=20)--22895(line=1409,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm684 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm683 = XATSTUP0([])
                  // I1CMP:return:jsxtnm683
                  return jsxtnm683
                } // endtimp(gs_print$sep(794))
                let jsxtnm685 = XATSDAPP(jsxtnm684())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22900(line=1410,offs=3)--22907(line=1410,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6941])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm686
                jsxtnm686 = auxpr_1677
                let jsxtnm687 = XATSDAPP(jsxtnm686(jsxtnm653))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22917(line=1410,offs=20)--22929(line=1410,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm689 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm688 = XATSTUP0([])
                  // I1CMP:return:jsxtnm688
                  return jsxtnm688
                } // endtimp(gs_print$sep(794))
                let jsxtnm690 = XATSDAPP(jsxtnm689())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22934(line=1411,offs=3)--22941(line=1411,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6942])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm696
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm695 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm691 = arg1
                  // I1CMP:start
                  let jsxtnm694 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(692);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(692)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm693 = XATSDAPP(XATS2JS_strn_print(jsxtnm691))
                    jsxtnm694 = jsxtnm693
                  } // endlet
                  // I1CMP:return:jsxtnm694
                  return jsxtnm694
                } // endtimp(strn_print(1029))
                jsxtnm696 = jsxtnm695
                let jsxtnm697 = XATSDAPP(jsxtnm696(jsxtnm654))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22951(line=1411,offs=20)--22963(line=1411,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm699 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm698 = XATSTUP0([])
                  // I1CMP:return:jsxtnm698
                  return jsxtnm698
                } // endtimp(gs_print$sep(794))
                let jsxtnm700 = XATSDAPP(jsxtnm699())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22968(line=1412,offs=3)--22975(line=1412,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x5[6943])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm701
                jsxtnm701 = auxpr_1677
                let jsxtnm702 = XATSDAPP(jsxtnm701(jsxtnm655))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22985(line=1412,offs=20)--22997(line=1412,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm704 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm703 = XATSTUP0([])
                  // I1CMP:return:jsxtnm703
                  return jsxtnm703
                } // endtimp(gs_print$sep(794))
                let jsxtnm705 = XATSDAPP(jsxtnm704())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23002(line=1413,offs=3)--23009(line=1413,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x6[6944])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm711
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm710 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm706 = arg1
                  // I1CMP:start
                  let jsxtnm709 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(707);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(707)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm708 = XATSDAPP(XATS2JS_strn_print(jsxtnm706))
                    jsxtnm709 = jsxtnm708
                  } // endlet
                  // I1CMP:return:jsxtnm709
                  return jsxtnm709
                } // endtimp(strn_print(1029))
                jsxtnm711 = jsxtnm710
                let jsxtnm712 = XATSDAPP(jsxtnm711(jsxtnm656))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23019(line=1413,offs=20)--23031(line=1413,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm714 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm713 = XATSTUP0([])
                  // I1CMP:return:jsxtnm713
                  return jsxtnm713
                } // endtimp(gs_print$end(795))
                let jsxtnm715 = XATSDAPP(jsxtnm714())
                jsxtnm716 = jsxtnm715
              } // endlet
              // I1CMP:return:jsxtnm716
              return jsxtnm716
            } // endtimp(gs_print_a7(803))
            let jsxtnm718 = XATSDAPP(jsxtnm717(XATSSTRN("TMif0("), XATSP1CN("TMif0", jsxtnm649[0+1]), XATSSTRN(";"), XATSP1CN("TMif0", jsxtnm649[1+1]), XATSSTRN(";"), XATSP1CN("TMif0", jsxtnm649[2+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm718
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(719);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5240)),I0Pvar(x01(5241)),I0Pvar(tmx(5242))));$list(@(f00(5240),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(719));0)),@(x01(5241),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(719));1)),@(tmx(5242),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(719));2)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMfix",7))) { // gpt
            let jsxtnm719 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(2131(line=144,offs=1)--2137(line=144,offs=7))
            // I0Etapq(I0Ecst(gs_print_a7(803)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12204(line=788,offs=1)--12215(line=788,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a7(803);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22634(line=1392,offs=1)--23038(line=1414,offs=4)))
            // T1IMPallx(gs_print_a7(803)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6938],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6939],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6940],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6941],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x4[6942],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x5[6943],T2Pcst(term)),@(x6[6944],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a7(803);$list(@(x0[2476],T2Pvar(x0[6938])),@(x1[2477],T2Pvar(x1[6939])),@(x2[2478],T2Pvar(x2[6940])),@(x3[2479],T2Pvar(x3[6941])),@(x4[2480],T2Pvar(x4[6942])),@(x5[2481],T2Pvar(x5[6943])),@(x6[2482],T2Pvar(x6[6944])))))))
            let jsxtnm797 = function (arg1, arg2, arg3, arg4, arg5, arg6, arg7) { // timp: gs_print_a7(803)
              let jsxtnm720 = arg1
              let jsxtnm721 = arg2
              let jsxtnm722 = arg3
              let jsxtnm723 = arg4
              let jsxtnm724 = arg5
              let jsxtnm725 = arg6
              let jsxtnm726 = arg7
              // I1CMP:start
              let jsxtnm796 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22762(line=1404,offs=1)--22785(line=1405,offs=15)))
                // I1VALDCL
                let jsxtnm730
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22771(line=1405,offs=1)--22783(line=1405,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm728 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm727 = XATSTUP0([])
                  // I1CMP:return:jsxtnm727
                  return jsxtnm727
                } // endtimp(gs_print$beg(793))
                let jsxtnm729 = XATSDAPP(jsxtnm728())
                jsxtnm730 = jsxtnm729
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22798(line=1407,offs=3)--22805(line=1407,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6938])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm736
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm735 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm731 = arg1
                  // I1CMP:start
                  let jsxtnm734 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(732);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(732)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm733 = XATSDAPP(XATS2JS_strn_print(jsxtnm731))
                    jsxtnm734 = jsxtnm733
                  } // endlet
                  // I1CMP:return:jsxtnm734
                  return jsxtnm734
                } // endtimp(strn_print(1029))
                jsxtnm736 = jsxtnm735
                let jsxtnm737 = XATSDAPP(jsxtnm736(jsxtnm720))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22815(line=1407,offs=20)--22827(line=1407,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm739 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm738 = XATSTUP0([])
                  // I1CMP:return:jsxtnm738
                  return jsxtnm738
                } // endtimp(gs_print$sep(794))
                let jsxtnm740 = XATSDAPP(jsxtnm739())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22832(line=1408,offs=3)--22839(line=1408,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6939])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm746
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm745 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm741 = arg1
                  // I1CMP:start
                  let jsxtnm744 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(742);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(742)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm743 = XATSDAPP(XATS2JS_strn_print(jsxtnm741))
                    jsxtnm744 = jsxtnm743
                  } // endlet
                  // I1CMP:return:jsxtnm744
                  return jsxtnm744
                } // endtimp(strn_print(1029))
                jsxtnm746 = jsxtnm745
                let jsxtnm747 = XATSDAPP(jsxtnm746(jsxtnm721))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22849(line=1408,offs=20)--22861(line=1408,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm749 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm748 = XATSTUP0([])
                  // I1CMP:return:jsxtnm748
                  return jsxtnm748
                } // endtimp(gs_print$sep(794))
                let jsxtnm750 = XATSDAPP(jsxtnm749())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22866(line=1409,offs=3)--22873(line=1409,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6940])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm756
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm755 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm751 = arg1
                  // I1CMP:start
                  let jsxtnm754 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(752);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(752)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm753 = XATSDAPP(XATS2JS_strn_print(jsxtnm751))
                    jsxtnm754 = jsxtnm753
                  } // endlet
                  // I1CMP:return:jsxtnm754
                  return jsxtnm754
                } // endtimp(strn_print(1029))
                jsxtnm756 = jsxtnm755
                let jsxtnm757 = XATSDAPP(jsxtnm756(jsxtnm722))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22883(line=1409,offs=20)--22895(line=1409,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm759 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm758 = XATSTUP0([])
                  // I1CMP:return:jsxtnm758
                  return jsxtnm758
                } // endtimp(gs_print$sep(794))
                let jsxtnm760 = XATSDAPP(jsxtnm759())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22900(line=1410,offs=3)--22907(line=1410,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6941])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm766
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm765 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm761 = arg1
                  // I1CMP:start
                  let jsxtnm764 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(762);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(762)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm763 = XATSDAPP(XATS2JS_strn_print(jsxtnm761))
                    jsxtnm764 = jsxtnm763
                  } // endlet
                  // I1CMP:return:jsxtnm764
                  return jsxtnm764
                } // endtimp(strn_print(1029))
                jsxtnm766 = jsxtnm765
                let jsxtnm767 = XATSDAPP(jsxtnm766(jsxtnm723))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22917(line=1410,offs=20)--22929(line=1410,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm769 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm768 = XATSTUP0([])
                  // I1CMP:return:jsxtnm768
                  return jsxtnm768
                } // endtimp(gs_print$sep(794))
                let jsxtnm770 = XATSDAPP(jsxtnm769())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22934(line=1411,offs=3)--22941(line=1411,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6942])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm776
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm775 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm771 = arg1
                  // I1CMP:start
                  let jsxtnm774 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(772);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(772)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm773 = XATSDAPP(XATS2JS_strn_print(jsxtnm771))
                    jsxtnm774 = jsxtnm773
                  } // endlet
                  // I1CMP:return:jsxtnm774
                  return jsxtnm774
                } // endtimp(strn_print(1029))
                jsxtnm776 = jsxtnm775
                let jsxtnm777 = XATSDAPP(jsxtnm776(jsxtnm724))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22951(line=1411,offs=20)--22963(line=1411,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm779 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm778 = XATSTUP0([])
                  // I1CMP:return:jsxtnm778
                  return jsxtnm778
                } // endtimp(gs_print$sep(794))
                let jsxtnm780 = XATSDAPP(jsxtnm779())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22968(line=1412,offs=3)--22975(line=1412,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x5[6943])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm781
                jsxtnm781 = auxpr_1677
                let jsxtnm782 = XATSDAPP(jsxtnm781(jsxtnm725))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22985(line=1412,offs=20)--22997(line=1412,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm784 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm783 = XATSTUP0([])
                  // I1CMP:return:jsxtnm783
                  return jsxtnm783
                } // endtimp(gs_print$sep(794))
                let jsxtnm785 = XATSDAPP(jsxtnm784())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23002(line=1413,offs=3)--23009(line=1413,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x6[6944])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm791
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm790 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm786 = arg1
                  // I1CMP:start
                  let jsxtnm789 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(787);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(787)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm788 = XATSDAPP(XATS2JS_strn_print(jsxtnm786))
                    jsxtnm789 = jsxtnm788
                  } // endlet
                  // I1CMP:return:jsxtnm789
                  return jsxtnm789
                } // endtimp(strn_print(1029))
                jsxtnm791 = jsxtnm790
                let jsxtnm792 = XATSDAPP(jsxtnm791(jsxtnm726))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23019(line=1413,offs=20)--23031(line=1413,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm794 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm793 = XATSTUP0([])
                  // I1CMP:return:jsxtnm793
                  return jsxtnm793
                } // endtimp(gs_print$end(795))
                let jsxtnm795 = XATSDAPP(jsxtnm794())
                jsxtnm796 = jsxtnm795
              } // endlet
              // I1CMP:return:jsxtnm796
              return jsxtnm796
            } // endtimp(gs_print_a7(803))
            let jsxtnm798 = XATSDAPP(jsxtnm797(XATSSTRN("TMfix("), XATSP1CN("TMfix", jsxtnm719[0+1]), XATSSTRN(";"), XATSP1CN("TMfix", jsxtnm719[1+1]), XATSSTRN(";"), XATSP1CN("TMfix", jsxtnm719[2+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm798
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(799);I0Pdapp(I0Pcon(TMlet(40));$list(I0Pvar(x01(5243)),I0Pvar(tm1(5244)),I0Pvar(tm2(5245))));$list(@(x01(5243),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(799));0)),@(tm1(5244),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(799));1)),@(tm2(5245),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(799));2)))))
          if (XATS000_ctgeq(jsxtnm72, XATSCTAG("TMlet",8))) { // gpt
            let jsxtnm799 = jsxtnm72
            // LCSRCsome1(lambda1.dats)@(2208(line=149,offs=1)--2214(line=149,offs=7))
            // I0Etapq(I0Ecst(gs_print_a7(803)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12204(line=788,offs=1)--12215(line=788,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
            // T1IMPallx(gs_print_a7(803);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22634(line=1392,offs=1)--23038(line=1414,offs=4)))
            // T1IMPallx(gs_print_a7(803)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6938],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6939],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6940],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6941],T2Pcst(term)),@(x4[6942],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x5[6943],T2Pcst(term)),@(x6[6944],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a7(803);$list(@(x0[2476],T2Pvar(x0[6938])),@(x1[2477],T2Pvar(x1[6939])),@(x2[2478],T2Pvar(x2[6940])),@(x3[2479],T2Pvar(x3[6941])),@(x4[2480],T2Pvar(x4[6942])),@(x5[2481],T2Pvar(x5[6943])),@(x6[2482],T2Pvar(x6[6944])))))))
            let jsxtnm872 = function (arg1, arg2, arg3, arg4, arg5, arg6, arg7) { // timp: gs_print_a7(803)
              let jsxtnm800 = arg1
              let jsxtnm801 = arg2
              let jsxtnm802 = arg3
              let jsxtnm803 = arg4
              let jsxtnm804 = arg5
              let jsxtnm805 = arg6
              let jsxtnm806 = arg7
              // I1CMP:start
              let jsxtnm871 // let
              { // let
                // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22762(line=1404,offs=1)--22785(line=1405,offs=15)))
                // I1VALDCL
                let jsxtnm810
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22771(line=1405,offs=1)--22783(line=1405,offs=13))
                // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
                // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
                let jsxtnm808 = function () { // timp: gs_print$beg(793)
                  // I1CMP:start
                  let jsxtnm807 = XATSTUP0([])
                  // I1CMP:return:jsxtnm807
                  return jsxtnm807
                } // endtimp(gs_print$beg(793))
                let jsxtnm809 = XATSDAPP(jsxtnm808())
                jsxtnm810 = jsxtnm809
                XATS000_patck(true)
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22798(line=1407,offs=3)--22805(line=1407,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6938])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm816
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm815 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm811 = arg1
                  // I1CMP:start
                  let jsxtnm814 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(812);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(812)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm813 = XATSDAPP(XATS2JS_strn_print(jsxtnm811))
                    jsxtnm814 = jsxtnm813
                  } // endlet
                  // I1CMP:return:jsxtnm814
                  return jsxtnm814
                } // endtimp(strn_print(1029))
                jsxtnm816 = jsxtnm815
                let jsxtnm817 = XATSDAPP(jsxtnm816(jsxtnm800))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22815(line=1407,offs=20)--22827(line=1407,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm819 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm818 = XATSTUP0([])
                  // I1CMP:return:jsxtnm818
                  return jsxtnm818
                } // endtimp(gs_print$sep(794))
                let jsxtnm820 = XATSDAPP(jsxtnm819())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22832(line=1408,offs=3)--22839(line=1408,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6939])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm826
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm825 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm821 = arg1
                  // I1CMP:start
                  let jsxtnm824 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(822);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(822)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm823 = XATSDAPP(XATS2JS_strn_print(jsxtnm821))
                    jsxtnm824 = jsxtnm823
                  } // endlet
                  // I1CMP:return:jsxtnm824
                  return jsxtnm824
                } // endtimp(strn_print(1029))
                jsxtnm826 = jsxtnm825
                let jsxtnm827 = XATSDAPP(jsxtnm826(jsxtnm801))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22849(line=1408,offs=20)--22861(line=1408,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm829 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm828 = XATSTUP0([])
                  // I1CMP:return:jsxtnm828
                  return jsxtnm828
                } // endtimp(gs_print$sep(794))
                let jsxtnm830 = XATSDAPP(jsxtnm829())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22866(line=1409,offs=3)--22873(line=1409,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6940])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm836
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm835 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm831 = arg1
                  // I1CMP:start
                  let jsxtnm834 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(832);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(832)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm833 = XATSDAPP(XATS2JS_strn_print(jsxtnm831))
                    jsxtnm834 = jsxtnm833
                  } // endlet
                  // I1CMP:return:jsxtnm834
                  return jsxtnm834
                } // endtimp(strn_print(1029))
                jsxtnm836 = jsxtnm835
                let jsxtnm837 = XATSDAPP(jsxtnm836(jsxtnm802))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22883(line=1409,offs=20)--22895(line=1409,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm839 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm838 = XATSTUP0([])
                  // I1CMP:return:jsxtnm838
                  return jsxtnm838
                } // endtimp(gs_print$sep(794))
                let jsxtnm840 = XATSDAPP(jsxtnm839())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22900(line=1410,offs=3)--22907(line=1410,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6941])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm841
                jsxtnm841 = auxpr_1677
                let jsxtnm842 = XATSDAPP(jsxtnm841(jsxtnm803))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22917(line=1410,offs=20)--22929(line=1410,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm844 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm843 = XATSTUP0([])
                  // I1CMP:return:jsxtnm843
                  return jsxtnm843
                } // endtimp(gs_print$sep(794))
                let jsxtnm845 = XATSDAPP(jsxtnm844())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22934(line=1411,offs=3)--22941(line=1411,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6942])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm851
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm850 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm846 = arg1
                  // I1CMP:start
                  let jsxtnm849 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(847);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(847)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm848 = XATSDAPP(XATS2JS_strn_print(jsxtnm846))
                    jsxtnm849 = jsxtnm848
                  } // endlet
                  // I1CMP:return:jsxtnm849
                  return jsxtnm849
                } // endtimp(strn_print(1029))
                jsxtnm851 = jsxtnm850
                let jsxtnm852 = XATSDAPP(jsxtnm851(jsxtnm804))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22951(line=1411,offs=20)--22963(line=1411,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm854 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm853 = XATSTUP0([])
                  // I1CMP:return:jsxtnm853
                  return jsxtnm853
                } // endtimp(gs_print$sep(794))
                let jsxtnm855 = XATSDAPP(jsxtnm854())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22968(line=1412,offs=3)--22975(line=1412,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x5[6943])))))
                // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
                let jsxtnm856
                jsxtnm856 = auxpr_1677
                let jsxtnm857 = XATSDAPP(jsxtnm856(jsxtnm805))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22985(line=1412,offs=20)--22997(line=1412,offs=32))
                // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
                // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
                let jsxtnm859 = function () { // timp: gs_print$sep(794)
                  // I1CMP:start
                  let jsxtnm858 = XATSTUP0([])
                  // I1CMP:return:jsxtnm858
                  return jsxtnm858
                } // endtimp(gs_print$sep(794))
                let jsxtnm860 = XATSDAPP(jsxtnm859())
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23002(line=1413,offs=3)--23009(line=1413,offs=10))
                // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x6[6944])))))
                // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
                // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
                let jsxtnm866
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
                // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
                // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                let jsxtnm865 = function (arg1) { // timp: strn_print(1029)
                  let jsxtnm861 = arg1
                  // I1CMP:start
                  let jsxtnm864 // let
                  { // let
                    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
                    // I1FUNDCL
                    // XATS2JS_strn_print_2202
                      // FJARGdarg($list(I1BNDcons(I1TNM(862);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(862)))))))
                      // I1CMP:start
                      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
                    let jsxtnm863 = XATSDAPP(XATS2JS_strn_print(jsxtnm861))
                    jsxtnm864 = jsxtnm863
                  } // endlet
                  // I1CMP:return:jsxtnm864
                  return jsxtnm864
                } // endtimp(strn_print(1029))
                jsxtnm866 = jsxtnm865
                let jsxtnm867 = XATSDAPP(jsxtnm866(jsxtnm806))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23019(line=1413,offs=20)--23031(line=1413,offs=32))
                // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
                // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
                // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
                let jsxtnm869 = function () { // timp: gs_print$end(795)
                  // I1CMP:start
                  let jsxtnm868 = XATSTUP0([])
                  // I1CMP:return:jsxtnm868
                  return jsxtnm868
                } // endtimp(gs_print$end(795))
                let jsxtnm870 = XATSDAPP(jsxtnm869())
                jsxtnm871 = jsxtnm870
              } // endlet
              // I1CMP:return:jsxtnm871
              return jsxtnm871
            } // endtimp(gs_print_a7(803))
            let jsxtnm873 = XATSDAPP(jsxtnm872(XATSSTRN("TMlet("), XATSP1CN("TMlet", jsxtnm799[0+1]), XATSSTRN(";"), XATSP1CN("TMlet", jsxtnm799[1+1]), XATSSTRN(";"), XATSP1CN("TMlet", jsxtnm799[2+1]), XATSSTRN(")")))
            jsxtnm874 = jsxtnm873
            break // cls
          } // gpt
          // } // cls
          XATS000_cfail()
        } while (false) // end-of(do)
        jsxtnm875 = jsxtnm874
      } // endlet
      // I1CMP:return:jsxtnm875
      return jsxtnm875
    } // endfun(auxpr_1677)
    let jsxtnm876 = XATSDAPP(auxpr_1677(jsxtnm71))
    jsxtnm877 = jsxtnm876
  } // endlet
  // I1CMP:return:jsxtnm877
  return jsxtnm877
} // endtimp(term_print(2664))
jsxtnm879 = jsxtnm878
XATS000_patck(true)
// I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
// I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term))))):timp
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2543(line=169,offs=1)--2571(line=169,offs=29)))
// I1VALDCL
let jsxtnm915
// LCSRCsome1(lambda1.dats)@(2552(line=169,offs=10)--2560(line=169,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm913 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm880 = arg1
  let jsxtnm881 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm904 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm882 = arg1
    let jsxtnm883 = arg2
    // I1CMP:start
    let jsxtnm903 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm887
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm885 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm884 = XATSTUP0([])
        // I1CMP:return:jsxtnm884
        return jsxtnm884
      } // endtimp(gs_print$beg(793))
      let jsxtnm886 = XATSDAPP(jsxtnm885())
      jsxtnm887 = jsxtnm886
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm893
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm892 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm888 = arg1
        // I1CMP:start
        let jsxtnm891 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(889);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(889)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm890 = XATSDAPP(XATS2JS_strn_print(jsxtnm888))
          jsxtnm891 = jsxtnm890
        } // endlet
        // I1CMP:return:jsxtnm891
        return jsxtnm891
      } // endtimp(strn_print(1029))
      jsxtnm893 = jsxtnm892
      let jsxtnm894 = XATSDAPP(jsxtnm893(jsxtnm882))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm896 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm895 = XATSTUP0([])
        // I1CMP:return:jsxtnm895
        return jsxtnm895
      } // endtimp(gs_print$sep(794))
      let jsxtnm897 = XATSDAPP(jsxtnm896())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm898
      jsxtnm898 = jsxtnm879
      let jsxtnm899 = XATSDAPP(jsxtnm898(jsxtnm883))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm901 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm900 = XATSTUP0([])
        // I1CMP:return:jsxtnm900
        return jsxtnm900
      } // endtimp(gs_print$end(795))
      let jsxtnm902 = XATSDAPP(jsxtnm901())
      jsxtnm903 = jsxtnm902
    } // endlet
    // I1CMP:return:jsxtnm903
    return jsxtnm903
  } // endtimp(gs_print_a2(798))
  let jsxtnm905 = XATSDAPP(jsxtnm904(jsxtnm880, jsxtnm881))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm911
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm910 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm906 = arg1
    // I1CMP:start
    let jsxtnm909 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(907);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(907)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm908 = XATSDAPP(XATS2JS_strn_print(jsxtnm906))
      jsxtnm909 = jsxtnm908
    } // endlet
    // I1CMP:return:jsxtnm909
    return jsxtnm909
  } // endtimp(strn_print(1029))
  jsxtnm911 = jsxtnm910
  let jsxtnm912 = XATSDAPP(jsxtnm911(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm912
  return jsxtnm912
} // endtimp(gs_println_a2(811))
let jsxtnm914 = XATSDAPP(jsxtnm913(XATSSTRN("I = "), jsxtnm27))
jsxtnm915 = jsxtnm914
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2572(line=170,offs=1)--2600(line=170,offs=29)))
// I1VALDCL
let jsxtnm951
// LCSRCsome1(lambda1.dats)@(2581(line=170,offs=10)--2589(line=170,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm949 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm916 = arg1
  let jsxtnm917 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm940 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm918 = arg1
    let jsxtnm919 = arg2
    // I1CMP:start
    let jsxtnm939 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm923
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm921 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm920 = XATSTUP0([])
        // I1CMP:return:jsxtnm920
        return jsxtnm920
      } // endtimp(gs_print$beg(793))
      let jsxtnm922 = XATSDAPP(jsxtnm921())
      jsxtnm923 = jsxtnm922
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm929
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm928 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm924 = arg1
        // I1CMP:start
        let jsxtnm927 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(925);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(925)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm926 = XATSDAPP(XATS2JS_strn_print(jsxtnm924))
          jsxtnm927 = jsxtnm926
        } // endlet
        // I1CMP:return:jsxtnm927
        return jsxtnm927
      } // endtimp(strn_print(1029))
      jsxtnm929 = jsxtnm928
      let jsxtnm930 = XATSDAPP(jsxtnm929(jsxtnm918))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm932 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm931 = XATSTUP0([])
        // I1CMP:return:jsxtnm931
        return jsxtnm931
      } // endtimp(gs_print$sep(794))
      let jsxtnm933 = XATSDAPP(jsxtnm932())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm934
      jsxtnm934 = jsxtnm879
      let jsxtnm935 = XATSDAPP(jsxtnm934(jsxtnm919))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm937 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm936 = XATSTUP0([])
        // I1CMP:return:jsxtnm936
        return jsxtnm936
      } // endtimp(gs_print$end(795))
      let jsxtnm938 = XATSDAPP(jsxtnm937())
      jsxtnm939 = jsxtnm938
    } // endlet
    // I1CMP:return:jsxtnm939
    return jsxtnm939
  } // endtimp(gs_print_a2(798))
  let jsxtnm941 = XATSDAPP(jsxtnm940(jsxtnm916, jsxtnm917))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm947
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm946 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm942 = arg1
    // I1CMP:start
    let jsxtnm945 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(943);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(943)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm944 = XATSDAPP(XATS2JS_strn_print(jsxtnm942))
      jsxtnm945 = jsxtnm944
    } // endlet
    // I1CMP:return:jsxtnm945
    return jsxtnm945
  } // endtimp(strn_print(1029))
  jsxtnm947 = jsxtnm946
  let jsxtnm948 = XATSDAPP(jsxtnm947(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm948
  return jsxtnm948
} // endtimp(gs_println_a2(811))
let jsxtnm950 = XATSDAPP(jsxtnm949(XATSSTRN("K = "), jsxtnm30))
jsxtnm951 = jsxtnm950
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2601(line=171,offs=1)--2629(line=171,offs=29)))
// I1VALDCL
let jsxtnm987
// LCSRCsome1(lambda1.dats)@(2610(line=171,offs=10)--2618(line=171,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm985 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm952 = arg1
  let jsxtnm953 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm976 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm954 = arg1
    let jsxtnm955 = arg2
    // I1CMP:start
    let jsxtnm975 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm959
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm957 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm956 = XATSTUP0([])
        // I1CMP:return:jsxtnm956
        return jsxtnm956
      } // endtimp(gs_print$beg(793))
      let jsxtnm958 = XATSDAPP(jsxtnm957())
      jsxtnm959 = jsxtnm958
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm965
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm964 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm960 = arg1
        // I1CMP:start
        let jsxtnm963 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(961);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(961)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm962 = XATSDAPP(XATS2JS_strn_print(jsxtnm960))
          jsxtnm963 = jsxtnm962
        } // endlet
        // I1CMP:return:jsxtnm963
        return jsxtnm963
      } // endtimp(strn_print(1029))
      jsxtnm965 = jsxtnm964
      let jsxtnm966 = XATSDAPP(jsxtnm965(jsxtnm954))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm968 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm967 = XATSTUP0([])
        // I1CMP:return:jsxtnm967
        return jsxtnm967
      } // endtimp(gs_print$sep(794))
      let jsxtnm969 = XATSDAPP(jsxtnm968())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm970
      jsxtnm970 = jsxtnm879
      let jsxtnm971 = XATSDAPP(jsxtnm970(jsxtnm955))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm973 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm972 = XATSTUP0([])
        // I1CMP:return:jsxtnm972
        return jsxtnm972
      } // endtimp(gs_print$end(795))
      let jsxtnm974 = XATSDAPP(jsxtnm973())
      jsxtnm975 = jsxtnm974
    } // endlet
    // I1CMP:return:jsxtnm975
    return jsxtnm975
  } // endtimp(gs_print_a2(798))
  let jsxtnm977 = XATSDAPP(jsxtnm976(jsxtnm952, jsxtnm953))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm983
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm982 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm978 = arg1
    // I1CMP:start
    let jsxtnm981 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(979);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(979)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm980 = XATSDAPP(XATS2JS_strn_print(jsxtnm978))
      jsxtnm981 = jsxtnm980
    } // endlet
    // I1CMP:return:jsxtnm981
    return jsxtnm981
  } // endtimp(strn_print(1029))
  jsxtnm983 = jsxtnm982
  let jsxtnm984 = XATSDAPP(jsxtnm983(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm984
  return jsxtnm984
} // endtimp(gs_println_a2(811))
let jsxtnm986 = XATSDAPP(jsxtnm985(XATSSTRN("S = "), jsxtnm37))
jsxtnm987 = jsxtnm986
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2630(line=172,offs=1)--2660(line=172,offs=31)))
// I1VALDCL
let jsxtnm1023
// LCSRCsome1(lambda1.dats)@(2639(line=172,offs=10)--2647(line=172,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1021 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm988 = arg1
  let jsxtnm989 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1012 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm990 = arg1
    let jsxtnm991 = arg2
    // I1CMP:start
    let jsxtnm1011 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm995
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm993 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm992 = XATSTUP0([])
        // I1CMP:return:jsxtnm992
        return jsxtnm992
      } // endtimp(gs_print$beg(793))
      let jsxtnm994 = XATSDAPP(jsxtnm993())
      jsxtnm995 = jsxtnm994
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1001
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1000 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm996 = arg1
        // I1CMP:start
        let jsxtnm999 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(997);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(997)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm998 = XATSDAPP(XATS2JS_strn_print(jsxtnm996))
          jsxtnm999 = jsxtnm998
        } // endlet
        // I1CMP:return:jsxtnm999
        return jsxtnm999
      } // endtimp(strn_print(1029))
      jsxtnm1001 = jsxtnm1000
      let jsxtnm1002 = XATSDAPP(jsxtnm1001(jsxtnm990))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1004 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1003 = XATSTUP0([])
        // I1CMP:return:jsxtnm1003
        return jsxtnm1003
      } // endtimp(gs_print$sep(794))
      let jsxtnm1005 = XATSDAPP(jsxtnm1004())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1006
      jsxtnm1006 = jsxtnm879
      let jsxtnm1007 = XATSDAPP(jsxtnm1006(jsxtnm991))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1009 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1008 = XATSTUP0([])
        // I1CMP:return:jsxtnm1008
        return jsxtnm1008
      } // endtimp(gs_print$end(795))
      let jsxtnm1010 = XATSDAPP(jsxtnm1009())
      jsxtnm1011 = jsxtnm1010
    } // endlet
    // I1CMP:return:jsxtnm1011
    return jsxtnm1011
  } // endtimp(gs_print_a2(798))
  let jsxtnm1013 = XATSDAPP(jsxtnm1012(jsxtnm988, jsxtnm989))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1019
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1018 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1014 = arg1
    // I1CMP:start
    let jsxtnm1017 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1015);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1015)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1016 = XATSDAPP(XATS2JS_strn_print(jsxtnm1014))
      jsxtnm1017 = jsxtnm1016
    } // endlet
    // I1CMP:return:jsxtnm1017
    return jsxtnm1017
  } // endtimp(strn_print(1029))
  jsxtnm1019 = jsxtnm1018
  let jsxtnm1020 = XATSDAPP(jsxtnm1019(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1020
  return jsxtnm1020
} // endtimp(gs_println_a2(811))
let jsxtnm1022 = XATSDAPP(jsxtnm1021(XATSSTRN("K1 = "), jsxtnm40))
jsxtnm1023 = jsxtnm1022
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2661(line=173,offs=1)--2697(line=173,offs=37)))
// I1VALDCL
let jsxtnm1059
// LCSRCsome1(lambda1.dats)@(2670(line=173,offs=10)--2678(line=173,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1057 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1024 = arg1
  let jsxtnm1025 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1048 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1026 = arg1
    let jsxtnm1027 = arg2
    // I1CMP:start
    let jsxtnm1047 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1031
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1029 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1028 = XATSTUP0([])
        // I1CMP:return:jsxtnm1028
        return jsxtnm1028
      } // endtimp(gs_print$beg(793))
      let jsxtnm1030 = XATSDAPP(jsxtnm1029())
      jsxtnm1031 = jsxtnm1030
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1037
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1036 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1032 = arg1
        // I1CMP:start
        let jsxtnm1035 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1033);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1033)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1034 = XATSDAPP(XATS2JS_strn_print(jsxtnm1032))
          jsxtnm1035 = jsxtnm1034
        } // endlet
        // I1CMP:return:jsxtnm1035
        return jsxtnm1035
      } // endtimp(strn_print(1029))
      jsxtnm1037 = jsxtnm1036
      let jsxtnm1038 = XATSDAPP(jsxtnm1037(jsxtnm1026))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1040 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1039 = XATSTUP0([])
        // I1CMP:return:jsxtnm1039
        return jsxtnm1039
      } // endtimp(gs_print$sep(794))
      let jsxtnm1041 = XATSDAPP(jsxtnm1040())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1042
      jsxtnm1042 = jsxtnm879
      let jsxtnm1043 = XATSDAPP(jsxtnm1042(jsxtnm1027))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1045 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1044 = XATSTUP0([])
        // I1CMP:return:jsxtnm1044
        return jsxtnm1044
      } // endtimp(gs_print$end(795))
      let jsxtnm1046 = XATSDAPP(jsxtnm1045())
      jsxtnm1047 = jsxtnm1046
    } // endlet
    // I1CMP:return:jsxtnm1047
    return jsxtnm1047
  } // endtimp(gs_print_a2(798))
  let jsxtnm1049 = XATSDAPP(jsxtnm1048(jsxtnm1024, jsxtnm1025))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1055
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1054 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1050 = arg1
    // I1CMP:start
    let jsxtnm1053 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1051);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1051)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1052 = XATSDAPP(XATS2JS_strn_print(jsxtnm1050))
      jsxtnm1053 = jsxtnm1052
    } // endlet
    // I1CMP:return:jsxtnm1053
    return jsxtnm1053
  } // endtimp(strn_print(1029))
  jsxtnm1055 = jsxtnm1054
  let jsxtnm1056 = XATSDAPP(jsxtnm1055(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1056
  return jsxtnm1056
} // endtimp(gs_println_a2(811))
let jsxtnm1058 = XATSDAPP(jsxtnm1057(XATSSTRN("omega = "), jsxtnm43))
jsxtnm1059 = jsxtnm1058
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2698(line=174,offs=1)--2734(line=174,offs=37)))
// I1VALDCL
let jsxtnm1095
// LCSRCsome1(lambda1.dats)@(2707(line=174,offs=10)--2715(line=174,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1093 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1060 = arg1
  let jsxtnm1061 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1084 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1062 = arg1
    let jsxtnm1063 = arg2
    // I1CMP:start
    let jsxtnm1083 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1067
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1065 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1064 = XATSTUP0([])
        // I1CMP:return:jsxtnm1064
        return jsxtnm1064
      } // endtimp(gs_print$beg(793))
      let jsxtnm1066 = XATSDAPP(jsxtnm1065())
      jsxtnm1067 = jsxtnm1066
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1073
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1072 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1068 = arg1
        // I1CMP:start
        let jsxtnm1071 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1069);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1069)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1070 = XATSDAPP(XATS2JS_strn_print(jsxtnm1068))
          jsxtnm1071 = jsxtnm1070
        } // endlet
        // I1CMP:return:jsxtnm1071
        return jsxtnm1071
      } // endtimp(strn_print(1029))
      jsxtnm1073 = jsxtnm1072
      let jsxtnm1074 = XATSDAPP(jsxtnm1073(jsxtnm1062))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1076 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1075 = XATSTUP0([])
        // I1CMP:return:jsxtnm1075
        return jsxtnm1075
      } // endtimp(gs_print$sep(794))
      let jsxtnm1077 = XATSDAPP(jsxtnm1076())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1078
      jsxtnm1078 = jsxtnm879
      let jsxtnm1079 = XATSDAPP(jsxtnm1078(jsxtnm1063))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1081 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1080 = XATSTUP0([])
        // I1CMP:return:jsxtnm1080
        return jsxtnm1080
      } // endtimp(gs_print$end(795))
      let jsxtnm1082 = XATSDAPP(jsxtnm1081())
      jsxtnm1083 = jsxtnm1082
    } // endlet
    // I1CMP:return:jsxtnm1083
    return jsxtnm1083
  } // endtimp(gs_print_a2(798))
  let jsxtnm1085 = XATSDAPP(jsxtnm1084(jsxtnm1060, jsxtnm1061))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1091
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1090 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1086 = arg1
    // I1CMP:start
    let jsxtnm1089 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1087);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1087)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1088 = XATSDAPP(XATS2JS_strn_print(jsxtnm1086))
      jsxtnm1089 = jsxtnm1088
    } // endlet
    // I1CMP:return:jsxtnm1089
    return jsxtnm1089
  } // endtimp(strn_print(1029))
  jsxtnm1091 = jsxtnm1090
  let jsxtnm1092 = XATSDAPP(jsxtnm1091(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1092
  return jsxtnm1092
} // endtimp(gs_println_a2(811))
let jsxtnm1094 = XATSDAPP(jsxtnm1093(XATSSTRN("Omega = "), jsxtnm45))
jsxtnm1095 = jsxtnm1094
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2824(line=183,offs=1)--2876(line=185,offs=41)))
// I1VALDCL
let jsxtnm1116
let jsxtnm1115 = function (arg1, arg2) { // lam0(T_LAM(0))
  let jsxtnm1096 = arg1
  let jsxtnm1097 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(2862(line=185,offs=27)--2866(line=185,offs=31))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1111 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1098 = arg1
    // I1CMP:start
    let jsxtnm1110 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1100
      let jsxtnm1099 = XATSPFLT(jsxtnm1098[0])
      jsxtnm1100 = jsxtnm1099
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1102
      let jsxtnm1101 = XATSPFLT(jsxtnm1098[1])
      jsxtnm1102 = jsxtnm1101
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1108 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1103 = arg1
        let jsxtnm1104 = arg2
        // I1CMP:start
        let jsxtnm1105 = XATSCAPP("list_nil", [0])
        let jsxtnm1106 = XATSCAPP("list_cons", [1, jsxtnm1104, jsxtnm1105])
        let jsxtnm1107 = XATSCAPP("list_cons", [1, jsxtnm1103, jsxtnm1106])
        // I1CMP:return:jsxtnm1107
        return jsxtnm1107
      } // endtimp(list_make_2val(1171))
      let jsxtnm1109 = XATSDAPP(jsxtnm1108(jsxtnm1100, jsxtnm1102))
      jsxtnm1110 = jsxtnm1109
    } // endlet
    // I1CMP:return:jsxtnm1110
    return jsxtnm1110
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1112 = XATSTUP1(XATSTRCD(0), [jsxtnm1096, jsxtnm1097])
  let jsxtnm1113 = XATSDAPP(jsxtnm1111(jsxtnm1112))
  let jsxtnm1114 = XATSCAPP("TMopr", [5, XATSSTRN("+"), jsxtnm1113])
  // I1CMP:return:jsxtnm1114
  return jsxtnm1114
} // endfun(lam0)
jsxtnm1116 = jsxtnm1115
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2877(line=186,offs=1)--2929(line=188,offs=41)))
// I1VALDCL
let jsxtnm1137
let jsxtnm1136 = function (arg1, arg2) { // lam0(T_LAM(0))
  let jsxtnm1117 = arg1
  let jsxtnm1118 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(2915(line=188,offs=27)--2919(line=188,offs=31))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1132 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1119 = arg1
    // I1CMP:start
    let jsxtnm1131 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1121
      let jsxtnm1120 = XATSPFLT(jsxtnm1119[0])
      jsxtnm1121 = jsxtnm1120
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1123
      let jsxtnm1122 = XATSPFLT(jsxtnm1119[1])
      jsxtnm1123 = jsxtnm1122
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1129 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1124 = arg1
        let jsxtnm1125 = arg2
        // I1CMP:start
        let jsxtnm1126 = XATSCAPP("list_nil", [0])
        let jsxtnm1127 = XATSCAPP("list_cons", [1, jsxtnm1125, jsxtnm1126])
        let jsxtnm1128 = XATSCAPP("list_cons", [1, jsxtnm1124, jsxtnm1127])
        // I1CMP:return:jsxtnm1128
        return jsxtnm1128
      } // endtimp(list_make_2val(1171))
      let jsxtnm1130 = XATSDAPP(jsxtnm1129(jsxtnm1121, jsxtnm1123))
      jsxtnm1131 = jsxtnm1130
    } // endlet
    // I1CMP:return:jsxtnm1131
    return jsxtnm1131
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1133 = XATSTUP1(XATSTRCD(0), [jsxtnm1117, jsxtnm1118])
  let jsxtnm1134 = XATSDAPP(jsxtnm1132(jsxtnm1133))
  let jsxtnm1135 = XATSCAPP("TMopr", [5, XATSSTRN("-"), jsxtnm1134])
  // I1CMP:return:jsxtnm1135
  return jsxtnm1135
} // endfun(lam0)
jsxtnm1137 = jsxtnm1136
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2930(line=189,offs=1)--2982(line=191,offs=41)))
// I1VALDCL
let jsxtnm1158
let jsxtnm1157 = function (arg1, arg2) { // lam0(T_LAM(0))
  let jsxtnm1138 = arg1
  let jsxtnm1139 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(2968(line=191,offs=27)--2972(line=191,offs=31))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1153 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1140 = arg1
    // I1CMP:start
    let jsxtnm1152 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1142
      let jsxtnm1141 = XATSPFLT(jsxtnm1140[0])
      jsxtnm1142 = jsxtnm1141
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1144
      let jsxtnm1143 = XATSPFLT(jsxtnm1140[1])
      jsxtnm1144 = jsxtnm1143
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1150 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1145 = arg1
        let jsxtnm1146 = arg2
        // I1CMP:start
        let jsxtnm1147 = XATSCAPP("list_nil", [0])
        let jsxtnm1148 = XATSCAPP("list_cons", [1, jsxtnm1146, jsxtnm1147])
        let jsxtnm1149 = XATSCAPP("list_cons", [1, jsxtnm1145, jsxtnm1148])
        // I1CMP:return:jsxtnm1149
        return jsxtnm1149
      } // endtimp(list_make_2val(1171))
      let jsxtnm1151 = XATSDAPP(jsxtnm1150(jsxtnm1142, jsxtnm1144))
      jsxtnm1152 = jsxtnm1151
    } // endlet
    // I1CMP:return:jsxtnm1152
    return jsxtnm1152
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1154 = XATSTUP1(XATSTRCD(0), [jsxtnm1138, jsxtnm1139])
  let jsxtnm1155 = XATSDAPP(jsxtnm1153(jsxtnm1154))
  let jsxtnm1156 = XATSCAPP("TMopr", [5, XATSSTRN("*"), jsxtnm1155])
  // I1CMP:return:jsxtnm1156
  return jsxtnm1156
} // endfun(lam0)
jsxtnm1158 = jsxtnm1157
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2983(line=192,offs=1)--3035(line=194,offs=41)))
// I1VALDCL
let jsxtnm1179
let jsxtnm1178 = function (arg1, arg2) { // lam0(T_LAM(0))
  let jsxtnm1159 = arg1
  let jsxtnm1160 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(3021(line=194,offs=27)--3025(line=194,offs=31))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1174 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1161 = arg1
    // I1CMP:start
    let jsxtnm1173 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1163
      let jsxtnm1162 = XATSPFLT(jsxtnm1161[0])
      jsxtnm1163 = jsxtnm1162
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1165
      let jsxtnm1164 = XATSPFLT(jsxtnm1161[1])
      jsxtnm1165 = jsxtnm1164
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1171 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1166 = arg1
        let jsxtnm1167 = arg2
        // I1CMP:start
        let jsxtnm1168 = XATSCAPP("list_nil", [0])
        let jsxtnm1169 = XATSCAPP("list_cons", [1, jsxtnm1167, jsxtnm1168])
        let jsxtnm1170 = XATSCAPP("list_cons", [1, jsxtnm1166, jsxtnm1169])
        // I1CMP:return:jsxtnm1170
        return jsxtnm1170
      } // endtimp(list_make_2val(1171))
      let jsxtnm1172 = XATSDAPP(jsxtnm1171(jsxtnm1163, jsxtnm1165))
      jsxtnm1173 = jsxtnm1172
    } // endlet
    // I1CMP:return:jsxtnm1173
    return jsxtnm1173
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1175 = XATSTUP1(XATSTRCD(0), [jsxtnm1159, jsxtnm1160])
  let jsxtnm1176 = XATSDAPP(jsxtnm1174(jsxtnm1175))
  let jsxtnm1177 = XATSCAPP("TMopr", [5, XATSSTRN("/"), jsxtnm1176])
  // I1CMP:return:jsxtnm1177
  return jsxtnm1177
} // endfun(lam0)
jsxtnm1179 = jsxtnm1178
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3036(line=195,offs=1)--3088(line=197,offs=41)))
// I1VALDCL
let jsxtnm1200
let jsxtnm1199 = function (arg1, arg2) { // lam0(T_LAM(0))
  let jsxtnm1180 = arg1
  let jsxtnm1181 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(3074(line=197,offs=27)--3078(line=197,offs=31))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1195 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1182 = arg1
    // I1CMP:start
    let jsxtnm1194 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1184
      let jsxtnm1183 = XATSPFLT(jsxtnm1182[0])
      jsxtnm1184 = jsxtnm1183
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1186
      let jsxtnm1185 = XATSPFLT(jsxtnm1182[1])
      jsxtnm1186 = jsxtnm1185
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1192 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1187 = arg1
        let jsxtnm1188 = arg2
        // I1CMP:start
        let jsxtnm1189 = XATSCAPP("list_nil", [0])
        let jsxtnm1190 = XATSCAPP("list_cons", [1, jsxtnm1188, jsxtnm1189])
        let jsxtnm1191 = XATSCAPP("list_cons", [1, jsxtnm1187, jsxtnm1190])
        // I1CMP:return:jsxtnm1191
        return jsxtnm1191
      } // endtimp(list_make_2val(1171))
      let jsxtnm1193 = XATSDAPP(jsxtnm1192(jsxtnm1184, jsxtnm1186))
      jsxtnm1194 = jsxtnm1193
    } // endlet
    // I1CMP:return:jsxtnm1194
    return jsxtnm1194
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1196 = XATSTUP1(XATSTRCD(0), [jsxtnm1180, jsxtnm1181])
  let jsxtnm1197 = XATSDAPP(jsxtnm1195(jsxtnm1196))
  let jsxtnm1198 = XATSCAPP("TMopr", [5, XATSSTRN("%"), jsxtnm1197])
  // I1CMP:return:jsxtnm1198
  return jsxtnm1198
} // endfun(lam0)
jsxtnm1200 = jsxtnm1199
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3135(line=202,offs=1)--3229(line=211,offs=29)))
// I1VALDCL
let jsxtnm1209
let jsxtnm1208 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3193(line=210,offs=1)--3227(line=211,offs=27)))
  // I1VALDCL
  let jsxtnm1202
  let jsxtnm1201 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
  jsxtnm1202 = jsxtnm1201
  XATS000_patck(true)
  // I1VALDCL
  let jsxtnm1204
  let jsxtnm1203 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm1204 = jsxtnm1203
  XATS000_patck(true)
  let jsxtnm1205 = XATSCAPP("TMapp", [4, jsxtnm1202, jsxtnm1204])
  let jsxtnm1206 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm1205])
  let jsxtnm1207 = XATSCAPP("TMlam", [3, XATSSTRN("f"), jsxtnm1206])
  jsxtnm1208 = jsxtnm1207
} // endlet
jsxtnm1209 = jsxtnm1208
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3230(line=212,offs=1)--3336(line=224,offs=29)))
// I1VALDCL
let jsxtnm1219
let jsxtnm1218 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3300(line=223,offs=1)--3334(line=224,offs=27)))
  // I1VALDCL
  let jsxtnm1211
  let jsxtnm1210 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
  jsxtnm1211 = jsxtnm1210
  XATS000_patck(true)
  // I1VALDCL
  let jsxtnm1213
  let jsxtnm1212 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm1213 = jsxtnm1212
  XATS000_patck(true)
  let jsxtnm1214 = XATSCAPP("TMapp", [4, jsxtnm1211, jsxtnm1213])
  let jsxtnm1215 = XATSCAPP("TMapp", [4, jsxtnm1211, jsxtnm1214])
  let jsxtnm1216 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm1215])
  let jsxtnm1217 = XATSCAPP("TMlam", [3, XATSSTRN("f"), jsxtnm1216])
  jsxtnm1218 = jsxtnm1217
} // endlet
jsxtnm1219 = jsxtnm1218
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3340(line=226,offs=1)--3381(line=227,offs=28)))
// I1VALDCL
let jsxtnm1255
// LCSRCsome1(lambda1.dats)@(3354(line=227,offs=1)--3362(line=227,offs=9))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1253 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1220 = arg1
  let jsxtnm1221 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1244 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1222 = arg1
    let jsxtnm1223 = arg2
    // I1CMP:start
    let jsxtnm1243 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1227
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1225 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1224 = XATSTUP0([])
        // I1CMP:return:jsxtnm1224
        return jsxtnm1224
      } // endtimp(gs_print$beg(793))
      let jsxtnm1226 = XATSDAPP(jsxtnm1225())
      jsxtnm1227 = jsxtnm1226
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1233
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1232 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1228 = arg1
        // I1CMP:start
        let jsxtnm1231 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1229);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1229)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1230 = XATSDAPP(XATS2JS_strn_print(jsxtnm1228))
          jsxtnm1231 = jsxtnm1230
        } // endlet
        // I1CMP:return:jsxtnm1231
        return jsxtnm1231
      } // endtimp(strn_print(1029))
      jsxtnm1233 = jsxtnm1232
      let jsxtnm1234 = XATSDAPP(jsxtnm1233(jsxtnm1222))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1236 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1235 = XATSTUP0([])
        // I1CMP:return:jsxtnm1235
        return jsxtnm1235
      } // endtimp(gs_print$sep(794))
      let jsxtnm1237 = XATSDAPP(jsxtnm1236())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1238
      jsxtnm1238 = jsxtnm879
      let jsxtnm1239 = XATSDAPP(jsxtnm1238(jsxtnm1223))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1241 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1240 = XATSTUP0([])
        // I1CMP:return:jsxtnm1240
        return jsxtnm1240
      } // endtimp(gs_print$end(795))
      let jsxtnm1242 = XATSDAPP(jsxtnm1241())
      jsxtnm1243 = jsxtnm1242
    } // endlet
    // I1CMP:return:jsxtnm1243
    return jsxtnm1243
  } // endtimp(gs_print_a2(798))
  let jsxtnm1245 = XATSDAPP(jsxtnm1244(jsxtnm1220, jsxtnm1221))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1251
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1250 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1246 = arg1
    // I1CMP:start
    let jsxtnm1249 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1247);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1247)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1248 = XATSDAPP(XATS2JS_strn_print(jsxtnm1246))
      jsxtnm1249 = jsxtnm1248
    } // endlet
    // I1CMP:return:jsxtnm1249
    return jsxtnm1249
  } // endtimp(strn_print(1029))
  jsxtnm1251 = jsxtnm1250
  let jsxtnm1252 = XATSDAPP(jsxtnm1251(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1252
  return jsxtnm1252
} // endtimp(gs_println_a2(811))
let jsxtnm1254 = XATSDAPP(jsxtnm1253(XATSSTRN("TMone = "), jsxtnm1209))
jsxtnm1255 = jsxtnm1254
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3382(line=228,offs=1)--3423(line=229,offs=28)))
// I1VALDCL
let jsxtnm1291
// LCSRCsome1(lambda1.dats)@(3396(line=229,offs=1)--3404(line=229,offs=9))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1289 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1256 = arg1
  let jsxtnm1257 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1280 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1258 = arg1
    let jsxtnm1259 = arg2
    // I1CMP:start
    let jsxtnm1279 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1263
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1261 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1260 = XATSTUP0([])
        // I1CMP:return:jsxtnm1260
        return jsxtnm1260
      } // endtimp(gs_print$beg(793))
      let jsxtnm1262 = XATSDAPP(jsxtnm1261())
      jsxtnm1263 = jsxtnm1262
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1269
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1268 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1264 = arg1
        // I1CMP:start
        let jsxtnm1267 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1265);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1265)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1266 = XATSDAPP(XATS2JS_strn_print(jsxtnm1264))
          jsxtnm1267 = jsxtnm1266
        } // endlet
        // I1CMP:return:jsxtnm1267
        return jsxtnm1267
      } // endtimp(strn_print(1029))
      jsxtnm1269 = jsxtnm1268
      let jsxtnm1270 = XATSDAPP(jsxtnm1269(jsxtnm1258))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1272 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1271 = XATSTUP0([])
        // I1CMP:return:jsxtnm1271
        return jsxtnm1271
      } // endtimp(gs_print$sep(794))
      let jsxtnm1273 = XATSDAPP(jsxtnm1272())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1274
      jsxtnm1274 = jsxtnm879
      let jsxtnm1275 = XATSDAPP(jsxtnm1274(jsxtnm1259))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1277 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1276 = XATSTUP0([])
        // I1CMP:return:jsxtnm1276
        return jsxtnm1276
      } // endtimp(gs_print$end(795))
      let jsxtnm1278 = XATSDAPP(jsxtnm1277())
      jsxtnm1279 = jsxtnm1278
    } // endlet
    // I1CMP:return:jsxtnm1279
    return jsxtnm1279
  } // endtimp(gs_print_a2(798))
  let jsxtnm1281 = XATSDAPP(jsxtnm1280(jsxtnm1256, jsxtnm1257))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1287
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1286 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1282 = arg1
    // I1CMP:start
    let jsxtnm1285 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1283);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1283)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1284 = XATSDAPP(XATS2JS_strn_print(jsxtnm1282))
      jsxtnm1285 = jsxtnm1284
    } // endlet
    // I1CMP:return:jsxtnm1285
    return jsxtnm1285
  } // endtimp(strn_print(1029))
  jsxtnm1287 = jsxtnm1286
  let jsxtnm1288 = XATSDAPP(jsxtnm1287(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1288
  return jsxtnm1288
} // endtimp(gs_println_a2(811))
let jsxtnm1290 = XATSDAPP(jsxtnm1289(XATSSTRN("TMtwo = "), jsxtnm1219))
jsxtnm1291 = jsxtnm1290
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3470(line=234,offs=1)--3533(line=238,offs=28)))
// I1VALDCL
let jsxtnm1297
let jsxtnm1296 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3486(line=236,offs=1)--3502(line=237,offs=9)))
  // I1VALDCL
  let jsxtnm1293
  let jsxtnm1292 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm1293 = jsxtnm1292
  XATS000_patck(true)
  let jsxtnm1294 = XATSDAPP(jsxtnm1116(jsxtnm1293, jsxtnm1293))
  let jsxtnm1295 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm1294])
  jsxtnm1296 = jsxtnm1295
} // endlet
jsxtnm1297 = jsxtnm1296
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3534(line=239,offs=1)--3607(line=243,offs=38)))
// I1VALDCL
let jsxtnm1304
let jsxtnm1303 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3550(line=241,offs=1)--3566(line=242,offs=9)))
  // I1VALDCL
  let jsxtnm1299
  let jsxtnm1298 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm1299 = jsxtnm1298
  XATS000_patck(true)
  let jsxtnm1300 = XATSDAPP(jsxtnm1116(jsxtnm1299, jsxtnm1299))
  let jsxtnm1301 = XATSDAPP(jsxtnm1116(jsxtnm1299, jsxtnm1300))
  let jsxtnm1302 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm1301])
  jsxtnm1303 = jsxtnm1302
} // endlet
jsxtnm1304 = jsxtnm1303
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3611(line=245,offs=1)--3652(line=245,offs=42)))
// I1VALDCL
let jsxtnm1340
// LCSRCsome1(lambda1.dats)@(3625(line=245,offs=15)--3633(line=245,offs=23))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1338 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1305 = arg1
  let jsxtnm1306 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1329 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1307 = arg1
    let jsxtnm1308 = arg2
    // I1CMP:start
    let jsxtnm1328 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1312
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1310 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1309 = XATSTUP0([])
        // I1CMP:return:jsxtnm1309
        return jsxtnm1309
      } // endtimp(gs_print$beg(793))
      let jsxtnm1311 = XATSDAPP(jsxtnm1310())
      jsxtnm1312 = jsxtnm1311
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1318
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1317 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1313 = arg1
        // I1CMP:start
        let jsxtnm1316 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1314);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1314)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1315 = XATSDAPP(XATS2JS_strn_print(jsxtnm1313))
          jsxtnm1316 = jsxtnm1315
        } // endlet
        // I1CMP:return:jsxtnm1316
        return jsxtnm1316
      } // endtimp(strn_print(1029))
      jsxtnm1318 = jsxtnm1317
      let jsxtnm1319 = XATSDAPP(jsxtnm1318(jsxtnm1307))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1321 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1320 = XATSTUP0([])
        // I1CMP:return:jsxtnm1320
        return jsxtnm1320
      } // endtimp(gs_print$sep(794))
      let jsxtnm1322 = XATSDAPP(jsxtnm1321())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1323
      jsxtnm1323 = jsxtnm879
      let jsxtnm1324 = XATSDAPP(jsxtnm1323(jsxtnm1308))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1326 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1325 = XATSTUP0([])
        // I1CMP:return:jsxtnm1325
        return jsxtnm1325
      } // endtimp(gs_print$end(795))
      let jsxtnm1327 = XATSDAPP(jsxtnm1326())
      jsxtnm1328 = jsxtnm1327
    } // endlet
    // I1CMP:return:jsxtnm1328
    return jsxtnm1328
  } // endtimp(gs_print_a2(798))
  let jsxtnm1330 = XATSDAPP(jsxtnm1329(jsxtnm1305, jsxtnm1306))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1336
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1335 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1331 = arg1
    // I1CMP:start
    let jsxtnm1334 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1332);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1332)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1333 = XATSDAPP(XATS2JS_strn_print(jsxtnm1331))
      jsxtnm1334 = jsxtnm1333
    } // endlet
    // I1CMP:return:jsxtnm1334
    return jsxtnm1334
  } // endtimp(strn_print(1029))
  jsxtnm1336 = jsxtnm1335
  let jsxtnm1337 = XATSDAPP(jsxtnm1336(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1337
  return jsxtnm1337
} // endtimp(gs_println_a2(811))
let jsxtnm1339 = XATSDAPP(jsxtnm1338(XATSSTRN("TMdbl = "), jsxtnm1297))
jsxtnm1340 = jsxtnm1339
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3653(line=246,offs=1)--3694(line=246,offs=42)))
// I1VALDCL
let jsxtnm1376
// LCSRCsome1(lambda1.dats)@(3667(line=246,offs=15)--3675(line=246,offs=23))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1374 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1341 = arg1
  let jsxtnm1342 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1365 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1343 = arg1
    let jsxtnm1344 = arg2
    // I1CMP:start
    let jsxtnm1364 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1348
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1346 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1345 = XATSTUP0([])
        // I1CMP:return:jsxtnm1345
        return jsxtnm1345
      } // endtimp(gs_print$beg(793))
      let jsxtnm1347 = XATSDAPP(jsxtnm1346())
      jsxtnm1348 = jsxtnm1347
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1354
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1353 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1349 = arg1
        // I1CMP:start
        let jsxtnm1352 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1350);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1350)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1351 = XATSDAPP(XATS2JS_strn_print(jsxtnm1349))
          jsxtnm1352 = jsxtnm1351
        } // endlet
        // I1CMP:return:jsxtnm1352
        return jsxtnm1352
      } // endtimp(strn_print(1029))
      jsxtnm1354 = jsxtnm1353
      let jsxtnm1355 = XATSDAPP(jsxtnm1354(jsxtnm1343))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1357 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1356 = XATSTUP0([])
        // I1CMP:return:jsxtnm1356
        return jsxtnm1356
      } // endtimp(gs_print$sep(794))
      let jsxtnm1358 = XATSDAPP(jsxtnm1357())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1359
      jsxtnm1359 = jsxtnm879
      let jsxtnm1360 = XATSDAPP(jsxtnm1359(jsxtnm1344))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1362 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1361 = XATSTUP0([])
        // I1CMP:return:jsxtnm1361
        return jsxtnm1361
      } // endtimp(gs_print$end(795))
      let jsxtnm1363 = XATSDAPP(jsxtnm1362())
      jsxtnm1364 = jsxtnm1363
    } // endlet
    // I1CMP:return:jsxtnm1364
    return jsxtnm1364
  } // endtimp(gs_print_a2(798))
  let jsxtnm1366 = XATSDAPP(jsxtnm1365(jsxtnm1341, jsxtnm1342))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1372
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1371 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1367 = arg1
    // I1CMP:start
    let jsxtnm1370 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1368);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1368)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1369 = XATSDAPP(XATS2JS_strn_print(jsxtnm1367))
      jsxtnm1370 = jsxtnm1369
    } // endlet
    // I1CMP:return:jsxtnm1370
    return jsxtnm1370
  } // endtimp(strn_print(1029))
  jsxtnm1372 = jsxtnm1371
  let jsxtnm1373 = XATSDAPP(jsxtnm1372(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1373
  return jsxtnm1373
} // endtimp(gs_println_a2(811))
let jsxtnm1375 = XATSDAPP(jsxtnm1374(XATSSTRN("TMtpl = "), jsxtnm1304))
jsxtnm1376 = jsxtnm1375
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3741(line=251,offs=1)--3804(line=255,offs=28)))
// I1VALDCL
let jsxtnm1382
let jsxtnm1381 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3757(line=253,offs=1)--3773(line=254,offs=9)))
  // I1VALDCL
  let jsxtnm1378
  let jsxtnm1377 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm1378 = jsxtnm1377
  XATS000_patck(true)
  let jsxtnm1379 = XATSDAPP(jsxtnm1158(jsxtnm1378, jsxtnm1378))
  let jsxtnm1380 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm1379])
  jsxtnm1381 = jsxtnm1380
} // endlet
jsxtnm1382 = jsxtnm1381
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3805(line=256,offs=1)--3878(line=260,offs=38)))
// I1VALDCL
let jsxtnm1389
let jsxtnm1388 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3821(line=258,offs=1)--3837(line=259,offs=9)))
  // I1VALDCL
  let jsxtnm1384
  let jsxtnm1383 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm1384 = jsxtnm1383
  XATS000_patck(true)
  let jsxtnm1385 = XATSDAPP(jsxtnm1158(jsxtnm1384, jsxtnm1384))
  let jsxtnm1386 = XATSDAPP(jsxtnm1158(jsxtnm1384, jsxtnm1385))
  let jsxtnm1387 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm1386])
  jsxtnm1388 = jsxtnm1387
} // endlet
jsxtnm1389 = jsxtnm1388
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3882(line=262,offs=1)--3923(line=262,offs=42)))
// I1VALDCL
let jsxtnm1425
// LCSRCsome1(lambda1.dats)@(3896(line=262,offs=15)--3904(line=262,offs=23))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1423 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1390 = arg1
  let jsxtnm1391 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1414 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1392 = arg1
    let jsxtnm1393 = arg2
    // I1CMP:start
    let jsxtnm1413 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1397
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1395 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1394 = XATSTUP0([])
        // I1CMP:return:jsxtnm1394
        return jsxtnm1394
      } // endtimp(gs_print$beg(793))
      let jsxtnm1396 = XATSDAPP(jsxtnm1395())
      jsxtnm1397 = jsxtnm1396
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1403
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1402 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1398 = arg1
        // I1CMP:start
        let jsxtnm1401 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1399);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1399)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1400 = XATSDAPP(XATS2JS_strn_print(jsxtnm1398))
          jsxtnm1401 = jsxtnm1400
        } // endlet
        // I1CMP:return:jsxtnm1401
        return jsxtnm1401
      } // endtimp(strn_print(1029))
      jsxtnm1403 = jsxtnm1402
      let jsxtnm1404 = XATSDAPP(jsxtnm1403(jsxtnm1392))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1406 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1405 = XATSTUP0([])
        // I1CMP:return:jsxtnm1405
        return jsxtnm1405
      } // endtimp(gs_print$sep(794))
      let jsxtnm1407 = XATSDAPP(jsxtnm1406())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1408
      jsxtnm1408 = jsxtnm879
      let jsxtnm1409 = XATSDAPP(jsxtnm1408(jsxtnm1393))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1411 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1410 = XATSTUP0([])
        // I1CMP:return:jsxtnm1410
        return jsxtnm1410
      } // endtimp(gs_print$end(795))
      let jsxtnm1412 = XATSDAPP(jsxtnm1411())
      jsxtnm1413 = jsxtnm1412
    } // endlet
    // I1CMP:return:jsxtnm1413
    return jsxtnm1413
  } // endtimp(gs_print_a2(798))
  let jsxtnm1415 = XATSDAPP(jsxtnm1414(jsxtnm1390, jsxtnm1391))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1421
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1420 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1416 = arg1
    // I1CMP:start
    let jsxtnm1419 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1417);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1417)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1418 = XATSDAPP(XATS2JS_strn_print(jsxtnm1416))
      jsxtnm1419 = jsxtnm1418
    } // endlet
    // I1CMP:return:jsxtnm1419
    return jsxtnm1419
  } // endtimp(strn_print(1029))
  jsxtnm1421 = jsxtnm1420
  let jsxtnm1422 = XATSDAPP(jsxtnm1421(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1422
  return jsxtnm1422
} // endtimp(gs_println_a2(811))
let jsxtnm1424 = XATSDAPP(jsxtnm1423(XATSSTRN("TMsqr = "), jsxtnm1382))
jsxtnm1425 = jsxtnm1424
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3924(line=263,offs=1)--3965(line=263,offs=42)))
// I1VALDCL
let jsxtnm1461
// LCSRCsome1(lambda1.dats)@(3938(line=263,offs=15)--3946(line=263,offs=23))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm1459 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm1426 = arg1
  let jsxtnm1427 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm1450 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm1428 = arg1
    let jsxtnm1429 = arg2
    // I1CMP:start
    let jsxtnm1449 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm1433
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm1431 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm1430 = XATSTUP0([])
        // I1CMP:return:jsxtnm1430
        return jsxtnm1430
      } // endtimp(gs_print$beg(793))
      let jsxtnm1432 = XATSDAPP(jsxtnm1431())
      jsxtnm1433 = jsxtnm1432
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm1439
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm1438 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm1434 = arg1
        // I1CMP:start
        let jsxtnm1437 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(1435);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1435)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm1436 = XATSDAPP(XATS2JS_strn_print(jsxtnm1434))
          jsxtnm1437 = jsxtnm1436
        } // endlet
        // I1CMP:return:jsxtnm1437
        return jsxtnm1437
      } // endtimp(strn_print(1029))
      jsxtnm1439 = jsxtnm1438
      let jsxtnm1440 = XATSDAPP(jsxtnm1439(jsxtnm1428))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm1442 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm1441 = XATSTUP0([])
        // I1CMP:return:jsxtnm1441
        return jsxtnm1441
      } // endtimp(gs_print$sep(794))
      let jsxtnm1443 = XATSDAPP(jsxtnm1442())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm1444
      jsxtnm1444 = jsxtnm879
      let jsxtnm1445 = XATSDAPP(jsxtnm1444(jsxtnm1429))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm1447 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm1446 = XATSTUP0([])
        // I1CMP:return:jsxtnm1446
        return jsxtnm1446
      } // endtimp(gs_print$end(795))
      let jsxtnm1448 = XATSDAPP(jsxtnm1447())
      jsxtnm1449 = jsxtnm1448
    } // endlet
    // I1CMP:return:jsxtnm1449
    return jsxtnm1449
  } // endtimp(gs_print_a2(798))
  let jsxtnm1451 = XATSDAPP(jsxtnm1450(jsxtnm1426, jsxtnm1427))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm1457
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm1456 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm1452 = arg1
    // I1CMP:start
    let jsxtnm1455 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(1453);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(1453)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm1454 = XATSDAPP(XATS2JS_strn_print(jsxtnm1452))
      jsxtnm1455 = jsxtnm1454
    } // endlet
    // I1CMP:return:jsxtnm1455
    return jsxtnm1455
  } // endtimp(strn_print(1029))
  jsxtnm1457 = jsxtnm1456
  let jsxtnm1458 = XATSDAPP(jsxtnm1457(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm1458
  return jsxtnm1458
} // endtimp(gs_println_a2(811))
let jsxtnm1460 = XATSDAPP(jsxtnm1459(XATSSTRN("TMcbr = "), jsxtnm1389))
jsxtnm1461 = jsxtnm1460
XATS000_patck(true)
// I1Dextern(LCSRCsome1(lambda1.dats)@(4054(line=272,offs=1)--4118(line=276,offs=30)))
// LCSRCsome1(lambda1.dats)@(4062(line=273,offs=1)--4118(line=276,offs=30))
// I1FUNDCL
// term_subst_4065
  // FJARGdarg($list(I1BNDcons(I1TNM(1462);I0Pvar(tm0(5277));$list(@(tm0(5277),I1Vtnm(I1TNM(1462))))),I1BNDcons(I1TNM(1463);I0Pvar(x00(5278));$list(@(x00(5278),I1Vtnm(I1TNM(1463))))),I1BNDcons(I1TNM(1464);I0Pvar(sub(5279));$list(@(sub(5279),I1Vtnm(I1TNM(1464)))))))
// I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(4122(line=278,offs=1)--4840(line=333,offs=4)))
let term_subst_4065 = function (arg1, arg2, arg3) { // impl
  let jsxtnm1465 = arg1
  let jsxtnm1466 = arg2
  let jsxtnm1467 = arg3
  // I1CMP:start
  let jsxtnm1710 // let
  { // let
    // I1Dfundclist(LCSRCsome1(lambda1.dats)@(4167(line=283,offs=1)--4209(line=285,offs=26)))
    // I1FUNDCL
    function subst_4170(arg1)
    { // fun
      let jsxtnm1468 = arg1
      // I1CMP:start
      let jsxtnm1469 = XATSDAPP(term_subst_4065(jsxtnm1468, jsxtnm1466, jsxtnm1467))
      // I1CMP:return:jsxtnm1469
      return jsxtnm1469
    } // endfun(subst_4170)
    let jsxtnm1709 // cas
    do {
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1470);I0Pdap1(I0Pcon(TMint(32)));$list()))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMint",0))) { // gpt
        let jsxtnm1470 = jsxtnm1465
        jsxtnm1709 = jsxtnm1465
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1471);I0Pdap1(I0Pcon(TMbtf(33)));$list()))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMbtf",1))) { // gpt
        let jsxtnm1471 = jsxtnm1465
        jsxtnm1709 = jsxtnm1465
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1472);I0Pdapp(I0Pcon(TMvar(34));$list(I0Pvar(x01(5285))));$list(@(x01(5285),I1Vp1cn(I0Pcon(TMvar(34));I1Vtnm(I1TNM(1472));0)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMvar",2))) { // gpt
        let jsxtnm1472 = jsxtnm1465
        // LCSRCsome1(lambda1.dats)@(4296(line=296,offs=4)--4297(line=296,offs=5))
        // I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
        // T1IMPallx(strn_eq(1024);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
        // T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
        let jsxtnm1493
        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
        // I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        // T1IMPallx(g_eq(226);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
        // T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5857],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[776],T2Pvar(x0[5857])))))))
        let jsxtnm1492 = function (arg1, arg2) { // timp: g_eq(226)
          let jsxtnm1473 = arg1
          let jsxtnm1474 = arg2
          // I1CMP:start
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
          // I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
          // T1IMPallx(sint_eq$sint(920);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
          // T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
          let jsxtnm1481 = function (arg1, arg2) { // timp: sint_eq$sint(920)
            let jsxtnm1475 = arg1
            let jsxtnm1476 = arg2
            // I1CMP:start
            let jsxtnm1480 // let
            { // let
              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2038(line=93,offs=1)--2101(line=95,offs=39))
              // I1FUNDCL
              // XATS2JS_sint_eq$sint_2041
                // FJARGdarg($list(I1BNDcons(I1TNM(1477);I0Pvar(i1(4913));$list(@(i1(4913),I1Vtnm(I1TNM(1477))))),I1BNDcons(I1TNM(1478);I0Pvar(i2(4914));$list(@(i2(4914),I1Vtnm(I1TNM(1478)))))))
                // I1CMP:start
                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_eq$sint);G1Nlist($list())) // I1CMP:return
              let jsxtnm1479 = XATSDAPP(XATS2JS_sint_eq$sint(jsxtnm1475, jsxtnm1476))
              jsxtnm1480 = jsxtnm1479
            } // endlet
            // I1CMP:return:jsxtnm1480
            return jsxtnm1480
          } // endtimp(sint_eq$sint(920))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
          // I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5857])))))
          // T1IMPallx(g_cmp(230);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
          // T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[780],T2Pcst(strn)))))))
          let jsxtnm1489
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
          // I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
          // T1IMPallx(strn_cmp(1028);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1859(line=79,offs=1)--2008(line=91,offs=2)))
          // T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
          let jsxtnm1488 = function (arg1, arg2) { // timp: strn_cmp(1028)
            let jsxtnm1482 = arg1
            let jsxtnm1483 = arg2
            // I1CMP:start
            let jsxtnm1487 // let
            { // let
              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1939(line=87,offs=1)--2006(line=90,offs=39)))
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1947(line=88,offs=1)--2006(line=90,offs=39))
              // I1FUNDCL
              // XATS2JS_strn_cmp_1950
                // FJARGdarg($list(I1BNDcons(I1TNM(1484);I0Pvar(x1(5089));$list(@(x1(5089),I1Vtnm(I1TNM(1484))))),I1BNDcons(I1TNM(1485);I0Pvar(x2(5090));$list(@(x2(5090),I1Vtnm(I1TNM(1485)))))))
                // I1CMP:start
                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_cmp);G1Nlist($list())) // I1CMP:return
              let jsxtnm1486 = XATSDAPP(XATS2JS_strn_cmp(jsxtnm1482, jsxtnm1483))
              jsxtnm1487 = jsxtnm1486
            } // endlet
            // I1CMP:return:jsxtnm1487
            return jsxtnm1487
          } // endtimp(strn_cmp(1028))
          jsxtnm1489 = jsxtnm1488
          let jsxtnm1490 = XATSDAPP(jsxtnm1489(jsxtnm1473, jsxtnm1474))
          let jsxtnm1491 = XATSDAPP(jsxtnm1481(jsxtnm1490, XATSINT1(0)))
          // I1CMP:return:jsxtnm1491
          return jsxtnm1491
        } // endtimp(g_eq(226))
        jsxtnm1493 = jsxtnm1492
        let jsxtnm1494 = XATSDAPP(jsxtnm1493(jsxtnm1466, XATSP1CN("TMvar", jsxtnm1472[0+1])))
        let jsxtnm1495 // ift
        if (jsxtnm1494) // ift
        {
          jsxtnm1495 = jsxtnm1467
        } else {
          jsxtnm1495 = jsxtnm1465
        } // end(if)
        jsxtnm1709 = jsxtnm1495
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1496);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5286)),I0Pvar(tmx(5287))));$list(@(x01(5286),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1496));0)),@(tmx(5287),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1496));1)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMlam",3))) { // gpt
        let jsxtnm1496 = jsxtnm1465
        // LCSRCsome1(lambda1.dats)@(4349(line=300,offs=5)--4350(line=300,offs=6))
        // I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
        // T1IMPallx(strn_eq(1024);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
        // T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
        let jsxtnm1517
        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
        // I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        // T1IMPallx(g_eq(226);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
        // T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5857],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[776],T2Pvar(x0[5857])))))))
        let jsxtnm1516 = function (arg1, arg2) { // timp: g_eq(226)
          let jsxtnm1497 = arg1
          let jsxtnm1498 = arg2
          // I1CMP:start
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
          // I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
          // T1IMPallx(sint_eq$sint(920);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
          // T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
          let jsxtnm1505 = function (arg1, arg2) { // timp: sint_eq$sint(920)
            let jsxtnm1499 = arg1
            let jsxtnm1500 = arg2
            // I1CMP:start
            let jsxtnm1504 // let
            { // let
              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2038(line=93,offs=1)--2101(line=95,offs=39))
              // I1FUNDCL
              // XATS2JS_sint_eq$sint_2041
                // FJARGdarg($list(I1BNDcons(I1TNM(1501);I0Pvar(i1(4913));$list(@(i1(4913),I1Vtnm(I1TNM(1501))))),I1BNDcons(I1TNM(1502);I0Pvar(i2(4914));$list(@(i2(4914),I1Vtnm(I1TNM(1502)))))))
                // I1CMP:start
                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_eq$sint);G1Nlist($list())) // I1CMP:return
              let jsxtnm1503 = XATSDAPP(XATS2JS_sint_eq$sint(jsxtnm1499, jsxtnm1500))
              jsxtnm1504 = jsxtnm1503
            } // endlet
            // I1CMP:return:jsxtnm1504
            return jsxtnm1504
          } // endtimp(sint_eq$sint(920))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
          // I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5857])))))
          // T1IMPallx(g_cmp(230);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
          // T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[780],T2Pcst(strn)))))))
          let jsxtnm1513
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
          // I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
          // T1IMPallx(strn_cmp(1028);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1859(line=79,offs=1)--2008(line=91,offs=2)))
          // T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
          let jsxtnm1512 = function (arg1, arg2) { // timp: strn_cmp(1028)
            let jsxtnm1506 = arg1
            let jsxtnm1507 = arg2
            // I1CMP:start
            let jsxtnm1511 // let
            { // let
              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1939(line=87,offs=1)--2006(line=90,offs=39)))
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1947(line=88,offs=1)--2006(line=90,offs=39))
              // I1FUNDCL
              // XATS2JS_strn_cmp_1950
                // FJARGdarg($list(I1BNDcons(I1TNM(1508);I0Pvar(x1(5089));$list(@(x1(5089),I1Vtnm(I1TNM(1508))))),I1BNDcons(I1TNM(1509);I0Pvar(x2(5090));$list(@(x2(5090),I1Vtnm(I1TNM(1509)))))))
                // I1CMP:start
                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_cmp);G1Nlist($list())) // I1CMP:return
              let jsxtnm1510 = XATSDAPP(XATS2JS_strn_cmp(jsxtnm1506, jsxtnm1507))
              jsxtnm1511 = jsxtnm1510
            } // endlet
            // I1CMP:return:jsxtnm1511
            return jsxtnm1511
          } // endtimp(strn_cmp(1028))
          jsxtnm1513 = jsxtnm1512
          let jsxtnm1514 = XATSDAPP(jsxtnm1513(jsxtnm1497, jsxtnm1498))
          let jsxtnm1515 = XATSDAPP(jsxtnm1505(jsxtnm1514, XATSINT1(0)))
          // I1CMP:return:jsxtnm1515
          return jsxtnm1515
        } // endtimp(g_eq(226))
        jsxtnm1517 = jsxtnm1516
        let jsxtnm1518 = XATSDAPP(jsxtnm1517(jsxtnm1466, XATSP1CN("TMlam", jsxtnm1496[0+1])))
        let jsxtnm1521 // ift
        if (jsxtnm1518) // ift
        {
          jsxtnm1521 = jsxtnm1465
        } else {
          let jsxtnm1519 = XATSDAPP(subst_4170(XATSP1CN("TMlam", jsxtnm1496[1+1])))
          let jsxtnm1520 = XATSCAPP("TMlam", [3, XATSP1CN("TMlam", jsxtnm1496[0+1]), jsxtnm1519])
          jsxtnm1521 = jsxtnm1520
        } // end(if)
        jsxtnm1709 = jsxtnm1521
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1522);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5288)),I0Pvar(tm2(5289))));$list(@(tm1(5288),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1522));0)),@(tm2(5289),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1522));1)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMapp",4))) { // gpt
        let jsxtnm1522 = jsxtnm1465
        let jsxtnm1523 = XATSDAPP(subst_4170(XATSP1CN("TMapp", jsxtnm1522[0+1])))
        let jsxtnm1524 = XATSDAPP(subst_4170(XATSP1CN("TMapp", jsxtnm1522[1+1])))
        let jsxtnm1525 = XATSCAPP("TMapp", [4, jsxtnm1523, jsxtnm1524])
        jsxtnm1709 = jsxtnm1525
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1526);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(f00(5290)),I0Pvar(tms(5291))));$list(@(f00(5290),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1526));0)),@(tms(5291),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1526));1)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMopr",5))) { // gpt
        let jsxtnm1526 = jsxtnm1465
        // LCSRCsome1(lambda1.dats)@(4488(line=310,offs=12)--4498(line=310,offs=22))
        // I0Etapq(I0Ecst(f1un_map$list(316)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gfun000.sats)@(4882(line=281,offs=1)--4895(line=281,offs=14))));$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term)))))
        // T1IMPallx(f1un_map$list(316);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gfun000.dats)@(5083(line=298,offs=1)--5181(line=304,offs=32)))
        // T1IMPallx(f1un_map$list(316)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[5903],T2Pcst(term)),@(y0[5904],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(f1un_map$list(316);$list(@(x0[989],T2Pvar(x0[5903])),@(y0[990],T2Pvar(y0[5904])))))))
        let jsxtnm1621 = function (arg1) { // timp: f1un_map$list(316)
          let jsxtnm1527 = arg1
          // I1CMP:start
          let jsxtnm1620 = function (arg1) { // lam0(T_LAM(0))
            let jsxtnm1528 = arg1
            // I1CMP:start
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gfun000.dats)@(5150(line=304,offs=1)--5163(line=304,offs=14))
            // I0Etapq(I0Ecst(list_map$f1un(1243)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(8026(line=382,offs=1)--8039(line=382,offs=14))));$list(T2JAG($list(T2Pvar(x0[5903]))),T2JAG($list(T2Pvar(y0[5904])))))
            // T1IMPallx(list_map$f1un(1243);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(9918(line=664,offs=1)--9999(line=668,offs=37)))
            // T1IMPallx(list_map$f1un(1243)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7422],T2Pcst(term)),@(y0[7423],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_map$f1un(1243);$list(@(x0[3419],T2Pvar(x0[7422])),@(y0[3420],T2Pvar(y0[7423])))))))
            let jsxtnm1618
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(9963(line=668,offs=1)--9981(line=668,offs=19))
            // I0Etapq(I0Ecst(gseq_map$f1un_list(428)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(13108(line=758,offs=1)--13126(line=758,offs=19))));$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pvar(x0[7422]),T2Pnone0())))),T2JAG($list(T2Pvar(x0[7422]))),T2JAG($list(T2Pvar(y0[7423])))))
            // T1IMPallx(gseq_map$f1un_list(428);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14500(line=996,offs=1)--14631(line=1004,offs=43)))
            // T1IMPallx(gseq_map$f1un_list(428)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6107],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6108],T2Pcst(term)),@(y0[6109],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map$f1un_list(428);$list(@(xs[1293],T2Pvar(xs[6107])),@(x0[1294],T2Pvar(x0[6108])),@(y0[1295],T2Pvar(y0[6109])))))))
            let jsxtnm1617 = function (arg1, arg2) { // timp: gseq_map$f1un_list(428)
              let jsxtnm1529 = arg1
              let jsxtnm1530 = arg2
              // I1CMP:start
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14589(line=1004,offs=1)--14608(line=1004,offs=20))
              // I0Etapq(I0Ecst(gseq_map$f1un_llist(429)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(13306(line=771,offs=1)--13325(line=771,offs=20))));$list(T2JAG($list(T2Pvar(xs[6107]))),T2JAG($list(T2Pvar(x0[6108]))),T2JAG($list(T2Pvar(y0[6109])))))
              // T1IMPallx(gseq_map$f1un_llist(429);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14781(line=1018,offs=1)--14943(line=1030,offs=2)))
              // T1IMPallx(gseq_map$f1un_llist(429)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6113],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6114],T2Pcst(term)),@(y0[6115],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map$f1un_llist(429);$list(@(xs[1296],T2Pvar(xs[6113])),@(x0[1297],T2Pvar(x0[6114])),@(y0[1298],T2Pvar(y0[6115])))))))
              let jsxtnm1614 = function (arg1, arg2) { // timp: gseq_map$f1un_llist(429)
                let jsxtnm1531 = arg1
                let jsxtnm1532 = arg2
                // I1CMP:start
                let jsxtnm1613 // let
                { // let
                  // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14897(line=1028,offs=1)--14941(line=1029,offs=36)))
                  // I1Dimplmnt0(DIMPLone2(map$fopr(75);$list(@(x0[483],T2Pvar(x0[6114])),@(y0[484],T2Pvar(y0[6115]))))):timp
                  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14857(line=1025,offs=1)--14871(line=1025,offs=15))
                  // I0Etapq(I0Ecst(gseq_map_llist(425)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(12650(line=732,offs=1)--12664(line=732,offs=15))));$list(T2JAG($list(T2Pvar(xs[6113]))),T2JAG($list(T2Pvar(x0[6114]))),T2JAG($list(T2Pvar(y0[6115])))))
                  // T1IMPallx(gseq_map_llist(425);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14658(line=1008,offs=1)--14777(line=1016,offs=32)))
                  // T1IMPallx(gseq_map_llist(425)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6110],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6111],T2Pcst(term)),@(y0[6112],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map_llist(425);$list(@(xs[1284],T2Pvar(xs[6110])),@(x0[1285],T2Pvar(x0[6111])),@(y0[1286],T2Pvar(y0[6112])))))))
                  let jsxtnm1611 = function (arg1) { // timp: gseq_map_llist(425)
                    let jsxtnm1535 = arg1
                    // I1CMP:start
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14723(line=1014,offs=1)--14739(line=1014,offs=17))
                    // I0Etapq(I0Ecst(strm_vt_listize0(2194)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/strm001_vt.sats)@(8819(line=452,offs=1)--8835(line=452,offs=17))));$list(T2JAG($list(T2Pvar(y0[6112])))))
                    // T1IMPallx(strm_vt_listize0(2194);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7222(line=450,offs=1)--7317(line=455,offs=28)))
                    // T1IMPallx(strm_vt_listize0(2194)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8567],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(strm_vt_listize0(2194);$list(@(x0[5484],T2Pvar(x0[8567])))))))
                    let jsxtnm1572 = function (arg1) { // timp: strm_vt_listize0(2194)
                      let jsxtnm1536 = arg1
                      // I1CMP:start
                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7269(line=454,offs=1)--7285(line=454,offs=17))
                      // I0Etapq(I0Ecst(list_vt_reverse0(2015)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/list000_vt.sats)@(4454(line=254,offs=1)--4470(line=254,offs=17))));$list(T2JAG($list(T2Pvar(x0[8567])))))
                      // T1IMPallx(list_vt_reverse0(2015);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6829(line=462,offs=1)--6916(line=465,offs=46)))
                      // T1IMPallx(list_vt_reverse0(2015)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(a[8401],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_vt_reverse0(2015);$list(@(x0[5185],T2Pvar(a[8401])))))))
                      let jsxtnm1555 = function (arg1) { // timp: list_vt_reverse0(2015)
                        let jsxtnm1537 = arg1
                        // I1CMP:start
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6871(line=465,offs=1)--6888(line=465,offs=18))
                        // I0Etapq(I0Ecst(list_vt_rappend00(2018)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/list000_vt.sats)@(4835(line=280,offs=1)--4852(line=280,offs=18))));$list(T2JAG($list(T2Pvar(a[8401])))))
                        // T1IMPallx(list_vt_rappend00(2018);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6351(line=426,offs=1)--6760(line=458,offs=2)))
                        // T1IMPallx(list_vt_rappend00(2018)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(a[8398],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_vt_rappend00(2018);$list(@(x0[5192],T2Pvar(a[8398])))))))
                        let jsxtnm1552 = function (arg1, arg2) { // timp: list_vt_rappend00(2018)
                          let jsxtnm1538 = arg1
                          let jsxtnm1539 = arg2
                          // I1CMP:start
                          let jsxtnm1551 // let
                          { // let
                            // I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6430(line=434,offs=1)--6721(line=456,offs=2)))
                            // I1FUNDCL
                            function loop_6433(arg1, arg2)
                            { // fun
                              let jsxtnm1540 = arg1
                              let jsxtnm1541 = arg2
                              // I1CMP:start
                              let jsxtnm1549 // cas
                              do {
                                // { // cls
                                // I1GPTpat(I1BNDcons(I1TNM(1542);I0Pfree(I0Pdapp(I0Pcon(list_vt_nil(10));$list()));$list()))
                                if (XATS000_ctgeq(jsxtnm1540, XATSCTAG("list_vt_nil",0))) { // gpt
                                  let jsxtnm1542 = jsxtnm1540
                                  jsxtnm1549 = jsxtnm1541
                                  break // cls
                                } // gpt
                                // } // cls
                                // { // cls
                                // I1GPTpat(I1BNDcons(I1TNM(1543);I0Pflat(I0Pdapp(I0Pcon(list_vt_cons(11));$list(I0Pany(),I0Pany())));$list()))
                                if (XATS000_ctgeq(jsxtnm1540, XATSCTAG("list_vt_cons",1))) { // gpt
                                  let jsxtnm1543 = jsxtnm1540
                                  let jsxtnm1548 // let
                                  { // let
                                    // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6604(line=450,offs=3)--6619(line=450,offs=18)))
                                    // I1VALDCL
                                    let jsxtnm1545
                                    let jsxtnm1544 = XATSPCON(jsxtnm1540,1)
                                    jsxtnm1545 = jsxtnm1544
                                    XATS000_patck(true)
                                    // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6622(line=451,offs=3)--6644(line=451,offs=25)))
                                    // I1VALDCL
                                    let jsxtnm1546
                                    XATS000_assgn(XATSLPCN(1, jsxtnm1540), jsxtnm1541)
                                    jsxtnm1546 = []
                                    XATS000_patck(true)
                                    XATS000_fold(jsxtnm1540)
                                    let jsxtnm1547 = XATSDAPP(loop_6433(jsxtnm1545, jsxtnm1540))
                                    jsxtnm1548 = jsxtnm1547
                                  } // endlet
                                  jsxtnm1549 = jsxtnm1548
                                  break // cls
                                } // gpt
                                // } // cls
                                XATS000_cfail()
                              } while (false) // end-of(do)
                              // I1CMP:return:jsxtnm1549
                              return jsxtnm1549
                            } // endfun(loop_6433)
                            let jsxtnm1550 = XATSDAPP(loop_6433(jsxtnm1538, jsxtnm1539))
                            jsxtnm1551 = jsxtnm1550
                          } // endlet
                          // I1CMP:return:jsxtnm1551
                          return jsxtnm1551
                        } // endtimp(list_vt_rappend00(2018))
                        let jsxtnm1553 = XATSCAPP("list_vt_nil", [0])
                        let jsxtnm1554 = XATSDAPP(jsxtnm1552(jsxtnm1537, jsxtnm1553))
                        // I1CMP:return:jsxtnm1554
                        return jsxtnm1554
                      } // endtimp(list_vt_reverse0(2015))
                      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7291(line=455,offs=2)--7308(line=455,offs=19))
                      // I0Etapq(I0Ecst(strm_vt_rlistize0(2196)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/strm001_vt.sats)@(8956(line=462,offs=1)--8973(line=462,offs=18))));$list(T2JAG($list(T2Pvar(x0[8567])))))
                      // T1IMPallx(strm_vt_rlistize0(2196);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7321(line=457,offs=1)--7614(line=480,offs=2)))
                      // T1IMPallx(strm_vt_rlistize0(2196)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8568],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(strm_vt_rlistize0(2196);$list(@(x0[5487],T2Pvar(x0[8568])))))))
                      let jsxtnm1569 = function (arg1) { // timp: strm_vt_rlistize0(2196)
                        let jsxtnm1556 = arg1
                        // I1CMP:start
                        let jsxtnm1568 // let
                        { // let
                          // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7398(line=465,offs=1)--7420(line=465,offs=23)))
                          // I1VALDCL
                          let jsxtnm1558
                          let jsxtnm1557 = XATSCAPP("list_vt_nil", [0])
                          jsxtnm1558 = jsxtnm1557
                          XATS000_patck(true)
                          // I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7424(line=467,offs=1)--7612(line=479,offs=35)))
                          // I1FUNDCL
                          function loop_7427(arg1, arg2)
                          { // fun
                            let jsxtnm1559 = arg1
                            let jsxtnm1560 = arg2
                            // I1CMP:start
                            let jsxtnm1561 = XATS000_dl1az(jsxtnm1559)
                            let jsxtnm1566 // cas
                            do {
                              // { // cls
                              // I1GPTpat(I1BNDcons(I1TNM(1562);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_nil(15));$list()));$list()))
                              if (XATS000_ctgeq(jsxtnm1561, XATSCTAG("strmcon_vt_nil",0))) { // gpt
                                let jsxtnm1562 = jsxtnm1561
                                jsxtnm1566 = jsxtnm1560
                                break // cls
                              } // gpt
                              // } // cls
                              // { // cls
                              // I1GPTpat(I1BNDcons(I1TNM(1563);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_cons(16));$list(I0Pvar(x1(4505)),I0Pvar(xs(4506)))));$list(@(x1(4505),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1563));0)),@(xs(4506),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1563));1)))))
                              if (XATS000_ctgeq(jsxtnm1561, XATSCTAG("strmcon_vt_cons",1))) { // gpt
                                let jsxtnm1563 = jsxtnm1561
                                let jsxtnm1564 = XATSCAPP("list_vt_cons", [1, XATSP1CN("strmcon_vt_cons", jsxtnm1563[0+1]), jsxtnm1560])
                                let jsxtnm1565 = XATSDAPP(loop_7427(XATSP1CN("strmcon_vt_cons", jsxtnm1563[1+1]), jsxtnm1564))
                                jsxtnm1566 = jsxtnm1565
                                break // cls
                              } // gpt
                              // } // cls
                              XATS000_cfail()
                            } while (false) // end-of(do)
                            // I1CMP:return:jsxtnm1566
                            return jsxtnm1566
                          } // endfun(loop_7427)
                          let jsxtnm1567 = XATSDAPP(loop_7427(jsxtnm1556, jsxtnm1558))
                          jsxtnm1568 = jsxtnm1567
                        } // endlet
                        // I1CMP:return:jsxtnm1568
                        return jsxtnm1568
                      } // endtimp(strm_vt_rlistize0(2196))
                      let jsxtnm1570 = XATSDAPP(jsxtnm1569(jsxtnm1536))
                      let jsxtnm1571 = XATSDAPP(jsxtnm1555(jsxtnm1570))
                      // I1CMP:return:jsxtnm1571
                      return jsxtnm1571
                    } // endtimp(strm_vt_listize0(2194))
                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14746(line=1016,offs=1)--14760(line=1016,offs=15))
                    // I0Etapq(I0Ecst(gseq_map_lstrm(426)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(12714(line=737,offs=1)--12728(line=737,offs=15))));$list(T2JAG($list(T2Pvar(xs[6110]))),T2JAG($list(T2Pvar(x0[6111]))),T2JAG($list(T2Pvar(y0[6112])))))
                    // T1IMPallx(gseq_map_lstrm(426);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15009(line=1034,offs=1)--15178(line=1046,offs=2)))
                    // T1IMPallx(gseq_map_lstrm(426)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6116],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6117],T2Pcst(term)),@(y0[6118],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map_lstrm(426);$list(@(xs[1287],T2Pvar(xs[6116])),@(x0[1288],T2Pvar(x0[6117])),@(y0[1289],T2Pvar(y0[6118])))))))
                    let jsxtnm1608 = function (arg1) { // timp: gseq_map_lstrm(426)
                      let jsxtnm1573 = arg1
                      // I1CMP:start
                      let jsxtnm1607 // let
                      { // let
                        // I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15131(line=1044,offs=1)--15176(line=1045,offs=37)))
                        // I1Dimplmnt0(DIMPLone2(map$fopr0(1471);$list(@(x0[3806],T2Pvar(x0[6117])),@(y0[3807],T2Pvar(y0[6118]))))):timp
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15074(line=1040,offs=1)--15086(line=1040,offs=13))
                        // I0Etapq(I0Ecst(strm_vt_map0(2174)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/strm001_vt.sats)@(5100(line=256,offs=1)--5112(line=256,offs=13))));$list(T2JAG($list(T2Pvar(x0[6117]))),T2JAG($list(T2Pvar(y0[6118])))))
                        // T1IMPallx(strm_vt_map0(2174);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(4033(line=214,offs=1)--4316(line=237,offs=2)))
                        // T1IMPallx(strm_vt_map0(2174)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8550],T2Pcst(term)),@(y0[8551],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(strm_vt_map0(2174);$list(@(x0[5443],T2Pvar(x0[8550])),@(y0[5444],T2Pvar(y0[8551])))))))
                        let jsxtnm1591 = function (arg1) { // timp: strm_vt_map0(2174)
                          let jsxtnm1574 = arg1
                          // I1CMP:start
                          let jsxtnm1590 // let
                          { // let
                            // I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(4111(line=222,offs=1)--4314(line=236,offs=2)))
                            // I1FUNDCL
                            function auxmain_4114(arg1)
                            { // fun
                              let jsxtnm1575 = arg1
                              // I1CMP:start
                              let jsxtnm1588 = XATS000_l1azy(function (tlaz) { // l1azy
                                // I1CMP:start
                                let jsxtnm1576 = XATS000_dl1az(jsxtnm1575)
                                let jsxtnm1587 // cas
                                do {
                                  // { // cls
                                  // I1GPTpat(I1BNDcons(I1TNM(1577);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_nil(15));$list()));$list()))
                                  if (XATS000_ctgeq(jsxtnm1576, XATSCTAG("strmcon_vt_nil",0))) { // gpt
                                    let jsxtnm1577 = jsxtnm1576
                                    let jsxtnm1578 = XATSCAPP("strmcon_vt_nil", [0])
                                    jsxtnm1587 = jsxtnm1578
                                    break // cls
                                  } // gpt
                                  // } // cls
                                  // { // cls
                                  // I1GPTpat(I1BNDcons(I1TNM(1579);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_cons(16));$list(I0Pvar(x1(4467)),I0Pvar(xs(4468)))));$list(@(x1(4467),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1579));0)),@(xs(4468),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1579));1)))))
                                  if (XATS000_ctgeq(jsxtnm1576, XATSCTAG("strmcon_vt_cons",1))) { // gpt
                                    let jsxtnm1579 = jsxtnm1576
                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(4277(line=235,offs=2)--4286(line=235,offs=11))
                                    // I0Etapq(I0Ecst(map$fopr0(1471)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas001_vt.sats)@(5345(line=363,offs=1)--5354(line=363,offs=10))));$list(T2JAG($list(T2Pvar(x0[8550]))),T2JAG($list(T2Pvar(y0[8551])))))
                                    // T1IMPallx(map$fopr0(1471);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15131(line=1044,offs=1)--15176(line=1045,offs=37)))
                                    // T1IMPallx(map$fopr0(1471)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6116],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6117],T2Pcst(term)),@(y0[6118],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(map$fopr0(1471);$list(@(x0[3806],T2Pcst(term)),@(y0[3807],T2Pcst(term)))))))
                                    let jsxtnm1583
                                    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15160(line=1045,offs=21)--15168(line=1045,offs=29))
                                    // I0Etapq(I0Ecst(map$fopr(75)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(3732(line=232,offs=1)--3740(line=232,offs=9))));$list(T2JAG($list(T2Pvar(x0[6117]))),T2JAG($list(T2Pvar(y0[6118])))))
                                    // T1IMPallx(map$fopr(75);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14897(line=1028,offs=1)--14941(line=1029,offs=36)))
                                    // T1IMPallx(map$fopr(75)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6113],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6114],T2Pcst(term)),@(y0[6115],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(map$fopr(75);$list(@(x0[483],T2Pcst(term)),@(y0[484],T2Pcst(term)))))))
                                    let jsxtnm1582 = function (arg1) { // timp: map$fopr(75)
                                      let jsxtnm1580 = arg1
                                      // I1CMP:start
                                      let jsxtnm1581 = XATSDAPP(jsxtnm1532(jsxtnm1580))
                                      // I1CMP:return:jsxtnm1581
                                      return jsxtnm1581
                                    } // endtimp(map$fopr(75))
                                    jsxtnm1583 = jsxtnm1582
                                    let jsxtnm1584 = XATSDAPP(jsxtnm1583(XATSP1CN("strmcon_vt_cons", jsxtnm1579[0+1])))
                                    let jsxtnm1585 = XATSDAPP(auxmain_4114(XATSP1CN("strmcon_vt_cons", jsxtnm1579[1+1])))
                                    let jsxtnm1586 = XATSCAPP("strmcon_vt_cons", [1, jsxtnm1584, jsxtnm1585])
                                    jsxtnm1587 = jsxtnm1586
                                    break // cls
                                  } // gpt
                                  // } // cls
                                  XATS000_cfail()
                                } while (false) // end-of(do)
                                // I1CMP:return:jsxtnm1587
                                return jsxtnm1587
                              }) // endfun(l1azy)
                              // I1CMP:return:jsxtnm1588
                              return jsxtnm1588
                            } // endfun(auxmain_4114)
                            let jsxtnm1589 = XATSDAPP(auxmain_4114(jsxtnm1574))
                            jsxtnm1590 = jsxtnm1589
                          } // endlet
                          // I1CMP:return:jsxtnm1590
                          return jsxtnm1590
                        } // endtimp(strm_vt_map0(2174))
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15097(line=1042,offs=1)--15109(line=1042,offs=13))
                        // I0Etapq(I0Ecst(gseq_strmize(372)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(2503(line=122,offs=1)--2515(line=122,offs=13))));$list(T2JAG($list(T2Pvar(xs[6116]))),T2JAG($list(T2Pvar(x0[6117])))))
                        // T1IMPallx(gseq_strmize(372);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6711(line=443,offs=1)--6775(line=445,offs=46)))
                        // T1IMPallx(gseq_strmize(372)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7407],T2Pcst(term)),@(x0[7407],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_strmize(372);$list(@(xs[1109],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7407])))),@(x0[1110],T2Pvar(x0[7407])))))))
                        let jsxtnm1604
                        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6759(line=445,offs=30)--6771(line=445,offs=42))
                        // I0Etapq(I0Ecst(list_strmize(1202)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(1677(line=61,offs=1)--1689(line=61,offs=13))));$list(T2JAG($list(T2Pvar(x0[7407])))))
                        // T1IMPallx(list_strmize(1202);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6452(line=418,offs=1)--6671(line=441,offs=2)))
                        // T1IMPallx(list_strmize(1202)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7406],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_strmize(1202);$list(@(a[3366],T2Pvar(x0[7406])))))))
                        let jsxtnm1603 = function (arg1) { // timp: list_strmize(1202)
                          let jsxtnm1592 = arg1
                          // I1CMP:start
                          let jsxtnm1602 // let
                          { // let
                            // I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6526(line=427,offs=1)--6666(line=439,offs=2)))
                            // I1FUNDCL
                            function auxmain_6529(arg1)
                            { // fun
                              let jsxtnm1593 = arg1
                              // I1CMP:start
                              let jsxtnm1600 = XATS000_l1azy(function (tlaz) { // l1azy
                                // I1CMP:start
                                let jsxtnm1599 // cas
                                do {
                                  // { // cls
                                  // I1GPTpat(I1BNDcons(I1TNM(1594);I0Pdapp(I0Pcon(list_nil(8));$list());$list()))
                                  if (XATS000_ctgeq(jsxtnm1593, XATSCTAG("list_nil",0))) { // gpt
                                    let jsxtnm1594 = jsxtnm1593
                                    let jsxtnm1595 = XATSCAPP("strmcon_vt_nil", [0])
                                    jsxtnm1599 = jsxtnm1595
                                    break // cls
                                  } // gpt
                                  // } // cls
                                  // { // cls
                                  // I1GPTpat(I1BNDcons(I1TNM(1596);I0Pdapp(I0Pcon(list_cons(9));$list(I0Pvar(x0(2601)),I0Pvar(xs(2602))));$list(@(x0(2601),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(1596));0)),@(xs(2602),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(1596));1)))))
                                  if (XATS000_ctgeq(jsxtnm1593, XATSCTAG("list_cons",1))) { // gpt
                                    let jsxtnm1596 = jsxtnm1593
                                    let jsxtnm1597 = XATSDAPP(auxmain_6529(XATSP1CN("list_cons", jsxtnm1596[1+1])))
                                    let jsxtnm1598 = XATSCAPP("strmcon_vt_cons", [1, XATSP1CN("list_cons", jsxtnm1596[0+1]), jsxtnm1597])
                                    jsxtnm1599 = jsxtnm1598
                                    break // cls
                                  } // gpt
                                  // } // cls
                                  XATS000_cfail()
                                } while (false) // end-of(do)
                                // I1CMP:return:jsxtnm1599
                                return jsxtnm1599
                              }) // endfun(l1azy)
                              // I1CMP:return:jsxtnm1600
                              return jsxtnm1600
                            } // endfun(auxmain_6529)
                            let jsxtnm1601 = XATSDAPP(auxmain_6529(jsxtnm1592))
                            jsxtnm1602 = jsxtnm1601
                          } // endlet
                          // I1CMP:return:jsxtnm1602
                          return jsxtnm1602
                        } // endtimp(list_strmize(1202))
                        jsxtnm1604 = jsxtnm1603
                        let jsxtnm1605 = XATSDAPP(jsxtnm1604(jsxtnm1573))
                        let jsxtnm1606 = XATSDAPP(jsxtnm1591(jsxtnm1605))
                        jsxtnm1607 = jsxtnm1606
                      } // endlet
                      // I1CMP:return:jsxtnm1607
                      return jsxtnm1607
                    } // endtimp(gseq_map_lstrm(426))
                    let jsxtnm1609 = XATSDAPP(jsxtnm1608(jsxtnm1535))
                    let jsxtnm1610 = XATSDAPP(jsxtnm1572(jsxtnm1609))
                    // I1CMP:return:jsxtnm1610
                    return jsxtnm1610
                  } // endtimp(gseq_map_llist(425))
                  let jsxtnm1612 = XATSDAPP(jsxtnm1611(jsxtnm1531))
                  jsxtnm1613 = jsxtnm1612
                } // endlet
                // I1CMP:return:jsxtnm1613
                return jsxtnm1613
              } // endtimp(gseq_map$f1un_llist(429))
              let jsxtnm1615 = XATSDAPP(jsxtnm1614(jsxtnm1529, jsxtnm1530))
              let jsxtnm1616 = XATSCAST("list_vt2t_17651", [jsxtnm1615])
              // I1CMP:return:jsxtnm1616
              return jsxtnm1616
            } // endtimp(gseq_map$f1un_list(428))
            jsxtnm1618 = jsxtnm1617
            let jsxtnm1619 = XATSDAPP(jsxtnm1618(jsxtnm1528, jsxtnm1527))
            // I1CMP:return:jsxtnm1619
            return jsxtnm1619
          } // endfun(lam0)
          // I1CMP:return:jsxtnm1620
          return jsxtnm1620
        } // endtimp(f1un_map$list(316))
        let jsxtnm1622 = XATSDAPP(jsxtnm1621(subst_4170))
        let jsxtnm1623 = XATSDAPP(jsxtnm1622(XATSP1CN("TMopr", jsxtnm1526[1+1])))
        let jsxtnm1624 = XATSCAPP("TMopr", [5, XATSP1CN("TMopr", jsxtnm1526[0+1]), jsxtnm1623])
        jsxtnm1709 = jsxtnm1624
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1625);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5292)),I0Pvar(tm2(5293)),I0Pvar(tm3(5294))));$list(@(tm1(5292),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1625));0)),@(tm2(5293),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1625));1)),@(tm3(5294),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1625));2)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMif0",6))) { // gpt
        let jsxtnm1625 = jsxtnm1465
        let jsxtnm1626 = XATSDAPP(subst_4170(XATSP1CN("TMif0", jsxtnm1625[0+1])))
        let jsxtnm1627 = XATSDAPP(subst_4170(XATSP1CN("TMif0", jsxtnm1625[1+1])))
        let jsxtnm1628 = XATSDAPP(subst_4170(XATSP1CN("TMif0", jsxtnm1625[2+1])))
        let jsxtnm1629 = XATSCAPP("TMif0", [6, jsxtnm1626, jsxtnm1627, jsxtnm1628])
        jsxtnm1709 = jsxtnm1629
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1630);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5295)),I0Pvar(x01(5296)),I0Pvar(tmx(5297))));$list(@(f00(5295),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1630));0)),@(x01(5296),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1630));1)),@(tmx(5297),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1630));2)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMfix",7))) { // gpt
        let jsxtnm1630 = jsxtnm1465
        // LCSRCsome1(lambda1.dats)@(4622(line=319,offs=6)--4623(line=319,offs=7))
        // I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
        // T1IMPallx(strn_eq(1024);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
        // T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
        let jsxtnm1651
        // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
        // I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        // T1IMPallx(g_eq(226);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
        // T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5857],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[776],T2Pvar(x0[5857])))))))
        let jsxtnm1650 = function (arg1, arg2) { // timp: g_eq(226)
          let jsxtnm1631 = arg1
          let jsxtnm1632 = arg2
          // I1CMP:start
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
          // I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
          // T1IMPallx(sint_eq$sint(920);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
          // T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
          let jsxtnm1639 = function (arg1, arg2) { // timp: sint_eq$sint(920)
            let jsxtnm1633 = arg1
            let jsxtnm1634 = arg2
            // I1CMP:start
            let jsxtnm1638 // let
            { // let
              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2038(line=93,offs=1)--2101(line=95,offs=39))
              // I1FUNDCL
              // XATS2JS_sint_eq$sint_2041
                // FJARGdarg($list(I1BNDcons(I1TNM(1635);I0Pvar(i1(4913));$list(@(i1(4913),I1Vtnm(I1TNM(1635))))),I1BNDcons(I1TNM(1636);I0Pvar(i2(4914));$list(@(i2(4914),I1Vtnm(I1TNM(1636)))))))
                // I1CMP:start
                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_eq$sint);G1Nlist($list())) // I1CMP:return
              let jsxtnm1637 = XATSDAPP(XATS2JS_sint_eq$sint(jsxtnm1633, jsxtnm1634))
              jsxtnm1638 = jsxtnm1637
            } // endlet
            // I1CMP:return:jsxtnm1638
            return jsxtnm1638
          } // endtimp(sint_eq$sint(920))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
          // I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5857])))))
          // T1IMPallx(g_cmp(230);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
          // T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[780],T2Pcst(strn)))))))
          let jsxtnm1647
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
          // I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
          // T1IMPallx(strn_cmp(1028);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1859(line=79,offs=1)--2008(line=91,offs=2)))
          // T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
          let jsxtnm1646 = function (arg1, arg2) { // timp: strn_cmp(1028)
            let jsxtnm1640 = arg1
            let jsxtnm1641 = arg2
            // I1CMP:start
            let jsxtnm1645 // let
            { // let
              // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1939(line=87,offs=1)--2006(line=90,offs=39)))
              // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1947(line=88,offs=1)--2006(line=90,offs=39))
              // I1FUNDCL
              // XATS2JS_strn_cmp_1950
                // FJARGdarg($list(I1BNDcons(I1TNM(1642);I0Pvar(x1(5089));$list(@(x1(5089),I1Vtnm(I1TNM(1642))))),I1BNDcons(I1TNM(1643);I0Pvar(x2(5090));$list(@(x2(5090),I1Vtnm(I1TNM(1643)))))))
                // I1CMP:start
                // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_cmp);G1Nlist($list())) // I1CMP:return
              let jsxtnm1644 = XATSDAPP(XATS2JS_strn_cmp(jsxtnm1640, jsxtnm1641))
              jsxtnm1645 = jsxtnm1644
            } // endlet
            // I1CMP:return:jsxtnm1645
            return jsxtnm1645
          } // endtimp(strn_cmp(1028))
          jsxtnm1647 = jsxtnm1646
          let jsxtnm1648 = XATSDAPP(jsxtnm1647(jsxtnm1631, jsxtnm1632))
          let jsxtnm1649 = XATSDAPP(jsxtnm1639(jsxtnm1648, XATSINT1(0)))
          // I1CMP:return:jsxtnm1649
          return jsxtnm1649
        } // endtimp(g_eq(226))
        jsxtnm1651 = jsxtnm1650
        let jsxtnm1652 = XATSDAPP(jsxtnm1651(jsxtnm1466, XATSP1CN("TMfix", jsxtnm1630[0+1])))
        let jsxtnm1678 // ift
        if (jsxtnm1652) // ift
        {
          jsxtnm1678 = jsxtnm1465
        } else {
          // LCSRCsome1(lambda1.dats)@(4651(line=322,offs=6)--4652(line=322,offs=7))
          // I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
          // T1IMPallx(strn_eq(1024);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
          // T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
          let jsxtnm1673
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
          // I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
          // T1IMPallx(g_eq(226);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
          // T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5857],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[776],T2Pvar(x0[5857])))))))
          let jsxtnm1672 = function (arg1, arg2) { // timp: g_eq(226)
            let jsxtnm1653 = arg1
            let jsxtnm1654 = arg2
            // I1CMP:start
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
            // I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
            // T1IMPallx(sint_eq$sint(920);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
            // T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
            let jsxtnm1661 = function (arg1, arg2) { // timp: sint_eq$sint(920)
              let jsxtnm1655 = arg1
              let jsxtnm1656 = arg2
              // I1CMP:start
              let jsxtnm1660 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2038(line=93,offs=1)--2101(line=95,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_eq$sint_2041
                  // FJARGdarg($list(I1BNDcons(I1TNM(1657);I0Pvar(i1(4913));$list(@(i1(4913),I1Vtnm(I1TNM(1657))))),I1BNDcons(I1TNM(1658);I0Pvar(i2(4914));$list(@(i2(4914),I1Vtnm(I1TNM(1658)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_eq$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1659 = XATSDAPP(XATS2JS_sint_eq$sint(jsxtnm1655, jsxtnm1656))
                jsxtnm1660 = jsxtnm1659
              } // endlet
              // I1CMP:return:jsxtnm1660
              return jsxtnm1660
            } // endtimp(sint_eq$sint(920))
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
            // I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5857])))))
            // T1IMPallx(g_cmp(230);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
            // T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[780],T2Pcst(strn)))))))
            let jsxtnm1669
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
            // I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
            // T1IMPallx(strn_cmp(1028);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1859(line=79,offs=1)--2008(line=91,offs=2)))
            // T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
            let jsxtnm1668 = function (arg1, arg2) { // timp: strn_cmp(1028)
              let jsxtnm1662 = arg1
              let jsxtnm1663 = arg2
              // I1CMP:start
              let jsxtnm1667 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1939(line=87,offs=1)--2006(line=90,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1947(line=88,offs=1)--2006(line=90,offs=39))
                // I1FUNDCL
                // XATS2JS_strn_cmp_1950
                  // FJARGdarg($list(I1BNDcons(I1TNM(1664);I0Pvar(x1(5089));$list(@(x1(5089),I1Vtnm(I1TNM(1664))))),I1BNDcons(I1TNM(1665);I0Pvar(x2(5090));$list(@(x2(5090),I1Vtnm(I1TNM(1665)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_cmp);G1Nlist($list())) // I1CMP:return
                let jsxtnm1666 = XATSDAPP(XATS2JS_strn_cmp(jsxtnm1662, jsxtnm1663))
                jsxtnm1667 = jsxtnm1666
              } // endlet
              // I1CMP:return:jsxtnm1667
              return jsxtnm1667
            } // endtimp(strn_cmp(1028))
            jsxtnm1669 = jsxtnm1668
            let jsxtnm1670 = XATSDAPP(jsxtnm1669(jsxtnm1653, jsxtnm1654))
            let jsxtnm1671 = XATSDAPP(jsxtnm1661(jsxtnm1670, XATSINT1(0)))
            // I1CMP:return:jsxtnm1671
            return jsxtnm1671
          } // endtimp(g_eq(226))
          jsxtnm1673 = jsxtnm1672
          let jsxtnm1674 = XATSDAPP(jsxtnm1673(jsxtnm1466, XATSP1CN("TMfix", jsxtnm1630[1+1])))
          let jsxtnm1677 // ift
          if (jsxtnm1674) // ift
          {
            jsxtnm1677 = jsxtnm1465
          } else {
            let jsxtnm1675 = XATSDAPP(subst_4170(XATSP1CN("TMfix", jsxtnm1630[2+1])))
            let jsxtnm1676 = XATSCAPP("TMfix", [7, XATSP1CN("TMfix", jsxtnm1630[0+1]), XATSP1CN("TMfix", jsxtnm1630[1+1]), jsxtnm1675])
            jsxtnm1677 = jsxtnm1676
          } // end(if)
          jsxtnm1678 = jsxtnm1677
        } // end(if)
        jsxtnm1709 = jsxtnm1678
        break // cls
      } // gpt
      // } // cls
      // { // cls
      // I1GPTpat(I1BNDcons(I1TNM(1679);I0Pdapp(I0Pcon(TMlet(40));$list(I0Pvar(x01(5298)),I0Pvar(tm1(5299)),I0Pvar(tm2(5300))));$list(@(x01(5298),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(1679));0)),@(tm1(5299),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(1679));1)),@(tm2(5300),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(1679));2)))))
      if (XATS000_ctgeq(jsxtnm1465, XATSCTAG("TMlet",8))) { // gpt
        let jsxtnm1679 = jsxtnm1465
        let jsxtnm1708 // let
        { // let
          // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(4761(line=329,offs=1)--4781(line=329,offs=21)))
          // I1VALDCL
          let jsxtnm1681
          let jsxtnm1680 = XATSDAPP(subst_4170(XATSP1CN("TMlet", jsxtnm1679[1+1])))
          jsxtnm1681 = jsxtnm1680
          XATS000_patck(true)
          // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(4782(line=330,offs=1)--4831(line=331,offs=40)))
          // I1VALDCL
          let jsxtnm1706
          // LCSRCsome1(lambda1.dats)@(4800(line=331,offs=9)--4801(line=331,offs=10))
          // I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
          // T1IMPallx(strn_eq(1024);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
          // T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
          let jsxtnm1702
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
          // I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
          // T1IMPallx(g_eq(226);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
          // T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5857],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[776],T2Pvar(x0[5857])))))))
          let jsxtnm1701 = function (arg1, arg2) { // timp: g_eq(226)
            let jsxtnm1682 = arg1
            let jsxtnm1683 = arg2
            // I1CMP:start
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
            // I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
            // T1IMPallx(sint_eq$sint(920);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
            // T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
            let jsxtnm1690 = function (arg1, arg2) { // timp: sint_eq$sint(920)
              let jsxtnm1684 = arg1
              let jsxtnm1685 = arg2
              // I1CMP:start
              let jsxtnm1689 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2038(line=93,offs=1)--2101(line=95,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_eq$sint_2041
                  // FJARGdarg($list(I1BNDcons(I1TNM(1686);I0Pvar(i1(4913));$list(@(i1(4913),I1Vtnm(I1TNM(1686))))),I1BNDcons(I1TNM(1687);I0Pvar(i2(4914));$list(@(i2(4914),I1Vtnm(I1TNM(1687)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_eq$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1688 = XATSDAPP(XATS2JS_sint_eq$sint(jsxtnm1684, jsxtnm1685))
                jsxtnm1689 = jsxtnm1688
              } // endlet
              // I1CMP:return:jsxtnm1689
              return jsxtnm1689
            } // endtimp(sint_eq$sint(920))
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
            // I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5857])))))
            // T1IMPallx(g_cmp(230);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
            // T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[780],T2Pcst(strn)))))))
            let jsxtnm1698
            // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
            // I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
            // T1IMPallx(strn_cmp(1028);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1859(line=79,offs=1)--2008(line=91,offs=2)))
            // T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
            let jsxtnm1697 = function (arg1, arg2) { // timp: strn_cmp(1028)
              let jsxtnm1691 = arg1
              let jsxtnm1692 = arg2
              // I1CMP:start
              let jsxtnm1696 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1939(line=87,offs=1)--2006(line=90,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(1947(line=88,offs=1)--2006(line=90,offs=39))
                // I1FUNDCL
                // XATS2JS_strn_cmp_1950
                  // FJARGdarg($list(I1BNDcons(I1TNM(1693);I0Pvar(x1(5089));$list(@(x1(5089),I1Vtnm(I1TNM(1693))))),I1BNDcons(I1TNM(1694);I0Pvar(x2(5090));$list(@(x2(5090),I1Vtnm(I1TNM(1694)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_cmp);G1Nlist($list())) // I1CMP:return
                let jsxtnm1695 = XATSDAPP(XATS2JS_strn_cmp(jsxtnm1691, jsxtnm1692))
                jsxtnm1696 = jsxtnm1695
              } // endlet
              // I1CMP:return:jsxtnm1696
              return jsxtnm1696
            } // endtimp(strn_cmp(1028))
            jsxtnm1698 = jsxtnm1697
            let jsxtnm1699 = XATSDAPP(jsxtnm1698(jsxtnm1682, jsxtnm1683))
            let jsxtnm1700 = XATSDAPP(jsxtnm1690(jsxtnm1699, XATSINT1(0)))
            // I1CMP:return:jsxtnm1700
            return jsxtnm1700
          } // endtimp(g_eq(226))
          jsxtnm1702 = jsxtnm1701
          let jsxtnm1703 = XATSDAPP(jsxtnm1702(jsxtnm1466, XATSP1CN("TMlet", jsxtnm1679[0+1])))
          let jsxtnm1705 // ift
          if (jsxtnm1703) // ift
          {
            jsxtnm1705 = XATSP1CN("TMlet", jsxtnm1679[2+1])
          } else {
            let jsxtnm1704 = XATSDAPP(subst_4170(XATSP1CN("TMlet", jsxtnm1679[2+1])))
            jsxtnm1705 = jsxtnm1704
          } // end(if)
          jsxtnm1706 = jsxtnm1705
          XATS000_patck(true)
          let jsxtnm1707 = XATSCAPP("TMlet", [8, XATSP1CN("TMlet", jsxtnm1679[0+1]), jsxtnm1681, jsxtnm1706])
          jsxtnm1708 = jsxtnm1707
        } // endlet
        jsxtnm1709 = jsxtnm1708
        break // cls
      } // gpt
      // } // cls
      XATS000_cfail()
    } while (false) // end-of(do)
    jsxtnm1710 = jsxtnm1709
  } // endlet
  // I1CMP:return:jsxtnm1710
  return jsxtnm1710
} // endfun(impl)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(4926(line=338,offs=1)--7455(line=495,offs=2)))
// I1FUNDCL
function term_interp_4929(arg1)
{ // fun
  let jsxtnm1711 = arg1
  // I1CMP:start
  let jsxtnm1927 // cas
  do {
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1712);I0Pdap1(I0Pcon(TMint(32)));$list()))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMint",0))) { // gpt
      let jsxtnm1712 = jsxtnm1711
      jsxtnm1927 = jsxtnm1711
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1713);I0Pdap1(I0Pcon(TMbtf(33)));$list()))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMbtf",1))) { // gpt
      let jsxtnm1713 = jsxtnm1711
      jsxtnm1927 = jsxtnm1711
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1714);I0Pdap1(I0Pcon(TMvar(34)));$list()))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMvar",2))) { // gpt
      let jsxtnm1714 = jsxtnm1711
      jsxtnm1927 = jsxtnm1711
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1715);I0Pdap1(I0Pcon(TMlam(35)));$list()))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMlam",3))) { // gpt
      let jsxtnm1715 = jsxtnm1711
      jsxtnm1927 = jsxtnm1711
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1716);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5305)),I0Pvar(tm2(5306))));$list(@(tm1(5305),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1716));0)),@(tm2(5306),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1716));1)))))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMapp",4))) { // gpt
      let jsxtnm1716 = jsxtnm1711
      let jsxtnm1726 // let
      { // let
        // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5095(line=355,offs=1)--5121(line=356,offs=23)))
        // I1VALDCL
        let jsxtnm1718
        let jsxtnm1717 = XATSDAPP(term_interp_4929(XATSP1CN("TMapp", jsxtnm1716[0+1])))
        jsxtnm1718 = jsxtnm1717
        XATS000_patck(true)
        let jsxtnm1725 // cas
        do {
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(1719);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5308)),I0Pvar(tmx(5309))));$list(@(x01(5308),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1719));0)),@(tmx(5309),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1719));1)))))
          if (XATS000_ctgeq(jsxtnm1718, XATSCTAG("TMlam",3))) { // gpt
            let jsxtnm1719 = jsxtnm1718
            let jsxtnm1720 = XATSDAPP(term_subst_4065(XATSP1CN("TMlam", jsxtnm1719[1+1]), XATSP1CN("TMlam", jsxtnm1719[0+1]), XATSP1CN("TMapp", jsxtnm1716[1+1])))
            let jsxtnm1721 = XATSDAPP(term_interp_4929(jsxtnm1720))
            jsxtnm1725 = jsxtnm1721
            break // cls
          } // gpt
          // } // cls
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(1722);I0Pany();$list()))
          if (true) { // gpt
            let jsxtnm1722 = jsxtnm1718
            let jsxtnm1723 = XATSDAPP(term_interp_4929(XATSP1CN("TMapp", jsxtnm1716[1+1])))
            let jsxtnm1724 = XATSCAPP("TMapp", [4, jsxtnm1718, jsxtnm1723])
            jsxtnm1725 = jsxtnm1724
            break // cls
          } // gpt
          // } // cls
          XATS000_cfail()
        } while (false) // end-of(do)
        jsxtnm1726 = jsxtnm1725
      } // endlet
      jsxtnm1927 = jsxtnm1726
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1727);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(pnm(5310)),I0Pvar(tms(5311))));$list(@(pnm(5310),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1727));0)),@(tms(5311),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1727));1)))))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMopr",5))) { // gpt
      let jsxtnm1727 = jsxtnm1711
      let jsxtnm1915 // cas
      do {
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1728);I0Pstr(T_STRN1_clsd("+";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("+"))) { // gpt
          let jsxtnm1728 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1744 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5408(line=381,offs=1)--5437(line=381,offs=30)))
            // I1VALDCL
            let jsxtnm1729
            jsxtnm1729 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5438(line=382,offs=1)--5467(line=382,offs=30)))
            // I1VALDCL
            let jsxtnm1730
            jsxtnm1730 = XATSP1CN("list_cons", jsxtnm1729[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1729[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5468(line=383,offs=1)--5501(line=383,offs=34)))
            // I1VALDCL
            let jsxtnm1732
            let jsxtnm1731 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1729[0+1])))
            jsxtnm1732 = jsxtnm1731
            XATS000_patck(XATS000_ctgeq(jsxtnm1731, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5502(line=384,offs=1)--5535(line=384,offs=34)))
            // I1VALDCL
            let jsxtnm1734
            let jsxtnm1733 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1730[0+1])))
            jsxtnm1734 = jsxtnm1733
            XATS000_patck(XATS000_ctgeq(jsxtnm1733, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(5393(line=379,offs=10)--5394(line=379,offs=11))
            // I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_add$sint(925);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
            // T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
            let jsxtnm1741 = function (arg1, arg2) { // timp: sint_add$sint(925)
              let jsxtnm1735 = arg1
              let jsxtnm1736 = arg2
              // I1CMP:start
              let jsxtnm1740 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2775(line=154,offs=1)--2839(line=156,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_add$sint_2778
                  // FJARGdarg($list(I1BNDcons(I1TNM(1737);I0Pvar(i1(4933));$list(@(i1(4933),I1Vtnm(I1TNM(1737))))),I1BNDcons(I1TNM(1738);I0Pvar(i2(4934));$list(@(i2(4934),I1Vtnm(I1TNM(1738)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_add$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1739 = XATSDAPP(XATS2JS_sint_add$sint(jsxtnm1735, jsxtnm1736))
                jsxtnm1740 = jsxtnm1739
              } // endlet
              // I1CMP:return:jsxtnm1740
              return jsxtnm1740
            } // endtimp(sint_add$sint(925))
            let jsxtnm1742 = XATSDAPP(jsxtnm1741(XATSP1CN("TMint", jsxtnm1732[0+1]), XATSP1CN("TMint", jsxtnm1734[0+1])))
            let jsxtnm1743 = XATSCAPP("TMint", [0, jsxtnm1742])
            jsxtnm1744 = jsxtnm1743
          } // endlet
          jsxtnm1915 = jsxtnm1744
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1745);I0Pstr(T_STRN1_clsd("-";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("-"))) { // gpt
          let jsxtnm1745 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1761 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5572(line=390,offs=1)--5601(line=390,offs=30)))
            // I1VALDCL
            let jsxtnm1746
            jsxtnm1746 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5602(line=391,offs=1)--5631(line=391,offs=30)))
            // I1VALDCL
            let jsxtnm1747
            jsxtnm1747 = XATSP1CN("list_cons", jsxtnm1746[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1746[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5632(line=392,offs=1)--5665(line=392,offs=34)))
            // I1VALDCL
            let jsxtnm1749
            let jsxtnm1748 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1746[0+1])))
            jsxtnm1749 = jsxtnm1748
            XATS000_patck(XATS000_ctgeq(jsxtnm1748, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5666(line=393,offs=1)--5699(line=393,offs=34)))
            // I1VALDCL
            let jsxtnm1751
            let jsxtnm1750 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1747[0+1])))
            jsxtnm1751 = jsxtnm1750
            XATS000_patck(XATS000_ctgeq(jsxtnm1750, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(5557(line=388,offs=10)--5558(line=388,offs=11))
            // I0Etapq(I0Ecst(sint_sub$sint(926)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2881(line=131,offs=1)--2894(line=131,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_sub$sint(926);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2845(line=159,offs=1)--3009(line=171,offs=2)))
            // T1IMPallx(sint_sub$sint(926)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_sub$sint(926);$list()))))
            let jsxtnm1758 = function (arg1, arg2) { // timp: sint_sub$sint(926)
              let jsxtnm1752 = arg1
              let jsxtnm1753 = arg2
              // I1CMP:start
              let jsxtnm1757 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2935(line=167,offs=1)--3007(line=170,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2943(line=168,offs=1)--3007(line=170,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_sub$sint_2946
                  // FJARGdarg($list(I1BNDcons(I1TNM(1754);I0Pvar(i1(4938));$list(@(i1(4938),I1Vtnm(I1TNM(1754))))),I1BNDcons(I1TNM(1755);I0Pvar(i2(4939));$list(@(i2(4939),I1Vtnm(I1TNM(1755)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_sub$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1756 = XATSDAPP(XATS2JS_sint_sub$sint(jsxtnm1752, jsxtnm1753))
                jsxtnm1757 = jsxtnm1756
              } // endlet
              // I1CMP:return:jsxtnm1757
              return jsxtnm1757
            } // endtimp(sint_sub$sint(926))
            let jsxtnm1759 = XATSDAPP(jsxtnm1758(XATSP1CN("TMint", jsxtnm1749[0+1]), XATSP1CN("TMint", jsxtnm1751[0+1])))
            let jsxtnm1760 = XATSCAPP("TMint", [0, jsxtnm1759])
            jsxtnm1761 = jsxtnm1760
          } // endlet
          jsxtnm1915 = jsxtnm1761
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1762);I0Pstr(T_STRN1_clsd("*";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("*"))) { // gpt
          let jsxtnm1762 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1778 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5736(line=399,offs=1)--5765(line=399,offs=30)))
            // I1VALDCL
            let jsxtnm1763
            jsxtnm1763 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5766(line=400,offs=1)--5795(line=400,offs=30)))
            // I1VALDCL
            let jsxtnm1764
            jsxtnm1764 = XATSP1CN("list_cons", jsxtnm1763[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1763[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5796(line=401,offs=1)--5829(line=401,offs=34)))
            // I1VALDCL
            let jsxtnm1766
            let jsxtnm1765 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1763[0+1])))
            jsxtnm1766 = jsxtnm1765
            XATS000_patck(XATS000_ctgeq(jsxtnm1765, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5830(line=402,offs=1)--5863(line=402,offs=34)))
            // I1VALDCL
            let jsxtnm1768
            let jsxtnm1767 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1764[0+1])))
            jsxtnm1768 = jsxtnm1767
            XATS000_patck(XATS000_ctgeq(jsxtnm1767, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(5721(line=397,offs=10)--5722(line=397,offs=11))
            // I0Etapq(I0Ecst(sint_mul$sint(927)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2946(line=135,offs=1)--2959(line=135,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_mul$sint(927);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3013(line=173,offs=1)--3177(line=185,offs=2)))
            // T1IMPallx(sint_mul$sint(927)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_mul$sint(927);$list()))))
            let jsxtnm1775 = function (arg1, arg2) { // timp: sint_mul$sint(927)
              let jsxtnm1769 = arg1
              let jsxtnm1770 = arg2
              // I1CMP:start
              let jsxtnm1774 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3103(line=181,offs=1)--3175(line=184,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3111(line=182,offs=1)--3175(line=184,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_mul$sint_3114
                  // FJARGdarg($list(I1BNDcons(I1TNM(1771);I0Pvar(i1(4943));$list(@(i1(4943),I1Vtnm(I1TNM(1771))))),I1BNDcons(I1TNM(1772);I0Pvar(i2(4944));$list(@(i2(4944),I1Vtnm(I1TNM(1772)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_mul$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1773 = XATSDAPP(XATS2JS_sint_mul$sint(jsxtnm1769, jsxtnm1770))
                jsxtnm1774 = jsxtnm1773
              } // endlet
              // I1CMP:return:jsxtnm1774
              return jsxtnm1774
            } // endtimp(sint_mul$sint(927))
            let jsxtnm1776 = XATSDAPP(jsxtnm1775(XATSP1CN("TMint", jsxtnm1766[0+1]), XATSP1CN("TMint", jsxtnm1768[0+1])))
            let jsxtnm1777 = XATSCAPP("TMint", [0, jsxtnm1776])
            jsxtnm1778 = jsxtnm1777
          } // endlet
          jsxtnm1915 = jsxtnm1778
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1779);I0Pstr(T_STRN1_clsd("/";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("/"))) { // gpt
          let jsxtnm1779 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1795 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5900(line=408,offs=1)--5929(line=408,offs=30)))
            // I1VALDCL
            let jsxtnm1780
            jsxtnm1780 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5930(line=409,offs=1)--5959(line=409,offs=30)))
            // I1VALDCL
            let jsxtnm1781
            jsxtnm1781 = XATSP1CN("list_cons", jsxtnm1780[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1780[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5960(line=410,offs=1)--5993(line=410,offs=34)))
            // I1VALDCL
            let jsxtnm1783
            let jsxtnm1782 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1780[0+1])))
            jsxtnm1783 = jsxtnm1782
            XATS000_patck(XATS000_ctgeq(jsxtnm1782, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5994(line=411,offs=1)--6027(line=411,offs=34)))
            // I1VALDCL
            let jsxtnm1785
            let jsxtnm1784 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1781[0+1])))
            jsxtnm1785 = jsxtnm1784
            XATS000_patck(XATS000_ctgeq(jsxtnm1784, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(5885(line=406,offs=10)--5886(line=406,offs=11))
            // I0Etapq(I0Ecst(sint_div$sint(928)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(3011(line=139,offs=1)--3024(line=139,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_div$sint(928);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3181(line=187,offs=1)--3345(line=199,offs=2)))
            // T1IMPallx(sint_div$sint(928)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_div$sint(928);$list()))))
            let jsxtnm1792 = function (arg1, arg2) { // timp: sint_div$sint(928)
              let jsxtnm1786 = arg1
              let jsxtnm1787 = arg2
              // I1CMP:start
              let jsxtnm1791 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3271(line=195,offs=1)--3343(line=198,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3279(line=196,offs=1)--3343(line=198,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_div$sint_3282
                  // FJARGdarg($list(I1BNDcons(I1TNM(1788);I0Pvar(i1(4948));$list(@(i1(4948),I1Vtnm(I1TNM(1788))))),I1BNDcons(I1TNM(1789);I0Pvar(i2(4949));$list(@(i2(4949),I1Vtnm(I1TNM(1789)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_div$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1790 = XATSDAPP(XATS2JS_sint_div$sint(jsxtnm1786, jsxtnm1787))
                jsxtnm1791 = jsxtnm1790
              } // endlet
              // I1CMP:return:jsxtnm1791
              return jsxtnm1791
            } // endtimp(sint_div$sint(928))
            let jsxtnm1793 = XATSDAPP(jsxtnm1792(XATSP1CN("TMint", jsxtnm1783[0+1]), XATSP1CN("TMint", jsxtnm1785[0+1])))
            let jsxtnm1794 = XATSCAPP("TMint", [0, jsxtnm1793])
            jsxtnm1795 = jsxtnm1794
          } // endlet
          jsxtnm1915 = jsxtnm1795
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1796);I0Pstr(T_STRN1_clsd("%";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("%"))) { // gpt
          let jsxtnm1796 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1812 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6064(line=417,offs=1)--6093(line=417,offs=30)))
            // I1VALDCL
            let jsxtnm1797
            jsxtnm1797 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6094(line=418,offs=1)--6123(line=418,offs=30)))
            // I1VALDCL
            let jsxtnm1798
            jsxtnm1798 = XATSP1CN("list_cons", jsxtnm1797[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1797[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6124(line=419,offs=1)--6157(line=419,offs=34)))
            // I1VALDCL
            let jsxtnm1800
            let jsxtnm1799 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1797[0+1])))
            jsxtnm1800 = jsxtnm1799
            XATS000_patck(XATS000_ctgeq(jsxtnm1799, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6158(line=420,offs=1)--6191(line=420,offs=34)))
            // I1VALDCL
            let jsxtnm1802
            let jsxtnm1801 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1798[0+1])))
            jsxtnm1802 = jsxtnm1801
            XATS000_patck(XATS000_ctgeq(jsxtnm1801, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(6049(line=415,offs=10)--6050(line=415,offs=11))
            // I0Etapq(I0Ecst(sint_mod$sint(929)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(3076(line=143,offs=1)--3089(line=143,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_mod$sint(929);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3349(line=201,offs=1)--3513(line=213,offs=2)))
            // T1IMPallx(sint_mod$sint(929)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_mod$sint(929);$list()))))
            let jsxtnm1809 = function (arg1, arg2) { // timp: sint_mod$sint(929)
              let jsxtnm1803 = arg1
              let jsxtnm1804 = arg2
              // I1CMP:start
              let jsxtnm1808 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3439(line=209,offs=1)--3511(line=212,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(3447(line=210,offs=1)--3511(line=212,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_mod$sint_3450
                  // FJARGdarg($list(I1BNDcons(I1TNM(1805);I0Pvar(i1(4953));$list(@(i1(4953),I1Vtnm(I1TNM(1805))))),I1BNDcons(I1TNM(1806);I0Pvar(i2(4954));$list(@(i2(4954),I1Vtnm(I1TNM(1806)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_mod$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1807 = XATSDAPP(XATS2JS_sint_mod$sint(jsxtnm1803, jsxtnm1804))
                jsxtnm1808 = jsxtnm1807
              } // endlet
              // I1CMP:return:jsxtnm1808
              return jsxtnm1808
            } // endtimp(sint_mod$sint(929))
            let jsxtnm1810 = XATSDAPP(jsxtnm1809(XATSP1CN("TMint", jsxtnm1800[0+1]), XATSP1CN("TMint", jsxtnm1802[0+1])))
            let jsxtnm1811 = XATSCAPP("TMint", [0, jsxtnm1810])
            jsxtnm1812 = jsxtnm1811
          } // endlet
          jsxtnm1915 = jsxtnm1812
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1813);I0Pstr(T_STRN1_clsd("<";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("<"))) { // gpt
          let jsxtnm1813 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1829 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6231(line=427,offs=1)--6260(line=427,offs=30)))
            // I1VALDCL
            let jsxtnm1814
            jsxtnm1814 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6261(line=428,offs=1)--6290(line=428,offs=30)))
            // I1VALDCL
            let jsxtnm1815
            jsxtnm1815 = XATSP1CN("list_cons", jsxtnm1814[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1814[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6291(line=429,offs=1)--6324(line=429,offs=34)))
            // I1VALDCL
            let jsxtnm1817
            let jsxtnm1816 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1814[0+1])))
            jsxtnm1817 = jsxtnm1816
            XATS000_patck(XATS000_ctgeq(jsxtnm1816, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6325(line=430,offs=1)--6358(line=430,offs=34)))
            // I1VALDCL
            let jsxtnm1819
            let jsxtnm1818 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1815[0+1])))
            jsxtnm1819 = jsxtnm1818
            XATS000_patck(XATS000_ctgeq(jsxtnm1818, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(6216(line=425,offs=10)--6217(line=425,offs=11))
            // I0Etapq(I0Ecst(sint_lt$sint(918)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2041(line=83,offs=1)--2053(line=83,offs=13))));$list(T2JAG($list())))
            // T1IMPallx(sint_lt$sint(918);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1612(line=56,offs=1)--1773(line=68,offs=2)))
            // T1IMPallx(sint_lt$sint(918)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_lt$sint(918);$list()))))
            let jsxtnm1826 = function (arg1, arg2) { // timp: sint_lt$sint(918)
              let jsxtnm1820 = arg1
              let jsxtnm1821 = arg2
              // I1CMP:start
              let jsxtnm1825 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1700(line=64,offs=1)--1771(line=67,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1708(line=65,offs=1)--1771(line=67,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_lt$sint_1711
                  // FJARGdarg($list(I1BNDcons(I1TNM(1822);I0Pvar(i1(4903));$list(@(i1(4903),I1Vtnm(I1TNM(1822))))),I1BNDcons(I1TNM(1823);I0Pvar(i2(4904));$list(@(i2(4904),I1Vtnm(I1TNM(1823)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_lt$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1824 = XATSDAPP(XATS2JS_sint_lt$sint(jsxtnm1820, jsxtnm1821))
                jsxtnm1825 = jsxtnm1824
              } // endlet
              // I1CMP:return:jsxtnm1825
              return jsxtnm1825
            } // endtimp(sint_lt$sint(918))
            let jsxtnm1827 = XATSDAPP(jsxtnm1826(XATSP1CN("TMint", jsxtnm1817[0+1]), XATSP1CN("TMint", jsxtnm1819[0+1])))
            let jsxtnm1828 = XATSCAPP("TMbtf", [1, jsxtnm1827])
            jsxtnm1829 = jsxtnm1828
          } // endlet
          jsxtnm1915 = jsxtnm1829
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1830);I0Pstr(T_STRN1_clsd(">";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN(">"))) { // gpt
          let jsxtnm1830 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1846 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6395(line=436,offs=1)--6424(line=436,offs=30)))
            // I1VALDCL
            let jsxtnm1831
            jsxtnm1831 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6425(line=437,offs=1)--6454(line=437,offs=30)))
            // I1VALDCL
            let jsxtnm1832
            jsxtnm1832 = XATSP1CN("list_cons", jsxtnm1831[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1831[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6455(line=438,offs=1)--6488(line=438,offs=34)))
            // I1VALDCL
            let jsxtnm1834
            let jsxtnm1833 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1831[0+1])))
            jsxtnm1834 = jsxtnm1833
            XATS000_patck(XATS000_ctgeq(jsxtnm1833, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6489(line=439,offs=1)--6522(line=439,offs=34)))
            // I1VALDCL
            let jsxtnm1836
            let jsxtnm1835 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1832[0+1])))
            jsxtnm1836 = jsxtnm1835
            XATS000_patck(XATS000_ctgeq(jsxtnm1835, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(6380(line=434,offs=10)--6381(line=434,offs=11))
            // I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
            // T1IMPallx(sint_gt$sint(919);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
            // T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
            let jsxtnm1843 = function (arg1, arg2) { // timp: sint_gt$sint(919)
              let jsxtnm1837 = arg1
              let jsxtnm1838 = arg2
              // I1CMP:start
              let jsxtnm1842 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1873(line=79,offs=1)--1936(line=81,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_gt$sint_1876
                  // FJARGdarg($list(I1BNDcons(I1TNM(1839);I0Pvar(i1(4908));$list(@(i1(4908),I1Vtnm(I1TNM(1839))))),I1BNDcons(I1TNM(1840);I0Pvar(i2(4909));$list(@(i2(4909),I1Vtnm(I1TNM(1840)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_gt$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1841 = XATSDAPP(XATS2JS_sint_gt$sint(jsxtnm1837, jsxtnm1838))
                jsxtnm1842 = jsxtnm1841
              } // endlet
              // I1CMP:return:jsxtnm1842
              return jsxtnm1842
            } // endtimp(sint_gt$sint(919))
            let jsxtnm1844 = XATSDAPP(jsxtnm1843(XATSP1CN("TMint", jsxtnm1834[0+1]), XATSP1CN("TMint", jsxtnm1836[0+1])))
            let jsxtnm1845 = XATSCAPP("TMbtf", [1, jsxtnm1844])
            jsxtnm1846 = jsxtnm1845
          } // endlet
          jsxtnm1915 = jsxtnm1846
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1847);I0Pstr(T_STRN1_clsd("=";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("="))) { // gpt
          let jsxtnm1847 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1863 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6559(line=445,offs=1)--6588(line=445,offs=30)))
            // I1VALDCL
            let jsxtnm1848
            jsxtnm1848 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6589(line=446,offs=1)--6618(line=446,offs=30)))
            // I1VALDCL
            let jsxtnm1849
            jsxtnm1849 = XATSP1CN("list_cons", jsxtnm1848[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1848[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6619(line=447,offs=1)--6652(line=447,offs=34)))
            // I1VALDCL
            let jsxtnm1851
            let jsxtnm1850 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1848[0+1])))
            jsxtnm1851 = jsxtnm1850
            XATS000_patck(XATS000_ctgeq(jsxtnm1850, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6653(line=448,offs=1)--6686(line=448,offs=34)))
            // I1VALDCL
            let jsxtnm1853
            let jsxtnm1852 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1849[0+1])))
            jsxtnm1853 = jsxtnm1852
            XATS000_patck(XATS000_ctgeq(jsxtnm1852, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(6544(line=443,offs=10)--6545(line=443,offs=11))
            // I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
            // T1IMPallx(sint_eq$sint(920);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
            // T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
            let jsxtnm1860 = function (arg1, arg2) { // timp: sint_eq$sint(920)
              let jsxtnm1854 = arg1
              let jsxtnm1855 = arg2
              // I1CMP:start
              let jsxtnm1859 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2038(line=93,offs=1)--2101(line=95,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_eq$sint_2041
                  // FJARGdarg($list(I1BNDcons(I1TNM(1856);I0Pvar(i1(4913));$list(@(i1(4913),I1Vtnm(I1TNM(1856))))),I1BNDcons(I1TNM(1857);I0Pvar(i2(4914));$list(@(i2(4914),I1Vtnm(I1TNM(1857)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_eq$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1858 = XATSDAPP(XATS2JS_sint_eq$sint(jsxtnm1854, jsxtnm1855))
                jsxtnm1859 = jsxtnm1858
              } // endlet
              // I1CMP:return:jsxtnm1859
              return jsxtnm1859
            } // endtimp(sint_eq$sint(920))
            let jsxtnm1861 = XATSDAPP(jsxtnm1860(XATSP1CN("TMint", jsxtnm1851[0+1]), XATSP1CN("TMint", jsxtnm1853[0+1])))
            let jsxtnm1862 = XATSCAPP("TMbtf", [1, jsxtnm1861])
            jsxtnm1863 = jsxtnm1862
          } // endlet
          jsxtnm1915 = jsxtnm1863
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1864);I0Pstr(T_STRN1_clsd("<=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("<="))) { // gpt
          let jsxtnm1864 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1880 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6725(line=454,offs=1)--6754(line=454,offs=30)))
            // I1VALDCL
            let jsxtnm1865
            jsxtnm1865 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6755(line=455,offs=1)--6784(line=455,offs=30)))
            // I1VALDCL
            let jsxtnm1866
            jsxtnm1866 = XATSP1CN("list_cons", jsxtnm1865[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1865[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6785(line=456,offs=1)--6818(line=456,offs=34)))
            // I1VALDCL
            let jsxtnm1868
            let jsxtnm1867 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1865[0+1])))
            jsxtnm1868 = jsxtnm1867
            XATS000_patck(XATS000_ctgeq(jsxtnm1867, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6819(line=457,offs=1)--6852(line=457,offs=34)))
            // I1VALDCL
            let jsxtnm1870
            let jsxtnm1869 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1866[0+1])))
            jsxtnm1870 = jsxtnm1869
            XATS000_patck(XATS000_ctgeq(jsxtnm1869, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(6709(line=452,offs=10)--6711(line=452,offs=12))
            // I0Etapq(I0Ecst(sint_lte$sint(921)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2344(line=100,offs=1)--2357(line=100,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_lte$sint(921);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2130(line=100,offs=1)--2294(line=112,offs=2)))
            // T1IMPallx(sint_lte$sint(921)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_lte$sint(921);$list()))))
            let jsxtnm1877 = function (arg1, arg2) { // timp: sint_lte$sint(921)
              let jsxtnm1871 = arg1
              let jsxtnm1872 = arg2
              // I1CMP:start
              let jsxtnm1876 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2220(line=108,offs=1)--2292(line=111,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2228(line=109,offs=1)--2292(line=111,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_lte$sint_2231
                  // FJARGdarg($list(I1BNDcons(I1TNM(1873);I0Pvar(i1(4918));$list(@(i1(4918),I1Vtnm(I1TNM(1873))))),I1BNDcons(I1TNM(1874);I0Pvar(i2(4919));$list(@(i2(4919),I1Vtnm(I1TNM(1874)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_lte$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1875 = XATSDAPP(XATS2JS_sint_lte$sint(jsxtnm1871, jsxtnm1872))
                jsxtnm1876 = jsxtnm1875
              } // endlet
              // I1CMP:return:jsxtnm1876
              return jsxtnm1876
            } // endtimp(sint_lte$sint(921))
            let jsxtnm1878 = XATSDAPP(jsxtnm1877(XATSP1CN("TMint", jsxtnm1868[0+1]), XATSP1CN("TMint", jsxtnm1870[0+1])))
            let jsxtnm1879 = XATSCAPP("TMbtf", [1, jsxtnm1878])
            jsxtnm1880 = jsxtnm1879
          } // endlet
          jsxtnm1915 = jsxtnm1880
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1881);I0Pstr(T_STRN1_clsd(">=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN(">="))) { // gpt
          let jsxtnm1881 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1897 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6891(line=463,offs=1)--6920(line=463,offs=30)))
            // I1VALDCL
            let jsxtnm1882
            jsxtnm1882 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6921(line=464,offs=1)--6950(line=464,offs=30)))
            // I1VALDCL
            let jsxtnm1883
            jsxtnm1883 = XATSP1CN("list_cons", jsxtnm1882[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1882[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6951(line=465,offs=1)--6984(line=465,offs=34)))
            // I1VALDCL
            let jsxtnm1885
            let jsxtnm1884 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1882[0+1])))
            jsxtnm1885 = jsxtnm1884
            XATS000_patck(XATS000_ctgeq(jsxtnm1884, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6985(line=466,offs=1)--7018(line=466,offs=34)))
            // I1VALDCL
            let jsxtnm1887
            let jsxtnm1886 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1883[0+1])))
            jsxtnm1887 = jsxtnm1886
            XATS000_patck(XATS000_ctgeq(jsxtnm1886, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(6875(line=461,offs=10)--6877(line=461,offs=12))
            // I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_gte$sint(922);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
            // T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
            let jsxtnm1894 = function (arg1, arg2) { // timp: sint_gte$sint(922)
              let jsxtnm1888 = arg1
              let jsxtnm1889 = arg2
              // I1CMP:start
              let jsxtnm1893 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2396(line=123,offs=1)--2460(line=125,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_gte$sint_2399
                  // FJARGdarg($list(I1BNDcons(I1TNM(1890);I0Pvar(i1(4923));$list(@(i1(4923),I1Vtnm(I1TNM(1890))))),I1BNDcons(I1TNM(1891);I0Pvar(i2(4924));$list(@(i2(4924),I1Vtnm(I1TNM(1891)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_gte$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1892 = XATSDAPP(XATS2JS_sint_gte$sint(jsxtnm1888, jsxtnm1889))
                jsxtnm1893 = jsxtnm1892
              } // endlet
              // I1CMP:return:jsxtnm1893
              return jsxtnm1893
            } // endtimp(sint_gte$sint(922))
            let jsxtnm1895 = XATSDAPP(jsxtnm1894(XATSP1CN("TMint", jsxtnm1885[0+1]), XATSP1CN("TMint", jsxtnm1887[0+1])))
            let jsxtnm1896 = XATSCAPP("TMbtf", [1, jsxtnm1895])
            jsxtnm1897 = jsxtnm1896
          } // endlet
          jsxtnm1915 = jsxtnm1897
          break // cls
        } // gpt
        // } // cls
        // { // cls
        // I1GPTpat(I1BNDcons(I1TNM(1898);I0Pstr(T_STRN1_clsd("!=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", jsxtnm1727[0+1]), XATSSTRN("!="))) { // gpt
          let jsxtnm1898 = XATSP1CN("TMopr", jsxtnm1727[0+1])
          let jsxtnm1914 // let
          { // let
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7057(line=472,offs=1)--7086(line=472,offs=30)))
            // I1VALDCL
            let jsxtnm1899
            jsxtnm1899 = XATSP1CN("TMopr", jsxtnm1727[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", jsxtnm1727[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7087(line=473,offs=1)--7116(line=473,offs=30)))
            // I1VALDCL
            let jsxtnm1900
            jsxtnm1900 = XATSP1CN("list_cons", jsxtnm1899[1+1])
            XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", jsxtnm1899[1+1]), XATSCTAG("list_cons",1)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7117(line=474,offs=1)--7150(line=474,offs=34)))
            // I1VALDCL
            let jsxtnm1902
            let jsxtnm1901 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1899[0+1])))
            jsxtnm1902 = jsxtnm1901
            XATS000_patck(XATS000_ctgeq(jsxtnm1901, XATSCTAG("TMint",0)))
            // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7151(line=475,offs=1)--7184(line=475,offs=34)))
            // I1VALDCL
            let jsxtnm1904
            let jsxtnm1903 = XATSDAPP(term_interp_4929(XATSP1CN("list_cons", jsxtnm1900[0+1])))
            jsxtnm1904 = jsxtnm1903
            XATS000_patck(XATS000_ctgeq(jsxtnm1903, XATSCTAG("TMint",0)))
            // LCSRCsome1(lambda1.dats)@(7041(line=470,offs=10)--7043(line=470,offs=12))
            // I0Etapq(I0Ecst(sint_neq$sint(923)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2472(line=108,offs=1)--2485(line=108,offs=14))));$list(T2JAG($list())))
            // T1IMPallx(sint_neq$sint(923);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2466(line=128,offs=1)--2630(line=140,offs=2)))
            // T1IMPallx(sint_neq$sint(923)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_neq$sint(923);$list()))))
            let jsxtnm1911 = function (arg1, arg2) { // timp: sint_neq$sint(923)
              let jsxtnm1905 = arg1
              let jsxtnm1906 = arg2
              // I1CMP:start
              let jsxtnm1910 // let
              { // let
                // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2556(line=136,offs=1)--2628(line=139,offs=39)))
                // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/gint000.dats)@(2564(line=137,offs=1)--2628(line=139,offs=39))
                // I1FUNDCL
                // XATS2JS_sint_neq$sint_2567
                  // FJARGdarg($list(I1BNDcons(I1TNM(1907);I0Pvar(i1(4928));$list(@(i1(4928),I1Vtnm(I1TNM(1907))))),I1BNDcons(I1TNM(1908);I0Pvar(i2(4929));$list(@(i2(4929),I1Vtnm(I1TNM(1908)))))))
                  // I1CMP:start
                  // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_sint_neq$sint);G1Nlist($list())) // I1CMP:return
                let jsxtnm1909 = XATSDAPP(XATS2JS_sint_neq$sint(jsxtnm1905, jsxtnm1906))
                jsxtnm1910 = jsxtnm1909
              } // endlet
              // I1CMP:return:jsxtnm1910
              return jsxtnm1910
            } // endtimp(sint_neq$sint(923))
            let jsxtnm1912 = XATSDAPP(jsxtnm1911(XATSP1CN("TMint", jsxtnm1902[0+1]), XATSP1CN("TMint", jsxtnm1904[0+1])))
            let jsxtnm1913 = XATSCAPP("TMbtf", [1, jsxtnm1912])
            jsxtnm1914 = jsxtnm1913
          } // endlet
          jsxtnm1915 = jsxtnm1914
          break // cls
        } // gpt
        // } // cls
        XATS000_cfail()
      } while (false) // end-of(do)
      jsxtnm1927 = jsxtnm1915
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1916);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5378)),I0Pvar(tm2(5379)),I0Pvar(tm3(5380))));$list(@(tm1(5378),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1916));0)),@(tm2(5379),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1916));1)),@(tm3(5380),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1916));2)))))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMif0",6))) { // gpt
      let jsxtnm1916 = jsxtnm1711
      let jsxtnm1923 // let
      { // let
        // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7255(line=483,offs=1)--7281(line=483,offs=27)))
        // I1VALDCL
        let jsxtnm1918
        let jsxtnm1917 = XATSDAPP(term_interp_4929(XATSP1CN("TMif0", jsxtnm1916[0+1])))
        jsxtnm1918 = jsxtnm1917
        XATS000_patck(true)
        let jsxtnm1922 // cas
        do {
          // { // cls
          // I1GPTpat(I1BNDcons(I1TNM(1919);I0Pdapp(I0Pcon(TMbtf(33));$list(I0Pvar(btf(5382))));$list(@(btf(5382),I1Vp1cn(I0Pcon(TMbtf(33));I1Vtnm(I1TNM(1919));0)))))
          if (XATS000_ctgeq(jsxtnm1918, XATSCTAG("TMbtf",1))) { // gpt
            let jsxtnm1919 = jsxtnm1918
            let jsxtnm1920 // ift
            if (XATSP1CN("TMbtf", jsxtnm1919[0+1])) // ift
            {
              jsxtnm1920 = XATSP1CN("TMif0", jsxtnm1916[1+1])
            } else {
              jsxtnm1920 = XATSP1CN("TMif0", jsxtnm1916[2+1])
            } // end(if)
            let jsxtnm1921 = XATSDAPP(term_interp_4929(jsxtnm1920))
            jsxtnm1922 = jsxtnm1921
            break // cls
          } // gpt
          // } // cls
          XATS000_cfail()
        } while (false) // end-of(do)
        jsxtnm1923 = jsxtnm1922
      } // endlet
      jsxtnm1927 = jsxtnm1923
      break // cls
    } // gpt
    // } // cls
    // { // cls
    // I1GPTpat(I1BNDcons(I1TNM(1924);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5383)),I0Pvar(x01(5384)),I0Pvar(tmx(5385))));$list(@(f00(5383),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1924));0)),@(x01(5384),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1924));1)),@(tmx(5385),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1924));2)))))
    if (XATS000_ctgeq(jsxtnm1711, XATSCTAG("TMfix",7))) { // gpt
      let jsxtnm1924 = jsxtnm1711
      let jsxtnm1925 = XATSDAPP(term_subst_4065(XATSP1CN("TMfix", jsxtnm1924[2+1]), XATSP1CN("TMfix", jsxtnm1924[0+1]), jsxtnm1711))
      let jsxtnm1926 = XATSCAPP("TMlam", [3, XATSP1CN("TMfix", jsxtnm1924[1+1]), jsxtnm1925])
      jsxtnm1927 = jsxtnm1926
      break // cls
    } // gpt
    // } // cls
    XATS000_cfail()
  } while (false) // end-of(do)
  // I1CMP:return:jsxtnm1927
  return jsxtnm1927
} // endfun(term_interp_4929)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7502(line=500,offs=1)--7563(line=503,offs=28)))
// I1FUNDCL
function TMlt_7505(arg1, arg2)
{ // fun
  let jsxtnm1928 = arg1
  let jsxtnm1929 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7547(line=503,offs=12)--7551(line=503,offs=16))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1943 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1930 = arg1
    // I1CMP:start
    let jsxtnm1942 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1932
      let jsxtnm1931 = XATSPFLT(jsxtnm1930[0])
      jsxtnm1932 = jsxtnm1931
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1934
      let jsxtnm1933 = XATSPFLT(jsxtnm1930[1])
      jsxtnm1934 = jsxtnm1933
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1940 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1935 = arg1
        let jsxtnm1936 = arg2
        // I1CMP:start
        let jsxtnm1937 = XATSCAPP("list_nil", [0])
        let jsxtnm1938 = XATSCAPP("list_cons", [1, jsxtnm1936, jsxtnm1937])
        let jsxtnm1939 = XATSCAPP("list_cons", [1, jsxtnm1935, jsxtnm1938])
        // I1CMP:return:jsxtnm1939
        return jsxtnm1939
      } // endtimp(list_make_2val(1171))
      let jsxtnm1941 = XATSDAPP(jsxtnm1940(jsxtnm1932, jsxtnm1934))
      jsxtnm1942 = jsxtnm1941
    } // endlet
    // I1CMP:return:jsxtnm1942
    return jsxtnm1942
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1944 = XATSTUP1(XATSTRCD(0), [jsxtnm1928, jsxtnm1929])
  let jsxtnm1945 = XATSDAPP(jsxtnm1943(jsxtnm1944))
  let jsxtnm1946 = XATSCAPP("TMopr", [5, XATSSTRN("<"), jsxtnm1945])
  // I1CMP:return:jsxtnm1946
  return jsxtnm1946
} // endfun(TMlt_7505)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7564(line=504,offs=1)--7625(line=507,offs=28)))
// I1FUNDCL
function TMgt_7567(arg1, arg2)
{ // fun
  let jsxtnm1947 = arg1
  let jsxtnm1948 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7609(line=507,offs=12)--7613(line=507,offs=16))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1962 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1949 = arg1
    // I1CMP:start
    let jsxtnm1961 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1951
      let jsxtnm1950 = XATSPFLT(jsxtnm1949[0])
      jsxtnm1951 = jsxtnm1950
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1953
      let jsxtnm1952 = XATSPFLT(jsxtnm1949[1])
      jsxtnm1953 = jsxtnm1952
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1959 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1954 = arg1
        let jsxtnm1955 = arg2
        // I1CMP:start
        let jsxtnm1956 = XATSCAPP("list_nil", [0])
        let jsxtnm1957 = XATSCAPP("list_cons", [1, jsxtnm1955, jsxtnm1956])
        let jsxtnm1958 = XATSCAPP("list_cons", [1, jsxtnm1954, jsxtnm1957])
        // I1CMP:return:jsxtnm1958
        return jsxtnm1958
      } // endtimp(list_make_2val(1171))
      let jsxtnm1960 = XATSDAPP(jsxtnm1959(jsxtnm1951, jsxtnm1953))
      jsxtnm1961 = jsxtnm1960
    } // endlet
    // I1CMP:return:jsxtnm1961
    return jsxtnm1961
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1963 = XATSTUP1(XATSTRCD(0), [jsxtnm1947, jsxtnm1948])
  let jsxtnm1964 = XATSDAPP(jsxtnm1962(jsxtnm1963))
  let jsxtnm1965 = XATSCAPP("TMopr", [5, XATSSTRN(">"), jsxtnm1964])
  // I1CMP:return:jsxtnm1965
  return jsxtnm1965
} // endfun(TMgt_7567)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7626(line=508,offs=1)--7687(line=511,offs=28)))
// I1FUNDCL
function TMeq_7629(arg1, arg2)
{ // fun
  let jsxtnm1966 = arg1
  let jsxtnm1967 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7671(line=511,offs=12)--7675(line=511,offs=16))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm1981 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1968 = arg1
    // I1CMP:start
    let jsxtnm1980 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1970
      let jsxtnm1969 = XATSPFLT(jsxtnm1968[0])
      jsxtnm1970 = jsxtnm1969
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1972
      let jsxtnm1971 = XATSPFLT(jsxtnm1968[1])
      jsxtnm1972 = jsxtnm1971
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1978 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1973 = arg1
        let jsxtnm1974 = arg2
        // I1CMP:start
        let jsxtnm1975 = XATSCAPP("list_nil", [0])
        let jsxtnm1976 = XATSCAPP("list_cons", [1, jsxtnm1974, jsxtnm1975])
        let jsxtnm1977 = XATSCAPP("list_cons", [1, jsxtnm1973, jsxtnm1976])
        // I1CMP:return:jsxtnm1977
        return jsxtnm1977
      } // endtimp(list_make_2val(1171))
      let jsxtnm1979 = XATSDAPP(jsxtnm1978(jsxtnm1970, jsxtnm1972))
      jsxtnm1980 = jsxtnm1979
    } // endlet
    // I1CMP:return:jsxtnm1980
    return jsxtnm1980
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm1982 = XATSTUP1(XATSTRCD(0), [jsxtnm1966, jsxtnm1967])
  let jsxtnm1983 = XATSDAPP(jsxtnm1981(jsxtnm1982))
  let jsxtnm1984 = XATSCAPP("TMopr", [5, XATSSTRN("="), jsxtnm1983])
  // I1CMP:return:jsxtnm1984
  return jsxtnm1984
} // endfun(TMeq_7629)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7691(line=513,offs=1)--7754(line=516,offs=29)))
// I1FUNDCL
function TMlte_7694(arg1, arg2)
{ // fun
  let jsxtnm1985 = arg1
  let jsxtnm1986 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7738(line=516,offs=13)--7742(line=516,offs=17))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm2000 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm1987 = arg1
    // I1CMP:start
    let jsxtnm1999 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm1989
      let jsxtnm1988 = XATSPFLT(jsxtnm1987[0])
      jsxtnm1989 = jsxtnm1988
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm1991
      let jsxtnm1990 = XATSPFLT(jsxtnm1987[1])
      jsxtnm1991 = jsxtnm1990
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm1997 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm1992 = arg1
        let jsxtnm1993 = arg2
        // I1CMP:start
        let jsxtnm1994 = XATSCAPP("list_nil", [0])
        let jsxtnm1995 = XATSCAPP("list_cons", [1, jsxtnm1993, jsxtnm1994])
        let jsxtnm1996 = XATSCAPP("list_cons", [1, jsxtnm1992, jsxtnm1995])
        // I1CMP:return:jsxtnm1996
        return jsxtnm1996
      } // endtimp(list_make_2val(1171))
      let jsxtnm1998 = XATSDAPP(jsxtnm1997(jsxtnm1989, jsxtnm1991))
      jsxtnm1999 = jsxtnm1998
    } // endlet
    // I1CMP:return:jsxtnm1999
    return jsxtnm1999
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm2001 = XATSTUP1(XATSTRCD(0), [jsxtnm1985, jsxtnm1986])
  let jsxtnm2002 = XATSDAPP(jsxtnm2000(jsxtnm2001))
  let jsxtnm2003 = XATSCAPP("TMopr", [5, XATSSTRN("<="), jsxtnm2002])
  // I1CMP:return:jsxtnm2003
  return jsxtnm2003
} // endfun(TMlte_7694)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7755(line=517,offs=1)--7818(line=520,offs=29)))
// I1FUNDCL
function TMgte_7758(arg1, arg2)
{ // fun
  let jsxtnm2004 = arg1
  let jsxtnm2005 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7802(line=520,offs=13)--7806(line=520,offs=17))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm2019 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm2006 = arg1
    // I1CMP:start
    let jsxtnm2018 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm2008
      let jsxtnm2007 = XATSPFLT(jsxtnm2006[0])
      jsxtnm2008 = jsxtnm2007
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm2010
      let jsxtnm2009 = XATSPFLT(jsxtnm2006[1])
      jsxtnm2010 = jsxtnm2009
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm2016 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm2011 = arg1
        let jsxtnm2012 = arg2
        // I1CMP:start
        let jsxtnm2013 = XATSCAPP("list_nil", [0])
        let jsxtnm2014 = XATSCAPP("list_cons", [1, jsxtnm2012, jsxtnm2013])
        let jsxtnm2015 = XATSCAPP("list_cons", [1, jsxtnm2011, jsxtnm2014])
        // I1CMP:return:jsxtnm2015
        return jsxtnm2015
      } // endtimp(list_make_2val(1171))
      let jsxtnm2017 = XATSDAPP(jsxtnm2016(jsxtnm2008, jsxtnm2010))
      jsxtnm2018 = jsxtnm2017
    } // endlet
    // I1CMP:return:jsxtnm2018
    return jsxtnm2018
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm2020 = XATSTUP1(XATSTRCD(0), [jsxtnm2004, jsxtnm2005])
  let jsxtnm2021 = XATSDAPP(jsxtnm2019(jsxtnm2020))
  let jsxtnm2022 = XATSCAPP("TMopr", [5, XATSSTRN(">="), jsxtnm2021])
  // I1CMP:return:jsxtnm2022
  return jsxtnm2022
} // endfun(TMgte_7758)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7819(line=521,offs=1)--7882(line=524,offs=29)))
// I1FUNDCL
function TMneq_7822(arg1, arg2)
{ // fun
  let jsxtnm2023 = arg1
  let jsxtnm2024 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7866(line=524,offs=13)--7870(line=524,offs=17))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm2038 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm2025 = arg1
    // I1CMP:start
    let jsxtnm2037 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm2027
      let jsxtnm2026 = XATSPFLT(jsxtnm2025[0])
      jsxtnm2027 = jsxtnm2026
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm2029
      let jsxtnm2028 = XATSPFLT(jsxtnm2025[1])
      jsxtnm2029 = jsxtnm2028
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm2035 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm2030 = arg1
        let jsxtnm2031 = arg2
        // I1CMP:start
        let jsxtnm2032 = XATSCAPP("list_nil", [0])
        let jsxtnm2033 = XATSCAPP("list_cons", [1, jsxtnm2031, jsxtnm2032])
        let jsxtnm2034 = XATSCAPP("list_cons", [1, jsxtnm2030, jsxtnm2033])
        // I1CMP:return:jsxtnm2034
        return jsxtnm2034
      } // endtimp(list_make_2val(1171))
      let jsxtnm2036 = XATSDAPP(jsxtnm2035(jsxtnm2027, jsxtnm2029))
      jsxtnm2037 = jsxtnm2036
    } // endlet
    // I1CMP:return:jsxtnm2037
    return jsxtnm2037
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm2039 = XATSTUP1(XATSTRCD(0), [jsxtnm2023, jsxtnm2024])
  let jsxtnm2040 = XATSDAPP(jsxtnm2038(jsxtnm2039))
  let jsxtnm2041 = XATSCAPP("TMopr", [5, XATSSTRN("!="), jsxtnm2040])
  // I1CMP:return:jsxtnm2041
  return jsxtnm2041
} // endfun(TMneq_7822)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7883(line=525,offs=1)--7947(line=528,offs=30)))
// I1FUNDCL
function TMcmp_7886(arg1, arg2)
{ // fun
  let jsxtnm2042 = arg1
  let jsxtnm2043 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7931(line=528,offs=14)--7935(line=528,offs=18))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm2057 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm2044 = arg1
    // I1CMP:start
    let jsxtnm2056 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm2046
      let jsxtnm2045 = XATSPFLT(jsxtnm2044[0])
      jsxtnm2046 = jsxtnm2045
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm2048
      let jsxtnm2047 = XATSPFLT(jsxtnm2044[1])
      jsxtnm2048 = jsxtnm2047
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm2054 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm2049 = arg1
        let jsxtnm2050 = arg2
        // I1CMP:start
        let jsxtnm2051 = XATSCAPP("list_nil", [0])
        let jsxtnm2052 = XATSCAPP("list_cons", [1, jsxtnm2050, jsxtnm2051])
        let jsxtnm2053 = XATSCAPP("list_cons", [1, jsxtnm2049, jsxtnm2052])
        // I1CMP:return:jsxtnm2053
        return jsxtnm2053
      } // endtimp(list_make_2val(1171))
      let jsxtnm2055 = XATSDAPP(jsxtnm2054(jsxtnm2046, jsxtnm2048))
      jsxtnm2056 = jsxtnm2055
    } // endlet
    // I1CMP:return:jsxtnm2056
    return jsxtnm2056
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm2058 = XATSTUP1(XATSTRCD(0), [jsxtnm2042, jsxtnm2043])
  let jsxtnm2059 = XATSDAPP(jsxtnm2057(jsxtnm2058))
  let jsxtnm2060 = XATSCAPP("TMopr", [5, XATSSTRN("cmp"), jsxtnm2059])
  // I1CMP:return:jsxtnm2060
  return jsxtnm2060
} // endfun(TMcmp_7886)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(7951(line=530,offs=1)--8015(line=533,offs=29)))
// I1FUNDCL
function TMconj_7954(arg1, arg2)
{ // fun
  let jsxtnm2061 = arg1
  let jsxtnm2062 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(7999(line=533,offs=13)--8003(line=533,offs=17))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm2076 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm2063 = arg1
    // I1CMP:start
    let jsxtnm2075 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm2065
      let jsxtnm2064 = XATSPFLT(jsxtnm2063[0])
      jsxtnm2065 = jsxtnm2064
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm2067
      let jsxtnm2066 = XATSPFLT(jsxtnm2063[1])
      jsxtnm2067 = jsxtnm2066
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm2073 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm2068 = arg1
        let jsxtnm2069 = arg2
        // I1CMP:start
        let jsxtnm2070 = XATSCAPP("list_nil", [0])
        let jsxtnm2071 = XATSCAPP("list_cons", [1, jsxtnm2069, jsxtnm2070])
        let jsxtnm2072 = XATSCAPP("list_cons", [1, jsxtnm2068, jsxtnm2071])
        // I1CMP:return:jsxtnm2072
        return jsxtnm2072
      } // endtimp(list_make_2val(1171))
      let jsxtnm2074 = XATSDAPP(jsxtnm2073(jsxtnm2065, jsxtnm2067))
      jsxtnm2075 = jsxtnm2074
    } // endlet
    // I1CMP:return:jsxtnm2075
    return jsxtnm2075
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm2077 = XATSTUP1(XATSTRCD(0), [jsxtnm2061, jsxtnm2062])
  let jsxtnm2078 = XATSDAPP(jsxtnm2076(jsxtnm2077))
  let jsxtnm2079 = XATSCAPP("TMopr", [5, XATSSTRN("&&"), jsxtnm2078])
  // I1CMP:return:jsxtnm2079
  return jsxtnm2079
} // endfun(TMconj_7954)
// I1Dfundclist(LCSRCsome1(lambda1.dats)@(8016(line=534,offs=1)--8080(line=537,offs=29)))
// I1FUNDCL
function TMdisj_8019(arg1, arg2)
{ // fun
  let jsxtnm2080 = arg1
  let jsxtnm2081 = arg2
  // I1CMP:start
  // LCSRCsome1(lambda1.dats)@(8064(line=537,offs=13)--8068(line=537,offs=17))
  // I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  // T1IMPallx(list_make_t0up2(1191);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  // T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7353],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3352],T2Pvar(x0[7353])))))))
  let jsxtnm2095 = function (arg1) { // timp: list_make_t0up2(1191)
    let jsxtnm2082 = arg1
    // I1CMP:start
    let jsxtnm2094 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
      // I1VALDCL
      let jsxtnm2084
      let jsxtnm2083 = XATSPFLT(jsxtnm2082[0])
      jsxtnm2084 = jsxtnm2083
      XATS000_patck(true)
      // I1VALDCL
      let jsxtnm2086
      let jsxtnm2085 = XATSPFLT(jsxtnm2082[1])
      jsxtnm2086 = jsxtnm2085
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
      // I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7353])))))
      // T1IMPallx(list_make_2val(1171);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
      // T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7343],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3309],T2Pvar(x0[7343])))))))
      let jsxtnm2092 = function (arg1, arg2) { // timp: list_make_2val(1171)
        let jsxtnm2087 = arg1
        let jsxtnm2088 = arg2
        // I1CMP:start
        let jsxtnm2089 = XATSCAPP("list_nil", [0])
        let jsxtnm2090 = XATSCAPP("list_cons", [1, jsxtnm2088, jsxtnm2089])
        let jsxtnm2091 = XATSCAPP("list_cons", [1, jsxtnm2087, jsxtnm2090])
        // I1CMP:return:jsxtnm2091
        return jsxtnm2091
      } // endtimp(list_make_2val(1171))
      let jsxtnm2093 = XATSDAPP(jsxtnm2092(jsxtnm2084, jsxtnm2086))
      jsxtnm2094 = jsxtnm2093
    } // endlet
    // I1CMP:return:jsxtnm2094
    return jsxtnm2094
  } // endtimp(list_make_t0up2(1191))
  let jsxtnm2096 = XATSTUP1(XATSTRCD(0), [jsxtnm2080, jsxtnm2081])
  let jsxtnm2097 = XATSDAPP(jsxtnm2095(jsxtnm2096))
  let jsxtnm2098 = XATSCAPP("TMopr", [5, XATSSTRN("||"), jsxtnm2097])
  // I1CMP:return:jsxtnm2098
  return jsxtnm2098
} // endfun(TMdisj_8019)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8127(line=542,offs=1)--8260(line=548,offs=2)))
// I1VALDCL
let jsxtnm2110
let jsxtnm2109 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8178(line=546,offs=1)--8211(line=546,offs=34)))
  // I1VALDCL
  let jsxtnm2100
  let jsxtnm2099 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
  jsxtnm2100 = jsxtnm2099
  XATS000_patck(true)
  // I1VALDCL
  let jsxtnm2102
  let jsxtnm2101 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm2102 = jsxtnm2101
  XATS000_patck(true)
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8212(line=547,offs=1)--8258(line=547,offs=47)))
  // I1VALDCL
  let jsxtnm2106
  let jsxtnm2103 = XATSCAPP("TMapp", [4, jsxtnm2102, jsxtnm2102])
  let jsxtnm2104 = XATSCAPP("TMapp", [4, jsxtnm2100, jsxtnm2103])
  let jsxtnm2105 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm2104])
  jsxtnm2106 = jsxtnm2105
  XATS000_patck(true)
  let jsxtnm2107 = XATSCAPP("TMapp", [4, jsxtnm2106, jsxtnm2106])
  let jsxtnm2108 = XATSCAPP("TMlam", [3, XATSSTRN("f"), jsxtnm2107])
  jsxtnm2109 = jsxtnm2108
} // endlet
jsxtnm2110 = jsxtnm2109
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8307(line=553,offs=1)--8495(line=568,offs=2)))
// I1VALDCL
let jsxtnm2128
let jsxtnm2127 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8343(line=558,offs=1)--8376(line=559,offs=26)))
  // I1VALDCL
  let jsxtnm2112
  let jsxtnm2111 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
  jsxtnm2112 = jsxtnm2111
  XATS000_patck(true)
  // I1VALDCL
  let jsxtnm2114
  let jsxtnm2113 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm2114 = jsxtnm2113
  XATS000_patck(true)
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8380(line=561,offs=1)--8490(line=566,offs=53)))
  // I1VALDCL
  let jsxtnm2125
  let jsxtnm2115 = XATSCAPP("TMint", [0, XATSINT1(0)])
  let jsxtnm2116 = XATSDAPP(TMlte_7694(jsxtnm2114, jsxtnm2115))
  let jsxtnm2117 = XATSCAPP("TMint", [0, XATSINT1(1)])
  let jsxtnm2118 = XATSCAPP("TMint", [0, XATSINT1(1)])
  let jsxtnm2119 = XATSDAPP(jsxtnm1137(jsxtnm2114, jsxtnm2118))
  let jsxtnm2120 = XATSCAPP("TMapp", [4, jsxtnm2112, jsxtnm2119])
  let jsxtnm2121 = XATSDAPP(jsxtnm1158(jsxtnm2114, jsxtnm2120))
  let jsxtnm2122 = XATSCAPP("TMif0", [6, jsxtnm2116, jsxtnm2117, jsxtnm2121])
  let jsxtnm2123 = XATSCAPP("TMlam", [3, XATSSTRN("x"), jsxtnm2122])
  let jsxtnm2124 = XATSCAPP("TMlam", [3, XATSSTRN("f"), jsxtnm2123])
  jsxtnm2125 = jsxtnm2124
  XATS000_patck(true)
  let jsxtnm2126 = XATSCAPP("TMapp", [4, jsxtnm2110, jsxtnm2125])
  jsxtnm2127 = jsxtnm2126
} // endlet
jsxtnm2128 = jsxtnm2127
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8528(line=570,offs=1)--8614(line=571,offs=69)))
// I1VALDCL
let jsxtnm2167
// LCSRCsome1(lambda1.dats)@(8537(line=570,offs=10)--8545(line=570,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm2162 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm2129 = arg1
  let jsxtnm2130 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm2153 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm2131 = arg1
    let jsxtnm2132 = arg2
    // I1CMP:start
    let jsxtnm2152 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm2136
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm2134 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm2133 = XATSTUP0([])
        // I1CMP:return:jsxtnm2133
        return jsxtnm2133
      } // endtimp(gs_print$beg(793))
      let jsxtnm2135 = XATSDAPP(jsxtnm2134())
      jsxtnm2136 = jsxtnm2135
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm2142
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm2141 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm2137 = arg1
        // I1CMP:start
        let jsxtnm2140 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(2138);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(2138)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm2139 = XATSDAPP(XATS2JS_strn_print(jsxtnm2137))
          jsxtnm2140 = jsxtnm2139
        } // endlet
        // I1CMP:return:jsxtnm2140
        return jsxtnm2140
      } // endtimp(strn_print(1029))
      jsxtnm2142 = jsxtnm2141
      let jsxtnm2143 = XATSDAPP(jsxtnm2142(jsxtnm2131))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm2145 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm2144 = XATSTUP0([])
        // I1CMP:return:jsxtnm2144
        return jsxtnm2144
      } // endtimp(gs_print$sep(794))
      let jsxtnm2146 = XATSDAPP(jsxtnm2145())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm2147
      jsxtnm2147 = jsxtnm879
      let jsxtnm2148 = XATSDAPP(jsxtnm2147(jsxtnm2132))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm2150 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm2149 = XATSTUP0([])
        // I1CMP:return:jsxtnm2149
        return jsxtnm2149
      } // endtimp(gs_print$end(795))
      let jsxtnm2151 = XATSDAPP(jsxtnm2150())
      jsxtnm2152 = jsxtnm2151
    } // endlet
    // I1CMP:return:jsxtnm2152
    return jsxtnm2152
  } // endtimp(gs_print_a2(798))
  let jsxtnm2154 = XATSDAPP(jsxtnm2153(jsxtnm2129, jsxtnm2130))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm2160
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm2159 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm2155 = arg1
    // I1CMP:start
    let jsxtnm2158 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(2156);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(2156)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm2157 = XATSDAPP(XATS2JS_strn_print(jsxtnm2155))
      jsxtnm2158 = jsxtnm2157
    } // endlet
    // I1CMP:return:jsxtnm2158
    return jsxtnm2158
  } // endtimp(strn_print(1029))
  jsxtnm2160 = jsxtnm2159
  let jsxtnm2161 = XATSDAPP(jsxtnm2160(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm2161
  return jsxtnm2161
} // endtimp(gs_println_a2(811))
let jsxtnm2163 = XATSCAPP("TMint", [0, XATSINT1(5)])
let jsxtnm2164 = XATSCAPP("TMapp", [4, jsxtnm2128, jsxtnm2163])
let jsxtnm2165 = XATSDAPP(term_interp_4929(jsxtnm2164))
let jsxtnm2166 = XATSDAPP(jsxtnm2162(XATSSTRN("TMapp(TMfact, TMint(5)) = "), jsxtnm2165))
jsxtnm2167 = jsxtnm2166
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8641(line=575,offs=1)--8818(line=589,offs=2)))
// I1VALDCL
let jsxtnm2183
let jsxtnm2182 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8689(line=581,offs=1)--8722(line=582,offs=26)))
  // I1VALDCL
  let jsxtnm2169
  let jsxtnm2168 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
  jsxtnm2169 = jsxtnm2168
  XATS000_patck(true)
  // I1VALDCL
  let jsxtnm2171
  let jsxtnm2170 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
  jsxtnm2171 = jsxtnm2170
  XATS000_patck(true)
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8726(line=584,offs=1)--8813(line=587,offs=51)))
  // I1VALDCL
  let jsxtnm2180
  let jsxtnm2172 = XATSCAPP("TMint", [0, XATSINT1(0)])
  let jsxtnm2173 = XATSDAPP(TMlte_7694(jsxtnm2171, jsxtnm2172))
  let jsxtnm2174 = XATSCAPP("TMint", [0, XATSINT1(1)])
  let jsxtnm2175 = XATSCAPP("TMint", [0, XATSINT1(1)])
  let jsxtnm2176 = XATSDAPP(jsxtnm1137(jsxtnm2171, jsxtnm2175))
  let jsxtnm2177 = XATSCAPP("TMapp", [4, jsxtnm2169, jsxtnm2176])
  let jsxtnm2178 = XATSDAPP(jsxtnm1158(jsxtnm2171, jsxtnm2177))
  let jsxtnm2179 = XATSCAPP("TMif0", [6, jsxtnm2173, jsxtnm2174, jsxtnm2178])
  jsxtnm2180 = jsxtnm2179
  XATS000_patck(true)
  let jsxtnm2181 = XATSCAPP("TMfix", [7, XATSSTRN("f"), XATSSTRN("x"), jsxtnm2180])
  jsxtnm2182 = jsxtnm2181
} // endlet
jsxtnm2183 = jsxtnm2182
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8854(line=591,offs=1)--8942(line=592,offs=71)))
// I1VALDCL
let jsxtnm2222
// LCSRCsome1(lambda1.dats)@(8863(line=591,offs=10)--8871(line=591,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm2217 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm2184 = arg1
  let jsxtnm2185 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm2208 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm2186 = arg1
    let jsxtnm2187 = arg2
    // I1CMP:start
    let jsxtnm2207 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm2191
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm2189 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm2188 = XATSTUP0([])
        // I1CMP:return:jsxtnm2188
        return jsxtnm2188
      } // endtimp(gs_print$beg(793))
      let jsxtnm2190 = XATSDAPP(jsxtnm2189())
      jsxtnm2191 = jsxtnm2190
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm2197
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm2196 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm2192 = arg1
        // I1CMP:start
        let jsxtnm2195 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(2193);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(2193)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm2194 = XATSDAPP(XATS2JS_strn_print(jsxtnm2192))
          jsxtnm2195 = jsxtnm2194
        } // endlet
        // I1CMP:return:jsxtnm2195
        return jsxtnm2195
      } // endtimp(strn_print(1029))
      jsxtnm2197 = jsxtnm2196
      let jsxtnm2198 = XATSDAPP(jsxtnm2197(jsxtnm2186))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm2200 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm2199 = XATSTUP0([])
        // I1CMP:return:jsxtnm2199
        return jsxtnm2199
      } // endtimp(gs_print$sep(794))
      let jsxtnm2201 = XATSDAPP(jsxtnm2200())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm2202
      jsxtnm2202 = jsxtnm879
      let jsxtnm2203 = XATSDAPP(jsxtnm2202(jsxtnm2187))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm2205 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm2204 = XATSTUP0([])
        // I1CMP:return:jsxtnm2204
        return jsxtnm2204
      } // endtimp(gs_print$end(795))
      let jsxtnm2206 = XATSDAPP(jsxtnm2205())
      jsxtnm2207 = jsxtnm2206
    } // endlet
    // I1CMP:return:jsxtnm2207
    return jsxtnm2207
  } // endtimp(gs_print_a2(798))
  let jsxtnm2209 = XATSDAPP(jsxtnm2208(jsxtnm2184, jsxtnm2185))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm2215
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm2214 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm2210 = arg1
    // I1CMP:start
    let jsxtnm2213 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(2211);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(2211)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm2212 = XATSDAPP(XATS2JS_strn_print(jsxtnm2210))
      jsxtnm2213 = jsxtnm2212
    } // endlet
    // I1CMP:return:jsxtnm2213
    return jsxtnm2213
  } // endtimp(strn_print(1029))
  jsxtnm2215 = jsxtnm2214
  let jsxtnm2216 = XATSDAPP(jsxtnm2215(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm2216
  return jsxtnm2216
} // endtimp(gs_println_a2(811))
let jsxtnm2218 = XATSCAPP("TMint", [0, XATSINT1(5)])
let jsxtnm2219 = XATSCAPP("TMapp", [4, jsxtnm2183, jsxtnm2218])
let jsxtnm2220 = XATSDAPP(term_interp_4929(jsxtnm2219))
let jsxtnm2221 = XATSDAPP(jsxtnm2217(XATSSTRN("TMapp(TMfact2, TMint(5)) = "), jsxtnm2220))
jsxtnm2222 = jsxtnm2221
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8989(line=597,offs=1)--9185(line=610,offs=2)))
// I1VALDCL
let jsxtnm2240
let jsxtnm2239 // let
{ // let
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9036(line=603,offs=1)--9069(line=604,offs=26)))
  // I1VALDCL
  let jsxtnm2224
  let jsxtnm2223 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
  jsxtnm2224 = jsxtnm2223
  XATS000_patck(true)
  // I1VALDCL
  let jsxtnm2226
  let jsxtnm2225 = XATSCAPP("TMvar", [2, XATSSTRN("n")])
  jsxtnm2226 = jsxtnm2225
  XATS000_patck(true)
  // I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9073(line=606,offs=1)--9180(line=608,offs=91)))
  // I1VALDCL
  let jsxtnm2237
  let jsxtnm2227 = XATSCAPP("TMint", [0, XATSINT1(1)])
  let jsxtnm2228 = XATSDAPP(TMlte_7694(jsxtnm2226, jsxtnm2227))
  let jsxtnm2229 = XATSCAPP("TMint", [0, XATSINT1(2)])
  let jsxtnm2230 = XATSDAPP(jsxtnm1137(jsxtnm2226, jsxtnm2229))
  let jsxtnm2231 = XATSCAPP("TMapp", [4, jsxtnm2224, jsxtnm2230])
  let jsxtnm2232 = XATSCAPP("TMint", [0, XATSINT1(1)])
  let jsxtnm2233 = XATSDAPP(jsxtnm1137(jsxtnm2226, jsxtnm2232))
  let jsxtnm2234 = XATSCAPP("TMapp", [4, jsxtnm2224, jsxtnm2233])
  let jsxtnm2235 = XATSDAPP(jsxtnm1116(jsxtnm2231, jsxtnm2234))
  let jsxtnm2236 = XATSCAPP("TMif0", [6, jsxtnm2228, jsxtnm2226, jsxtnm2235])
  jsxtnm2237 = jsxtnm2236
  XATS000_patck(true)
  let jsxtnm2238 = XATSCAPP("TMfix", [7, XATSSTRN("f"), XATSSTRN("n"), jsxtnm2237])
  jsxtnm2239 = jsxtnm2238
} // endlet
jsxtnm2240 = jsxtnm2239
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9221(line=612,offs=1)--9309(line=613,offs=71)))
// I1VALDCL
let jsxtnm2279
// LCSRCsome1(lambda1.dats)@(9230(line=612,offs=10)--9238(line=612,offs=18))
// I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
// T1IMPallx(gs_println_a2(811);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
// T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6996],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6997],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2534],T2Pvar(x0[6996])),@(x1[2535],T2Pvar(x1[6997])))))))
let jsxtnm2274 = function (arg1, arg2) { // timp: gs_println_a2(811)
  let jsxtnm2241 = arg1
  let jsxtnm2242 = arg2
  // I1CMP:start
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  // I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6996]))),T2JAG($list(T2Pvar(x1[6997])))))
  // T1IMPallx(gs_print_a2(798);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  // T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6918],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6919],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2456],T2Pvar(x0[6918])),@(x1[2457],T2Pvar(x1[6919])))))))
  let jsxtnm2265 = function (arg1, arg2) { // timp: gs_print_a2(798)
    let jsxtnm2243 = arg1
    let jsxtnm2244 = arg2
    // I1CMP:start
    let jsxtnm2264 // let
    { // let
      // I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
      // I1VALDCL
      let jsxtnm2248
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
      // I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$beg(793);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
      // T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
      let jsxtnm2246 = function () { // timp: gs_print$beg(793)
        // I1CMP:start
        let jsxtnm2245 = XATSTUP0([])
        // I1CMP:return:jsxtnm2245
        return jsxtnm2245
      } // endtimp(gs_print$beg(793))
      let jsxtnm2247 = XATSDAPP(jsxtnm2246())
      jsxtnm2248 = jsxtnm2247
      XATS000_patck(true)
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6918])))))
      // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
      let jsxtnm2254
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
      // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
      // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
      // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
      let jsxtnm2253 = function (arg1) { // timp: strn_print(1029)
        let jsxtnm2249 = arg1
        // I1CMP:start
        let jsxtnm2252 // let
        { // let
          // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
          // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
          // I1FUNDCL
          // XATS2JS_strn_print_2202
            // FJARGdarg($list(I1BNDcons(I1TNM(2250);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(2250)))))))
            // I1CMP:start
            // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
          let jsxtnm2251 = XATSDAPP(XATS2JS_strn_print(jsxtnm2249))
          jsxtnm2252 = jsxtnm2251
        } // endlet
        // I1CMP:return:jsxtnm2252
        return jsxtnm2252
      } // endtimp(strn_print(1029))
      jsxtnm2254 = jsxtnm2253
      let jsxtnm2255 = XATSDAPP(jsxtnm2254(jsxtnm2243))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
      // I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$sep(794);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
      // T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
      let jsxtnm2257 = function () { // timp: gs_print$sep(794)
        // I1CMP:start
        let jsxtnm2256 = XATSTUP0([])
        // I1CMP:return:jsxtnm2256
        return jsxtnm2256
      } // endtimp(gs_print$sep(794))
      let jsxtnm2258 = XATSDAPP(jsxtnm2257())
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
      // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6919])))))
      // T1IMPallx(g_print(39);LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
      // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(term)))))))
      let jsxtnm2259
      jsxtnm2259 = jsxtnm879
      let jsxtnm2260 = XATSDAPP(jsxtnm2259(jsxtnm2244))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
      // I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
      // T1IMPallx(gs_print$end(795);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
      // T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
      let jsxtnm2262 = function () { // timp: gs_print$end(795)
        // I1CMP:start
        let jsxtnm2261 = XATSTUP0([])
        // I1CMP:return:jsxtnm2261
        return jsxtnm2261
      } // endtimp(gs_print$end(795))
      let jsxtnm2263 = XATSDAPP(jsxtnm2262())
      jsxtnm2264 = jsxtnm2263
    } // endlet
    // I1CMP:return:jsxtnm2264
    return jsxtnm2264
  } // endtimp(gs_print_a2(798))
  let jsxtnm2266 = XATSDAPP(jsxtnm2265(jsxtnm2241, jsxtnm2242))
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  // I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  // T1IMPallx(g_print(39);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  // T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[434],T2Pcst(strn)))))))
  let jsxtnm2272
  // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  // I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  // T1IMPallx(strn_print(1029);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2111(line=101,offs=1)--2251(line=112,offs=2)))
  // T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  let jsxtnm2271 = function (arg1) { // timp: strn_print(1029)
    let jsxtnm2267 = arg1
    // I1CMP:start
    let jsxtnm2270 // let
    { // let
      // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2191(line=109,offs=1)--2249(line=111,offs=47)))
      // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/strn000.dats)@(2199(line=110,offs=1)--2249(line=111,offs=47))
      // I1FUNDCL
      // XATS2JS_strn_print_2202
        // FJARGdarg($list(I1BNDcons(I1TNM(2268);I0Pvar(cs(5093));$list(@(cs(5093),I1Vtnm(I1TNM(2268)))))))
        // I1CMP:start
        // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_strn_print);G1Nlist($list())) // I1CMP:return
      let jsxtnm2269 = XATSDAPP(XATS2JS_strn_print(jsxtnm2267))
      jsxtnm2270 = jsxtnm2269
    } // endlet
    // I1CMP:return:jsxtnm2270
    return jsxtnm2270
  } // endtimp(strn_print(1029))
  jsxtnm2272 = jsxtnm2271
  let jsxtnm2273 = XATSDAPP(jsxtnm2272(XATSSTRN("\n")))
  // I1CMP:return:jsxtnm2273
  return jsxtnm2273
} // endtimp(gs_println_a2(811))
let jsxtnm2275 = XATSCAPP("TMint", [0, XATSINT1(10)])
let jsxtnm2276 = XATSCAPP("TMapp", [4, jsxtnm2240, jsxtnm2275])
let jsxtnm2277 = XATSDAPP(term_interp_4929(jsxtnm2276))
let jsxtnm2278 = XATSDAPP(jsxtnm2274(XATSSTRN("TMapp(TMfibo, TMint(10)) = "), jsxtnm2277))
jsxtnm2279 = jsxtnm2278
XATS000_patck(true)
// I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9382(line=621,offs=1)--9436(line=623,offs=34)))
// I1VALDCL
let jsxtnm2290
// LCSRCsome1(lambda1.dats)@(9391(line=622,offs=1)--9402(line=622,offs=12))
// I0Etapq(I0Ecst(console_log(2559)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(1544(line=50,offs=1)--1555(line=50,offs=12))));$list(T2JAG($list())))
// T1IMPallx(console_log(2559);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(1581(line=53,offs=1)--1730(line=65,offs=2)))
// T1IMPallx(console_log(2559)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(console_log(2559);$list()))))
let jsxtnm2284 = function (arg1) { // timp: console_log(2559)
  let jsxtnm2280 = arg1
  // I1CMP:start
  let jsxtnm2283 // let
  { // let
    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(1663(line=61,offs=1)--1728(line=64,offs=34)))
    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(1671(line=62,offs=1)--1728(line=64,offs=34))
    // I1FUNDCL
    // XATS2JS_console_log_1674
      // FJARGdarg($list(I1BNDcons(I1TNM(2281);I0Pvar(x0(4785));$list(@(x0(4785),I1Vtnm(I1TNM(2281)))))))
      // I1CMP:start
      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_console_log);G1Nlist($list())) // I1CMP:return
    let jsxtnm2282 = XATSDAPP(XATS2JS_console_log(jsxtnm2280))
    jsxtnm2283 = jsxtnm2282
  } // endlet
  // I1CMP:return:jsxtnm2283
  return jsxtnm2283
} // endtimp(console_log(2559))
// LCSRCsome1(lambda1.dats)@(9404(line=623,offs=2)--9425(line=623,offs=23))
// I0Etapq(I0Ecst(the_print_store_flush(2562)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(1836(line=76,offs=1)--1857(line=76,offs=22))));$list(T2JAG($list())))
// T1IMPallx(the_print_store_flush(2562);LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(1998(line=87,offs=1)--2171(line=98,offs=2)))
// T1IMPallx(the_print_store_flush(2562)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(the_print_store_flush(2562);$list()))))
let jsxtnm2287 = function () { // timp: the_print_store_flush(2562)
  // I1CMP:start
  let jsxtnm2286 // let
  { // let
    // I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(2108(line=95,offs=1)--2169(line=97,offs=50)))
    // LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/JS/xtop000.dats)@(2116(line=96,offs=1)--2169(line=97,offs=50))
    // I1FUNDCL
    // XATS2JS_the_print_store_flush_2119
      // FJARGdarg($list())
      // I1CMP:start
      // I1CMP(ival):I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2JS_the_print_store_flush);G1Nlist($list())) // I1CMP:return
    let jsxtnm2285 = XATSDAPP(XATS2JS_the_print_store_flush())
    jsxtnm2286 = jsxtnm2285
  } // endlet
  // I1CMP:return:jsxtnm2286
  return jsxtnm2286
} // endtimp(the_print_store_flush(2562))
let jsxtnm2288 = XATSDAPP(jsxtnm2287())
let jsxtnm2289 = XATSDAPP(jsxtnm2284(jsxtnm2288))
jsxtnm2290 = jsxtnm2289
XATS000_patck(true)
// LCSRCsome1(lambda1.dats)@(9746(line=632,offs=1)--9746(line=632,offs=1))
// I1Dnone1(I0Dnone1(LCSRCsome1(lambda1.dats)@(9746(line=632,offs=1)--9746(line=632,offs=1));D3Cnone0()))

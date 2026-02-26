## Fri Feb 13 08:49:24 AM EST 2026
########################################################################.
########################################################################.
##
## HX-2025-01-02:
## ATS3-XANADU/srcgen2/xats2py/srcgen1
##
########################################################################.
########################################################################.
##
XATSTOP0 = None
##
########################################################################.
##
def XATSINT0(i0): return i0
def XATSINT1(i0): return i0
##
def XATSBTF0(b0): return b0
def XATSBOOL(b0): return b0
##
def XATSCNUL(  ): return (0)
def XATSCHR1(  ): return (0)
##
def XATSCHR0(ch):
  return ord(ch[0]) ## acsii
def XATSCHR2(ch):
  return ord(ch[0]) ## acsii
##
def XATSCHR3(ch):
  c1 = ord(ch[1])
  ## ord('0') = 48
  ## ord('7') = 55
  if (c1 < 48 or c1 > 55):
    ## for example: '\(', '\)'
    return ord(ch[1]) ## acsii
  else:
    i1 = 2
    d1 = c1 - 48
    while (i1 < len(ch)):
      c1 = ch[i1]
      if (c1 == "'"):
        return d1
      else:
        d1 = 8*d1 + ord(c1)-48
    return d1 ## ascii code of [ch]
##
def XATSFLT0(f0): return (f0)
def XATSFLT1(f0): return (f0)
##
def XATSSTR0(cs): return (cs)
def XATSSTRN(cs): return (cs)
##
def XATSSFLT(sf): return float(sf)
def XATSDFLT(df): return float(df)
##
########################################################################.

def XATSDAPP(dapp): return dapp
def XATSCAPP(_, capp): return capp
def XATSCAST(_, args): return args[0]

########################################################################.
##
def XATSPFLT(pflt): return pflt
def XATSPROJ(proj): return proj
def XATSP0RJ(p0rj): return p0rj
def XATSP1RJ(_, p1rj): return p1rj
def XATSP1CN(_, p1cn): return p1cn
##
def XATSPCON(pcon, argi): return pcon[argi+1]
##
########################################################################.
##
def XATSTRCD(knd0): return knd0
##
def XATSTUP0(tpl0): return tpl0
def XATSTUP1(knd0, tpl1): return tpl1
def XATSRCD2(knd0, rcd2): return rcd2
##
########################################################################.
##
def XATSROOT(x): return [0, x]
def XATSLPFT(i, x): return [1+0, x, i]
def XATSLPBX(i, x): return [1+1, x, i]
def XATSLPCN(i, x): return [1+2, x, i+1]
##
def XATSVAR0(    ): return XATSROOT([None])
def XATSVAR1(init): return XATSROOT([init])
##
def XATSADDR(addr): return addr ## HX: no-op
def XATSFLAT(addr): return XATS000_lvget(addr)
##
########################################################################.
##
def XATSCTAG(_, t): return t
##
def XATS000_inteq(x, y): return (x == y)
def XATS000_btfeq(x, y): return (x == y)
def XATS000_chreq(x, y): return (x == y)
##
def XATS000_streq(x, y): return (x == y)
##
def XATS000_ctgeq(v, t): return (v[0] == t)
##
########################################################################.
##
def XATS2PY_optn_nil():
  return XATSCAPP("optn_nil", [0])
def XATS2PY_optn_cons(x0):
  return XATSCAPP("optn_cons", [1, x0])
##
def XATS2PY_list_nil():
  return XATSCAPP("list_nil", [0])
def XATS2PY_list_cons(x0, xs):
  return XATSCAPP("list_cons", [1, x0, xs])
##
def XATS2PY_optn_vt_nil():
  return XATSCAPP("optn_vt_nil", [0])
def XATS2PY_optn_vt_cons(x0):
  return XATSCAPP("optn_vt_cons", [1, x0])
##
def XATS2PY_list_vt_nil():
  return XATSCAPP("list_vt_nil", [0])
def XATS2PY_list_vt_cons(x0, xs):
  return XATSCAPP("list_vt_cons", [1, x0, xs])
##
########################################################################.
##
def XATS000_casef():
  raise Exception("XATS000_casef")
##
def XATS000_patck(pck):
  if not(pck):
    raise Exception("XATS000_patck")
  ## end-of(if)
##
########################################################################.
##
def XATS000_fold(pcon): return None
def XATS000_free(pcon): return None
##
########################################################################.
##
def XATS000_dp2tr(p2tr):
  return XATS000_lvget(p2tr)
##
def XATS000_l0azy(lfun):
  return [0, lfun] # unevaled
def XATS000_dl0az(l0az):
  res = None
  if (l0az[0] > 0):
    l0az[0] += 1;
    res = l0az[1]; return res
  else:
    l0az[0] = 0+1;
    res = l0az[1]()
    l0az[1] = res; return res
##
def XATS000_l1azy(lfun): return lfun
def XATS000_dl1az(l1az): return l1az(1)
##
def XATS000_assgn(lval, rval):
  return XATS000_lvset(lval, rval)
##
########################################################################.
##
def XATS000_lvget(lval):
  ctag = lval[0]
  if (ctag == 0):
    return lval[1][0]
  if (ctag == 1+0):
    return XATS000_lvget(lval[1])[lval[2]]
  if (ctag == 1+1):
    return lval[1][lval[2]]
  if (ctag == 1+2):
    return lval[1][lval[2]]
##
def XATS000_lvset(lval, rval):
  ctag = lval[0]
  if (ctag == 0):
    lval[1][0] = rval; return
  if (ctag == 1+0):
    return XATS000_lvset(lval[1], XATS000_ftset(XATS000_lvget(lval[1]), lval[2], rval))
  if (ctag == 1+1):
    lval[1][lval[2]] = rval; return
  if (ctag == 1+2):
    lval[1][lval[2]] = rval; return
##
def XATS000_ftset(tpl0, idx1, rval):
  tpl1 = tpl0.copy(); tpl1[idx1] = rval; return tpl1
##
########################################################################.
class X2PYExcptn(Exception):
    pass
## end of [class X2PYExcptn]
########################################################################.
##
def XATS000_raise(xcon): raise(X2PYExcptn(xcon))
##
########################################################################.
########################################################################.
##
## the end of
## [ATS3-XANADU/srcgen2/xats2py/srcgen1/xshared/runtime/xats2py_py1emit.py]
##
########################################################################.
########################################################################.
## Sat Jan 17 10:53:13 PM EST 2026
########################################################################
########################################################################
##
## the beg of
## [ATS3-XANADU
## /srcgen2/xats2py/srcgen1/xshared/runtime/srcgen2_prelude.py]
##
########################################################################
########################################################################
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:38:30 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
import sys
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_xtop000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:43:18 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_gbas000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:49:44 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_bool_assert_errmsg(cond, emsg):
  if not(cond):
    raise Exception("XATS2PY_bool_assert_errmsg: emsg = " + emsg)
  return ## HX: void is returned!
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_gdbg000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:50:50 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_sint_neg(i1):
  return ( -i1 ) ## HX: neg
##
########################################################################.
##
def XATS2PY_sint_lt_sint(i1, i2):
  return (i1 < i2) ## HX: lt
def XATS2PY_sint_gt_sint(i1, i2):
  return (i1 > i2) ## HX: gt
##
def XATS2PY_sint_lte_sint(i1, i2):
  return (i1 <= i2) ## HX: lte
def XATS2PY_sint_gte_sint(i1, i2):
  return (i1 >= i2) ## HX: gte
##
def XATS2PY_sint_eq_sint(i1, i2):
  return (i1 == i2) ## HX: equal
def XATS2PY_sint_neq_sint(i1, i2):
  return (i1 != i2) ## HX: noteq
##
########################################################################.
##
def XATS2PY_sint_add_sint(i1, i2):
  return (i1 + i2) ## HX: add
def XATS2PY_sint_sub_sint(i1, i2):
  return (i1 - i2) ## HX: sub
def XATS2PY_sint_mul_sint(i1, i2):
  return (i1 * i2) ## HX: mul
def XATS2PY_sint_mod_sint(i1, i2):
  return (i1 % i2) ## HX: mod
def XATS2PY_sint_div_sint(i1, i2):
  return (i1 // i2) ## HX: int div
##
########################################################################.
##
def XATS2PY_sint_print(i0):
  sys.stdout.write(str(i0)); return None
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_gint000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:48:20 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_bool_lt(b1, b2):
  return (b1 < b2) ## HX: lt
def XATS2PY_bool_gt(b1, b2):
  return (b1 > b2) ## HX: gt
def XATS2PY_bool_eq(b1, b2):
  return (b1 == b2) ## HX: eq
def XATS2PY_bool_lte(b1, b2):
  return (b1 <= b2) ## HX: lte
def XATS2PY_bool_gte(b1, b2):
  return (b1 >= b2) ## HX: gte
def XATS2PY_bool_neq(b1, b2):
  return (b1 != b2) ## HX: neq
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_bool000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:49:26 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_char_lt(c1, c2):
  return (c1 < c2) ## HX: lt
def XATS2PY_char_gt(c1, c2):
  return (c1 > c2) ## HX: gt
def XATS2PY_char_eq(c1, c2):
  return (c1 == c2) ## HX: eq
##
def XATS2PY_char_lte(c1, c2):
  return (c1 <= c2) ## HX: lte
def XATS2PY_char_gte(c1, c2):
  return (c1 >= c2) ## HX: gte
def XATS2PY_char_neq(c1, c2):
  return (c1 != c2) ## HX: noteq
##
########################################################################.
##
def XATS2PY_char_add_sint(c1, i2):
  c2 = c1+i2
  return (c2%256) ## HX: char=int8
##
def XATS2PY_char_sub_char(c1, c2):
  return (c1 - c2) ## HX: char=int8
##
########################################################################.
##
def XATS2PY_char_print(c0):
  XATS2PY_strn_print(chr(c0)); return
##
########################################################################.
########################################################################.
##
## HX-2026-01-17:
## Sat Jan 17 09:51:13 PM EST 2026
##
def \
XATS2PY_char_make_sint(i0): return i0
def \
XATS2PY_sint_make_char(ch): return ch
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_char000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:50:50 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_dflt_neg(df):
  return ( -df ) ## HX:neg
##
########################################################################.
##
def XATS2PY_dflt_abs(df):
  if df >= 0.0:
    return df
  else:
    return (-df) ## HX:abs
##
########################################################################.
##
def XATS2PY_dflt_sqrt(df):
  return math.sqrt(  df  )
##
def XATS2PY_dflt_cbrt(df):
  return math.cbrt(  df  )
##
########################################################################.
##
def XATS2PY_dflt_lt_dflt(f1, f2):
  return (f1 < f2) ## HX: lt
def XATS2PY_dflt_gt_dflt(f1, f2):
  return (f1 > f2) ## HX: gt
def XATS2PY_dflt_eq_dflt(f1, f2):
  return (f1 == f2) ## HX: equal
##
def XATS2PY_dflt_lte_dflt(f1, f2):
  return (f1 <= f2) ## HX: lte
def XATS2PY_dflt_gte_dflt(f1, f2):
  return (f1 >= f2) ## HX: gte
def XATS2PY_dflt_neq_dflt(f1, f2):
  return (f1 != f2) ## HX: noteq
##
########################################################################.
##
def XATS2PY_dflt_add_dflt(f1, f2):
  return (f1 + f2) ## HX: add
def XATS2PY_dflt_sub_dflt(f1, f2):
  return (f1 - f2) ## HX: sub
##
def XATS2PY_dflt_mul_dflt(f1, f2):
  return (f1 * f2) ## HX: mul
##
def XATS2PY_dflt_div_dflt(f1, f2):
  return (f1 / f2) ## HX: div
def XATS2PY_dflt_mod_dflt(f1, f2):
  return (f1 % f2) ## HX: mod
##
########################################################################.
########################################################################.
##
def XATS2PY_dflt_ceil(df):
  return math.ceil(df) ## (1.2) = 2
def XATS2PY_dflt_floor(df):
  return math.floor(df) ## (1.2) = 1
def XATS2PY_dflt_round(df):
  ## HX: (1.2) = 1 ## (1.5) = 2
  return math.round(df) ## (-1.5) = 1
def XATS2PY_dflt_trunc(df):
  ## HX: (1.2) = 1 ## (1.9) = 1
  return math.trunc(df) ## (-1.2) = -1
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_gflt000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:46:58 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_strn_cmp(x1, x2):
  df = 0
  i0 = 0
  n1 = len(x1)
  n2 = len(x2)
  n0 = n1 if (n1 <= n2) else n2
  while (i0 < n0):
    df = ord(x1[i0]) - ord(x2[i0])
    if (df != 0):
      return df
    else:
      i0 = i0 + 1
  return (n1 - n2)
##
########################################################################.
##
def XATS2PY_strn_length(cs):
  return len(cs) # PY special [len]
def XATS000_strn_length(cs):
  return len(cs) # PY special [len]
##
########################################################################.
##
def XATS2PY_strn_print(cs):
  sys.stdout.write(cs); return None
def XATS000_strn_print(cs):
  sys.stdout.write(cs); return None
##
########################################################################.
##
def XATS2PY_strn_get_at_raw(cs, i0):
  return ord(cs[i0]) # PY is charless
def XATS000_strn_get_at_raw(cs, i0):
  return XATS2PY_strn_get_at_raw(cs, i0)
##
########################################################################.
##
def XATS2PY_strn_fmake_fwork(fwork):
  res = []
  fwork(lambda ch: res.append(chr(ch)))
  return "".join(res)
def XATS000_strn_fmake_fwork(fwork):
  return XATS2PY_strn_fmake_fwork(fwork)
##
########################################################################.
##
def \
XATS2PY_strn_fmake_env_fwork(env, fwork):
  res = []
  fwork(env, lambda ch: res.append(chr(ch)))
  return "".join(res)
def \
XATS2PY_strn_fmake1_env_fwork(env, fwork):
  res = []
  fwork(env, lambda ch: res.append(chr(ch)))
  return "".join(res)
##
def XATS000_strn_fmake_env_fwork(env, fwork):
  return XATS2PY_strn_fmake_env_fwork(env, fwork)
def XATS000_strn_fmake1_env_fwork(env, fwork):
  return XATS2PY_strn_fmake1_env_fwork(env, fwork)
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_strn000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Sat Jan  3 05:24:14 PM EST 2026
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def \
XATS2PY_list_vt_foritm0_f1un \
  (xs, work):
  while (True):
    if XATS2PY_list_vt_nilq1(xs):
      break
    else:
      x1 = XATS2PY_list_vt_head_raw1(xs)
      work(x1)
      xs = XATS2PY_list_vt_tail_raw0(xs)
    ## end-of-(if(XATS2PY_list_vt_nilq1(xs)))
  return None ## XATS2PY_list_vt_foritm0_f1un(...)
##
########################################################################.
##
def \
XATS2PY_list_vt_forall0_f1un \
  (xs, test, free):
  while (True):
    if (XATS2PY_list_vt_nilq1(xs)):
      break
    else:
      x1 = XATS2PY_list_vt_head_raw1(xs)
      if (test(x1)):
        xs = XATS2PY_list_vt_tail_raw0(xs)
      else:
        xs = XATS2PY_list_vt_tail_raw0(xs)
        XATS2PY_list_vt_foritm0_f1un(xs, free)
        return False
    ## end-of-(if(XATS2PY_list_vt_nilq1(xs)))
  return True ## XATS2PY_list_vt_forall0_f1un(...)
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_list000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Sat Jan  3 05:24:14 PM EST 2026
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
## HX: It is yet to be populated!
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_optn000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Sat Jan  3 04:47:20 PM EST 2026
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def \
XATS2PY_strm_vt_forall0_f1un \
  (fxs, test):
  while (True):
    cxs = XATS2PY_lazy_vt_eval(fxs)
    if XATS2PY_strmcon_vt_nilq1(cxs):
      break
    else:
      x01 = XATS2PY_strmcon_vt_head_raw1(cxs)
      if (test(x01)):
        fxs = XATS2PY_strmcon_vt_tail_raw0(cxs)
      else:
        fxs = XATS2PY_strmcon_vt_tail_raw0(cxs)
        XATS2PY_lazy_vt_free(fxs)
        return False
      ## end-of-(if(test(x01))
    ## end-of-(if(XATS2PY_strmcon_vt_nilq1(cxs)))
  return True ## XATS2PY_strm_vt_forall0_f1un(...)
##
########################################################################.
##
def \
XATS2PY_strm_vt_filter0_f1un \
  (fxs, test, free):
  return XATS2PY_lazy_vt_make_f0un(
    lambda: XATS2PY_strmcon_vt_filter0_f1un(XATS2PY_lazy_vt_eval(fxs), test, free)
  )
##
def \
XATS2PY_strmcon_vt_filter0_f1un \
  (cxs, test, free):
  while (True):
    if XATS2PY_strmcon_vt_nilq1(cxs):
      return XATS2PY_strmcon_vt_nil()
    else:
      x01 = XATS2PY_strmcon_vt_head_raw1(cxs)
      fxs = XATS2PY_strmcon_vt_tail_raw0(cxs)
      if (test(x01)):
        return XATS2PY_strmcon_vt_cons(x01, XATS2PY_strm_vt_filter0_f1un(fxs, test, free))
      else:
        free(x01)
        cxs = XATS2PY_lazy_vt_eval(fxs)
        continue
      ## end-of-(if(test(x01))
    ## end-of-(if(XATS2PY_strmcon_vt_nilq1(cxs))
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_strm000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2026 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan 14 02:42:28 PM EST 2026
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def \
XATS2PY_strx_vt_forall0_f1un \
  (fxs, test):
  while (True):
    cxs = XATS2PY_lazy_vt_eval(fxs)
    x01 = XATS2PY_strxcon_vt_head_raw1(cxs)
    if (test(x01)):
      fxs = XATS2PY_strxcon_vt_tail_raw0(cxs)
    else:
      fxs = XATS2PY_strxcon_vt_tail_raw0(cxs)
      XATS2PY_lazy_vt_free(fxs)
      return False
    ## end-of-(if(test(x01)))
  return true ## XATS2PY_strx_vt_forall0_f1un(...)
##
########################################################################.
##
def \
XATS2PY_strx_vt_filter0_f1un \
  (fxs, test, free):
  return XATS2PY_lazy_vt_make_f0un(
    lambda: XATS2PY_strxcon_vt_filter0_f1un(XATS2PY_lazy_vt_eval(fxs), test, free)
  )
##
def \
XATS2PY_strxcon_vt_filter0_f1un \
  (cxs, test, free):
  while (True):
    x01 = XATS2PY_strxcon_vt_head_raw1(cxs)
    fxs = XATS2PY_strxcon_vt_tail_raw0(cxs)
    if (test(x01)):
      return XATS2PY_strxcon_vt_cons(x01, XATS2PY_strx_vt_filter0_f1un(fxs, test, free))
    else:
      free(x01)
      cxs = XATS2PY_lazy_vt_eval(fxs)
      continue
    ## end-of-(if(test(x01))
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_strx000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:46:14 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_a0rf_lget(A):
  return A[0]
def XATS2PY_a0rf_lset(A, x1):
  A[0] = x1; return
##
def XATS2PY_a0rf_make_1val(x0):
  return [x0] ## HX: singleton
##
########################################################################.
########################################################################.
##
def XATS2PY_a1rf_lget_at(A, i0):
  return A[i0]
def XATS2PY_a1rf_lset_at(A, i0, x1):
  A[i0] = x1; return
##
def XATS2PY_a1rf_make_ncpy(n0, x0):
  i0 = 0
  A0 = []
  while (i0 < n0):
    A0.append(x0); i0 = i0 + 1
  return A0 ## HX: A0 = [x0, x0, ..., x0]
##
def XATS2PY_a1rf_make_nfun(n0, fopr):
  i0 = 0
  A0 = []
  while (i0 < n0):
    A0.append(fopr(i0)); i0 = i0 + 1
  return A0 ## HX: A0 = [fopr(0),...,fopr(n)]
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_axrf000.cats]
########################################################################.
########################################################################.
########################################################################.
##                                                                    ##.
##                         Applied Type System                        ##.
##                                                                    ##.
########################################################################.

##
## ATS/Xanadu - Unleashing the Potential of Types!
## Copyright (C) 2025 Hongwei Xi, ATS Trustful Software, Inc.
## All rights reserved
##
## ATS is free software;  you can  redistribute it and/or modify it under
## the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
## Free Software Foundation; either version 3, or (at  your  option)  any
## later version.
## 
## ATS is distributed in the hope that it will be useful, but WITHOUT ANY
## WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
## FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
## for more details.
## 
## You  should  have  received  a  copy of the GNU General Public License
## along  with  ATS;  see the  file COPYING.  If not, please write to the
## Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
## 02110-1301, USA.
##

########################################################################.
########################################################################.
##
## Author: Hongwei Xi
## Wed Jan  8 02:46:14 AM EST 2025
## Authoremail: gmhwxiATgmailDOTcom
##
########################################################################.
########################################################################.
##
def XATS2PY_a1sz_length(A0):
  return len(A0)
##
########################################################################.
##
def XATS2PY_a1sz_lget_at(A0, i0):
  return A0[i0]
def XATS2PY_a1sz_lset_at(A0, i0, x1):
  A0[i0] = x1; return
##
########################################################################.
##
def XATS2PY_a1sz_make_ncpy(n0, x0):
  i0 = 0
  A0 = []
  while (i0 < n0):
    A0.append(x0); i0 = i0 + 1
  return A0 ## HX: A0 = [x0, ..., x0]
##
def XATS2PY_a1sz_make_nfun(n0, fopr):
  i0 = 0
  A0 = []
  while (i0 < n0):
    A0.append(fopr(i0)); i0 = i0 + 1
  return A0 ## HX: A0 = [fopr(0),...,fopr(n-1)]
##
########################################################################.
##
def XATS2PY_a1sz_fmake_fwork(fwork):
  A0 = []
  fwork(lambda x0: A0.append(x0)); return A0
##
########################################################################.
########################################################################.
## end of [ATS3/XANADU_prelude_DATS_CATS_PY_axsz000.cats]
########################################################################.
########################################################################.
## LCSRCsome1(lambda1.dats)@(134(line=9,offs=1)--175(line=10,offs=28))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(0;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(UN);G1Estr(T_STRN1_clsd("prelude/SATS/unsfx00.sats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats));...)))
## I1Dinclude(LCSRCsome1(lambda1.dats)@(216(line=13,offs=1)--257(line=14,offs=33)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(244(line=17,offs=1)--291(line=19,offs=28))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gbas000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(292(line=20,offs=1)--339(line=22,offs=28))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gbas001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(340(line=23,offs=1)--387(line=25,offs=28))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gbas002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas002.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(414(line=29,offs=1)--461(line=31,offs=28))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gdbg000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gdbg000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(488(line=35,offs=1)--541(line=37,offs=34))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gbas000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gbas000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(542(line=38,offs=1)--595(line=40,offs=34))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gbas001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gbas001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(767(line=51,offs=1)--807(line=51,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gxyz000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gxyz000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(854(line=56,offs=1)--894(line=56,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/unsfx00.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1038(line=65,offs=1)--1078(line=65,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gnum000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gnum000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1079(line=66,offs=1)--1119(line=66,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gord000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1120(line=67,offs=1)--1160(line=67,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gfun000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gfun000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1164(line=69,offs=1)--1204(line=69,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gseq000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1205(line=70,offs=1)--1245(line=70,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gseq001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1246(line=71,offs=1)--1286(line=71,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gseq002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq002.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1290(line=73,offs=1)--1330(line=73,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gasq000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gasq000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1331(line=74,offs=1)--1371(line=74,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gasq001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gasq001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1372(line=75,offs=1)--1412(line=75,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gasq002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gasq002.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1416(line=77,offs=1)--1456(line=77,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gmap000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gmap000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1457(line=78,offs=1)--1497(line=78,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gmap001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gmap001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1501(line=80,offs=1)--1541(line=80,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gcls000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gcls000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1542(line=81,offs=1)--1582(line=81,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gsyn000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1583(line=82,offs=1)--1623(line=82,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gsyn001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1650(line=86,offs=1)--1690(line=86,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/bool000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1691(line=87,offs=1)--1731(line=87,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/char000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/char000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1732(line=88,offs=1)--1772(line=88,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gint000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1773(line=89,offs=1)--1813(line=89,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gint001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1814(line=90,offs=1)--1854(line=90,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/gflt000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gflt000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1881(line=94,offs=1)--1921(line=94,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strn000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1922(line=95,offs=1)--1962(line=95,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strn001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(1989(line=99,offs=1)--2029(line=99,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axrf000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axrf000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2030(line=100,offs=1)--2070(line=100,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axrf001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axrf001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2071(line=101,offs=1)--2111(line=101,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axsz000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axsz000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2112(line=102,offs=1)--2152(line=102,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/axsz001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/axsz001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2153(line=103,offs=1)--2193(line=103,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/asrt000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/asrt000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2194(line=104,offs=1)--2234(line=104,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/tupl000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/tupl000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2235(line=105,offs=1)--2275(line=105,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/tupl001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/tupl001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2276(line=106,offs=1)--2316(line=106,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/tupl002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/tupl002.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2317(line=107,offs=1)--2357(line=107,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/list000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2358(line=108,offs=1)--2398(line=108,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/list001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2399(line=109,offs=1)--2439(line=109,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/list002.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list002.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2440(line=110,offs=1)--2480(line=110,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/lsrt000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/lsrt000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2481(line=111,offs=1)--2521(line=111,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/optn000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/optn000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2522(line=112,offs=1)--2562(line=112,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/optn001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/optn001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2563(line=113,offs=1)--2603(line=113,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strm000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strm000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2604(line=114,offs=1)--2644(line=114,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strm001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strm001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2645(line=115,offs=1)--2685(line=115,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strx000.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strx000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2686(line=116,offs=1)--2726(line=116,offs=41))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/strx001.dats";27)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strx001.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2773(line=121,offs=1)--2818(line=121,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/gbas000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/gbas000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2822(line=123,offs=1)--2867(line=123,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/bool000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/bool000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2868(line=124,offs=1)--2913(line=124,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/char000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/char000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2917(line=126,offs=1)--2962(line=126,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/gint000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/gint000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(2963(line=127,offs=1)--3008(line=127,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/gflt000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/gflt000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3012(line=129,offs=1)--3057(line=129,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/strn000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/strn000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3061(line=131,offs=1)--3106(line=131,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/axrf000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/axrf000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3107(line=132,offs=1)--3152(line=132,offs=46))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/axsz000.dats";32)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/axsz000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3258(line=140,offs=1)--3304(line=140,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gnum000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gnum000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3305(line=141,offs=1)--3351(line=141,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gord000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gord000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3352(line=142,offs=1)--3398(line=142,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gfun000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gfun000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3399(line=143,offs=1)--3445(line=143,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gcls000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gcls000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3446(line=144,offs=1)--3492(line=144,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gseq000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3493(line=145,offs=1)--3539(line=145,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gseq001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3540(line=146,offs=1)--3586(line=146,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gseq002_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq002_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3587(line=147,offs=1)--3633(line=147,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gasq000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gasq000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3634(line=148,offs=1)--3680(line=148,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gasq001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gasq001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3681(line=149,offs=1)--3727(line=149,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gsyn000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gsyn000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3754(line=153,offs=1)--3800(line=153,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strn000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strn000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3827(line=157,offs=1)--3873(line=157,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/axrf000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/axrf000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3874(line=158,offs=1)--3920(line=158,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/axsz000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/axsz000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3921(line=159,offs=1)--3967(line=159,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/tupl000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/tupl000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(3971(line=161,offs=1)--4017(line=161,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/list000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4018(line=162,offs=1)--4064(line=162,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/list001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4065(line=163,offs=1)--4111(line=163,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/lsrt000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/lsrt000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4112(line=164,offs=1)--4158(line=164,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/optn000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/optn000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4159(line=165,offs=1)--4205(line=165,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/optn001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/optn001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4209(line=167,offs=1)--4255(line=167,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strm000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4256(line=168,offs=1)--4302(line=168,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strm001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4303(line=169,offs=1)--4349(line=169,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strm002_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm002_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4350(line=170,offs=1)--4396(line=170,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strx000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strx000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4397(line=171,offs=1)--4443(line=171,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/strx001_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strx001_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4614(line=182,offs=1)--4660(line=182,offs=47))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/VT/gxyz000_vt.dats";33)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4989(line=190,offs=1)--4989(line=190,offs=1))
## I1Dnone1(I0Dnone1(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_dats.hats)@(4989(line=190,offs=1)--4989(line=190,offs=1));D3Cnone0()))
## I1Dinclude(LCSRCsome1(lambda1.dats)@(435(line=27,offs=1)--479(line=28,offs=36)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(197(line=15,offs=1)--249(line=16,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/xtop000.dats";35));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/xtop000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(296(line=21,offs=1)--344(line=22,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/gbas000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gbas000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(345(line=23,offs=1)--393(line=24,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/gdbg000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gdbg000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(440(line=29,offs=1)--488(line=30,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/bool000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(489(line=31,offs=1)--537(line=32,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/char000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/char000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(538(line=33,offs=1)--586(line=34,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/gint000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(587(line=35,offs=1)--635(line=36,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/gflt000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gflt000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(682(line=41,offs=1)--730(line=42,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/strn000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(777(line=47,offs=1)--825(line=48,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/list000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/list000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(826(line=49,offs=1)--874(line=50,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/optn000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/optn000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(901(line=54,offs=1)--949(line=55,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/strm000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strm000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(950(line=56,offs=1)--998(line=57,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/strx000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strx000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(1045(line=62,offs=1)--1093(line=63,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/axrf000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/axrf000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(1094(line=64,offs=1)--1142(line=65,offs=36))
## I1Di0dcl(I0Dd3ecl(D3Cstaload(1;T_SRP_STALOAD();G1Ea2pp(G1Eid0(=);G1Eid0(_);G1Estr(T_STRN1_clsd("prelude/DATS/CATS/PY/axsz000.dats";35)));$optn(FPATH(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/axsz000.dats));...)))
## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(1398(line=73,offs=1)--1398(line=73,offs=1))
## I1Dnone1(I0Dnone1(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/HATS/prelude_PY_dats.hats)@(1398(line=73,offs=1)--1398(line=73,offs=1));D3Cnone0()))
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(566(line=34,offs=1)--609(line=35,offs=28)))
## I1VALDCL
pyxtnm19 = None
## LCSRCsome1(lambda1.dats)@(575(line=34,offs=10)--581(line=34,offs=16))
## I0Etapq(I0Ecst(gs_print_a1(797)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11760(line=745,offs=1)--11771(line=745,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
## T1IMPallx(gs_print_a1(797), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21002(line=1292,offs=1)--21119(line=1301,offs=4)))
## T1IMPallx(gs_print_a1(797)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6825],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a1(797);$list(@(x0[2393],T2Pvar(x0[6825])))))))
def pyxtnm17(arg1): ## timp: gs_print_a1(797)
  pyxtnm1 = arg1
  ## I1CMP:start
  ## let
  pyxtnm16 = None
  ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21049(line=1297,offs=1)--21072(line=1298,offs=15)))
  ## I1VALDCL
  pyxtnm5 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21058(line=1298,offs=1)--21070(line=1298,offs=13))
  ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
  ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
  ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
  def pyxtnm3(): ## timp: gs_print$beg(793)
    ## I1CMP:start
    pyxtnm2 = XATSTUP0([])
    ## I1CMP:return:pyxtnm2
    return pyxtnm2
  ## endtimp(gs_print$beg(793))
  pyxtnm4 = XATSDAPP(pyxtnm3())
  pyxtnm5 = pyxtnm4
  XATS000_patck(True)
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21083(line=1300,offs=1)--21090(line=1300,offs=8))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6825])))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm11 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm10(arg1): ## timp: strn_print(1029)
    pyxtnm6 = arg1
    ## I1CMP:start
    ## let
    pyxtnm9 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(7);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(7))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm8 = XATSDAPP(XATS2PY_strn_print(pyxtnm6))
    pyxtnm9 = pyxtnm8
    ## end-of(let)
    ## I1CMP:return:pyxtnm9
    return pyxtnm9
  ## endtimp(strn_print(1029))
  pyxtnm11 = pyxtnm10
  pyxtnm12 = XATSDAPP(pyxtnm11(pyxtnm1))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21100(line=1300,offs=18)--21112(line=1300,offs=30))
  ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
  ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
  ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
  def pyxtnm14(): ## timp: gs_print$end(795)
    ## I1CMP:start
    pyxtnm13 = XATSTUP0([])
    ## I1CMP:return:pyxtnm13
    return pyxtnm13
  ## endtimp(gs_print$end(795))
  pyxtnm15 = XATSDAPP(pyxtnm14())
  pyxtnm16 = pyxtnm15
  ## end-of(let)
  ## I1CMP:return:pyxtnm16
  return pyxtnm16
## endtimp(gs_print_a1(797))
pyxtnm18 = XATSDAPP(pyxtnm17(XATSSTRN("Hello from [lambda1]!\n")))
pyxtnm19 = pyxtnm18
XATS000_patck(True)
## LCSRCsome1(lambda1.dats)@(653(line=39,offs=1)--673(line=39,offs=21))
## I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Csexpdef(tvar;S2Ecst(strn)))))
## LCSRCsome1(lambda1.dats)@(674(line=40,offs=1)--694(line=40,offs=21))
## I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Csexpdef(topr;S2Ecst(strn)))))
## LCSRCsome1(lambda1.dats)@(718(line=43,offs=1)--1048(line=64,offs=29))
## I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Cdatatype(D1Cdatatype(T_DATATYPE(0);$list(D1TYPnode(T_IDALP(term);$list();$optn();$list(D1TCNnode($list();T_IDALP(TMint);$list();$optn(S1Eid0(sint))),D1TCNnode($list();T_IDALP(TMbtf);$list();$optn(S1Eid0(bool))),D1TCNnode($list();T_IDALP(TMvar);$list();$optn(S1Eid0(tvar))),D1TCNnode($list();T_IDALP(TMlam);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMapp);$list();$optn(S1El1st($list(S1Eid0(term),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMopr);$list();$optn(S1El1st($list(S1Eid0(topr),S1Ea1pp(S1Eid0(list);S1El1st($list(S1Eid0(term)))))))),D1TCNnode($list();T_IDALP(TMif0);$list();$optn(S1El1st($list(S1Eid0(term),S1Eid0(term),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMfix);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(tvar),S1Eid0(term))))),D1TCNnode($list();T_IDALP(TMlet);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(term),S1Eid0(term))))))));WD1CSnone());$list(term)))))
## LCSRCsome1(lambda1.dats)@(1052(line=66,offs=1)--1081(line=66,offs=30))
## I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Csexpdef(termlst;S2Eapps(S2Ecst(list);$list(S2Ecst(term)))))))
## I1Dlocal0(LCSRCsome1(lambda1.dats)@(1126(line=71,offs=1)--1482(line=96,offs=4)))
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1135(line=73,offs=1)--1191(line=75,offs=19)))
## I1VALDCL
pyxtnm21 = None
pyxtnm20 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm21 = pyxtnm20
XATS000_patck(True)
## I1VALDCL
pyxtnm23 = None
pyxtnm22 = XATSCAPP("TMvar", [2, XATSSTRN("y")])
pyxtnm23 = pyxtnm22
XATS000_patck(True)
## I1VALDCL
pyxtnm25 = None
pyxtnm24 = XATSCAPP("TMvar", [2, XATSSTRN("z")])
pyxtnm25 = pyxtnm24
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1210(line=79,offs=1)--1231(line=79,offs=22)))
## I1VALDCL
pyxtnm27 = None
pyxtnm26 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm21])
pyxtnm27 = pyxtnm26
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1235(line=81,offs=1)--1268(line=81,offs=34)))
## I1VALDCL
pyxtnm30 = None
pyxtnm28 = XATSCAPP("TMlam", [3, XATSSTRN("y"), pyxtnm21])
pyxtnm29 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm28])
pyxtnm30 = pyxtnm29
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1272(line=83,offs=1)--1347(line=87,offs=35)))
## I1VALDCL
pyxtnm37 = None
pyxtnm31 = XATSCAPP("TMapp", [4, pyxtnm21, pyxtnm25])
pyxtnm32 = XATSCAPP("TMapp", [4, pyxtnm23, pyxtnm25])
pyxtnm33 = XATSCAPP("TMapp", [4, pyxtnm31, pyxtnm32])
pyxtnm34 = XATSCAPP("TMlam", [3, XATSSTRN("z"), pyxtnm33])
pyxtnm35 = XATSCAPP("TMlam", [3, XATSSTRN("y"), pyxtnm34])
pyxtnm36 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm35])
pyxtnm37 = pyxtnm36
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1351(line=89,offs=1)--1385(line=89,offs=35)))
## I1VALDCL
pyxtnm40 = None
pyxtnm38 = XATSCAPP("TMlam", [3, XATSSTRN("y"), pyxtnm23])
pyxtnm39 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm38])
pyxtnm40 = pyxtnm39
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1389(line=91,offs=1)--1424(line=91,offs=36)))
## I1VALDCL
pyxtnm43 = None
pyxtnm41 = XATSCAPP("TMapp", [4, pyxtnm21, pyxtnm21])
pyxtnm42 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm41])
pyxtnm43 = pyxtnm42
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(1425(line=92,offs=1)--1475(line=94,offs=37)))
## I1VALDCL
pyxtnm45 = None
pyxtnm44 = XATSCAPP("TMapp", [4, pyxtnm43, pyxtnm43])
pyxtnm45 = pyxtnm44
XATS000_patck(True)
## I1Dextern(LCSRCsome1(lambda1.dats)@(1566(line=101,offs=1)--1607(line=103,offs=28)))
## I1Dfundclst(T_FUN(FNKfn1);$list(T2QAG($list()));$list(term_print(2643));$list(I1FUNDCL(term_print(5149);$list(FJARGdarg($list(I1BNDcons(I1TNM(46);I0Pvar(tm0(5150));$list(@(tm0(5150),I1Vtnm(I1TNM(46))))))));TEQI1CMPnone())))
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(1611(line=105,offs=1)--2326(line=156,offs=2)))
## I1Dimplmnt0(DIMPLone2(term_print(2643);$list())):timp
## I1Dlocal0(LCSRCsome1(lambda1.dats)@(2400(line=160,offs=1)--2489(line=164,offs=4)))
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2406(line=161,offs=1)--2437(line=161,offs=32)))
## I1VALDCL
pyxtnm879 = None
## LCSRCsome1(lambda1.dats)@(2425(line=161,offs=20)--2435(line=161,offs=30))
## I0Etapq(I0Ecst(term_print(2643)(LCSRCsome1(lambda1.dats)@(1580(line=103,offs=1)--1590(line=103,offs=11))));$list(T2JAG($list())))
## T1IMPallx(term_print(2643), LCSRCsome1(lambda1.dats)@(1611(line=105,offs=1)--2326(line=156,offs=2)))
## T1IMPallx(term_print(2643)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(term_print(2643);$list()))))
def pyxtnm878(arg1): ## timp: term_print(2643)
  pyxtnm71 = arg1
  ## I1CMP:start
  ## let
  pyxtnm877 = None
  ## I1Dfundclist(LCSRCsome1(lambda1.dats)@(1674(line=112,offs=1)--2315(line=155,offs=2)))
  ## I1FUNDCL
  def auxpr_1677(arg1): ## fun
    pyxtnm72 = arg1
    ## I1CMP:start
    ## let
    pyxtnm875 = None
    ## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
    ## I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term))))):timp
    pyxtnm874 = None
    while True: ## do {
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(73);I0Pdapp(I0Pcon(TMint(32));$list(I0Pvar(int(5154))));$list(@(int(5154),I1Vp1cn(I0Pcon(TMint(32));I1Vtnm(I1TNM(73));0)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMint",0))): ## { // gpt
        pyxtnm73 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(1738(line=120,offs=1)--1744(line=120,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a3(799), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
        ## T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6828],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6829],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))),@(x2[6830],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2396],T2Pvar(x0[6828])),@(x1[2397],T2Pvar(x1[6829])),@(x2[2398],T2Pvar(x2[6830])))))))
        def pyxtnm112(arg1, arg2, arg3): ## timp: gs_print_a3(799)
          pyxtnm74 = arg1
          pyxtnm75 = arg2
          pyxtnm76 = arg3
          ## I1CMP:start
          ## let
          pyxtnm111 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
          ## I1VALDCL
          pyxtnm80 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm78(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm77 = XATSTUP0([])
            ## I1CMP:return:pyxtnm77
            return pyxtnm77
          ## endtimp(gs_print$beg(793))
          pyxtnm79 = XATSDAPP(pyxtnm78())
          pyxtnm80 = pyxtnm79
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6828])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm86 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm85(arg1): ## timp: strn_print(1029)
            pyxtnm81 = arg1
            ## I1CMP:start
            ## let
            pyxtnm84 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(82);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(82))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm83 = XATSDAPP(XATS2PY_strn_print(pyxtnm81))
            pyxtnm84 = pyxtnm83
            ## end-of(let)
            ## I1CMP:return:pyxtnm84
            return pyxtnm84
          ## endtimp(strn_print(1029))
          pyxtnm86 = pyxtnm85
          pyxtnm87 = XATSDAPP(pyxtnm86(pyxtnm74))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm89(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm88 = XATSTUP0([])
            ## I1CMP:return:pyxtnm88
            return pyxtnm88
          ## endtimp(gs_print$sep(794))
          pyxtnm90 = XATSDAPP(pyxtnm89())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6829])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats)@(2286(line=96,offs=1)--2321(line=97,offs=27)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(si)))))))
          pyxtnm96 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats)@(2309(line=97,offs=15)--2319(line=97,offs=25))
          ## I0Etapq(I0Ecst(sint_print(913)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(1506(line=49,offs=1)--1516(line=49,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(sint_print(913), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3560(line=218,offs=1)--3700(line=229,offs=2)))
          ## T1IMPallx(sint_print(913)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_print(913);$list()))))
          def pyxtnm95(arg1): ## timp: sint_print(913)
            pyxtnm91 = arg1
            ## I1CMP:start
            ## let
            pyxtnm94 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3640(line=226,offs=1)--3698(line=228,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_print(2589));$list(I1FUNDCL(XATS2PY_sint_print(4925);$list(FJARGdarg($list(I1BNDcons(I1TNM(92);I0Pvar(i0(4926));$list(@(i0(4926),I1Vtnm(I1TNM(92))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_print);G1Nlist($list())))))))
            pyxtnm93 = XATSDAPP(XATS2PY_sint_print(pyxtnm91))
            pyxtnm94 = pyxtnm93
            ## end-of(let)
            ## I1CMP:return:pyxtnm94
            return pyxtnm94
          ## endtimp(sint_print(913))
          pyxtnm96 = pyxtnm95
          pyxtnm97 = XATSDAPP(pyxtnm96(pyxtnm75))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm99(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm98 = XATSTUP0([])
            ## I1CMP:return:pyxtnm98
            return pyxtnm98
          ## endtimp(gs_print$sep(794))
          pyxtnm100 = XATSDAPP(pyxtnm99())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6830])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm106 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm105(arg1): ## timp: strn_print(1029)
            pyxtnm101 = arg1
            ## I1CMP:start
            ## let
            pyxtnm104 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(102);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(102))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm103 = XATSDAPP(XATS2PY_strn_print(pyxtnm101))
            pyxtnm104 = pyxtnm103
            ## end-of(let)
            ## I1CMP:return:pyxtnm104
            return pyxtnm104
          ## endtimp(strn_print(1029))
          pyxtnm106 = pyxtnm105
          pyxtnm107 = XATSDAPP(pyxtnm106(pyxtnm76))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm109(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm108 = XATSTUP0([])
            ## I1CMP:return:pyxtnm108
            return pyxtnm108
          ## endtimp(gs_print$end(795))
          pyxtnm110 = XATSDAPP(pyxtnm109())
          pyxtnm111 = pyxtnm110
          ## end-of(let)
          ## I1CMP:return:pyxtnm111
          return pyxtnm111
        ## endtimp(gs_print_a3(799))
        pyxtnm113 = XATSDAPP(pyxtnm112(XATSSTRN("TMint("), XATSP1CN("TMint", pyxtnm73[0+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm113
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(114);I0Pdapp(I0Pcon(TMbtf(33));$list(I0Pvar(btf(5155))));$list(@(btf(5155),I1Vp1cn(I0Pcon(TMbtf(33));I1Vtnm(I1TNM(114));0)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMbtf",1))): ## { // gpt
        pyxtnm114 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(1781(line=123,offs=1)--1787(line=123,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a3(799), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
        ## T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6828],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6829],T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))),@(x2[6830],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2396],T2Pvar(x0[6828])),@(x1[2397],T2Pvar(x1[6829])),@(x2[2398],T2Pvar(x2[6830])))))))
        def pyxtnm163(arg1, arg2, arg3): ## timp: gs_print_a3(799)
          pyxtnm115 = arg1
          pyxtnm116 = arg2
          pyxtnm117 = arg3
          ## I1CMP:start
          ## let
          pyxtnm162 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
          ## I1VALDCL
          pyxtnm121 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm119(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm118 = XATSTUP0([])
            ## I1CMP:return:pyxtnm118
            return pyxtnm118
          ## endtimp(gs_print$beg(793))
          pyxtnm120 = XATSDAPP(pyxtnm119())
          pyxtnm121 = pyxtnm120
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6828])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm127 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm126(arg1): ## timp: strn_print(1029)
            pyxtnm122 = arg1
            ## I1CMP:start
            ## let
            pyxtnm125 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(123);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(123))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm124 = XATSDAPP(XATS2PY_strn_print(pyxtnm122))
            pyxtnm125 = pyxtnm124
            ## end-of(let)
            ## I1CMP:return:pyxtnm125
            return pyxtnm125
          ## endtimp(strn_print(1029))
          pyxtnm127 = pyxtnm126
          pyxtnm128 = XATSDAPP(pyxtnm127(pyxtnm115))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm130(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm129 = XATSTUP0([])
            ## I1CMP:return:pyxtnm129
            return pyxtnm129
          ## endtimp(gs_print$sep(794))
          pyxtnm131 = XATSDAPP(pyxtnm130())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6829])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1767(line=64,offs=1)--1804(line=65,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(bool)))))))
          pyxtnm147 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1792(line=65,offs=17)--1802(line=65,offs=27))
          ## I0Etapq(I0Ecst(bool_print(861)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/bool000.sats)@(2405(line=107,offs=1)--2415(line=107,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(bool_print(861), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats)@(2485(line=137,offs=1)--2582(line=143,offs=28)))
          ## T1IMPallx(bool_print(861)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(bool_print(861);$list()))))
          def pyxtnm146(arg1): ## timp: bool_print(861)
            pyxtnm132 = arg1
            ## I1CMP:start
            pyxtnm145 = None
            if (pyxtnm132):
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats)@(2534(line=142,offs=6)--2544(line=142,offs=16))
              ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
              ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
              ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
              def pyxtnm137(arg1): ## timp: strn_print(1029)
                pyxtnm133 = arg1
                ## I1CMP:start
                ## let
                pyxtnm136 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(134);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(134))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                pyxtnm135 = XATSDAPP(XATS2PY_strn_print(pyxtnm133))
                pyxtnm136 = pyxtnm135
                ## end-of(let)
                ## I1CMP:return:pyxtnm136
                return pyxtnm136
              ## endtimp(strn_print(1029))
              pyxtnm138 = XATSDAPP(pyxtnm137(XATSSTRN("true")))
              pyxtnm145 = pyxtnm138
            else:
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats)@(2560(line=143,offs=6)--2570(line=143,offs=16))
              ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
              ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
              ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
              def pyxtnm143(arg1): ## timp: strn_print(1029)
                pyxtnm139 = arg1
                ## I1CMP:start
                ## let
                pyxtnm142 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(140);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(140))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                pyxtnm141 = XATSDAPP(XATS2PY_strn_print(pyxtnm139))
                pyxtnm142 = pyxtnm141
                ## end-of(let)
                ## I1CMP:return:pyxtnm142
                return pyxtnm142
              ## endtimp(strn_print(1029))
              pyxtnm144 = XATSDAPP(pyxtnm143(XATSSTRN("false")))
              pyxtnm145 = pyxtnm144
            ## end-of(if)
            ## I1CMP:return:pyxtnm145
            return pyxtnm145
          ## endtimp(bool_print(861))
          pyxtnm147 = pyxtnm146
          pyxtnm148 = XATSDAPP(pyxtnm147(pyxtnm116))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm150(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm149 = XATSTUP0([])
            ## I1CMP:return:pyxtnm149
            return pyxtnm149
          ## endtimp(gs_print$sep(794))
          pyxtnm151 = XATSDAPP(pyxtnm150())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6830])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm157 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm156(arg1): ## timp: strn_print(1029)
            pyxtnm152 = arg1
            ## I1CMP:start
            ## let
            pyxtnm155 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(153);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(153))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm154 = XATSDAPP(XATS2PY_strn_print(pyxtnm152))
            pyxtnm155 = pyxtnm154
            ## end-of(let)
            ## I1CMP:return:pyxtnm155
            return pyxtnm155
          ## endtimp(strn_print(1029))
          pyxtnm157 = pyxtnm156
          pyxtnm158 = XATSDAPP(pyxtnm157(pyxtnm117))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm160(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm159 = XATSTUP0([])
            ## I1CMP:return:pyxtnm159
            return pyxtnm159
          ## endtimp(gs_print$end(795))
          pyxtnm161 = XATSDAPP(pyxtnm160())
          pyxtnm162 = pyxtnm161
          ## end-of(let)
          ## I1CMP:return:pyxtnm162
          return pyxtnm162
        ## endtimp(gs_print_a3(799))
        pyxtnm164 = XATSDAPP(pyxtnm163(XATSSTRN("TMbtf("), XATSP1CN("TMbtf", pyxtnm114[0+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm164
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(165);I0Pdapp(I0Pcon(TMvar(34));$list(I0Pvar(nam(5156))));$list(@(nam(5156),I1Vp1cn(I0Pcon(TMvar(34));I1Vtnm(I1TNM(165));0)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMvar",2))): ## { // gpt
        pyxtnm165 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(1824(line=126,offs=1)--1830(line=126,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a3(799), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
        ## T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6828],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6829],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6830],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2396],T2Pvar(x0[6828])),@(x1[2397],T2Pvar(x1[6829])),@(x2[2398],T2Pvar(x2[6830])))))))
        def pyxtnm204(arg1, arg2, arg3): ## timp: gs_print_a3(799)
          pyxtnm166 = arg1
          pyxtnm167 = arg2
          pyxtnm168 = arg3
          ## I1CMP:start
          ## let
          pyxtnm203 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
          ## I1VALDCL
          pyxtnm172 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm170(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm169 = XATSTUP0([])
            ## I1CMP:return:pyxtnm169
            return pyxtnm169
          ## endtimp(gs_print$beg(793))
          pyxtnm171 = XATSDAPP(pyxtnm170())
          pyxtnm172 = pyxtnm171
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6828])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm178 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm177(arg1): ## timp: strn_print(1029)
            pyxtnm173 = arg1
            ## I1CMP:start
            ## let
            pyxtnm176 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(174);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(174))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm175 = XATSDAPP(XATS2PY_strn_print(pyxtnm173))
            pyxtnm176 = pyxtnm175
            ## end-of(let)
            ## I1CMP:return:pyxtnm176
            return pyxtnm176
          ## endtimp(strn_print(1029))
          pyxtnm178 = pyxtnm177
          pyxtnm179 = XATSDAPP(pyxtnm178(pyxtnm166))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm181(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm180 = XATSTUP0([])
            ## I1CMP:return:pyxtnm180
            return pyxtnm180
          ## endtimp(gs_print$sep(794))
          pyxtnm182 = XATSDAPP(pyxtnm181())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6829])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm188 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm187(arg1): ## timp: strn_print(1029)
            pyxtnm183 = arg1
            ## I1CMP:start
            ## let
            pyxtnm186 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(184);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(184))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm185 = XATSDAPP(XATS2PY_strn_print(pyxtnm183))
            pyxtnm186 = pyxtnm185
            ## end-of(let)
            ## I1CMP:return:pyxtnm186
            return pyxtnm186
          ## endtimp(strn_print(1029))
          pyxtnm188 = pyxtnm187
          pyxtnm189 = XATSDAPP(pyxtnm188(pyxtnm167))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm191(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm190 = XATSTUP0([])
            ## I1CMP:return:pyxtnm190
            return pyxtnm190
          ## endtimp(gs_print$sep(794))
          pyxtnm192 = XATSDAPP(pyxtnm191())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6830])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm198 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm197(arg1): ## timp: strn_print(1029)
            pyxtnm193 = arg1
            ## I1CMP:start
            ## let
            pyxtnm196 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(194);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(194))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm195 = XATSDAPP(XATS2PY_strn_print(pyxtnm193))
            pyxtnm196 = pyxtnm195
            ## end-of(let)
            ## I1CMP:return:pyxtnm196
            return pyxtnm196
          ## endtimp(strn_print(1029))
          pyxtnm198 = pyxtnm197
          pyxtnm199 = XATSDAPP(pyxtnm198(pyxtnm168))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm201(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm200 = XATSTUP0([])
            ## I1CMP:return:pyxtnm200
            return pyxtnm200
          ## endtimp(gs_print$end(795))
          pyxtnm202 = XATSDAPP(pyxtnm201())
          pyxtnm203 = pyxtnm202
          ## end-of(let)
          ## I1CMP:return:pyxtnm203
          return pyxtnm203
        ## endtimp(gs_print_a3(799))
        pyxtnm205 = XATSDAPP(pyxtnm204(XATSSTRN("TMvar("), XATSP1CN("TMvar", pyxtnm165[0+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm205
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(206);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5157)),I0Pvar(tmx(5158))));$list(@(x01(5157),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(206));0)),@(tmx(5158),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(206));1)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMlam",3))): ## { // gpt
        pyxtnm206 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(1872(line=129,offs=1)--1878(line=129,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a5(801), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
        ## T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6835],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6836],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6837],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6838],T2Pcst(term)),@(x4[6839],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2403],T2Pvar(x0[6835])),@(x1[2404],T2Pvar(x1[6836])),@(x2[2405],T2Pvar(x2[6837])),@(x3[2406],T2Pvar(x3[6838])),@(x4[2407],T2Pvar(x4[6839])))))))
        def pyxtnm262(arg1, arg2, arg3, arg4, arg5): ## timp: gs_print_a5(801)
          pyxtnm207 = arg1
          pyxtnm208 = arg2
          pyxtnm209 = arg3
          pyxtnm210 = arg4
          pyxtnm211 = arg5
          ## I1CMP:start
          ## let
          pyxtnm261 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
          ## I1VALDCL
          pyxtnm215 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm213(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm212 = XATSTUP0([])
            ## I1CMP:return:pyxtnm212
            return pyxtnm212
          ## endtimp(gs_print$beg(793))
          pyxtnm214 = XATSDAPP(pyxtnm213())
          pyxtnm215 = pyxtnm214
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6835])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm221 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm220(arg1): ## timp: strn_print(1029)
            pyxtnm216 = arg1
            ## I1CMP:start
            ## let
            pyxtnm219 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(217);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(217))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm218 = XATSDAPP(XATS2PY_strn_print(pyxtnm216))
            pyxtnm219 = pyxtnm218
            ## end-of(let)
            ## I1CMP:return:pyxtnm219
            return pyxtnm219
          ## endtimp(strn_print(1029))
          pyxtnm221 = pyxtnm220
          pyxtnm222 = XATSDAPP(pyxtnm221(pyxtnm207))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm224(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm223 = XATSTUP0([])
            ## I1CMP:return:pyxtnm223
            return pyxtnm223
          ## endtimp(gs_print$sep(794))
          pyxtnm225 = XATSDAPP(pyxtnm224())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6836])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm231 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm230(arg1): ## timp: strn_print(1029)
            pyxtnm226 = arg1
            ## I1CMP:start
            ## let
            pyxtnm229 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(227);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(227))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm228 = XATSDAPP(XATS2PY_strn_print(pyxtnm226))
            pyxtnm229 = pyxtnm228
            ## end-of(let)
            ## I1CMP:return:pyxtnm229
            return pyxtnm229
          ## endtimp(strn_print(1029))
          pyxtnm231 = pyxtnm230
          pyxtnm232 = XATSDAPP(pyxtnm231(pyxtnm208))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm234(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm233 = XATSTUP0([])
            ## I1CMP:return:pyxtnm233
            return pyxtnm233
          ## endtimp(gs_print$sep(794))
          pyxtnm235 = XATSDAPP(pyxtnm234())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6837])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm241 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm240(arg1): ## timp: strn_print(1029)
            pyxtnm236 = arg1
            ## I1CMP:start
            ## let
            pyxtnm239 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(237);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(237))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm238 = XATSDAPP(XATS2PY_strn_print(pyxtnm236))
            pyxtnm239 = pyxtnm238
            ## end-of(let)
            ## I1CMP:return:pyxtnm239
            return pyxtnm239
          ## endtimp(strn_print(1029))
          pyxtnm241 = pyxtnm240
          pyxtnm242 = XATSDAPP(pyxtnm241(pyxtnm209))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm244(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm243 = XATSTUP0([])
            ## I1CMP:return:pyxtnm243
            return pyxtnm243
          ## endtimp(gs_print$sep(794))
          pyxtnm245 = XATSDAPP(pyxtnm244())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6838])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm246 = None
          pyxtnm246 = auxpr_1677
          pyxtnm247 = XATSDAPP(pyxtnm246(pyxtnm210))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm249(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm248 = XATSTUP0([])
            ## I1CMP:return:pyxtnm248
            return pyxtnm248
          ## endtimp(gs_print$sep(794))
          pyxtnm250 = XATSDAPP(pyxtnm249())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6839])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm256 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm255(arg1): ## timp: strn_print(1029)
            pyxtnm251 = arg1
            ## I1CMP:start
            ## let
            pyxtnm254 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(252);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(252))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm253 = XATSDAPP(XATS2PY_strn_print(pyxtnm251))
            pyxtnm254 = pyxtnm253
            ## end-of(let)
            ## I1CMP:return:pyxtnm254
            return pyxtnm254
          ## endtimp(strn_print(1029))
          pyxtnm256 = pyxtnm255
          pyxtnm257 = XATSDAPP(pyxtnm256(pyxtnm211))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm259(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm258 = XATSTUP0([])
            ## I1CMP:return:pyxtnm258
            return pyxtnm258
          ## endtimp(gs_print$end(795))
          pyxtnm260 = XATSDAPP(pyxtnm259())
          pyxtnm261 = pyxtnm260
          ## end-of(let)
          ## I1CMP:return:pyxtnm261
          return pyxtnm261
        ## endtimp(gs_print_a5(801))
        pyxtnm263 = XATSDAPP(pyxtnm262(XATSSTRN("TMlam("), XATSP1CN("TMlam", pyxtnm206[0+1]), XATSSTRN(";"), XATSP1CN("TMlam", pyxtnm206[1+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm263
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(264);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5159)),I0Pvar(tm2(5160))));$list(@(tm1(5159),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(264));0)),@(tm2(5160),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(264));1)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMapp",4))): ## { // gpt
        pyxtnm264 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(1930(line=132,offs=1)--1936(line=132,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a5(801), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
        ## T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6835],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6836],T2Pcst(term)),@(x2[6837],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6838],T2Pcst(term)),@(x4[6839],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2403],T2Pvar(x0[6835])),@(x1[2404],T2Pvar(x1[6836])),@(x2[2405],T2Pvar(x2[6837])),@(x3[2406],T2Pvar(x3[6838])),@(x4[2407],T2Pvar(x4[6839])))))))
        def pyxtnm315(arg1, arg2, arg3, arg4, arg5): ## timp: gs_print_a5(801)
          pyxtnm265 = arg1
          pyxtnm266 = arg2
          pyxtnm267 = arg3
          pyxtnm268 = arg4
          pyxtnm269 = arg5
          ## I1CMP:start
          ## let
          pyxtnm314 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
          ## I1VALDCL
          pyxtnm273 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm271(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm270 = XATSTUP0([])
            ## I1CMP:return:pyxtnm270
            return pyxtnm270
          ## endtimp(gs_print$beg(793))
          pyxtnm272 = XATSDAPP(pyxtnm271())
          pyxtnm273 = pyxtnm272
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6835])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm279 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm278(arg1): ## timp: strn_print(1029)
            pyxtnm274 = arg1
            ## I1CMP:start
            ## let
            pyxtnm277 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(275);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(275))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm276 = XATSDAPP(XATS2PY_strn_print(pyxtnm274))
            pyxtnm277 = pyxtnm276
            ## end-of(let)
            ## I1CMP:return:pyxtnm277
            return pyxtnm277
          ## endtimp(strn_print(1029))
          pyxtnm279 = pyxtnm278
          pyxtnm280 = XATSDAPP(pyxtnm279(pyxtnm265))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm282(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm281 = XATSTUP0([])
            ## I1CMP:return:pyxtnm281
            return pyxtnm281
          ## endtimp(gs_print$sep(794))
          pyxtnm283 = XATSDAPP(pyxtnm282())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6836])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm284 = None
          pyxtnm284 = auxpr_1677
          pyxtnm285 = XATSDAPP(pyxtnm284(pyxtnm266))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm287(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm286 = XATSTUP0([])
            ## I1CMP:return:pyxtnm286
            return pyxtnm286
          ## endtimp(gs_print$sep(794))
          pyxtnm288 = XATSDAPP(pyxtnm287())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6837])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm294 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm293(arg1): ## timp: strn_print(1029)
            pyxtnm289 = arg1
            ## I1CMP:start
            ## let
            pyxtnm292 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(290);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(290))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm291 = XATSDAPP(XATS2PY_strn_print(pyxtnm289))
            pyxtnm292 = pyxtnm291
            ## end-of(let)
            ## I1CMP:return:pyxtnm292
            return pyxtnm292
          ## endtimp(strn_print(1029))
          pyxtnm294 = pyxtnm293
          pyxtnm295 = XATSDAPP(pyxtnm294(pyxtnm267))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm297(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm296 = XATSTUP0([])
            ## I1CMP:return:pyxtnm296
            return pyxtnm296
          ## endtimp(gs_print$sep(794))
          pyxtnm298 = XATSDAPP(pyxtnm297())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6838])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm299 = None
          pyxtnm299 = auxpr_1677
          pyxtnm300 = XATSDAPP(pyxtnm299(pyxtnm268))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm302(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm301 = XATSTUP0([])
            ## I1CMP:return:pyxtnm301
            return pyxtnm301
          ## endtimp(gs_print$sep(794))
          pyxtnm303 = XATSDAPP(pyxtnm302())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6839])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm309 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm308(arg1): ## timp: strn_print(1029)
            pyxtnm304 = arg1
            ## I1CMP:start
            ## let
            pyxtnm307 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(305);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(305))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm306 = XATSDAPP(XATS2PY_strn_print(pyxtnm304))
            pyxtnm307 = pyxtnm306
            ## end-of(let)
            ## I1CMP:return:pyxtnm307
            return pyxtnm307
          ## endtimp(strn_print(1029))
          pyxtnm309 = pyxtnm308
          pyxtnm310 = XATSDAPP(pyxtnm309(pyxtnm269))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm312(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm311 = XATSTUP0([])
            ## I1CMP:return:pyxtnm311
            return pyxtnm311
          ## endtimp(gs_print$end(795))
          pyxtnm313 = XATSDAPP(pyxtnm312())
          pyxtnm314 = pyxtnm313
          ## end-of(let)
          ## I1CMP:return:pyxtnm314
          return pyxtnm314
        ## endtimp(gs_print_a5(801))
        pyxtnm316 = XATSDAPP(pyxtnm315(XATSSTRN("TMapp("), XATSP1CN("TMapp", pyxtnm264[0+1]), XATSSTRN(";"), XATSP1CN("TMapp", pyxtnm264[1+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm316
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(317);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(opr(5161)),I0Pvar(tms(5162))));$list(@(opr(5161),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(317));0)),@(tms(5162),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(317));1)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMopr",5))): ## { // gpt
        pyxtnm317 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(1991(line=136,offs=1)--1997(line=136,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a5(801), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
        ## T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6835],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6836],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6837],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6838],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x4[6839],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2403],T2Pvar(x0[6835])),@(x1[2404],T2Pvar(x1[6836])),@(x2[2405],T2Pvar(x2[6837])),@(x3[2406],T2Pvar(x3[6838])),@(x4[2407],T2Pvar(x4[6839])))))))
        def pyxtnm647(arg1, arg2, arg3, arg4, arg5): ## timp: gs_print_a5(801)
          pyxtnm318 = arg1
          pyxtnm319 = arg2
          pyxtnm320 = arg3
          pyxtnm321 = arg4
          pyxtnm322 = arg5
          ## I1CMP:start
          ## let
          pyxtnm646 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
          ## I1VALDCL
          pyxtnm326 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm324(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm323 = XATSTUP0([])
            ## I1CMP:return:pyxtnm323
            return pyxtnm323
          ## endtimp(gs_print$beg(793))
          pyxtnm325 = XATSDAPP(pyxtnm324())
          pyxtnm326 = pyxtnm325
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6835])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm332 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm331(arg1): ## timp: strn_print(1029)
            pyxtnm327 = arg1
            ## I1CMP:start
            ## let
            pyxtnm330 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(328);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(328))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm329 = XATSDAPP(XATS2PY_strn_print(pyxtnm327))
            pyxtnm330 = pyxtnm329
            ## end-of(let)
            ## I1CMP:return:pyxtnm330
            return pyxtnm330
          ## endtimp(strn_print(1029))
          pyxtnm332 = pyxtnm331
          pyxtnm333 = XATSDAPP(pyxtnm332(pyxtnm318))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm335(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm334 = XATSTUP0([])
            ## I1CMP:return:pyxtnm334
            return pyxtnm334
          ## endtimp(gs_print$sep(794))
          pyxtnm336 = XATSDAPP(pyxtnm335())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6836])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm342 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm341(arg1): ## timp: strn_print(1029)
            pyxtnm337 = arg1
            ## I1CMP:start
            ## let
            pyxtnm340 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(338);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(338))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm339 = XATSDAPP(XATS2PY_strn_print(pyxtnm337))
            pyxtnm340 = pyxtnm339
            ## end-of(let)
            ## I1CMP:return:pyxtnm340
            return pyxtnm340
          ## endtimp(strn_print(1029))
          pyxtnm342 = pyxtnm341
          pyxtnm343 = XATSDAPP(pyxtnm342(pyxtnm319))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm345(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm344 = XATSTUP0([])
            ## I1CMP:return:pyxtnm344
            return pyxtnm344
          ## endtimp(gs_print$sep(794))
          pyxtnm346 = XATSDAPP(pyxtnm345())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6837])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm352 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm351(arg1): ## timp: strn_print(1029)
            pyxtnm347 = arg1
            ## I1CMP:start
            ## let
            pyxtnm350 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(348);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(348))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm349 = XATSDAPP(XATS2PY_strn_print(pyxtnm347))
            pyxtnm350 = pyxtnm349
            ## end-of(let)
            ## I1CMP:return:pyxtnm350
            return pyxtnm350
          ## endtimp(strn_print(1029))
          pyxtnm352 = pyxtnm351
          pyxtnm353 = XATSDAPP(pyxtnm352(pyxtnm320))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm355(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm354 = XATSTUP0([])
            ## I1CMP:return:pyxtnm354
            return pyxtnm354
          ## endtimp(gs_print$sep(794))
          pyxtnm356 = XATSDAPP(pyxtnm355())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6838])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3531(line=203,offs=1)--3606(line=208,offs=30)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))))>;I1Dtmpsub($list(@(x0[7226],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7226])))))))))
          def pyxtnm631(arg1): ## timp: g_print(39)
            pyxtnm357 = arg1
            ## I1CMP:start
            ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3577(line=208,offs=1)--3587(line=208,offs=11))
            ## I0Etapq(I0Ecst(gseq_print(347)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2894(line=179,offs=1)--2904(line=179,offs=11))));$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pvar(x0[7226]),T2Pnone0())))),T2JAG($list(T2Pvar(x0[7226])))))
            ## T1IMPallx(gseq_print(347), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(2803(line=154,offs=1)--2864(line=157,offs=33)))
            ## T1IMPallx(gseq_print(347)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5874],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5875],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_print(347);$list(@(xs[995],T2Pvar(xs[5874])),@(x0[996],T2Pvar(x0[5875])))))))
            pyxtnm629 = None
            ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(2845(line=157,offs=14)--2856(line=157,offs=25))
            ## I0Etapq(I0Ecst(gseq_print0(1658)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gseq000_vt.sats)@(3950(line=241,offs=1)--3961(line=241,offs=12))));$list(T2JAG($list(T2Pvar(xs[5874]))),T2JAG($list(T2Pvar(x0[5875])))))
            ## T1IMPallx(gseq_print0(1658), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3715(line=210,offs=1)--4381(line=277,offs=7)))
            ## T1IMPallx(gseq_print0(1658)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[7693],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[7694],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_print0(1658);$list(@(xs[4057],T2Pvar(xs[7693])),@(x0[4058],T2Pvar(x0[7694])))))))
            def pyxtnm628(arg1): ## timp: gseq_print0(1658)
              pyxtnm358 = arg1
              ## I1CMP:start
              ## let
              pyxtnm627 = None
              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3769(line=216,offs=1)--3811(line=218,offs=21)))
              ## I1VALDCL
              pyxtnm367 = None
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3778(line=217,offs=1)--3788(line=217,offs=11))
              ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
              ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
              ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
              def pyxtnm363(arg1): ## timp: strn_print(1029)
                pyxtnm359 = arg1
                ## I1CMP:start
                ## let
                pyxtnm362 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(360);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(360))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                pyxtnm361 = XATSDAPP(XATS2PY_strn_print(pyxtnm359))
                pyxtnm362 = pyxtnm361
                ## end-of(let)
                ## I1CMP:return:pyxtnm362
                return pyxtnm362
              ## endtimp(strn_print(1029))
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3792(line=218,offs=2)--3800(line=218,offs=10))
              ## I0Etapq(I0Ecst(gseq$beg(340)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2390(line=130,offs=1)--2398(line=130,offs=9))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
              ## T1IMPallx(gseq$beg(340), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3473(line=198,offs=1)--3527(line=201,offs=27)))
              ## T1IMPallx(gseq$beg(340)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7225],T2Pcst(term)),@(x0[7225],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$beg(340);$list(@(xs[981],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7225])))),@(x0[982],T2Pvar(x0[7225])))))))
              def pyxtnm364(): ## timp: gseq$beg(340)
                ## I1CMP:start
                ## I1CMP:return:XATSSTRN("list(")
                return XATSSTRN("list(")
              ## endtimp(gseq$beg(340))
              pyxtnm365 = XATSDAPP(pyxtnm364())
              pyxtnm366 = XATSDAPP(pyxtnm363(pyxtnm365))
              pyxtnm367 = pyxtnm366
              XATS000_patck(True)
              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3815(line=220,offs=1)--4326(line=272,offs=2)))
              ## I1VALDCL
              pyxtnm617 = None
              ## let
              pyxtnm616 = None
              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3927(line=234,offs=1)--3964(line=236,offs=27)))
              ## I1VALDCL
              pyxtnm376 = None
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3938(line=236,offs=1)--3948(line=236,offs=11))
              ## I0Etapq(I0Ecst(gseq$prlen(344)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2565(line=148,offs=1)--2575(line=148,offs=11))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
              ## T1IMPallx(gseq$prlen(344), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(1709(line=64,offs=1)--1764(line=67,offs=27)))
              ## T1IMPallx(gseq$prlen(344)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5852],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5853],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$prlen(344);$list(@(xs[989],T2Pvar(xs[5852])),@(x0[990],T2Pvar(x0[5853])))))))
              def pyxtnm374(): ## timp: gseq$prlen(344)
                ## I1CMP:start
                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(1760(line=67,offs=23)--1761(line=67,offs=24))
                ## I0Etapq(I0Ecst(sint_neg(914)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(1585(line=55,offs=1)--1593(line=55,offs=9))));$list(T2JAG($list())))
                ## T1IMPallx(sint_neg(914), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1430(line=40,offs=1)--1565(line=51,offs=31)))
                ## T1IMPallx(sint_neg(914)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_neg(914);$list()))))
                def pyxtnm372(arg1): ## timp: sint_neg(914)
                  pyxtnm368 = arg1
                  ## I1CMP:start
                  ## let
                  pyxtnm371 = None
                  ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1506(line=48,offs=1)--1563(line=51,offs=29)))
                  ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_neg(2577));$list(I1FUNDCL(XATS2PY_sint_neg(4867);$list(FJARGdarg($list(I1BNDcons(I1TNM(369);I0Pvar(i1(4868));$list(@(i1(4868),I1Vtnm(I1TNM(369))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_neg);G1Nlist($list())))))))
                  pyxtnm370 = XATSDAPP(XATS2PY_sint_neg(pyxtnm368))
                  pyxtnm371 = pyxtnm370
                  ## end-of(let)
                  ## I1CMP:return:pyxtnm371
                  return pyxtnm371
                ## endtimp(sint_neg(914))
                pyxtnm373 = XATSDAPP(pyxtnm372(XATSINT1(1)))
                ## I1CMP:return:pyxtnm373
                return pyxtnm373
              ## endtimp(gseq$prlen(344))
              pyxtnm375 = XATSDAPP(pyxtnm374())
              pyxtnm376 = pyxtnm375
              XATS000_patck(True)
              ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3968(line=238,offs=1)--4093(line=246,offs=32)))
              ## I1Dimplmnt0(DIMPLone2(iforitm$work0(1435);$list(@(x0[3652],T2Pvar(x0[7694]))))):timp
              ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4097(line=248,offs=1)--4321(line=270,offs=32)))
              ## I1Dimplmnt0(DIMPLone2(iforall$test0(1419);$list(@(x0[3636],T2Pvar(x0[7694]))))):timp
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3833(line=223,offs=5)--3835(line=223,offs=7))
              ## I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
              ## T1IMPallx(sint_gte$sint(922), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
              ## T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
              def pyxtnm407(arg1, arg2): ## timp: sint_gte$sint(922)
                pyxtnm401 = arg1
                pyxtnm402 = arg2
                ## I1CMP:start
                ## let
                pyxtnm406 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gte$sint(2582));$list(I1FUNDCL(XATS2PY_sint_gte$sint(4891);$list(FJARGdarg($list(I1BNDcons(I1TNM(403);I0Pvar(i1(4892));$list(@(i1(4892),I1Vtnm(I1TNM(403))))),I1BNDcons(I1TNM(404);I0Pvar(i2(4893));$list(@(i2(4893),I1Vtnm(I1TNM(404))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gte$sint);G1Nlist($list())))))))
                pyxtnm405 = XATSDAPP(XATS2PY_sint_gte_sint(pyxtnm401, pyxtnm402))
                pyxtnm406 = pyxtnm405
                ## end-of(let)
                ## I1CMP:return:pyxtnm406
                return pyxtnm406
              ## endtimp(sint_gte$sint(922))
              pyxtnm408 = XATSDAPP(pyxtnm407(pyxtnm376, XATSINT1(0)))
              pyxtnm615 = None
              if (pyxtnm408):
                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3844(line=225,offs=1)--3850(line=225,offs=7))
                ## I0Etapq(I0Ecst(g_void(21)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(1486(line=46,offs=1)--1492(line=46,offs=7))));$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))))))
                ## T1IMPallx(g_void(21), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gbas000.dats)@(1416(line=41,offs=1)--1455(line=43,offs=21)))
                ## T1IMPallx(g_void(21)<$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5571],T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_void(21);$list(@(a[363],T2Pvar(x0[5571])))))))
                def pyxtnm411(arg1): ## timp: g_void(21)
                  pyxtnm409 = arg1
                  ## I1CMP:start
                  pyxtnm410 = XATSTUP0([])
                  ## I1CMP:return:pyxtnm410
                  return pyxtnm410
                ## endtimp(g_void(21))
                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3853(line=227,offs=1)--3866(line=227,offs=14))
                ## I0Etapq(I0Ecst(gseq_iforall0(1708)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gseq001_vt.sats)@(6472(line=342,offs=1)--6485(line=342,offs=14))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
                ## T1IMPallx(gseq_iforall0(1708), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2821(line=159,offs=1)--2955(line=169,offs=2)))
                ## T1IMPallx(gseq_iforall0(1708)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8589],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8590],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforall0(1708);$list(@(xs[4195],T2Pvar(xs[8589])),@(x0[4196],T2Pvar(x0[8590])))))))
                def pyxtnm512(arg1): ## timp: gseq_iforall0(1708)
                  pyxtnm412 = arg1
                  ## I1CMP:start
                  ## let
                  pyxtnm511 = None
                  ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2908(line=167,offs=1)--2953(line=168,offs=37)))
                  ## I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[396],T2Pvar(x0[8590]))))):timp
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2874(line=164,offs=3)--2886(line=164,offs=15))
                  ## I0Etapq(I0Ecst(gseq_iforall(384)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3907(line=226,offs=1)--3919(line=226,offs=13))));$list(T2JAG($list(T2Pvar(xs[8589]))),T2JAG($list(T2Pvar(x0[8590])))))
                  ## T1IMPallx(gseq_iforall(384), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4419(line=260,offs=1)--4718(line=286,offs=2)))
                  ## T1IMPallx(gseq_iforall(384)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5920],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5921],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforall(384);$list(@(xs[1089],T2Pvar(xs[5920])),@(x0[1090],T2Pvar(x0[5921])))))))
                  def pyxtnm509(arg1): ## timp: gseq_iforall(384)
                    pyxtnm413 = arg1
                    ## I1CMP:start
                    ## let
                    pyxtnm508 = None
                    ## I1Dvardclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4486(line=267,offs=1)--4502(line=267,offs=17)))
                    ## I1VARDCL
                    ## I1CMP:start
                    ## I1CMP:return:XATSINT1(0)
                    pyxtnm414 = XATSVAR1(XATSINT1(0))
                    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4506(line=269,offs=1)--4524(line=269,offs=19)))
                    ## I1VALDCL
                    pyxtnm415 = None
                    pyxtnm415 = XATSADDR(pyxtnm414)
                    XATS000_patck(True)
                    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4528(line=271,offs=1)--4713(line=284,offs=2)))
                    ## I1VALDCL
                    pyxtnm507 = None
                    ## let
                    pyxtnm506 = None
                    ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                    ## I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[394],T2Pvar(x0[5921]))))):timp
                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4539(line=273,offs=1)--4550(line=273,offs=12))
                    ## I0Etapq(I0Ecst(gseq_forall(380)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3721(line=210,offs=1)--3732(line=210,offs=12))));$list(T2JAG($list(T2Pvar(xs[5920]))),T2JAG($list(T2Pvar(x0[5921])))))
                    ## T1IMPallx(gseq_forall(380), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1841(line=78,offs=1)--1904(line=81,offs=33)))
                    ## T1IMPallx(gseq_forall(380)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7275],T2Pcst(term)),@(x0[7275],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_forall(380);$list(@(xs[1081],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7275])))),@(x0[1082],T2Pvar(x0[7275])))))))
                    pyxtnm504 = None
                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1889(line=81,offs=18)--1900(line=81,offs=29))
                    ## I0Etapq(I0Ecst(list_forall(1206)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(2160(line=92,offs=1)--2171(line=92,offs=12))));$list(T2JAG($list(T2Pvar(x0[7275])))))
                    ## T1IMPallx(list_forall(1206), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1591(line=53,offs=1)--1837(line=76,offs=2)))
                    ## T1IMPallx(list_forall(1206)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7274],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_forall(1206);$list(@(x0[3286],T2Pvar(x0[7274])))))))
                    def pyxtnm503(arg1): ## timp: list_forall(1206)
                      pyxtnm424 = arg1
                      ## I1CMP:start
                      ## let
                      pyxtnm502 = None
                      ## I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1657(line=60,offs=1)--1835(line=75,offs=31)))
                      ## I1FUNDCL
                      def loop_1660(arg1): ## fun
                        pyxtnm425 = arg1
                        ## I1CMP:start
                        pyxtnm500 = None
                        while True: ## do {
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(426);I0Pfree(I0Pdapp(I0Pcon(list_nil(8));$list()));$list()))
                          if (XATS000_ctgeq(pyxtnm425, XATSCTAG("list_nil",0))): ## { // gpt
                            pyxtnm426 = pyxtnm425
                            pyxtnm500 = XATSBOOL(True)
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(427);I0Pfree(I0Pdapp(I0Pcon(list_cons(9));$list(I0Pvar(x1(2569)),I0Pvar(xs(2570)))));$list(@(x1(2569),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(427));0)),@(xs(2570),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(427));1)))))
                          if (XATS000_ctgeq(pyxtnm425, XATSCTAG("list_cons",1))): ## { // gpt
                            pyxtnm427 = pyxtnm425
                            ## let
                            pyxtnm499 = None
                            ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1761(line=71,offs=1)--1791(line=72,offs=20)))
                            ## I1VALDCL
                            pyxtnm496 = None
                            ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1772(line=72,offs=1)--1783(line=72,offs=12))
                            ## I0Etapq(I0Ecst(forall$test(47)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2003(line=96,offs=1)--2014(line=96,offs=12))));$list(T2JAG($list(T2Pvar(x0[7274])))))
                            ## T1IMPallx(forall$test(47), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                            ## T1IMPallx(forall$test(47)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5920],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5921],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[394],T2Pcst(term)))))))
                            def pyxtnm494(arg1): ## timp: forall$test(47)
                              pyxtnm428 = arg1
                              ## I1CMP:start
                              ## let
                              pyxtnm493 = None
                              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4646(line=282,offs=1)--4675(line=282,offs=30)))
                              ## I1VALDCL
                              pyxtnm433 = None
                              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4659(line=282,offs=14)--4667(line=282,offs=22))
                              ## I0Etapq(I0Ecst(p2tr_get(2280)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2573(line=124,offs=1)--2581(line=124,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                              ## T1IMPallx(p2tr_get(2280), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(197(line=15,offs=1)--245(line=18,offs=17)))
                              ## T1IMPallx(p2tr_get(2280)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5726],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_get(2280);$list(@(a[5528],T2Pvar(a[5726])))))))
                              def pyxtnm431(arg1): ## timp: p2tr_get(2280)
                                pyxtnm429 = arg1
                                ## I1CMP:start
                                pyxtnm430 = XATS000_dp2tr(pyxtnm429)
                                ## I1CMP:return:pyxtnm430
                                return pyxtnm430
                              ## endtimp(p2tr_get(2280))
                              pyxtnm432 = XATSDAPP(pyxtnm431(pyxtnm415))
                              pyxtnm433 = pyxtnm432
                              XATS000_patck(True)
                              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4676(line=283,offs=1)--4709(line=283,offs=34)))
                              ## I1VALDCL
                              pyxtnm480 = None
                              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4685(line=283,offs=10)--4697(line=283,offs=22))
                              ## I0Etapq(I0Ecst(iforall$test(49)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2080(line=102,offs=1)--2092(line=102,offs=13))));$list(T2JAG($list(T2Pvar(x0[5921])))))
                              ## T1IMPallx(iforall$test(49), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2908(line=167,offs=1)--2953(line=168,offs=37)))
                              ## T1IMPallx(iforall$test(49)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8589],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8590],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[396],T2Pcst(term)))))))
                              pyxtnm478 = None
                              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(2936(line=168,offs=20)--2949(line=168,offs=33))
                              ## I0Etapq(I0Ecst(iforall$test0(1419)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas001_vt.sats)@(2570(line=145,offs=1)--2583(line=145,offs=14))));$list(T2JAG($list(T2Pvar(x0[8590])))))
                              ## T1IMPallx(iforall$test0(1419), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4097(line=248,offs=1)--4321(line=270,offs=32)))
                              ## T1IMPallx(iforall$test0(1419)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[7693],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[7694],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforall$test0(1419);$list(@(x0[3636],T2Pcst(term)))))))
                              def pyxtnm477(arg1, arg2): ## timp: iforall$test0(1419)
                                pyxtnm434 = arg1
                                pyxtnm435 = arg2
                                ## I1CMP:start
                                ## let
                                pyxtnm476 = None
                                ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4266(line=268,offs=1)--4320(line=270,offs=31)))
                                ## I1VALDCL
                                pyxtnm453 = None
                                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4281(line=269,offs=7)--4282(line=269,offs=8))
                                ## I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
                                ## T1IMPallx(sint_gt$sint(919), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
                                ## T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
                                def pyxtnm442(arg1, arg2): ## timp: sint_gt$sint(919)
                                  pyxtnm436 = arg1
                                  pyxtnm437 = arg2
                                  ## I1CMP:start
                                  ## let
                                  pyxtnm441 = None
                                  ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
                                  ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gt$sint(2579));$list(I1FUNDCL(XATS2PY_sint_gt$sint(4876);$list(FJARGdarg($list(I1BNDcons(I1TNM(438);I0Pvar(i1(4877));$list(@(i1(4877),I1Vtnm(I1TNM(438))))),I1BNDcons(I1TNM(439);I0Pvar(i2(4878));$list(@(i2(4878),I1Vtnm(I1TNM(439))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gt$sint);G1Nlist($list())))))))
                                  pyxtnm440 = XATSDAPP(XATS2PY_sint_gt_sint(pyxtnm436, pyxtnm437))
                                  pyxtnm441 = pyxtnm440
                                  ## end-of(let)
                                  ## I1CMP:return:pyxtnm441
                                  return pyxtnm441
                                ## endtimp(sint_gt$sint(919))
                                pyxtnm443 = XATSDAPP(pyxtnm442(pyxtnm434, XATSINT1(0)))
                                pyxtnm452 = None
                                if (pyxtnm443):
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4290(line=270,offs=1)--4300(line=270,offs=11))
                                  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                                  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
                                  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                                  def pyxtnm448(arg1): ## timp: strn_print(1029)
                                    pyxtnm444 = arg1
                                    ## I1CMP:start
                                    ## let
                                    pyxtnm447 = None
                                    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                                    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(445);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(445))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                                    pyxtnm446 = XATSDAPP(XATS2PY_strn_print(pyxtnm444))
                                    pyxtnm447 = pyxtnm446
                                    ## end-of(let)
                                    ## I1CMP:return:pyxtnm447
                                    return pyxtnm447
                                  ## endtimp(strn_print(1029))
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4301(line=270,offs=12)--4309(line=270,offs=20))
                                  ## I0Etapq(I0Ecst(gseq$sep(342)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2474(line=138,offs=1)--2482(line=138,offs=9))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
                                  ## T1IMPallx(gseq$sep(342), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3371(line=190,offs=1)--3421(line=193,offs=23)))
                                  ## T1IMPallx(gseq$sep(342)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7223],T2Pcst(term)),@(x0[7223],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$sep(342);$list(@(xs[985],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7223])))),@(x0[986],T2Pvar(x0[7223])))))))
                                  def pyxtnm449(): ## timp: gseq$sep(342)
                                    ## I1CMP:start
                                    ## I1CMP:return:XATSSTRN(",")
                                    return XATSSTRN(",")
                                  ## endtimp(gseq$sep(342))
                                  pyxtnm450 = XATSDAPP(pyxtnm449())
                                  pyxtnm451 = XATSDAPP(pyxtnm448(pyxtnm450))
                                  pyxtnm452 = pyxtnm451
                                ## else: None
                                ## end-of(if)
                                pyxtnm453 = pyxtnm452
                                XATS000_patck(True)
                                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4145(line=253,offs=4)--4147(line=253,offs=6))
                                ## I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
                                ## T1IMPallx(sint_gte$sint(922), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
                                ## T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
                                def pyxtnm460(arg1, arg2): ## timp: sint_gte$sint(922)
                                  pyxtnm454 = arg1
                                  pyxtnm455 = arg2
                                  ## I1CMP:start
                                  ## let
                                  pyxtnm459 = None
                                  ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
                                  ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gte$sint(2582));$list(I1FUNDCL(XATS2PY_sint_gte$sint(4891);$list(FJARGdarg($list(I1BNDcons(I1TNM(456);I0Pvar(i1(4892));$list(@(i1(4892),I1Vtnm(I1TNM(456))))),I1BNDcons(I1TNM(457);I0Pvar(i2(4893));$list(@(i2(4893),I1Vtnm(I1TNM(457))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gte$sint);G1Nlist($list())))))))
                                  pyxtnm458 = XATSDAPP(XATS2PY_sint_gte_sint(pyxtnm454, pyxtnm455))
                                  pyxtnm459 = pyxtnm458
                                  ## end-of(let)
                                  ## I1CMP:return:pyxtnm459
                                  return pyxtnm459
                                ## endtimp(sint_gte$sint(922))
                                pyxtnm461 = XATSDAPP(pyxtnm460(pyxtnm434, pyxtnm376))
                                pyxtnm475 = None
                                if (pyxtnm461):
                                  ## let
                                  pyxtnm471 = None
                                  ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4179(line=259,offs=1)--4220(line=261,offs=22)))
                                  ## I1VALDCL
                                  pyxtnm470 = None
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4188(line=260,offs=1)--4198(line=260,offs=11))
                                  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                                  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
                                  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                                  def pyxtnm466(arg1): ## timp: strn_print(1029)
                                    pyxtnm462 = arg1
                                    ## I1CMP:start
                                    ## let
                                    pyxtnm465 = None
                                    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                                    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(463);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(463))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                                    pyxtnm464 = XATSDAPP(XATS2PY_strn_print(pyxtnm462))
                                    pyxtnm465 = pyxtnm464
                                    ## end-of(let)
                                    ## I1CMP:return:pyxtnm465
                                    return pyxtnm465
                                  ## endtimp(strn_print(1029))
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4200(line=261,offs=2)--4209(line=261,offs=11))
                                  ## I0Etapq(I0Ecst(gseq$omit(343)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2519(line=143,offs=1)--2528(line=143,offs=10))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
                                  ## T1IMPallx(gseq$omit(343), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq000.dats)@(1627(line=57,offs=1)--1682(line=60,offs=27)))
                                  ## T1IMPallx(gseq$omit(343)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5850],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5851],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$omit(343);$list(@(xs[987],T2Pvar(xs[5850])),@(x0[988],T2Pvar(x0[5851])))))))
                                  def pyxtnm467(): ## timp: gseq$omit(343)
                                    ## I1CMP:start
                                    ## I1CMP:return:XATSSTRN("...")
                                    return XATSSTRN("...")
                                  ## endtimp(gseq$omit(343))
                                  pyxtnm468 = XATSDAPP(pyxtnm467())
                                  pyxtnm469 = XATSDAPP(pyxtnm466(pyxtnm468))
                                  pyxtnm470 = pyxtnm469
                                  XATS000_patck(True)
                                  pyxtnm471 = XATSBOOL(False)
                                  ## end-of(let)
                                  pyxtnm475 = pyxtnm471
                                else:
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4233(line=265,offs=1)--4241(line=265,offs=9))
                                  ## I0Etapq(I0Ecst(g_print0(1398)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas000_vt.sats)@(2080(line=106,offs=1)--2088(line=106,offs=9))));$list(T2JAG($list(T2Pvar(x0[7694])))))
                                  ## T1IMPallx(g_print0(1398), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1589(line=56,offs=1)--1634(line=58,offs=27)))
                                  ## T1IMPallx(g_print0(1398)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8571],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(g_print0(1398);$list(@(x0[3610],T2Pvar(x0[8571])))))))
                                  pyxtnm473 = None
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1623(line=58,offs=16)--1630(line=58,offs=23))
                                  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[8571])))))
                                  ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                                  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
                                  pyxtnm472 = None
                                  pyxtnm472 = auxpr_1677
                                  pyxtnm473 = pyxtnm472
                                  pyxtnm474 = XATSDAPP(pyxtnm473(pyxtnm435))
                                  pyxtnm475 = XATSBOOL(True)
                                ## end-of(if)
                                pyxtnm476 = pyxtnm475
                                ## end-of(let)
                                ## I1CMP:return:pyxtnm476
                                return pyxtnm476
                              ## endtimp(iforall$test0(1419))
                              pyxtnm478 = pyxtnm477
                              pyxtnm479 = XATSDAPP(pyxtnm478(pyxtnm433, pyxtnm428))
                              pyxtnm480 = pyxtnm479
                              XATS000_patck(True)
                              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4610(line=279,offs=5)--4618(line=279,offs=13))
                              ## I0Etapq(I0Ecst(p2tr_set(2281)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2611(line=127,offs=1)--2619(line=127,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                              ## T1IMPallx(p2tr_set(2281), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(246(line=19,offs=1)--305(line=22,offs=27)))
                              ## T1IMPallx(p2tr_set(2281)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5727],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_set(2281);$list(@(a[5529],T2Pvar(a[5727])))))))
                              def pyxtnm483(arg1, arg2): ## timp: p2tr_set(2281)
                                pyxtnm481 = arg1
                                pyxtnm482 = arg2
                                ## I1CMP:start
                                XATS000_assgn(pyxtnm481, pyxtnm482)
                                ## I1CMP:return:[]
                                return []
                              ## endtimp(p2tr_set(2281))
                              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4629(line=279,offs=24)--4630(line=279,offs=25))
                              ## I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
                              ## T1IMPallx(sint_add$sint(925), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
                              ## T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
                              def pyxtnm490(arg1, arg2): ## timp: sint_add$sint(925)
                                pyxtnm484 = arg1
                                pyxtnm485 = arg2
                                ## I1CMP:start
                                ## let
                                pyxtnm489 = None
                                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
                                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_add$sint(2584));$list(I1FUNDCL(XATS2PY_sint_add$sint(4901);$list(FJARGdarg($list(I1BNDcons(I1TNM(486);I0Pvar(i1(4902));$list(@(i1(4902),I1Vtnm(I1TNM(486))))),I1BNDcons(I1TNM(487);I0Pvar(i2(4903));$list(@(i2(4903),I1Vtnm(I1TNM(487))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_add$sint);G1Nlist($list())))))))
                                pyxtnm488 = XATSDAPP(XATS2PY_sint_add_sint(pyxtnm484, pyxtnm485))
                                pyxtnm489 = pyxtnm488
                                ## end-of(let)
                                ## I1CMP:return:pyxtnm489
                                return pyxtnm489
                              ## endtimp(sint_add$sint(925))
                              pyxtnm491 = XATSDAPP(pyxtnm490(pyxtnm433, XATSINT1(1)))
                              pyxtnm492 = XATSDAPP(pyxtnm483(pyxtnm415, pyxtnm491))
                              pyxtnm493 = pyxtnm480
                              ## end-of(let)
                              ## I1CMP:return:pyxtnm493
                              return pyxtnm493
                            ## endtimp(forall$test(47))
                            pyxtnm495 = XATSDAPP(pyxtnm494(XATSP1CN("list_cons", pyxtnm427[0+1])))
                            pyxtnm496 = pyxtnm495
                            XATS000_patck(True)
                            pyxtnm498 = None
                            if (pyxtnm496):
                              pyxtnm497 = XATSDAPP(loop_1660(XATSP1CN("list_cons", pyxtnm427[1+1])))
                              pyxtnm498 = pyxtnm497
                            else:
                              pyxtnm498 = XATSBOOL(False)
                            ## end-of(if)
                            pyxtnm499 = pyxtnm498
                            ## end-of(let)
                            pyxtnm500 = pyxtnm499
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          XATS000_cfail()
                        ## } while True // end-of(do-cls)
                        ## I1CMP:return:pyxtnm500
                        return pyxtnm500
                      pyxtnm501 = XATSDAPP(loop_1660(pyxtnm424))
                      pyxtnm502 = pyxtnm501
                      ## end-of(let)
                      ## I1CMP:return:pyxtnm502
                      return pyxtnm502
                    ## endtimp(list_forall(1206))
                    pyxtnm504 = pyxtnm503
                    pyxtnm505 = XATSDAPP(pyxtnm504(pyxtnm413))
                    pyxtnm506 = pyxtnm505
                    ## end-of(let)
                    pyxtnm507 = pyxtnm506
                    XATS000_patck(True)
                    pyxtnm508 = pyxtnm507
                    ## end-of(let)
                    ## I1CMP:return:pyxtnm508
                    return pyxtnm508
                  ## endtimp(gseq_iforall(384))
                  pyxtnm510 = XATSDAPP(pyxtnm509(pyxtnm412))
                  pyxtnm511 = pyxtnm510
                  ## end-of(let)
                  ## I1CMP:return:pyxtnm511
                  return pyxtnm511
                ## endtimp(gseq_iforall0(1708))
                pyxtnm513 = XATSDAPP(pyxtnm512(pyxtnm358))
                pyxtnm514 = XATSDAPP(pyxtnm411(pyxtnm513))
                pyxtnm615 = pyxtnm514
              else:
                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3887(line=230,offs=1)--3900(line=230,offs=14))
                ## I0Etapq(I0Ecst(gseq_iforitm0(1732)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gseq001_vt.sats)@(10830(line=584,offs=1)--10843(line=584,offs=14))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
                ## T1IMPallx(gseq_iforitm0(1732), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5533(line=373,offs=1)--5667(line=383,offs=2)))
                ## T1IMPallx(gseq_iforitm0(1732)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8629],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8630],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforitm0(1732);$list(@(xs[4243],T2Pvar(xs[8629])),@(x0[4244],T2Pvar(x0[8630])))))))
                def pyxtnm613(arg1): ## timp: gseq_iforitm0(1732)
                  pyxtnm515 = arg1
                  ## I1CMP:start
                  ## let
                  pyxtnm612 = None
                  ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5620(line=381,offs=1)--5665(line=382,offs=37)))
                  ## I1Dimplmnt0(DIMPLone2(iforitm$work(53);$list(@(x0[400],T2Pvar(x0[8630]))))):timp
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5586(line=378,offs=3)--5598(line=378,offs=15))
                  ## I0Etapq(I0Ecst(gseq_iforitm(398)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(7171(line=410,offs=1)--7183(line=410,offs=13))));$list(T2JAG($list(T2Pvar(xs[8629]))),T2JAG($list(T2Pvar(x0[8630])))))
                  ## T1IMPallx(gseq_iforitm(398), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7318(line=471,offs=1)--7515(line=488,offs=2)))
                  ## T1IMPallx(gseq_iforitm(398)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5944],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5945],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforitm(398);$list(@(xs[1133],T2Pvar(xs[5944])),@(x0[1134],T2Pvar(x0[5945])))))))
                  def pyxtnm610(arg1): ## timp: gseq_iforitm(398)
                    pyxtnm516 = arg1
                    ## I1CMP:start
                    ## let
                    pyxtnm609 = None
                    ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7430(line=483,offs=1)--7513(line=487,offs=36)))
                    ## I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[396],T2Pvar(x0[5945]))))):timp
                    ## let
                    pyxtnm608 = None
                    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7377(line=478,offs=1)--7410(line=480,offs=13)))
                    ## I1VALDCL
                    pyxtnm607 = None
                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7385(line=479,offs=1)--7397(line=479,offs=13))
                    ## I0Etapq(I0Ecst(gseq_iforall(384)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3907(line=226,offs=1)--3919(line=226,offs=13))));$list(T2JAG($list(T2Pvar(xs[5944]))),T2JAG($list(T2Pvar(x0[5945])))))
                    ## T1IMPallx(gseq_iforall(384), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4419(line=260,offs=1)--4718(line=286,offs=2)))
                    ## T1IMPallx(gseq_iforall(384)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5920],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5921],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_iforall(384);$list(@(xs[1089],T2Pvar(xs[5920])),@(x0[1090],T2Pvar(x0[5921])))))))
                    def pyxtnm605(arg1): ## timp: gseq_iforall(384)
                      pyxtnm522 = arg1
                      ## I1CMP:start
                      ## let
                      pyxtnm604 = None
                      ## I1Dvardclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4486(line=267,offs=1)--4502(line=267,offs=17)))
                      ## I1VARDCL
                      ## I1CMP:start
                      ## I1CMP:return:XATSINT1(0)
                      pyxtnm523 = XATSVAR1(XATSINT1(0))
                      ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4506(line=269,offs=1)--4524(line=269,offs=19)))
                      ## I1VALDCL
                      pyxtnm524 = None
                      pyxtnm524 = XATSADDR(pyxtnm523)
                      XATS000_patck(True)
                      ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4528(line=271,offs=1)--4713(line=284,offs=2)))
                      ## I1VALDCL
                      pyxtnm603 = None
                      ## let
                      pyxtnm602 = None
                      ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                      ## I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[394],T2Pvar(x0[5921]))))):timp
                      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4539(line=273,offs=1)--4550(line=273,offs=12))
                      ## I0Etapq(I0Ecst(gseq_forall(380)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(3721(line=210,offs=1)--3732(line=210,offs=12))));$list(T2JAG($list(T2Pvar(xs[5920]))),T2JAG($list(T2Pvar(x0[5921])))))
                      ## T1IMPallx(gseq_forall(380), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1841(line=78,offs=1)--1904(line=81,offs=33)))
                      ## T1IMPallx(gseq_forall(380)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7275],T2Pcst(term)),@(x0[7275],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_forall(380);$list(@(xs[1081],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7275])))),@(x0[1082],T2Pvar(x0[7275])))))))
                      pyxtnm600 = None
                      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1889(line=81,offs=18)--1900(line=81,offs=29))
                      ## I0Etapq(I0Ecst(list_forall(1206)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(2160(line=92,offs=1)--2171(line=92,offs=12))));$list(T2JAG($list(T2Pvar(x0[7275])))))
                      ## T1IMPallx(list_forall(1206), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1591(line=53,offs=1)--1837(line=76,offs=2)))
                      ## T1IMPallx(list_forall(1206)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7274],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_forall(1206);$list(@(x0[3286],T2Pvar(x0[7274])))))))
                      def pyxtnm599(arg1): ## timp: list_forall(1206)
                        pyxtnm533 = arg1
                        ## I1CMP:start
                        ## let
                        pyxtnm598 = None
                        ## I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1657(line=60,offs=1)--1835(line=75,offs=31)))
                        ## I1FUNDCL
                        def loop_1660(arg1): ## fun
                          pyxtnm534 = arg1
                          ## I1CMP:start
                          pyxtnm596 = None
                          while True: ## do {
                            ## { // cls
                            ## I1GPTpat(I1BNDcons(I1TNM(535);I0Pfree(I0Pdapp(I0Pcon(list_nil(8));$list()));$list()))
                            if (XATS000_ctgeq(pyxtnm534, XATSCTAG("list_nil",0))): ## { // gpt
                              pyxtnm535 = pyxtnm534
                              pyxtnm596 = XATSBOOL(True)
                              break ## cls
                            ## } // gpt
                            ## } // cls
                            ## { // cls
                            ## I1GPTpat(I1BNDcons(I1TNM(536);I0Pfree(I0Pdapp(I0Pcon(list_cons(9));$list(I0Pvar(x1(2569)),I0Pvar(xs(2570)))));$list(@(x1(2569),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(536));0)),@(xs(2570),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(536));1)))))
                            if (XATS000_ctgeq(pyxtnm534, XATSCTAG("list_cons",1))): ## { // gpt
                              pyxtnm536 = pyxtnm534
                              ## let
                              pyxtnm595 = None
                              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1761(line=71,offs=1)--1791(line=72,offs=20)))
                              ## I1VALDCL
                              pyxtnm592 = None
                              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(1772(line=72,offs=1)--1783(line=72,offs=12))
                              ## I0Etapq(I0Ecst(forall$test(47)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2003(line=96,offs=1)--2014(line=96,offs=12))));$list(T2JAG($list(T2Pvar(x0[7274])))))
                              ## T1IMPallx(forall$test(47), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4573(line=276,offs=1)--4711(line=283,offs=36)))
                              ## T1IMPallx(forall$test(47)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5920],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5921],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(forall$test(47);$list(@(x0[394],T2Pcst(term)))))))
                              def pyxtnm590(arg1): ## timp: forall$test(47)
                                pyxtnm537 = arg1
                                ## I1CMP:start
                                ## let
                                pyxtnm589 = None
                                ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4646(line=282,offs=1)--4675(line=282,offs=30)))
                                ## I1VALDCL
                                pyxtnm542 = None
                                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4659(line=282,offs=14)--4667(line=282,offs=22))
                                ## I0Etapq(I0Ecst(p2tr_get(2280)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2573(line=124,offs=1)--2581(line=124,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                                ## T1IMPallx(p2tr_get(2280), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(197(line=15,offs=1)--245(line=18,offs=17)))
                                ## T1IMPallx(p2tr_get(2280)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5726],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_get(2280);$list(@(a[5528],T2Pvar(a[5726])))))))
                                def pyxtnm540(arg1): ## timp: p2tr_get(2280)
                                  pyxtnm538 = arg1
                                  ## I1CMP:start
                                  pyxtnm539 = XATS000_dp2tr(pyxtnm538)
                                  ## I1CMP:return:pyxtnm539
                                  return pyxtnm539
                                ## endtimp(p2tr_get(2280))
                                pyxtnm541 = XATSDAPP(pyxtnm540(pyxtnm524))
                                pyxtnm542 = pyxtnm541
                                XATS000_patck(True)
                                ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4676(line=283,offs=1)--4709(line=283,offs=34)))
                                ## I1VALDCL
                                pyxtnm576 = None
                                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4685(line=283,offs=10)--4697(line=283,offs=22))
                                ## I0Etapq(I0Ecst(iforall$test(49)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2080(line=102,offs=1)--2092(line=102,offs=13))));$list(T2JAG($list(T2Pvar(x0[5921])))))
                                ## T1IMPallx(iforall$test(49), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7430(line=483,offs=1)--7513(line=487,offs=36)))
                                ## T1IMPallx(iforall$test(49)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[5944],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[5945],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforall$test(49);$list(@(x0[396],T2Pcst(term)))))))
                                def pyxtnm574(arg1, arg2): ## timp: iforall$test(49)
                                  pyxtnm543 = arg1
                                  pyxtnm544 = arg2
                                  ## I1CMP:start
                                  ## let
                                  pyxtnm573 = None
                                  ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7469(line=486,offs=1)--7501(line=487,offs=24)))
                                  ## I1VALDCL
                                  pyxtnm572 = None
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(7478(line=487,offs=1)--7490(line=487,offs=13))
                                  ## I0Etapq(I0Ecst(iforitm$work(53)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(2418(line=130,offs=1)--2430(line=130,offs=13))));$list(T2JAG($list(T2Pvar(x0[5945])))))
                                  ## T1IMPallx(iforitm$work(53), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5620(line=381,offs=1)--5665(line=382,offs=37)))
                                  ## T1IMPallx(iforitm$work(53)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[8629],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[8630],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforitm$work(53);$list(@(x0[400],T2Pcst(term)))))))
                                  pyxtnm570 = None
                                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(5648(line=382,offs=20)--5661(line=382,offs=33))
                                  ## I0Etapq(I0Ecst(iforitm$work0(1435)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas001_vt.sats)@(3293(line=203,offs=1)--3306(line=203,offs=14))));$list(T2JAG($list(T2Pvar(x0[8630])))))
                                  ## T1IMPallx(iforitm$work0(1435), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(3968(line=238,offs=1)--4093(line=246,offs=32)))
                                  ## T1IMPallx(iforitm$work0(1435)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[7693],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[7694],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(iforitm$work0(1435);$list(@(x0[3652],T2Pcst(term)))))))
                                  def pyxtnm569(arg1, arg2): ## timp: iforitm$work0(1435)
                                    pyxtnm545 = arg1
                                    pyxtnm546 = arg2
                                    ## I1CMP:start
                                    ## let
                                    pyxtnm568 = None
                                    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4038(line=244,offs=1)--4092(line=246,offs=31)))
                                    ## I1VALDCL
                                    pyxtnm564 = None
                                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4053(line=245,offs=7)--4054(line=245,offs=8))
                                    ## I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
                                    ## T1IMPallx(sint_gt$sint(919), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
                                    ## T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
                                    def pyxtnm553(arg1, arg2): ## timp: sint_gt$sint(919)
                                      pyxtnm547 = arg1
                                      pyxtnm548 = arg2
                                      ## I1CMP:start
                                      ## let
                                      pyxtnm552 = None
                                      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
                                      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gt$sint(2579));$list(I1FUNDCL(XATS2PY_sint_gt$sint(4876);$list(FJARGdarg($list(I1BNDcons(I1TNM(549);I0Pvar(i1(4877));$list(@(i1(4877),I1Vtnm(I1TNM(549))))),I1BNDcons(I1TNM(550);I0Pvar(i2(4878));$list(@(i2(4878),I1Vtnm(I1TNM(550))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gt$sint);G1Nlist($list())))))))
                                      pyxtnm551 = XATSDAPP(XATS2PY_sint_gt_sint(pyxtnm547, pyxtnm548))
                                      pyxtnm552 = pyxtnm551
                                      ## end-of(let)
                                      ## I1CMP:return:pyxtnm552
                                      return pyxtnm552
                                    ## endtimp(sint_gt$sint(919))
                                    pyxtnm554 = XATSDAPP(pyxtnm553(pyxtnm545, XATSINT1(0)))
                                    pyxtnm563 = None
                                    if (pyxtnm554):
                                      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4062(line=246,offs=1)--4072(line=246,offs=11))
                                      ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
                                      ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
                                      ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
                                      def pyxtnm559(arg1): ## timp: strn_print(1029)
                                        pyxtnm555 = arg1
                                        ## I1CMP:start
                                        ## let
                                        pyxtnm558 = None
                                        ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                                        ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(556);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(556))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                                        pyxtnm557 = XATSDAPP(XATS2PY_strn_print(pyxtnm555))
                                        pyxtnm558 = pyxtnm557
                                        ## end-of(let)
                                        ## I1CMP:return:pyxtnm558
                                        return pyxtnm558
                                      ## endtimp(strn_print(1029))
                                      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4073(line=246,offs=12)--4081(line=246,offs=20))
                                      ## I0Etapq(I0Ecst(gseq$sep(342)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2474(line=138,offs=1)--2482(line=138,offs=9))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
                                      ## T1IMPallx(gseq$sep(342), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3371(line=190,offs=1)--3421(line=193,offs=23)))
                                      ## T1IMPallx(gseq$sep(342)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7223],T2Pcst(term)),@(x0[7223],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$sep(342);$list(@(xs[985],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7223])))),@(x0[986],T2Pvar(x0[7223])))))))
                                      def pyxtnm560(): ## timp: gseq$sep(342)
                                        ## I1CMP:start
                                        ## I1CMP:return:XATSSTRN(",")
                                        return XATSSTRN(",")
                                      ## endtimp(gseq$sep(342))
                                      pyxtnm561 = XATSDAPP(pyxtnm560())
                                      pyxtnm562 = XATSDAPP(pyxtnm559(pyxtnm561))
                                      pyxtnm563 = pyxtnm562
                                    ## else: None
                                    ## end-of(if)
                                    pyxtnm564 = pyxtnm563
                                    XATS000_patck(True)
                                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4012(line=242,offs=3)--4020(line=242,offs=11))
                                    ## I0Etapq(I0Ecst(g_print0(1398)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas000_vt.sats)@(2080(line=106,offs=1)--2088(line=106,offs=9))));$list(T2JAG($list(T2Pvar(x0[7694])))))
                                    ## T1IMPallx(g_print0(1398), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1589(line=56,offs=1)--1634(line=58,offs=27)))
                                    ## T1IMPallx(g_print0(1398)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8571],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(g_print0(1398);$list(@(x0[3610],T2Pvar(x0[8571])))))))
                                    pyxtnm566 = None
                                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gxyz000_vt.dats)@(1623(line=58,offs=16)--1630(line=58,offs=23))
                                    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[8571])))))
                                    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
                                    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
                                    pyxtnm565 = None
                                    pyxtnm565 = auxpr_1677
                                    pyxtnm566 = pyxtnm565
                                    pyxtnm567 = XATSDAPP(pyxtnm566(pyxtnm546))
                                    pyxtnm568 = pyxtnm567
                                    ## end-of(let)
                                    ## I1CMP:return:pyxtnm568
                                    return pyxtnm568
                                  ## endtimp(iforitm$work0(1435))
                                  pyxtnm570 = pyxtnm569
                                  pyxtnm571 = XATSDAPP(pyxtnm570(pyxtnm543, pyxtnm544))
                                  pyxtnm572 = pyxtnm571
                                  XATS000_patck(True)
                                  pyxtnm573 = XATSBOOL(True)
                                  ## end-of(let)
                                  ## I1CMP:return:pyxtnm573
                                  return pyxtnm573
                                ## endtimp(iforall$test(49))
                                pyxtnm575 = XATSDAPP(pyxtnm574(pyxtnm542, pyxtnm537))
                                pyxtnm576 = pyxtnm575
                                XATS000_patck(True)
                                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4610(line=279,offs=5)--4618(line=279,offs=13))
                                ## I0Etapq(I0Ecst(p2tr_set(2281)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/unsfx00.sats)@(2611(line=127,offs=1)--2619(line=127,offs=9))));$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))))))
                                ## T1IMPallx(p2tr_set(2281), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/unsfx00.dats)@(246(line=19,offs=1)--305(line=22,offs=27)))
                                ## T1IMPallx(p2tr_set(2281)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list(@(a[5727],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))));I1Dimplmnt0(DIMPLone2(p2tr_set(2281);$list(@(a[5529],T2Pvar(a[5727])))))))
                                def pyxtnm579(arg1, arg2): ## timp: p2tr_set(2281)
                                  pyxtnm577 = arg1
                                  pyxtnm578 = arg2
                                  ## I1CMP:start
                                  XATS000_assgn(pyxtnm577, pyxtnm578)
                                  ## I1CMP:return:[]
                                  return []
                                ## endtimp(p2tr_set(2281))
                                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(4629(line=279,offs=24)--4630(line=279,offs=25))
                                ## I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
                                ## T1IMPallx(sint_add$sint(925), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
                                ## T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
                                def pyxtnm586(arg1, arg2): ## timp: sint_add$sint(925)
                                  pyxtnm580 = arg1
                                  pyxtnm581 = arg2
                                  ## I1CMP:start
                                  ## let
                                  pyxtnm585 = None
                                  ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
                                  ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_add$sint(2584));$list(I1FUNDCL(XATS2PY_sint_add$sint(4901);$list(FJARGdarg($list(I1BNDcons(I1TNM(582);I0Pvar(i1(4902));$list(@(i1(4902),I1Vtnm(I1TNM(582))))),I1BNDcons(I1TNM(583);I0Pvar(i2(4903));$list(@(i2(4903),I1Vtnm(I1TNM(583))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_add$sint);G1Nlist($list())))))))
                                  pyxtnm584 = XATSDAPP(XATS2PY_sint_add_sint(pyxtnm580, pyxtnm581))
                                  pyxtnm585 = pyxtnm584
                                  ## end-of(let)
                                  ## I1CMP:return:pyxtnm585
                                  return pyxtnm585
                                ## endtimp(sint_add$sint(925))
                                pyxtnm587 = XATSDAPP(pyxtnm586(pyxtnm542, XATSINT1(1)))
                                pyxtnm588 = XATSDAPP(pyxtnm579(pyxtnm524, pyxtnm587))
                                pyxtnm589 = pyxtnm576
                                ## end-of(let)
                                ## I1CMP:return:pyxtnm589
                                return pyxtnm589
                              ## endtimp(forall$test(47))
                              pyxtnm591 = XATSDAPP(pyxtnm590(XATSP1CN("list_cons", pyxtnm536[0+1])))
                              pyxtnm592 = pyxtnm591
                              XATS000_patck(True)
                              pyxtnm594 = None
                              if (pyxtnm592):
                                pyxtnm593 = XATSDAPP(loop_1660(XATSP1CN("list_cons", pyxtnm536[1+1])))
                                pyxtnm594 = pyxtnm593
                              else:
                                pyxtnm594 = XATSBOOL(False)
                              ## end-of(if)
                              pyxtnm595 = pyxtnm594
                              ## end-of(let)
                              pyxtnm596 = pyxtnm595
                              break ## cls
                            ## } // gpt
                            ## } // cls
                            XATS000_cfail()
                          ## } while True // end-of(do-cls)
                          ## I1CMP:return:pyxtnm596
                          return pyxtnm596
                        pyxtnm597 = XATSDAPP(loop_1660(pyxtnm533))
                        pyxtnm598 = pyxtnm597
                        ## end-of(let)
                        ## I1CMP:return:pyxtnm598
                        return pyxtnm598
                      ## endtimp(list_forall(1206))
                      pyxtnm600 = pyxtnm599
                      pyxtnm601 = XATSDAPP(pyxtnm600(pyxtnm522))
                      pyxtnm602 = pyxtnm601
                      ## end-of(let)
                      pyxtnm603 = pyxtnm602
                      XATS000_patck(True)
                      pyxtnm604 = pyxtnm603
                      ## end-of(let)
                      ## I1CMP:return:pyxtnm604
                      return pyxtnm604
                    ## endtimp(gseq_iforall(384))
                    pyxtnm606 = XATSDAPP(pyxtnm605(pyxtnm516))
                    pyxtnm607 = pyxtnm606
                    XATS000_patck(True)
                    pyxtnm608 = []
                    ## end-of(let)
                    pyxtnm609 = pyxtnm608
                    ## end-of(let)
                    ## I1CMP:return:pyxtnm609
                    return pyxtnm609
                  ## endtimp(gseq_iforitm(398))
                  pyxtnm611 = XATSDAPP(pyxtnm610(pyxtnm515))
                  pyxtnm612 = pyxtnm611
                  ## end-of(let)
                  ## I1CMP:return:pyxtnm612
                  return pyxtnm612
                ## endtimp(gseq_iforitm0(1732))
                pyxtnm614 = XATSDAPP(pyxtnm613(pyxtnm358))
                pyxtnm615 = pyxtnm614
              ## end-of(if)
              pyxtnm616 = pyxtnm615
              ## end-of(let)
              pyxtnm617 = pyxtnm616
              XATS000_patck(True)
              ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4330(line=274,offs=1)--4371(line=275,offs=33)))
              ## I1VALDCL
              pyxtnm626 = None
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4339(line=275,offs=1)--4349(line=275,offs=11))
              ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
              ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
              ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
              def pyxtnm622(arg1): ## timp: strn_print(1029)
                pyxtnm618 = arg1
                ## I1CMP:start
                ## let
                pyxtnm621 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(619);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(619))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                pyxtnm620 = XATSDAPP(XATS2PY_strn_print(pyxtnm618))
                pyxtnm621 = pyxtnm620
                ## end-of(let)
                ## I1CMP:return:pyxtnm621
                return pyxtnm621
              ## endtimp(strn_print(1029))
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/gseq000_vt.dats)@(4352(line=275,offs=14)--4360(line=275,offs=22))
              ## I0Etapq(I0Ecst(gseq$end(341)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq000.sats)@(2432(line=134,offs=1)--2440(line=134,offs=9))));$list(T2JAG($list(T2Pvar(xs[7693]))),T2JAG($list(T2Pvar(x0[7694])))))
              ## T1IMPallx(gseq$end(341), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(3422(line=194,offs=1)--3472(line=197,offs=23)))
              ## T1IMPallx(gseq$end(341)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7224],T2Pcst(term)),@(x0[7224],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq$end(341);$list(@(xs[983],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7224])))),@(x0[984],T2Pvar(x0[7224])))))))
              def pyxtnm623(): ## timp: gseq$end(341)
                ## I1CMP:start
                ## I1CMP:return:XATSSTRN(")")
                return XATSSTRN(")")
              ## endtimp(gseq$end(341))
              pyxtnm624 = XATSDAPP(pyxtnm623())
              pyxtnm625 = XATSDAPP(pyxtnm622(pyxtnm624))
              pyxtnm626 = pyxtnm625
              XATS000_patck(True)
              pyxtnm627 = []
              ## end-of(let)
              ## I1CMP:return:pyxtnm627
              return pyxtnm627
            ## endtimp(gseq_print0(1658))
            pyxtnm629 = pyxtnm628
            pyxtnm630 = XATSDAPP(pyxtnm629(pyxtnm357))
            ## I1CMP:return:pyxtnm630
            return pyxtnm630
          ## endtimp(g_print(39))
          pyxtnm632 = XATSDAPP(pyxtnm631(pyxtnm321))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm634(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm633 = XATSTUP0([])
            ## I1CMP:return:pyxtnm633
            return pyxtnm633
          ## endtimp(gs_print$sep(794))
          pyxtnm635 = XATSDAPP(pyxtnm634())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6839])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm641 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm640(arg1): ## timp: strn_print(1029)
            pyxtnm636 = arg1
            ## I1CMP:start
            ## let
            pyxtnm639 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(637);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(637))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm638 = XATSDAPP(XATS2PY_strn_print(pyxtnm636))
            pyxtnm639 = pyxtnm638
            ## end-of(let)
            ## I1CMP:return:pyxtnm639
            return pyxtnm639
          ## endtimp(strn_print(1029))
          pyxtnm641 = pyxtnm640
          pyxtnm642 = XATSDAPP(pyxtnm641(pyxtnm322))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm644(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm643 = XATSTUP0([])
            ## I1CMP:return:pyxtnm643
            return pyxtnm643
          ## endtimp(gs_print$end(795))
          pyxtnm645 = XATSDAPP(pyxtnm644())
          pyxtnm646 = pyxtnm645
          ## end-of(let)
          ## I1CMP:return:pyxtnm646
          return pyxtnm646
        ## endtimp(gs_print_a5(801))
        pyxtnm648 = XATSDAPP(pyxtnm647(XATSSTRN("TMopr("), XATSP1CN("TMopr", pyxtnm317[0+1]), XATSSTRN(";"), XATSP1CN("TMopr", pyxtnm317[1+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm648
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(649);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5163)),I0Pvar(tm2(5164)),I0Pvar(tm3(5165))));$list(@(tm1(5163),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(649));0)),@(tm2(5164),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(649));1)),@(tm3(5165),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(649));2)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMif0",6))): ## { // gpt
        pyxtnm649 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(2054(line=139,offs=1)--2060(line=139,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a7(803)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12204(line=788,offs=1)--12215(line=788,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a7(803), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22634(line=1392,offs=1)--23038(line=1414,offs=4)))
        ## T1IMPallx(gs_print_a7(803)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6846],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6847],T2Pcst(term)),@(x2[6848],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6849],T2Pcst(term)),@(x4[6850],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x5[6851],T2Pcst(term)),@(x6[6852],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a7(803);$list(@(x0[2414],T2Pvar(x0[6846])),@(x1[2415],T2Pvar(x1[6847])),@(x2[2416],T2Pvar(x2[6848])),@(x3[2417],T2Pvar(x3[6849])),@(x4[2418],T2Pvar(x4[6850])),@(x5[2419],T2Pvar(x5[6851])),@(x6[2420],T2Pvar(x6[6852])))))))
        def pyxtnm717(arg1, arg2, arg3, arg4, arg5, arg6, arg7): ## timp: gs_print_a7(803)
          pyxtnm650 = arg1
          pyxtnm651 = arg2
          pyxtnm652 = arg3
          pyxtnm653 = arg4
          pyxtnm654 = arg5
          pyxtnm655 = arg6
          pyxtnm656 = arg7
          ## I1CMP:start
          ## let
          pyxtnm716 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22762(line=1404,offs=1)--22785(line=1405,offs=15)))
          ## I1VALDCL
          pyxtnm660 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22771(line=1405,offs=1)--22783(line=1405,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm658(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm657 = XATSTUP0([])
            ## I1CMP:return:pyxtnm657
            return pyxtnm657
          ## endtimp(gs_print$beg(793))
          pyxtnm659 = XATSDAPP(pyxtnm658())
          pyxtnm660 = pyxtnm659
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22798(line=1407,offs=3)--22805(line=1407,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6846])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm666 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm665(arg1): ## timp: strn_print(1029)
            pyxtnm661 = arg1
            ## I1CMP:start
            ## let
            pyxtnm664 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(662);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(662))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm663 = XATSDAPP(XATS2PY_strn_print(pyxtnm661))
            pyxtnm664 = pyxtnm663
            ## end-of(let)
            ## I1CMP:return:pyxtnm664
            return pyxtnm664
          ## endtimp(strn_print(1029))
          pyxtnm666 = pyxtnm665
          pyxtnm667 = XATSDAPP(pyxtnm666(pyxtnm650))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22815(line=1407,offs=20)--22827(line=1407,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm669(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm668 = XATSTUP0([])
            ## I1CMP:return:pyxtnm668
            return pyxtnm668
          ## endtimp(gs_print$sep(794))
          pyxtnm670 = XATSDAPP(pyxtnm669())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22832(line=1408,offs=3)--22839(line=1408,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6847])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm671 = None
          pyxtnm671 = auxpr_1677
          pyxtnm672 = XATSDAPP(pyxtnm671(pyxtnm651))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22849(line=1408,offs=20)--22861(line=1408,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm674(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm673 = XATSTUP0([])
            ## I1CMP:return:pyxtnm673
            return pyxtnm673
          ## endtimp(gs_print$sep(794))
          pyxtnm675 = XATSDAPP(pyxtnm674())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22866(line=1409,offs=3)--22873(line=1409,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6848])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm681 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm680(arg1): ## timp: strn_print(1029)
            pyxtnm676 = arg1
            ## I1CMP:start
            ## let
            pyxtnm679 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(677);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(677))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm678 = XATSDAPP(XATS2PY_strn_print(pyxtnm676))
            pyxtnm679 = pyxtnm678
            ## end-of(let)
            ## I1CMP:return:pyxtnm679
            return pyxtnm679
          ## endtimp(strn_print(1029))
          pyxtnm681 = pyxtnm680
          pyxtnm682 = XATSDAPP(pyxtnm681(pyxtnm652))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22883(line=1409,offs=20)--22895(line=1409,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm684(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm683 = XATSTUP0([])
            ## I1CMP:return:pyxtnm683
            return pyxtnm683
          ## endtimp(gs_print$sep(794))
          pyxtnm685 = XATSDAPP(pyxtnm684())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22900(line=1410,offs=3)--22907(line=1410,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6849])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm686 = None
          pyxtnm686 = auxpr_1677
          pyxtnm687 = XATSDAPP(pyxtnm686(pyxtnm653))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22917(line=1410,offs=20)--22929(line=1410,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm689(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm688 = XATSTUP0([])
            ## I1CMP:return:pyxtnm688
            return pyxtnm688
          ## endtimp(gs_print$sep(794))
          pyxtnm690 = XATSDAPP(pyxtnm689())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22934(line=1411,offs=3)--22941(line=1411,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6850])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm696 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm695(arg1): ## timp: strn_print(1029)
            pyxtnm691 = arg1
            ## I1CMP:start
            ## let
            pyxtnm694 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(692);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(692))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm693 = XATSDAPP(XATS2PY_strn_print(pyxtnm691))
            pyxtnm694 = pyxtnm693
            ## end-of(let)
            ## I1CMP:return:pyxtnm694
            return pyxtnm694
          ## endtimp(strn_print(1029))
          pyxtnm696 = pyxtnm695
          pyxtnm697 = XATSDAPP(pyxtnm696(pyxtnm654))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22951(line=1411,offs=20)--22963(line=1411,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm699(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm698 = XATSTUP0([])
            ## I1CMP:return:pyxtnm698
            return pyxtnm698
          ## endtimp(gs_print$sep(794))
          pyxtnm700 = XATSDAPP(pyxtnm699())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22968(line=1412,offs=3)--22975(line=1412,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x5[6851])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm701 = None
          pyxtnm701 = auxpr_1677
          pyxtnm702 = XATSDAPP(pyxtnm701(pyxtnm655))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22985(line=1412,offs=20)--22997(line=1412,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm704(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm703 = XATSTUP0([])
            ## I1CMP:return:pyxtnm703
            return pyxtnm703
          ## endtimp(gs_print$sep(794))
          pyxtnm705 = XATSDAPP(pyxtnm704())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23002(line=1413,offs=3)--23009(line=1413,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x6[6852])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm711 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm710(arg1): ## timp: strn_print(1029)
            pyxtnm706 = arg1
            ## I1CMP:start
            ## let
            pyxtnm709 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(707);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(707))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm708 = XATSDAPP(XATS2PY_strn_print(pyxtnm706))
            pyxtnm709 = pyxtnm708
            ## end-of(let)
            ## I1CMP:return:pyxtnm709
            return pyxtnm709
          ## endtimp(strn_print(1029))
          pyxtnm711 = pyxtnm710
          pyxtnm712 = XATSDAPP(pyxtnm711(pyxtnm656))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23019(line=1413,offs=20)--23031(line=1413,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm714(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm713 = XATSTUP0([])
            ## I1CMP:return:pyxtnm713
            return pyxtnm713
          ## endtimp(gs_print$end(795))
          pyxtnm715 = XATSDAPP(pyxtnm714())
          pyxtnm716 = pyxtnm715
          ## end-of(let)
          ## I1CMP:return:pyxtnm716
          return pyxtnm716
        ## endtimp(gs_print_a7(803))
        pyxtnm718 = XATSDAPP(pyxtnm717(XATSSTRN("TMif0("), XATSP1CN("TMif0", pyxtnm649[0+1]), XATSSTRN(";"), XATSP1CN("TMif0", pyxtnm649[1+1]), XATSSTRN(";"), XATSP1CN("TMif0", pyxtnm649[2+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm718
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(719);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5166)),I0Pvar(x01(5167)),I0Pvar(tmx(5168))));$list(@(f00(5166),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(719));0)),@(x01(5167),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(719));1)),@(tmx(5168),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(719));2)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMfix",7))): ## { // gpt
        pyxtnm719 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(2131(line=144,offs=1)--2137(line=144,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a7(803)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12204(line=788,offs=1)--12215(line=788,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a7(803), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22634(line=1392,offs=1)--23038(line=1414,offs=4)))
        ## T1IMPallx(gs_print_a7(803)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6846],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6847],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6848],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6849],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x4[6850],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x5[6851],T2Pcst(term)),@(x6[6852],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a7(803);$list(@(x0[2414],T2Pvar(x0[6846])),@(x1[2415],T2Pvar(x1[6847])),@(x2[2416],T2Pvar(x2[6848])),@(x3[2417],T2Pvar(x3[6849])),@(x4[2418],T2Pvar(x4[6850])),@(x5[2419],T2Pvar(x5[6851])),@(x6[2420],T2Pvar(x6[6852])))))))
        def pyxtnm797(arg1, arg2, arg3, arg4, arg5, arg6, arg7): ## timp: gs_print_a7(803)
          pyxtnm720 = arg1
          pyxtnm721 = arg2
          pyxtnm722 = arg3
          pyxtnm723 = arg4
          pyxtnm724 = arg5
          pyxtnm725 = arg6
          pyxtnm726 = arg7
          ## I1CMP:start
          ## let
          pyxtnm796 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22762(line=1404,offs=1)--22785(line=1405,offs=15)))
          ## I1VALDCL
          pyxtnm730 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22771(line=1405,offs=1)--22783(line=1405,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm728(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm727 = XATSTUP0([])
            ## I1CMP:return:pyxtnm727
            return pyxtnm727
          ## endtimp(gs_print$beg(793))
          pyxtnm729 = XATSDAPP(pyxtnm728())
          pyxtnm730 = pyxtnm729
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22798(line=1407,offs=3)--22805(line=1407,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6846])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm736 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm735(arg1): ## timp: strn_print(1029)
            pyxtnm731 = arg1
            ## I1CMP:start
            ## let
            pyxtnm734 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(732);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(732))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm733 = XATSDAPP(XATS2PY_strn_print(pyxtnm731))
            pyxtnm734 = pyxtnm733
            ## end-of(let)
            ## I1CMP:return:pyxtnm734
            return pyxtnm734
          ## endtimp(strn_print(1029))
          pyxtnm736 = pyxtnm735
          pyxtnm737 = XATSDAPP(pyxtnm736(pyxtnm720))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22815(line=1407,offs=20)--22827(line=1407,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm739(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm738 = XATSTUP0([])
            ## I1CMP:return:pyxtnm738
            return pyxtnm738
          ## endtimp(gs_print$sep(794))
          pyxtnm740 = XATSDAPP(pyxtnm739())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22832(line=1408,offs=3)--22839(line=1408,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6847])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm746 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm745(arg1): ## timp: strn_print(1029)
            pyxtnm741 = arg1
            ## I1CMP:start
            ## let
            pyxtnm744 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(742);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(742))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm743 = XATSDAPP(XATS2PY_strn_print(pyxtnm741))
            pyxtnm744 = pyxtnm743
            ## end-of(let)
            ## I1CMP:return:pyxtnm744
            return pyxtnm744
          ## endtimp(strn_print(1029))
          pyxtnm746 = pyxtnm745
          pyxtnm747 = XATSDAPP(pyxtnm746(pyxtnm721))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22849(line=1408,offs=20)--22861(line=1408,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm749(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm748 = XATSTUP0([])
            ## I1CMP:return:pyxtnm748
            return pyxtnm748
          ## endtimp(gs_print$sep(794))
          pyxtnm750 = XATSDAPP(pyxtnm749())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22866(line=1409,offs=3)--22873(line=1409,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6848])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm756 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm755(arg1): ## timp: strn_print(1029)
            pyxtnm751 = arg1
            ## I1CMP:start
            ## let
            pyxtnm754 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(752);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(752))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm753 = XATSDAPP(XATS2PY_strn_print(pyxtnm751))
            pyxtnm754 = pyxtnm753
            ## end-of(let)
            ## I1CMP:return:pyxtnm754
            return pyxtnm754
          ## endtimp(strn_print(1029))
          pyxtnm756 = pyxtnm755
          pyxtnm757 = XATSDAPP(pyxtnm756(pyxtnm722))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22883(line=1409,offs=20)--22895(line=1409,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm759(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm758 = XATSTUP0([])
            ## I1CMP:return:pyxtnm758
            return pyxtnm758
          ## endtimp(gs_print$sep(794))
          pyxtnm760 = XATSDAPP(pyxtnm759())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22900(line=1410,offs=3)--22907(line=1410,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6849])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm766 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm765(arg1): ## timp: strn_print(1029)
            pyxtnm761 = arg1
            ## I1CMP:start
            ## let
            pyxtnm764 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(762);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(762))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm763 = XATSDAPP(XATS2PY_strn_print(pyxtnm761))
            pyxtnm764 = pyxtnm763
            ## end-of(let)
            ## I1CMP:return:pyxtnm764
            return pyxtnm764
          ## endtimp(strn_print(1029))
          pyxtnm766 = pyxtnm765
          pyxtnm767 = XATSDAPP(pyxtnm766(pyxtnm723))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22917(line=1410,offs=20)--22929(line=1410,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm769(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm768 = XATSTUP0([])
            ## I1CMP:return:pyxtnm768
            return pyxtnm768
          ## endtimp(gs_print$sep(794))
          pyxtnm770 = XATSDAPP(pyxtnm769())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22934(line=1411,offs=3)--22941(line=1411,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6850])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm776 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm775(arg1): ## timp: strn_print(1029)
            pyxtnm771 = arg1
            ## I1CMP:start
            ## let
            pyxtnm774 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(772);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(772))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm773 = XATSDAPP(XATS2PY_strn_print(pyxtnm771))
            pyxtnm774 = pyxtnm773
            ## end-of(let)
            ## I1CMP:return:pyxtnm774
            return pyxtnm774
          ## endtimp(strn_print(1029))
          pyxtnm776 = pyxtnm775
          pyxtnm777 = XATSDAPP(pyxtnm776(pyxtnm724))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22951(line=1411,offs=20)--22963(line=1411,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm779(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm778 = XATSTUP0([])
            ## I1CMP:return:pyxtnm778
            return pyxtnm778
          ## endtimp(gs_print$sep(794))
          pyxtnm780 = XATSDAPP(pyxtnm779())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22968(line=1412,offs=3)--22975(line=1412,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x5[6851])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm781 = None
          pyxtnm781 = auxpr_1677
          pyxtnm782 = XATSDAPP(pyxtnm781(pyxtnm725))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22985(line=1412,offs=20)--22997(line=1412,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm784(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm783 = XATSTUP0([])
            ## I1CMP:return:pyxtnm783
            return pyxtnm783
          ## endtimp(gs_print$sep(794))
          pyxtnm785 = XATSDAPP(pyxtnm784())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23002(line=1413,offs=3)--23009(line=1413,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x6[6852])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm791 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm790(arg1): ## timp: strn_print(1029)
            pyxtnm786 = arg1
            ## I1CMP:start
            ## let
            pyxtnm789 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(787);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(787))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm788 = XATSDAPP(XATS2PY_strn_print(pyxtnm786))
            pyxtnm789 = pyxtnm788
            ## end-of(let)
            ## I1CMP:return:pyxtnm789
            return pyxtnm789
          ## endtimp(strn_print(1029))
          pyxtnm791 = pyxtnm790
          pyxtnm792 = XATSDAPP(pyxtnm791(pyxtnm726))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23019(line=1413,offs=20)--23031(line=1413,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm794(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm793 = XATSTUP0([])
            ## I1CMP:return:pyxtnm793
            return pyxtnm793
          ## endtimp(gs_print$end(795))
          pyxtnm795 = XATSDAPP(pyxtnm794())
          pyxtnm796 = pyxtnm795
          ## end-of(let)
          ## I1CMP:return:pyxtnm796
          return pyxtnm796
        ## endtimp(gs_print_a7(803))
        pyxtnm798 = XATSDAPP(pyxtnm797(XATSSTRN("TMfix("), XATSP1CN("TMfix", pyxtnm719[0+1]), XATSSTRN(";"), XATSP1CN("TMfix", pyxtnm719[1+1]), XATSSTRN(";"), XATSP1CN("TMfix", pyxtnm719[2+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm798
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(799);I0Pdapp(I0Pcon(TMlet(40));$list(I0Pvar(x01(5169)),I0Pvar(tm1(5170)),I0Pvar(tm2(5171))));$list(@(x01(5169),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(799));0)),@(tm1(5170),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(799));1)),@(tm2(5171),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(799));2)))))
      if (XATS000_ctgeq(pyxtnm72, XATSCTAG("TMlet",8))): ## { // gpt
        pyxtnm799 = pyxtnm72
        ## LCSRCsome1(lambda1.dats)@(2208(line=149,offs=1)--2214(line=149,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a7(803)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12204(line=788,offs=1)--12215(line=788,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a7(803), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22634(line=1392,offs=1)--23038(line=1414,offs=4)))
        ## T1IMPallx(gs_print_a7(803)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6846],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6847],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x2[6848],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6849],T2Pcst(term)),@(x4[6850],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x5[6851],T2Pcst(term)),@(x6[6852],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a7(803);$list(@(x0[2414],T2Pvar(x0[6846])),@(x1[2415],T2Pvar(x1[6847])),@(x2[2416],T2Pvar(x2[6848])),@(x3[2417],T2Pvar(x3[6849])),@(x4[2418],T2Pvar(x4[6850])),@(x5[2419],T2Pvar(x5[6851])),@(x6[2420],T2Pvar(x6[6852])))))))
        def pyxtnm872(arg1, arg2, arg3, arg4, arg5, arg6, arg7): ## timp: gs_print_a7(803)
          pyxtnm800 = arg1
          pyxtnm801 = arg2
          pyxtnm802 = arg3
          pyxtnm803 = arg4
          pyxtnm804 = arg5
          pyxtnm805 = arg6
          pyxtnm806 = arg7
          ## I1CMP:start
          ## let
          pyxtnm871 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22762(line=1404,offs=1)--22785(line=1405,offs=15)))
          ## I1VALDCL
          pyxtnm810 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22771(line=1405,offs=1)--22783(line=1405,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm808(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm807 = XATSTUP0([])
            ## I1CMP:return:pyxtnm807
            return pyxtnm807
          ## endtimp(gs_print$beg(793))
          pyxtnm809 = XATSDAPP(pyxtnm808())
          pyxtnm810 = pyxtnm809
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22798(line=1407,offs=3)--22805(line=1407,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6846])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm816 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm815(arg1): ## timp: strn_print(1029)
            pyxtnm811 = arg1
            ## I1CMP:start
            ## let
            pyxtnm814 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(812);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(812))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm813 = XATSDAPP(XATS2PY_strn_print(pyxtnm811))
            pyxtnm814 = pyxtnm813
            ## end-of(let)
            ## I1CMP:return:pyxtnm814
            return pyxtnm814
          ## endtimp(strn_print(1029))
          pyxtnm816 = pyxtnm815
          pyxtnm817 = XATSDAPP(pyxtnm816(pyxtnm800))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22815(line=1407,offs=20)--22827(line=1407,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm819(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm818 = XATSTUP0([])
            ## I1CMP:return:pyxtnm818
            return pyxtnm818
          ## endtimp(gs_print$sep(794))
          pyxtnm820 = XATSDAPP(pyxtnm819())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22832(line=1408,offs=3)--22839(line=1408,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6847])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm826 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm825(arg1): ## timp: strn_print(1029)
            pyxtnm821 = arg1
            ## I1CMP:start
            ## let
            pyxtnm824 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(822);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(822))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm823 = XATSDAPP(XATS2PY_strn_print(pyxtnm821))
            pyxtnm824 = pyxtnm823
            ## end-of(let)
            ## I1CMP:return:pyxtnm824
            return pyxtnm824
          ## endtimp(strn_print(1029))
          pyxtnm826 = pyxtnm825
          pyxtnm827 = XATSDAPP(pyxtnm826(pyxtnm801))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22849(line=1408,offs=20)--22861(line=1408,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm829(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm828 = XATSTUP0([])
            ## I1CMP:return:pyxtnm828
            return pyxtnm828
          ## endtimp(gs_print$sep(794))
          pyxtnm830 = XATSDAPP(pyxtnm829())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22866(line=1409,offs=3)--22873(line=1409,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6848])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm836 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm835(arg1): ## timp: strn_print(1029)
            pyxtnm831 = arg1
            ## I1CMP:start
            ## let
            pyxtnm834 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(832);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(832))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm833 = XATSDAPP(XATS2PY_strn_print(pyxtnm831))
            pyxtnm834 = pyxtnm833
            ## end-of(let)
            ## I1CMP:return:pyxtnm834
            return pyxtnm834
          ## endtimp(strn_print(1029))
          pyxtnm836 = pyxtnm835
          pyxtnm837 = XATSDAPP(pyxtnm836(pyxtnm802))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22883(line=1409,offs=20)--22895(line=1409,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm839(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm838 = XATSTUP0([])
            ## I1CMP:return:pyxtnm838
            return pyxtnm838
          ## endtimp(gs_print$sep(794))
          pyxtnm840 = XATSDAPP(pyxtnm839())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22900(line=1410,offs=3)--22907(line=1410,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6849])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm841 = None
          pyxtnm841 = auxpr_1677
          pyxtnm842 = XATSDAPP(pyxtnm841(pyxtnm803))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22917(line=1410,offs=20)--22929(line=1410,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm844(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm843 = XATSTUP0([])
            ## I1CMP:return:pyxtnm843
            return pyxtnm843
          ## endtimp(gs_print$sep(794))
          pyxtnm845 = XATSDAPP(pyxtnm844())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22934(line=1411,offs=3)--22941(line=1411,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6850])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm851 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm850(arg1): ## timp: strn_print(1029)
            pyxtnm846 = arg1
            ## I1CMP:start
            ## let
            pyxtnm849 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(847);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(847))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm848 = XATSDAPP(XATS2PY_strn_print(pyxtnm846))
            pyxtnm849 = pyxtnm848
            ## end-of(let)
            ## I1CMP:return:pyxtnm849
            return pyxtnm849
          ## endtimp(strn_print(1029))
          pyxtnm851 = pyxtnm850
          pyxtnm852 = XATSDAPP(pyxtnm851(pyxtnm804))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22951(line=1411,offs=20)--22963(line=1411,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm854(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm853 = XATSTUP0([])
            ## I1CMP:return:pyxtnm853
            return pyxtnm853
          ## endtimp(gs_print$sep(794))
          pyxtnm855 = XATSDAPP(pyxtnm854())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22968(line=1412,offs=3)--22975(line=1412,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x5[6851])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2269(line=154,offs=1)--2306(line=154,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm856 = None
          pyxtnm856 = auxpr_1677
          pyxtnm857 = XATSDAPP(pyxtnm856(pyxtnm805))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22985(line=1412,offs=20)--22997(line=1412,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm859(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm858 = XATSTUP0([])
            ## I1CMP:return:pyxtnm858
            return pyxtnm858
          ## endtimp(gs_print$sep(794))
          pyxtnm860 = XATSDAPP(pyxtnm859())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23002(line=1413,offs=3)--23009(line=1413,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x6[6852])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm866 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm865(arg1): ## timp: strn_print(1029)
            pyxtnm861 = arg1
            ## I1CMP:start
            ## let
            pyxtnm864 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(862);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(862))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm863 = XATSDAPP(XATS2PY_strn_print(pyxtnm861))
            pyxtnm864 = pyxtnm863
            ## end-of(let)
            ## I1CMP:return:pyxtnm864
            return pyxtnm864
          ## endtimp(strn_print(1029))
          pyxtnm866 = pyxtnm865
          pyxtnm867 = XATSDAPP(pyxtnm866(pyxtnm806))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(23019(line=1413,offs=20)--23031(line=1413,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm869(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm868 = XATSTUP0([])
            ## I1CMP:return:pyxtnm868
            return pyxtnm868
          ## endtimp(gs_print$end(795))
          pyxtnm870 = XATSDAPP(pyxtnm869())
          pyxtnm871 = pyxtnm870
          ## end-of(let)
          ## I1CMP:return:pyxtnm871
          return pyxtnm871
        ## endtimp(gs_print_a7(803))
        pyxtnm873 = XATSDAPP(pyxtnm872(XATSSTRN("TMlet("), XATSP1CN("TMlet", pyxtnm799[0+1]), XATSSTRN(";"), XATSP1CN("TMlet", pyxtnm799[1+1]), XATSSTRN(";"), XATSP1CN("TMlet", pyxtnm799[2+1]), XATSSTRN(")")))
        pyxtnm874 = pyxtnm873
        break ## cls
      ## } // gpt
      ## } // cls
      XATS000_cfail()
    ## } while True // end-of(do-cls)
    pyxtnm875 = pyxtnm874
    ## end-of(let)
    ## I1CMP:return:pyxtnm875
    return pyxtnm875
  pyxtnm876 = XATSDAPP(auxpr_1677(pyxtnm71))
  pyxtnm877 = pyxtnm876
  ## end-of(let)
  ## I1CMP:return:pyxtnm877
  return pyxtnm877
## endtimp(term_print(2643))
pyxtnm879 = pyxtnm878
XATS000_patck(True)
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
## I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term))))):timp
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2543(line=169,offs=1)--2571(line=169,offs=29)))
## I1VALDCL
pyxtnm915 = None
## LCSRCsome1(lambda1.dats)@(2552(line=169,offs=10)--2560(line=169,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm913(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm880 = arg1
  pyxtnm881 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm904(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm882 = arg1
    pyxtnm883 = arg2
    ## I1CMP:start
    ## let
    pyxtnm903 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm887 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm885(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm884 = XATSTUP0([])
      ## I1CMP:return:pyxtnm884
      return pyxtnm884
    ## endtimp(gs_print$beg(793))
    pyxtnm886 = XATSDAPP(pyxtnm885())
    pyxtnm887 = pyxtnm886
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm893 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm892(arg1): ## timp: strn_print(1029)
      pyxtnm888 = arg1
      ## I1CMP:start
      ## let
      pyxtnm891 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(889);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(889))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm890 = XATSDAPP(XATS2PY_strn_print(pyxtnm888))
      pyxtnm891 = pyxtnm890
      ## end-of(let)
      ## I1CMP:return:pyxtnm891
      return pyxtnm891
    ## endtimp(strn_print(1029))
    pyxtnm893 = pyxtnm892
    pyxtnm894 = XATSDAPP(pyxtnm893(pyxtnm882))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm896(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm895 = XATSTUP0([])
      ## I1CMP:return:pyxtnm895
      return pyxtnm895
    ## endtimp(gs_print$sep(794))
    pyxtnm897 = XATSDAPP(pyxtnm896())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm898 = None
    pyxtnm898 = pyxtnm879
    pyxtnm899 = XATSDAPP(pyxtnm898(pyxtnm883))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm901(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm900 = XATSTUP0([])
      ## I1CMP:return:pyxtnm900
      return pyxtnm900
    ## endtimp(gs_print$end(795))
    pyxtnm902 = XATSDAPP(pyxtnm901())
    pyxtnm903 = pyxtnm902
    ## end-of(let)
    ## I1CMP:return:pyxtnm903
    return pyxtnm903
  ## endtimp(gs_print_a2(798))
  pyxtnm905 = XATSDAPP(pyxtnm904(pyxtnm880, pyxtnm881))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm911 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm910(arg1): ## timp: strn_print(1029)
    pyxtnm906 = arg1
    ## I1CMP:start
    ## let
    pyxtnm909 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(907);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(907))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm908 = XATSDAPP(XATS2PY_strn_print(pyxtnm906))
    pyxtnm909 = pyxtnm908
    ## end-of(let)
    ## I1CMP:return:pyxtnm909
    return pyxtnm909
  ## endtimp(strn_print(1029))
  pyxtnm911 = pyxtnm910
  pyxtnm912 = XATSDAPP(pyxtnm911(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm912
  return pyxtnm912
## endtimp(gs_println_a2(811))
pyxtnm914 = XATSDAPP(pyxtnm913(XATSSTRN("I = "), pyxtnm27))
pyxtnm915 = pyxtnm914
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2572(line=170,offs=1)--2600(line=170,offs=29)))
## I1VALDCL
pyxtnm951 = None
## LCSRCsome1(lambda1.dats)@(2581(line=170,offs=10)--2589(line=170,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm949(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm916 = arg1
  pyxtnm917 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm940(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm918 = arg1
    pyxtnm919 = arg2
    ## I1CMP:start
    ## let
    pyxtnm939 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm923 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm921(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm920 = XATSTUP0([])
      ## I1CMP:return:pyxtnm920
      return pyxtnm920
    ## endtimp(gs_print$beg(793))
    pyxtnm922 = XATSDAPP(pyxtnm921())
    pyxtnm923 = pyxtnm922
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm929 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm928(arg1): ## timp: strn_print(1029)
      pyxtnm924 = arg1
      ## I1CMP:start
      ## let
      pyxtnm927 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(925);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(925))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm926 = XATSDAPP(XATS2PY_strn_print(pyxtnm924))
      pyxtnm927 = pyxtnm926
      ## end-of(let)
      ## I1CMP:return:pyxtnm927
      return pyxtnm927
    ## endtimp(strn_print(1029))
    pyxtnm929 = pyxtnm928
    pyxtnm930 = XATSDAPP(pyxtnm929(pyxtnm918))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm932(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm931 = XATSTUP0([])
      ## I1CMP:return:pyxtnm931
      return pyxtnm931
    ## endtimp(gs_print$sep(794))
    pyxtnm933 = XATSDAPP(pyxtnm932())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm934 = None
    pyxtnm934 = pyxtnm879
    pyxtnm935 = XATSDAPP(pyxtnm934(pyxtnm919))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm937(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm936 = XATSTUP0([])
      ## I1CMP:return:pyxtnm936
      return pyxtnm936
    ## endtimp(gs_print$end(795))
    pyxtnm938 = XATSDAPP(pyxtnm937())
    pyxtnm939 = pyxtnm938
    ## end-of(let)
    ## I1CMP:return:pyxtnm939
    return pyxtnm939
  ## endtimp(gs_print_a2(798))
  pyxtnm941 = XATSDAPP(pyxtnm940(pyxtnm916, pyxtnm917))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm947 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm946(arg1): ## timp: strn_print(1029)
    pyxtnm942 = arg1
    ## I1CMP:start
    ## let
    pyxtnm945 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(943);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(943))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm944 = XATSDAPP(XATS2PY_strn_print(pyxtnm942))
    pyxtnm945 = pyxtnm944
    ## end-of(let)
    ## I1CMP:return:pyxtnm945
    return pyxtnm945
  ## endtimp(strn_print(1029))
  pyxtnm947 = pyxtnm946
  pyxtnm948 = XATSDAPP(pyxtnm947(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm948
  return pyxtnm948
## endtimp(gs_println_a2(811))
pyxtnm950 = XATSDAPP(pyxtnm949(XATSSTRN("K = "), pyxtnm30))
pyxtnm951 = pyxtnm950
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2601(line=171,offs=1)--2629(line=171,offs=29)))
## I1VALDCL
pyxtnm987 = None
## LCSRCsome1(lambda1.dats)@(2610(line=171,offs=10)--2618(line=171,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm985(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm952 = arg1
  pyxtnm953 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm976(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm954 = arg1
    pyxtnm955 = arg2
    ## I1CMP:start
    ## let
    pyxtnm975 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm959 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm957(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm956 = XATSTUP0([])
      ## I1CMP:return:pyxtnm956
      return pyxtnm956
    ## endtimp(gs_print$beg(793))
    pyxtnm958 = XATSDAPP(pyxtnm957())
    pyxtnm959 = pyxtnm958
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm965 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm964(arg1): ## timp: strn_print(1029)
      pyxtnm960 = arg1
      ## I1CMP:start
      ## let
      pyxtnm963 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(961);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(961))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm962 = XATSDAPP(XATS2PY_strn_print(pyxtnm960))
      pyxtnm963 = pyxtnm962
      ## end-of(let)
      ## I1CMP:return:pyxtnm963
      return pyxtnm963
    ## endtimp(strn_print(1029))
    pyxtnm965 = pyxtnm964
    pyxtnm966 = XATSDAPP(pyxtnm965(pyxtnm954))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm968(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm967 = XATSTUP0([])
      ## I1CMP:return:pyxtnm967
      return pyxtnm967
    ## endtimp(gs_print$sep(794))
    pyxtnm969 = XATSDAPP(pyxtnm968())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm970 = None
    pyxtnm970 = pyxtnm879
    pyxtnm971 = XATSDAPP(pyxtnm970(pyxtnm955))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm973(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm972 = XATSTUP0([])
      ## I1CMP:return:pyxtnm972
      return pyxtnm972
    ## endtimp(gs_print$end(795))
    pyxtnm974 = XATSDAPP(pyxtnm973())
    pyxtnm975 = pyxtnm974
    ## end-of(let)
    ## I1CMP:return:pyxtnm975
    return pyxtnm975
  ## endtimp(gs_print_a2(798))
  pyxtnm977 = XATSDAPP(pyxtnm976(pyxtnm952, pyxtnm953))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm983 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm982(arg1): ## timp: strn_print(1029)
    pyxtnm978 = arg1
    ## I1CMP:start
    ## let
    pyxtnm981 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(979);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(979))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm980 = XATSDAPP(XATS2PY_strn_print(pyxtnm978))
    pyxtnm981 = pyxtnm980
    ## end-of(let)
    ## I1CMP:return:pyxtnm981
    return pyxtnm981
  ## endtimp(strn_print(1029))
  pyxtnm983 = pyxtnm982
  pyxtnm984 = XATSDAPP(pyxtnm983(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm984
  return pyxtnm984
## endtimp(gs_println_a2(811))
pyxtnm986 = XATSDAPP(pyxtnm985(XATSSTRN("S = "), pyxtnm37))
pyxtnm987 = pyxtnm986
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2630(line=172,offs=1)--2660(line=172,offs=31)))
## I1VALDCL
pyxtnm1023 = None
## LCSRCsome1(lambda1.dats)@(2639(line=172,offs=10)--2647(line=172,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1021(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm988 = arg1
  pyxtnm989 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1012(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm990 = arg1
    pyxtnm991 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1011 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm995 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm993(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm992 = XATSTUP0([])
      ## I1CMP:return:pyxtnm992
      return pyxtnm992
    ## endtimp(gs_print$beg(793))
    pyxtnm994 = XATSDAPP(pyxtnm993())
    pyxtnm995 = pyxtnm994
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1001 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1000(arg1): ## timp: strn_print(1029)
      pyxtnm996 = arg1
      ## I1CMP:start
      ## let
      pyxtnm999 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(997);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(997))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm998 = XATSDAPP(XATS2PY_strn_print(pyxtnm996))
      pyxtnm999 = pyxtnm998
      ## end-of(let)
      ## I1CMP:return:pyxtnm999
      return pyxtnm999
    ## endtimp(strn_print(1029))
    pyxtnm1001 = pyxtnm1000
    pyxtnm1002 = XATSDAPP(pyxtnm1001(pyxtnm990))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1004(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1003 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1003
      return pyxtnm1003
    ## endtimp(gs_print$sep(794))
    pyxtnm1005 = XATSDAPP(pyxtnm1004())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1006 = None
    pyxtnm1006 = pyxtnm879
    pyxtnm1007 = XATSDAPP(pyxtnm1006(pyxtnm991))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1009(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1008 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1008
      return pyxtnm1008
    ## endtimp(gs_print$end(795))
    pyxtnm1010 = XATSDAPP(pyxtnm1009())
    pyxtnm1011 = pyxtnm1010
    ## end-of(let)
    ## I1CMP:return:pyxtnm1011
    return pyxtnm1011
  ## endtimp(gs_print_a2(798))
  pyxtnm1013 = XATSDAPP(pyxtnm1012(pyxtnm988, pyxtnm989))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1019 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1018(arg1): ## timp: strn_print(1029)
    pyxtnm1014 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1017 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1015);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1015))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1016 = XATSDAPP(XATS2PY_strn_print(pyxtnm1014))
    pyxtnm1017 = pyxtnm1016
    ## end-of(let)
    ## I1CMP:return:pyxtnm1017
    return pyxtnm1017
  ## endtimp(strn_print(1029))
  pyxtnm1019 = pyxtnm1018
  pyxtnm1020 = XATSDAPP(pyxtnm1019(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1020
  return pyxtnm1020
## endtimp(gs_println_a2(811))
pyxtnm1022 = XATSDAPP(pyxtnm1021(XATSSTRN("K1 = "), pyxtnm40))
pyxtnm1023 = pyxtnm1022
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2661(line=173,offs=1)--2697(line=173,offs=37)))
## I1VALDCL
pyxtnm1059 = None
## LCSRCsome1(lambda1.dats)@(2670(line=173,offs=10)--2678(line=173,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1057(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1024 = arg1
  pyxtnm1025 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1048(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1026 = arg1
    pyxtnm1027 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1047 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1031 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1029(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1028 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1028
      return pyxtnm1028
    ## endtimp(gs_print$beg(793))
    pyxtnm1030 = XATSDAPP(pyxtnm1029())
    pyxtnm1031 = pyxtnm1030
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1037 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1036(arg1): ## timp: strn_print(1029)
      pyxtnm1032 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1035 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1033);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1033))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1034 = XATSDAPP(XATS2PY_strn_print(pyxtnm1032))
      pyxtnm1035 = pyxtnm1034
      ## end-of(let)
      ## I1CMP:return:pyxtnm1035
      return pyxtnm1035
    ## endtimp(strn_print(1029))
    pyxtnm1037 = pyxtnm1036
    pyxtnm1038 = XATSDAPP(pyxtnm1037(pyxtnm1026))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1040(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1039 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1039
      return pyxtnm1039
    ## endtimp(gs_print$sep(794))
    pyxtnm1041 = XATSDAPP(pyxtnm1040())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1042 = None
    pyxtnm1042 = pyxtnm879
    pyxtnm1043 = XATSDAPP(pyxtnm1042(pyxtnm1027))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1045(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1044 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1044
      return pyxtnm1044
    ## endtimp(gs_print$end(795))
    pyxtnm1046 = XATSDAPP(pyxtnm1045())
    pyxtnm1047 = pyxtnm1046
    ## end-of(let)
    ## I1CMP:return:pyxtnm1047
    return pyxtnm1047
  ## endtimp(gs_print_a2(798))
  pyxtnm1049 = XATSDAPP(pyxtnm1048(pyxtnm1024, pyxtnm1025))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1055 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1054(arg1): ## timp: strn_print(1029)
    pyxtnm1050 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1053 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1051);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1051))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1052 = XATSDAPP(XATS2PY_strn_print(pyxtnm1050))
    pyxtnm1053 = pyxtnm1052
    ## end-of(let)
    ## I1CMP:return:pyxtnm1053
    return pyxtnm1053
  ## endtimp(strn_print(1029))
  pyxtnm1055 = pyxtnm1054
  pyxtnm1056 = XATSDAPP(pyxtnm1055(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1056
  return pyxtnm1056
## endtimp(gs_println_a2(811))
pyxtnm1058 = XATSDAPP(pyxtnm1057(XATSSTRN("omega = "), pyxtnm43))
pyxtnm1059 = pyxtnm1058
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2698(line=174,offs=1)--2734(line=174,offs=37)))
## I1VALDCL
pyxtnm1095 = None
## LCSRCsome1(lambda1.dats)@(2707(line=174,offs=10)--2715(line=174,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1093(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1060 = arg1
  pyxtnm1061 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1084(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1062 = arg1
    pyxtnm1063 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1083 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1067 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1065(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1064 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1064
      return pyxtnm1064
    ## endtimp(gs_print$beg(793))
    pyxtnm1066 = XATSDAPP(pyxtnm1065())
    pyxtnm1067 = pyxtnm1066
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1073 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1072(arg1): ## timp: strn_print(1029)
      pyxtnm1068 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1071 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1069);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1069))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1070 = XATSDAPP(XATS2PY_strn_print(pyxtnm1068))
      pyxtnm1071 = pyxtnm1070
      ## end-of(let)
      ## I1CMP:return:pyxtnm1071
      return pyxtnm1071
    ## endtimp(strn_print(1029))
    pyxtnm1073 = pyxtnm1072
    pyxtnm1074 = XATSDAPP(pyxtnm1073(pyxtnm1062))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1076(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1075 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1075
      return pyxtnm1075
    ## endtimp(gs_print$sep(794))
    pyxtnm1077 = XATSDAPP(pyxtnm1076())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1078 = None
    pyxtnm1078 = pyxtnm879
    pyxtnm1079 = XATSDAPP(pyxtnm1078(pyxtnm1063))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1081(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1080 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1080
      return pyxtnm1080
    ## endtimp(gs_print$end(795))
    pyxtnm1082 = XATSDAPP(pyxtnm1081())
    pyxtnm1083 = pyxtnm1082
    ## end-of(let)
    ## I1CMP:return:pyxtnm1083
    return pyxtnm1083
  ## endtimp(gs_print_a2(798))
  pyxtnm1085 = XATSDAPP(pyxtnm1084(pyxtnm1060, pyxtnm1061))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1091 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1090(arg1): ## timp: strn_print(1029)
    pyxtnm1086 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1089 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1087);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1087))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1088 = XATSDAPP(XATS2PY_strn_print(pyxtnm1086))
    pyxtnm1089 = pyxtnm1088
    ## end-of(let)
    ## I1CMP:return:pyxtnm1089
    return pyxtnm1089
  ## endtimp(strn_print(1029))
  pyxtnm1091 = pyxtnm1090
  pyxtnm1092 = XATSDAPP(pyxtnm1091(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1092
  return pyxtnm1092
## endtimp(gs_println_a2(811))
pyxtnm1094 = XATSDAPP(pyxtnm1093(XATSSTRN("Omega = "), pyxtnm45))
pyxtnm1095 = pyxtnm1094
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2824(line=183,offs=1)--2876(line=185,offs=41)))
## I1VALDCL
pyxtnm1116 = None
def pyxtnm1115(arg1, arg2): ## { // lam0(T_LAM(0))
  pyxtnm1096 = arg1
  pyxtnm1097 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(2862(line=185,offs=27)--2866(line=185,offs=31))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm1111(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm1098 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1110 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm1100 = None
    pyxtnm1099 = XATSPFLT(pyxtnm1098[0])
    pyxtnm1100 = pyxtnm1099
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm1102 = None
    pyxtnm1101 = XATSPFLT(pyxtnm1098[1])
    pyxtnm1102 = pyxtnm1101
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm1108(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm1103 = arg1
      pyxtnm1104 = arg2
      ## I1CMP:start
      pyxtnm1105 = XATSCAPP("list_nil", [0])
      pyxtnm1106 = XATSCAPP("list_cons", [1, pyxtnm1104, pyxtnm1105])
      pyxtnm1107 = XATSCAPP("list_cons", [1, pyxtnm1103, pyxtnm1106])
      ## I1CMP:return:pyxtnm1107
      return pyxtnm1107
    ## endtimp(list_make_2val(1171))
    pyxtnm1109 = XATSDAPP(pyxtnm1108(pyxtnm1100, pyxtnm1102))
    pyxtnm1110 = pyxtnm1109
    ## end-of(let)
    ## I1CMP:return:pyxtnm1110
    return pyxtnm1110
  ## endtimp(list_make_t0up2(1191))
  pyxtnm1112 = XATSTUP1(XATSTRCD(0), [pyxtnm1096, pyxtnm1097])
  pyxtnm1113 = XATSDAPP(pyxtnm1111(pyxtnm1112))
  pyxtnm1114 = XATSCAPP("TMopr", [5, XATSSTRN("+"), pyxtnm1113])
  ## I1CMP:return:pyxtnm1114
  return pyxtnm1114
## } // end(lam0)
pyxtnm1116 = pyxtnm1115
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2877(line=186,offs=1)--2929(line=188,offs=41)))
## I1VALDCL
pyxtnm1137 = None
def pyxtnm1136(arg1, arg2): ## { // lam0(T_LAM(0))
  pyxtnm1117 = arg1
  pyxtnm1118 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(2915(line=188,offs=27)--2919(line=188,offs=31))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm1132(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm1119 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1131 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm1121 = None
    pyxtnm1120 = XATSPFLT(pyxtnm1119[0])
    pyxtnm1121 = pyxtnm1120
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm1123 = None
    pyxtnm1122 = XATSPFLT(pyxtnm1119[1])
    pyxtnm1123 = pyxtnm1122
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm1129(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm1124 = arg1
      pyxtnm1125 = arg2
      ## I1CMP:start
      pyxtnm1126 = XATSCAPP("list_nil", [0])
      pyxtnm1127 = XATSCAPP("list_cons", [1, pyxtnm1125, pyxtnm1126])
      pyxtnm1128 = XATSCAPP("list_cons", [1, pyxtnm1124, pyxtnm1127])
      ## I1CMP:return:pyxtnm1128
      return pyxtnm1128
    ## endtimp(list_make_2val(1171))
    pyxtnm1130 = XATSDAPP(pyxtnm1129(pyxtnm1121, pyxtnm1123))
    pyxtnm1131 = pyxtnm1130
    ## end-of(let)
    ## I1CMP:return:pyxtnm1131
    return pyxtnm1131
  ## endtimp(list_make_t0up2(1191))
  pyxtnm1133 = XATSTUP1(XATSTRCD(0), [pyxtnm1117, pyxtnm1118])
  pyxtnm1134 = XATSDAPP(pyxtnm1132(pyxtnm1133))
  pyxtnm1135 = XATSCAPP("TMopr", [5, XATSSTRN("-"), pyxtnm1134])
  ## I1CMP:return:pyxtnm1135
  return pyxtnm1135
## } // end(lam0)
pyxtnm1137 = pyxtnm1136
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2930(line=189,offs=1)--2982(line=191,offs=41)))
## I1VALDCL
pyxtnm1158 = None
def pyxtnm1157(arg1, arg2): ## { // lam0(T_LAM(0))
  pyxtnm1138 = arg1
  pyxtnm1139 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(2968(line=191,offs=27)--2972(line=191,offs=31))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm1153(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm1140 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1152 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm1142 = None
    pyxtnm1141 = XATSPFLT(pyxtnm1140[0])
    pyxtnm1142 = pyxtnm1141
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm1144 = None
    pyxtnm1143 = XATSPFLT(pyxtnm1140[1])
    pyxtnm1144 = pyxtnm1143
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm1150(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm1145 = arg1
      pyxtnm1146 = arg2
      ## I1CMP:start
      pyxtnm1147 = XATSCAPP("list_nil", [0])
      pyxtnm1148 = XATSCAPP("list_cons", [1, pyxtnm1146, pyxtnm1147])
      pyxtnm1149 = XATSCAPP("list_cons", [1, pyxtnm1145, pyxtnm1148])
      ## I1CMP:return:pyxtnm1149
      return pyxtnm1149
    ## endtimp(list_make_2val(1171))
    pyxtnm1151 = XATSDAPP(pyxtnm1150(pyxtnm1142, pyxtnm1144))
    pyxtnm1152 = pyxtnm1151
    ## end-of(let)
    ## I1CMP:return:pyxtnm1152
    return pyxtnm1152
  ## endtimp(list_make_t0up2(1191))
  pyxtnm1154 = XATSTUP1(XATSTRCD(0), [pyxtnm1138, pyxtnm1139])
  pyxtnm1155 = XATSDAPP(pyxtnm1153(pyxtnm1154))
  pyxtnm1156 = XATSCAPP("TMopr", [5, XATSSTRN("*"), pyxtnm1155])
  ## I1CMP:return:pyxtnm1156
  return pyxtnm1156
## } // end(lam0)
pyxtnm1158 = pyxtnm1157
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(2983(line=192,offs=1)--3035(line=194,offs=41)))
## I1VALDCL
pyxtnm1179 = None
def pyxtnm1178(arg1, arg2): ## { // lam0(T_LAM(0))
  pyxtnm1159 = arg1
  pyxtnm1160 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(3021(line=194,offs=27)--3025(line=194,offs=31))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm1174(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm1161 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1173 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm1163 = None
    pyxtnm1162 = XATSPFLT(pyxtnm1161[0])
    pyxtnm1163 = pyxtnm1162
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm1165 = None
    pyxtnm1164 = XATSPFLT(pyxtnm1161[1])
    pyxtnm1165 = pyxtnm1164
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm1171(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm1166 = arg1
      pyxtnm1167 = arg2
      ## I1CMP:start
      pyxtnm1168 = XATSCAPP("list_nil", [0])
      pyxtnm1169 = XATSCAPP("list_cons", [1, pyxtnm1167, pyxtnm1168])
      pyxtnm1170 = XATSCAPP("list_cons", [1, pyxtnm1166, pyxtnm1169])
      ## I1CMP:return:pyxtnm1170
      return pyxtnm1170
    ## endtimp(list_make_2val(1171))
    pyxtnm1172 = XATSDAPP(pyxtnm1171(pyxtnm1163, pyxtnm1165))
    pyxtnm1173 = pyxtnm1172
    ## end-of(let)
    ## I1CMP:return:pyxtnm1173
    return pyxtnm1173
  ## endtimp(list_make_t0up2(1191))
  pyxtnm1175 = XATSTUP1(XATSTRCD(0), [pyxtnm1159, pyxtnm1160])
  pyxtnm1176 = XATSDAPP(pyxtnm1174(pyxtnm1175))
  pyxtnm1177 = XATSCAPP("TMopr", [5, XATSSTRN("/"), pyxtnm1176])
  ## I1CMP:return:pyxtnm1177
  return pyxtnm1177
## } // end(lam0)
pyxtnm1179 = pyxtnm1178
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3036(line=195,offs=1)--3088(line=197,offs=41)))
## I1VALDCL
pyxtnm1200 = None
def pyxtnm1199(arg1, arg2): ## { // lam0(T_LAM(0))
  pyxtnm1180 = arg1
  pyxtnm1181 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(3074(line=197,offs=27)--3078(line=197,offs=31))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm1195(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm1182 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1194 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm1184 = None
    pyxtnm1183 = XATSPFLT(pyxtnm1182[0])
    pyxtnm1184 = pyxtnm1183
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm1186 = None
    pyxtnm1185 = XATSPFLT(pyxtnm1182[1])
    pyxtnm1186 = pyxtnm1185
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm1192(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm1187 = arg1
      pyxtnm1188 = arg2
      ## I1CMP:start
      pyxtnm1189 = XATSCAPP("list_nil", [0])
      pyxtnm1190 = XATSCAPP("list_cons", [1, pyxtnm1188, pyxtnm1189])
      pyxtnm1191 = XATSCAPP("list_cons", [1, pyxtnm1187, pyxtnm1190])
      ## I1CMP:return:pyxtnm1191
      return pyxtnm1191
    ## endtimp(list_make_2val(1171))
    pyxtnm1193 = XATSDAPP(pyxtnm1192(pyxtnm1184, pyxtnm1186))
    pyxtnm1194 = pyxtnm1193
    ## end-of(let)
    ## I1CMP:return:pyxtnm1194
    return pyxtnm1194
  ## endtimp(list_make_t0up2(1191))
  pyxtnm1196 = XATSTUP1(XATSTRCD(0), [pyxtnm1180, pyxtnm1181])
  pyxtnm1197 = XATSDAPP(pyxtnm1195(pyxtnm1196))
  pyxtnm1198 = XATSCAPP("TMopr", [5, XATSSTRN("%"), pyxtnm1197])
  ## I1CMP:return:pyxtnm1198
  return pyxtnm1198
## } // end(lam0)
pyxtnm1200 = pyxtnm1199
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3135(line=202,offs=1)--3229(line=211,offs=29)))
## I1VALDCL
pyxtnm1209 = None
## let
pyxtnm1208 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3193(line=210,offs=1)--3227(line=211,offs=27)))
## I1VALDCL
pyxtnm1202 = None
pyxtnm1201 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm1202 = pyxtnm1201
XATS000_patck(True)
## I1VALDCL
pyxtnm1204 = None
pyxtnm1203 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm1204 = pyxtnm1203
XATS000_patck(True)
pyxtnm1205 = XATSCAPP("TMapp", [4, pyxtnm1202, pyxtnm1204])
pyxtnm1206 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm1205])
pyxtnm1207 = XATSCAPP("TMlam", [3, XATSSTRN("f"), pyxtnm1206])
pyxtnm1208 = pyxtnm1207
## end-of(let)
pyxtnm1209 = pyxtnm1208
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3230(line=212,offs=1)--3336(line=224,offs=29)))
## I1VALDCL
pyxtnm1219 = None
## let
pyxtnm1218 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3300(line=223,offs=1)--3334(line=224,offs=27)))
## I1VALDCL
pyxtnm1211 = None
pyxtnm1210 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm1211 = pyxtnm1210
XATS000_patck(True)
## I1VALDCL
pyxtnm1213 = None
pyxtnm1212 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm1213 = pyxtnm1212
XATS000_patck(True)
pyxtnm1214 = XATSCAPP("TMapp", [4, pyxtnm1211, pyxtnm1213])
pyxtnm1215 = XATSCAPP("TMapp", [4, pyxtnm1211, pyxtnm1214])
pyxtnm1216 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm1215])
pyxtnm1217 = XATSCAPP("TMlam", [3, XATSSTRN("f"), pyxtnm1216])
pyxtnm1218 = pyxtnm1217
## end-of(let)
pyxtnm1219 = pyxtnm1218
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3340(line=226,offs=1)--3381(line=227,offs=28)))
## I1VALDCL
pyxtnm1255 = None
## LCSRCsome1(lambda1.dats)@(3354(line=227,offs=1)--3362(line=227,offs=9))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1253(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1220 = arg1
  pyxtnm1221 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1244(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1222 = arg1
    pyxtnm1223 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1243 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1227 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1225(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1224 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1224
      return pyxtnm1224
    ## endtimp(gs_print$beg(793))
    pyxtnm1226 = XATSDAPP(pyxtnm1225())
    pyxtnm1227 = pyxtnm1226
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1233 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1232(arg1): ## timp: strn_print(1029)
      pyxtnm1228 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1231 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1229);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1229))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1230 = XATSDAPP(XATS2PY_strn_print(pyxtnm1228))
      pyxtnm1231 = pyxtnm1230
      ## end-of(let)
      ## I1CMP:return:pyxtnm1231
      return pyxtnm1231
    ## endtimp(strn_print(1029))
    pyxtnm1233 = pyxtnm1232
    pyxtnm1234 = XATSDAPP(pyxtnm1233(pyxtnm1222))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1236(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1235 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1235
      return pyxtnm1235
    ## endtimp(gs_print$sep(794))
    pyxtnm1237 = XATSDAPP(pyxtnm1236())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1238 = None
    pyxtnm1238 = pyxtnm879
    pyxtnm1239 = XATSDAPP(pyxtnm1238(pyxtnm1223))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1241(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1240 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1240
      return pyxtnm1240
    ## endtimp(gs_print$end(795))
    pyxtnm1242 = XATSDAPP(pyxtnm1241())
    pyxtnm1243 = pyxtnm1242
    ## end-of(let)
    ## I1CMP:return:pyxtnm1243
    return pyxtnm1243
  ## endtimp(gs_print_a2(798))
  pyxtnm1245 = XATSDAPP(pyxtnm1244(pyxtnm1220, pyxtnm1221))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1251 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1250(arg1): ## timp: strn_print(1029)
    pyxtnm1246 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1249 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1247);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1247))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1248 = XATSDAPP(XATS2PY_strn_print(pyxtnm1246))
    pyxtnm1249 = pyxtnm1248
    ## end-of(let)
    ## I1CMP:return:pyxtnm1249
    return pyxtnm1249
  ## endtimp(strn_print(1029))
  pyxtnm1251 = pyxtnm1250
  pyxtnm1252 = XATSDAPP(pyxtnm1251(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1252
  return pyxtnm1252
## endtimp(gs_println_a2(811))
pyxtnm1254 = XATSDAPP(pyxtnm1253(XATSSTRN("TMone = "), pyxtnm1209))
pyxtnm1255 = pyxtnm1254
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3382(line=228,offs=1)--3423(line=229,offs=28)))
## I1VALDCL
pyxtnm1291 = None
## LCSRCsome1(lambda1.dats)@(3396(line=229,offs=1)--3404(line=229,offs=9))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1289(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1256 = arg1
  pyxtnm1257 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1280(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1258 = arg1
    pyxtnm1259 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1279 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1263 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1261(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1260 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1260
      return pyxtnm1260
    ## endtimp(gs_print$beg(793))
    pyxtnm1262 = XATSDAPP(pyxtnm1261())
    pyxtnm1263 = pyxtnm1262
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1269 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1268(arg1): ## timp: strn_print(1029)
      pyxtnm1264 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1267 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1265);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1265))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1266 = XATSDAPP(XATS2PY_strn_print(pyxtnm1264))
      pyxtnm1267 = pyxtnm1266
      ## end-of(let)
      ## I1CMP:return:pyxtnm1267
      return pyxtnm1267
    ## endtimp(strn_print(1029))
    pyxtnm1269 = pyxtnm1268
    pyxtnm1270 = XATSDAPP(pyxtnm1269(pyxtnm1258))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1272(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1271 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1271
      return pyxtnm1271
    ## endtimp(gs_print$sep(794))
    pyxtnm1273 = XATSDAPP(pyxtnm1272())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1274 = None
    pyxtnm1274 = pyxtnm879
    pyxtnm1275 = XATSDAPP(pyxtnm1274(pyxtnm1259))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1277(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1276 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1276
      return pyxtnm1276
    ## endtimp(gs_print$end(795))
    pyxtnm1278 = XATSDAPP(pyxtnm1277())
    pyxtnm1279 = pyxtnm1278
    ## end-of(let)
    ## I1CMP:return:pyxtnm1279
    return pyxtnm1279
  ## endtimp(gs_print_a2(798))
  pyxtnm1281 = XATSDAPP(pyxtnm1280(pyxtnm1256, pyxtnm1257))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1287 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1286(arg1): ## timp: strn_print(1029)
    pyxtnm1282 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1285 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1283);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1283))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1284 = XATSDAPP(XATS2PY_strn_print(pyxtnm1282))
    pyxtnm1285 = pyxtnm1284
    ## end-of(let)
    ## I1CMP:return:pyxtnm1285
    return pyxtnm1285
  ## endtimp(strn_print(1029))
  pyxtnm1287 = pyxtnm1286
  pyxtnm1288 = XATSDAPP(pyxtnm1287(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1288
  return pyxtnm1288
## endtimp(gs_println_a2(811))
pyxtnm1290 = XATSDAPP(pyxtnm1289(XATSSTRN("TMtwo = "), pyxtnm1219))
pyxtnm1291 = pyxtnm1290
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3470(line=234,offs=1)--3533(line=238,offs=28)))
## I1VALDCL
pyxtnm1297 = None
## let
pyxtnm1296 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3486(line=236,offs=1)--3502(line=237,offs=9)))
## I1VALDCL
pyxtnm1293 = None
pyxtnm1292 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm1293 = pyxtnm1292
XATS000_patck(True)
pyxtnm1294 = XATSDAPP(pyxtnm1116(pyxtnm1293, pyxtnm1293))
pyxtnm1295 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm1294])
pyxtnm1296 = pyxtnm1295
## end-of(let)
pyxtnm1297 = pyxtnm1296
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3534(line=239,offs=1)--3607(line=243,offs=38)))
## I1VALDCL
pyxtnm1304 = None
## let
pyxtnm1303 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3550(line=241,offs=1)--3566(line=242,offs=9)))
## I1VALDCL
pyxtnm1299 = None
pyxtnm1298 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm1299 = pyxtnm1298
XATS000_patck(True)
pyxtnm1300 = XATSDAPP(pyxtnm1116(pyxtnm1299, pyxtnm1299))
pyxtnm1301 = XATSDAPP(pyxtnm1116(pyxtnm1299, pyxtnm1300))
pyxtnm1302 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm1301])
pyxtnm1303 = pyxtnm1302
## end-of(let)
pyxtnm1304 = pyxtnm1303
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3611(line=245,offs=1)--3652(line=245,offs=42)))
## I1VALDCL
pyxtnm1340 = None
## LCSRCsome1(lambda1.dats)@(3625(line=245,offs=15)--3633(line=245,offs=23))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1338(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1305 = arg1
  pyxtnm1306 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1329(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1307 = arg1
    pyxtnm1308 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1328 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1312 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1310(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1309 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1309
      return pyxtnm1309
    ## endtimp(gs_print$beg(793))
    pyxtnm1311 = XATSDAPP(pyxtnm1310())
    pyxtnm1312 = pyxtnm1311
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1318 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1317(arg1): ## timp: strn_print(1029)
      pyxtnm1313 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1316 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1314);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1314))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1315 = XATSDAPP(XATS2PY_strn_print(pyxtnm1313))
      pyxtnm1316 = pyxtnm1315
      ## end-of(let)
      ## I1CMP:return:pyxtnm1316
      return pyxtnm1316
    ## endtimp(strn_print(1029))
    pyxtnm1318 = pyxtnm1317
    pyxtnm1319 = XATSDAPP(pyxtnm1318(pyxtnm1307))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1321(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1320 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1320
      return pyxtnm1320
    ## endtimp(gs_print$sep(794))
    pyxtnm1322 = XATSDAPP(pyxtnm1321())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1323 = None
    pyxtnm1323 = pyxtnm879
    pyxtnm1324 = XATSDAPP(pyxtnm1323(pyxtnm1308))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1326(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1325 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1325
      return pyxtnm1325
    ## endtimp(gs_print$end(795))
    pyxtnm1327 = XATSDAPP(pyxtnm1326())
    pyxtnm1328 = pyxtnm1327
    ## end-of(let)
    ## I1CMP:return:pyxtnm1328
    return pyxtnm1328
  ## endtimp(gs_print_a2(798))
  pyxtnm1330 = XATSDAPP(pyxtnm1329(pyxtnm1305, pyxtnm1306))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1336 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1335(arg1): ## timp: strn_print(1029)
    pyxtnm1331 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1334 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1332);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1332))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1333 = XATSDAPP(XATS2PY_strn_print(pyxtnm1331))
    pyxtnm1334 = pyxtnm1333
    ## end-of(let)
    ## I1CMP:return:pyxtnm1334
    return pyxtnm1334
  ## endtimp(strn_print(1029))
  pyxtnm1336 = pyxtnm1335
  pyxtnm1337 = XATSDAPP(pyxtnm1336(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1337
  return pyxtnm1337
## endtimp(gs_println_a2(811))
pyxtnm1339 = XATSDAPP(pyxtnm1338(XATSSTRN("TMdbl = "), pyxtnm1297))
pyxtnm1340 = pyxtnm1339
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3653(line=246,offs=1)--3694(line=246,offs=42)))
## I1VALDCL
pyxtnm1376 = None
## LCSRCsome1(lambda1.dats)@(3667(line=246,offs=15)--3675(line=246,offs=23))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1374(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1341 = arg1
  pyxtnm1342 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1365(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1343 = arg1
    pyxtnm1344 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1364 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1348 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1346(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1345 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1345
      return pyxtnm1345
    ## endtimp(gs_print$beg(793))
    pyxtnm1347 = XATSDAPP(pyxtnm1346())
    pyxtnm1348 = pyxtnm1347
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1354 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1353(arg1): ## timp: strn_print(1029)
      pyxtnm1349 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1352 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1350);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1350))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1351 = XATSDAPP(XATS2PY_strn_print(pyxtnm1349))
      pyxtnm1352 = pyxtnm1351
      ## end-of(let)
      ## I1CMP:return:pyxtnm1352
      return pyxtnm1352
    ## endtimp(strn_print(1029))
    pyxtnm1354 = pyxtnm1353
    pyxtnm1355 = XATSDAPP(pyxtnm1354(pyxtnm1343))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1357(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1356 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1356
      return pyxtnm1356
    ## endtimp(gs_print$sep(794))
    pyxtnm1358 = XATSDAPP(pyxtnm1357())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1359 = None
    pyxtnm1359 = pyxtnm879
    pyxtnm1360 = XATSDAPP(pyxtnm1359(pyxtnm1344))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1362(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1361 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1361
      return pyxtnm1361
    ## endtimp(gs_print$end(795))
    pyxtnm1363 = XATSDAPP(pyxtnm1362())
    pyxtnm1364 = pyxtnm1363
    ## end-of(let)
    ## I1CMP:return:pyxtnm1364
    return pyxtnm1364
  ## endtimp(gs_print_a2(798))
  pyxtnm1366 = XATSDAPP(pyxtnm1365(pyxtnm1341, pyxtnm1342))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1372 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1371(arg1): ## timp: strn_print(1029)
    pyxtnm1367 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1370 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1368);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1368))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1369 = XATSDAPP(XATS2PY_strn_print(pyxtnm1367))
    pyxtnm1370 = pyxtnm1369
    ## end-of(let)
    ## I1CMP:return:pyxtnm1370
    return pyxtnm1370
  ## endtimp(strn_print(1029))
  pyxtnm1372 = pyxtnm1371
  pyxtnm1373 = XATSDAPP(pyxtnm1372(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1373
  return pyxtnm1373
## endtimp(gs_println_a2(811))
pyxtnm1375 = XATSDAPP(pyxtnm1374(XATSSTRN("TMtpl = "), pyxtnm1304))
pyxtnm1376 = pyxtnm1375
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3741(line=251,offs=1)--3804(line=255,offs=28)))
## I1VALDCL
pyxtnm1382 = None
## let
pyxtnm1381 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3757(line=253,offs=1)--3773(line=254,offs=9)))
## I1VALDCL
pyxtnm1378 = None
pyxtnm1377 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm1378 = pyxtnm1377
XATS000_patck(True)
pyxtnm1379 = XATSDAPP(pyxtnm1158(pyxtnm1378, pyxtnm1378))
pyxtnm1380 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm1379])
pyxtnm1381 = pyxtnm1380
## end-of(let)
pyxtnm1382 = pyxtnm1381
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3805(line=256,offs=1)--3878(line=260,offs=38)))
## I1VALDCL
pyxtnm1389 = None
## let
pyxtnm1388 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3821(line=258,offs=1)--3837(line=259,offs=9)))
## I1VALDCL
pyxtnm1384 = None
pyxtnm1383 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm1384 = pyxtnm1383
XATS000_patck(True)
pyxtnm1385 = XATSDAPP(pyxtnm1158(pyxtnm1384, pyxtnm1384))
pyxtnm1386 = XATSDAPP(pyxtnm1158(pyxtnm1384, pyxtnm1385))
pyxtnm1387 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm1386])
pyxtnm1388 = pyxtnm1387
## end-of(let)
pyxtnm1389 = pyxtnm1388
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3882(line=262,offs=1)--3923(line=262,offs=42)))
## I1VALDCL
pyxtnm1425 = None
## LCSRCsome1(lambda1.dats)@(3896(line=262,offs=15)--3904(line=262,offs=23))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1423(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1390 = arg1
  pyxtnm1391 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1414(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1392 = arg1
    pyxtnm1393 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1413 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1397 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1395(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1394 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1394
      return pyxtnm1394
    ## endtimp(gs_print$beg(793))
    pyxtnm1396 = XATSDAPP(pyxtnm1395())
    pyxtnm1397 = pyxtnm1396
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1403 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1402(arg1): ## timp: strn_print(1029)
      pyxtnm1398 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1401 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1399);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1399))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1400 = XATSDAPP(XATS2PY_strn_print(pyxtnm1398))
      pyxtnm1401 = pyxtnm1400
      ## end-of(let)
      ## I1CMP:return:pyxtnm1401
      return pyxtnm1401
    ## endtimp(strn_print(1029))
    pyxtnm1403 = pyxtnm1402
    pyxtnm1404 = XATSDAPP(pyxtnm1403(pyxtnm1392))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1406(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1405 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1405
      return pyxtnm1405
    ## endtimp(gs_print$sep(794))
    pyxtnm1407 = XATSDAPP(pyxtnm1406())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1408 = None
    pyxtnm1408 = pyxtnm879
    pyxtnm1409 = XATSDAPP(pyxtnm1408(pyxtnm1393))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1411(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1410 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1410
      return pyxtnm1410
    ## endtimp(gs_print$end(795))
    pyxtnm1412 = XATSDAPP(pyxtnm1411())
    pyxtnm1413 = pyxtnm1412
    ## end-of(let)
    ## I1CMP:return:pyxtnm1413
    return pyxtnm1413
  ## endtimp(gs_print_a2(798))
  pyxtnm1415 = XATSDAPP(pyxtnm1414(pyxtnm1390, pyxtnm1391))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1421 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1420(arg1): ## timp: strn_print(1029)
    pyxtnm1416 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1419 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1417);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1417))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1418 = XATSDAPP(XATS2PY_strn_print(pyxtnm1416))
    pyxtnm1419 = pyxtnm1418
    ## end-of(let)
    ## I1CMP:return:pyxtnm1419
    return pyxtnm1419
  ## endtimp(strn_print(1029))
  pyxtnm1421 = pyxtnm1420
  pyxtnm1422 = XATSDAPP(pyxtnm1421(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1422
  return pyxtnm1422
## endtimp(gs_println_a2(811))
pyxtnm1424 = XATSDAPP(pyxtnm1423(XATSSTRN("TMsqr = "), pyxtnm1382))
pyxtnm1425 = pyxtnm1424
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(3924(line=263,offs=1)--3965(line=263,offs=42)))
## I1VALDCL
pyxtnm1461 = None
## LCSRCsome1(lambda1.dats)@(3938(line=263,offs=15)--3946(line=263,offs=23))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1459(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1426 = arg1
  pyxtnm1427 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1450(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1428 = arg1
    pyxtnm1429 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1449 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1433 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1431(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1430 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1430
      return pyxtnm1430
    ## endtimp(gs_print$beg(793))
    pyxtnm1432 = XATSDAPP(pyxtnm1431())
    pyxtnm1433 = pyxtnm1432
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1439 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1438(arg1): ## timp: strn_print(1029)
      pyxtnm1434 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1437 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1435);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1435))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1436 = XATSDAPP(XATS2PY_strn_print(pyxtnm1434))
      pyxtnm1437 = pyxtnm1436
      ## end-of(let)
      ## I1CMP:return:pyxtnm1437
      return pyxtnm1437
    ## endtimp(strn_print(1029))
    pyxtnm1439 = pyxtnm1438
    pyxtnm1440 = XATSDAPP(pyxtnm1439(pyxtnm1428))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1442(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1441 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1441
      return pyxtnm1441
    ## endtimp(gs_print$sep(794))
    pyxtnm1443 = XATSDAPP(pyxtnm1442())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1444 = None
    pyxtnm1444 = pyxtnm879
    pyxtnm1445 = XATSDAPP(pyxtnm1444(pyxtnm1429))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1447(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1446 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1446
      return pyxtnm1446
    ## endtimp(gs_print$end(795))
    pyxtnm1448 = XATSDAPP(pyxtnm1447())
    pyxtnm1449 = pyxtnm1448
    ## end-of(let)
    ## I1CMP:return:pyxtnm1449
    return pyxtnm1449
  ## endtimp(gs_print_a2(798))
  pyxtnm1451 = XATSDAPP(pyxtnm1450(pyxtnm1426, pyxtnm1427))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1457 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1456(arg1): ## timp: strn_print(1029)
    pyxtnm1452 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1455 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1453);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1453))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1454 = XATSDAPP(XATS2PY_strn_print(pyxtnm1452))
    pyxtnm1455 = pyxtnm1454
    ## end-of(let)
    ## I1CMP:return:pyxtnm1455
    return pyxtnm1455
  ## endtimp(strn_print(1029))
  pyxtnm1457 = pyxtnm1456
  pyxtnm1458 = XATSDAPP(pyxtnm1457(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1458
  return pyxtnm1458
## endtimp(gs_println_a2(811))
pyxtnm1460 = XATSDAPP(pyxtnm1459(XATSSTRN("TMcbr = "), pyxtnm1389))
pyxtnm1461 = pyxtnm1460
XATS000_patck(True)
## I1Dextern(LCSRCsome1(lambda1.dats)@(4012(line=268,offs=1)--4076(line=272,offs=30)))
## I1Dfundclst(T_FUN(FNKfn1);$list();$list(term_subst(2645));$list(I1FUNDCL(term_subst(5202);$list(FJARGdarg($list(I1BNDcons(I1TNM(1462);I0Pvar(tm0(5203));$list(@(tm0(5203),I1Vtnm(I1TNM(1462))))),I1BNDcons(I1TNM(1463);I0Pvar(x00(5204));$list(@(x00(5204),I1Vtnm(I1TNM(1463))))),I1BNDcons(I1TNM(1464);I0Pvar(sub(5205));$list(@(sub(5205),I1Vtnm(I1TNM(1464))))))));TEQI1CMPnone())))
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(4080(line=274,offs=1)--4805(line=329,offs=4)))
def term_subst_4023(arg1, arg2, arg3): ## impl
  pyxtnm1465 = arg1
  pyxtnm1466 = arg2
  pyxtnm1467 = arg3
  ## I1CMP:start
  ## let
  pyxtnm1712 = None
  ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(4125(line=279,offs=1)--4174(line=281,offs=26)))
  ## I1VALDCL
  pyxtnm1471 = None
  def pyxtnm1470(arg1): ## { // lam0(T_LAM(0))
    pyxtnm1468 = arg1
    ## I1CMP:start
    pyxtnm1469 = XATSDAPP(term_subst_4023(pyxtnm1468, pyxtnm1466, pyxtnm1467))
    ## I1CMP:return:pyxtnm1469
    return pyxtnm1469
  ## } // end(lam0)
  pyxtnm1471 = pyxtnm1470
  XATS000_patck(True)
  pyxtnm1711 = None
  while True: ## do {
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1472);I0Pdap1(I0Pcon(TMint(32)));$list()))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMint",0))): ## { // gpt
      pyxtnm1472 = pyxtnm1465
      pyxtnm1711 = pyxtnm1465
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1473);I0Pdap1(I0Pcon(TMbtf(33)));$list()))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMbtf",1))): ## { // gpt
      pyxtnm1473 = pyxtnm1465
      pyxtnm1711 = pyxtnm1465
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1474);I0Pdapp(I0Pcon(TMvar(34));$list(I0Pvar(x01(5211))));$list(@(x01(5211),I1Vp1cn(I0Pcon(TMvar(34));I1Vtnm(I1TNM(1474));0)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMvar",2))): ## { // gpt
      pyxtnm1474 = pyxtnm1465
      ## LCSRCsome1(lambda1.dats)@(4261(line=292,offs=4)--4262(line=292,offs=5))
      ## I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
      ## T1IMPallx(strn_eq(1024), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
      ## T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
      pyxtnm1495 = None
      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
      ## I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
      ## T1IMPallx(g_eq(226), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
      ## T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5765],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[718],T2Pvar(x0[5765])))))))
      def pyxtnm1494(arg1, arg2): ## timp: g_eq(226)
        pyxtnm1475 = arg1
        pyxtnm1476 = arg2
        ## I1CMP:start
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
        ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
        ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
        ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
        def pyxtnm1483(arg1, arg2): ## timp: sint_eq$sint(920)
          pyxtnm1477 = arg1
          pyxtnm1478 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1482 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(1479);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(1479))))),I1BNDcons(I1TNM(1480);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(1480))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
          pyxtnm1481 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm1477, pyxtnm1478))
          pyxtnm1482 = pyxtnm1481
          ## end-of(let)
          ## I1CMP:return:pyxtnm1482
          return pyxtnm1482
        ## endtimp(sint_eq$sint(920))
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
        ## I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5765])))))
        ## T1IMPallx(g_cmp(230), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
        ## T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[722],T2Pcst(strn)))))))
        pyxtnm1491 = None
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
        ## I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
        ## T1IMPallx(strn_cmp(1028), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1623(line=57,offs=1)--1772(line=69,offs=2)))
        ## T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
        def pyxtnm1490(arg1, arg2): ## timp: strn_cmp(1028)
          pyxtnm1484 = arg1
          pyxtnm1485 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1489 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1703(line=65,offs=1)--1770(line=68,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_cmp(2612));$list(I1FUNDCL(XATS2PY_strn_cmp(5017);$list(FJARGdarg($list(I1BNDcons(I1TNM(1486);I0Pvar(x1(5018));$list(@(x1(5018),I1Vtnm(I1TNM(1486))))),I1BNDcons(I1TNM(1487);I0Pvar(x2(5019));$list(@(x2(5019),I1Vtnm(I1TNM(1487))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_cmp);G1Nlist($list())))))))
          pyxtnm1488 = XATSDAPP(XATS2PY_strn_cmp(pyxtnm1484, pyxtnm1485))
          pyxtnm1489 = pyxtnm1488
          ## end-of(let)
          ## I1CMP:return:pyxtnm1489
          return pyxtnm1489
        ## endtimp(strn_cmp(1028))
        pyxtnm1491 = pyxtnm1490
        pyxtnm1492 = XATSDAPP(pyxtnm1491(pyxtnm1475, pyxtnm1476))
        pyxtnm1493 = XATSDAPP(pyxtnm1483(pyxtnm1492, XATSINT1(0)))
        ## I1CMP:return:pyxtnm1493
        return pyxtnm1493
      ## endtimp(g_eq(226))
      pyxtnm1495 = pyxtnm1494
      pyxtnm1496 = XATSDAPP(pyxtnm1495(pyxtnm1466, XATSP1CN("TMvar", pyxtnm1474[0+1])))
      pyxtnm1497 = None
      if (pyxtnm1496):
        pyxtnm1497 = pyxtnm1467
      else:
        pyxtnm1497 = pyxtnm1465
      ## end-of(if)
      pyxtnm1711 = pyxtnm1497
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1498);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5212)),I0Pvar(tmx(5213))));$list(@(x01(5212),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1498));0)),@(tmx(5213),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1498));1)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMlam",3))): ## { // gpt
      pyxtnm1498 = pyxtnm1465
      ## LCSRCsome1(lambda1.dats)@(4314(line=296,offs=5)--4315(line=296,offs=6))
      ## I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
      ## T1IMPallx(strn_eq(1024), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
      ## T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
      pyxtnm1519 = None
      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
      ## I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
      ## T1IMPallx(g_eq(226), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
      ## T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5765],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[718],T2Pvar(x0[5765])))))))
      def pyxtnm1518(arg1, arg2): ## timp: g_eq(226)
        pyxtnm1499 = arg1
        pyxtnm1500 = arg2
        ## I1CMP:start
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
        ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
        ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
        ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
        def pyxtnm1507(arg1, arg2): ## timp: sint_eq$sint(920)
          pyxtnm1501 = arg1
          pyxtnm1502 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1506 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(1503);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(1503))))),I1BNDcons(I1TNM(1504);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(1504))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
          pyxtnm1505 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm1501, pyxtnm1502))
          pyxtnm1506 = pyxtnm1505
          ## end-of(let)
          ## I1CMP:return:pyxtnm1506
          return pyxtnm1506
        ## endtimp(sint_eq$sint(920))
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
        ## I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5765])))))
        ## T1IMPallx(g_cmp(230), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
        ## T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[722],T2Pcst(strn)))))))
        pyxtnm1515 = None
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
        ## I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
        ## T1IMPallx(strn_cmp(1028), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1623(line=57,offs=1)--1772(line=69,offs=2)))
        ## T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
        def pyxtnm1514(arg1, arg2): ## timp: strn_cmp(1028)
          pyxtnm1508 = arg1
          pyxtnm1509 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1513 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1703(line=65,offs=1)--1770(line=68,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_cmp(2612));$list(I1FUNDCL(XATS2PY_strn_cmp(5017);$list(FJARGdarg($list(I1BNDcons(I1TNM(1510);I0Pvar(x1(5018));$list(@(x1(5018),I1Vtnm(I1TNM(1510))))),I1BNDcons(I1TNM(1511);I0Pvar(x2(5019));$list(@(x2(5019),I1Vtnm(I1TNM(1511))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_cmp);G1Nlist($list())))))))
          pyxtnm1512 = XATSDAPP(XATS2PY_strn_cmp(pyxtnm1508, pyxtnm1509))
          pyxtnm1513 = pyxtnm1512
          ## end-of(let)
          ## I1CMP:return:pyxtnm1513
          return pyxtnm1513
        ## endtimp(strn_cmp(1028))
        pyxtnm1515 = pyxtnm1514
        pyxtnm1516 = XATSDAPP(pyxtnm1515(pyxtnm1499, pyxtnm1500))
        pyxtnm1517 = XATSDAPP(pyxtnm1507(pyxtnm1516, XATSINT1(0)))
        ## I1CMP:return:pyxtnm1517
        return pyxtnm1517
      ## endtimp(g_eq(226))
      pyxtnm1519 = pyxtnm1518
      pyxtnm1520 = XATSDAPP(pyxtnm1519(pyxtnm1466, XATSP1CN("TMlam", pyxtnm1498[0+1])))
      pyxtnm1523 = None
      if (pyxtnm1520):
        pyxtnm1523 = pyxtnm1465
      else:
        pyxtnm1521 = XATSDAPP(pyxtnm1471(XATSP1CN("TMlam", pyxtnm1498[1+1])))
        pyxtnm1522 = XATSCAPP("TMlam", [3, XATSP1CN("TMlam", pyxtnm1498[0+1]), pyxtnm1521])
        pyxtnm1523 = pyxtnm1522
      ## end-of(if)
      pyxtnm1711 = pyxtnm1523
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1524);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5214)),I0Pvar(tm2(5215))));$list(@(tm1(5214),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1524));0)),@(tm2(5215),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1524));1)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMapp",4))): ## { // gpt
      pyxtnm1524 = pyxtnm1465
      pyxtnm1525 = XATSDAPP(pyxtnm1471(XATSP1CN("TMapp", pyxtnm1524[0+1])))
      pyxtnm1526 = XATSDAPP(pyxtnm1471(XATSP1CN("TMapp", pyxtnm1524[1+1])))
      pyxtnm1527 = XATSCAPP("TMapp", [4, pyxtnm1525, pyxtnm1526])
      pyxtnm1711 = pyxtnm1527
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1528);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(f00(5216)),I0Pvar(tms(5217))));$list(@(f00(5216),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1528));0)),@(tms(5217),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1528));1)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMopr",5))): ## { // gpt
      pyxtnm1528 = pyxtnm1465
      ## LCSRCsome1(lambda1.dats)@(4453(line=306,offs=12)--4463(line=306,offs=22))
      ## I0Etapq(I0Ecst(f1un_map$list(316)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gfun000.sats)@(4882(line=281,offs=1)--4895(line=281,offs=14))));$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term)))))
      ## T1IMPallx(f1un_map$list(316), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gfun000.dats)@(5083(line=298,offs=1)--5181(line=304,offs=32)))
      ## T1IMPallx(f1un_map$list(316)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[5811],T2Pcst(term)),@(y0[5812],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(f1un_map$list(316);$list(@(x0[927],T2Pvar(x0[5811])),@(y0[928],T2Pvar(y0[5812])))))))
      def pyxtnm1623(arg1): ## timp: f1un_map$list(316)
        pyxtnm1529 = arg1
        ## I1CMP:start
        def pyxtnm1622(arg1): ## { // lam0(T_LAM(0))
          pyxtnm1530 = arg1
          ## I1CMP:start
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gfun000.dats)@(5150(line=304,offs=1)--5163(line=304,offs=14))
          ## I0Etapq(I0Ecst(list_map$f1un(1243)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(8026(line=382,offs=1)--8039(line=382,offs=14))));$list(T2JAG($list(T2Pvar(x0[5811]))),T2JAG($list(T2Pvar(y0[5812])))))
          ## T1IMPallx(list_map$f1un(1243), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(9918(line=664,offs=1)--9999(line=668,offs=37)))
          ## T1IMPallx(list_map$f1un(1243)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7330],T2Pcst(term)),@(y0[7331],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_map$f1un(1243);$list(@(x0[3333],T2Pvar(x0[7330])),@(y0[3334],T2Pvar(y0[7331])))))))
          pyxtnm1620 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(9963(line=668,offs=1)--9981(line=668,offs=19))
          ## I0Etapq(I0Ecst(gseq_map$f1un_list(428)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(13108(line=758,offs=1)--13126(line=758,offs=19))));$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pvar(x0[7330]),T2Pnone0())))),T2JAG($list(T2Pvar(x0[7330]))),T2JAG($list(T2Pvar(y0[7331])))))
          ## T1IMPallx(gseq_map$f1un_list(428), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14500(line=996,offs=1)--14631(line=1004,offs=43)))
          ## T1IMPallx(gseq_map$f1un_list(428)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6015],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6016],T2Pcst(term)),@(y0[6017],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map$f1un_list(428);$list(@(xs[1231],T2Pvar(xs[6015])),@(x0[1232],T2Pvar(x0[6016])),@(y0[1233],T2Pvar(y0[6017])))))))
          def pyxtnm1619(arg1, arg2): ## timp: gseq_map$f1un_list(428)
            pyxtnm1531 = arg1
            pyxtnm1532 = arg2
            ## I1CMP:start
            ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14589(line=1004,offs=1)--14608(line=1004,offs=20))
            ## I0Etapq(I0Ecst(gseq_map$f1un_llist(429)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(13306(line=771,offs=1)--13325(line=771,offs=20))));$list(T2JAG($list(T2Pvar(xs[6015]))),T2JAG($list(T2Pvar(x0[6016]))),T2JAG($list(T2Pvar(y0[6017])))))
            ## T1IMPallx(gseq_map$f1un_llist(429), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14781(line=1018,offs=1)--14943(line=1030,offs=2)))
            ## T1IMPallx(gseq_map$f1un_llist(429)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6021],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6022],T2Pcst(term)),@(y0[6023],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map$f1un_llist(429);$list(@(xs[1234],T2Pvar(xs[6021])),@(x0[1235],T2Pvar(x0[6022])),@(y0[1236],T2Pvar(y0[6023])))))))
            def pyxtnm1616(arg1, arg2): ## timp: gseq_map$f1un_llist(429)
              pyxtnm1533 = arg1
              pyxtnm1534 = arg2
              ## I1CMP:start
              ## let
              pyxtnm1615 = None
              ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14897(line=1028,offs=1)--14941(line=1029,offs=36)))
              ## I1Dimplmnt0(DIMPLone2(map$fopr(75);$list(@(x0[430],T2Pvar(x0[6022])),@(y0[431],T2Pvar(y0[6023]))))):timp
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14857(line=1025,offs=1)--14871(line=1025,offs=15))
              ## I0Etapq(I0Ecst(gseq_map_llist(425)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(12650(line=732,offs=1)--12664(line=732,offs=15))));$list(T2JAG($list(T2Pvar(xs[6021]))),T2JAG($list(T2Pvar(x0[6022]))),T2JAG($list(T2Pvar(y0[6023])))))
              ## T1IMPallx(gseq_map_llist(425), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14658(line=1008,offs=1)--14777(line=1016,offs=32)))
              ## T1IMPallx(gseq_map_llist(425)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6018],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6019],T2Pcst(term)),@(y0[6020],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map_llist(425);$list(@(xs[1222],T2Pvar(xs[6018])),@(x0[1223],T2Pvar(x0[6019])),@(y0[1224],T2Pvar(y0[6020])))))))
              def pyxtnm1613(arg1): ## timp: gseq_map_llist(425)
                pyxtnm1537 = arg1
                ## I1CMP:start
                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14723(line=1014,offs=1)--14739(line=1014,offs=17))
                ## I0Etapq(I0Ecst(strm_vt_listize0(2194)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/strm001_vt.sats)@(8819(line=452,offs=1)--8835(line=452,offs=17))));$list(T2JAG($list(T2Pvar(y0[6020])))))
                ## T1IMPallx(strm_vt_listize0(2194), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7222(line=450,offs=1)--7317(line=455,offs=28)))
                ## T1IMPallx(strm_vt_listize0(2194)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8475],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(strm_vt_listize0(2194);$list(@(x0[5392],T2Pvar(x0[8475])))))))
                def pyxtnm1574(arg1): ## timp: strm_vt_listize0(2194)
                  pyxtnm1538 = arg1
                  ## I1CMP:start
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7269(line=454,offs=1)--7285(line=454,offs=17))
                  ## I0Etapq(I0Ecst(list_vt_reverse0(2015)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/list000_vt.sats)@(4454(line=254,offs=1)--4470(line=254,offs=17))));$list(T2JAG($list(T2Pvar(x0[8475])))))
                  ## T1IMPallx(list_vt_reverse0(2015), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6829(line=462,offs=1)--6916(line=465,offs=46)))
                  ## T1IMPallx(list_vt_reverse0(2015)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(a[8309],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_vt_reverse0(2015);$list(@(x0[5093],T2Pvar(a[8309])))))))
                  def pyxtnm1557(arg1): ## timp: list_vt_reverse0(2015)
                    pyxtnm1539 = arg1
                    ## I1CMP:start
                    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6871(line=465,offs=1)--6888(line=465,offs=18))
                    ## I0Etapq(I0Ecst(list_vt_rappend00(2018)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/list000_vt.sats)@(4835(line=280,offs=1)--4852(line=280,offs=18))));$list(T2JAG($list(T2Pvar(a[8309])))))
                    ## T1IMPallx(list_vt_rappend00(2018), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6351(line=426,offs=1)--6760(line=458,offs=2)))
                    ## T1IMPallx(list_vt_rappend00(2018)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(a[8306],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_vt_rappend00(2018);$list(@(x0[5100],T2Pvar(a[8306])))))))
                    def pyxtnm1554(arg1, arg2): ## timp: list_vt_rappend00(2018)
                      pyxtnm1540 = arg1
                      pyxtnm1541 = arg2
                      ## I1CMP:start
                      ## let
                      pyxtnm1553 = None
                      ## I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6430(line=434,offs=1)--6721(line=456,offs=2)))
                      ## I1FUNDCL
                      def loop_6433(arg1, arg2): ## fun
                        pyxtnm1542 = arg1
                        pyxtnm1543 = arg2
                        ## I1CMP:start
                        pyxtnm1551 = None
                        while True: ## do {
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(1544);I0Pfree(I0Pdapp(I0Pcon(list_vt_nil(10));$list()));$list()))
                          if (XATS000_ctgeq(pyxtnm1542, XATSCTAG("list_vt_nil",0))): ## { // gpt
                            pyxtnm1544 = pyxtnm1542
                            pyxtnm1551 = pyxtnm1543
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(1545);I0Pflat(I0Pdapp(I0Pcon(list_vt_cons(11));$list(I0Pany(),I0Pany())));$list()))
                          if (XATS000_ctgeq(pyxtnm1542, XATSCTAG("list_vt_cons",1))): ## { // gpt
                            pyxtnm1545 = pyxtnm1542
                            ## let
                            pyxtnm1550 = None
                            ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6604(line=450,offs=3)--6619(line=450,offs=18)))
                            ## I1VALDCL
                            pyxtnm1547 = None
                            pyxtnm1546 = XATSPCON(pyxtnm1542,1)
                            pyxtnm1547 = pyxtnm1546
                            XATS000_patck(True)
                            ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/list000_vt.dats)@(6622(line=451,offs=3)--6644(line=451,offs=25)))
                            ## I1VALDCL
                            pyxtnm1548 = None
                            XATS000_assgn(XATSLPCN(1, pyxtnm1542), pyxtnm1543)
                            pyxtnm1548 = []
                            XATS000_patck(True)
                            XATS000_fold(pyxtnm1542)
                            pyxtnm1549 = XATSDAPP(loop_6433(pyxtnm1547, pyxtnm1542))
                            pyxtnm1550 = pyxtnm1549
                            ## end-of(let)
                            pyxtnm1551 = pyxtnm1550
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          XATS000_cfail()
                        ## } while True // end-of(do-cls)
                        ## I1CMP:return:pyxtnm1551
                        return pyxtnm1551
                      pyxtnm1552 = XATSDAPP(loop_6433(pyxtnm1540, pyxtnm1541))
                      pyxtnm1553 = pyxtnm1552
                      ## end-of(let)
                      ## I1CMP:return:pyxtnm1553
                      return pyxtnm1553
                    ## endtimp(list_vt_rappend00(2018))
                    pyxtnm1555 = XATSCAPP("list_vt_nil", [0])
                    pyxtnm1556 = XATSDAPP(pyxtnm1554(pyxtnm1539, pyxtnm1555))
                    ## I1CMP:return:pyxtnm1556
                    return pyxtnm1556
                  ## endtimp(list_vt_reverse0(2015))
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7291(line=455,offs=2)--7308(line=455,offs=19))
                  ## I0Etapq(I0Ecst(strm_vt_rlistize0(2196)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/strm001_vt.sats)@(8956(line=462,offs=1)--8973(line=462,offs=18))));$list(T2JAG($list(T2Pvar(x0[8475])))))
                  ## T1IMPallx(strm_vt_rlistize0(2196), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7321(line=457,offs=1)--7614(line=480,offs=2)))
                  ## T1IMPallx(strm_vt_rlistize0(2196)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8476],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(strm_vt_rlistize0(2196);$list(@(x0[5395],T2Pvar(x0[8476])))))))
                  def pyxtnm1571(arg1): ## timp: strm_vt_rlistize0(2196)
                    pyxtnm1558 = arg1
                    ## I1CMP:start
                    ## let
                    pyxtnm1570 = None
                    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7398(line=465,offs=1)--7420(line=465,offs=23)))
                    ## I1VALDCL
                    pyxtnm1560 = None
                    pyxtnm1559 = XATSCAPP("list_vt_nil", [0])
                    pyxtnm1560 = pyxtnm1559
                    XATS000_patck(True)
                    ## I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(7424(line=467,offs=1)--7612(line=479,offs=35)))
                    ## I1FUNDCL
                    def loop_7427(arg1, arg2): ## fun
                      pyxtnm1561 = arg1
                      pyxtnm1562 = arg2
                      ## I1CMP:start
                      pyxtnm1563 = XATS000_dl1az(pyxtnm1561)
                      pyxtnm1568 = None
                      while True: ## do {
                        ## { // cls
                        ## I1GPTpat(I1BNDcons(I1TNM(1564);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_nil(15));$list()));$list()))
                        if (XATS000_ctgeq(pyxtnm1563, XATSCTAG("strmcon_vt_nil",0))): ## { // gpt
                          pyxtnm1564 = pyxtnm1563
                          pyxtnm1568 = pyxtnm1562
                          break ## cls
                        ## } // gpt
                        ## } // cls
                        ## { // cls
                        ## I1GPTpat(I1BNDcons(I1TNM(1565);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_cons(16));$list(I0Pvar(x1(4505)),I0Pvar(xs(4506)))));$list(@(x1(4505),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1565));0)),@(xs(4506),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1565));1)))))
                        if (XATS000_ctgeq(pyxtnm1563, XATSCTAG("strmcon_vt_cons",1))): ## { // gpt
                          pyxtnm1565 = pyxtnm1563
                          pyxtnm1566 = XATSCAPP("list_vt_cons", [1, XATSP1CN("strmcon_vt_cons", pyxtnm1565[0+1]), pyxtnm1562])
                          pyxtnm1567 = XATSDAPP(loop_7427(XATSP1CN("strmcon_vt_cons", pyxtnm1565[1+1]), pyxtnm1566))
                          pyxtnm1568 = pyxtnm1567
                          break ## cls
                        ## } // gpt
                        ## } // cls
                        XATS000_cfail()
                      ## } while True // end-of(do-cls)
                      ## I1CMP:return:pyxtnm1568
                      return pyxtnm1568
                    pyxtnm1569 = XATSDAPP(loop_7427(pyxtnm1558, pyxtnm1560))
                    pyxtnm1570 = pyxtnm1569
                    ## end-of(let)
                    ## I1CMP:return:pyxtnm1570
                    return pyxtnm1570
                  ## endtimp(strm_vt_rlistize0(2196))
                  pyxtnm1572 = XATSDAPP(pyxtnm1571(pyxtnm1538))
                  pyxtnm1573 = XATSDAPP(pyxtnm1557(pyxtnm1572))
                  ## I1CMP:return:pyxtnm1573
                  return pyxtnm1573
                ## endtimp(strm_vt_listize0(2194))
                ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14746(line=1016,offs=1)--14760(line=1016,offs=15))
                ## I0Etapq(I0Ecst(gseq_map_lstrm(426)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(12714(line=737,offs=1)--12728(line=737,offs=15))));$list(T2JAG($list(T2Pvar(xs[6018]))),T2JAG($list(T2Pvar(x0[6019]))),T2JAG($list(T2Pvar(y0[6020])))))
                ## T1IMPallx(gseq_map_lstrm(426), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15009(line=1034,offs=1)--15178(line=1046,offs=2)))
                ## T1IMPallx(gseq_map_lstrm(426)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6024],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6025],T2Pcst(term)),@(y0[6026],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_map_lstrm(426);$list(@(xs[1225],T2Pvar(xs[6024])),@(x0[1226],T2Pvar(x0[6025])),@(y0[1227],T2Pvar(y0[6026])))))))
                def pyxtnm1610(arg1): ## timp: gseq_map_lstrm(426)
                  pyxtnm1575 = arg1
                  ## I1CMP:start
                  ## let
                  pyxtnm1609 = None
                  ## I1Dimplmnt0(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15131(line=1044,offs=1)--15176(line=1045,offs=37)))
                  ## I1Dimplmnt0(DIMPLone2(map$fopr0(1471);$list(@(x0[3718],T2Pvar(x0[6025])),@(y0[3719],T2Pvar(y0[6026]))))):timp
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15074(line=1040,offs=1)--15086(line=1040,offs=13))
                  ## I0Etapq(I0Ecst(strm_vt_map0(2174)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/strm001_vt.sats)@(5100(line=256,offs=1)--5112(line=256,offs=13))));$list(T2JAG($list(T2Pvar(x0[6025]))),T2JAG($list(T2Pvar(y0[6026])))))
                  ## T1IMPallx(strm_vt_map0(2174), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(4033(line=214,offs=1)--4316(line=237,offs=2)))
                  ## T1IMPallx(strm_vt_map0(2174)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[8458],T2Pcst(term)),@(y0[8459],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(strm_vt_map0(2174);$list(@(x0[5351],T2Pvar(x0[8458])),@(y0[5352],T2Pvar(y0[8459])))))))
                  def pyxtnm1593(arg1): ## timp: strm_vt_map0(2174)
                    pyxtnm1576 = arg1
                    ## I1CMP:start
                    ## let
                    pyxtnm1592 = None
                    ## I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(4111(line=222,offs=1)--4314(line=236,offs=2)))
                    ## I1FUNDCL
                    def auxmain_4114(arg1): ## fun
                      pyxtnm1577 = arg1
                      ## I1CMP:start
                      def pyxtnm1590(tlaz): ## { // l1azy
                        ## I1CMP:start
                        pyxtnm1578 = XATS000_dl1az(pyxtnm1577)
                        pyxtnm1589 = None
                        while True: ## do {
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(1579);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_nil(15));$list()));$list()))
                          if (XATS000_ctgeq(pyxtnm1578, XATSCTAG("strmcon_vt_nil",0))): ## { // gpt
                            pyxtnm1579 = pyxtnm1578
                            pyxtnm1580 = XATSCAPP("strmcon_vt_nil", [0])
                            pyxtnm1589 = pyxtnm1580
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(1581);I0Pfree(I0Pdapp(I0Pcon(strmcon_vt_cons(16));$list(I0Pvar(x1(4467)),I0Pvar(xs(4468)))));$list(@(x1(4467),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1581));0)),@(xs(4468),I1Vp1cn(I0Pcon(strmcon_vt_cons(16));I1Vtnm(I1TNM(1581));1)))))
                          if (XATS000_ctgeq(pyxtnm1578, XATSCTAG("strmcon_vt_cons",1))): ## { // gpt
                            pyxtnm1581 = pyxtnm1578
                            ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/VT/strm001_vt.dats)@(4277(line=235,offs=2)--4286(line=235,offs=11))
                            ## I0Etapq(I0Ecst(map$fopr0(1471)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/VT/gbas001_vt.sats)@(5345(line=363,offs=1)--5354(line=363,offs=10))));$list(T2JAG($list(T2Pvar(x0[8458]))),T2JAG($list(T2Pvar(y0[8459])))))
                            ## T1IMPallx(map$fopr0(1471), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15131(line=1044,offs=1)--15176(line=1045,offs=37)))
                            ## T1IMPallx(map$fopr0(1471)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6024],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6025],T2Pcst(term)),@(y0[6026],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(map$fopr0(1471);$list(@(x0[3718],T2Pcst(term)),@(y0[3719],T2Pcst(term)))))))
                            pyxtnm1585 = None
                            ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15160(line=1045,offs=21)--15168(line=1045,offs=29))
                            ## I0Etapq(I0Ecst(map$fopr(75)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas001.sats)@(3732(line=232,offs=1)--3740(line=232,offs=9))));$list(T2JAG($list(T2Pvar(x0[6025]))),T2JAG($list(T2Pvar(y0[6026])))))
                            ## T1IMPallx(map$fopr(75), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(14897(line=1028,offs=1)--14941(line=1029,offs=36)))
                            ## T1IMPallx(map$fopr(75)<$list(T2JAG($list(T2Pcst(term))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(xs[6021],T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0()))),@(x0[6022],T2Pcst(term)),@(y0[6023],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(map$fopr(75);$list(@(x0[430],T2Pcst(term)),@(y0[431],T2Pcst(term)))))))
                            def pyxtnm1584(arg1): ## timp: map$fopr(75)
                              pyxtnm1582 = arg1
                              ## I1CMP:start
                              pyxtnm1583 = XATSDAPP(pyxtnm1534(pyxtnm1582))
                              ## I1CMP:return:pyxtnm1583
                              return pyxtnm1583
                            ## endtimp(map$fopr(75))
                            pyxtnm1585 = pyxtnm1584
                            pyxtnm1586 = XATSDAPP(pyxtnm1585(XATSP1CN("strmcon_vt_cons", pyxtnm1581[0+1])))
                            pyxtnm1587 = XATSDAPP(auxmain_4114(XATSP1CN("strmcon_vt_cons", pyxtnm1581[1+1])))
                            pyxtnm1588 = XATSCAPP("strmcon_vt_cons", [1, pyxtnm1586, pyxtnm1587])
                            pyxtnm1589 = pyxtnm1588
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          XATS000_cfail()
                        ## } while True // end-of(do-cls)
                        ## I1CMP:return:pyxtnm1589
                        return pyxtnm1589
                      ## } // end(l1azy)
                      ## I1CMP:return:pyxtnm1590
                      return pyxtnm1590
                    pyxtnm1591 = XATSDAPP(auxmain_4114(pyxtnm1576))
                    pyxtnm1592 = pyxtnm1591
                    ## end-of(let)
                    ## I1CMP:return:pyxtnm1592
                    return pyxtnm1592
                  ## endtimp(strm_vt_map0(2174))
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gseq001.dats)@(15097(line=1042,offs=1)--15109(line=1042,offs=13))
                  ## I0Etapq(I0Ecst(gseq_strmize(372)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gseq001.sats)@(2503(line=122,offs=1)--2515(line=122,offs=13))));$list(T2JAG($list(T2Pvar(xs[6024]))),T2JAG($list(T2Pvar(x0[6025])))))
                  ## T1IMPallx(gseq_strmize(372), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6711(line=443,offs=1)--6775(line=445,offs=46)))
                  ## T1IMPallx(gseq_strmize(372)<$list(T2JAG($list(T2Papps(T2Pcst(list_t0_i0_tx);$list(T2Pcst(term),T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7315],T2Pcst(term)),@(x0[7315],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gseq_strmize(372);$list(@(xs[1047],T2Papps(T2Pcst(list);$list(T2Pvar(x0[7315])))),@(x0[1048],T2Pvar(x0[7315])))))))
                  pyxtnm1606 = None
                  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6759(line=445,offs=30)--6771(line=445,offs=42))
                  ## I0Etapq(I0Ecst(list_strmize(1202)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list001.sats)@(1677(line=61,offs=1)--1689(line=61,offs=13))));$list(T2JAG($list(T2Pvar(x0[7315])))))
                  ## T1IMPallx(list_strmize(1202), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6452(line=418,offs=1)--6671(line=441,offs=2)))
                  ## T1IMPallx(list_strmize(1202)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7314],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_strmize(1202);$list(@(a[3280],T2Pvar(x0[7314])))))))
                  def pyxtnm1605(arg1): ## timp: list_strmize(1202)
                    pyxtnm1594 = arg1
                    ## I1CMP:start
                    ## let
                    pyxtnm1604 = None
                    ## I1Dfundclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list001.dats)@(6526(line=427,offs=1)--6666(line=439,offs=2)))
                    ## I1FUNDCL
                    def auxmain_6529(arg1): ## fun
                      pyxtnm1595 = arg1
                      ## I1CMP:start
                      def pyxtnm1602(tlaz): ## { // l1azy
                        ## I1CMP:start
                        pyxtnm1601 = None
                        while True: ## do {
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(1596);I0Pdapp(I0Pcon(list_nil(8));$list());$list()))
                          if (XATS000_ctgeq(pyxtnm1595, XATSCTAG("list_nil",0))): ## { // gpt
                            pyxtnm1596 = pyxtnm1595
                            pyxtnm1597 = XATSCAPP("strmcon_vt_nil", [0])
                            pyxtnm1601 = pyxtnm1597
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          ## { // cls
                          ## I1GPTpat(I1BNDcons(I1TNM(1598);I0Pdapp(I0Pcon(list_cons(9));$list(I0Pvar(x0(2601)),I0Pvar(xs(2602))));$list(@(x0(2601),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(1598));0)),@(xs(2602),I1Vp1cn(I0Pcon(list_cons(9));I1Vtnm(I1TNM(1598));1)))))
                          if (XATS000_ctgeq(pyxtnm1595, XATSCTAG("list_cons",1))): ## { // gpt
                            pyxtnm1598 = pyxtnm1595
                            pyxtnm1599 = XATSDAPP(auxmain_6529(XATSP1CN("list_cons", pyxtnm1598[1+1])))
                            pyxtnm1600 = XATSCAPP("strmcon_vt_cons", [1, XATSP1CN("list_cons", pyxtnm1598[0+1]), pyxtnm1599])
                            pyxtnm1601 = pyxtnm1600
                            break ## cls
                          ## } // gpt
                          ## } // cls
                          XATS000_cfail()
                        ## } while True // end-of(do-cls)
                        ## I1CMP:return:pyxtnm1601
                        return pyxtnm1601
                      ## } // end(l1azy)
                      ## I1CMP:return:pyxtnm1602
                      return pyxtnm1602
                    pyxtnm1603 = XATSDAPP(auxmain_6529(pyxtnm1594))
                    pyxtnm1604 = pyxtnm1603
                    ## end-of(let)
                    ## I1CMP:return:pyxtnm1604
                    return pyxtnm1604
                  ## endtimp(list_strmize(1202))
                  pyxtnm1606 = pyxtnm1605
                  pyxtnm1607 = XATSDAPP(pyxtnm1606(pyxtnm1575))
                  pyxtnm1608 = XATSDAPP(pyxtnm1593(pyxtnm1607))
                  pyxtnm1609 = pyxtnm1608
                  ## end-of(let)
                  ## I1CMP:return:pyxtnm1609
                  return pyxtnm1609
                ## endtimp(gseq_map_lstrm(426))
                pyxtnm1611 = XATSDAPP(pyxtnm1610(pyxtnm1537))
                pyxtnm1612 = XATSDAPP(pyxtnm1574(pyxtnm1611))
                ## I1CMP:return:pyxtnm1612
                return pyxtnm1612
              ## endtimp(gseq_map_llist(425))
              pyxtnm1614 = XATSDAPP(pyxtnm1613(pyxtnm1533))
              pyxtnm1615 = pyxtnm1614
              ## end-of(let)
              ## I1CMP:return:pyxtnm1615
              return pyxtnm1615
            ## endtimp(gseq_map$f1un_llist(429))
            pyxtnm1617 = XATSDAPP(pyxtnm1616(pyxtnm1531, pyxtnm1532))
            pyxtnm1618 = XATSCAST("list_vt2t_17651", [pyxtnm1617])
            ## I1CMP:return:pyxtnm1618
            return pyxtnm1618
          ## endtimp(gseq_map$f1un_list(428))
          pyxtnm1620 = pyxtnm1619
          pyxtnm1621 = XATSDAPP(pyxtnm1620(pyxtnm1530, pyxtnm1529))
          ## I1CMP:return:pyxtnm1621
          return pyxtnm1621
        ## } // end(lam0)
        ## I1CMP:return:pyxtnm1622
        return pyxtnm1622
      ## endtimp(f1un_map$list(316))
      pyxtnm1624 = XATSDAPP(pyxtnm1623(pyxtnm1471))
      pyxtnm1625 = XATSDAPP(pyxtnm1624(XATSP1CN("TMopr", pyxtnm1528[1+1])))
      pyxtnm1626 = XATSCAPP("TMopr", [5, XATSP1CN("TMopr", pyxtnm1528[0+1]), pyxtnm1625])
      pyxtnm1711 = pyxtnm1626
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1627);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5218)),I0Pvar(tm2(5219)),I0Pvar(tm3(5220))));$list(@(tm1(5218),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1627));0)),@(tm2(5219),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1627));1)),@(tm3(5220),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1627));2)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMif0",6))): ## { // gpt
      pyxtnm1627 = pyxtnm1465
      pyxtnm1628 = XATSDAPP(pyxtnm1471(XATSP1CN("TMif0", pyxtnm1627[0+1])))
      pyxtnm1629 = XATSDAPP(pyxtnm1471(XATSP1CN("TMif0", pyxtnm1627[1+1])))
      pyxtnm1630 = XATSDAPP(pyxtnm1471(XATSP1CN("TMif0", pyxtnm1627[2+1])))
      pyxtnm1631 = XATSCAPP("TMif0", [6, pyxtnm1628, pyxtnm1629, pyxtnm1630])
      pyxtnm1711 = pyxtnm1631
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1632);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5221)),I0Pvar(x01(5222)),I0Pvar(tmx(5223))));$list(@(f00(5221),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1632));0)),@(x01(5222),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1632));1)),@(tmx(5223),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1632));2)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMfix",7))): ## { // gpt
      pyxtnm1632 = pyxtnm1465
      ## LCSRCsome1(lambda1.dats)@(4587(line=315,offs=6)--4588(line=315,offs=7))
      ## I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
      ## T1IMPallx(strn_eq(1024), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
      ## T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
      pyxtnm1653 = None
      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
      ## I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
      ## T1IMPallx(g_eq(226), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
      ## T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5765],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[718],T2Pvar(x0[5765])))))))
      def pyxtnm1652(arg1, arg2): ## timp: g_eq(226)
        pyxtnm1633 = arg1
        pyxtnm1634 = arg2
        ## I1CMP:start
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
        ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
        ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
        ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
        def pyxtnm1641(arg1, arg2): ## timp: sint_eq$sint(920)
          pyxtnm1635 = arg1
          pyxtnm1636 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1640 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(1637);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(1637))))),I1BNDcons(I1TNM(1638);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(1638))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
          pyxtnm1639 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm1635, pyxtnm1636))
          pyxtnm1640 = pyxtnm1639
          ## end-of(let)
          ## I1CMP:return:pyxtnm1640
          return pyxtnm1640
        ## endtimp(sint_eq$sint(920))
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
        ## I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5765])))))
        ## T1IMPallx(g_cmp(230), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
        ## T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[722],T2Pcst(strn)))))))
        pyxtnm1649 = None
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
        ## I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
        ## T1IMPallx(strn_cmp(1028), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1623(line=57,offs=1)--1772(line=69,offs=2)))
        ## T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
        def pyxtnm1648(arg1, arg2): ## timp: strn_cmp(1028)
          pyxtnm1642 = arg1
          pyxtnm1643 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1647 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1703(line=65,offs=1)--1770(line=68,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_cmp(2612));$list(I1FUNDCL(XATS2PY_strn_cmp(5017);$list(FJARGdarg($list(I1BNDcons(I1TNM(1644);I0Pvar(x1(5018));$list(@(x1(5018),I1Vtnm(I1TNM(1644))))),I1BNDcons(I1TNM(1645);I0Pvar(x2(5019));$list(@(x2(5019),I1Vtnm(I1TNM(1645))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_cmp);G1Nlist($list())))))))
          pyxtnm1646 = XATSDAPP(XATS2PY_strn_cmp(pyxtnm1642, pyxtnm1643))
          pyxtnm1647 = pyxtnm1646
          ## end-of(let)
          ## I1CMP:return:pyxtnm1647
          return pyxtnm1647
        ## endtimp(strn_cmp(1028))
        pyxtnm1649 = pyxtnm1648
        pyxtnm1650 = XATSDAPP(pyxtnm1649(pyxtnm1633, pyxtnm1634))
        pyxtnm1651 = XATSDAPP(pyxtnm1641(pyxtnm1650, XATSINT1(0)))
        ## I1CMP:return:pyxtnm1651
        return pyxtnm1651
      ## endtimp(g_eq(226))
      pyxtnm1653 = pyxtnm1652
      pyxtnm1654 = XATSDAPP(pyxtnm1653(pyxtnm1466, XATSP1CN("TMfix", pyxtnm1632[0+1])))
      pyxtnm1680 = None
      if (pyxtnm1654):
        pyxtnm1680 = pyxtnm1465
      else:
        ## LCSRCsome1(lambda1.dats)@(4616(line=318,offs=6)--4617(line=318,offs=7))
        ## I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
        ## T1IMPallx(strn_eq(1024), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
        ## T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
        pyxtnm1675 = None
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
        ## I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(g_eq(226), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
        ## T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5765],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[718],T2Pvar(x0[5765])))))))
        def pyxtnm1674(arg1, arg2): ## timp: g_eq(226)
          pyxtnm1655 = arg1
          pyxtnm1656 = arg2
          ## I1CMP:start
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
          ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
          ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
          def pyxtnm1663(arg1, arg2): ## timp: sint_eq$sint(920)
            pyxtnm1657 = arg1
            pyxtnm1658 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1662 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(1659);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(1659))))),I1BNDcons(I1TNM(1660);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(1660))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
            pyxtnm1661 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm1657, pyxtnm1658))
            pyxtnm1662 = pyxtnm1661
            ## end-of(let)
            ## I1CMP:return:pyxtnm1662
            return pyxtnm1662
          ## endtimp(sint_eq$sint(920))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
          ## I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5765])))))
          ## T1IMPallx(g_cmp(230), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
          ## T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[722],T2Pcst(strn)))))))
          pyxtnm1671 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
          ## I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
          ## T1IMPallx(strn_cmp(1028), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1623(line=57,offs=1)--1772(line=69,offs=2)))
          ## T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
          def pyxtnm1670(arg1, arg2): ## timp: strn_cmp(1028)
            pyxtnm1664 = arg1
            pyxtnm1665 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1669 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1703(line=65,offs=1)--1770(line=68,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_cmp(2612));$list(I1FUNDCL(XATS2PY_strn_cmp(5017);$list(FJARGdarg($list(I1BNDcons(I1TNM(1666);I0Pvar(x1(5018));$list(@(x1(5018),I1Vtnm(I1TNM(1666))))),I1BNDcons(I1TNM(1667);I0Pvar(x2(5019));$list(@(x2(5019),I1Vtnm(I1TNM(1667))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_cmp);G1Nlist($list())))))))
            pyxtnm1668 = XATSDAPP(XATS2PY_strn_cmp(pyxtnm1664, pyxtnm1665))
            pyxtnm1669 = pyxtnm1668
            ## end-of(let)
            ## I1CMP:return:pyxtnm1669
            return pyxtnm1669
          ## endtimp(strn_cmp(1028))
          pyxtnm1671 = pyxtnm1670
          pyxtnm1672 = XATSDAPP(pyxtnm1671(pyxtnm1655, pyxtnm1656))
          pyxtnm1673 = XATSDAPP(pyxtnm1663(pyxtnm1672, XATSINT1(0)))
          ## I1CMP:return:pyxtnm1673
          return pyxtnm1673
        ## endtimp(g_eq(226))
        pyxtnm1675 = pyxtnm1674
        pyxtnm1676 = XATSDAPP(pyxtnm1675(pyxtnm1466, XATSP1CN("TMfix", pyxtnm1632[1+1])))
        pyxtnm1679 = None
        if (pyxtnm1676):
          pyxtnm1679 = pyxtnm1465
        else:
          pyxtnm1677 = XATSDAPP(pyxtnm1471(XATSP1CN("TMfix", pyxtnm1632[2+1])))
          pyxtnm1678 = XATSCAPP("TMfix", [7, XATSP1CN("TMfix", pyxtnm1632[0+1]), XATSP1CN("TMfix", pyxtnm1632[1+1]), pyxtnm1677])
          pyxtnm1679 = pyxtnm1678
        ## end-of(if)
        pyxtnm1680 = pyxtnm1679
      ## end-of(if)
      pyxtnm1711 = pyxtnm1680
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1681);I0Pdapp(I0Pcon(TMlet(40));$list(I0Pvar(x01(5224)),I0Pvar(tm1(5225)),I0Pvar(tm2(5226))));$list(@(x01(5224),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(1681));0)),@(tm1(5225),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(1681));1)),@(tm2(5226),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(1681));2)))))
    if (XATS000_ctgeq(pyxtnm1465, XATSCTAG("TMlet",8))): ## { // gpt
      pyxtnm1681 = pyxtnm1465
      ## let
      pyxtnm1710 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(4726(line=325,offs=1)--4746(line=325,offs=21)))
      ## I1VALDCL
      pyxtnm1683 = None
      pyxtnm1682 = XATSDAPP(pyxtnm1471(XATSP1CN("TMlet", pyxtnm1681[1+1])))
      pyxtnm1683 = pyxtnm1682
      XATS000_patck(True)
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(4747(line=326,offs=1)--4796(line=327,offs=40)))
      ## I1VALDCL
      pyxtnm1708 = None
      ## LCSRCsome1(lambda1.dats)@(4765(line=327,offs=9)--4766(line=327,offs=10))
      ## I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
      ## T1IMPallx(strn_eq(1024), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
      ## T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
      pyxtnm1704 = None
      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
      ## I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
      ## T1IMPallx(g_eq(226), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
      ## T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5765],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[718],T2Pvar(x0[5765])))))))
      def pyxtnm1703(arg1, arg2): ## timp: g_eq(226)
        pyxtnm1684 = arg1
        pyxtnm1685 = arg2
        ## I1CMP:start
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
        ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
        ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
        ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
        def pyxtnm1692(arg1, arg2): ## timp: sint_eq$sint(920)
          pyxtnm1686 = arg1
          pyxtnm1687 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1691 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(1688);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(1688))))),I1BNDcons(I1TNM(1689);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(1689))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
          pyxtnm1690 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm1686, pyxtnm1687))
          pyxtnm1691 = pyxtnm1690
          ## end-of(let)
          ## I1CMP:return:pyxtnm1691
          return pyxtnm1691
        ## endtimp(sint_eq$sint(920))
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
        ## I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5765])))))
        ## T1IMPallx(g_cmp(230), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
        ## T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[722],T2Pcst(strn)))))))
        pyxtnm1700 = None
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
        ## I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
        ## T1IMPallx(strn_cmp(1028), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1623(line=57,offs=1)--1772(line=69,offs=2)))
        ## T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
        def pyxtnm1699(arg1, arg2): ## timp: strn_cmp(1028)
          pyxtnm1693 = arg1
          pyxtnm1694 = arg2
          ## I1CMP:start
          ## let
          pyxtnm1698 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1703(line=65,offs=1)--1770(line=68,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_cmp(2612));$list(I1FUNDCL(XATS2PY_strn_cmp(5017);$list(FJARGdarg($list(I1BNDcons(I1TNM(1695);I0Pvar(x1(5018));$list(@(x1(5018),I1Vtnm(I1TNM(1695))))),I1BNDcons(I1TNM(1696);I0Pvar(x2(5019));$list(@(x2(5019),I1Vtnm(I1TNM(1696))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_cmp);G1Nlist($list())))))))
          pyxtnm1697 = XATSDAPP(XATS2PY_strn_cmp(pyxtnm1693, pyxtnm1694))
          pyxtnm1698 = pyxtnm1697
          ## end-of(let)
          ## I1CMP:return:pyxtnm1698
          return pyxtnm1698
        ## endtimp(strn_cmp(1028))
        pyxtnm1700 = pyxtnm1699
        pyxtnm1701 = XATSDAPP(pyxtnm1700(pyxtnm1684, pyxtnm1685))
        pyxtnm1702 = XATSDAPP(pyxtnm1692(pyxtnm1701, XATSINT1(0)))
        ## I1CMP:return:pyxtnm1702
        return pyxtnm1702
      ## endtimp(g_eq(226))
      pyxtnm1704 = pyxtnm1703
      pyxtnm1705 = XATSDAPP(pyxtnm1704(pyxtnm1466, XATSP1CN("TMlet", pyxtnm1681[0+1])))
      pyxtnm1707 = None
      if (pyxtnm1705):
        pyxtnm1707 = XATSP1CN("TMlet", pyxtnm1681[2+1])
      else:
        pyxtnm1706 = XATSDAPP(pyxtnm1471(XATSP1CN("TMlet", pyxtnm1681[2+1])))
        pyxtnm1707 = pyxtnm1706
      ## end-of(if)
      pyxtnm1708 = pyxtnm1707
      XATS000_patck(True)
      pyxtnm1709 = XATSCAPP("TMlet", [8, XATSP1CN("TMlet", pyxtnm1681[0+1]), pyxtnm1683, pyxtnm1708])
      pyxtnm1710 = pyxtnm1709
      ## end-of(let)
      pyxtnm1711 = pyxtnm1710
      break ## cls
    ## } // gpt
    ## } // cls
    XATS000_cfail()
  ## } while True // end-of(do-cls)
  pyxtnm1712 = pyxtnm1711
  ## end-of(let)
  ## I1CMP:return:pyxtnm1712
  return pyxtnm1712
## endfun(impl)
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(4891(line=334,offs=1)--7420(line=491,offs=2)))
## I1FUNDCL
def term_interp_4894(arg1): ## fun
  pyxtnm1713 = arg1
  ## I1CMP:start
  pyxtnm1929 = None
  while True: ## do {
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1714);I0Pdap1(I0Pcon(TMint(32)));$list()))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMint",0))): ## { // gpt
      pyxtnm1714 = pyxtnm1713
      pyxtnm1929 = pyxtnm1713
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1715);I0Pdap1(I0Pcon(TMbtf(33)));$list()))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMbtf",1))): ## { // gpt
      pyxtnm1715 = pyxtnm1713
      pyxtnm1929 = pyxtnm1713
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1716);I0Pdap1(I0Pcon(TMvar(34)));$list()))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMvar",2))): ## { // gpt
      pyxtnm1716 = pyxtnm1713
      pyxtnm1929 = pyxtnm1713
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1717);I0Pdap1(I0Pcon(TMlam(35)));$list()))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMlam",3))): ## { // gpt
      pyxtnm1717 = pyxtnm1713
      pyxtnm1929 = pyxtnm1713
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1718);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5231)),I0Pvar(tm2(5232))));$list(@(tm1(5231),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1718));0)),@(tm2(5232),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(1718));1)))))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMapp",4))): ## { // gpt
      pyxtnm1718 = pyxtnm1713
      ## let
      pyxtnm1728 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5060(line=351,offs=1)--5086(line=352,offs=23)))
      ## I1VALDCL
      pyxtnm1720 = None
      pyxtnm1719 = XATSDAPP(term_interp_4894(XATSP1CN("TMapp", pyxtnm1718[0+1])))
      pyxtnm1720 = pyxtnm1719
      XATS000_patck(True)
      pyxtnm1727 = None
      while True: ## do {
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1721);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5234)),I0Pvar(tmx(5235))));$list(@(x01(5234),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1721));0)),@(tmx(5235),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(1721));1)))))
        if (XATS000_ctgeq(pyxtnm1720, XATSCTAG("TMlam",3))): ## { // gpt
          pyxtnm1721 = pyxtnm1720
          pyxtnm1722 = XATSDAPP(term_subst_4023(XATSP1CN("TMlam", pyxtnm1721[1+1]), XATSP1CN("TMlam", pyxtnm1721[0+1]), XATSP1CN("TMapp", pyxtnm1718[1+1])))
          pyxtnm1723 = XATSDAPP(term_interp_4894(pyxtnm1722))
          pyxtnm1727 = pyxtnm1723
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1724);I0Pany();$list()))
        if (True): ## { // gpt
          pyxtnm1724 = pyxtnm1720
          pyxtnm1725 = XATSDAPP(term_interp_4894(XATSP1CN("TMapp", pyxtnm1718[1+1])))
          pyxtnm1726 = XATSCAPP("TMapp", [4, pyxtnm1720, pyxtnm1725])
          pyxtnm1727 = pyxtnm1726
          break ## cls
        ## } // gpt
        ## } // cls
        XATS000_cfail()
      ## } while True // end-of(do-cls)
      pyxtnm1728 = pyxtnm1727
      ## end-of(let)
      pyxtnm1929 = pyxtnm1728
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1729);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(pnm(5236)),I0Pvar(tms(5237))));$list(@(pnm(5236),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1729));0)),@(tms(5237),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(1729));1)))))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMopr",5))): ## { // gpt
      pyxtnm1729 = pyxtnm1713
      pyxtnm1917 = None
      while True: ## do {
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1730);I0Pstr(T_STRN1_clsd("+";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("+"))): ## { // gpt
          pyxtnm1730 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1746 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5373(line=377,offs=1)--5402(line=377,offs=30)))
          ## I1VALDCL
          pyxtnm1731 = None
          pyxtnm1731 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5403(line=378,offs=1)--5432(line=378,offs=30)))
          ## I1VALDCL
          pyxtnm1732 = None
          pyxtnm1732 = XATSP1CN("list_cons", pyxtnm1731[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1731[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5433(line=379,offs=1)--5466(line=379,offs=34)))
          ## I1VALDCL
          pyxtnm1734 = None
          pyxtnm1733 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1731[0+1])))
          pyxtnm1734 = pyxtnm1733
          XATS000_patck(XATS000_ctgeq(pyxtnm1733, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5467(line=380,offs=1)--5500(line=380,offs=34)))
          ## I1VALDCL
          pyxtnm1736 = None
          pyxtnm1735 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1732[0+1])))
          pyxtnm1736 = pyxtnm1735
          XATS000_patck(XATS000_ctgeq(pyxtnm1735, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(5358(line=375,offs=10)--5359(line=375,offs=11))
          ## I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_add$sint(925), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
          ## T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
          def pyxtnm1743(arg1, arg2): ## timp: sint_add$sint(925)
            pyxtnm1737 = arg1
            pyxtnm1738 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1742 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_add$sint(2584));$list(I1FUNDCL(XATS2PY_sint_add$sint(4901);$list(FJARGdarg($list(I1BNDcons(I1TNM(1739);I0Pvar(i1(4902));$list(@(i1(4902),I1Vtnm(I1TNM(1739))))),I1BNDcons(I1TNM(1740);I0Pvar(i2(4903));$list(@(i2(4903),I1Vtnm(I1TNM(1740))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_add$sint);G1Nlist($list())))))))
            pyxtnm1741 = XATSDAPP(XATS2PY_sint_add_sint(pyxtnm1737, pyxtnm1738))
            pyxtnm1742 = pyxtnm1741
            ## end-of(let)
            ## I1CMP:return:pyxtnm1742
            return pyxtnm1742
          ## endtimp(sint_add$sint(925))
          pyxtnm1744 = XATSDAPP(pyxtnm1743(XATSP1CN("TMint", pyxtnm1734[0+1]), XATSP1CN("TMint", pyxtnm1736[0+1])))
          pyxtnm1745 = XATSCAPP("TMint", [0, pyxtnm1744])
          pyxtnm1746 = pyxtnm1745
          ## end-of(let)
          pyxtnm1917 = pyxtnm1746
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1747);I0Pstr(T_STRN1_clsd("-";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("-"))): ## { // gpt
          pyxtnm1747 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1763 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5537(line=386,offs=1)--5566(line=386,offs=30)))
          ## I1VALDCL
          pyxtnm1748 = None
          pyxtnm1748 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5567(line=387,offs=1)--5596(line=387,offs=30)))
          ## I1VALDCL
          pyxtnm1749 = None
          pyxtnm1749 = XATSP1CN("list_cons", pyxtnm1748[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1748[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5597(line=388,offs=1)--5630(line=388,offs=34)))
          ## I1VALDCL
          pyxtnm1751 = None
          pyxtnm1750 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1748[0+1])))
          pyxtnm1751 = pyxtnm1750
          XATS000_patck(XATS000_ctgeq(pyxtnm1750, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5631(line=389,offs=1)--5664(line=389,offs=34)))
          ## I1VALDCL
          pyxtnm1753 = None
          pyxtnm1752 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1749[0+1])))
          pyxtnm1753 = pyxtnm1752
          XATS000_patck(XATS000_ctgeq(pyxtnm1752, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(5522(line=384,offs=10)--5523(line=384,offs=11))
          ## I0Etapq(I0Ecst(sint_sub$sint(926)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2881(line=131,offs=1)--2894(line=131,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_sub$sint(926), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2845(line=159,offs=1)--3009(line=171,offs=2)))
          ## T1IMPallx(sint_sub$sint(926)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_sub$sint(926);$list()))))
          def pyxtnm1760(arg1, arg2): ## timp: sint_sub$sint(926)
            pyxtnm1754 = arg1
            pyxtnm1755 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1759 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2935(line=167,offs=1)--3007(line=170,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_sub$sint(2585));$list(I1FUNDCL(XATS2PY_sint_sub$sint(4906);$list(FJARGdarg($list(I1BNDcons(I1TNM(1756);I0Pvar(i1(4907));$list(@(i1(4907),I1Vtnm(I1TNM(1756))))),I1BNDcons(I1TNM(1757);I0Pvar(i2(4908));$list(@(i2(4908),I1Vtnm(I1TNM(1757))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_sub$sint);G1Nlist($list())))))))
            pyxtnm1758 = XATSDAPP(XATS2PY_sint_sub_sint(pyxtnm1754, pyxtnm1755))
            pyxtnm1759 = pyxtnm1758
            ## end-of(let)
            ## I1CMP:return:pyxtnm1759
            return pyxtnm1759
          ## endtimp(sint_sub$sint(926))
          pyxtnm1761 = XATSDAPP(pyxtnm1760(XATSP1CN("TMint", pyxtnm1751[0+1]), XATSP1CN("TMint", pyxtnm1753[0+1])))
          pyxtnm1762 = XATSCAPP("TMint", [0, pyxtnm1761])
          pyxtnm1763 = pyxtnm1762
          ## end-of(let)
          pyxtnm1917 = pyxtnm1763
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1764);I0Pstr(T_STRN1_clsd("*";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("*"))): ## { // gpt
          pyxtnm1764 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1780 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5701(line=395,offs=1)--5730(line=395,offs=30)))
          ## I1VALDCL
          pyxtnm1765 = None
          pyxtnm1765 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5731(line=396,offs=1)--5760(line=396,offs=30)))
          ## I1VALDCL
          pyxtnm1766 = None
          pyxtnm1766 = XATSP1CN("list_cons", pyxtnm1765[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1765[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5761(line=397,offs=1)--5794(line=397,offs=34)))
          ## I1VALDCL
          pyxtnm1768 = None
          pyxtnm1767 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1765[0+1])))
          pyxtnm1768 = pyxtnm1767
          XATS000_patck(XATS000_ctgeq(pyxtnm1767, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5795(line=398,offs=1)--5828(line=398,offs=34)))
          ## I1VALDCL
          pyxtnm1770 = None
          pyxtnm1769 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1766[0+1])))
          pyxtnm1770 = pyxtnm1769
          XATS000_patck(XATS000_ctgeq(pyxtnm1769, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(5686(line=393,offs=10)--5687(line=393,offs=11))
          ## I0Etapq(I0Ecst(sint_mul$sint(927)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2946(line=135,offs=1)--2959(line=135,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_mul$sint(927), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3013(line=173,offs=1)--3177(line=185,offs=2)))
          ## T1IMPallx(sint_mul$sint(927)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_mul$sint(927);$list()))))
          def pyxtnm1777(arg1, arg2): ## timp: sint_mul$sint(927)
            pyxtnm1771 = arg1
            pyxtnm1772 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1776 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3103(line=181,offs=1)--3175(line=184,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_mul$sint(2586));$list(I1FUNDCL(XATS2PY_sint_mul$sint(4911);$list(FJARGdarg($list(I1BNDcons(I1TNM(1773);I0Pvar(i1(4912));$list(@(i1(4912),I1Vtnm(I1TNM(1773))))),I1BNDcons(I1TNM(1774);I0Pvar(i2(4913));$list(@(i2(4913),I1Vtnm(I1TNM(1774))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_mul$sint);G1Nlist($list())))))))
            pyxtnm1775 = XATSDAPP(XATS2PY_sint_mul_sint(pyxtnm1771, pyxtnm1772))
            pyxtnm1776 = pyxtnm1775
            ## end-of(let)
            ## I1CMP:return:pyxtnm1776
            return pyxtnm1776
          ## endtimp(sint_mul$sint(927))
          pyxtnm1778 = XATSDAPP(pyxtnm1777(XATSP1CN("TMint", pyxtnm1768[0+1]), XATSP1CN("TMint", pyxtnm1770[0+1])))
          pyxtnm1779 = XATSCAPP("TMint", [0, pyxtnm1778])
          pyxtnm1780 = pyxtnm1779
          ## end-of(let)
          pyxtnm1917 = pyxtnm1780
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1781);I0Pstr(T_STRN1_clsd("/";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("/"))): ## { // gpt
          pyxtnm1781 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1797 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5865(line=404,offs=1)--5894(line=404,offs=30)))
          ## I1VALDCL
          pyxtnm1782 = None
          pyxtnm1782 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5895(line=405,offs=1)--5924(line=405,offs=30)))
          ## I1VALDCL
          pyxtnm1783 = None
          pyxtnm1783 = XATSP1CN("list_cons", pyxtnm1782[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1782[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5925(line=406,offs=1)--5958(line=406,offs=34)))
          ## I1VALDCL
          pyxtnm1785 = None
          pyxtnm1784 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1782[0+1])))
          pyxtnm1785 = pyxtnm1784
          XATS000_patck(XATS000_ctgeq(pyxtnm1784, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(5959(line=407,offs=1)--5992(line=407,offs=34)))
          ## I1VALDCL
          pyxtnm1787 = None
          pyxtnm1786 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1783[0+1])))
          pyxtnm1787 = pyxtnm1786
          XATS000_patck(XATS000_ctgeq(pyxtnm1786, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(5850(line=402,offs=10)--5851(line=402,offs=11))
          ## I0Etapq(I0Ecst(sint_div$sint(928)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(3011(line=139,offs=1)--3024(line=139,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_div$sint(928), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3181(line=187,offs=1)--3345(line=199,offs=2)))
          ## T1IMPallx(sint_div$sint(928)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_div$sint(928);$list()))))
          def pyxtnm1794(arg1, arg2): ## timp: sint_div$sint(928)
            pyxtnm1788 = arg1
            pyxtnm1789 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1793 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3271(line=195,offs=1)--3343(line=198,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_div$sint(2587));$list(I1FUNDCL(XATS2PY_sint_div$sint(4916);$list(FJARGdarg($list(I1BNDcons(I1TNM(1790);I0Pvar(i1(4917));$list(@(i1(4917),I1Vtnm(I1TNM(1790))))),I1BNDcons(I1TNM(1791);I0Pvar(i2(4918));$list(@(i2(4918),I1Vtnm(I1TNM(1791))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_div$sint);G1Nlist($list())))))))
            pyxtnm1792 = XATSDAPP(XATS2PY_sint_div_sint(pyxtnm1788, pyxtnm1789))
            pyxtnm1793 = pyxtnm1792
            ## end-of(let)
            ## I1CMP:return:pyxtnm1793
            return pyxtnm1793
          ## endtimp(sint_div$sint(928))
          pyxtnm1795 = XATSDAPP(pyxtnm1794(XATSP1CN("TMint", pyxtnm1785[0+1]), XATSP1CN("TMint", pyxtnm1787[0+1])))
          pyxtnm1796 = XATSCAPP("TMint", [0, pyxtnm1795])
          pyxtnm1797 = pyxtnm1796
          ## end-of(let)
          pyxtnm1917 = pyxtnm1797
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1798);I0Pstr(T_STRN1_clsd("%";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("%"))): ## { // gpt
          pyxtnm1798 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1814 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6029(line=413,offs=1)--6058(line=413,offs=30)))
          ## I1VALDCL
          pyxtnm1799 = None
          pyxtnm1799 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6059(line=414,offs=1)--6088(line=414,offs=30)))
          ## I1VALDCL
          pyxtnm1800 = None
          pyxtnm1800 = XATSP1CN("list_cons", pyxtnm1799[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1799[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6089(line=415,offs=1)--6122(line=415,offs=34)))
          ## I1VALDCL
          pyxtnm1802 = None
          pyxtnm1801 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1799[0+1])))
          pyxtnm1802 = pyxtnm1801
          XATS000_patck(XATS000_ctgeq(pyxtnm1801, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6123(line=416,offs=1)--6156(line=416,offs=34)))
          ## I1VALDCL
          pyxtnm1804 = None
          pyxtnm1803 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1800[0+1])))
          pyxtnm1804 = pyxtnm1803
          XATS000_patck(XATS000_ctgeq(pyxtnm1803, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(6014(line=411,offs=10)--6015(line=411,offs=11))
          ## I0Etapq(I0Ecst(sint_mod$sint(929)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(3076(line=143,offs=1)--3089(line=143,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_mod$sint(929), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3349(line=201,offs=1)--3513(line=213,offs=2)))
          ## T1IMPallx(sint_mod$sint(929)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_mod$sint(929);$list()))))
          def pyxtnm1811(arg1, arg2): ## timp: sint_mod$sint(929)
            pyxtnm1805 = arg1
            pyxtnm1806 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1810 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3439(line=209,offs=1)--3511(line=212,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_mod$sint(2588));$list(I1FUNDCL(XATS2PY_sint_mod$sint(4921);$list(FJARGdarg($list(I1BNDcons(I1TNM(1807);I0Pvar(i1(4922));$list(@(i1(4922),I1Vtnm(I1TNM(1807))))),I1BNDcons(I1TNM(1808);I0Pvar(i2(4923));$list(@(i2(4923),I1Vtnm(I1TNM(1808))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_mod$sint);G1Nlist($list())))))))
            pyxtnm1809 = XATSDAPP(XATS2PY_sint_mod_sint(pyxtnm1805, pyxtnm1806))
            pyxtnm1810 = pyxtnm1809
            ## end-of(let)
            ## I1CMP:return:pyxtnm1810
            return pyxtnm1810
          ## endtimp(sint_mod$sint(929))
          pyxtnm1812 = XATSDAPP(pyxtnm1811(XATSP1CN("TMint", pyxtnm1802[0+1]), XATSP1CN("TMint", pyxtnm1804[0+1])))
          pyxtnm1813 = XATSCAPP("TMint", [0, pyxtnm1812])
          pyxtnm1814 = pyxtnm1813
          ## end-of(let)
          pyxtnm1917 = pyxtnm1814
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1815);I0Pstr(T_STRN1_clsd("<";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("<"))): ## { // gpt
          pyxtnm1815 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1831 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6196(line=423,offs=1)--6225(line=423,offs=30)))
          ## I1VALDCL
          pyxtnm1816 = None
          pyxtnm1816 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6226(line=424,offs=1)--6255(line=424,offs=30)))
          ## I1VALDCL
          pyxtnm1817 = None
          pyxtnm1817 = XATSP1CN("list_cons", pyxtnm1816[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1816[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6256(line=425,offs=1)--6289(line=425,offs=34)))
          ## I1VALDCL
          pyxtnm1819 = None
          pyxtnm1818 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1816[0+1])))
          pyxtnm1819 = pyxtnm1818
          XATS000_patck(XATS000_ctgeq(pyxtnm1818, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6290(line=426,offs=1)--6323(line=426,offs=34)))
          ## I1VALDCL
          pyxtnm1821 = None
          pyxtnm1820 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1817[0+1])))
          pyxtnm1821 = pyxtnm1820
          XATS000_patck(XATS000_ctgeq(pyxtnm1820, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(6181(line=421,offs=10)--6182(line=421,offs=11))
          ## I0Etapq(I0Ecst(sint_lt$sint(918)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2041(line=83,offs=1)--2053(line=83,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_lt$sint(918), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1612(line=56,offs=1)--1773(line=68,offs=2)))
          ## T1IMPallx(sint_lt$sint(918)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_lt$sint(918);$list()))))
          def pyxtnm1828(arg1, arg2): ## timp: sint_lt$sint(918)
            pyxtnm1822 = arg1
            pyxtnm1823 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1827 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1700(line=64,offs=1)--1771(line=67,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_lt$sint(2578));$list(I1FUNDCL(XATS2PY_sint_lt$sint(4871);$list(FJARGdarg($list(I1BNDcons(I1TNM(1824);I0Pvar(i1(4872));$list(@(i1(4872),I1Vtnm(I1TNM(1824))))),I1BNDcons(I1TNM(1825);I0Pvar(i2(4873));$list(@(i2(4873),I1Vtnm(I1TNM(1825))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_lt$sint);G1Nlist($list())))))))
            pyxtnm1826 = XATSDAPP(XATS2PY_sint_lt_sint(pyxtnm1822, pyxtnm1823))
            pyxtnm1827 = pyxtnm1826
            ## end-of(let)
            ## I1CMP:return:pyxtnm1827
            return pyxtnm1827
          ## endtimp(sint_lt$sint(918))
          pyxtnm1829 = XATSDAPP(pyxtnm1828(XATSP1CN("TMint", pyxtnm1819[0+1]), XATSP1CN("TMint", pyxtnm1821[0+1])))
          pyxtnm1830 = XATSCAPP("TMbtf", [1, pyxtnm1829])
          pyxtnm1831 = pyxtnm1830
          ## end-of(let)
          pyxtnm1917 = pyxtnm1831
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1832);I0Pstr(T_STRN1_clsd(">";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN(">"))): ## { // gpt
          pyxtnm1832 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1848 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6360(line=432,offs=1)--6389(line=432,offs=30)))
          ## I1VALDCL
          pyxtnm1833 = None
          pyxtnm1833 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6390(line=433,offs=1)--6419(line=433,offs=30)))
          ## I1VALDCL
          pyxtnm1834 = None
          pyxtnm1834 = XATSP1CN("list_cons", pyxtnm1833[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1833[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6420(line=434,offs=1)--6453(line=434,offs=34)))
          ## I1VALDCL
          pyxtnm1836 = None
          pyxtnm1835 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1833[0+1])))
          pyxtnm1836 = pyxtnm1835
          XATS000_patck(XATS000_ctgeq(pyxtnm1835, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6454(line=435,offs=1)--6487(line=435,offs=34)))
          ## I1VALDCL
          pyxtnm1838 = None
          pyxtnm1837 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1834[0+1])))
          pyxtnm1838 = pyxtnm1837
          XATS000_patck(XATS000_ctgeq(pyxtnm1837, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(6345(line=430,offs=10)--6346(line=430,offs=11))
          ## I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_gt$sint(919), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
          ## T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
          def pyxtnm1845(arg1, arg2): ## timp: sint_gt$sint(919)
            pyxtnm1839 = arg1
            pyxtnm1840 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1844 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gt$sint(2579));$list(I1FUNDCL(XATS2PY_sint_gt$sint(4876);$list(FJARGdarg($list(I1BNDcons(I1TNM(1841);I0Pvar(i1(4877));$list(@(i1(4877),I1Vtnm(I1TNM(1841))))),I1BNDcons(I1TNM(1842);I0Pvar(i2(4878));$list(@(i2(4878),I1Vtnm(I1TNM(1842))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gt$sint);G1Nlist($list())))))))
            pyxtnm1843 = XATSDAPP(XATS2PY_sint_gt_sint(pyxtnm1839, pyxtnm1840))
            pyxtnm1844 = pyxtnm1843
            ## end-of(let)
            ## I1CMP:return:pyxtnm1844
            return pyxtnm1844
          ## endtimp(sint_gt$sint(919))
          pyxtnm1846 = XATSDAPP(pyxtnm1845(XATSP1CN("TMint", pyxtnm1836[0+1]), XATSP1CN("TMint", pyxtnm1838[0+1])))
          pyxtnm1847 = XATSCAPP("TMbtf", [1, pyxtnm1846])
          pyxtnm1848 = pyxtnm1847
          ## end-of(let)
          pyxtnm1917 = pyxtnm1848
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1849);I0Pstr(T_STRN1_clsd("=";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("="))): ## { // gpt
          pyxtnm1849 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1865 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6524(line=441,offs=1)--6553(line=441,offs=30)))
          ## I1VALDCL
          pyxtnm1850 = None
          pyxtnm1850 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6554(line=442,offs=1)--6583(line=442,offs=30)))
          ## I1VALDCL
          pyxtnm1851 = None
          pyxtnm1851 = XATSP1CN("list_cons", pyxtnm1850[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1850[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6584(line=443,offs=1)--6617(line=443,offs=34)))
          ## I1VALDCL
          pyxtnm1853 = None
          pyxtnm1852 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1850[0+1])))
          pyxtnm1853 = pyxtnm1852
          XATS000_patck(XATS000_ctgeq(pyxtnm1852, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6618(line=444,offs=1)--6651(line=444,offs=34)))
          ## I1VALDCL
          pyxtnm1855 = None
          pyxtnm1854 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1851[0+1])))
          pyxtnm1855 = pyxtnm1854
          XATS000_patck(XATS000_ctgeq(pyxtnm1854, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(6509(line=439,offs=10)--6510(line=439,offs=11))
          ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
          ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
          def pyxtnm1862(arg1, arg2): ## timp: sint_eq$sint(920)
            pyxtnm1856 = arg1
            pyxtnm1857 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1861 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(1858);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(1858))))),I1BNDcons(I1TNM(1859);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(1859))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
            pyxtnm1860 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm1856, pyxtnm1857))
            pyxtnm1861 = pyxtnm1860
            ## end-of(let)
            ## I1CMP:return:pyxtnm1861
            return pyxtnm1861
          ## endtimp(sint_eq$sint(920))
          pyxtnm1863 = XATSDAPP(pyxtnm1862(XATSP1CN("TMint", pyxtnm1853[0+1]), XATSP1CN("TMint", pyxtnm1855[0+1])))
          pyxtnm1864 = XATSCAPP("TMbtf", [1, pyxtnm1863])
          pyxtnm1865 = pyxtnm1864
          ## end-of(let)
          pyxtnm1917 = pyxtnm1865
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1866);I0Pstr(T_STRN1_clsd("<=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("<="))): ## { // gpt
          pyxtnm1866 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1882 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6690(line=450,offs=1)--6719(line=450,offs=30)))
          ## I1VALDCL
          pyxtnm1867 = None
          pyxtnm1867 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6720(line=451,offs=1)--6749(line=451,offs=30)))
          ## I1VALDCL
          pyxtnm1868 = None
          pyxtnm1868 = XATSP1CN("list_cons", pyxtnm1867[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1867[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6750(line=452,offs=1)--6783(line=452,offs=34)))
          ## I1VALDCL
          pyxtnm1870 = None
          pyxtnm1869 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1867[0+1])))
          pyxtnm1870 = pyxtnm1869
          XATS000_patck(XATS000_ctgeq(pyxtnm1869, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6784(line=453,offs=1)--6817(line=453,offs=34)))
          ## I1VALDCL
          pyxtnm1872 = None
          pyxtnm1871 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1868[0+1])))
          pyxtnm1872 = pyxtnm1871
          XATS000_patck(XATS000_ctgeq(pyxtnm1871, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(6674(line=448,offs=10)--6676(line=448,offs=12))
          ## I0Etapq(I0Ecst(sint_lte$sint(921)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2344(line=100,offs=1)--2357(line=100,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_lte$sint(921), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2130(line=100,offs=1)--2294(line=112,offs=2)))
          ## T1IMPallx(sint_lte$sint(921)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_lte$sint(921);$list()))))
          def pyxtnm1879(arg1, arg2): ## timp: sint_lte$sint(921)
            pyxtnm1873 = arg1
            pyxtnm1874 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1878 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2220(line=108,offs=1)--2292(line=111,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_lte$sint(2581));$list(I1FUNDCL(XATS2PY_sint_lte$sint(4886);$list(FJARGdarg($list(I1BNDcons(I1TNM(1875);I0Pvar(i1(4887));$list(@(i1(4887),I1Vtnm(I1TNM(1875))))),I1BNDcons(I1TNM(1876);I0Pvar(i2(4888));$list(@(i2(4888),I1Vtnm(I1TNM(1876))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_lte$sint);G1Nlist($list())))))))
            pyxtnm1877 = XATSDAPP(XATS2PY_sint_lte_sint(pyxtnm1873, pyxtnm1874))
            pyxtnm1878 = pyxtnm1877
            ## end-of(let)
            ## I1CMP:return:pyxtnm1878
            return pyxtnm1878
          ## endtimp(sint_lte$sint(921))
          pyxtnm1880 = XATSDAPP(pyxtnm1879(XATSP1CN("TMint", pyxtnm1870[0+1]), XATSP1CN("TMint", pyxtnm1872[0+1])))
          pyxtnm1881 = XATSCAPP("TMbtf", [1, pyxtnm1880])
          pyxtnm1882 = pyxtnm1881
          ## end-of(let)
          pyxtnm1917 = pyxtnm1882
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1883);I0Pstr(T_STRN1_clsd(">=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN(">="))): ## { // gpt
          pyxtnm1883 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1899 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6856(line=459,offs=1)--6885(line=459,offs=30)))
          ## I1VALDCL
          pyxtnm1884 = None
          pyxtnm1884 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6886(line=460,offs=1)--6915(line=460,offs=30)))
          ## I1VALDCL
          pyxtnm1885 = None
          pyxtnm1885 = XATSP1CN("list_cons", pyxtnm1884[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1884[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6916(line=461,offs=1)--6949(line=461,offs=34)))
          ## I1VALDCL
          pyxtnm1887 = None
          pyxtnm1886 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1884[0+1])))
          pyxtnm1887 = pyxtnm1886
          XATS000_patck(XATS000_ctgeq(pyxtnm1886, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(6950(line=462,offs=1)--6983(line=462,offs=34)))
          ## I1VALDCL
          pyxtnm1889 = None
          pyxtnm1888 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1885[0+1])))
          pyxtnm1889 = pyxtnm1888
          XATS000_patck(XATS000_ctgeq(pyxtnm1888, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(6840(line=457,offs=10)--6842(line=457,offs=12))
          ## I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_gte$sint(922), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
          ## T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
          def pyxtnm1896(arg1, arg2): ## timp: sint_gte$sint(922)
            pyxtnm1890 = arg1
            pyxtnm1891 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1895 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gte$sint(2582));$list(I1FUNDCL(XATS2PY_sint_gte$sint(4891);$list(FJARGdarg($list(I1BNDcons(I1TNM(1892);I0Pvar(i1(4892));$list(@(i1(4892),I1Vtnm(I1TNM(1892))))),I1BNDcons(I1TNM(1893);I0Pvar(i2(4893));$list(@(i2(4893),I1Vtnm(I1TNM(1893))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gte$sint);G1Nlist($list())))))))
            pyxtnm1894 = XATSDAPP(XATS2PY_sint_gte_sint(pyxtnm1890, pyxtnm1891))
            pyxtnm1895 = pyxtnm1894
            ## end-of(let)
            ## I1CMP:return:pyxtnm1895
            return pyxtnm1895
          ## endtimp(sint_gte$sint(922))
          pyxtnm1897 = XATSDAPP(pyxtnm1896(XATSP1CN("TMint", pyxtnm1887[0+1]), XATSP1CN("TMint", pyxtnm1889[0+1])))
          pyxtnm1898 = XATSCAPP("TMbtf", [1, pyxtnm1897])
          pyxtnm1899 = pyxtnm1898
          ## end-of(let)
          pyxtnm1917 = pyxtnm1899
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1900);I0Pstr(T_STRN1_clsd("!=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm1729[0+1]), XATSSTRN("!="))): ## { // gpt
          pyxtnm1900 = XATSP1CN("TMopr", pyxtnm1729[0+1])
          ## let
          pyxtnm1916 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7022(line=468,offs=1)--7051(line=468,offs=30)))
          ## I1VALDCL
          pyxtnm1901 = None
          pyxtnm1901 = XATSP1CN("TMopr", pyxtnm1729[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm1729[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7052(line=469,offs=1)--7081(line=469,offs=30)))
          ## I1VALDCL
          pyxtnm1902 = None
          pyxtnm1902 = XATSP1CN("list_cons", pyxtnm1901[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm1901[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7082(line=470,offs=1)--7115(line=470,offs=34)))
          ## I1VALDCL
          pyxtnm1904 = None
          pyxtnm1903 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1901[0+1])))
          pyxtnm1904 = pyxtnm1903
          XATS000_patck(XATS000_ctgeq(pyxtnm1903, XATSCTAG("TMint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7116(line=471,offs=1)--7149(line=471,offs=34)))
          ## I1VALDCL
          pyxtnm1906 = None
          pyxtnm1905 = XATSDAPP(term_interp_4894(XATSP1CN("list_cons", pyxtnm1902[0+1])))
          pyxtnm1906 = pyxtnm1905
          XATS000_patck(XATS000_ctgeq(pyxtnm1905, XATSCTAG("TMint",0)))
          ## LCSRCsome1(lambda1.dats)@(7006(line=466,offs=10)--7008(line=466,offs=12))
          ## I0Etapq(I0Ecst(sint_neq$sint(923)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2472(line=108,offs=1)--2485(line=108,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_neq$sint(923), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2466(line=128,offs=1)--2630(line=140,offs=2)))
          ## T1IMPallx(sint_neq$sint(923)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_neq$sint(923);$list()))))
          def pyxtnm1913(arg1, arg2): ## timp: sint_neq$sint(923)
            pyxtnm1907 = arg1
            pyxtnm1908 = arg2
            ## I1CMP:start
            ## let
            pyxtnm1912 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2556(line=136,offs=1)--2628(line=139,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_neq$sint(2583));$list(I1FUNDCL(XATS2PY_sint_neq$sint(4896);$list(FJARGdarg($list(I1BNDcons(I1TNM(1909);I0Pvar(i1(4897));$list(@(i1(4897),I1Vtnm(I1TNM(1909))))),I1BNDcons(I1TNM(1910);I0Pvar(i2(4898));$list(@(i2(4898),I1Vtnm(I1TNM(1910))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_neq$sint);G1Nlist($list())))))))
            pyxtnm1911 = XATSDAPP(XATS2PY_sint_neq_sint(pyxtnm1907, pyxtnm1908))
            pyxtnm1912 = pyxtnm1911
            ## end-of(let)
            ## I1CMP:return:pyxtnm1912
            return pyxtnm1912
          ## endtimp(sint_neq$sint(923))
          pyxtnm1914 = XATSDAPP(pyxtnm1913(XATSP1CN("TMint", pyxtnm1904[0+1]), XATSP1CN("TMint", pyxtnm1906[0+1])))
          pyxtnm1915 = XATSCAPP("TMbtf", [1, pyxtnm1914])
          pyxtnm1916 = pyxtnm1915
          ## end-of(let)
          pyxtnm1917 = pyxtnm1916
          break ## cls
        ## } // gpt
        ## } // cls
        XATS000_cfail()
      ## } while True // end-of(do-cls)
      pyxtnm1929 = pyxtnm1917
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1918);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5304)),I0Pvar(tm2(5305)),I0Pvar(tm3(5306))));$list(@(tm1(5304),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1918));0)),@(tm2(5305),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1918));1)),@(tm3(5306),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(1918));2)))))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMif0",6))): ## { // gpt
      pyxtnm1918 = pyxtnm1713
      ## let
      pyxtnm1925 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7220(line=479,offs=1)--7246(line=479,offs=27)))
      ## I1VALDCL
      pyxtnm1920 = None
      pyxtnm1919 = XATSDAPP(term_interp_4894(XATSP1CN("TMif0", pyxtnm1918[0+1])))
      pyxtnm1920 = pyxtnm1919
      XATS000_patck(True)
      pyxtnm1924 = None
      while True: ## do {
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(1921);I0Pdapp(I0Pcon(TMbtf(33));$list(I0Pvar(btf(5308))));$list(@(btf(5308),I1Vp1cn(I0Pcon(TMbtf(33));I1Vtnm(I1TNM(1921));0)))))
        if (XATS000_ctgeq(pyxtnm1920, XATSCTAG("TMbtf",1))): ## { // gpt
          pyxtnm1921 = pyxtnm1920
          pyxtnm1922 = None
          if (XATSP1CN("TMbtf", pyxtnm1921[0+1])):
            pyxtnm1922 = XATSP1CN("TMif0", pyxtnm1918[1+1])
          else:
            pyxtnm1922 = XATSP1CN("TMif0", pyxtnm1918[2+1])
          ## end-of(if)
          pyxtnm1923 = XATSDAPP(term_interp_4894(pyxtnm1922))
          pyxtnm1924 = pyxtnm1923
          break ## cls
        ## } // gpt
        ## } // cls
        XATS000_cfail()
      ## } while True // end-of(do-cls)
      pyxtnm1925 = pyxtnm1924
      ## end-of(let)
      pyxtnm1929 = pyxtnm1925
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(1926);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5309)),I0Pvar(x01(5310)),I0Pvar(tmx(5311))));$list(@(f00(5309),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1926));0)),@(x01(5310),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1926));1)),@(tmx(5311),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(1926));2)))))
    if (XATS000_ctgeq(pyxtnm1713, XATSCTAG("TMfix",7))): ## { // gpt
      pyxtnm1926 = pyxtnm1713
      pyxtnm1927 = XATSDAPP(term_subst_4023(XATSP1CN("TMfix", pyxtnm1926[2+1]), XATSP1CN("TMfix", pyxtnm1926[0+1]), pyxtnm1713))
      pyxtnm1928 = XATSCAPP("TMlam", [3, XATSP1CN("TMfix", pyxtnm1926[1+1]), pyxtnm1927])
      pyxtnm1929 = pyxtnm1928
      break ## cls
    ## } // gpt
    ## } // cls
    XATS000_cfail()
  ## } while True // end-of(do-cls)
  ## I1CMP:return:pyxtnm1929
  return pyxtnm1929
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7467(line=496,offs=1)--7541(line=497,offs=54)))
## I1VALDCL
pyxtnm1967 = None
## LCSRCsome1(lambda1.dats)@(7476(line=496,offs=10)--7484(line=496,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm1963(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1930 = arg1
  pyxtnm1931 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1954(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1932 = arg1
    pyxtnm1933 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1953 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1937 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1935(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1934 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1934
      return pyxtnm1934
    ## endtimp(gs_print$beg(793))
    pyxtnm1936 = XATSDAPP(pyxtnm1935())
    pyxtnm1937 = pyxtnm1936
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1943 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1942(arg1): ## timp: strn_print(1029)
      pyxtnm1938 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1941 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1939);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1939))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1940 = XATSDAPP(XATS2PY_strn_print(pyxtnm1938))
      pyxtnm1941 = pyxtnm1940
      ## end-of(let)
      ## I1CMP:return:pyxtnm1941
      return pyxtnm1941
    ## endtimp(strn_print(1029))
    pyxtnm1943 = pyxtnm1942
    pyxtnm1944 = XATSDAPP(pyxtnm1943(pyxtnm1932))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1946(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1945 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1945
      return pyxtnm1945
    ## endtimp(gs_print$sep(794))
    pyxtnm1947 = XATSDAPP(pyxtnm1946())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1948 = None
    pyxtnm1948 = pyxtnm879
    pyxtnm1949 = XATSDAPP(pyxtnm1948(pyxtnm1933))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1951(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1950 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1950
      return pyxtnm1950
    ## endtimp(gs_print$end(795))
    pyxtnm1952 = XATSDAPP(pyxtnm1951())
    pyxtnm1953 = pyxtnm1952
    ## end-of(let)
    ## I1CMP:return:pyxtnm1953
    return pyxtnm1953
  ## endtimp(gs_print_a2(798))
  pyxtnm1955 = XATSDAPP(pyxtnm1954(pyxtnm1930, pyxtnm1931))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1961 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1960(arg1): ## timp: strn_print(1029)
    pyxtnm1956 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1959 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1957);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1957))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1958 = XATSDAPP(XATS2PY_strn_print(pyxtnm1956))
    pyxtnm1959 = pyxtnm1958
    ## end-of(let)
    ## I1CMP:return:pyxtnm1959
    return pyxtnm1959
  ## endtimp(strn_print(1029))
  pyxtnm1961 = pyxtnm1960
  pyxtnm1962 = XATSDAPP(pyxtnm1961(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm1962
  return pyxtnm1962
## endtimp(gs_println_a2(811))
pyxtnm1964 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm1965 = XATSCAPP("TMapp", [4, pyxtnm1297, pyxtnm1964])
pyxtnm1966 = XATSDAPP(pyxtnm1963(XATSSTRN("TMapp(TMdbl, TMint(10)) = "), pyxtnm1965))
pyxtnm1967 = pyxtnm1966
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7542(line=498,offs=1)--7630(line=500,offs=2)))
## I1VALDCL
pyxtnm2006 = None
## LCSRCsome1(lambda1.dats)@(7551(line=498,offs=10)--7559(line=498,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2001(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm1968 = arg1
  pyxtnm1969 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm1992(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm1970 = arg1
    pyxtnm1971 = arg2
    ## I1CMP:start
    ## let
    pyxtnm1991 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm1975 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm1973(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm1972 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1972
      return pyxtnm1972
    ## endtimp(gs_print$beg(793))
    pyxtnm1974 = XATSDAPP(pyxtnm1973())
    pyxtnm1975 = pyxtnm1974
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm1981 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm1980(arg1): ## timp: strn_print(1029)
      pyxtnm1976 = arg1
      ## I1CMP:start
      ## let
      pyxtnm1979 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1977);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1977))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm1978 = XATSDAPP(XATS2PY_strn_print(pyxtnm1976))
      pyxtnm1979 = pyxtnm1978
      ## end-of(let)
      ## I1CMP:return:pyxtnm1979
      return pyxtnm1979
    ## endtimp(strn_print(1029))
    pyxtnm1981 = pyxtnm1980
    pyxtnm1982 = XATSDAPP(pyxtnm1981(pyxtnm1970))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm1984(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm1983 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1983
      return pyxtnm1983
    ## endtimp(gs_print$sep(794))
    pyxtnm1985 = XATSDAPP(pyxtnm1984())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm1986 = None
    pyxtnm1986 = pyxtnm879
    pyxtnm1987 = XATSDAPP(pyxtnm1986(pyxtnm1971))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm1989(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm1988 = XATSTUP0([])
      ## I1CMP:return:pyxtnm1988
      return pyxtnm1988
    ## endtimp(gs_print$end(795))
    pyxtnm1990 = XATSDAPP(pyxtnm1989())
    pyxtnm1991 = pyxtnm1990
    ## end-of(let)
    ## I1CMP:return:pyxtnm1991
    return pyxtnm1991
  ## endtimp(gs_print_a2(798))
  pyxtnm1993 = XATSDAPP(pyxtnm1992(pyxtnm1968, pyxtnm1969))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm1999 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm1998(arg1): ## timp: strn_print(1029)
    pyxtnm1994 = arg1
    ## I1CMP:start
    ## let
    pyxtnm1997 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(1995);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(1995))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm1996 = XATSDAPP(XATS2PY_strn_print(pyxtnm1994))
    pyxtnm1997 = pyxtnm1996
    ## end-of(let)
    ## I1CMP:return:pyxtnm1997
    return pyxtnm1997
  ## endtimp(strn_print(1029))
  pyxtnm1999 = pyxtnm1998
  pyxtnm2000 = XATSDAPP(pyxtnm1999(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2000
  return pyxtnm2000
## endtimp(gs_println_a2(811))
pyxtnm2002 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm2003 = XATSCAPP("TMapp", [4, pyxtnm1297, pyxtnm2002])
pyxtnm2004 = XATSDAPP(term_interp_4894(pyxtnm2003))
pyxtnm2005 = XATSDAPP(pyxtnm2001(XATSSTRN("TMapp(TMdbl, TMint(10)) = "), pyxtnm2004))
pyxtnm2006 = pyxtnm2005
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7654(line=502,offs=1)--7728(line=504,offs=54)))
## I1VALDCL
pyxtnm2044 = None
## LCSRCsome1(lambda1.dats)@(7663(line=503,offs=1)--7671(line=503,offs=9))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2040(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2007 = arg1
  pyxtnm2008 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2031(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2009 = arg1
    pyxtnm2010 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2030 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2014 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2012(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2011 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2011
      return pyxtnm2011
    ## endtimp(gs_print$beg(793))
    pyxtnm2013 = XATSDAPP(pyxtnm2012())
    pyxtnm2014 = pyxtnm2013
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2020 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2019(arg1): ## timp: strn_print(1029)
      pyxtnm2015 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2018 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2016);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2016))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2017 = XATSDAPP(XATS2PY_strn_print(pyxtnm2015))
      pyxtnm2018 = pyxtnm2017
      ## end-of(let)
      ## I1CMP:return:pyxtnm2018
      return pyxtnm2018
    ## endtimp(strn_print(1029))
    pyxtnm2020 = pyxtnm2019
    pyxtnm2021 = XATSDAPP(pyxtnm2020(pyxtnm2009))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2023(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2022 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2022
      return pyxtnm2022
    ## endtimp(gs_print$sep(794))
    pyxtnm2024 = XATSDAPP(pyxtnm2023())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2025 = None
    pyxtnm2025 = pyxtnm879
    pyxtnm2026 = XATSDAPP(pyxtnm2025(pyxtnm2010))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2028(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2027 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2027
      return pyxtnm2027
    ## endtimp(gs_print$end(795))
    pyxtnm2029 = XATSDAPP(pyxtnm2028())
    pyxtnm2030 = pyxtnm2029
    ## end-of(let)
    ## I1CMP:return:pyxtnm2030
    return pyxtnm2030
  ## endtimp(gs_print_a2(798))
  pyxtnm2032 = XATSDAPP(pyxtnm2031(pyxtnm2007, pyxtnm2008))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2038 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2037(arg1): ## timp: strn_print(1029)
    pyxtnm2033 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2036 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2034);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2034))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2035 = XATSDAPP(XATS2PY_strn_print(pyxtnm2033))
    pyxtnm2036 = pyxtnm2035
    ## end-of(let)
    ## I1CMP:return:pyxtnm2036
    return pyxtnm2036
  ## endtimp(strn_print(1029))
  pyxtnm2038 = pyxtnm2037
  pyxtnm2039 = XATSDAPP(pyxtnm2038(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2039
  return pyxtnm2039
## endtimp(gs_println_a2(811))
pyxtnm2041 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm2042 = XATSCAPP("TMapp", [4, pyxtnm1382, pyxtnm2041])
pyxtnm2043 = XATSDAPP(pyxtnm2040(XATSSTRN("TMapp(TMsqr, TMint(10)) = "), pyxtnm2042))
pyxtnm2044 = pyxtnm2043
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7729(line=505,offs=1)--7817(line=508,offs=2)))
## I1VALDCL
pyxtnm2083 = None
## LCSRCsome1(lambda1.dats)@(7738(line=506,offs=1)--7746(line=506,offs=9))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2078(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2045 = arg1
  pyxtnm2046 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2069(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2047 = arg1
    pyxtnm2048 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2068 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2052 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2050(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2049 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2049
      return pyxtnm2049
    ## endtimp(gs_print$beg(793))
    pyxtnm2051 = XATSDAPP(pyxtnm2050())
    pyxtnm2052 = pyxtnm2051
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2058 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2057(arg1): ## timp: strn_print(1029)
      pyxtnm2053 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2056 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2054);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2054))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2055 = XATSDAPP(XATS2PY_strn_print(pyxtnm2053))
      pyxtnm2056 = pyxtnm2055
      ## end-of(let)
      ## I1CMP:return:pyxtnm2056
      return pyxtnm2056
    ## endtimp(strn_print(1029))
    pyxtnm2058 = pyxtnm2057
    pyxtnm2059 = XATSDAPP(pyxtnm2058(pyxtnm2047))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2061(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2060 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2060
      return pyxtnm2060
    ## endtimp(gs_print$sep(794))
    pyxtnm2062 = XATSDAPP(pyxtnm2061())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2063 = None
    pyxtnm2063 = pyxtnm879
    pyxtnm2064 = XATSDAPP(pyxtnm2063(pyxtnm2048))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2066(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2065 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2065
      return pyxtnm2065
    ## endtimp(gs_print$end(795))
    pyxtnm2067 = XATSDAPP(pyxtnm2066())
    pyxtnm2068 = pyxtnm2067
    ## end-of(let)
    ## I1CMP:return:pyxtnm2068
    return pyxtnm2068
  ## endtimp(gs_print_a2(798))
  pyxtnm2070 = XATSDAPP(pyxtnm2069(pyxtnm2045, pyxtnm2046))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2076 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2075(arg1): ## timp: strn_print(1029)
    pyxtnm2071 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2074 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2072);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2072))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2073 = XATSDAPP(XATS2PY_strn_print(pyxtnm2071))
    pyxtnm2074 = pyxtnm2073
    ## end-of(let)
    ## I1CMP:return:pyxtnm2074
    return pyxtnm2074
  ## endtimp(strn_print(1029))
  pyxtnm2076 = pyxtnm2075
  pyxtnm2077 = XATSDAPP(pyxtnm2076(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2077
  return pyxtnm2077
## endtimp(gs_println_a2(811))
pyxtnm2079 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm2080 = XATSCAPP("TMapp", [4, pyxtnm1382, pyxtnm2079])
pyxtnm2081 = XATSDAPP(term_interp_4894(pyxtnm2080))
pyxtnm2082 = XATSDAPP(pyxtnm2078(XATSSTRN("TMapp(TMsqr, TMint(10)) = "), pyxtnm2081))
pyxtnm2083 = pyxtnm2082
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7841(line=510,offs=1)--7956(line=512,offs=52)))
## I1VALDCL
pyxtnm2123 = None
## LCSRCsome1(lambda1.dats)@(7850(line=510,offs=10)--7858(line=510,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2117(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2084 = arg1
  pyxtnm2085 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2108(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2086 = arg1
    pyxtnm2087 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2107 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2091 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2089(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2088 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2088
      return pyxtnm2088
    ## endtimp(gs_print$beg(793))
    pyxtnm2090 = XATSDAPP(pyxtnm2089())
    pyxtnm2091 = pyxtnm2090
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2097 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2096(arg1): ## timp: strn_print(1029)
      pyxtnm2092 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2095 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2093);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2093))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2094 = XATSDAPP(XATS2PY_strn_print(pyxtnm2092))
      pyxtnm2095 = pyxtnm2094
      ## end-of(let)
      ## I1CMP:return:pyxtnm2095
      return pyxtnm2095
    ## endtimp(strn_print(1029))
    pyxtnm2097 = pyxtnm2096
    pyxtnm2098 = XATSDAPP(pyxtnm2097(pyxtnm2086))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2100(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2099 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2099
      return pyxtnm2099
    ## endtimp(gs_print$sep(794))
    pyxtnm2101 = XATSDAPP(pyxtnm2100())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2102 = None
    pyxtnm2102 = pyxtnm879
    pyxtnm2103 = XATSDAPP(pyxtnm2102(pyxtnm2087))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2105(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2104 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2104
      return pyxtnm2104
    ## endtimp(gs_print$end(795))
    pyxtnm2106 = XATSDAPP(pyxtnm2105())
    pyxtnm2107 = pyxtnm2106
    ## end-of(let)
    ## I1CMP:return:pyxtnm2107
    return pyxtnm2107
  ## endtimp(gs_print_a2(798))
  pyxtnm2109 = XATSDAPP(pyxtnm2108(pyxtnm2084, pyxtnm2085))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2115 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2114(arg1): ## timp: strn_print(1029)
    pyxtnm2110 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2113 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2111);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2111))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2112 = XATSDAPP(XATS2PY_strn_print(pyxtnm2110))
    pyxtnm2113 = pyxtnm2112
    ## end-of(let)
    ## I1CMP:return:pyxtnm2113
    return pyxtnm2113
  ## endtimp(strn_print(1029))
  pyxtnm2115 = pyxtnm2114
  pyxtnm2116 = XATSDAPP(pyxtnm2115(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2116
  return pyxtnm2116
## endtimp(gs_println_a2(811))
pyxtnm2118 = XATSCAPP("TMapp", [4, pyxtnm1219, pyxtnm1304])
pyxtnm2119 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm2120 = XATSCAPP("TMapp", [4, pyxtnm2118, pyxtnm2119])
pyxtnm2121 = XATSDAPP(term_interp_4894(pyxtnm2120))
pyxtnm2122 = XATSDAPP(pyxtnm2117(XATSSTRN("TMapp(TMapp(TMtwo, TMtpl), TMint(10)) = "), pyxtnm2121))
pyxtnm2123 = pyxtnm2122
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(7960(line=514,offs=1)--8103(line=516,offs=66)))
## I1VALDCL
pyxtnm2164 = None
## LCSRCsome1(lambda1.dats)@(7969(line=514,offs=10)--7977(line=514,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2157(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2124 = arg1
  pyxtnm2125 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2148(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2126 = arg1
    pyxtnm2127 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2147 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2131 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2129(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2128 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2128
      return pyxtnm2128
    ## endtimp(gs_print$beg(793))
    pyxtnm2130 = XATSDAPP(pyxtnm2129())
    pyxtnm2131 = pyxtnm2130
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2137 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2136(arg1): ## timp: strn_print(1029)
      pyxtnm2132 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2135 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2133);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2133))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2134 = XATSDAPP(XATS2PY_strn_print(pyxtnm2132))
      pyxtnm2135 = pyxtnm2134
      ## end-of(let)
      ## I1CMP:return:pyxtnm2135
      return pyxtnm2135
    ## endtimp(strn_print(1029))
    pyxtnm2137 = pyxtnm2136
    pyxtnm2138 = XATSDAPP(pyxtnm2137(pyxtnm2126))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2140(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2139 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2139
      return pyxtnm2139
    ## endtimp(gs_print$sep(794))
    pyxtnm2141 = XATSDAPP(pyxtnm2140())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2142 = None
    pyxtnm2142 = pyxtnm879
    pyxtnm2143 = XATSDAPP(pyxtnm2142(pyxtnm2127))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2145(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2144 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2144
      return pyxtnm2144
    ## endtimp(gs_print$end(795))
    pyxtnm2146 = XATSDAPP(pyxtnm2145())
    pyxtnm2147 = pyxtnm2146
    ## end-of(let)
    ## I1CMP:return:pyxtnm2147
    return pyxtnm2147
  ## endtimp(gs_print_a2(798))
  pyxtnm2149 = XATSDAPP(pyxtnm2148(pyxtnm2124, pyxtnm2125))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2155 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2154(arg1): ## timp: strn_print(1029)
    pyxtnm2150 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2153 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2151);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2151))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2152 = XATSDAPP(XATS2PY_strn_print(pyxtnm2150))
    pyxtnm2153 = pyxtnm2152
    ## end-of(let)
    ## I1CMP:return:pyxtnm2153
    return pyxtnm2153
  ## endtimp(strn_print(1029))
  pyxtnm2155 = pyxtnm2154
  pyxtnm2156 = XATSDAPP(pyxtnm2155(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2156
  return pyxtnm2156
## endtimp(gs_println_a2(811))
pyxtnm2158 = XATSCAPP("TMapp", [4, pyxtnm1219, pyxtnm1219])
pyxtnm2159 = XATSCAPP("TMapp", [4, pyxtnm2158, pyxtnm1304])
pyxtnm2160 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm2161 = XATSCAPP("TMapp", [4, pyxtnm2159, pyxtnm2160])
pyxtnm2162 = XATSDAPP(term_interp_4894(pyxtnm2161))
pyxtnm2163 = XATSDAPP(pyxtnm2157(XATSSTRN("TMapp(TMapp(TMapp(TMtwo, TMtwo), TMtpl), TMint(10)) = "), pyxtnm2162))
pyxtnm2164 = pyxtnm2163
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8150(line=521,offs=1)--8283(line=527,offs=2)))
## I1VALDCL
pyxtnm2176 = None
## let
pyxtnm2175 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8201(line=525,offs=1)--8234(line=525,offs=34)))
## I1VALDCL
pyxtnm2166 = None
pyxtnm2165 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm2166 = pyxtnm2165
XATS000_patck(True)
## I1VALDCL
pyxtnm2168 = None
pyxtnm2167 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm2168 = pyxtnm2167
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8235(line=526,offs=1)--8281(line=526,offs=47)))
## I1VALDCL
pyxtnm2172 = None
pyxtnm2169 = XATSCAPP("TMapp", [4, pyxtnm2168, pyxtnm2168])
pyxtnm2170 = XATSCAPP("TMapp", [4, pyxtnm2166, pyxtnm2169])
pyxtnm2171 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm2170])
pyxtnm2172 = pyxtnm2171
XATS000_patck(True)
pyxtnm2173 = XATSCAPP("TMapp", [4, pyxtnm2172, pyxtnm2172])
pyxtnm2174 = XATSCAPP("TMlam", [3, XATSSTRN("f"), pyxtnm2173])
pyxtnm2175 = pyxtnm2174
## end-of(let)
pyxtnm2176 = pyxtnm2175
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8328(line=533,offs=1)--8504(line=541,offs=2)))
## I1VALDCL
pyxtnm2192 = None
## let
pyxtnm2191 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8382(line=537,offs=1)--8432(line=538,offs=34)))
## I1VALDCL
pyxtnm2178 = None
pyxtnm2177 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm2178 = pyxtnm2177
XATS000_patck(True)
## I1VALDCL
pyxtnm2180 = None
pyxtnm2179 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm2180 = pyxtnm2179
XATS000_patck(True)
## I1VALDCL
pyxtnm2182 = None
pyxtnm2181 = XATSCAPP("TMvar", [2, XATSSTRN("y")])
pyxtnm2182 = pyxtnm2181
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(8433(line=539,offs=1)--8502(line=540,offs=56)))
## I1VALDCL
pyxtnm2188 = None
pyxtnm2183 = XATSCAPP("TMapp", [4, pyxtnm2180, pyxtnm2180])
pyxtnm2184 = XATSCAPP("TMapp", [4, pyxtnm2178, pyxtnm2183])
pyxtnm2185 = XATSCAPP("TMapp", [4, pyxtnm2184, pyxtnm2182])
pyxtnm2186 = XATSCAPP("TMlam", [3, XATSSTRN("y"), pyxtnm2185])
pyxtnm2187 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm2186])
pyxtnm2188 = pyxtnm2187
XATS000_patck(True)
pyxtnm2189 = XATSCAPP("TMapp", [4, pyxtnm2188, pyxtnm2188])
pyxtnm2190 = XATSCAPP("TMlam", [3, XATSSTRN("f"), pyxtnm2189])
pyxtnm2191 = pyxtnm2190
## end-of(let)
pyxtnm2192 = pyxtnm2191
XATS000_patck(True)
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8551(line=546,offs=1)--8612(line=549,offs=28)))
## I1FUNDCL
def TMlt_8554(arg1, arg2): ## fun
  pyxtnm2193 = arg1
  pyxtnm2194 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8596(line=549,offs=12)--8600(line=549,offs=16))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2208(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2195 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2207 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2197 = None
    pyxtnm2196 = XATSPFLT(pyxtnm2195[0])
    pyxtnm2197 = pyxtnm2196
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2199 = None
    pyxtnm2198 = XATSPFLT(pyxtnm2195[1])
    pyxtnm2199 = pyxtnm2198
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2205(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2200 = arg1
      pyxtnm2201 = arg2
      ## I1CMP:start
      pyxtnm2202 = XATSCAPP("list_nil", [0])
      pyxtnm2203 = XATSCAPP("list_cons", [1, pyxtnm2201, pyxtnm2202])
      pyxtnm2204 = XATSCAPP("list_cons", [1, pyxtnm2200, pyxtnm2203])
      ## I1CMP:return:pyxtnm2204
      return pyxtnm2204
    ## endtimp(list_make_2val(1171))
    pyxtnm2206 = XATSDAPP(pyxtnm2205(pyxtnm2197, pyxtnm2199))
    pyxtnm2207 = pyxtnm2206
    ## end-of(let)
    ## I1CMP:return:pyxtnm2207
    return pyxtnm2207
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2209 = XATSTUP1(XATSTRCD(0), [pyxtnm2193, pyxtnm2194])
  pyxtnm2210 = XATSDAPP(pyxtnm2208(pyxtnm2209))
  pyxtnm2211 = XATSCAPP("TMopr", [5, XATSSTRN("<"), pyxtnm2210])
  ## I1CMP:return:pyxtnm2211
  return pyxtnm2211
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8613(line=550,offs=1)--8674(line=553,offs=28)))
## I1FUNDCL
def TMgt_8616(arg1, arg2): ## fun
  pyxtnm2212 = arg1
  pyxtnm2213 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8658(line=553,offs=12)--8662(line=553,offs=16))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2227(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2214 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2226 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2216 = None
    pyxtnm2215 = XATSPFLT(pyxtnm2214[0])
    pyxtnm2216 = pyxtnm2215
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2218 = None
    pyxtnm2217 = XATSPFLT(pyxtnm2214[1])
    pyxtnm2218 = pyxtnm2217
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2224(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2219 = arg1
      pyxtnm2220 = arg2
      ## I1CMP:start
      pyxtnm2221 = XATSCAPP("list_nil", [0])
      pyxtnm2222 = XATSCAPP("list_cons", [1, pyxtnm2220, pyxtnm2221])
      pyxtnm2223 = XATSCAPP("list_cons", [1, pyxtnm2219, pyxtnm2222])
      ## I1CMP:return:pyxtnm2223
      return pyxtnm2223
    ## endtimp(list_make_2val(1171))
    pyxtnm2225 = XATSDAPP(pyxtnm2224(pyxtnm2216, pyxtnm2218))
    pyxtnm2226 = pyxtnm2225
    ## end-of(let)
    ## I1CMP:return:pyxtnm2226
    return pyxtnm2226
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2228 = XATSTUP1(XATSTRCD(0), [pyxtnm2212, pyxtnm2213])
  pyxtnm2229 = XATSDAPP(pyxtnm2227(pyxtnm2228))
  pyxtnm2230 = XATSCAPP("TMopr", [5, XATSSTRN(">"), pyxtnm2229])
  ## I1CMP:return:pyxtnm2230
  return pyxtnm2230
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8675(line=554,offs=1)--8736(line=557,offs=28)))
## I1FUNDCL
def TMeq_8678(arg1, arg2): ## fun
  pyxtnm2231 = arg1
  pyxtnm2232 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8720(line=557,offs=12)--8724(line=557,offs=16))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2246(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2233 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2245 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2235 = None
    pyxtnm2234 = XATSPFLT(pyxtnm2233[0])
    pyxtnm2235 = pyxtnm2234
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2237 = None
    pyxtnm2236 = XATSPFLT(pyxtnm2233[1])
    pyxtnm2237 = pyxtnm2236
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2243(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2238 = arg1
      pyxtnm2239 = arg2
      ## I1CMP:start
      pyxtnm2240 = XATSCAPP("list_nil", [0])
      pyxtnm2241 = XATSCAPP("list_cons", [1, pyxtnm2239, pyxtnm2240])
      pyxtnm2242 = XATSCAPP("list_cons", [1, pyxtnm2238, pyxtnm2241])
      ## I1CMP:return:pyxtnm2242
      return pyxtnm2242
    ## endtimp(list_make_2val(1171))
    pyxtnm2244 = XATSDAPP(pyxtnm2243(pyxtnm2235, pyxtnm2237))
    pyxtnm2245 = pyxtnm2244
    ## end-of(let)
    ## I1CMP:return:pyxtnm2245
    return pyxtnm2245
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2247 = XATSTUP1(XATSTRCD(0), [pyxtnm2231, pyxtnm2232])
  pyxtnm2248 = XATSDAPP(pyxtnm2246(pyxtnm2247))
  pyxtnm2249 = XATSCAPP("TMopr", [5, XATSSTRN("="), pyxtnm2248])
  ## I1CMP:return:pyxtnm2249
  return pyxtnm2249
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8740(line=559,offs=1)--8803(line=562,offs=29)))
## I1FUNDCL
def TMlte_8743(arg1, arg2): ## fun
  pyxtnm2250 = arg1
  pyxtnm2251 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8787(line=562,offs=13)--8791(line=562,offs=17))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2265(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2252 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2264 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2254 = None
    pyxtnm2253 = XATSPFLT(pyxtnm2252[0])
    pyxtnm2254 = pyxtnm2253
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2256 = None
    pyxtnm2255 = XATSPFLT(pyxtnm2252[1])
    pyxtnm2256 = pyxtnm2255
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2262(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2257 = arg1
      pyxtnm2258 = arg2
      ## I1CMP:start
      pyxtnm2259 = XATSCAPP("list_nil", [0])
      pyxtnm2260 = XATSCAPP("list_cons", [1, pyxtnm2258, pyxtnm2259])
      pyxtnm2261 = XATSCAPP("list_cons", [1, pyxtnm2257, pyxtnm2260])
      ## I1CMP:return:pyxtnm2261
      return pyxtnm2261
    ## endtimp(list_make_2val(1171))
    pyxtnm2263 = XATSDAPP(pyxtnm2262(pyxtnm2254, pyxtnm2256))
    pyxtnm2264 = pyxtnm2263
    ## end-of(let)
    ## I1CMP:return:pyxtnm2264
    return pyxtnm2264
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2266 = XATSTUP1(XATSTRCD(0), [pyxtnm2250, pyxtnm2251])
  pyxtnm2267 = XATSDAPP(pyxtnm2265(pyxtnm2266))
  pyxtnm2268 = XATSCAPP("TMopr", [5, XATSSTRN("<="), pyxtnm2267])
  ## I1CMP:return:pyxtnm2268
  return pyxtnm2268
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8804(line=563,offs=1)--8867(line=566,offs=29)))
## I1FUNDCL
def TMgte_8807(arg1, arg2): ## fun
  pyxtnm2269 = arg1
  pyxtnm2270 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8851(line=566,offs=13)--8855(line=566,offs=17))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2284(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2271 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2283 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2273 = None
    pyxtnm2272 = XATSPFLT(pyxtnm2271[0])
    pyxtnm2273 = pyxtnm2272
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2275 = None
    pyxtnm2274 = XATSPFLT(pyxtnm2271[1])
    pyxtnm2275 = pyxtnm2274
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2281(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2276 = arg1
      pyxtnm2277 = arg2
      ## I1CMP:start
      pyxtnm2278 = XATSCAPP("list_nil", [0])
      pyxtnm2279 = XATSCAPP("list_cons", [1, pyxtnm2277, pyxtnm2278])
      pyxtnm2280 = XATSCAPP("list_cons", [1, pyxtnm2276, pyxtnm2279])
      ## I1CMP:return:pyxtnm2280
      return pyxtnm2280
    ## endtimp(list_make_2val(1171))
    pyxtnm2282 = XATSDAPP(pyxtnm2281(pyxtnm2273, pyxtnm2275))
    pyxtnm2283 = pyxtnm2282
    ## end-of(let)
    ## I1CMP:return:pyxtnm2283
    return pyxtnm2283
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2285 = XATSTUP1(XATSTRCD(0), [pyxtnm2269, pyxtnm2270])
  pyxtnm2286 = XATSDAPP(pyxtnm2284(pyxtnm2285))
  pyxtnm2287 = XATSCAPP("TMopr", [5, XATSSTRN(">="), pyxtnm2286])
  ## I1CMP:return:pyxtnm2287
  return pyxtnm2287
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8868(line=567,offs=1)--8931(line=570,offs=29)))
## I1FUNDCL
def TMneq_8871(arg1, arg2): ## fun
  pyxtnm2288 = arg1
  pyxtnm2289 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8915(line=570,offs=13)--8919(line=570,offs=17))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2303(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2290 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2302 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2292 = None
    pyxtnm2291 = XATSPFLT(pyxtnm2290[0])
    pyxtnm2292 = pyxtnm2291
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2294 = None
    pyxtnm2293 = XATSPFLT(pyxtnm2290[1])
    pyxtnm2294 = pyxtnm2293
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2300(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2295 = arg1
      pyxtnm2296 = arg2
      ## I1CMP:start
      pyxtnm2297 = XATSCAPP("list_nil", [0])
      pyxtnm2298 = XATSCAPP("list_cons", [1, pyxtnm2296, pyxtnm2297])
      pyxtnm2299 = XATSCAPP("list_cons", [1, pyxtnm2295, pyxtnm2298])
      ## I1CMP:return:pyxtnm2299
      return pyxtnm2299
    ## endtimp(list_make_2val(1171))
    pyxtnm2301 = XATSDAPP(pyxtnm2300(pyxtnm2292, pyxtnm2294))
    pyxtnm2302 = pyxtnm2301
    ## end-of(let)
    ## I1CMP:return:pyxtnm2302
    return pyxtnm2302
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2304 = XATSTUP1(XATSTRCD(0), [pyxtnm2288, pyxtnm2289])
  pyxtnm2305 = XATSDAPP(pyxtnm2303(pyxtnm2304))
  pyxtnm2306 = XATSCAPP("TMopr", [5, XATSSTRN("!="), pyxtnm2305])
  ## I1CMP:return:pyxtnm2306
  return pyxtnm2306
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(8932(line=571,offs=1)--8996(line=574,offs=30)))
## I1FUNDCL
def TMcmp_8935(arg1, arg2): ## fun
  pyxtnm2307 = arg1
  pyxtnm2308 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(8980(line=574,offs=14)--8984(line=574,offs=18))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2322(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2309 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2321 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2311 = None
    pyxtnm2310 = XATSPFLT(pyxtnm2309[0])
    pyxtnm2311 = pyxtnm2310
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2313 = None
    pyxtnm2312 = XATSPFLT(pyxtnm2309[1])
    pyxtnm2313 = pyxtnm2312
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2319(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2314 = arg1
      pyxtnm2315 = arg2
      ## I1CMP:start
      pyxtnm2316 = XATSCAPP("list_nil", [0])
      pyxtnm2317 = XATSCAPP("list_cons", [1, pyxtnm2315, pyxtnm2316])
      pyxtnm2318 = XATSCAPP("list_cons", [1, pyxtnm2314, pyxtnm2317])
      ## I1CMP:return:pyxtnm2318
      return pyxtnm2318
    ## endtimp(list_make_2val(1171))
    pyxtnm2320 = XATSDAPP(pyxtnm2319(pyxtnm2311, pyxtnm2313))
    pyxtnm2321 = pyxtnm2320
    ## end-of(let)
    ## I1CMP:return:pyxtnm2321
    return pyxtnm2321
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2323 = XATSTUP1(XATSTRCD(0), [pyxtnm2307, pyxtnm2308])
  pyxtnm2324 = XATSDAPP(pyxtnm2322(pyxtnm2323))
  pyxtnm2325 = XATSCAPP("TMopr", [5, XATSSTRN("cmp"), pyxtnm2324])
  ## I1CMP:return:pyxtnm2325
  return pyxtnm2325
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(9000(line=576,offs=1)--9064(line=579,offs=29)))
## I1FUNDCL
def TMconj_9003(arg1, arg2): ## fun
  pyxtnm2326 = arg1
  pyxtnm2327 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(9048(line=579,offs=13)--9052(line=579,offs=17))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2341(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2328 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2340 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2330 = None
    pyxtnm2329 = XATSPFLT(pyxtnm2328[0])
    pyxtnm2330 = pyxtnm2329
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2332 = None
    pyxtnm2331 = XATSPFLT(pyxtnm2328[1])
    pyxtnm2332 = pyxtnm2331
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2338(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2333 = arg1
      pyxtnm2334 = arg2
      ## I1CMP:start
      pyxtnm2335 = XATSCAPP("list_nil", [0])
      pyxtnm2336 = XATSCAPP("list_cons", [1, pyxtnm2334, pyxtnm2335])
      pyxtnm2337 = XATSCAPP("list_cons", [1, pyxtnm2333, pyxtnm2336])
      ## I1CMP:return:pyxtnm2337
      return pyxtnm2337
    ## endtimp(list_make_2val(1171))
    pyxtnm2339 = XATSDAPP(pyxtnm2338(pyxtnm2330, pyxtnm2332))
    pyxtnm2340 = pyxtnm2339
    ## end-of(let)
    ## I1CMP:return:pyxtnm2340
    return pyxtnm2340
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2342 = XATSTUP1(XATSTRCD(0), [pyxtnm2326, pyxtnm2327])
  pyxtnm2343 = XATSDAPP(pyxtnm2341(pyxtnm2342))
  pyxtnm2344 = XATSCAPP("TMopr", [5, XATSSTRN("&&"), pyxtnm2343])
  ## I1CMP:return:pyxtnm2344
  return pyxtnm2344
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(9065(line=580,offs=1)--9129(line=583,offs=29)))
## I1FUNDCL
def TMdisj_9068(arg1, arg2): ## fun
  pyxtnm2345 = arg1
  pyxtnm2346 = arg2
  ## I1CMP:start
  ## LCSRCsome1(lambda1.dats)@(9113(line=583,offs=13)--9117(line=583,offs=17))
  ## I0Etapq(I0Ecst(list_make_t0up2(1191)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(5525(line=349,offs=1)--5540(line=349,offs=16))));$list(T2JAG($list(T2Pcst(term)))))
  ## T1IMPallx(list_make_t0up2(1191), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7931(line=538,offs=1)--8043(line=545,offs=32)))
  ## T1IMPallx(list_make_t0up2(1191)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7261],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_t0up2(1191);$list(@(x0[3266],T2Pvar(x0[7261])))))))
  def pyxtnm2360(arg1): ## timp: list_make_t0up2(1191)
    pyxtnm2347 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2359 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(8014(line=545,offs=3)--8041(line=545,offs=30)))
    ## I1VALDCL
    pyxtnm2349 = None
    pyxtnm2348 = XATSPFLT(pyxtnm2347[0])
    pyxtnm2349 = pyxtnm2348
    XATS000_patck(True)
    ## I1VALDCL
    pyxtnm2351 = None
    pyxtnm2350 = XATSPFLT(pyxtnm2347[1])
    pyxtnm2351 = pyxtnm2350
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(7976(line=542,offs=3)--7990(line=542,offs=17))
    ## I0Etapq(I0Ecst(list_make_2val(1171)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/list000.sats)@(2519(line=130,offs=1)--2533(line=130,offs=15))));$list(T2JAG($list(T2Pvar(x0[7261])))))
    ## T1IMPallx(list_make_2val(1171), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/list000.dats)@(6517(line=436,offs=1)--6605(line=441,offs=30)))
    ## T1IMPallx(list_make_2val(1171)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[7251],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(list_make_2val(1171);$list(@(a[3223],T2Pvar(x0[7251])))))))
    def pyxtnm2357(arg1, arg2): ## timp: list_make_2val(1171)
      pyxtnm2352 = arg1
      pyxtnm2353 = arg2
      ## I1CMP:start
      pyxtnm2354 = XATSCAPP("list_nil", [0])
      pyxtnm2355 = XATSCAPP("list_cons", [1, pyxtnm2353, pyxtnm2354])
      pyxtnm2356 = XATSCAPP("list_cons", [1, pyxtnm2352, pyxtnm2355])
      ## I1CMP:return:pyxtnm2356
      return pyxtnm2356
    ## endtimp(list_make_2val(1171))
    pyxtnm2358 = XATSDAPP(pyxtnm2357(pyxtnm2349, pyxtnm2351))
    pyxtnm2359 = pyxtnm2358
    ## end-of(let)
    ## I1CMP:return:pyxtnm2359
    return pyxtnm2359
  ## endtimp(list_make_t0up2(1191))
  pyxtnm2361 = XATSTUP1(XATSTRCD(0), [pyxtnm2345, pyxtnm2346])
  pyxtnm2362 = XATSDAPP(pyxtnm2360(pyxtnm2361))
  pyxtnm2363 = XATSCAPP("TMopr", [5, XATSSTRN("||"), pyxtnm2362])
  ## I1CMP:return:pyxtnm2363
  return pyxtnm2363
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9176(line=588,offs=1)--9364(line=603,offs=2)))
## I1VALDCL
pyxtnm2381 = None
## let
pyxtnm2380 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9212(line=593,offs=1)--9245(line=594,offs=26)))
## I1VALDCL
pyxtnm2365 = None
pyxtnm2364 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm2365 = pyxtnm2364
XATS000_patck(True)
## I1VALDCL
pyxtnm2367 = None
pyxtnm2366 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm2367 = pyxtnm2366
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9249(line=596,offs=1)--9359(line=601,offs=53)))
## I1VALDCL
pyxtnm2378 = None
pyxtnm2368 = XATSCAPP("TMint", [0, XATSINT1(0)])
pyxtnm2369 = XATSDAPP(TMlte_8743(pyxtnm2367, pyxtnm2368))
pyxtnm2370 = XATSCAPP("TMint", [0, XATSINT1(1)])
pyxtnm2371 = XATSCAPP("TMint", [0, XATSINT1(1)])
pyxtnm2372 = XATSDAPP(pyxtnm1137(pyxtnm2367, pyxtnm2371))
pyxtnm2373 = XATSCAPP("TMapp", [4, pyxtnm2365, pyxtnm2372])
pyxtnm2374 = XATSDAPP(pyxtnm1158(pyxtnm2367, pyxtnm2373))
pyxtnm2375 = XATSCAPP("TMif0", [6, pyxtnm2369, pyxtnm2370, pyxtnm2374])
pyxtnm2376 = XATSCAPP("TMlam", [3, XATSSTRN("x"), pyxtnm2375])
pyxtnm2377 = XATSCAPP("TMlam", [3, XATSSTRN("f"), pyxtnm2376])
pyxtnm2378 = pyxtnm2377
XATS000_patck(True)
pyxtnm2379 = XATSCAPP("TMapp", [4, pyxtnm2176, pyxtnm2378])
pyxtnm2380 = pyxtnm2379
## end-of(let)
pyxtnm2381 = pyxtnm2380
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9397(line=605,offs=1)--9483(line=606,offs=69)))
## I1VALDCL
pyxtnm2420 = None
## LCSRCsome1(lambda1.dats)@(9406(line=605,offs=10)--9414(line=605,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2415(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2382 = arg1
  pyxtnm2383 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2406(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2384 = arg1
    pyxtnm2385 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2405 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2389 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2387(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2386 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2386
      return pyxtnm2386
    ## endtimp(gs_print$beg(793))
    pyxtnm2388 = XATSDAPP(pyxtnm2387())
    pyxtnm2389 = pyxtnm2388
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2395 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2394(arg1): ## timp: strn_print(1029)
      pyxtnm2390 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2393 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2391);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2391))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2392 = XATSDAPP(XATS2PY_strn_print(pyxtnm2390))
      pyxtnm2393 = pyxtnm2392
      ## end-of(let)
      ## I1CMP:return:pyxtnm2393
      return pyxtnm2393
    ## endtimp(strn_print(1029))
    pyxtnm2395 = pyxtnm2394
    pyxtnm2396 = XATSDAPP(pyxtnm2395(pyxtnm2384))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2398(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2397 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2397
      return pyxtnm2397
    ## endtimp(gs_print$sep(794))
    pyxtnm2399 = XATSDAPP(pyxtnm2398())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2400 = None
    pyxtnm2400 = pyxtnm879
    pyxtnm2401 = XATSDAPP(pyxtnm2400(pyxtnm2385))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2403(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2402 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2402
      return pyxtnm2402
    ## endtimp(gs_print$end(795))
    pyxtnm2404 = XATSDAPP(pyxtnm2403())
    pyxtnm2405 = pyxtnm2404
    ## end-of(let)
    ## I1CMP:return:pyxtnm2405
    return pyxtnm2405
  ## endtimp(gs_print_a2(798))
  pyxtnm2407 = XATSDAPP(pyxtnm2406(pyxtnm2382, pyxtnm2383))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2413 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2412(arg1): ## timp: strn_print(1029)
    pyxtnm2408 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2411 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2409);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2409))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2410 = XATSDAPP(XATS2PY_strn_print(pyxtnm2408))
    pyxtnm2411 = pyxtnm2410
    ## end-of(let)
    ## I1CMP:return:pyxtnm2411
    return pyxtnm2411
  ## endtimp(strn_print(1029))
  pyxtnm2413 = pyxtnm2412
  pyxtnm2414 = XATSDAPP(pyxtnm2413(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2414
  return pyxtnm2414
## endtimp(gs_println_a2(811))
pyxtnm2416 = XATSCAPP("TMint", [0, XATSINT1(5)])
pyxtnm2417 = XATSCAPP("TMapp", [4, pyxtnm2381, pyxtnm2416])
pyxtnm2418 = XATSDAPP(term_interp_4894(pyxtnm2417))
pyxtnm2419 = XATSDAPP(pyxtnm2415(XATSSTRN("TMapp(TMfact, TMint(5)) = "), pyxtnm2418))
pyxtnm2420 = pyxtnm2419
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9530(line=611,offs=1)--9707(line=625,offs=2)))
## I1VALDCL
pyxtnm2437 = None
## let
pyxtnm2436 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9672(line=624,offs=1)--9705(line=624,offs=34)))
## I1VALDCL
pyxtnm2422 = None
pyxtnm2421 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm2422 = pyxtnm2421
XATS000_patck(True)
## I1VALDCL
pyxtnm2424 = None
pyxtnm2423 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm2424 = pyxtnm2423
XATS000_patck(True)
pyxtnm2425 = XATSCAPP("TMint", [0, XATSINT1(1)])
pyxtnm2426 = XATSDAPP(TMlte_8743(pyxtnm2424, pyxtnm2425))
pyxtnm2427 = XATSCAPP("TMint", [0, XATSINT1(1)])
pyxtnm2428 = XATSDAPP(pyxtnm1137(pyxtnm2424, pyxtnm2427))
pyxtnm2429 = XATSCAPP("TMapp", [4, pyxtnm2422, pyxtnm2428])
pyxtnm2430 = XATSCAPP("TMint", [0, XATSINT1(2)])
pyxtnm2431 = XATSDAPP(pyxtnm1137(pyxtnm2424, pyxtnm2430))
pyxtnm2432 = XATSCAPP("TMapp", [4, pyxtnm2422, pyxtnm2431])
pyxtnm2433 = XATSDAPP(pyxtnm1116(pyxtnm2429, pyxtnm2432))
pyxtnm2434 = XATSCAPP("TMif0", [6, pyxtnm2426, pyxtnm2424, pyxtnm2433])
pyxtnm2435 = XATSCAPP("TMfix", [7, XATSSTRN("f"), XATSSTRN("x"), pyxtnm2434])
pyxtnm2436 = pyxtnm2435
## end-of(let)
pyxtnm2437 = pyxtnm2436
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9711(line=627,offs=1)--9799(line=628,offs=71)))
## I1VALDCL
pyxtnm2476 = None
## LCSRCsome1(lambda1.dats)@(9720(line=627,offs=10)--9728(line=627,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2471(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2438 = arg1
  pyxtnm2439 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2462(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2440 = arg1
    pyxtnm2441 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2461 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2445 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2443(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2442 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2442
      return pyxtnm2442
    ## endtimp(gs_print$beg(793))
    pyxtnm2444 = XATSDAPP(pyxtnm2443())
    pyxtnm2445 = pyxtnm2444
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2451 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2450(arg1): ## timp: strn_print(1029)
      pyxtnm2446 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2449 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2447);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2447))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2448 = XATSDAPP(XATS2PY_strn_print(pyxtnm2446))
      pyxtnm2449 = pyxtnm2448
      ## end-of(let)
      ## I1CMP:return:pyxtnm2449
      return pyxtnm2449
    ## endtimp(strn_print(1029))
    pyxtnm2451 = pyxtnm2450
    pyxtnm2452 = XATSDAPP(pyxtnm2451(pyxtnm2440))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2454(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2453 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2453
      return pyxtnm2453
    ## endtimp(gs_print$sep(794))
    pyxtnm2455 = XATSDAPP(pyxtnm2454())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2456 = None
    pyxtnm2456 = pyxtnm879
    pyxtnm2457 = XATSDAPP(pyxtnm2456(pyxtnm2441))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2459(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2458 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2458
      return pyxtnm2458
    ## endtimp(gs_print$end(795))
    pyxtnm2460 = XATSDAPP(pyxtnm2459())
    pyxtnm2461 = pyxtnm2460
    ## end-of(let)
    ## I1CMP:return:pyxtnm2461
    return pyxtnm2461
  ## endtimp(gs_print_a2(798))
  pyxtnm2463 = XATSDAPP(pyxtnm2462(pyxtnm2438, pyxtnm2439))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2469 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2468(arg1): ## timp: strn_print(1029)
    pyxtnm2464 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2467 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2465);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2465))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2466 = XATSDAPP(XATS2PY_strn_print(pyxtnm2464))
    pyxtnm2467 = pyxtnm2466
    ## end-of(let)
    ## I1CMP:return:pyxtnm2467
    return pyxtnm2467
  ## endtimp(strn_print(1029))
  pyxtnm2469 = pyxtnm2468
  pyxtnm2470 = XATSDAPP(pyxtnm2469(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2470
  return pyxtnm2470
## endtimp(gs_println_a2(811))
pyxtnm2472 = XATSCAPP("TMint", [0, XATSINT1(10)])
pyxtnm2473 = XATSCAPP("TMapp", [4, pyxtnm2437, pyxtnm2472])
pyxtnm2474 = XATSDAPP(term_interp_4894(pyxtnm2473))
pyxtnm2475 = XATSDAPP(pyxtnm2471(XATSSTRN("TMapp(TMfibo, TMint(10)) = "), pyxtnm2474))
pyxtnm2476 = pyxtnm2475
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9846(line=633,offs=1)--10001(line=643,offs=2)))
## I1VALDCL
pyxtnm2491 = None
## let
pyxtnm2490 = None
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(9966(line=642,offs=1)--9999(line=642,offs=34)))
## I1VALDCL
pyxtnm2478 = None
pyxtnm2477 = XATSCAPP("TMvar", [2, XATSSTRN("f")])
pyxtnm2478 = pyxtnm2477
XATS000_patck(True)
## I1VALDCL
pyxtnm2480 = None
pyxtnm2479 = XATSCAPP("TMvar", [2, XATSSTRN("x")])
pyxtnm2480 = pyxtnm2479
XATS000_patck(True)
pyxtnm2481 = XATSCAPP("TMint", [0, XATSINT1(0)])
pyxtnm2482 = XATSDAPP(TMlte_8743(pyxtnm2480, pyxtnm2481))
pyxtnm2483 = XATSCAPP("TMint", [0, XATSINT1(1)])
pyxtnm2484 = XATSCAPP("TMint", [0, XATSINT1(1)])
pyxtnm2485 = XATSDAPP(pyxtnm1137(pyxtnm2480, pyxtnm2484))
pyxtnm2486 = XATSCAPP("TMapp", [4, pyxtnm2478, pyxtnm2485])
pyxtnm2487 = XATSDAPP(pyxtnm1158(pyxtnm2480, pyxtnm2486))
pyxtnm2488 = XATSCAPP("TMif0", [6, pyxtnm2482, pyxtnm2483, pyxtnm2487])
pyxtnm2489 = XATSCAPP("TMfix", [7, XATSSTRN("f"), XATSSTRN("x"), pyxtnm2488])
pyxtnm2490 = pyxtnm2489
## end-of(let)
pyxtnm2491 = pyxtnm2490
XATS000_patck(True)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(10005(line=645,offs=1)--10093(line=646,offs=71)))
## I1VALDCL
pyxtnm2530 = None
## LCSRCsome1(lambda1.dats)@(10014(line=645,offs=10)--10022(line=645,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm2525(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm2492 = arg1
  pyxtnm2493 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(term)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm2516(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm2494 = arg1
    pyxtnm2495 = arg2
    ## I1CMP:start
    ## let
    pyxtnm2515 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm2499 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm2497(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm2496 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2496
      return pyxtnm2496
    ## endtimp(gs_print$beg(793))
    pyxtnm2498 = XATSDAPP(pyxtnm2497())
    pyxtnm2499 = pyxtnm2498
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm2505 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm2504(arg1): ## timp: strn_print(1029)
      pyxtnm2500 = arg1
      ## I1CMP:start
      ## let
      pyxtnm2503 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2501);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2501))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm2502 = XATSDAPP(XATS2PY_strn_print(pyxtnm2500))
      pyxtnm2503 = pyxtnm2502
      ## end-of(let)
      ## I1CMP:return:pyxtnm2503
      return pyxtnm2503
    ## endtimp(strn_print(1029))
    pyxtnm2505 = pyxtnm2504
    pyxtnm2506 = XATSDAPP(pyxtnm2505(pyxtnm2494))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm2508(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm2507 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2507
      return pyxtnm2507
    ## endtimp(gs_print$sep(794))
    pyxtnm2509 = XATSDAPP(pyxtnm2508())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
    pyxtnm2510 = None
    pyxtnm2510 = pyxtnm879
    pyxtnm2511 = XATSDAPP(pyxtnm2510(pyxtnm2495))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm2513(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm2512 = XATSTUP0([])
      ## I1CMP:return:pyxtnm2512
      return pyxtnm2512
    ## endtimp(gs_print$end(795))
    pyxtnm2514 = XATSDAPP(pyxtnm2513())
    pyxtnm2515 = pyxtnm2514
    ## end-of(let)
    ## I1CMP:return:pyxtnm2515
    return pyxtnm2515
  ## endtimp(gs_print_a2(798))
  pyxtnm2517 = XATSDAPP(pyxtnm2516(pyxtnm2492, pyxtnm2493))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm2523 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm2522(arg1): ## timp: strn_print(1029)
    pyxtnm2518 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2521 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2519);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2519))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm2520 = XATSDAPP(XATS2PY_strn_print(pyxtnm2518))
    pyxtnm2521 = pyxtnm2520
    ## end-of(let)
    ## I1CMP:return:pyxtnm2521
    return pyxtnm2521
  ## endtimp(strn_print(1029))
  pyxtnm2523 = pyxtnm2522
  pyxtnm2524 = XATSDAPP(pyxtnm2523(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm2524
  return pyxtnm2524
## endtimp(gs_println_a2(811))
pyxtnm2526 = XATSCAPP("TMint", [0, XATSINT1(5)])
pyxtnm2527 = XATSCAPP("TMapp", [4, pyxtnm2491, pyxtnm2526])
pyxtnm2528 = XATSDAPP(term_interp_4894(pyxtnm2527))
pyxtnm2529 = XATSDAPP(pyxtnm2525(XATSSTRN("TMapp(TMfact2, TMint(5)) = "), pyxtnm2528))
pyxtnm2530 = pyxtnm2529
XATS000_patck(True)
## LCSRCsome1(lambda1.dats)@(10140(line=651,offs=1)--10312(line=664,offs=30))
## I1Di0dcl(I0Dd3ecl(D3Cd2ecl(D2Cdatatype(D1Cdatatype(T_DATATYPE(0);$list(D1TYPnode(T_IDALP(tval);$list();$optn();$list(D1TCNnode($list();T_IDALP(TVint);$list();$optn(S1Eid0(sint))),D1TCNnode($list();T_IDALP(TVbtf);$list();$optn(S1Eid0(bool))),D1TCNnode($list();T_IDALP(TVclo);$list();$optn(S1El1st($list(S1Eid0(term),S1Eid0(xenv))))))),D1TYPnode(T_IDALP(xenv);$list();$optn();$list(D1TCNnode($list();T_IDALP(EVnil);$list();$optn(S1El1st($list()))),D1TCNnode($list();T_IDALP(EVcons);$list();$optn(S1El1st($list(S1Eid0(tvar),S1Eid0(tval),S1Eid0(xenv))))))));WD1CSnone());$list(tval,xenv)))))
## I1Dextern(LCSRCsome1(lambda1.dats)@(10359(line=669,offs=1)--10401(line=671,offs=29)))
## I1Dfundclst(T_FUN(FNKfn1);$list(T2QAG($list()));$list(tval_print(2656));$list(I1FUNDCL(tval_print(5358);$list(FJARGdarg($list(I1BNDcons(I1TNM(2531);I0Pvar(tval(5359));$list(@(tval(5359),I1Vtnm(I1TNM(2531))))))));TEQI1CMPnone())))
## I1Dextern(LCSRCsome1(lambda1.dats)@(10402(line=672,offs=1)--10444(line=674,offs=29)))
## I1Dfundclst(T_FUN(FNKfn1);$list(T2QAG($list()));$list(evnx_print(2657));$list(I1FUNDCL(evnx_print(5360);$list(FJARGdarg($list(I1BNDcons(I1TNM(2532);I0Pvar(xenv(5361));$list(@(xenv(5361),I1Vtnm(I1TNM(2532))))))));TEQI1CMPnone())))
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(10448(line=676,offs=1)--10755(line=701,offs=2)))
## I1Dimplmnt0(DIMPLone2(tval_print(2656);$list())):timp
## I1Dlocal0(LCSRCsome1(lambda1.dats)@(10819(line=705,offs=1)--10908(line=709,offs=4)))
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(10825(line=706,offs=1)--10856(line=706,offs=32)))
## I1VALDCL
pyxtnm2702 = None
## LCSRCsome1(lambda1.dats)@(10844(line=706,offs=20)--10854(line=706,offs=30))
## I0Etapq(I0Ecst(tval_print(2656)(LCSRCsome1(lambda1.dats)@(10373(line=671,offs=1)--10383(line=671,offs=11))));$list(T2JAG($list())))
## T1IMPallx(tval_print(2656), LCSRCsome1(lambda1.dats)@(10448(line=676,offs=1)--10755(line=701,offs=2)))
## T1IMPallx(tval_print(2656)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(tval_print(2656);$list()))))
def pyxtnm2701(arg1): ## timp: tval_print(2656)
  pyxtnm2545 = arg1
  ## I1CMP:start
  ## let
  pyxtnm2700 = None
  ## I1Dfundclist(LCSRCsome1(lambda1.dats)@(10511(line=683,offs=1)--10753(line=700,offs=35)))
  ## I1FUNDCL
  def auxpr_10514(arg1): ## fun
    pyxtnm2546 = arg1
    ## I1CMP:start
    ## let
    pyxtnm2698 = None
    ## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(10721(line=700,offs=3)--10751(line=700,offs=33)))
    ## I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(tval))))):timp
    pyxtnm2697 = None
    while True: ## do {
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(2547);I0Pdapp(I0Pcon(TVint(41));$list(I0Pvar(int(5365))));$list(@(int(5365),I1Vp1cn(I0Pcon(TVint(41));I1Vtnm(I1TNM(2547));0)))))
      if (XATS000_ctgeq(pyxtnm2546, XATSCTAG("TVint",0))): ## { // gpt
        pyxtnm2547 = pyxtnm2546
        ## LCSRCsome1(lambda1.dats)@(10574(line=690,offs=1)--10580(line=690,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a3(799), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
        ## T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6828],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6829],T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0()))),@(x2[6830],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2396],T2Pvar(x0[6828])),@(x1[2397],T2Pvar(x1[6829])),@(x2[2398],T2Pvar(x2[6830])))))))
        def pyxtnm2586(arg1, arg2, arg3): ## timp: gs_print_a3(799)
          pyxtnm2548 = arg1
          pyxtnm2549 = arg2
          pyxtnm2550 = arg3
          ## I1CMP:start
          ## let
          pyxtnm2585 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
          ## I1VALDCL
          pyxtnm2554 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm2552(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm2551 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2551
            return pyxtnm2551
          ## endtimp(gs_print$beg(793))
          pyxtnm2553 = XATSDAPP(pyxtnm2552())
          pyxtnm2554 = pyxtnm2553
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6828])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2560 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2559(arg1): ## timp: strn_print(1029)
            pyxtnm2555 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2558 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2556);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2556))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2557 = XATSDAPP(XATS2PY_strn_print(pyxtnm2555))
            pyxtnm2558 = pyxtnm2557
            ## end-of(let)
            ## I1CMP:return:pyxtnm2558
            return pyxtnm2558
          ## endtimp(strn_print(1029))
          pyxtnm2560 = pyxtnm2559
          pyxtnm2561 = XATSDAPP(pyxtnm2560(pyxtnm2548))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2563(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2562 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2562
            return pyxtnm2562
          ## endtimp(gs_print$sep(794))
          pyxtnm2564 = XATSDAPP(pyxtnm2563())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6829])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats)@(2286(line=96,offs=1)--2321(line=97,offs=27)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(gint_type);$list(T2Ptext(xats_sint_t;$list()),T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(si)))))))
          pyxtnm2570 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gint000.dats)@(2309(line=97,offs=15)--2319(line=97,offs=25))
          ## I0Etapq(I0Ecst(sint_print(913)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(1506(line=49,offs=1)--1516(line=49,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(sint_print(913), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3560(line=218,offs=1)--3700(line=229,offs=2)))
          ## T1IMPallx(sint_print(913)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_print(913);$list()))))
          def pyxtnm2569(arg1): ## timp: sint_print(913)
            pyxtnm2565 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2568 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3640(line=226,offs=1)--3698(line=228,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_print(2589));$list(I1FUNDCL(XATS2PY_sint_print(4925);$list(FJARGdarg($list(I1BNDcons(I1TNM(2566);I0Pvar(i0(4926));$list(@(i0(4926),I1Vtnm(I1TNM(2566))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_print);G1Nlist($list())))))))
            pyxtnm2567 = XATSDAPP(XATS2PY_sint_print(pyxtnm2565))
            pyxtnm2568 = pyxtnm2567
            ## end-of(let)
            ## I1CMP:return:pyxtnm2568
            return pyxtnm2568
          ## endtimp(sint_print(913))
          pyxtnm2570 = pyxtnm2569
          pyxtnm2571 = XATSDAPP(pyxtnm2570(pyxtnm2549))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2573(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2572 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2572
            return pyxtnm2572
          ## endtimp(gs_print$sep(794))
          pyxtnm2574 = XATSDAPP(pyxtnm2573())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6830])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2580 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2579(arg1): ## timp: strn_print(1029)
            pyxtnm2575 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2578 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2576);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2576))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2577 = XATSDAPP(XATS2PY_strn_print(pyxtnm2575))
            pyxtnm2578 = pyxtnm2577
            ## end-of(let)
            ## I1CMP:return:pyxtnm2578
            return pyxtnm2578
          ## endtimp(strn_print(1029))
          pyxtnm2580 = pyxtnm2579
          pyxtnm2581 = XATSDAPP(pyxtnm2580(pyxtnm2550))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm2583(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm2582 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2582
            return pyxtnm2582
          ## endtimp(gs_print$end(795))
          pyxtnm2584 = XATSDAPP(pyxtnm2583())
          pyxtnm2585 = pyxtnm2584
          ## end-of(let)
          ## I1CMP:return:pyxtnm2585
          return pyxtnm2585
        ## endtimp(gs_print_a3(799))
        pyxtnm2587 = XATSDAPP(pyxtnm2586(XATSSTRN("TVint("), XATSP1CN("TVint", pyxtnm2547[0+1]), XATSSTRN(")")))
        pyxtnm2697 = pyxtnm2587
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(2588);I0Pdapp(I0Pcon(TVbtf(42));$list(I0Pvar(btf(5366))));$list(@(btf(5366),I1Vp1cn(I0Pcon(TVbtf(42));I1Vtnm(I1TNM(2588));0)))))
      if (XATS000_ctgeq(pyxtnm2546, XATSCTAG("TVbtf",1))): ## { // gpt
        pyxtnm2588 = pyxtnm2546
        ## LCSRCsome1(lambda1.dats)@(10616(line=692,offs=1)--10622(line=692,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a3(799)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11856(line=754,offs=1)--11867(line=754,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a3(799), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21354(line=1316,offs=1)--21566(line=1330,offs=4)))
        ## T1IMPallx(gs_print_a3(799)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6828],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6829],T2Papps(T2Pcst(bool_type);$list(T2Pnone0()))),@(x2[6830],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a3(799);$list(@(x0[2396],T2Pvar(x0[6828])),@(x1[2397],T2Pvar(x1[6829])),@(x2[2398],T2Pvar(x2[6830])))))))
        def pyxtnm2637(arg1, arg2, arg3): ## timp: gs_print_a3(799)
          pyxtnm2589 = arg1
          pyxtnm2590 = arg2
          pyxtnm2591 = arg3
          ## I1CMP:start
          ## let
          pyxtnm2636 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21426(line=1324,offs=1)--21449(line=1325,offs=15)))
          ## I1VALDCL
          pyxtnm2595 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21435(line=1325,offs=1)--21447(line=1325,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm2593(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm2592 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2592
            return pyxtnm2592
          ## endtimp(gs_print$beg(793))
          pyxtnm2594 = XATSDAPP(pyxtnm2593())
          pyxtnm2595 = pyxtnm2594
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21462(line=1327,offs=3)--21469(line=1327,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6828])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2601 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2600(arg1): ## timp: strn_print(1029)
            pyxtnm2596 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2599 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2597);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2597))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2598 = XATSDAPP(XATS2PY_strn_print(pyxtnm2596))
            pyxtnm2599 = pyxtnm2598
            ## end-of(let)
            ## I1CMP:return:pyxtnm2599
            return pyxtnm2599
          ## endtimp(strn_print(1029))
          pyxtnm2601 = pyxtnm2600
          pyxtnm2602 = XATSDAPP(pyxtnm2601(pyxtnm2589))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21479(line=1327,offs=20)--21491(line=1327,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2604(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2603 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2603
            return pyxtnm2603
          ## endtimp(gs_print$sep(794))
          pyxtnm2605 = XATSDAPP(pyxtnm2604())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21496(line=1328,offs=3)--21503(line=1328,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6829])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1767(line=64,offs=1)--1804(line=65,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(bool_type);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(bool)))))))
          pyxtnm2621 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1792(line=65,offs=17)--1802(line=65,offs=27))
          ## I0Etapq(I0Ecst(bool_print(861)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/bool000.sats)@(2405(line=107,offs=1)--2415(line=107,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(bool_print(861), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats)@(2485(line=137,offs=1)--2582(line=143,offs=28)))
          ## T1IMPallx(bool_print(861)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(bool_print(861);$list()))))
          def pyxtnm2620(arg1): ## timp: bool_print(861)
            pyxtnm2606 = arg1
            ## I1CMP:start
            pyxtnm2619 = None
            if (pyxtnm2606):
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats)@(2534(line=142,offs=6)--2544(line=142,offs=16))
              ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
              ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
              ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
              def pyxtnm2611(arg1): ## timp: strn_print(1029)
                pyxtnm2607 = arg1
                ## I1CMP:start
                ## let
                pyxtnm2610 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2608);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2608))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                pyxtnm2609 = XATSDAPP(XATS2PY_strn_print(pyxtnm2607))
                pyxtnm2610 = pyxtnm2609
                ## end-of(let)
                ## I1CMP:return:pyxtnm2610
                return pyxtnm2610
              ## endtimp(strn_print(1029))
              pyxtnm2612 = XATSDAPP(pyxtnm2611(XATSSTRN("true")))
              pyxtnm2619 = pyxtnm2612
            else:
              ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/bool000.dats)@(2560(line=143,offs=6)--2570(line=143,offs=16))
              ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
              ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
              ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
              def pyxtnm2617(arg1): ## timp: strn_print(1029)
                pyxtnm2613 = arg1
                ## I1CMP:start
                ## let
                pyxtnm2616 = None
                ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
                ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2614);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2614))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
                pyxtnm2615 = XATSDAPP(XATS2PY_strn_print(pyxtnm2613))
                pyxtnm2616 = pyxtnm2615
                ## end-of(let)
                ## I1CMP:return:pyxtnm2616
                return pyxtnm2616
              ## endtimp(strn_print(1029))
              pyxtnm2618 = XATSDAPP(pyxtnm2617(XATSSTRN("false")))
              pyxtnm2619 = pyxtnm2618
            ## end-of(if)
            ## I1CMP:return:pyxtnm2619
            return pyxtnm2619
          ## endtimp(bool_print(861))
          pyxtnm2621 = pyxtnm2620
          pyxtnm2622 = XATSDAPP(pyxtnm2621(pyxtnm2590))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21513(line=1328,offs=20)--21525(line=1328,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2624(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2623 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2623
            return pyxtnm2623
          ## endtimp(gs_print$sep(794))
          pyxtnm2625 = XATSDAPP(pyxtnm2624())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21530(line=1329,offs=3)--21537(line=1329,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6830])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2631 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2630(arg1): ## timp: strn_print(1029)
            pyxtnm2626 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2629 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2627);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2627))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2628 = XATSDAPP(XATS2PY_strn_print(pyxtnm2626))
            pyxtnm2629 = pyxtnm2628
            ## end-of(let)
            ## I1CMP:return:pyxtnm2629
            return pyxtnm2629
          ## endtimp(strn_print(1029))
          pyxtnm2631 = pyxtnm2630
          pyxtnm2632 = XATSDAPP(pyxtnm2631(pyxtnm2591))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21547(line=1329,offs=20)--21559(line=1329,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm2634(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm2633 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2633
            return pyxtnm2633
          ## endtimp(gs_print$end(795))
          pyxtnm2635 = XATSDAPP(pyxtnm2634())
          pyxtnm2636 = pyxtnm2635
          ## end-of(let)
          ## I1CMP:return:pyxtnm2636
          return pyxtnm2636
        ## endtimp(gs_print_a3(799))
        pyxtnm2638 = XATSDAPP(pyxtnm2637(XATSSTRN("TVbtf("), XATSP1CN("TVbtf", pyxtnm2588[0+1]), XATSSTRN(")")))
        pyxtnm2697 = pyxtnm2638
        break ## cls
      ## } // gpt
      ## } // cls
      ## { // cls
      ## I1GPTpat(I1BNDcons(I1TNM(2639);I0Pdapp(I0Pcon(TVclo(43));$list(I0Pvar(tm1(5367)),I0Pvar(env(5368))));$list(@(tm1(5367),I1Vp1cn(I0Pcon(TVclo(43));I1Vtnm(I1TNM(2639));0)),@(env(5368),I1Vp1cn(I0Pcon(TVclo(43));I1Vtnm(I1TNM(2639));1)))))
      if (XATS000_ctgeq(pyxtnm2546, XATSCTAG("TVclo",2))): ## { // gpt
        pyxtnm2639 = pyxtnm2546
        ## LCSRCsome1(lambda1.dats)@(10666(line=695,offs=1)--10672(line=695,offs=7))
        ## I0Etapq(I0Ecst(gs_print_a5(801)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(12006(line=769,offs=1)--12017(line=769,offs=12))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
        ## T1IMPallx(gs_print_a5(801), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21898(line=1350,offs=1)--22206(line=1368,offs=4)))
        ## T1IMPallx(gs_print_a5(801)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(term))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[6835],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6836],T2Pcst(term)),@(x2[6837],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x3[6838],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x4[6839],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(gs_print_a5(801);$list(@(x0[2403],T2Pvar(x0[6835])),@(x1[2404],T2Pvar(x1[6836])),@(x2[2405],T2Pvar(x2[6837])),@(x3[2406],T2Pvar(x3[6838])),@(x4[2407],T2Pvar(x4[6839])))))))
        def pyxtnm2695(arg1, arg2, arg3, arg4, arg5): ## timp: gs_print_a5(801)
          pyxtnm2640 = arg1
          pyxtnm2641 = arg2
          pyxtnm2642 = arg3
          pyxtnm2643 = arg4
          pyxtnm2644 = arg5
          ## I1CMP:start
          ## let
          pyxtnm2694 = None
          ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21998(line=1360,offs=1)--22021(line=1361,offs=15)))
          ## I1VALDCL
          pyxtnm2648 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22007(line=1361,offs=1)--22019(line=1361,offs=13))
          ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
          ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
          def pyxtnm2646(): ## timp: gs_print$beg(793)
            ## I1CMP:start
            pyxtnm2645 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2645
            return pyxtnm2645
          ## endtimp(gs_print$beg(793))
          pyxtnm2647 = XATSDAPP(pyxtnm2646())
          pyxtnm2648 = pyxtnm2647
          XATS000_patck(True)
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22034(line=1363,offs=3)--22041(line=1363,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6835])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2654 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2653(arg1): ## timp: strn_print(1029)
            pyxtnm2649 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2652 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2650);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2650))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2651 = XATSDAPP(XATS2PY_strn_print(pyxtnm2649))
            pyxtnm2652 = pyxtnm2651
            ## end-of(let)
            ## I1CMP:return:pyxtnm2652
            return pyxtnm2652
          ## endtimp(strn_print(1029))
          pyxtnm2654 = pyxtnm2653
          pyxtnm2655 = XATSDAPP(pyxtnm2654(pyxtnm2640))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22051(line=1363,offs=20)--22063(line=1363,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2657(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2656 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2656
            return pyxtnm2656
          ## endtimp(gs_print$sep(794))
          pyxtnm2658 = XATSDAPP(pyxtnm2657())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22068(line=1364,offs=3)--22075(line=1364,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6836])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(2448(line=163,offs=1)--2485(line=163,offs=38)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(term))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(term)))))))
          pyxtnm2659 = None
          pyxtnm2659 = pyxtnm879
          pyxtnm2660 = XATSDAPP(pyxtnm2659(pyxtnm2641))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22085(line=1364,offs=20)--22097(line=1364,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2662(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2661 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2661
            return pyxtnm2661
          ## endtimp(gs_print$sep(794))
          pyxtnm2663 = XATSDAPP(pyxtnm2662())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22102(line=1365,offs=3)--22109(line=1365,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x2[6837])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2669 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2668(arg1): ## timp: strn_print(1029)
            pyxtnm2664 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2667 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2665);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2665))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2666 = XATSDAPP(XATS2PY_strn_print(pyxtnm2664))
            pyxtnm2667 = pyxtnm2666
            ## end-of(let)
            ## I1CMP:return:pyxtnm2667
            return pyxtnm2667
          ## endtimp(strn_print(1029))
          pyxtnm2669 = pyxtnm2668
          pyxtnm2670 = XATSDAPP(pyxtnm2669(pyxtnm2642))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22119(line=1365,offs=20)--22131(line=1365,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2672(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2671 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2671
            return pyxtnm2671
          ## endtimp(gs_print$sep(794))
          pyxtnm2673 = XATSDAPP(pyxtnm2672())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22136(line=1366,offs=3)--22143(line=1366,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x3[6838])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2679 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2678(arg1): ## timp: strn_print(1029)
            pyxtnm2674 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2677 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2675);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2675))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2676 = XATSDAPP(XATS2PY_strn_print(pyxtnm2674))
            pyxtnm2677 = pyxtnm2676
            ## end-of(let)
            ## I1CMP:return:pyxtnm2677
            return pyxtnm2677
          ## endtimp(strn_print(1029))
          pyxtnm2679 = pyxtnm2678
          pyxtnm2680 = XATSDAPP(pyxtnm2679(pyxtnm2643))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22153(line=1366,offs=20)--22165(line=1366,offs=32))
          ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
          ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
          def pyxtnm2682(): ## timp: gs_print$sep(794)
            ## I1CMP:start
            pyxtnm2681 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2681
            return pyxtnm2681
          ## endtimp(gs_print$sep(794))
          pyxtnm2683 = XATSDAPP(pyxtnm2682())
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22170(line=1367,offs=3)--22177(line=1367,offs=10))
          ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x4[6839])))))
          ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
          ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
          pyxtnm2689 = None
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
          ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
          ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
          ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
          def pyxtnm2688(arg1): ## timp: strn_print(1029)
            pyxtnm2684 = arg1
            ## I1CMP:start
            ## let
            pyxtnm2687 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(2685);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(2685))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
            pyxtnm2686 = XATSDAPP(XATS2PY_strn_print(pyxtnm2684))
            pyxtnm2687 = pyxtnm2686
            ## end-of(let)
            ## I1CMP:return:pyxtnm2687
            return pyxtnm2687
          ## endtimp(strn_print(1029))
          pyxtnm2689 = pyxtnm2688
          pyxtnm2690 = XATSDAPP(pyxtnm2689(pyxtnm2644))
          ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(22187(line=1367,offs=20)--22199(line=1367,offs=32))
          ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
          ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
          def pyxtnm2692(): ## timp: gs_print$end(795)
            ## I1CMP:start
            pyxtnm2691 = XATSTUP0([])
            ## I1CMP:return:pyxtnm2691
            return pyxtnm2691
          ## endtimp(gs_print$end(795))
          pyxtnm2693 = XATSDAPP(pyxtnm2692())
          pyxtnm2694 = pyxtnm2693
          ## end-of(let)
          ## I1CMP:return:pyxtnm2694
          return pyxtnm2694
        ## endtimp(gs_print_a5(801))
        pyxtnm2696 = XATSDAPP(pyxtnm2695(XATSSTRN("TVclo("), XATSP1CN("TVclo", pyxtnm2639[0+1]), XATSSTRN(";"), XATSSTRN("..."), XATSSTRN(")")))
        pyxtnm2697 = pyxtnm2696
        break ## cls
      ## } // gpt
      ## } // cls
      XATS000_cfail()
    ## } while True // end-of(do-cls)
    pyxtnm2698 = pyxtnm2697
    ## end-of(let)
    ## I1CMP:return:pyxtnm2698
    return pyxtnm2698
  pyxtnm2699 = XATSDAPP(auxpr_10514(pyxtnm2545))
  pyxtnm2700 = pyxtnm2699
  ## end-of(let)
  ## I1CMP:return:pyxtnm2700
  return pyxtnm2700
## endtimp(tval_print(2656))
pyxtnm2702 = pyxtnm2701
XATS000_patck(True)
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(10867(line=708,offs=1)--10904(line=708,offs=38)))
## I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(tval))))):timp
## I1Dextern(LCSRCsome1(lambda1.dats)@(10962(line=714,offs=1)--11002(line=716,offs=29)))
## I1Dfundclst(T_FUN(FNKfn1);$list();$list(term_eval00(2659));$list(I1FUNDCL(term_eval00(5370);$list(FJARGdarg($list(I1BNDcons(I1TNM(2703);I0Pvar(tm0(5371));$list(@(tm0(5371),I1Vtnm(I1TNM(2703))))))));TEQI1CMPnone())))
## I1Dextern(LCSRCsome1(lambda1.dats)@(11003(line=717,offs=1)--11054(line=719,offs=40)))
## I1Dfundclst(T_FUN(FNKfn1);$list();$list(term_eval01(2660));$list(I1FUNDCL(term_eval01(5372);$list(FJARGdarg($list(I1BNDcons(I1TNM(2704);I0Pvar(tm0(5373));$list(@(tm0(5373),I1Vtnm(I1TNM(2704))))),I1BNDcons(I1TNM(2705);I0Pvar(env(5374));$list(@(env(5374),I1Vtnm(I1TNM(2705))))))));TEQI1CMPnone())))
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(11058(line=721,offs=1)--11111(line=722,offs=45)))
def term_eval00_10973(arg1): ## impl
  pyxtnm2706 = arg1
  ## I1CMP:start
  pyxtnm2707 = XATSCAPP("EVnil", [0])
  pyxtnm2708 = XATSDAPP(term_eval01_11014(pyxtnm2706, pyxtnm2707))
  ## I1CMP:return:pyxtnm2708
  return pyxtnm2708
## endfun(impl)
## I1Dfundclist(LCSRCsome1(lambda1.dats)@(11158(line=727,offs=1)--11363(line=744,offs=2)))
## I1FUNDCL
def xenv_search_11161(arg1, arg2): ## fun
  pyxtnm2709 = arg1
  pyxtnm2710 = arg2
  ## I1CMP:start
  pyxtnm2739 = None
  while True: ## do {
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2711);I0Pdapp(I0Pcon(EVnil(44));$list());$list()))
    if (XATS000_ctgeq(pyxtnm2709, XATSCTAG("EVnil",0))): ## { // gpt
      pyxtnm2711 = pyxtnm2709
      pyxtnm2712 = XATSCAPP("optn_vt_nil", [0])
      pyxtnm2739 = pyxtnm2712
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2713);I0Pdapp(I0Pcon(EVcons(45));$list(I0Pvar(x01(5379)),I0Pvar(v01(5380)),I0Pvar(env(5381))));$list(@(x01(5379),I1Vp1cn(I0Pcon(EVcons(45));I1Vtnm(I1TNM(2713));0)),@(v01(5380),I1Vp1cn(I0Pcon(EVcons(45));I1Vtnm(I1TNM(2713));1)),@(env(5381),I1Vp1cn(I0Pcon(EVcons(45));I1Vtnm(I1TNM(2713));2)))))
    if (XATS000_ctgeq(pyxtnm2709, XATSCTAG("EVcons",1))): ## { // gpt
      pyxtnm2713 = pyxtnm2709
      ## LCSRCsome1(lambda1.dats)@(11298(line=740,offs=8)--11299(line=740,offs=9))
      ## I0Etapq(I0Ecst(strn_eq(1024)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(1883(line=77,offs=1)--1890(line=77,offs=8))));$list(T2JAG($list())))
      ## T1IMPallx(strn_eq(1024), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1665(line=57,offs=1)--1696(line=58,offs=23)))
      ## T1IMPallx(strn_eq(1024)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_eq(1024);$list()))))
      pyxtnm2734 = None
      ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1686(line=58,offs=13)--1690(line=58,offs=17))
      ## I0Etapq(I0Ecst(g_eq(226)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1486(line=50,offs=1)--1490(line=50,offs=5))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
      ## T1IMPallx(g_eq(226), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1922(line=85,offs=1)--1980(line=89,offs=23)))
      ## T1IMPallx(g_eq(226)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list(@(x0[5765],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))));I1Dimplmnt0(DIMPLone2(g_eq(226);$list(@(a[718],T2Pvar(x0[5765])))))))
      def pyxtnm2733(arg1, arg2): ## timp: g_eq(226)
        pyxtnm2714 = arg1
        pyxtnm2715 = arg2
        ## I1CMP:start
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1976(line=89,offs=19)--1977(line=89,offs=20))
        ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
        ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
        ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
        def pyxtnm2722(arg1, arg2): ## timp: sint_eq$sint(920)
          pyxtnm2716 = arg1
          pyxtnm2717 = arg2
          ## I1CMP:start
          ## let
          pyxtnm2721 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(2718);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(2718))))),I1BNDcons(I1TNM(2719);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(2719))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
          pyxtnm2720 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm2716, pyxtnm2717))
          pyxtnm2721 = pyxtnm2720
          ## end-of(let)
          ## I1CMP:return:pyxtnm2721
          return pyxtnm2721
        ## endtimp(sint_eq$sint(920))
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gord000.dats)@(1958(line=89,offs=1)--1963(line=89,offs=6))
        ## I0Etapq(I0Ecst(g_cmp(230)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gord000.sats)@(1630(line=66,offs=1)--1635(line=66,offs=6))));$list(T2JAG($list(T2Pvar(x0[5765])))))
        ## T1IMPallx(g_cmp(230), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1828(line=69,offs=1)--1861(line=70,offs=25)))
        ## T1IMPallx(g_cmp(230)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_cmp(230);$list(@(a[722],T2Pcst(strn)))))))
        pyxtnm2730 = None
        ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(1851(line=70,offs=15)--1859(line=70,offs=23))
        ## I0Etapq(I0Ecst(strn_cmp(1028)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2269(line=99,offs=1)--2277(line=99,offs=9))));$list(T2JAG($list())))
        ## T1IMPallx(strn_cmp(1028), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1623(line=57,offs=1)--1772(line=69,offs=2)))
        ## T1IMPallx(strn_cmp(1028)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_cmp(1028);$list()))))
        def pyxtnm2729(arg1, arg2): ## timp: strn_cmp(1028)
          pyxtnm2723 = arg1
          pyxtnm2724 = arg2
          ## I1CMP:start
          ## let
          pyxtnm2728 = None
          ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1703(line=65,offs=1)--1770(line=68,offs=39)))
          ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_cmp(2612));$list(I1FUNDCL(XATS2PY_strn_cmp(5017);$list(FJARGdarg($list(I1BNDcons(I1TNM(2725);I0Pvar(x1(5018));$list(@(x1(5018),I1Vtnm(I1TNM(2725))))),I1BNDcons(I1TNM(2726);I0Pvar(x2(5019));$list(@(x2(5019),I1Vtnm(I1TNM(2726))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_cmp);G1Nlist($list())))))))
          pyxtnm2727 = XATSDAPP(XATS2PY_strn_cmp(pyxtnm2723, pyxtnm2724))
          pyxtnm2728 = pyxtnm2727
          ## end-of(let)
          ## I1CMP:return:pyxtnm2728
          return pyxtnm2728
        ## endtimp(strn_cmp(1028))
        pyxtnm2730 = pyxtnm2729
        pyxtnm2731 = XATSDAPP(pyxtnm2730(pyxtnm2714, pyxtnm2715))
        pyxtnm2732 = XATSDAPP(pyxtnm2722(pyxtnm2731, XATSINT1(0)))
        ## I1CMP:return:pyxtnm2732
        return pyxtnm2732
      ## endtimp(g_eq(226))
      pyxtnm2734 = pyxtnm2733
      pyxtnm2735 = XATSDAPP(pyxtnm2734(pyxtnm2710, XATSP1CN("EVcons", pyxtnm2713[0+1])))
      pyxtnm2738 = None
      if (pyxtnm2735):
        pyxtnm2736 = XATSCAPP("optn_vt_cons", [1, XATSP1CN("EVcons", pyxtnm2713[1+1])])
        pyxtnm2738 = pyxtnm2736
      else:
        pyxtnm2737 = XATSDAPP(xenv_search_11161(XATSP1CN("EVcons", pyxtnm2713[2+1]), pyxtnm2710))
        pyxtnm2738 = pyxtnm2737
      ## end-of(if)
      pyxtnm2739 = pyxtnm2738
      break ## cls
    ## } // gpt
    ## } // cls
    XATS000_cfail()
  ## } while True // end-of(do-cls)
  ## I1CMP:return:pyxtnm2739
  return pyxtnm2739
## I1Dimplmnt0(LCSRCsome1(lambda1.dats)@(11446(line=749,offs=1)--15080(line=1028,offs=2)))
def term_eval01_11014(arg1, arg2): ## impl
  pyxtnm2740 = arg1
  pyxtnm2741 = arg2
  ## I1CMP:start
  ## let
  pyxtnm3012 = None
  pyxtnm3011 = None
  while True: ## do {
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2742);I0Pdapp(I0Pcon(TMint(32));$list(I0Pvar(int(5384))));$list(@(int(5384),I1Vp1cn(I0Pcon(TMint(32));I1Vtnm(I1TNM(2742));0)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMint",0))): ## { // gpt
      pyxtnm2742 = pyxtnm2740
      pyxtnm2743 = XATSCAPP("TVint", [0, XATSP1CN("TMint", pyxtnm2742[0+1])])
      pyxtnm3011 = pyxtnm2743
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2744);I0Pdapp(I0Pcon(TMbtf(33));$list(I0Pvar(btf(5385))));$list(@(btf(5385),I1Vp1cn(I0Pcon(TMbtf(33));I1Vtnm(I1TNM(2744));0)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMbtf",1))): ## { // gpt
      pyxtnm2744 = pyxtnm2740
      pyxtnm2745 = XATSCAPP("TVbtf", [1, XATSP1CN("TMbtf", pyxtnm2744[0+1])])
      pyxtnm3011 = pyxtnm2745
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2746);I0Pdapp(I0Pcon(TMvar(34));$list(I0Pvar(x00(5386))));$list(@(x00(5386),I1Vp1cn(I0Pcon(TMvar(34));I1Vtnm(I1TNM(2746));0)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMvar",2))): ## { // gpt
      pyxtnm2746 = pyxtnm2740
      ## let
      pyxtnm2751 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(11572(line=762,offs=1)--11603(line=763,offs=22)))
      ## I1VALDCL
      pyxtnm2748 = None
      pyxtnm2747 = XATSDAPP(xenv_search_11161(pyxtnm2741, XATSP1CN("TMvar", pyxtnm2746[0+1])))
      pyxtnm2748 = pyxtnm2747
      XATS000_patck(True)
      pyxtnm2750 = None
      while True: ## do {
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2749);I0Pfree(I0Pdapp(I0Pcon(optn_vt_cons(7));$list(I0Pvar(tvx(5388)))));$list(@(tvx(5388),I1Vp1cn(I0Pcon(optn_vt_cons(7));I1Vtnm(I1TNM(2749));0)))))
        if (XATS000_ctgeq(pyxtnm2748, XATSCTAG("optn_vt_cons",1))): ## { // gpt
          pyxtnm2749 = pyxtnm2748
          pyxtnm2750 = XATSP1CN("optn_vt_cons", pyxtnm2749[0+1])
          break ## cls
        ## } // gpt
        ## } // cls
        XATS000_cfail()
      ## } while True // end-of(do-cls)
      pyxtnm2751 = pyxtnm2750
      ## end-of(let)
      pyxtnm3011 = pyxtnm2751
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2752);I0Pdapp(I0Pcon(TMapp(36));$list(I0Pvar(tm1(5389)),I0Pvar(tm2(5390))));$list(@(tm1(5389),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(2752));0)),@(tm2(5390),I1Vp1cn(I0Pcon(TMapp(36));I1Vtnm(I1TNM(2752));1)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMapp",4))): ## { // gpt
      pyxtnm2752 = pyxtnm2740
      ## let
      pyxtnm2772 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(11765(line=778,offs=1)--11796(line=779,offs=22)))
      ## I1VALDCL
      pyxtnm2754 = None
      pyxtnm2753 = XATSDAPP(term_eval01_11014(XATSP1CN("TMapp", pyxtnm2752[0+1]), pyxtnm2741))
      pyxtnm2754 = pyxtnm2753
      XATS000_patck(True)
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(11797(line=780,offs=1)--11828(line=781,offs=22)))
      ## I1VALDCL
      pyxtnm2756 = None
      pyxtnm2755 = XATSDAPP(term_eval01_11014(XATSP1CN("TMapp", pyxtnm2752[1+1]), pyxtnm2741))
      pyxtnm2756 = pyxtnm2755
      XATS000_patck(True)
      pyxtnm2771 = None
      while True: ## do {
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2757);I0Pdapp(I0Pcon(TVclo(43));$list(I0Pvar(tm1(5393)),I0Pvar(env(5394))));$list(@(tm1(5393),I1Vp1cn(I0Pcon(TVclo(43));I1Vtnm(I1TNM(2757));0)),@(env(5394),I1Vp1cn(I0Pcon(TVclo(43));I1Vtnm(I1TNM(2757));1)))))
        if (XATS000_ctgeq(pyxtnm2754, XATSCTAG("TVclo",2))): ## { // gpt
          pyxtnm2757 = pyxtnm2754
          pyxtnm2770 = None
          while True: ## do {
            ## { // cls
            ## I1GPTpat(I1BNDcons(I1TNM(2758);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5395)),I0Pvar(tmx(5396))));$list(@(x01(5395),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(2758));0)),@(tmx(5396),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(2758));1)))))
            if (XATS000_ctgeq(XATSP1CN("TVclo", pyxtnm2757[0+1]), XATSCTAG("TMlam",3))): ## { // gpt
              pyxtnm2758 = XATSP1CN("TVclo", pyxtnm2757[0+1])
              ## let
              pyxtnm2762 = None
              ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(11945(line=797,offs=1)--11976(line=798,offs=28)))
              ## I1VALDCL
              pyxtnm2760 = None
              pyxtnm2759 = XATSCAPP("EVcons", [1, XATSP1CN("TMlam", pyxtnm2758[0+1]), pyxtnm2756, XATSP1CN("TVclo", pyxtnm2757[1+1])])
              pyxtnm2760 = pyxtnm2759
              XATS000_patck(True)
              pyxtnm2761 = XATSDAPP(term_eval01_11014(XATSP1CN("TMlam", pyxtnm2758[1+1]), pyxtnm2760))
              pyxtnm2762 = pyxtnm2761
              ## end-of(let)
              pyxtnm2770 = pyxtnm2762
              break ## cls
            ## } // gpt
            ## } // cls
            ## { // cls
            ## I1GPTpat(I1BNDcons(I1TNM(2763);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5398)),I0Pvar(x01(5399)),I0Pvar(tmx(5400))));$list(@(f00(5398),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(2763));0)),@(x01(5399),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(2763));1)),@(tmx(5400),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(2763));2)))))
            if (XATS000_ctgeq(XATSP1CN("TVclo", pyxtnm2757[0+1]), XATSCTAG("TMfix",7))): ## { // gpt
              pyxtnm2763 = XATSP1CN("TVclo", pyxtnm2757[0+1])
              ## let
              pyxtnm2769 = None
              ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12036(line=805,offs=1)--12067(line=806,offs=28)))
              ## I1VALDCL
              pyxtnm2765 = None
              pyxtnm2764 = XATSCAPP("EVcons", [1, XATSP1CN("TMfix", pyxtnm2763[0+1]), pyxtnm2754, XATSP1CN("TVclo", pyxtnm2757[1+1])])
              pyxtnm2765 = pyxtnm2764
              XATS000_patck(True)
              ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12068(line=807,offs=1)--12099(line=808,offs=28)))
              ## I1VALDCL
              pyxtnm2767 = None
              pyxtnm2766 = XATSCAPP("EVcons", [1, XATSP1CN("TMfix", pyxtnm2763[1+1]), pyxtnm2756, pyxtnm2765])
              pyxtnm2767 = pyxtnm2766
              XATS000_patck(True)
              pyxtnm2768 = XATSDAPP(term_eval01_11014(XATSP1CN("TMfix", pyxtnm2763[2+1]), pyxtnm2767))
              pyxtnm2769 = pyxtnm2768
              ## end-of(let)
              pyxtnm2770 = pyxtnm2769
              break ## cls
            ## } // gpt
            ## } // cls
            XATS000_cfail()
          ## } while True // end-of(do-cls)
          pyxtnm2771 = pyxtnm2770
          break ## cls
        ## } // gpt
        ## } // cls
        XATS000_cfail()
      ## } while True // end-of(do-cls)
      pyxtnm2772 = pyxtnm2771
      ## end-of(let)
      pyxtnm3011 = pyxtnm2772
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2773);I0Pdapp(I0Pcon(TMlam(35));$list(I0Pvar(x01(5403)),I0Pvar(tmx(5404))));$list(@(x01(5403),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(2773));0)),@(tmx(5404),I1Vp1cn(I0Pcon(TMlam(35));I1Vtnm(I1TNM(2773));1)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMlam",3))): ## { // gpt
      pyxtnm2773 = pyxtnm2740
      pyxtnm2774 = XATSCAPP("TVclo", [2, pyxtnm2740, pyxtnm2741])
      pyxtnm3011 = pyxtnm2774
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2775);I0Pdapp(I0Pcon(TMfix(39));$list(I0Pvar(f00(5405)),I0Pvar(x01(5406)),I0Pvar(tmx(5407))));$list(@(f00(5405),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(2775));0)),@(x01(5406),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(2775));1)),@(tmx(5407),I1Vp1cn(I0Pcon(TMfix(39));I1Vtnm(I1TNM(2775));2)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMfix",7))): ## { // gpt
      pyxtnm2775 = pyxtnm2740
      pyxtnm2776 = XATSCAPP("TVclo", [2, pyxtnm2740, pyxtnm2741])
      pyxtnm3011 = pyxtnm2776
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2777);I0Pdapp(I0Pcon(TMopr(37));$list(I0Pvar(pnm(5408)),I0Pvar(tms(5409))));$list(@(pnm(5408),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(2777));0)),@(tms(5409),I1Vp1cn(I0Pcon(TMopr(37));I1Vtnm(I1TNM(2777));1)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMopr",5))): ## { // gpt
      pyxtnm2777 = pyxtnm2740
      pyxtnm2997 = None
      while True: ## do {
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2778);I0Pstr(T_STRN1_clsd("+";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("+"))): ## { // gpt
          pyxtnm2778 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2794 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12302(line=830,offs=1)--12331(line=830,offs=30)))
          ## I1VALDCL
          pyxtnm2779 = None
          pyxtnm2779 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12332(line=831,offs=1)--12361(line=831,offs=30)))
          ## I1VALDCL
          pyxtnm2780 = None
          pyxtnm2780 = XATSP1CN("list_cons", pyxtnm2779[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2779[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12362(line=832,offs=1)--12401(line=833,offs=35)))
          ## I1VALDCL
          pyxtnm2782 = None
          pyxtnm2781 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2779[0+1]), pyxtnm2741))
          pyxtnm2782 = pyxtnm2781
          XATS000_patck(XATS000_ctgeq(pyxtnm2781, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12402(line=834,offs=1)--12441(line=835,offs=35)))
          ## I1VALDCL
          pyxtnm2784 = None
          pyxtnm2783 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2780[0+1]), pyxtnm2741))
          pyxtnm2784 = pyxtnm2783
          XATS000_patck(XATS000_ctgeq(pyxtnm2783, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(12287(line=828,offs=10)--12288(line=828,offs=11))
          ## I0Etapq(I0Ecst(sint_add$sint(925)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2816(line=127,offs=1)--2829(line=127,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_add$sint(925), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2677(line=145,offs=1)--2841(line=157,offs=2)))
          ## T1IMPallx(sint_add$sint(925)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_add$sint(925);$list()))))
          def pyxtnm2791(arg1, arg2): ## timp: sint_add$sint(925)
            pyxtnm2785 = arg1
            pyxtnm2786 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2790 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2767(line=153,offs=1)--2839(line=156,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_add$sint(2584));$list(I1FUNDCL(XATS2PY_sint_add$sint(4901);$list(FJARGdarg($list(I1BNDcons(I1TNM(2787);I0Pvar(i1(4902));$list(@(i1(4902),I1Vtnm(I1TNM(2787))))),I1BNDcons(I1TNM(2788);I0Pvar(i2(4903));$list(@(i2(4903),I1Vtnm(I1TNM(2788))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_add$sint);G1Nlist($list())))))))
            pyxtnm2789 = XATSDAPP(XATS2PY_sint_add_sint(pyxtnm2785, pyxtnm2786))
            pyxtnm2790 = pyxtnm2789
            ## end-of(let)
            ## I1CMP:return:pyxtnm2790
            return pyxtnm2790
          ## endtimp(sint_add$sint(925))
          pyxtnm2792 = XATSDAPP(pyxtnm2791(XATSP1CN("TVint", pyxtnm2782[0+1]), XATSP1CN("TVint", pyxtnm2784[0+1])))
          pyxtnm2793 = XATSCAPP("TVint", [0, pyxtnm2792])
          pyxtnm2794 = pyxtnm2793
          ## end-of(let)
          pyxtnm2997 = pyxtnm2794
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2795);I0Pstr(T_STRN1_clsd("-";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("-"))): ## { // gpt
          pyxtnm2795 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2811 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12481(line=842,offs=1)--12510(line=842,offs=30)))
          ## I1VALDCL
          pyxtnm2796 = None
          pyxtnm2796 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12511(line=843,offs=1)--12540(line=843,offs=30)))
          ## I1VALDCL
          pyxtnm2797 = None
          pyxtnm2797 = XATSP1CN("list_cons", pyxtnm2796[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2796[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12541(line=844,offs=1)--12580(line=845,offs=35)))
          ## I1VALDCL
          pyxtnm2799 = None
          pyxtnm2798 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2796[0+1]), pyxtnm2741))
          pyxtnm2799 = pyxtnm2798
          XATS000_patck(XATS000_ctgeq(pyxtnm2798, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12581(line=846,offs=1)--12620(line=847,offs=35)))
          ## I1VALDCL
          pyxtnm2801 = None
          pyxtnm2800 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2797[0+1]), pyxtnm2741))
          pyxtnm2801 = pyxtnm2800
          XATS000_patck(XATS000_ctgeq(pyxtnm2800, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(12466(line=840,offs=10)--12467(line=840,offs=11))
          ## I0Etapq(I0Ecst(sint_sub$sint(926)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2881(line=131,offs=1)--2894(line=131,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_sub$sint(926), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2845(line=159,offs=1)--3009(line=171,offs=2)))
          ## T1IMPallx(sint_sub$sint(926)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_sub$sint(926);$list()))))
          def pyxtnm2808(arg1, arg2): ## timp: sint_sub$sint(926)
            pyxtnm2802 = arg1
            pyxtnm2803 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2807 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2935(line=167,offs=1)--3007(line=170,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_sub$sint(2585));$list(I1FUNDCL(XATS2PY_sint_sub$sint(4906);$list(FJARGdarg($list(I1BNDcons(I1TNM(2804);I0Pvar(i1(4907));$list(@(i1(4907),I1Vtnm(I1TNM(2804))))),I1BNDcons(I1TNM(2805);I0Pvar(i2(4908));$list(@(i2(4908),I1Vtnm(I1TNM(2805))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_sub$sint);G1Nlist($list())))))))
            pyxtnm2806 = XATSDAPP(XATS2PY_sint_sub_sint(pyxtnm2802, pyxtnm2803))
            pyxtnm2807 = pyxtnm2806
            ## end-of(let)
            ## I1CMP:return:pyxtnm2807
            return pyxtnm2807
          ## endtimp(sint_sub$sint(926))
          pyxtnm2809 = XATSDAPP(pyxtnm2808(XATSP1CN("TVint", pyxtnm2799[0+1]), XATSP1CN("TVint", pyxtnm2801[0+1])))
          pyxtnm2810 = XATSCAPP("TVint", [0, pyxtnm2809])
          pyxtnm2811 = pyxtnm2810
          ## end-of(let)
          pyxtnm2997 = pyxtnm2811
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2812);I0Pstr(T_STRN1_clsd("*";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("*"))): ## { // gpt
          pyxtnm2812 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2828 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12660(line=854,offs=1)--12689(line=854,offs=30)))
          ## I1VALDCL
          pyxtnm2813 = None
          pyxtnm2813 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12690(line=855,offs=1)--12719(line=855,offs=30)))
          ## I1VALDCL
          pyxtnm2814 = None
          pyxtnm2814 = XATSP1CN("list_cons", pyxtnm2813[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2813[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12720(line=856,offs=1)--12759(line=857,offs=35)))
          ## I1VALDCL
          pyxtnm2816 = None
          pyxtnm2815 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2813[0+1]), pyxtnm2741))
          pyxtnm2816 = pyxtnm2815
          XATS000_patck(XATS000_ctgeq(pyxtnm2815, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12760(line=858,offs=1)--12799(line=859,offs=35)))
          ## I1VALDCL
          pyxtnm2818 = None
          pyxtnm2817 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2814[0+1]), pyxtnm2741))
          pyxtnm2818 = pyxtnm2817
          XATS000_patck(XATS000_ctgeq(pyxtnm2817, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(12645(line=852,offs=10)--12646(line=852,offs=11))
          ## I0Etapq(I0Ecst(sint_mul$sint(927)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2946(line=135,offs=1)--2959(line=135,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_mul$sint(927), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3013(line=173,offs=1)--3177(line=185,offs=2)))
          ## T1IMPallx(sint_mul$sint(927)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_mul$sint(927);$list()))))
          def pyxtnm2825(arg1, arg2): ## timp: sint_mul$sint(927)
            pyxtnm2819 = arg1
            pyxtnm2820 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2824 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3103(line=181,offs=1)--3175(line=184,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_mul$sint(2586));$list(I1FUNDCL(XATS2PY_sint_mul$sint(4911);$list(FJARGdarg($list(I1BNDcons(I1TNM(2821);I0Pvar(i1(4912));$list(@(i1(4912),I1Vtnm(I1TNM(2821))))),I1BNDcons(I1TNM(2822);I0Pvar(i2(4913));$list(@(i2(4913),I1Vtnm(I1TNM(2822))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_mul$sint);G1Nlist($list())))))))
            pyxtnm2823 = XATSDAPP(XATS2PY_sint_mul_sint(pyxtnm2819, pyxtnm2820))
            pyxtnm2824 = pyxtnm2823
            ## end-of(let)
            ## I1CMP:return:pyxtnm2824
            return pyxtnm2824
          ## endtimp(sint_mul$sint(927))
          pyxtnm2826 = XATSDAPP(pyxtnm2825(XATSP1CN("TVint", pyxtnm2816[0+1]), XATSP1CN("TVint", pyxtnm2818[0+1])))
          pyxtnm2827 = XATSCAPP("TVint", [0, pyxtnm2826])
          pyxtnm2828 = pyxtnm2827
          ## end-of(let)
          pyxtnm2997 = pyxtnm2828
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2829);I0Pstr(T_STRN1_clsd("/";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("/"))): ## { // gpt
          pyxtnm2829 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2845 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12839(line=866,offs=1)--12868(line=866,offs=30)))
          ## I1VALDCL
          pyxtnm2830 = None
          pyxtnm2830 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12869(line=867,offs=1)--12898(line=867,offs=30)))
          ## I1VALDCL
          pyxtnm2831 = None
          pyxtnm2831 = XATSP1CN("list_cons", pyxtnm2830[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2830[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12899(line=868,offs=1)--12938(line=869,offs=35)))
          ## I1VALDCL
          pyxtnm2833 = None
          pyxtnm2832 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2830[0+1]), pyxtnm2741))
          pyxtnm2833 = pyxtnm2832
          XATS000_patck(XATS000_ctgeq(pyxtnm2832, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(12939(line=870,offs=1)--12978(line=871,offs=35)))
          ## I1VALDCL
          pyxtnm2835 = None
          pyxtnm2834 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2831[0+1]), pyxtnm2741))
          pyxtnm2835 = pyxtnm2834
          XATS000_patck(XATS000_ctgeq(pyxtnm2834, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(12824(line=864,offs=10)--12825(line=864,offs=11))
          ## I0Etapq(I0Ecst(sint_div$sint(928)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(3011(line=139,offs=1)--3024(line=139,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_div$sint(928), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3181(line=187,offs=1)--3345(line=199,offs=2)))
          ## T1IMPallx(sint_div$sint(928)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_div$sint(928);$list()))))
          def pyxtnm2842(arg1, arg2): ## timp: sint_div$sint(928)
            pyxtnm2836 = arg1
            pyxtnm2837 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2841 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3271(line=195,offs=1)--3343(line=198,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_div$sint(2587));$list(I1FUNDCL(XATS2PY_sint_div$sint(4916);$list(FJARGdarg($list(I1BNDcons(I1TNM(2838);I0Pvar(i1(4917));$list(@(i1(4917),I1Vtnm(I1TNM(2838))))),I1BNDcons(I1TNM(2839);I0Pvar(i2(4918));$list(@(i2(4918),I1Vtnm(I1TNM(2839))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_div$sint);G1Nlist($list())))))))
            pyxtnm2840 = XATSDAPP(XATS2PY_sint_div_sint(pyxtnm2836, pyxtnm2837))
            pyxtnm2841 = pyxtnm2840
            ## end-of(let)
            ## I1CMP:return:pyxtnm2841
            return pyxtnm2841
          ## endtimp(sint_div$sint(928))
          pyxtnm2843 = XATSDAPP(pyxtnm2842(XATSP1CN("TVint", pyxtnm2833[0+1]), XATSP1CN("TVint", pyxtnm2835[0+1])))
          pyxtnm2844 = XATSCAPP("TVint", [0, pyxtnm2843])
          pyxtnm2845 = pyxtnm2844
          ## end-of(let)
          pyxtnm2997 = pyxtnm2845
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2846);I0Pstr(T_STRN1_clsd("%";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("%"))): ## { // gpt
          pyxtnm2846 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2862 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13018(line=878,offs=1)--13047(line=878,offs=30)))
          ## I1VALDCL
          pyxtnm2847 = None
          pyxtnm2847 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13048(line=879,offs=1)--13077(line=879,offs=30)))
          ## I1VALDCL
          pyxtnm2848 = None
          pyxtnm2848 = XATSP1CN("list_cons", pyxtnm2847[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2847[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13078(line=880,offs=1)--13117(line=881,offs=35)))
          ## I1VALDCL
          pyxtnm2850 = None
          pyxtnm2849 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2847[0+1]), pyxtnm2741))
          pyxtnm2850 = pyxtnm2849
          XATS000_patck(XATS000_ctgeq(pyxtnm2849, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13118(line=882,offs=1)--13157(line=883,offs=35)))
          ## I1VALDCL
          pyxtnm2852 = None
          pyxtnm2851 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2848[0+1]), pyxtnm2741))
          pyxtnm2852 = pyxtnm2851
          XATS000_patck(XATS000_ctgeq(pyxtnm2851, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(13003(line=876,offs=10)--13004(line=876,offs=11))
          ## I0Etapq(I0Ecst(sint_mod$sint(929)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(3076(line=143,offs=1)--3089(line=143,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_mod$sint(929), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3349(line=201,offs=1)--3513(line=213,offs=2)))
          ## T1IMPallx(sint_mod$sint(929)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_mod$sint(929);$list()))))
          def pyxtnm2859(arg1, arg2): ## timp: sint_mod$sint(929)
            pyxtnm2853 = arg1
            pyxtnm2854 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2858 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(3439(line=209,offs=1)--3511(line=212,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_mod$sint(2588));$list(I1FUNDCL(XATS2PY_sint_mod$sint(4921);$list(FJARGdarg($list(I1BNDcons(I1TNM(2855);I0Pvar(i1(4922));$list(@(i1(4922),I1Vtnm(I1TNM(2855))))),I1BNDcons(I1TNM(2856);I0Pvar(i2(4923));$list(@(i2(4923),I1Vtnm(I1TNM(2856))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_mod$sint);G1Nlist($list())))))))
            pyxtnm2857 = XATSDAPP(XATS2PY_sint_mod_sint(pyxtnm2853, pyxtnm2854))
            pyxtnm2858 = pyxtnm2857
            ## end-of(let)
            ## I1CMP:return:pyxtnm2858
            return pyxtnm2858
          ## endtimp(sint_mod$sint(929))
          pyxtnm2860 = XATSDAPP(pyxtnm2859(XATSP1CN("TVint", pyxtnm2850[0+1]), XATSP1CN("TVint", pyxtnm2852[0+1])))
          pyxtnm2861 = XATSCAPP("TVint", [0, pyxtnm2860])
          pyxtnm2862 = pyxtnm2861
          ## end-of(let)
          pyxtnm2997 = pyxtnm2862
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2863);I0Pstr(T_STRN1_clsd("<";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("<"))): ## { // gpt
          pyxtnm2863 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2879 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13197(line=890,offs=1)--13226(line=890,offs=30)))
          ## I1VALDCL
          pyxtnm2864 = None
          pyxtnm2864 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13227(line=891,offs=1)--13256(line=891,offs=30)))
          ## I1VALDCL
          pyxtnm2865 = None
          pyxtnm2865 = XATSP1CN("list_cons", pyxtnm2864[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2864[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13257(line=892,offs=1)--13296(line=893,offs=35)))
          ## I1VALDCL
          pyxtnm2867 = None
          pyxtnm2866 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2864[0+1]), pyxtnm2741))
          pyxtnm2867 = pyxtnm2866
          XATS000_patck(XATS000_ctgeq(pyxtnm2866, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13297(line=894,offs=1)--13336(line=895,offs=35)))
          ## I1VALDCL
          pyxtnm2869 = None
          pyxtnm2868 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2865[0+1]), pyxtnm2741))
          pyxtnm2869 = pyxtnm2868
          XATS000_patck(XATS000_ctgeq(pyxtnm2868, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(13182(line=888,offs=10)--13183(line=888,offs=11))
          ## I0Etapq(I0Ecst(sint_lt$sint(918)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2041(line=83,offs=1)--2053(line=83,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_lt$sint(918), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1612(line=56,offs=1)--1773(line=68,offs=2)))
          ## T1IMPallx(sint_lt$sint(918)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_lt$sint(918);$list()))))
          def pyxtnm2876(arg1, arg2): ## timp: sint_lt$sint(918)
            pyxtnm2870 = arg1
            pyxtnm2871 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2875 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1700(line=64,offs=1)--1771(line=67,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_lt$sint(2578));$list(I1FUNDCL(XATS2PY_sint_lt$sint(4871);$list(FJARGdarg($list(I1BNDcons(I1TNM(2872);I0Pvar(i1(4872));$list(@(i1(4872),I1Vtnm(I1TNM(2872))))),I1BNDcons(I1TNM(2873);I0Pvar(i2(4873));$list(@(i2(4873),I1Vtnm(I1TNM(2873))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_lt$sint);G1Nlist($list())))))))
            pyxtnm2874 = XATSDAPP(XATS2PY_sint_lt_sint(pyxtnm2870, pyxtnm2871))
            pyxtnm2875 = pyxtnm2874
            ## end-of(let)
            ## I1CMP:return:pyxtnm2875
            return pyxtnm2875
          ## endtimp(sint_lt$sint(918))
          pyxtnm2877 = XATSDAPP(pyxtnm2876(XATSP1CN("TVint", pyxtnm2867[0+1]), XATSP1CN("TVint", pyxtnm2869[0+1])))
          pyxtnm2878 = XATSCAPP("TVbtf", [1, pyxtnm2877])
          pyxtnm2879 = pyxtnm2878
          ## end-of(let)
          pyxtnm2997 = pyxtnm2879
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2880);I0Pstr(T_STRN1_clsd(">";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN(">"))): ## { // gpt
          pyxtnm2880 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2896 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13376(line=902,offs=1)--13405(line=902,offs=30)))
          ## I1VALDCL
          pyxtnm2881 = None
          pyxtnm2881 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13406(line=903,offs=1)--13435(line=903,offs=30)))
          ## I1VALDCL
          pyxtnm2882 = None
          pyxtnm2882 = XATSP1CN("list_cons", pyxtnm2881[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2881[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13436(line=904,offs=1)--13475(line=905,offs=35)))
          ## I1VALDCL
          pyxtnm2884 = None
          pyxtnm2883 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2881[0+1]), pyxtnm2741))
          pyxtnm2884 = pyxtnm2883
          XATS000_patck(XATS000_ctgeq(pyxtnm2883, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13476(line=906,offs=1)--13515(line=907,offs=35)))
          ## I1VALDCL
          pyxtnm2886 = None
          pyxtnm2885 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2882[0+1]), pyxtnm2741))
          pyxtnm2886 = pyxtnm2885
          XATS000_patck(XATS000_ctgeq(pyxtnm2885, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(13361(line=900,offs=10)--13362(line=900,offs=11))
          ## I0Etapq(I0Ecst(sint_gt$sint(919)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2103(line=87,offs=1)--2115(line=87,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_gt$sint(919), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1777(line=70,offs=1)--1938(line=82,offs=2)))
          ## T1IMPallx(sint_gt$sint(919)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gt$sint(919);$list()))))
          def pyxtnm2893(arg1, arg2): ## timp: sint_gt$sint(919)
            pyxtnm2887 = arg1
            pyxtnm2888 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2892 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1865(line=78,offs=1)--1936(line=81,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gt$sint(2579));$list(I1FUNDCL(XATS2PY_sint_gt$sint(4876);$list(FJARGdarg($list(I1BNDcons(I1TNM(2889);I0Pvar(i1(4877));$list(@(i1(4877),I1Vtnm(I1TNM(2889))))),I1BNDcons(I1TNM(2890);I0Pvar(i2(4878));$list(@(i2(4878),I1Vtnm(I1TNM(2890))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gt$sint);G1Nlist($list())))))))
            pyxtnm2891 = XATSDAPP(XATS2PY_sint_gt_sint(pyxtnm2887, pyxtnm2888))
            pyxtnm2892 = pyxtnm2891
            ## end-of(let)
            ## I1CMP:return:pyxtnm2892
            return pyxtnm2892
          ## endtimp(sint_gt$sint(919))
          pyxtnm2894 = XATSDAPP(pyxtnm2893(XATSP1CN("TVint", pyxtnm2884[0+1]), XATSP1CN("TVint", pyxtnm2886[0+1])))
          pyxtnm2895 = XATSCAPP("TVbtf", [1, pyxtnm2894])
          pyxtnm2896 = pyxtnm2895
          ## end-of(let)
          pyxtnm2997 = pyxtnm2896
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2897);I0Pstr(T_STRN1_clsd("=";3));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("="))): ## { // gpt
          pyxtnm2897 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2913 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13555(line=914,offs=1)--13584(line=914,offs=30)))
          ## I1VALDCL
          pyxtnm2898 = None
          pyxtnm2898 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13585(line=915,offs=1)--13614(line=915,offs=30)))
          ## I1VALDCL
          pyxtnm2899 = None
          pyxtnm2899 = XATSP1CN("list_cons", pyxtnm2898[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2898[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13615(line=916,offs=1)--13654(line=917,offs=35)))
          ## I1VALDCL
          pyxtnm2901 = None
          pyxtnm2900 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2898[0+1]), pyxtnm2741))
          pyxtnm2901 = pyxtnm2900
          XATS000_patck(XATS000_ctgeq(pyxtnm2900, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13655(line=918,offs=1)--13694(line=919,offs=35)))
          ## I1VALDCL
          pyxtnm2903 = None
          pyxtnm2902 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2899[0+1]), pyxtnm2741))
          pyxtnm2903 = pyxtnm2902
          XATS000_patck(XATS000_ctgeq(pyxtnm2902, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(13540(line=912,offs=10)--13541(line=912,offs=11))
          ## I0Etapq(I0Ecst(sint_eq$sint(920)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2165(line=91,offs=1)--2177(line=91,offs=13))));$list(T2JAG($list())))
          ## T1IMPallx(sint_eq$sint(920), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(1942(line=84,offs=1)--2103(line=96,offs=2)))
          ## T1IMPallx(sint_eq$sint(920)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_eq$sint(920);$list()))))
          def pyxtnm2910(arg1, arg2): ## timp: sint_eq$sint(920)
            pyxtnm2904 = arg1
            pyxtnm2905 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2909 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2030(line=92,offs=1)--2101(line=95,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_eq$sint(2580));$list(I1FUNDCL(XATS2PY_sint_eq$sint(4881);$list(FJARGdarg($list(I1BNDcons(I1TNM(2906);I0Pvar(i1(4882));$list(@(i1(4882),I1Vtnm(I1TNM(2906))))),I1BNDcons(I1TNM(2907);I0Pvar(i2(4883));$list(@(i2(4883),I1Vtnm(I1TNM(2907))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_eq$sint);G1Nlist($list())))))))
            pyxtnm2908 = XATSDAPP(XATS2PY_sint_eq_sint(pyxtnm2904, pyxtnm2905))
            pyxtnm2909 = pyxtnm2908
            ## end-of(let)
            ## I1CMP:return:pyxtnm2909
            return pyxtnm2909
          ## endtimp(sint_eq$sint(920))
          pyxtnm2911 = XATSDAPP(pyxtnm2910(XATSP1CN("TVint", pyxtnm2901[0+1]), XATSP1CN("TVint", pyxtnm2903[0+1])))
          pyxtnm2912 = XATSCAPP("TVbtf", [1, pyxtnm2911])
          pyxtnm2913 = pyxtnm2912
          ## end-of(let)
          pyxtnm2997 = pyxtnm2913
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2914);I0Pstr(T_STRN1_clsd("<=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("<="))): ## { // gpt
          pyxtnm2914 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2930 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13736(line=926,offs=1)--13765(line=926,offs=30)))
          ## I1VALDCL
          pyxtnm2915 = None
          pyxtnm2915 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13766(line=927,offs=1)--13795(line=927,offs=30)))
          ## I1VALDCL
          pyxtnm2916 = None
          pyxtnm2916 = XATSP1CN("list_cons", pyxtnm2915[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2915[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13796(line=928,offs=1)--13835(line=929,offs=35)))
          ## I1VALDCL
          pyxtnm2918 = None
          pyxtnm2917 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2915[0+1]), pyxtnm2741))
          pyxtnm2918 = pyxtnm2917
          XATS000_patck(XATS000_ctgeq(pyxtnm2917, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13836(line=930,offs=1)--13875(line=931,offs=35)))
          ## I1VALDCL
          pyxtnm2920 = None
          pyxtnm2919 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2916[0+1]), pyxtnm2741))
          pyxtnm2920 = pyxtnm2919
          XATS000_patck(XATS000_ctgeq(pyxtnm2919, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(13720(line=924,offs=10)--13722(line=924,offs=12))
          ## I0Etapq(I0Ecst(sint_lte$sint(921)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2344(line=100,offs=1)--2357(line=100,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_lte$sint(921), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2130(line=100,offs=1)--2294(line=112,offs=2)))
          ## T1IMPallx(sint_lte$sint(921)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_lte$sint(921);$list()))))
          def pyxtnm2927(arg1, arg2): ## timp: sint_lte$sint(921)
            pyxtnm2921 = arg1
            pyxtnm2922 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2926 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2220(line=108,offs=1)--2292(line=111,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_lte$sint(2581));$list(I1FUNDCL(XATS2PY_sint_lte$sint(4886);$list(FJARGdarg($list(I1BNDcons(I1TNM(2923);I0Pvar(i1(4887));$list(@(i1(4887),I1Vtnm(I1TNM(2923))))),I1BNDcons(I1TNM(2924);I0Pvar(i2(4888));$list(@(i2(4888),I1Vtnm(I1TNM(2924))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_lte$sint);G1Nlist($list())))))))
            pyxtnm2925 = XATSDAPP(XATS2PY_sint_lte_sint(pyxtnm2921, pyxtnm2922))
            pyxtnm2926 = pyxtnm2925
            ## end-of(let)
            ## I1CMP:return:pyxtnm2926
            return pyxtnm2926
          ## endtimp(sint_lte$sint(921))
          pyxtnm2928 = XATSDAPP(pyxtnm2927(XATSP1CN("TVint", pyxtnm2918[0+1]), XATSP1CN("TVint", pyxtnm2920[0+1])))
          pyxtnm2929 = XATSCAPP("TVbtf", [1, pyxtnm2928])
          pyxtnm2930 = pyxtnm2929
          ## end-of(let)
          pyxtnm2997 = pyxtnm2930
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2931);I0Pstr(T_STRN1_clsd(">=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN(">="))): ## { // gpt
          pyxtnm2931 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2947 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13917(line=938,offs=1)--13946(line=938,offs=30)))
          ## I1VALDCL
          pyxtnm2932 = None
          pyxtnm2932 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13947(line=939,offs=1)--13976(line=939,offs=30)))
          ## I1VALDCL
          pyxtnm2933 = None
          pyxtnm2933 = XATSP1CN("list_cons", pyxtnm2932[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2932[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(13977(line=940,offs=1)--14016(line=941,offs=35)))
          ## I1VALDCL
          pyxtnm2935 = None
          pyxtnm2934 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2932[0+1]), pyxtnm2741))
          pyxtnm2935 = pyxtnm2934
          XATS000_patck(XATS000_ctgeq(pyxtnm2934, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14017(line=942,offs=1)--14056(line=943,offs=35)))
          ## I1VALDCL
          pyxtnm2937 = None
          pyxtnm2936 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2933[0+1]), pyxtnm2741))
          pyxtnm2937 = pyxtnm2936
          XATS000_patck(XATS000_ctgeq(pyxtnm2936, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(13901(line=936,offs=10)--13903(line=936,offs=12))
          ## I0Etapq(I0Ecst(sint_gte$sint(922)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2408(line=104,offs=1)--2421(line=104,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_gte$sint(922), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2298(line=114,offs=1)--2462(line=126,offs=2)))
          ## T1IMPallx(sint_gte$sint(922)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_gte$sint(922);$list()))))
          def pyxtnm2944(arg1, arg2): ## timp: sint_gte$sint(922)
            pyxtnm2938 = arg1
            pyxtnm2939 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2943 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2388(line=122,offs=1)--2460(line=125,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_gte$sint(2582));$list(I1FUNDCL(XATS2PY_sint_gte$sint(4891);$list(FJARGdarg($list(I1BNDcons(I1TNM(2940);I0Pvar(i1(4892));$list(@(i1(4892),I1Vtnm(I1TNM(2940))))),I1BNDcons(I1TNM(2941);I0Pvar(i2(4893));$list(@(i2(4893),I1Vtnm(I1TNM(2941))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_gte$sint);G1Nlist($list())))))))
            pyxtnm2942 = XATSDAPP(XATS2PY_sint_gte_sint(pyxtnm2938, pyxtnm2939))
            pyxtnm2943 = pyxtnm2942
            ## end-of(let)
            ## I1CMP:return:pyxtnm2943
            return pyxtnm2943
          ## endtimp(sint_gte$sint(922))
          pyxtnm2945 = XATSDAPP(pyxtnm2944(XATSP1CN("TVint", pyxtnm2935[0+1]), XATSP1CN("TVint", pyxtnm2937[0+1])))
          pyxtnm2946 = XATSCAPP("TVbtf", [1, pyxtnm2945])
          pyxtnm2947 = pyxtnm2946
          ## end-of(let)
          pyxtnm2997 = pyxtnm2947
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2948);I0Pstr(T_STRN1_clsd("!=";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("!="))): ## { // gpt
          pyxtnm2948 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2964 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14098(line=950,offs=1)--14127(line=950,offs=30)))
          ## I1VALDCL
          pyxtnm2949 = None
          pyxtnm2949 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14128(line=951,offs=1)--14157(line=951,offs=30)))
          ## I1VALDCL
          pyxtnm2950 = None
          pyxtnm2950 = XATSP1CN("list_cons", pyxtnm2949[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2949[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14158(line=952,offs=1)--14197(line=953,offs=35)))
          ## I1VALDCL
          pyxtnm2952 = None
          pyxtnm2951 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2949[0+1]), pyxtnm2741))
          pyxtnm2952 = pyxtnm2951
          XATS000_patck(XATS000_ctgeq(pyxtnm2951, XATSCTAG("TVint",0)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14198(line=954,offs=1)--14237(line=955,offs=35)))
          ## I1VALDCL
          pyxtnm2954 = None
          pyxtnm2953 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2950[0+1]), pyxtnm2741))
          pyxtnm2954 = pyxtnm2953
          XATS000_patck(XATS000_ctgeq(pyxtnm2953, XATSCTAG("TVint",0)))
          ## LCSRCsome1(lambda1.dats)@(14082(line=948,offs=10)--14084(line=948,offs=12))
          ## I0Etapq(I0Ecst(sint_neq$sint(923)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gint000.sats)@(2472(line=108,offs=1)--2485(line=108,offs=14))));$list(T2JAG($list())))
          ## T1IMPallx(sint_neq$sint(923), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2466(line=128,offs=1)--2630(line=140,offs=2)))
          ## T1IMPallx(sint_neq$sint(923)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(sint_neq$sint(923);$list()))))
          def pyxtnm2961(arg1, arg2): ## timp: sint_neq$sint(923)
            pyxtnm2955 = arg1
            pyxtnm2956 = arg2
            ## I1CMP:start
            ## let
            pyxtnm2960 = None
            ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/gint000.dats)@(2556(line=136,offs=1)--2628(line=139,offs=39)))
            ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_sint_neq$sint(2583));$list(I1FUNDCL(XATS2PY_sint_neq$sint(4896);$list(FJARGdarg($list(I1BNDcons(I1TNM(2957);I0Pvar(i1(4897));$list(@(i1(4897),I1Vtnm(I1TNM(2957))))),I1BNDcons(I1TNM(2958);I0Pvar(i2(4898));$list(@(i2(4898),I1Vtnm(I1TNM(2958))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_sint_neq$sint);G1Nlist($list())))))))
            pyxtnm2959 = XATSDAPP(XATS2PY_sint_neq_sint(pyxtnm2955, pyxtnm2956))
            pyxtnm2960 = pyxtnm2959
            ## end-of(let)
            ## I1CMP:return:pyxtnm2960
            return pyxtnm2960
          ## endtimp(sint_neq$sint(923))
          pyxtnm2962 = XATSDAPP(pyxtnm2961(XATSP1CN("TVint", pyxtnm2952[0+1]), XATSP1CN("TVint", pyxtnm2954[0+1])))
          pyxtnm2963 = XATSCAPP("TVbtf", [1, pyxtnm2962])
          pyxtnm2964 = pyxtnm2963
          ## end-of(let)
          pyxtnm2997 = pyxtnm2964
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2965);I0Pstr(T_STRN1_clsd("||";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("||"))): ## { // gpt
          pyxtnm2965 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2976 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14256(line=960,offs=1)--14285(line=960,offs=30)))
          ## I1VALDCL
          pyxtnm2966 = None
          pyxtnm2966 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14286(line=961,offs=1)--14315(line=961,offs=30)))
          ## I1VALDCL
          pyxtnm2967 = None
          pyxtnm2967 = XATSP1CN("list_cons", pyxtnm2966[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2966[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14316(line=962,offs=1)--14355(line=963,offs=35)))
          ## I1VALDCL
          pyxtnm2969 = None
          pyxtnm2968 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2966[0+1]), pyxtnm2741))
          pyxtnm2969 = pyxtnm2968
          XATS000_patck(XATS000_ctgeq(pyxtnm2968, XATSCTAG("TVbtf",1)))
          pyxtnm2975 = None
          if (XATSP1CN("TVbtf", pyxtnm2969[0+1])):
            pyxtnm2970 = XATSCAPP("TVbtf", [1, XATSBOOL(True)])
            pyxtnm2975 = pyxtnm2970
          else:
            ## let
            pyxtnm2974 = None
            ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14417(line=972,offs=1)--14456(line=973,offs=35)))
            ## I1VALDCL
            pyxtnm2972 = None
            pyxtnm2971 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2967[0+1]), pyxtnm2741))
            pyxtnm2972 = pyxtnm2971
            XATS000_patck(XATS000_ctgeq(pyxtnm2971, XATSCTAG("TVbtf",1)))
            pyxtnm2973 = XATSCAPP("TVbtf", [1, XATSP1CN("TVbtf", pyxtnm2972[0+1])])
            pyxtnm2974 = pyxtnm2973
            ## end-of(let)
            pyxtnm2975 = pyxtnm2974
          ## end-of(if)
          pyxtnm2976 = pyxtnm2975
          ## end-of(let)
          pyxtnm2997 = pyxtnm2976
          break ## cls
        ## } // gpt
        ## } // cls
        ## { // cls
        ## I1GPTpat(I1BNDcons(I1TNM(2977);I0Pstr(T_STRN1_clsd("&&";4));$list()))
        if (XATS000_streq(XATSP1CN("TMopr", pyxtnm2777[0+1]), XATSSTRN("&&"))): ## { // gpt
          pyxtnm2977 = XATSP1CN("TMopr", pyxtnm2777[0+1])
          ## let
          pyxtnm2996 = None
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14486(line=979,offs=1)--14515(line=979,offs=30)))
          ## I1VALDCL
          pyxtnm2978 = None
          pyxtnm2978 = XATSP1CN("TMopr", pyxtnm2777[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("TMopr", pyxtnm2777[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14516(line=980,offs=1)--14545(line=980,offs=30)))
          ## I1VALDCL
          pyxtnm2979 = None
          pyxtnm2979 = XATSP1CN("list_cons", pyxtnm2978[1+1])
          XATS000_patck(XATS000_ctgeq(XATSP1CN("list_cons", pyxtnm2978[1+1]), XATSCTAG("list_cons",1)))
          ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14546(line=981,offs=1)--14585(line=982,offs=35)))
          ## I1VALDCL
          pyxtnm2981 = None
          pyxtnm2980 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2978[0+1]), pyxtnm2741))
          pyxtnm2981 = pyxtnm2980
          XATS000_patck(XATS000_ctgeq(pyxtnm2980, XATSCTAG("TVbtf",1)))
          ## LCSRCsome1(lambda1.dats)@(14601(line=986,offs=2)--14602(line=986,offs=3))
          ## I0Etapq(I0Ecst(bool_neg(857)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/bool000.sats)@(1748(line=63,offs=1)--1756(line=63,offs=9))));$list(T2JAG($list())))
          ## T1IMPallx(bool_neg(857), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1851(line=70,offs=1)--1916(line=74,offs=30)))
          ## T1IMPallx(bool_neg(857)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(bool_neg(857);$list()))))
          def pyxtnm2984(arg1): ## timp: bool_neg(857)
            pyxtnm2982 = arg1
            ## I1CMP:start
            pyxtnm2983 = None
            if (pyxtnm2982):
              pyxtnm2983 = XATSBOOL(False)
            else:
              pyxtnm2983 = XATSBOOL(True)
            ## end-of(if)
            ## I1CMP:return:pyxtnm2983
            return pyxtnm2983
          ## endtimp(bool_neg(857))
          pyxtnm2985 = XATSDAPP(pyxtnm2984(XATSP1CN("TVbtf", pyxtnm2981[0+1])))
          pyxtnm2995 = None
          if (pyxtnm2985):
            ## LCSRCsome1(lambda1.dats)@(14618(line=988,offs=7)--14619(line=988,offs=8))
            ## I0Etapq(I0Ecst(bool_neg(857)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/bool000.sats)@(1748(line=63,offs=1)--1756(line=63,offs=9))));$list(T2JAG($list())))
            ## T1IMPallx(bool_neg(857), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/bool000.dats)@(1851(line=70,offs=1)--1916(line=74,offs=30)))
            ## T1IMPallx(bool_neg(857)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(bool_neg(857);$list()))))
            def pyxtnm2988(arg1): ## timp: bool_neg(857)
              pyxtnm2986 = arg1
              ## I1CMP:start
              pyxtnm2987 = None
              if (pyxtnm2986):
                pyxtnm2987 = XATSBOOL(False)
              else:
                pyxtnm2987 = XATSBOOL(True)
              ## end-of(if)
              ## I1CMP:return:pyxtnm2987
              return pyxtnm2987
            ## endtimp(bool_neg(857))
            pyxtnm2989 = XATSDAPP(pyxtnm2988(XATSBOOL(True)))
            pyxtnm2990 = XATSCAPP("TVbtf", [1, pyxtnm2989])
            pyxtnm2995 = pyxtnm2990
          else:
            ## let
            pyxtnm2994 = None
            ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14649(line=991,offs=1)--14688(line=992,offs=35)))
            ## I1VALDCL
            pyxtnm2992 = None
            pyxtnm2991 = XATSDAPP(term_eval01_11014(XATSP1CN("list_cons", pyxtnm2979[0+1]), pyxtnm2741))
            pyxtnm2992 = pyxtnm2991
            XATS000_patck(XATS000_ctgeq(pyxtnm2991, XATSCTAG("TVbtf",1)))
            pyxtnm2993 = XATSCAPP("TVbtf", [1, XATSP1CN("TVbtf", pyxtnm2992[0+1])])
            pyxtnm2994 = pyxtnm2993
            ## end-of(let)
            pyxtnm2995 = pyxtnm2994
          ## end-of(if)
          pyxtnm2996 = pyxtnm2995
          ## end-of(let)
          pyxtnm2997 = pyxtnm2996
          break ## cls
        ## } // gpt
        ## } // cls
        XATS000_cfail()
      ## } while True // end-of(do-cls)
      pyxtnm3011 = pyxtnm2997
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(2998);I0Pdapp(I0Pcon(TMif0(38));$list(I0Pvar(tm1(5488)),I0Pvar(tm2(5489)),I0Pvar(tm3(5490))));$list(@(tm1(5488),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(2998));0)),@(tm2(5489),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(2998));1)),@(tm3(5490),I1Vp1cn(I0Pcon(TMif0(38));I1Vtnm(I1TNM(2998));2)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMif0",6))): ## { // gpt
      pyxtnm2998 = pyxtnm2740
      ## let
      pyxtnm3003 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14775(line=1002,offs=1)--14814(line=1004,offs=22)))
      ## I1VALDCL
      pyxtnm3000 = None
      pyxtnm2999 = XATSDAPP(term_eval01_11014(XATSP1CN("TMif0", pyxtnm2998[0+1]), pyxtnm2741))
      pyxtnm3000 = pyxtnm2999
      XATS000_patck(XATS000_ctgeq(pyxtnm2999, XATSCTAG("TVbtf",1)))
      pyxtnm3001 = None
      if (XATSP1CN("TVbtf", pyxtnm3000[0+1])):
        pyxtnm3001 = XATSP1CN("TMif0", pyxtnm2998[1+1])
      else:
        pyxtnm3001 = XATSP1CN("TMif0", pyxtnm2998[2+1])
      ## end-of(if)
      pyxtnm3002 = XATSDAPP(term_eval01_11014(pyxtnm3001, pyxtnm2741))
      pyxtnm3003 = pyxtnm3002
      ## end-of(let)
      pyxtnm3011 = pyxtnm3003
      break ## cls
    ## } // gpt
    ## } // cls
    ## { // cls
    ## I1GPTpat(I1BNDcons(I1TNM(3004);I0Pdapp(I0Pcon(TMlet(40));$list(I0Pvar(x01(5492)),I0Pvar(tm1(5493)),I0Pvar(tm2(5494))));$list(@(x01(5492),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(3004));0)),@(tm1(5493),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(3004));1)),@(tm2(5494),I1Vp1cn(I0Pcon(TMlet(40));I1Vtnm(I1TNM(3004));2)))))
    if (XATS000_ctgeq(pyxtnm2740, XATSCTAG("TMlet",8))): ## { // gpt
      pyxtnm3004 = pyxtnm2740
      ## let
      pyxtnm3010 = None
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14942(line=1017,offs=1)--14973(line=1017,offs=32)))
      ## I1VALDCL
      pyxtnm3006 = None
      pyxtnm3005 = XATSDAPP(term_eval01_11014(XATSP1CN("TMlet", pyxtnm3004[1+1]), pyxtnm2741))
      pyxtnm3006 = pyxtnm3005
      XATS000_patck(True)
      ## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(14974(line=1018,offs=1)--15005(line=1018,offs=32)))
      ## I1VALDCL
      pyxtnm3008 = None
      pyxtnm3007 = XATSCAPP("EVcons", [1, XATSP1CN("TMlet", pyxtnm3004[0+1]), pyxtnm3006, pyxtnm2741])
      pyxtnm3008 = pyxtnm3007
      XATS000_patck(True)
      pyxtnm3009 = XATSDAPP(term_eval01_11014(XATSP1CN("TMlet", pyxtnm3004[2+1]), pyxtnm3008))
      pyxtnm3010 = pyxtnm3009
      ## end-of(let)
      pyxtnm3011 = pyxtnm3010
      break ## cls
    ## } // gpt
    ## } // cls
    XATS000_cfail()
  ## } while True // end-of(do-cls)
  pyxtnm3012 = pyxtnm3011
  ## end-of(let)
  ## I1CMP:return:pyxtnm3012
  return pyxtnm3012
## endfun(impl)
## I1Dvaldclist(LCSRCsome1(lambda1.dats)@(15167(line=1033,offs=1)--15255(line=1034,offs=71)))
## I1VALDCL
pyxtnm3051 = None
## LCSRCsome1(lambda1.dats)@(15176(line=1033,offs=10)--15184(line=1033,offs=18))
## I0Etapq(I0Ecst(gs_println_a2(811)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(13791(line=896,offs=1)--13804(line=896,offs=14))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(tval)))))
## T1IMPallx(gs_println_a2(811), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26238(line=1586,offs=1)--26339(line=1592,offs=45)))
## T1IMPallx(gs_println_a2(811)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(tval))))>;I1Dtmpsub($list(@(x0[6904],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6905],T2Pcst(tval)));I1Dimplmnt0(DIMPLone2(gs_println_a2(811);$list(@(x0[2472],T2Pvar(x0[6904])),@(x1[2473],T2Pvar(x1[6905])))))))
def pyxtnm3046(arg1, arg2): ## timp: gs_println_a2(811)
  pyxtnm3013 = arg1
  pyxtnm3014 = arg2
  ## I1CMP:start
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26297(line=1592,offs=3)--26308(line=1592,offs=14))
  ## I0Etapq(I0Ecst(gs_print_a2(798)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11802(line=749,offs=1)--11813(line=749,offs=12))));$list(T2JAG($list(T2Pvar(x0[6904]))),T2JAG($list(T2Pvar(x1[6905])))))
  ## T1IMPallx(gs_print_a2(798), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21155(line=1303,offs=1)--21318(line=1314,offs=4)))
  ## T1IMPallx(gs_print_a2(798)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))),T2JAG($list(T2Pcst(tval))))>;I1Dtmpsub($list(@(x0[6826],T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))),@(x1[6827],T2Pcst(tval)));I1Dimplmnt0(DIMPLone2(gs_print_a2(798);$list(@(x0[2394],T2Pvar(x0[6826])),@(x1[2395],T2Pvar(x1[6827])))))))
  def pyxtnm3037(arg1, arg2): ## timp: gs_print_a2(798)
    pyxtnm3015 = arg1
    pyxtnm3016 = arg2
    ## I1CMP:start
    ## let
    pyxtnm3036 = None
    ## I1Dvaldclist(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21212(line=1309,offs=1)--21235(line=1310,offs=15)))
    ## I1VALDCL
    pyxtnm3020 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21221(line=1310,offs=1)--21233(line=1310,offs=13))
    ## I0Etapq(I0Ecst(gs_print$beg(793)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11602(line=730,offs=1)--11614(line=730,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$beg(793), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20721(line=1268,offs=1)--20759(line=1270,offs=20)))
    ## T1IMPallx(gs_print$beg(793)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$beg(793);$list()))))
    def pyxtnm3018(): ## timp: gs_print$beg(793)
      ## I1CMP:start
      pyxtnm3017 = XATSTUP0([])
      ## I1CMP:return:pyxtnm3017
      return pyxtnm3017
    ## endtimp(gs_print$beg(793))
    pyxtnm3019 = XATSDAPP(pyxtnm3018())
    pyxtnm3020 = pyxtnm3019
    XATS000_patck(True)
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21248(line=1312,offs=3)--21255(line=1312,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x0[6826])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
    pyxtnm3026 = None
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
    ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
    ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
    ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
    def pyxtnm3025(arg1): ## timp: strn_print(1029)
      pyxtnm3021 = arg1
      ## I1CMP:start
      ## let
      pyxtnm3024 = None
      ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
      ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(3022);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(3022))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
      pyxtnm3023 = XATSDAPP(XATS2PY_strn_print(pyxtnm3021))
      pyxtnm3024 = pyxtnm3023
      ## end-of(let)
      ## I1CMP:return:pyxtnm3024
      return pyxtnm3024
    ## endtimp(strn_print(1029))
    pyxtnm3026 = pyxtnm3025
    pyxtnm3027 = XATSDAPP(pyxtnm3026(pyxtnm3015))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21265(line=1312,offs=20)--21277(line=1312,offs=32))
    ## I0Etapq(I0Ecst(gs_print$sep(794)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11637(line=733,offs=1)--11649(line=733,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$sep(794), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20760(line=1271,offs=1)--20798(line=1273,offs=20)))
    ## T1IMPallx(gs_print$sep(794)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$sep(794);$list()))))
    def pyxtnm3029(): ## timp: gs_print$sep(794)
      ## I1CMP:start
      pyxtnm3028 = XATSTUP0([])
      ## I1CMP:return:pyxtnm3028
      return pyxtnm3028
    ## endtimp(gs_print$sep(794))
    pyxtnm3030 = XATSDAPP(pyxtnm3029())
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21282(line=1313,offs=3)--21289(line=1313,offs=10))
    ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Pvar(x1[6827])))))
    ## T1IMPallx(g_print(39), LCSRCsome1(lambda1.dats)@(10867(line=708,offs=1)--10904(line=708,offs=38)))
    ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Pcst(tval))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(tval)))))))
    pyxtnm3031 = None
    pyxtnm3031 = pyxtnm2702
    pyxtnm3032 = XATSDAPP(pyxtnm3031(pyxtnm3016))
    ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(21299(line=1313,offs=20)--21311(line=1313,offs=32))
    ## I0Etapq(I0Ecst(gs_print$end(795)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gsyn000.sats)@(11672(line=736,offs=1)--11684(line=736,offs=13))));$list(T2JAG($list())))
    ## T1IMPallx(gs_print$end(795), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(20799(line=1274,offs=1)--20837(line=1276,offs=20)))
    ## T1IMPallx(gs_print$end(795)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(gs_print$end(795);$list()))))
    def pyxtnm3034(): ## timp: gs_print$end(795)
      ## I1CMP:start
      pyxtnm3033 = XATSTUP0([])
      ## I1CMP:return:pyxtnm3033
      return pyxtnm3033
    ## endtimp(gs_print$end(795))
    pyxtnm3035 = XATSDAPP(pyxtnm3034())
    pyxtnm3036 = pyxtnm3035
    ## end-of(let)
    ## I1CMP:return:pyxtnm3036
    return pyxtnm3036
  ## endtimp(gs_print_a2(798))
  pyxtnm3038 = XATSDAPP(pyxtnm3037(pyxtnm3013, pyxtnm3014))
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/gsyn000.dats)@(26325(line=1592,offs=31)--26332(line=1592,offs=38))
  ## I0Etapq(I0Ecst(g_print(39)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/gbas000.sats)@(2820(line=170,offs=1)--2827(line=170,offs=8))));$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0()))))))
  ## T1IMPallx(g_print(39), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2143(line=94,offs=1)--2180(line=95,offs=29)))
  ## T1IMPallx(g_print(39)<$list(T2JAG($list(T2Papps(T2Pcst(string_i0_tx);$list(T2Pnone0())))))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(g_print(39);$list(@(x0[381],T2Pcst(strn)))))))
  pyxtnm3044 = None
  ## LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/strn000.dats)@(2168(line=95,offs=17)--2178(line=95,offs=27))
  ## I0Etapq(I0Ecst(strn_print(1029)(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/SATS/strn000.sats)@(2592(line=122,offs=1)--2602(line=122,offs=11))));$list(T2JAG($list())))
  ## T1IMPallx(strn_print(1029), LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1819(line=74,offs=1)--1959(line=85,offs=2)))
  ## T1IMPallx(strn_print(1029)<$list(T2JAG($list()))>;I1Dtmpsub($list();I1Dimplmnt0(DIMPLone2(strn_print(1029);$list()))))
  def pyxtnm3043(arg1): ## timp: strn_print(1029)
    pyxtnm3039 = arg1
    ## I1CMP:start
    ## let
    pyxtnm3042 = None
    ## I1Dextern(LCSRCsome1(/home/hwxi/Research/githwxi/XATSHOME/prelude/DATS/CATS/PY/strn000.dats)@(1899(line=82,offs=1)--1957(line=84,offs=47)))
    ## I1Dfundclst(T_FUN(FNKfn1);$list();$list(XATS2PY_strn_print(2613));$list(I1FUNDCL(XATS2PY_strn_print(5021);$list(FJARGdarg($list(I1BNDcons(I1TNM(3040);I0Pvar(cs(5022));$list(@(cs(5022),I1Vtnm(I1TNM(3040))))))));TEQI1CMPsome(T_EQ0();I1CMPcons($list();I1Vextnam(T_DLR_EXTNAM();I1Vvar(XATS2PY_strn_print);G1Nlist($list())))))))
    pyxtnm3041 = XATSDAPP(XATS2PY_strn_print(pyxtnm3039))
    pyxtnm3042 = pyxtnm3041
    ## end-of(let)
    ## I1CMP:return:pyxtnm3042
    return pyxtnm3042
  ## endtimp(strn_print(1029))
  pyxtnm3044 = pyxtnm3043
  pyxtnm3045 = XATSDAPP(pyxtnm3044(XATSSTRN("\n")))
  ## I1CMP:return:pyxtnm3045
  return pyxtnm3045
## endtimp(gs_println_a2(811))
pyxtnm3047 = XATSCAPP("TMint", [0, XATSINT1(5)])
pyxtnm3048 = XATSCAPP("TMapp", [4, pyxtnm2491, pyxtnm3047])
pyxtnm3049 = XATSDAPP(term_eval00_10973(pyxtnm3048))
pyxtnm3050 = XATSDAPP(pyxtnm3046(XATSSTRN("TMapp(TMfact2, TMint(5)) = "), pyxtnm3049))
pyxtnm3051 = pyxtnm3050
XATS000_patck(True)
## LCSRCsome1(lambda1.dats)@(15302(line=1039,offs=1)--15321(line=1040,offs=16))
## I1Dnone1(I0Dnone1(LCSRCsome1(lambda1.dats)@(15302(line=1039,offs=1)--15321(line=1040,offs=16));D3Cnone0()))
## LCSRCsome1(lambda1.dats)@(15692(line=1053,offs=1)--15692(line=1053,offs=1))
## I1Dnone1(I0Dnone1(LCSRCsome1(lambda1.dats)@(15692(line=1053,offs=1)--15692(line=1053,offs=1));D3Cnone0()))

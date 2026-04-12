import sys
sys.setrecursionlimit(10000)

##################################################################
# datatype styp =
# | STbas  of strn
# | STxyz  of ref(optn(styp))   # existential variable for inference
# | STtup  of (styp, styp)
# | STfun  of (styp, styp)
# | STlazy of styp
# | STlist of styp
# | STarry of styp
# | STstcn of styp
##################################################################

class styp:
    ctag = ""
    def __str__(self):
        return "styp(" + self.ctag + ")"

class styp_bas(styp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "STbas"
    def __str__(self):
        return "STbas(" + self.arg1 + ")"

class styp_xyz(styp):
    nvar = 0
    def __init__(self):
        self.arg1 = None
        self.stmp = styp_xyz.nvar
        styp_xyz.nvar += 1
        self.ctag = "STxyz"
    def __str__(self):
        st1 = prune(self)
        if st1 is not self:
            return str(st1)
        return "STxyz(" + str(self.stmp) + ")"

class styp_tup(styp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "STtup"
    def __str__(self):
        return "STtup(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class styp_fun(styp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "STfun"
    def __str__(self):
        return "STfun(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class styp_lazy(styp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "STlazy"
    def __str__(self):
        return "STlazy(" + str(self.arg1) + ")"

class styp_list(styp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "STlist"
    def __str__(self):
        return "STlist(" + str(self.arg1) + ")"

class styp_arry(styp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "STarry"
    def __str__(self):
        return "STarry(" + str(self.arg1) + ")"

class styp_stcn(styp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "STstcn"
    def __str__(self):
        return "STstcn(" + str(self.arg1) + ")"

styp_int = styp_bas("int")
styp_bool = styp_bas("bool")
styp_str = styp_bas("string")

def styp_new():
    return styp_xyz()

def prune(st0):
    if st0.ctag == "STxyz" and st0.arg1 is not None:
        st0.arg1 = prune(st0.arg1)
        return st0.arg1
    return st0

def occurs(stv, st0):
    st0 = prune(st0)
    if st0 is stv:
        return True
    if st0.ctag == "STtup" or st0.ctag == "STfun":
        return occurs(stv, st0.arg1) or occurs(stv, st0.arg2)
    if st0.ctag in ("STlazy", "STlist", "STarry", "STstcn"):
        return occurs(stv, st0.arg1)
    return False

def unify(st1, st2):
    st1 = prune(st1)
    st2 = prune(st2)
    if st1 is st2:
        return
    if st1.ctag == "STxyz":
        if occurs(st1, st2):
            raise TypeError("occurs check failed: " + str(st1) + " in " + str(st2))
        st1.arg1 = st2
        return
    if st2.ctag == "STxyz":
        if occurs(st2, st1):
            raise TypeError("occurs check failed: " + str(st2) + " in " + str(st1))
        st2.arg1 = st1
        return
    if st1.ctag != st2.ctag:
        raise TypeError("type mismatch: " + str(st1) + " <> " + str(st2))
    if st1.ctag == "STbas":
        if st1.arg1 != st2.arg1:
            raise TypeError("type mismatch: " + str(st1) + " <> " + str(st2))
        return
    if st1.ctag == "STtup" or st1.ctag == "STfun":
        unify(st1.arg1, st2.arg1)
        unify(st1.arg2, st2.arg2)
        return
    if st1.ctag in ("STlazy", "STlist", "STarry", "STstcn"):
        unify(st1.arg1, st2.arg1)
        return
    raise TypeError("unify: deadcode")

##################################################################
# datatype dexp =
# | DEint of int
# | DEbtf of bool
# | DEstr of strn
# | DEvar of strn
# | DElam of (strn, dexp)
# | DEapp of (dexp, dexp)
# | DEopr of (strn, list(dexp))
# | DEfst of dexp
# | DEsnd of dexp
# | DEtup of (dexp, dexp)
# | DEif0 of (dexp, dexp, dexp)
# | DEfix of (strn, strn, dexp)
# | DElet of (strn, dexp, dexp)
# | DElist_nil of ()
# | DElist_cons of (dexp, dexp)
# | DElazy of dexp
# | DEstcn_nil of ()
# | DEstcn_cons of (dexp, dexp)
# | DEarry_size$val of (dexp, dexp)
# | DEarry_size$fun of (dexp, dexp)
# | DEanno of (dexp, styp)
# | DElam1 of (strn, styp, dexp)
# | DEfix1 of (strn, strn, styp, dexp, styp)
##################################################################

class dexp:
    ctag = ""
    def __str__(self):
        return "dexp(" + self.ctag + ")"

class dexp_int(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DEint"
    def __str__(self):
        return "DEint(" + str(self.arg1) + ")"

class dexp_btf(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DEbtf"
    def __str__(self):
        return "DEbtf(" + str(self.arg1) + ")"

class dexp_str(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DEstr"
    def __str__(self):
        return "DEstr(" + str(self.arg1) + ")"

class dexp_var(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DEvar"
    def __str__(self):
        return "DEvar(" + self.arg1 + ")"

class dexp_lam(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DElam"
    def __str__(self):
        return "DElam(" + self.arg1 + ";" + str(self.arg2) + ")"

class dexp_lam1(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "DElam1"
    def __str__(self):
        return "DElam1(" + self.arg1 + ";" + str(self.arg2) + ";" + str(self.arg3) + ")"

class dexp_app(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEapp"
    def __str__(self):
        return "DEapp(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class dexp_opr(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEopr"
    def __str__(self):
        return "DEopr(" + self.arg1 + ";" + str(self.arg2) + ")"

class dexp_fst(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DEfst"
    def __str__(self):
        return "DEfst(" + str(self.arg1) + ")"

class dexp_snd(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DEsnd"
    def __str__(self):
        return "DEsnd(" + str(self.arg1) + ")"

class dexp_tup(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEtup"
    def __str__(self):
        return "DEtup(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class dexp_if0(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "DEif0"
    def __str__(self):
        return "DEif0(" + str(self.arg1) + ";" + str(self.arg2) + ";" + str(self.arg3) + ")"

class dexp_fix(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "DEfix"
    def __str__(self):
        return "DEfix(" + self.arg1 + ";" + self.arg2 + ";" + str(self.arg3) + ")"

class dexp_fix1(dexp):
    def __init__(self, arg1, arg2, arg3, arg4, arg5):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.arg4 = arg4
        self.arg5 = arg5
        self.ctag = "DEfix1"
    def __str__(self):
        return "DEfix1(" + self.arg1 + ";" + self.arg2 + ";" + str(self.arg3) + ";" + str(self.arg4) + ";" + str(self.arg5) + ")"

class dexp_let(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "DElet"
    def __str__(self):
        return "DElet(" + self.arg1 + ";" + str(self.arg2) + ";" + str(self.arg3) + ")"

class dexp_list_nil(dexp):
    def __init__(self):
        self.ctag = "DElist_nil"
    def __str__(self):
        return "DElist_nil()"

class dexp_list_cons(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DElist_cons"
    def __str__(self):
        return "DElist_cons(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class dexp_lazy(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "DElazy"
    def __str__(self):
        return "DElazy(" + str(self.arg1) + ")"

class dexp_stcn_nil(dexp):
    def __init__(self):
        self.ctag = "DEstcn_nil"
    def __str__(self):
        return "DEstcn_nil()"

class dexp_stcn_cons(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEstcn_cons"
    def __str__(self):
        return "DEstcn_cons(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class dexp_arry_size_val(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEarry_size$val"
    def __str__(self):
        return "DEarry_size$val(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class dexp_arry_size_fun(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEarry_size$fun"
    def __str__(self):
        return "DEarry_size$fun(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class dexp_anno(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "DEanno"
    def __str__(self):
        return "DEanno(" + str(self.arg1) + ";" + str(self.arg2) + ")"

##################################################################
# datatype tctx =
# | CXnil of ()
# | CXcons of (strn, styp, tctx)
##################################################################

class tctx:
    ctag = ""
    def __str__(self):
        return "tctx(" + self.ctag + ")"

class tctx_nil(tctx):
    def __init__(self):
        self.ctag = "CXnil"
    def __str__(self):
        return "CXnil()"

class tctx_cons(tctx):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1
        self.arg2 = arg2
        self.arg3 = arg3
        self.ctag = "CXcons"
    def __str__(self):
        return "CXcons(" + self.arg1 + ";" + str(self.arg2) + ";" + str(self.arg3) + ")"


def tctx_search(ctx, x00):
    if ctx.ctag == "CXnil":
        return None
    if ctx.ctag == "CXcons":
        if ctx.arg1 == x00:
            return ctx.arg2
        return tctx_search(ctx.arg3, x00)
    raise TypeError(ctx)

##################################################################
# type inference
##################################################################

def dexp_tinfer(de0):
    return prune(dexp_tinfer1(de0, tctx_nil()))


def dexp_tinfer_opr(pnm, ags, ctx):
    if pnm in ["+", "-", "*", "/", "%", "cmp"]:
        assert len(ags) == 2
        st1 = dexp_tinfer1(ags[0], ctx)
        st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_int)
        unify(st2, styp_int)
        return styp_int
    if pnm in ["<", ">", "=", "<=", ">=", "!="]:
        assert len(ags) == 2
        st1 = dexp_tinfer1(ags[0], ctx)
        st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_int)
        unify(st2, styp_int)
        return styp_bool
    if pnm in ["and", "or", "&&", "||"]:
        assert len(ags) == 2
        st1 = dexp_tinfer1(ags[0], ctx)
        st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_bool)
        unify(st2, styp_bool)
        return styp_bool
    if pnm in ["not", "!"]:
        assert len(ags) == 1
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_bool)
        return styp_bool
    if pnm in ["strcat", "^"]:
        assert len(ags) == 2
        st1 = dexp_tinfer1(ags[0], ctx)
        st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_str)
        unify(st2, styp_str)
        return styp_str
    if pnm == "list_head":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_list(stv))
        return stv
    if pnm == "list_tail":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_list(stv))
        return styp_list(stv)
    if pnm == "list_is_nil":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_list(stv))
        return styp_bool
    if pnm == "lazy_force":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_lazy(stv))
        return stv
    if pnm == "stream_head":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_stcn(stv))
        return stv
    if pnm == "stream_tail":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_stcn(stv))
        return styp_lazy(styp_stcn(stv))
    if pnm == "array_get":
        assert len(ags) == 2
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_arry(stv))
        unify(st2, styp_int)
        return stv
    if pnm == "array_set":
        assert len(ags) == 3
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        st2 = dexp_tinfer1(ags[1], ctx)
        st3 = dexp_tinfer1(ags[2], ctx)
        unify(st1, styp_arry(stv))
        unify(st2, styp_int)
        unify(st3, stv)
        return styp_arry(stv)
    if pnm == "array_length":
        assert len(ags) == 1
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_arry(stv))
        return styp_int
    raise TypeError("unknown operator: " + pnm)


def dexp_tinfer1(de0, ctx):
    if de0.ctag == "DEint":
        return styp_int
    if de0.ctag == "DEbtf":
        return styp_bool
    if de0.ctag == "DEstr":
        return styp_str
    if de0.ctag == "DEvar":
        st0 = tctx_search(ctx, de0.arg1)
        assert st0 is not None
        return st0
    if de0.ctag == "DElam":
        x01 = de0.arg1
        st1 = styp_new()
        ctx1 = tctx_cons(x01, st1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx1)
        return styp_fun(st1, st2)
    if de0.ctag == "DElam1":
        x01 = de0.arg1
        st1 = de0.arg2
        ctx1 = tctx_cons(x01, st1, ctx)
        st2 = dexp_tinfer1(de0.arg3, ctx1)
        return styp_fun(st1, st2)
    if de0.ctag == "DEapp":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        st3 = styp_new()
        unify(st1, styp_fun(st2, st3))
        return st3
    if de0.ctag == "DEopr":
        return dexp_tinfer_opr(de0.arg1, de0.arg2, ctx)
    if de0.ctag == "DEtup":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        return styp_tup(st1, st2)
    if de0.ctag == "DEfst":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = styp_new()
        st3 = styp_new()
        unify(st1, styp_tup(st2, st3))
        return st2
    if de0.ctag == "DEsnd":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = styp_new()
        st3 = styp_new()
        unify(st1, styp_tup(st2, st3))
        return st3
    if de0.ctag == "DEif0":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        unify(st1, styp_bool)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        st3 = dexp_tinfer1(de0.arg3, ctx)
        unify(st2, st3)
        return st2
    if de0.ctag == "DEfix":
        f00 = de0.arg1
        x01 = de0.arg2
        st1 = styp_new()
        st2 = styp_new()
        stf = styp_fun(st1, st2)
        ctx1 = tctx_cons(f00, stf, ctx)
        ctx2 = tctx_cons(x01, st1, ctx1)
        stx = dexp_tinfer1(de0.arg3, ctx2)
        unify(st2, stx)
        return stf
    if de0.ctag == "DEfix1":
        f00 = de0.arg1
        x01 = de0.arg2
        st1 = de0.arg3
        st2 = de0.arg5
        stf = styp_fun(st1, st2)
        ctx1 = tctx_cons(f00, stf, ctx)
        ctx2 = tctx_cons(x01, st1, ctx1)
        stx = dexp_tinfer1(de0.arg4, ctx2)
        unify(st2, stx)
        return stf
    if de0.ctag == "DElet":
        x01 = de0.arg1
        st1 = dexp_tinfer1(de0.arg2, ctx)
        ctx1 = tctx_cons(x01, st1, ctx)
        return dexp_tinfer1(de0.arg3, ctx1)
    if de0.ctag == "DElist_nil":
        return styp_list(styp_new())
    if de0.ctag == "DElist_cons":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        unify(st2, styp_list(st1))
        return styp_list(st1)
    if de0.ctag == "DElazy":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        return styp_lazy(st1)
    if de0.ctag == "DEstcn_nil":
        return styp_stcn(styp_new())
    if de0.ctag == "DEstcn_cons":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        unify(st2, styp_lazy(styp_stcn(st1)))
        return styp_stcn(st1)
    if de0.ctag == "DEarry_size$val":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        unify(st1, styp_int)
        return styp_arry(st2)
    if de0.ctag == "DEarry_size$fun":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx)
        st3 = styp_new()
        unify(st1, styp_int)
        unify(st2, styp_fun(styp_int, st3))
        return styp_arry(st3)
    if de0.ctag == "DEanno":
        st1 = dexp_tinfer1(de0.arg1, ctx)
        st2 = de0.arg2
        unify(st1, st2)
        return st2
    raise TypeError(de0)

##################################################################
# JS code generation (simple direct transpiler)
# The lecture code builds Python through an IR. For submission purposes,
# this function directly generates JavaScript source code.
##################################################################


def js_escape(s):
    return repr(s).replace("'", '"')


def dexp_trx2js(de0):
    return dexp_trx2js1(de0)


def dexp_trx2js_opr(pnm, ags):
    ss = [dexp_trx2js1(x) for x in ags]
    if pnm == "=":
        pnm = "==="
    if pnm == "and":
        pnm = "&&"
    if pnm == "or":
        pnm = "||"
    if pnm == "not":
        return "(!" + ss[0] + ")"
    if pnm == "strcat" or pnm == "^":
        return "(" + ss[0] + " + " + ss[1] + ")"
    if pnm in ["+", "-", "*", "/", "%", "<", ">", "<=", ">=", "===", "!=", "&&", "||"]:
        return "(" + ss[0] + " " + pnm + " " + ss[1] + ")"
    if pnm == "list_head":
        return "(" + ss[0] + ")[0]"
    if pnm == "list_tail":
        return "(" + ss[0] + ").slice(1)"
    if pnm == "list_is_nil":
        return "((" + ss[0] + ").length === 0)"
    if pnm == "lazy_force":
        return "(" + ss[0] + ")()"
    if pnm == "stream_head":
        return "(" + ss[0] + ").head"
    if pnm == "stream_tail":
        return "(" + ss[0] + ").tail"
    if pnm == "array_get":
        return "(" + ss[0] + ")[" + ss[1] + "]"
    if pnm == "array_set":
        return "((" + ss[0] + ")[" + ss[1] + "] = " + ss[2] + ", " + ss[0] + ")"
    if pnm == "array_length":
        return "(" + ss[0] + ").length"
    raise TypeError("unknown JS operator: " + pnm)


def dexp_trx2js1(de0):
    if de0.ctag == "DEint":
        return str(de0.arg1)
    if de0.ctag == "DEbtf":
        return "true" if de0.arg1 else "false"
    if de0.ctag == "DEstr":
        return js_escape(de0.arg1)
    if de0.ctag == "DEvar":
        return de0.arg1
    if de0.ctag == "DElam":
        return "((" + de0.arg1 + ") => " + dexp_trx2js1(de0.arg2) + ")"
    if de0.ctag == "DElam1":
        return "((" + de0.arg1 + ") => " + dexp_trx2js1(de0.arg3) + ")"
    if de0.ctag == "DEapp":
        return "(" + dexp_trx2js1(de0.arg1) + ")(" + dexp_trx2js1(de0.arg2) + ")"
    if de0.ctag == "DEopr":
        return dexp_trx2js_opr(de0.arg1, de0.arg2)
    if de0.ctag == "DEfst":
        return "(" + dexp_trx2js1(de0.arg1) + ")[0]"
    if de0.ctag == "DEsnd":
        return "(" + dexp_trx2js1(de0.arg1) + ")[1]"
    if de0.ctag == "DEtup":
        return "[" + dexp_trx2js1(de0.arg1) + ", " + dexp_trx2js1(de0.arg2) + "]"
    if de0.ctag == "DEif0":
        return "(" + dexp_trx2js1(de0.arg1) + " ? " + dexp_trx2js1(de0.arg2) + " : " + dexp_trx2js1(de0.arg3) + ")"
    if de0.ctag == "DEfix":
        f00 = de0.arg1
        x01 = de0.arg2
        body = de0.arg3
        return "(() => { const " + f00 + " = (" + x01 + ") => " + dexp_trx2js1(body) + "; return " + f00 + "; })()"
    if de0.ctag == "DEfix1":
        f00 = de0.arg1
        x01 = de0.arg2
        body = de0.arg4
        return "(() => { const " + f00 + " = (" + x01 + ") => " + dexp_trx2js1(body) + "; return " + f00 + "; })()"
    if de0.ctag == "DElet":
        return "((" + de0.arg1 + ") => " + dexp_trx2js1(de0.arg3) + ")(" + dexp_trx2js1(de0.arg2) + ")"
    if de0.ctag == "DElist_nil":
        return "[]"
    if de0.ctag == "DElist_cons":
        return "[" + dexp_trx2js1(de0.arg1) + "].concat(" + dexp_trx2js1(de0.arg2) + ")"
    if de0.ctag == "DElazy":
        ejs = dexp_trx2js1(de0.arg1)
        return "(() => { let __memo = false; let __value; return () => { if(!__memo){ __value = " + ejs + "; __memo = true; } return __value; }; })()"
    if de0.ctag == "DEstcn_nil":
        return "null"
    if de0.ctag == "DEstcn_cons":
        return "({ tag: 'cons', head: " + dexp_trx2js1(de0.arg1) + ", tail: " + dexp_trx2js1(de0.arg2) + " })"
    if de0.ctag == "DEarry_size$val":
        return "Array(" + dexp_trx2js1(de0.arg1) + ").fill(" + dexp_trx2js1(de0.arg2) + ")"
    if de0.ctag == "DEarry_size$fun":
        return "Array.from({length: " + dexp_trx2js1(de0.arg1) + "}, (_,i) => (" + dexp_trx2js1(de0.arg2) + ")(i))"
    if de0.ctag == "DEanno":
        return dexp_trx2js1(de0.arg1)
    raise TypeError(de0)

##################################################################
# examples
##################################################################

if __name__ == "__main__":
    var_x = dexp_var("x")
    id0 = dexp_lam("x", var_x)
    print("tinfer(id0) = " + str(dexp_tinfer(id0)))
    print("js(id0) = " + dexp_trx2js(id0))

    pair0 = dexp_tup(dexp_int(1), dexp_btf(True))
    print("tinfer(pair0) = " + str(dexp_tinfer(pair0)))
    print("js(pair0) = " + dexp_trx2js(pair0))

    fact = dexp_fix1(
        "fact", "n", styp_int,
        dexp_if0(
            dexp_opr("<=", [dexp_var("n"), dexp_int(0)]),
            dexp_int(1),
            dexp_opr("*", [
                dexp_var("n"),
                dexp_app(dexp_var("fact"), dexp_opr("-", [dexp_var("n"), dexp_int(1)]))
            ])
        ),
        styp_int
    )
    print("tinfer(fact) = " + str(dexp_tinfer(fact)))
    print("js(fact) = " + dexp_trx2js(fact))


    print("=== LIST SUM ===")
    sum_list = dexp_fix(
        "sum", "xs",
        dexp_if0(
            dexp_opr("list_is_nil", [dexp_var("xs")]),
            dexp_int(0),
            dexp_opr("+", [
                dexp_opr("list_head", [dexp_var("xs")]),
                dexp_app(
                    dexp_var("sum"),
                    dexp_opr("list_tail", [dexp_var("xs")])
                )
            ])
        )
    )
    lst = dexp_list_cons(
        dexp_int(1),
        dexp_list_cons(
            dexp_int(2),
            dexp_list_cons(
                dexp_int(3),
                dexp_list_nil()
            )
        )
    )
    test_sum = dexp_app(sum_list, lst)
    print("tinfer(test_sum) =", dexp_tinfer(test_sum))
    print("js(test_sum) =", dexp_trx2js(test_sum))
    print()

    print("=== TUPLE ===")
    fst_test = dexp_fst(pair0)
    snd_test = dexp_snd(pair0)
    print("tinfer(fst_test) =", dexp_tinfer(fst_test))
    print("js(fst_test) =", dexp_trx2js(fst_test))
    print("tinfer(snd_test) =", dexp_tinfer(snd_test))
    print("js(snd_test) =", dexp_trx2js(snd_test))
    print()

    print("=== ARRAY ===")
    arr = dexp_arry_size_val(dexp_int(5), dexp_int(0))
    print("tinfer(arr) =", dexp_tinfer(arr))
    print("js(arr) =", dexp_trx2js(arr))
    print()

    print("=== LAZY ===")
    lazy_exp = dexp_lazy(
        dexp_opr("+", [dexp_int(1), dexp_int(2)])
    )
    force_exp = dexp_opr("lazy_force", [lazy_exp])
    print("tinfer(force_exp) =", dexp_tinfer(force_exp))
    print("js(force_exp) =", dexp_trx2js(force_exp))
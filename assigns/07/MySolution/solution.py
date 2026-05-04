"""
CS525 Final Project (Spring 2026)
LAMBDA -> JavaScript compiler with closure conversion.

This compiler:
  1. Performs Hindley-Milner-style type inference using unification.
  2. Emits JavaScript code from the source AST (`dexp`).
  3. Performs closure conversion so that the generated JS contains
     NO inner functions — every function is hoisted to the top level.

Public entry points:
  - dexp_tinfer(de): styp           -- type inference
  - dexp_trx2js(de): str            -- closure-converted JS program
  - dexp_trx2js_naive(de): str      -- legacy emitter (with inner fns)
"""

import sys
sys.setrecursionlimit(10000)

##################################################################
# datatype styp
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
        self.arg1 = arg1; self.arg2 = arg2
        self.ctag = "STtup"
    def __str__(self):
        return "STtup(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class styp_fun(styp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2
        self.ctag = "STfun"
    def __str__(self):
        return "STfun(" + str(self.arg1) + ";" + str(self.arg2) + ")"

class styp_lazy(styp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "STlazy"
    def __str__(self):
        return "STlazy(" + str(self.arg1) + ")"

class styp_list(styp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "STlist"
    def __str__(self):
        return "STlist(" + str(self.arg1) + ")"

class styp_arry(styp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "STarry"
    def __str__(self):
        return "STarry(" + str(self.arg1) + ")"

class styp_stcn(styp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "STstcn"
    def __str__(self):
        return "STstcn(" + str(self.arg1) + ")"

styp_int  = styp_bas("int")
styp_bool = styp_bas("bool")
styp_str  = styp_bas("string")

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
    st1 = prune(st1); st2 = prune(st2)
    if st1 is st2:
        return
    if st1.ctag == "STxyz":
        if occurs(st1, st2):
            raise TypeError("occurs check failed: " + str(st1) + " in " + str(st2))
        st1.arg1 = st2; return
    if st2.ctag == "STxyz":
        if occurs(st2, st1):
            raise TypeError("occurs check failed: " + str(st2) + " in " + str(st1))
        st2.arg1 = st1; return
    if st1.ctag != st2.ctag:
        raise TypeError("type mismatch: " + str(st1) + " <> " + str(st2))
    if st1.ctag == "STbas":
        if st1.arg1 != st2.arg1:
            raise TypeError("type mismatch: " + str(st1) + " <> " + str(st2))
        return
    if st1.ctag == "STtup" or st1.ctag == "STfun":
        unify(st1.arg1, st2.arg1); unify(st1.arg2, st2.arg2); return
    if st1.ctag in ("STlazy", "STlist", "STarry", "STstcn"):
        unify(st1.arg1, st2.arg1); return
    raise TypeError("unify: deadcode")

##################################################################
# datatype dexp
##################################################################

class dexp:
    ctag = ""
    def __str__(self):
        return "dexp(" + self.ctag + ")"

class dexp_int(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DEint"
class dexp_btf(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DEbtf"
class dexp_str(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DEstr"
class dexp_var(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DEvar"
class dexp_lam(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DElam"
class dexp_lam1(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1; self.arg2 = arg2; self.arg3 = arg3; self.ctag = "DElam1"
class dexp_app(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEapp"
class dexp_opr(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEopr"
class dexp_fst(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DEfst"
class dexp_snd(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DEsnd"
class dexp_tup(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEtup"
class dexp_if0(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1; self.arg2 = arg2; self.arg3 = arg3; self.ctag = "DEif0"
class dexp_fix(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1; self.arg2 = arg2; self.arg3 = arg3; self.ctag = "DEfix"
class dexp_fix1(dexp):
    def __init__(self, arg1, arg2, arg3, arg4, arg5):
        self.arg1 = arg1; self.arg2 = arg2; self.arg3 = arg3
        self.arg4 = arg4; self.arg5 = arg5; self.ctag = "DEfix1"
class dexp_let(dexp):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1; self.arg2 = arg2; self.arg3 = arg3; self.ctag = "DElet"
class dexp_list_nil(dexp):
    def __init__(self):
        self.ctag = "DElist_nil"
class dexp_list_cons(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DElist_cons"
class dexp_lazy(dexp):
    def __init__(self, arg1):
        self.arg1 = arg1; self.ctag = "DElazy"
class dexp_stcn_nil(dexp):
    def __init__(self):
        self.ctag = "DEstcn_nil"
class dexp_stcn_cons(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEstcn_cons"
class dexp_arry_size_val(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEarry_size$val"
class dexp_arry_size_fun(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEarry_size$fun"
class dexp_anno(dexp):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1; self.arg2 = arg2; self.ctag = "DEanno"

##################################################################
# Type context (linked list)
##################################################################

class tctx:
    ctag = ""

class tctx_nil(tctx):
    def __init__(self):
        self.ctag = "CXnil"

class tctx_cons(tctx):
    def __init__(self, arg1, arg2, arg3):
        self.arg1 = arg1; self.arg2 = arg2; self.arg3 = arg3
        self.ctag = "CXcons"

def tctx_search(ctx, x00):
    if ctx.ctag == "CXnil":
        return None
    if ctx.ctag == "CXcons":
        if ctx.arg1 == x00:
            return ctx.arg2
        return tctx_search(ctx.arg3, x00)
    raise TypeError(ctx)

##################################################################
# Type inference
##################################################################

def dexp_tinfer(de0):
    return prune(dexp_tinfer1(de0, tctx_nil()))

def dexp_tinfer_opr(pnm, ags, ctx):
    if pnm in ["+", "-", "*", "/", "%", "cmp"]:
        st1 = dexp_tinfer1(ags[0], ctx); st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_int); unify(st2, styp_int); return styp_int
    if pnm in ["<", ">", "=", "<=", ">=", "!="]:
        st1 = dexp_tinfer1(ags[0], ctx); st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_int); unify(st2, styp_int); return styp_bool
    if pnm in ["and", "or", "&&", "||"]:
        st1 = dexp_tinfer1(ags[0], ctx); st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_bool); unify(st2, styp_bool); return styp_bool
    if pnm in ["not", "!"]:
        st1 = dexp_tinfer1(ags[0], ctx); unify(st1, styp_bool); return styp_bool
    if pnm in ["strcat", "^"]:
        st1 = dexp_tinfer1(ags[0], ctx); st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_str); unify(st2, styp_str); return styp_str
    if pnm == "list_head":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_list(stv)); return stv
    if pnm == "list_tail":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_list(stv)); return styp_list(stv)
    if pnm == "list_is_nil":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_list(stv)); return styp_bool
    if pnm == "lazy_force":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_lazy(stv)); return stv
    if pnm == "stream_head":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_stcn(stv)); return stv
    if pnm == "stream_tail":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_stcn(stv)); return styp_lazy(styp_stcn(stv))
    if pnm == "array_get":
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx); st2 = dexp_tinfer1(ags[1], ctx)
        unify(st1, styp_arry(stv)); unify(st2, styp_int); return stv
    if pnm == "array_set":
        stv = styp_new()
        st1 = dexp_tinfer1(ags[0], ctx); st2 = dexp_tinfer1(ags[1], ctx)
        st3 = dexp_tinfer1(ags[2], ctx)
        unify(st1, styp_arry(stv)); unify(st2, styp_int); unify(st3, stv)
        return styp_arry(stv)
    if pnm == "array_length":
        stv = styp_new(); st1 = dexp_tinfer1(ags[0], ctx)
        unify(st1, styp_arry(stv)); return styp_int
    raise TypeError("unknown operator: " + pnm)

def dexp_tinfer1(de0, ctx):
    if de0.ctag == "DEint":  return styp_int
    if de0.ctag == "DEbtf":  return styp_bool
    if de0.ctag == "DEstr":  return styp_str
    if de0.ctag == "DEvar":
        st0 = tctx_search(ctx, de0.arg1)
        assert st0 is not None, "unbound variable: " + de0.arg1
        return st0
    if de0.ctag == "DElam":
        st1 = styp_new()
        ctx1 = tctx_cons(de0.arg1, st1, ctx)
        st2 = dexp_tinfer1(de0.arg2, ctx1)
        return styp_fun(st1, st2)
    if de0.ctag == "DElam1":
        ctx1 = tctx_cons(de0.arg1, de0.arg2, ctx)
        st2 = dexp_tinfer1(de0.arg3, ctx1)
        return styp_fun(de0.arg2, st2)
    if de0.ctag == "DEapp":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = dexp_tinfer1(de0.arg2, ctx)
        st3 = styp_new(); unify(st1, styp_fun(st2, st3)); return st3
    if de0.ctag == "DEopr":
        return dexp_tinfer_opr(de0.arg1, de0.arg2, ctx)
    if de0.ctag == "DEtup":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = dexp_tinfer1(de0.arg2, ctx)
        return styp_tup(st1, st2)
    if de0.ctag == "DEfst":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = styp_new(); st3 = styp_new()
        unify(st1, styp_tup(st2, st3)); return st2
    if de0.ctag == "DEsnd":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = styp_new(); st3 = styp_new()
        unify(st1, styp_tup(st2, st3)); return st3
    if de0.ctag == "DEif0":
        st1 = dexp_tinfer1(de0.arg1, ctx); unify(st1, styp_bool)
        st2 = dexp_tinfer1(de0.arg2, ctx); st3 = dexp_tinfer1(de0.arg3, ctx)
        unify(st2, st3); return st2
    if de0.ctag == "DEfix":
        st1 = styp_new(); st2 = styp_new(); stf = styp_fun(st1, st2)
        ctx1 = tctx_cons(de0.arg1, stf, ctx)
        ctx2 = tctx_cons(de0.arg2, st1, ctx1)
        stx = dexp_tinfer1(de0.arg3, ctx2); unify(st2, stx); return stf
    if de0.ctag == "DEfix1":
        stf = styp_fun(de0.arg3, de0.arg5)
        ctx1 = tctx_cons(de0.arg1, stf, ctx)
        ctx2 = tctx_cons(de0.arg2, de0.arg3, ctx1)
        stx = dexp_tinfer1(de0.arg4, ctx2); unify(de0.arg5, stx); return stf
    if de0.ctag == "DElet":
        st1 = dexp_tinfer1(de0.arg2, ctx)
        ctx1 = tctx_cons(de0.arg1, st1, ctx)
        return dexp_tinfer1(de0.arg3, ctx1)
    if de0.ctag == "DElist_nil":
        return styp_list(styp_new())
    if de0.ctag == "DElist_cons":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = dexp_tinfer1(de0.arg2, ctx)
        unify(st2, styp_list(st1)); return styp_list(st1)
    if de0.ctag == "DElazy":
        st1 = dexp_tinfer1(de0.arg1, ctx); return styp_lazy(st1)
    if de0.ctag == "DEstcn_nil":
        return styp_stcn(styp_new())
    if de0.ctag == "DEstcn_cons":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = dexp_tinfer1(de0.arg2, ctx)
        unify(st2, styp_lazy(styp_stcn(st1))); return styp_stcn(st1)
    if de0.ctag == "DEarry_size$val":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = dexp_tinfer1(de0.arg2, ctx)
        unify(st1, styp_int); return styp_arry(st2)
    if de0.ctag == "DEarry_size$fun":
        st1 = dexp_tinfer1(de0.arg1, ctx); st2 = dexp_tinfer1(de0.arg2, ctx)
        st3 = styp_new(); unify(st1, styp_int)
        unify(st2, styp_fun(styp_int, st3)); return styp_arry(st3)
    if de0.ctag == "DEanno":
        st1 = dexp_tinfer1(de0.arg1, ctx); unify(st1, de0.arg2); return de0.arg2
    raise TypeError(de0)

##################################################################
# Free variable computation (used for closure conversion)
##################################################################

def freevars(de):
    if de.ctag in ("DEint", "DEbtf", "DEstr", "DElist_nil", "DEstcn_nil"):
        return set()
    if de.ctag == "DEvar":
        return {de.arg1}
    if de.ctag == "DElam":
        return freevars(de.arg2) - {de.arg1}
    if de.ctag == "DElam1":
        return freevars(de.arg3) - {de.arg1}
    if de.ctag == "DEapp":
        return freevars(de.arg1) | freevars(de.arg2)
    if de.ctag == "DEopr":
        s = set()
        for a in de.arg2:
            s |= freevars(a)
        return s
    if de.ctag in ("DEfst", "DEsnd", "DElazy", "DEanno"):
        return freevars(de.arg1)
    if de.ctag in ("DEtup", "DElist_cons", "DEstcn_cons",
                   "DEarry_size$val", "DEarry_size$fun"):
        return freevars(de.arg1) | freevars(de.arg2)
    if de.ctag == "DEif0":
        return freevars(de.arg1) | freevars(de.arg2) | freevars(de.arg3)
    if de.ctag == "DEfix":
        return freevars(de.arg3) - {de.arg1, de.arg2}
    if de.ctag == "DEfix1":
        return freevars(de.arg4) - {de.arg1, de.arg2}
    if de.ctag == "DElet":
        return freevars(de.arg2) | (freevars(de.arg3) - {de.arg1})
    raise TypeError("freevars: " + de.ctag)

##################################################################
# JS escape helper
##################################################################

def js_escape(s):
    return repr(s).replace("'", '"')

##################################################################
# CLOSURE-CONVERTED JS EMITTER
#
# Strategy:
#   - Every DElam / DElam1 / DEfix / DEfix1 / DElazy is hoisted into
#     a TOP-LEVEL `function` declaration that takes (__env__, x) as
#     parameters. The expression itself is replaced by a closure
#     object {code: <fn-name>, env: {<captured vars>}}.
#   - DEapp(f, a) becomes __apply(cf, ca). __apply is a top-level
#     helper, NOT an inner function.
#   - Variables that are free in the current function body are
#     accessed through __env__.x; parameters and let-locals are
#     accessed by their bare name.
#   - DElet(x, d, s) is desugared to (\x. s)(d) so it goes through
#     the same lambda-lifting machinery.
#
# Result: the emitted JS has zero anonymous / nested functions.
##################################################################

RUNTIME_PREAMBLE = """\
// === Runtime helpers (no inner functions; declared at top level) ===
function __mkclos(code, env) { return { code: code, env: env }; }
function __mkfix(code, env, selfname) {
  var c = { code: code, env: env };
  c.env[selfname] = c;
  return c;
}
function __apply(c, x) { return c.code(c.env, x); }
function __mklazy(code, env) {
  return { code: code, env: env, memo: false, value: null };
}
function __force(t) {
  if (!t.memo) { t.value = t.code(t.env); t.memo = true; }
  return t.value;
}
function __arr_from(n, c) {
  var r = [];
  for (var i = 0; i < n; i++) r.push(__apply(c, i));
  return r;
}
function __arr_set(a, i, v) {
  a[i] = v;
  return a;
}
"""

class CCState:
    def __init__(self):
        self.lifted = []   # list[str], top-level function decls
        self.counter = 0
    def fresh(self, prefix="__fn"):
        n = self.counter; self.counter += 1
        return prefix + str(n)

def _env_obj(fvs, env_vars):
    """Build the JS object literal that captures the free variables `fvs`
    at this point. If a free variable is itself captured in the surrounding
    function (i.e. is in `env_vars`), we read it from __env__; otherwise it
    is a parameter or local and we reference it by its bare name."""
    pairs = []
    for fv in fvs:
        if fv in env_vars:
            pairs.append(fv + ": __env__." + fv)
        else:
            pairs.append(fv + ": " + fv)
    return "{" + ", ".join(pairs) + "}"

def cc(de, env_vars, state):
    """Closure-conversion + JS emission for expression `de`.

    `env_vars` is the set of variable names that, in the *currently being
    emitted* JS function, must be read from __env__ (i.e. they are free in
    that function). All other variables are JS parameters or local lets and
    are emitted as bare identifiers."""

    if de.ctag == "DEint":
        return str(de.arg1)
    if de.ctag == "DEbtf":
        return "true" if de.arg1 else "false"
    if de.ctag == "DEstr":
        return js_escape(de.arg1)
    if de.ctag == "DEvar":
        return ("__env__." + de.arg1) if de.arg1 in env_vars else de.arg1

    if de.ctag in ("DElam", "DElam1"):
        x    = de.arg1
        body = de.arg2 if de.ctag == "DElam" else de.arg3
        fvs  = sorted(freevars(de))
        fname = state.fresh("__fn")
        # Inside the body, free variables are now read from __env__,
        # while x is a parameter (bare name).
        body_js = cc(body, set(fvs), state)
        state.lifted.append(
            "function " + fname + "(__env__, " + x + ") { return " + body_js + "; }"
        )
        return "__mkclos(" + fname + ", " + _env_obj(fvs, env_vars) + ")"

    if de.ctag == "DEapp":
        cf = cc(de.arg1, env_vars, state)
        ca = cc(de.arg2, env_vars, state)
        return "__apply(" + cf + ", " + ca + ")"

    if de.ctag == "DEopr":
        return cc_opr(de.arg1, de.arg2, env_vars, state)

    if de.ctag == "DEfst":
        return "(" + cc(de.arg1, env_vars, state) + ")[0]"
    if de.ctag == "DEsnd":
        return "(" + cc(de.arg1, env_vars, state) + ")[1]"
    if de.ctag == "DEtup":
        return ("[" + cc(de.arg1, env_vars, state) + ", "
                    + cc(de.arg2, env_vars, state) + "]")
    if de.ctag == "DEif0":
        return ("(" + cc(de.arg1, env_vars, state) + " ? "
                    + cc(de.arg2, env_vars, state) + " : "
                    + cc(de.arg3, env_vars, state) + ")")

    if de.ctag in ("DEfix", "DEfix1"):
        f_name = de.arg1
        x_name = de.arg2
        body   = de.arg3 if de.ctag == "DEfix" else de.arg4
        fvs    = sorted(freevars(de))   # excludes f_name and x_name already
        fname  = state.fresh("__fn")
        # Inside the body, both f_name (via __env__) and the captured
        # free vars are accessed through __env__. x_name is a parameter.
        body_js = cc(body, set(fvs) | {f_name}, state)
        state.lifted.append(
            "function " + fname + "(__env__, " + x_name + ") { return " + body_js + "; }"
        )
        return ("__mkfix(" + fname + ", " + _env_obj(fvs, env_vars)
                + ', "' + f_name + '")')

    if de.ctag == "DElet":
        # (let x = d in s)  ==  (\x. s)(d)
        equiv = dexp_app(dexp_lam(de.arg1, de.arg3), de.arg2)
        return cc(equiv, env_vars, state)

    if de.ctag == "DElist_nil":
        return "[]"
    if de.ctag == "DElist_cons":
        return ("[" + cc(de.arg1, env_vars, state) + "].concat("
                    + cc(de.arg2, env_vars, state) + ")")

    if de.ctag == "DElazy":
        body = de.arg1
        fvs  = sorted(freevars(body))
        fname = state.fresh("__lz")
        body_js = cc(body, set(fvs), state)
        state.lifted.append(
            "function " + fname + "(__env__) { return " + body_js + "; }"
        )
        return "__mklazy(" + fname + ", " + _env_obj(fvs, env_vars) + ")"

    if de.ctag == "DEstcn_nil":
        return "null"
    if de.ctag == "DEstcn_cons":
        return ("({ tag: 'cons', head: " + cc(de.arg1, env_vars, state)
                + ", tail: " + cc(de.arg2, env_vars, state) + " })")

    if de.ctag == "DEarry_size$val":
        return ("Array(" + cc(de.arg1, env_vars, state)
                + ").fill(" + cc(de.arg2, env_vars, state) + ")")
    if de.ctag == "DEarry_size$fun":
        return ("__arr_from(" + cc(de.arg1, env_vars, state)
                + ", " + cc(de.arg2, env_vars, state) + ")")

    if de.ctag == "DEanno":
        return cc(de.arg1, env_vars, state)

    raise TypeError("cc: " + de.ctag)

def cc_opr(pnm, ags, env_vars, state):
    ss = [cc(x, env_vars, state) for x in ags]
    if pnm == "=":   pnm = "==="
    if pnm == "and": pnm = "&&"
    if pnm == "or":  pnm = "||"
    ##
    if pnm in ["not", "!"]:
        return "(!" + ss[0] + ")"
    if pnm == "cmp":
        return "(((" + ss[0] + ") < (" + ss[1] + ")) ? -1 : (((" + ss[0] + ") > (" + ss[1] + ")) ? 1 : 0))"
    ##
    if pnm in ["strcat", "^"]:
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
        return "__force(" + ss[0] + ")"
    if pnm == "stream_head":
        return "(" + ss[0] + ").head"
    if pnm == "stream_tail":
        return "(" + ss[0] + ").tail"
    if pnm == "array_get":
        return "(" + ss[0] + ")[" + ss[1] + "]"
    if pnm == "array_set":
        return "__arr_set(" + ss[0] + ", " + ss[1] + ", " + ss[2] + ")"
    if pnm == "array_length":
        return "(" + ss[0] + ").length"
    raise TypeError("unknown JS operator: " + pnm)

def dexp_trx2js(de0):
    """Generate a complete, closure-converted JS program (no inner fns)."""
    state = CCState()
    main_expr = cc(de0, set(), state)
    parts = [RUNTIME_PREAMBLE]
    parts.extend(state.lifted)
    parts.append("// === Main ===")
    parts.append("var __result = " + main_expr + ";")
    parts.append("console.log(__result);")
    return "\n".join(parts)

##################################################################
# Naive (non-closure-converted) emitter, kept for comparison only.
##################################################################

def dexp_trx2js_naive(de0):
    return _naive(de0)

def _naive_opr(pnm, ags):
    ss = [_naive(x) for x in ags]
    if pnm == "=":   pnm = "==="
    if pnm == "and": pnm = "&&"
    if pnm == "or":  pnm = "||"
    if pnm == "not":
        return "(!" + ss[0] + ")"
    if pnm in ["strcat", "^"]:
        return "(" + ss[0] + " + " + ss[1] + ")"
    if pnm in ["+", "-", "*", "/", "%", "<", ">", "<=", ">=", "===", "!=", "&&", "||"]:
        return "(" + ss[0] + " " + pnm + " " + ss[1] + ")"
    if pnm == "list_head":   return "(" + ss[0] + ")[0]"
    if pnm == "list_tail":   return "(" + ss[0] + ").slice(1)"
    if pnm == "list_is_nil": return "((" + ss[0] + ").length === 0)"
    if pnm == "lazy_force":  return "(" + ss[0] + ")()"
    if pnm == "stream_head": return "(" + ss[0] + ").head"
    if pnm == "stream_tail": return "(" + ss[0] + ").tail"
    if pnm == "array_get":   return "(" + ss[0] + ")[" + ss[1] + "]"
    if pnm == "array_set":   return ("((" + ss[0] + ")[" + ss[1] + "] = "
                                     + ss[2] + ", " + ss[0] + ")")
    if pnm == "array_length": return "(" + ss[0] + ").length"
    raise TypeError("naive: unknown operator: " + pnm)

def _naive(de0):
    if de0.ctag == "DEint": return str(de0.arg1)
    if de0.ctag == "DEbtf": return "true" if de0.arg1 else "false"
    if de0.ctag == "DEstr": return js_escape(de0.arg1)
    if de0.ctag == "DEvar": return de0.arg1
    if de0.ctag == "DElam":
        return "((" + de0.arg1 + ") => " + _naive(de0.arg2) + ")"
    if de0.ctag == "DElam1":
        return "((" + de0.arg1 + ") => " + _naive(de0.arg3) + ")"
    if de0.ctag == "DEapp":
        return "(" + _naive(de0.arg1) + ")(" + _naive(de0.arg2) + ")"
    if de0.ctag == "DEopr":
        return _naive_opr(de0.arg1, de0.arg2)
    if de0.ctag == "DEfst": return "(" + _naive(de0.arg1) + ")[0]"
    if de0.ctag == "DEsnd": return "(" + _naive(de0.arg1) + ")[1]"
    if de0.ctag == "DEtup":
        return "[" + _naive(de0.arg1) + ", " + _naive(de0.arg2) + "]"
    if de0.ctag == "DEif0":
        return ("(" + _naive(de0.arg1) + " ? " + _naive(de0.arg2)
                + " : " + _naive(de0.arg3) + ")")
    if de0.ctag == "DEfix":
        return ("(() => { const " + de0.arg1 + " = (" + de0.arg2 + ") => "
                + _naive(de0.arg3) + "; return " + de0.arg1 + "; })()")
    if de0.ctag == "DEfix1":
        return ("(() => { const " + de0.arg1 + " = (" + de0.arg2 + ") => "
                + _naive(de0.arg4) + "; return " + de0.arg1 + "; })()")
    if de0.ctag == "DElet":
        return ("((" + de0.arg1 + ") => " + _naive(de0.arg3) + ")("
                + _naive(de0.arg2) + ")")
    if de0.ctag == "DElist_nil": return "[]"
    if de0.ctag == "DElist_cons":
        return "[" + _naive(de0.arg1) + "].concat(" + _naive(de0.arg2) + ")"
    if de0.ctag == "DElazy":
        ejs = _naive(de0.arg1)
        return ("(() => { let __m=false,__v; return () => { if(!__m){__v="
                + ejs + ";__m=true;} return __v; }; })()")
    if de0.ctag == "DEstcn_nil": return "null"
    if de0.ctag == "DEstcn_cons":
        return ("({ tag: 'cons', head: " + _naive(de0.arg1)
                + ", tail: " + _naive(de0.arg2) + " })")
    if de0.ctag == "DEarry_size$val":
        return "Array(" + _naive(de0.arg1) + ").fill(" + _naive(de0.arg2) + ")"
    if de0.ctag == "DEarry_size$fun":
        return ("Array.from({length: " + _naive(de0.arg1)
                + "}, (_,i) => (" + _naive(de0.arg2) + ")(i))")
    if de0.ctag == "DEanno": return _naive(de0.arg1)
    raise TypeError(de0)


##################################################################
# Tiny demo when run directly
##################################################################

if __name__ == "__main__":
    # identity
    id0 = dexp_lam("x", dexp_var("x"))
    print("=== id ===")
    print("type:", dexp_tinfer(id0))
    print(dexp_trx2js(id0))

    # factorial
    print("\n=== factorial ===")
    fact = dexp_fix1(
        "fact", "n", styp_int,
        dexp_if0(
            dexp_opr("<=", [dexp_var("n"), dexp_int(0)]),
            dexp_int(1),
            dexp_opr("*", [
                dexp_var("n"),
                dexp_app(dexp_var("fact"),
                         dexp_opr("-", [dexp_var("n"), dexp_int(1)]))
            ])
        ),
        styp_int)
    fact_call = dexp_app(fact, dexp_int(5))
    print("type:", dexp_tinfer(fact_call))
    print(dexp_trx2js(fact_call))

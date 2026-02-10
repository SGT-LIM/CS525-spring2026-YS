############################################################
############################################################
#
class term:
    ctag = ""
# end-of-class(term)
#
class term_var(term):
    def __init__(self, arg1):
        self.arg1 = arg1
        self.ctag = "TMvar"
    def __str__(self):
        return ("TMvar(" + self.arg1 + ")")
# end-of-class(term_var(term))
#
class term_lam(term):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "TMlam"
    def __str__(self):
        return ("TMlam(" + self.arg1 + "," + str(self.arg2) + ")")
# end-of-class(term_lam(term))
#
class term_app(term):
    def __init__(self, arg1, arg2):
        self.arg1 = arg1
        self.arg2 = arg2
        self.ctag = "TMapp"
    def __str__(self):
        return ("TMapp(" + str(self.arg1) + "," + str(self.arg2) + ")")
# end-of-class(term_app(term))
#
############################################################
#
def TMvar(x00):
    return term_var(x00)
def TMlam(x00, tm1):
    return term_lam(x00, tm1)
def TMapp(tm1, tm2):
    return term_app(tm1, tm2)
#
############################################################
############################################################
def term_subst0(tm0, x00, sub):
    def subst0(tm0):
        if (tm0.ctag == "TMvar"):
            x01 = tm0.arg1
            return sub if (x00 == x01) else tm0
        if (tm0.ctag == "TMlam"):
            x01 = tm0.arg1
            if (x00 == x01):
                return tm0
            else:
                return TMlam(x01, subst0(tm0.arg2))
        if (tm0.ctag == "TMapp"):
            return TMapp(subst0(tm0.arg1), subst0(tm0.arg2))
        raise TypeError(tm0) # HX: should be deadcode!
    return subst0(tm0)

def term_freevars(tm0):
    if isinstance(tm0, term_var):
        return {tm0.arg1}
    if isinstance(tm0, term_lam):
        return term_freevars(tm0.arg2) - {tm0.arg1}
    if isinstance(tm0, term_app):
        return term_freevars(tm0.arg1) | term_freevars(tm0.arg2)
    raise NotImplementedError

def term_gsubst(tm0, x00, sub):
    """
    Points: 20
    This function implements the (general) substitution
    function on terms that should correctly handle an open
    [sub] (that is, [sub] containing free variables)
    You can use the function [term_freevars] implemented
    in Assign01.
    """
    freevar_sub = term_freevars(sub)
    def gsubst(tm0):
        if tm0.ctag == "TMvar":
            x01 = tm0.arg1
            return sub if x01 == x00 else tm0
        
        if tm0.ctag == "TMlam":
            y = tm0.arg1
            body = tm0.arg2

            if y == x00:
                return tm0
            if y not in freevar_sub:
                return TMlam(y, gsubst(body))

            z = y
            used_names = term_freevars(body) | freevar_sub | {x00}
            while z in used_names:
                z = z + "'"

            body_renamed = term_subst0(body, y, TMvar(z))

            return TMlam(z, gsubst(body_renamed))
        
        if tm0.ctag == "TMapp":
            return TMapp(gsubst(tm0.arg1), gsubst(tm0.arg2))

    return gsubst(tm0)
    raise NotImplementedError

############################################################
############################################################
#
# Assign03 for CS525, Spring, 2026
# It is due the 10th of February, 2026
# Note that the due time is always 11:59pm of
# the due date unless specified otherwise.
#
############################################################
############################################################

def lambda_normalize(tm0):
    def step(tm):
        # 1) Application
        if isinstance(tm, term_app):
            fun = tm.arg1
            arg = tm.arg2

            if isinstance(fun, term_lam):
                x = fun.arg1
                body = fun.arg2
                return term_gsubst(body, x, arg)

            fun1 = step(fun)
            if fun1 is not None:
                return TMapp(fun1, arg)

            arg1 = step(arg)
            if arg1 is not None:
                return TMapp(fun, arg1)

            return None

        # 2) Lambda
        if isinstance(tm, term_lam):
            body1 = step(tm.arg2)
            if body1 is not None:
                return TMlam(tm.arg1, body1)
            return None

        # 3) Variable
        if isinstance(tm, term_var):
            return None
        raise TypeError("Unknown term node: " + str(tm))

    tm = tm0
    while True:
        tm1 = step(tm)
        if tm1 is None:
            return tm
        tm = tm1

############################################################

def ipred_in_lambda():
    n = "n"
    f = "f"
    x = "x"
    g = "g"
    h = "h"
    u = "u"

    gf_step = TMlam(
        g,
        TMlam(
            h,
            TMapp(
                TMvar(h),
                TMapp(TMvar(g), TMvar(f))
            )
        )
    )

    lam_u_x = TMlam(u, TMvar(x))
    lam_u_u = TMlam(u, TMvar(u))

    inner = TMapp(
        TMapp(
            TMapp(TMvar(n), gf_step),
            lam_u_x
        ),
        lam_u_u
    )
    return TMlam(n, TMlam(f, TMlam(x, inner)))


############################################################

def isqrt_in_lambda():
    # ---- Church boolean ----
    TRUE  = TMlam("t", TMlam("f", TMvar("t")))
    FALSE = TMlam("t", TMlam("f", TMvar("f")))
    IF    = TMlam("b", TMlam("x", TMlam("y", TMapp(TMapp(TMvar("b"), TMvar("x")), TMvar("y")))))

    # ---- Church Number ----
    ZERO = TMlam("f", TMlam("x", TMvar("x")))
    SUCC = TMlam("n", TMlam("f", TMlam("x", TMapp(TMvar("f"), TMapp(TMapp(TMvar("n"), TMvar("f")), TMvar("x"))))))

    ONE  = TMapp(SUCC, ZERO)
    TWO  = TMapp(SUCC, ONE)

    PAIR = TMlam("a", TMlam("b", TMlam("p", TMapp(TMapp(TMvar("p"), TMvar("a")), TMvar("b")))))
    FIRST = TMlam("p", TMapp(TMvar("p"), TMlam("a", TMlam("b", TMvar("a")))))
    SECOND = TMlam("p", TMapp(TMvar("p"), TMlam("a", TMlam("b", TMvar("b")))))

    ADD = TMlam("m", TMlam("n", TMlam("f", TMlam("x", TMapp( TMapp(TMvar("m"), TMvar("f")), TMapp(TMapp(TMvar("n"), TMvar("f")), TMvar("x")))))))
    MULT = TMlam("m", TMlam("n", TMlam("f",TMapp(TMvar("m"), TMapp(TMvar("n"), TMvar("f"))))))

    PRED = ipred_in_lambda()

    SUB = TMlam("m", TMlam("n", TMapp(TMapp(TMvar("n"), PRED), TMvar("m"))))

    ISZERO = TMlam("n", TMapp(TMapp(TMvar("n"), TMlam("x", FALSE)),TRUE))

    LEQ = TMlam("m",TMlam("n",TMapp(ISZERO,TMapp(TMapp(SUB, TMvar("m")), TMvar("n")))))

    # ---- Y-combinator (FIX) ----
    # Y = λf. (λx. f (x x)) (λx. f (x x))
    Y_inner = TMlam("x",TMapp(TMvar("f"),TMapp(TMvar("x"), TMvar("x"))))
    Y = TMlam("f", TMapp(Y_inner, Y_inner))

    g = "g"
    p = "p"

    p_var = TMvar(p)
    x_term = TMapp(FIRST, p_var)
    r_term = TMapp(SECOND, p_var)

    twox  = TMapp(TMapp(ADD, x_term), x_term)
    t_term = TMapp(TMapp(ADD, twox), ONE)

    cond = TMapp(TMapp(LEQ, t_term), r_term)

    new_x = TMapp(SUCC, x_term)
    new_r = TMapp(TMapp(SUB, r_term), t_term)
    new_p = TMapp(TMapp(PAIR, new_x), new_r)

    rec_call = TMapp(TMvar(g), new_p)

    F_body = TMapp( TMapp(TMapp(IF, cond),rec_call),x_term)

    F = TMlam(g, TMlam(p, F_body))

    n = "n"
    pair0n = TMapp(TMapp(PAIR, ZERO), TMvar(n))
    ISQRT_body = TMapp(TMapp(Y, F), pair0n)
    ISQRT = TMlam(n, ISQRT_body)

    return ISQRT


############################################################
# end of [HWXI/CS525-2026-Spring/assigns/03/assign03.py]
############################################################
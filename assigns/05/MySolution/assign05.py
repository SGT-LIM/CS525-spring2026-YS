############################################################
# Preliminary (Assignment 01-04)
############################################################
class term:
    ctag = ""

############################################################
# Basic Lambda Calculus
############################################################

class term_var(term):
    def __init__(self, x):
        self.arg1 = x
        self.ctag = "TMvar"
    def __str__(self):
        return f"TMvar({self.arg1})"

class term_lam(term):
    def __init__(self, x, body):
        self.arg1 = x
        self.arg2 = body
        self.ctag = "TMlam"
    def __str__(self):
        return f"TMlam({self.arg1},{self.arg2})"

class term_app(term):
    def __init__(self, t1, t2):
        self.arg1 = t1
        self.arg2 = t2
        self.ctag = "TMapp"
    def __str__(self):
        return f"TMapp({self.arg1},{self.arg2})"

############################################################
# Constants
############################################################

class term_int(term):
    def __init__(self, n):
        self.arg1 = n
        self.ctag = "TMint"
    def __str__(self):
        return f"TMint({self.arg1})"

class term_bool(term):
    def __init__(self, b):
        self.arg1 = b
        self.ctag = "TMbtf"
    def __str__(self):
        return f"TMbtf({self.arg1})"

class term_str(term):
    def __init__(self, s):
        self.arg1 = s
        self.ctag = "TMstr"
    def __str__(self):
        return f"TMstr({self.arg1})"

############################################################
# Operator
############################################################

class term_opr(term):
    def __init__(self, op, args):
        self.arg1 = op
        self.arg2 = args   # list of terms
        self.ctag = "TMopr"
    def __str__(self):
        return f"TMopr({self.arg1},{self.arg2})"

############################################################
# Tuple
############################################################

class term_tup(term):
    def __init__(self, t1, t2):
        self.arg1 = t1
        self.arg2 = t2
        self.ctag = "TMtup"
    def __str__(self):
        return f"TMtup({self.arg1},{self.arg2})"

class term_fst(term):
    def __init__(self, t):
        self.arg1 = t
        self.ctag = "TMfst"
    def __str__(self):
        return f"TMfst({self.arg1})"

class term_snd(term):
    def __init__(self, t):
        self.arg1 = t
        self.ctag = "TMsnd"
    def __str__(self):
        return f"TMsnd({self.arg1})"

############################################################
# If0
############################################################
class term_if0(term):
    def __init__(self, cond, t_then, t_else):
        self.arg1 = cond
        self.arg2 = t_then
        self.arg3 = t_else
        self.ctag = "TMif0"
    def __str__(self):
        return f"TMif0({self.arg1},{self.arg2},{self.arg3})"

############################################################
# Let
############################################################
class term_let(term):
    def __init__(self, name, t1, t2):
        self.arg1 = name
        self.arg2 = t1
        self.arg3 = t2
        self.ctag = "TMlet"
    def __str__(self):
        return f"TMlet({self.arg1},{self.arg2},{self.arg3})"

############################################################
# Fix (recursion)
############################################################
class term_fix(term):
    def __init__(self, fname, param, body):
        self.arg1 = fname
        self.arg2 = param
        self.arg3 = body
        self.ctag = "TMfix"
    def __str__(self):
        return f"TMfix({self.arg1},{self.arg2},{self.arg3})"

############################################################
## Assignment 4-1
############################################################
class Closure:
    def __init__(self, param, body, env):
        self.param = param
        self.body = body
        self.env = env

    def __repr__(self):
        return f"<closure {self.param}>"


def eval_term(tm, env):
    tag = tm.ctag

    # INT
    if tag == "TMint":
        return tm.arg1
    # BOOL
    if tag == "TMbtf":
        return tm.arg1
    # STRING
    if tag == "TMstr":
        return tm.arg1
    # ------------------------
    # VAR
    if tag == "TMvar":
        return env[tm.arg1]
    # ------------------------
    # LAMBDA
    if tag == "TMlam":
        return Closure(tm.arg1, tm.arg2, env.copy())
    # ------------------------
    # APPLICATION (CALL-BY-VALUE)
    if tag == "TMapp":
        fun = eval_term(tm.arg1, env)
        arg = eval_term(tm.arg2, env)

        if not isinstance(fun, Closure):
            raise Exception("Not a function")

        new_env = fun.env.copy()
        new_env[fun.param] = arg
        return eval_term(fun.body, new_env)

    # ------------------------
    # OPERATOR
    if tag == "TMopr":
        op = tm.arg1
        args = [eval_term(t, env) for t in tm.arg2]

        if op == "+":
            return args[0] + args[1]
        if op == "-":
            return args[0] - args[1]
        if op == "*":
            return args[0] * args[1]
        if op == "==":
            return args[0] == args[1]
        if op == "<":
            return args[0] < args[1]
        raise Exception("Unknown operator")
    # ------------------------
    # TUPLE
    if tag == "TMtup":
        v1 = eval_term(tm.arg1, env)
        v2 = eval_term(tm.arg2, env)
        return (v1, v2)

    if tag == "TMfst":
        v = eval_term(tm.arg1, env)
        return v[0]

    if tag == "TMsnd":
        v = eval_term(tm.arg1, env)
        return v[1]
    # ------------------------
    # IF0
    if tag == "TMif0":
        cond = eval_term(tm.arg1, env)
        if cond == 0:
            return eval_term(tm.arg2, env)
        else:
            return eval_term(tm.arg3, env)
    # ------------------------
    # LET
    if tag == "TMlet":
        name = tm.arg1
        v1 = eval_term(tm.arg2, env)
        new_env = env.copy()
        new_env[name] = v1
        return eval_term(tm.arg3, new_env)
    # ------------------------
    # FIX (RECURSION)
    if tag == "TMfix":
        fname = tm.arg1
        param = tm.arg2
        body  = tm.arg3

        new_env = env.copy()
        closure = Closure(param, body, new_env)
        new_env[fname] = closure
        return closure

    raise Exception("Unknown term type")



############################################################
# Assignment 5: compile extended lambda calculus
# to pure lambda calculus (Church encoding)
############################################################

############################################################
# Helpers
############################################################
def church_int(pos, neg):
    return APP(church_pair(), [pos, neg])

def V(x):
    return term_var(x)

def LAM(params, body):
    res = body
    for p in reversed(params):
        res = term_lam(p, res)
    return res

def APP(fun, args):
    res = fun
    for a in args:
        res = term_app(res, a)
    return res

############################################################
# Church encodings
############################################################

# Natural numbers
# n := λf. λx. f^n(x)
def church_num(n):
    if n < 0:
        raise Exception("Negative integers are not supported")
    body = V("x")
    for _ in range(n):
        body = APP(V("f"), [body])
    return LAM(["f", "x"], body)

# Booleans
# true  = λt. λf. t
# false = λt. λf. f
def church_true():
    return LAM(["t", "f"], V("t"))

def church_false():
    return LAM(["t", "f"], V("f"))

# Pair
# pair = λa. λb. λp. p a b
def church_pair():
    return LAM(["a", "b", "p"], APP(V("p"), [V("a"), V("b")]))

# fst = λp. p (λa. λb. a)
def church_fst():
    return LAM(["p"], APP(V("p"), [LAM(["a", "b"], V("a"))]))

# snd = λp. p (λa. λb. b)
def church_snd():
    return LAM(["p"], APP(V("p"), [LAM(["a", "b"], V("b"))]))

############################################################
# Arithmetic / tests
############################################################

# succ = λn. λf. λx. f (n f x)
def church_succ():
    return LAM(
        ["n", "f", "x"],
        APP(V("f"), [APP(V("n"), [V("f"), V("x")])])
    )

# add = λm. λn. λf. λx. m f (n f x)
def church_add():
    return LAM(
        ["m", "n", "f", "x"],
        APP(V("m"), [V("f"), APP(V("n"), [V("f"), V("x")])])
    )
def church_int_add():
    return LAM(["x","y"],
        APP(church_pair(), [
            APP(church_add(), [
                APP(church_fst(), [V("x")]),
                APP(church_fst(), [V("y")])
            ]),
            APP(church_add(), [
                APP(church_snd(), [V("x")]),
                APP(church_snd(), [V("y")])
            ])
        ])
    )

def church_int_neg():
    return LAM(["x"],
        APP(church_pair(), [
            APP(church_snd(), [V("x")]),
            APP(church_fst(), [V("x")])
        ])
    )

def church_int_sub():
    return LAM(["x","y"],
        APP(church_int_add(), [
            V("x"),
            APP(church_int_neg(), [V("y")])
        ])
    )

# mul = λm. λn. λf. λx. m (n f) x
def church_mul():
    return LAM(
        ["m", "n", "f", "x"],
        APP(V("m"), [APP(V("n"), [V("f")]), V("x")])
    )

def church_int_mul():
    return LAM(["x","y"],
        APP(church_pair(), [
            APP(church_add(), [
                APP(church_mul(), [
                    APP(church_fst(), [V("x")]),
                    APP(church_fst(), [V("y")])
                ]),
                APP(church_mul(), [
                    APP(church_snd(), [V("x")]),
                    APP(church_snd(), [V("y")])
                ])
            ]),
            APP(church_add(), [
                APP(church_mul(), [
                    APP(church_fst(), [V("x")]),
                    APP(church_snd(), [V("y")])
                ]),
                APP(church_mul(), [
                    APP(church_snd(), [V("x")]),
                    APP(church_fst(), [V("y")])
                ])
            ])
        ])
    )

def church_int_iszero():
    return LAM(["x"],
        APP(church_and(), [
            APP(church_iszero(), [
                APP(church_sub(), [
                    APP(church_fst(), [V("x")]),
                    APP(church_snd(), [V("x")])
                ])
            ]),
            APP(church_iszero(), [
                APP(church_sub(), [
                    APP(church_snd(), [V("x")]),
                    APP(church_fst(), [V("x")])
                ])
            ])
        ])
    )


def church_pred():
    step = LAM(["g", "h"], APP(V("h"), [APP(V("g"), [V("f")])]))
    base = LAM(["u"], V("x"))
    ident = LAM(["u"], V("u"))
    return LAM(
        ["n", "f", "x"],
        APP(V("n"), [step, base, ident])
    )

# sub = λm. λn. n pred m
def church_sub():
    return LAM(
        ["m", "n"],
        APP(V("n"), [church_pred(), V("m")])
    )

# iszero = λn. n (λx. false) true
def church_iszero():
    return LAM(
        ["n"],
        APP(V("n"), [LAM(["x"], church_false()), church_true()])
    )

# not = λb. λt. λf. b f t
def church_not():
    return LAM(
        ["b", "t", "f"],
        APP(V("b"), [V("f"), V("t")])
    )

# and = λp. λq. p q false
def church_and():
    return LAM(
        ["p", "q"],
        APP(V("p"), [V("q"), church_false()])
    )

# lazy-if helper for CBV:
# if_lazy b th el = b th el 0
# where th/el are thunks of one argument
def church_if_lazy():
    return LAM(
        ["b", "th", "el"],
        APP(V("b"), [V("th"), V("el"), church_num(0)])
    )

# leq = λm. λn. iszero (sub m n)
def church_leq():
    return LAM(
        ["m", "n"],
        APP(church_iszero(), [
            APP(church_sub(), [V("m"), V("n")])
        ])
    )

# lt = λm. λn. not (leq n m)
def church_lt():
    return LAM(
        ["m", "n"],
        APP(church_not(), [
            APP(church_leq(), [V("n"), V("m")])
        ])
    )

# xor = λp. λq. p (not q) q
def church_xor():
    return LAM(
        ["p", "q"],
        APP(V("p"), [APP(church_not(), [V("q")]), V("q")])
    )

# nat_eq = λm. λn. and (leq m n) (leq n m)
def church_nat_eq():
    return LAM(
        ["m", "n"],
        APP(church_and(), [
            APP(church_leq(), [V("m"), V("n")]),
            APP(church_leq(), [V("n"), V("m")])
        ])
    )

# int_isneg(x) : true iff fst(x) < snd(x)
def church_int_isneg():
    return LAM(
        ["x"],
        APP(church_lt(), [
            APP(church_fst(), [V("x")]),
            APP(church_snd(), [V("x")])
        ])
    )

# abs_nat(x) = |fst(x) - snd(x)|, returned as a natural Church numeral
def church_int_abs_nat():
    return LAM(
        ["x"],
        APP(church_if_lazy(), [
            APP(church_lt(), [
                APP(church_fst(), [V("x")]),
                APP(church_snd(), [V("x")])
            ]),
            LAM(["u"],
                APP(church_sub(), [
                    APP(church_snd(), [V("x")]),
                    APP(church_fst(), [V("x")])
                ])
            ),
            LAM(["u"],
                APP(church_sub(), [
                    APP(church_fst(), [V("x")]),
                    APP(church_snd(), [V("x")])
                ])
            )
        ])
    )

# build signed integer from sign bit and natural magnitude
# neg = true  -> (0, mag)
# neg = false -> (mag, 0)
def church_int_from_signmag():
    return LAM(
        ["neg", "mag"],
        APP(church_if_lazy(), [
            V("neg"),
            LAM(["u"], church_int(church_num(0), V("mag"))),
            LAM(["u"], church_int(V("mag"), church_num(0)))
        ])
    )

# signed integer division (truncate toward zero)
def church_int_div():
    return LAM(
        ["x", "y"],
        APP(church_if_lazy(), [
            APP(church_int_iszero(), [V("y")]),
            LAM(["u"], church_int(church_num(0), church_num(0))),

            LAM(["u"],
                APP(church_int_from_signmag(), [
                    APP(church_xor(), [
                        APP(church_int_isneg(), [V("x")]),
                        APP(church_int_isneg(), [V("y")])
                    ]),
                    APP(church_div(), [
                        APP(church_int_abs_nat(), [V("x")]),
                        APP(church_int_abs_nat(), [V("y")])
                    ])
                ])
            )
        ])
    )

# signed integer modulo:
# r = x - y * (x / y)
def church_int_mod():
    return LAM(
        ["x", "y"],
        APP(church_if_lazy(), [
            APP(church_int_iszero(), [V("y")]),
            LAM(["u"], V("x")),

            LAM(["u"],
                APP(church_int_sub(), [
                    V("x"),
                    APP(church_int_mul(), [
                        V("y"),
                        APP(church_int_div(), [V("x"), V("y")])
                    ])
                ])
            )
        ])
    )

# div for naturals:
# div m n =
#   if n == 0 then 0
#   else if m < n then 0
#   else 1 + div(m-n, n)
def church_div():
    return APP(church_Y(), [
        LAM(["self", "m", "n"],
            APP(church_if_lazy(), [
                APP(church_iszero(), [V("n")]),
                LAM(["u"], church_num(0)),
                LAM(["u"],
                    APP(church_if_lazy(), [
                        APP(church_lt(), [V("m"), V("n")]),
                        LAM(["v"], church_num(0)),
                        LAM(["v"],
                            APP(church_succ(), [
                                APP(V("self"), [
                                    APP(church_sub(), [V("m"), V("n")]),
                                    V("n")
                                ])
                            ])
                        )
                    ])
                )
            ])
        )
    ])

# mod for naturals:
# mod m n =
#   if n == 0 then m
#   else if m < n then m
#   else mod(m-n, n)
def church_mod():
    return APP(church_Y(), [
        LAM(["self", "m", "n"],
            APP(church_if_lazy(), [
                APP(church_iszero(), [V("n")]),
                LAM(["u"], V("m")),
                LAM(["u"],
                    APP(church_if_lazy(), [
                        APP(church_lt(), [V("m"), V("n")]),
                        LAM(["v"], V("m")),
                        LAM(["v"],
                            APP(V("self"), [
                                APP(church_sub(), [V("m"), V("n")]),
                                V("n")
                            ])
                        )
                    ])
                )
            ])
        )
    ])

def decode_church_nat(tm):
    applied = APP(tm, [
        term_lam("z", term_opr("+", [term_var("z"), term_int(1)])),
        term_int(0)
    ])
    return eval_term(applied, {})

def decode_church_int(tm):
    pos_tm = APP(church_fst(), [tm])
    neg_tm = APP(church_snd(), [tm])
    return decode_church_nat(pos_tm) - decode_church_nat(neg_tm)
    
############################################################
# Fixed point combinator
############################################################


# Z combinator for call-by-value
# Z = λg. (λx. g (λv. x x v)) (λx. g (λv. x x v))
def church_Y():
    inner = LAM(
        ["x"],
        APP(V("g"), [
            LAM(["v"], APP(APP(V("x"), [V("x")]), [V("v")]))
        ])
    )
    return LAM(["g"], APP(inner, [inner]))

############################################################
# Operator compilation
############################################################

def compile_opr(op, args):
    cargs = [assign05_compile(t) for t in args]

    if op == "+":
        if len(cargs) != 2:
            raise Exception("Operator + expects 2 arguments")
        return APP(church_int_add(), cargs)

    if op == "-":
        if len(cargs) != 2:
            raise Exception("Operator - expects 2 arguments")
        return APP(church_int_sub(), cargs)

    if op == "*":
        if len(cargs) != 2:
            raise Exception("Operator * expects 2 arguments")
        return APP(church_int_mul(), cargs)

    if op == "/":
        if len(cargs) != 2:
            raise Exception("Operator / expects 2 arguments")
        return APP(church_int_div(), cargs)

    if op == "%":
        if len(cargs) != 2:
            raise Exception("Operator % expects 2 arguments")
        return APP(church_int_mod(), cargs)

    raise Exception(f"Unsupported operator in assign05_compile: {op}")

############################################################
# Main compiler
############################################################

def assign05_compile(tm):
    tag = tm.ctag

    # Pure lambda terms remain pure after recursive compilation
    if tag == "TMvar":
        return tm

    if tag == "TMlam":
        return term_lam(tm.arg1, assign05_compile(tm.arg2))

    if tag == "TMapp":
        return term_app(assign05_compile(tm.arg1), assign05_compile(tm.arg2))

    # Constants
    # if tag == "TMint":
    #     return church_num(tm.arg1)

    if tag == "TMint":
        n = tm.arg1
        if n >= 0:
            return church_int(church_num(n), church_num(0))
        else:
            return church_int(church_num(0), church_num(-n))

    if tag == "TMbtf":
        return church_true() if tm.arg1 else church_false()

    # Tuple
    if tag == "TMtup":
        return APP(church_pair(), [
            assign05_compile(tm.arg1),
            assign05_compile(tm.arg2)
        ])

    if tag == "TMfst":
        return APP(church_fst(), [assign05_compile(tm.arg1)])

    if tag == "TMsnd":
        return APP(church_snd(), [assign05_compile(tm.arg1)])

    # Operator
    if tag == "TMopr":
        return compile_opr(tm.arg1, tm.arg2)

    # if0(c, t_then, t_else)  ===  if iszero(c) then t_then else t_else
    # if tag == "TMif0":
    #     c = assign05_compile(tm.arg1)
    #     t_then = assign05_compile(tm.arg2)
    #     t_else = assign05_compile(tm.arg3)
    #     return APP(church_iszero(), [c, t_then, t_else])
    if tag == "TMif0":
        c = assign05_compile(tm.arg1)
        t_then = assign05_compile(tm.arg2)
        t_else = assign05_compile(tm.arg3)

        return APP(church_if_lazy(), [
            APP(church_int_iszero(), [c]),
            LAM(["u"], t_then),
            LAM(["u"], t_else)
        ])

    # let x = t1 in t2  ===  (λx. t2) t1
    if tag == "TMlet":
        x = tm.arg1
        t1 = assign05_compile(tm.arg2)
        t2 = assign05_compile(tm.arg3)
        return APP(LAM([x], t2), [t1])

    # TMfix(f, x, body)  ===  Y (λf. λx. body)
    if tag == "TMfix":
        f = tm.arg1
        x = tm.arg2
        body = assign05_compile(tm.arg3)
        return APP(church_Y(), [LAM([f, x], body)])

    raise Exception(f"Unknown term tag: {tag}")

############################################################
# Utilities for checking target purity
############################################################

def is_pure_lambda(tm):
    tag = tm.ctag
    if tag == "TMvar":
        return True
    if tag == "TMlam":
        return is_pure_lambda(tm.arg2)
    if tag == "TMapp":
        return is_pure_lambda(tm.arg1) and is_pure_lambda(tm.arg2)
    return False

############################################################
# Example programs
############################################################

# factorial(n) =
#   if0 n then 1 else n * factorial(n-1)
def make_fact_ast():
    return term_fix(
        "fact", "n",
        term_if0(
            term_var("n"),
            term_int(1),
            term_opr("*", [
                term_var("n"),
                term_app(
                    term_var("fact"),
                    term_opr("-", [term_var("n"), term_int(1)])
                )
            ])
        )
    )

# fib(n) =
#   if0 n then 0
#   else if0 (n-1) then 1
#   else fib(n-1) + fib(n-2)
def make_fib_ast():
    return term_fix(
        "fib", "n",
        term_if0(
            term_var("n"),
            term_int(0),
            term_if0(
                term_opr("-", [term_var("n"), term_int(1)]),
                term_int(1),
                term_opr("+", [
                    term_app(
                        term_var("fib"),
                        term_opr("-", [term_var("n"), term_int(1)])
                    ),
                    term_app(
                        term_var("fib"),
                        term_opr("-", [term_var("n"), term_int(2)])
                    )
                ])
            )
        )
    )

# power(x, n) =
#   if0 n then 1 else x * power(x, n-1)
#
# Curried version:
#   fix power x => λn. ...
def make_power_ast():
    return term_fix(
        "power", "x",
        term_lam(
            "n",
            term_if0(
                term_var("n"),
                term_int(1),
                term_opr("*", [
                    term_var("x"),
                    term_app(
                        term_app(term_var("power"), term_var("x")),
                        term_opr("-", [term_var("n"), term_int(1)])
                    )
                ])
            )
        )
    )


############################################################
# Testing for reference
############################################################

# def decode_church_nat(tm):
#     applied = APP(tm, [
#         term_lam("z", term_opr("+", [term_var("z"), term_int(1)])),
#         term_int(0)
#     ])
#     return eval_term(applied, {})

# def decode_church_int(tm):
#     pos_tm = APP(church_fst(), [tm])
#     neg_tm = APP(church_snd(), [tm])
#     return decode_church_nat(pos_tm) - decode_church_nat(neg_tm)

# # factorial
# fact_call = term_app(make_fact_ast(), term_int(5))
# fact_compiled = assign05_compile(fact_call)
# print(decode_church_int(fact_compiled))  # 120

# # fibonacci
# fib_call = term_app(make_fib_ast(), term_int(6))
# fib_compiled = assign05_compile(fib_call)
# print(decode_church_int(fib_compiled))  # 8

# # power
# power_call = term_app(term_app(make_power_ast(), term_int(2)), term_int(5))
# power_compiled = assign05_compile(power_call)
# print(decode_church_int(power_compiled))  # 32

# # signed arithmetic
# tests = [
#     ("-3 + 5", term_opr("+", [term_int(-3), term_int(5)])),
#     ("-7 / 3", term_opr("/", [term_int(-7), term_int(3)])),
#     ("7 % -3", term_opr("%", [term_int(7), term_int(-3)])),
# ]

# for name, ast in tests:
#     result = decode_church_int(assign05_compile(ast))
#     print(name, "=>", result)

############################################################
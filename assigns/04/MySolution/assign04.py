############################################################
# Preliminary
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
## Assignment 4-2
############################################################

def IF_THEN_ELSE(cond, then_b, else_b):
    return term_if0(cond, else_b, then_b)

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

def T_Abs(x):
    cond = term_opr("<", [x, term_int(0)])
    return IF_THEN_ELSE(cond, term_opr("-", [term_int(0), x]), x)

def T_Neq(a, b):
    return IF_THEN_ELSE(term_opr("==", [a, b]), term_int(0), term_int(1))


def make_board_get():
    def get_idx(bd, idx):
        res = bd
        for _ in range(idx): res = term_snd(res)
        return term_fst(res) if idx < 7 else res

    bd, i = term_var("bd"), term_var("i")
    body = term_int(-1)
    
    for idx in reversed(range(8)):
        body = IF_THEN_ELSE(term_opr("==", [i, term_int(idx)]), get_idx(bd, idx), body)
    return LAM(["bd", "i"], body)

def make_board_set():
    def get_idx(bd, idx):
        res = bd
        for _ in range(idx): res = term_snd(res)
        return term_fst(res) if idx < 7 else res

    bd, i, j = term_var("bd"), term_var("i"), term_var("j")

    def build_tup(replace_idx):
        elements = [j if x == replace_idx else get_idx(bd, x) for x in range(8)]
        res = elements[7]
        for x in reversed(range(7)):
            res = term_tup(elements[x], res)
        return res

    body = bd
    for idx in reversed(range(8)):
        body = IF_THEN_ELSE(term_opr("==", [i, term_int(idx)]), build_tup(idx), body)
    return LAM(["bd", "i", "j"], body)

def make_safety_test1():
    i0, j0, i1, j1 = term_var("i0"), term_var("j0"), term_var("i1"), term_var("j1")
    
    cond1 = T_Neq(j0, j1)
    cond2 = T_Neq(T_Abs(term_opr("-", [i0, i1])), T_Abs(term_opr("-", [j0, j1])))
    
    body = IF_THEN_ELSE(cond1, cond2, term_int(0))
    return LAM(["i0", "j0", "i1", "j1"], body)

def make_safety_test2():
    i0, j0, bd, i = term_var("i0"), term_var("j0"), term_var("bd"), term_var("i")

    cond_i_less_0 = term_opr("<", [i, term_int(0)])
    
    call_st1 = APP(term_var("safety_test1"), [i0, j0, i, APP(term_var("board_get"), [bd, i])])
    call_st2 = APP(term_var("safety_test2"), [i0, j0, bd, term_opr("-", [i, term_int(1)])])
    
    then_b = IF_THEN_ELSE(call_st1, call_st2, term_int(0))
    
    body = IF_THEN_ELSE(cond_i_less_0, term_int(1), then_b)
    
    return term_fix("safety_test2", "i0", LAM(["j0", "bd", "i"], body))

def make_search():
    bd, i, j, nsol = term_var("bd"), term_var("i"), term_var("j"), term_var("nsol")
    N = term_int(8)

    cond_j = term_opr("<", [j, N])
    
    call_st2 = APP(term_var("safety_test2"), [i, j, bd, term_opr("-", [i, term_int(1)])])
    bd1_val = APP(term_var("board_set"), [bd, i, j])
    
    cond_i_plus_1 = term_opr("==", [term_opr("+", [i, term_int(1)]), N])
    
    search_next_row = APP(term_var("search"), [bd, i, term_opr("+", [j, term_int(1)]), term_opr("+", [nsol, term_int(1)])])
    search_next_col = APP(term_var("search"), [term_var("bd1"), term_opr("+", [i, term_int(1)]), term_int(0), nsol])
    
    inner_if = IF_THEN_ELSE(cond_i_plus_1, search_next_row, search_next_col)
    
    test_if = IF_THEN_ELSE(term_var("test"), 
                           term_let("bd1", bd1_val, inner_if), 
                           APP(term_var("search"), [bd, i, term_opr("+", [j, term_int(1)]), nsol]))
    
    then_j = term_let("test", call_st2, test_if)

    cond_i_gt_0 = term_opr("<", [term_int(0), i]) # 0 < i
    call_search_back = APP(term_var("search"), [
        bd,
        term_opr("-", [i, term_int(1)]),
        term_opr("+", [APP(term_var("board_get"), [bd, term_opr("-", [i, term_int(1)])]), term_int(1)]),
        nsol
    ])
    else_j = IF_THEN_ELSE(cond_i_gt_0, call_search_back, nsol)

    body = IF_THEN_ELSE(cond_j, then_j, else_j)
    
    return term_fix("search", "bd", LAM(["i", "j", "nsol"], body))


def make_init_bd():
    res = term_int(0)
    for _ in range(7): res = term_tup(term_int(0), res)
    return res

eight_queens_ast = \
    term_let("board_get", make_board_get(),
    term_let("board_set", make_board_set(),
    term_let("safety_test1", make_safety_test1(),
    term_let("safety_test2", make_safety_test2(),
    term_let("search", make_search(),
        APP(term_var("search"), [make_init_bd(), term_int(0), term_int(0), term_int(0)])
    )))))

print("Evaluating LAMBDA AST for 8-Queens...")
result = eval_term(eight_queens_ast, {})
print(f"Total number of solutions: {result}")
"""
Test driver. For each test program:
  1. Print the inferred type.
  2. Generate JS via dexp_trx2js (closure-converted).
  3. Run the JS through node and print the output.

Usage: python3 run_tests.py
Requires: node (Node.js) on PATH.
"""

import os, sys, subprocess, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + "/..")

from solution import (
    # AST constructors
    dexp_int, dexp_btf, dexp_str, dexp_var, dexp_lam, dexp_lam1, dexp_app,
    dexp_opr, dexp_fst, dexp_snd, dexp_tup, dexp_if0, dexp_fix, dexp_fix1,
    dexp_let, dexp_list_nil, dexp_list_cons, dexp_lazy,
    dexp_stcn_nil, dexp_stcn_cons,
    dexp_arry_size_val, dexp_arry_size_fun, dexp_anno,
    # types
    styp_int, styp_bool, styp_str, styp_list, styp_lazy, styp_stcn,
    styp_arry, styp_fun,
    # API
    dexp_tinfer, dexp_trx2js,
)

def run_js(js_code):
    """Run JS through node and return stdout."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".js", delete=False) as f:
        f.write(js_code)
        path = f.name
    try:
        r = subprocess.run(["node", path], capture_output=True, text=True, timeout=10)
        return r.stdout.strip(), r.stderr.strip()
    finally:
        os.unlink(path)

def report(name, de):
    print("=" * 60)
    print("TEST:", name)
    print("=" * 60)
    try:
        t = dexp_tinfer(de)
        print("Type :", t)
    except Exception as e:
        print("Type-error:", e); return
    js = dexp_trx2js(de)
    print("--- generated JS ---")
    print(js)
    out, err = run_js(js)
    print("--- node stdout ---")
    print(out)
    if err:
        print("--- node stderr ---")
        print(err)
    print()

# ============================================================
# Tests
# ============================================================

# 1. Identity applied
def t_id():
    idf = dexp_lam("x", dexp_var("x"))
    return dexp_app(idf, dexp_int(42))

# 2. Nested lambda capture: ((\x. \y. x + y) 3) 4  = 7
def t_nested_capture():
    add = dexp_lam("x", dexp_lam("y",
            dexp_opr("+", [dexp_var("x"), dexp_var("y")])))
    return dexp_app(dexp_app(add, dexp_int(3)), dexp_int(4))

# 3. Three-deep capture: x + y + z
def t_triple_capture():
    f = dexp_lam("x", dexp_lam("y", dexp_lam("z",
        dexp_opr("+", [
            dexp_opr("+", [dexp_var("x"), dexp_var("y")]),
            dexp_var("z")
        ]))))
    return dexp_app(dexp_app(dexp_app(f, dexp_int(10)), dexp_int(20)), dexp_int(30))

# 4. Let
def t_let():
    return dexp_let("x", dexp_int(5),
            dexp_let("y", dexp_int(7),
              dexp_opr("*", [dexp_var("x"), dexp_var("y")])))

# 5. Factorial via DEfix1
def t_fact():
    fact = dexp_fix1("fact", "n", styp_int,
            dexp_if0(
                dexp_opr("<=", [dexp_var("n"), dexp_int(0)]),
                dexp_int(1),
                dexp_opr("*", [
                    dexp_var("n"),
                    dexp_app(dexp_var("fact"),
                             dexp_opr("-", [dexp_var("n"), dexp_int(1)]))])),
            styp_int)
    return dexp_app(fact, dexp_int(6))   # 720

# 6. Fibonacci via DEfix
def t_fib():
    fib = dexp_fix("fib", "n",
            dexp_if0(
                dexp_opr("<=", [dexp_var("n"), dexp_int(1)]),
                dexp_var("n"),
                dexp_opr("+", [
                    dexp_app(dexp_var("fib"),
                             dexp_opr("-", [dexp_var("n"), dexp_int(1)])),
                    dexp_app(dexp_var("fib"),
                             dexp_opr("-", [dexp_var("n"), dexp_int(2)]))])))
    return dexp_app(fib, dexp_int(10))   # 55

# 7. Sum of a list
def t_sum_list():
    sum_fn = dexp_fix("sum", "xs",
        dexp_if0(
            dexp_opr("list_is_nil", [dexp_var("xs")]),
            dexp_int(0),
            dexp_opr("+", [
                dexp_opr("list_head", [dexp_var("xs")]),
                dexp_app(dexp_var("sum"),
                         dexp_opr("list_tail", [dexp_var("xs")]))])))
    lst = dexp_list_cons(dexp_int(1),
          dexp_list_cons(dexp_int(2),
          dexp_list_cons(dexp_int(3),
          dexp_list_cons(dexp_int(4), dexp_list_nil()))))
    return dexp_app(sum_fn, lst)   # 10

# 8. Tuple, fst/snd
def t_tuple():
    p = dexp_tup(dexp_int(1), dexp_btf(True))
    return dexp_fst(p)   # 1

# 9. Higher-order: map-like via fold won't fit easily, use a 'twice'
#    twice f x = f (f x); twice (\n. n+1) 5 = 7
def t_twice():
    twice = dexp_lam("f", dexp_lam("x",
        dexp_app(dexp_var("f"),
                 dexp_app(dexp_var("f"), dexp_var("x")))))
    inc = dexp_lam("n", dexp_opr("+", [dexp_var("n"), dexp_int(1)]))
    return dexp_app(dexp_app(twice, inc), dexp_int(5))   # 7

# 10. Closure inside fix: a counter-style demonstration via let
def t_closure_in_fix():
    # let add = \x. \y. x+y in (add 100) 7
    return dexp_let("add",
            dexp_lam("x", dexp_lam("y",
                dexp_opr("+", [dexp_var("x"), dexp_var("y")]))),
            dexp_app(dexp_app(dexp_var("add"), dexp_int(100)),
                     dexp_int(7)))   # 107

# 11. Lazy
def t_lazy():
    # force(lazy(2 + 3))
    return dexp_opr("lazy_force",
        [dexp_lazy(dexp_opr("+", [dexp_int(2), dexp_int(3)]))])  # 5

# 12. Lazy capturing free var
def t_lazy_capture():
    # let x = 41 in force(lazy (x + 1))
    return dexp_let("x", dexp_int(41),
        dexp_opr("lazy_force",
            [dexp_lazy(dexp_opr("+", [dexp_var("x"), dexp_int(1)]))])) # 42

# 13. Array from size+val
def t_array_val():
    return dexp_opr("array_length",
        [dexp_arry_size_val(dexp_int(7), dexp_int(0))])   # 7

# 14. Array from size+fun (this requires __arr_from helper, no inner fn)
def t_array_fun():
    # array of length 5 where a[i] = i*i; sum first by getting a[3]
    sq = dexp_lam("i", dexp_opr("*", [dexp_var("i"), dexp_var("i")]))
    arr = dexp_arry_size_fun(dexp_int(5), sq)
    return dexp_opr("array_get", [arr, dexp_int(3)])   # 9

# 15. Stream: take first 3 elements of an infinite stream of ones,
#     check head and head-of-tail.
def t_stream():
    # from = \n. cons(n, lazy(from(n+1)))
    # hd(tl(force(... wait, type needs care
    # Simpler: explicit two-element stream
    # s = cons(10, lazy(cons(20, lazy(stcn_nil))))   
    # But stcn_nil's type is stcn(?), need same elem type as 10/20.
    # Use:
    inner = dexp_stcn_cons(dexp_int(20), dexp_lazy(dexp_stcn_nil()))
    s = dexp_stcn_cons(dexp_int(10), dexp_lazy(inner))
    # Take s.head + (force(s.tail)).head  =  10 + 20 = 30
    head1 = dexp_opr("stream_head", [s])
    tail1 = dexp_opr("stream_tail", [s])
    forced = dexp_opr("lazy_force", [tail1])
    head2 = dexp_opr("stream_head", [forced])
    return dexp_opr("+", [head1, head2])   # 30

# Run all
TESTS = [
    ("identity_applied",        t_id()),
    ("nested_capture",          t_nested_capture()),
    ("triple_capture",          t_triple_capture()),
    ("let",                     t_let()),
    ("factorial_6",             t_fact()),
    ("fib_10",                  t_fib()),
    ("sum_list",                t_sum_list()),
    ("tuple_fst",               t_tuple()),
    ("twice",                   t_twice()),
    ("closure_in_let",          t_closure_in_fix()),
    ("lazy_simple",             t_lazy()),
    ("lazy_capture",            t_lazy_capture()),
    ("array_size_val",          t_array_val()),
    ("array_size_fun",          t_array_fun()),
    ("stream",                  t_stream()),
]

if __name__ == "__main__":
    for name, de in TESTS:
        report(name, de)

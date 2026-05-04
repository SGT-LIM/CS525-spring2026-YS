# TEST directory

This directory contains the test driver `run_tests.py` for the LAMBDA-to-JS
compiler in `../solution.py`.

## How to run

```bash
python3 TEST/run_tests.py
```

Requires Node.js on `PATH`; the driver feeds each generated JS program to
`node` and prints the result, so we are testing both the type-checker AND
the run-time correctness of the closure-converted JS.

## Tests included (15)

| # | Name              | Source program (in LAMBDA, sketched)                | Expected |
|---|-------------------|-----------------------------------------------------|----------|
| 1 | identity_applied  | `(λx. x) 42`                                        | `42`     |
| 2 | nested_capture    | `((λx.λy. x + y) 3) 4`                              | `7`      |
| 3 | triple_capture    | `(((λx.λy.λz. x + y + z) 10) 20) 30`                | `60`     |
| 4 | let               | `let x = 5 in let y = 7 in x * y`                   | `35`     |
| 5 | factorial_6       | `fix1 fact n:int. ... : int  applied to 6`         | `720`    |
| 6 | fib_10            | `fix fib n. ...  applied to 10`                     | `55`     |
| 7 | sum_list          | sum of `[1; 2; 3; 4]` via recursive `sum`           | `10`     |
| 8 | tuple_fst         | `fst (1, true)`                                     | `1`      |
| 9 | twice             | `(λf.λx. f(f x)) (λn. n+1) 5`                       | `7`      |
| 10| closure_in_let    | `let add = λx.λy.x+y in (add 100) 7`                | `107`    |
| 11| lazy_simple       | `force (lazy (2+3))`                                | `5`      |
| 12| lazy_capture      | `let x = 41 in force (lazy (x + 1))`                | `42`     |
| 13| array_size_val    | `array_length (Array(7).fill(0))`                   | `7`      |
| 14| array_size_fun    | element 3 of `Array.from(5, λi. i*i)`               | `9`      |
| 15| stream            | `head s + head(force(tail s))`, `s = stream 10::lazy(20::nil)` | `30` |

All 15 tests **pass** (Python type inference succeeds, generated JS runs in
Node and prints the expected value).

## Closure-conversion sanity check

Test #3 (`triple_capture`) is included specifically to exercise nested-lambda
capture with **two** layers of free-variable lifting (`x`, then `y`). After
closure conversion, the generated JS is:

```js
function __fn2(__env__, z) { return ((__env__.x + __env__.y) + z); }
function __fn1(__env__, y) { return __mkclos(__fn2, {x: __env__.x, y: y}); }
function __fn0(__env__, x) { return __mkclos(__fn1, {x: x}); }
```

— note that **all three** `function` declarations are at the top level. There
are zero `=>` arrow functions and zero nested `function` expressions in any
test output. This confirms the closure-conversion goal stated in the
assignment.

## Results

All 15 tests pass — type inference succeeds, and the generated JS produces the expected output under Node.js. No known issues at the time of writing.
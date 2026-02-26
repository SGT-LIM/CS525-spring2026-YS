# Assignment 4

It is due Thursday, the 26th of February, 2026

## Assignment 4-1 (50 points)

Please implement a call-by-value evaluator for
LAMBDA, which is based (for the moment) on the
following extended lambda-calculus:

datatype term =
//
  | TMvar of strn
  | TMlam of (strn, term)
  | TMapp of (term, term)
//
  | TMint of sint // signed ints
  | TMbtf of bool // true / false
  | TMstr of strn // string consts
//
  | TMopr of (strn, list(term))
//
  | TMtup of
    (term, term) // for pairs
  | TMfst of term // 1st projection
  | TMsnd of term // 2nd projection
//
  | TMif0 of (term, term, term)
//
  | TMlet of (strn(*x*), term, term)
  | TMfix of (strn(*f*), strn(*x*), term)

## Assignment 4-2 (50 points)

There is a functional program solving the 8-queen puzzle
described [here](https://ats-lang.github.io/FROZEN000/DOCUMENT/INT2PROGINATS/HTML/INT2PROGINATS-BOOK-onechunk.html#example-the-eight-queens-puzzle)

Please *closely translate* it into the above programming langauge LAMBDA.

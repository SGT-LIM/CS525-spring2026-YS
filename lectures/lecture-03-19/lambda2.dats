//
#typedef tvar = strn
//
datatype styp =
//
|STbas of strn(*name*)
|STtup of (styp(*T1*), styp(*T2*)) // T1 * T2
|STfun of (styp(*T1*), styp(*T2*)) // T1 -> T2

datatype tctx = // typing context
|TCnil of ()
|TCcons of (tvar, styp, tctx)

val STint = STbas"sint"
val STbtf = STbas"bool"

fun
term_oftp
(tm0: term, env: tctx): styp =
(
case tm0 of
| TMint _ => STint
| TMbtf _ => STbtf

|
TMlam(x00, st1, tm1) =>
let
val env =
TCcons(x0, st1, env)
val st2 = term_oftp(tm1, env)
in
  STfun(st1, st2)
end
|
TMapp(tm1, tm2)
let
val st1 =
term_oftp(tm1, env)
val st2 =
term_oftp(tm2, env)
in
case st1 of
STfun(st11, st12) =>
let
val () = assert(st2 = st11) in st12
end
|
TMfix(f00, x01, st1, tm1, st2) =>
let
val stf = STfun(st1, st2)
val env = TCcons(x01, st1, env)
val env = TCcons(f00, stf, env)
val st3 = term_oftp(tm1, env)
in
let val ( ) = assert(st2 = st3) in stf end
end
|
TMtup(tm1, tm2) => help_tup(tm0)
|
TMfst(tm1) =>
let
val st1 =
term_oftp(tm1, env)
in
  case st1 of
  | STtup(st11, _) => st11
(*
  | _ => print some error messge
*)
end

) where
{
fun
help_tup
(tm0: term, env: tctx): styp =
let
val-
TMtup(tm1, tm2) = tm0
val st1 =
term_oftp(tm1, env)
val st2 =
term_oftp(tm2, env)
in
  STtup(st1, st2)
end
}

val STsint = STbas"sint"
val STbool = STbas"bool"

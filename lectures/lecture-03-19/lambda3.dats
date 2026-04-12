(*
HX-2026-03-19:
Let's finalize the source language
of your compiler project for this class
*)
//
datatype styp =
//
|STbas of strn(*name*)
//
(*
HX: existential variable
*)
|STxyz of (ref(optn(styp))
//
|STtup of
(styp(*T1*), styp(*T2*)) // T1 * T2
//
|STfun of
(styp(*T1*), styp(*T2*)) // T1 -> T2
//
|STlazy of styp // lazy evaluation
//
|STlist of styp // list constructor
//
|STarry of styp // array constructor
|STstcn of styp // stream constructor
//
(* ****** ****** *)

#typedef dvar = strn

datatype dexp =
//
| DEint of sint
| DEbtf of bool
| DEstr of strn
//
| DEvar of dvar
| DElam of
( dvar, dexp(*body*))
| DEapp of
( dexp(*fun*), dexp(*arg*))
//
| DEopr of (strn, list(dexp))
//
| DEfst of (dexp)
| DEsnd of (dexp)
| DEtup of (dexp, dexp)
//
| DEif0 of
( dexp(*test*)
, dexp(*then*), dexp(*else*))
//
| DEfix of
( dvar(*fun*)
, dvar(*arg*), dexp(*body*))
//
| DElet of
( dvar(*x*)
, dexp(*def*), dexp(*scope*))
//
| DElist_nil of ()
| DElist_cons of (dexp, dexp)
//
| DElazy of dexp
| DEstcn_nil of ()
| DEstcn_cons of (dexp, dexp)
//
| DEarry_size$val of
  (dexp(*size*), dexp(*val*))
| DEarry_size$fun of
  (dexp(*size*), dexp(*fun*))
//
(*
HX: for type annotion
*)
| DEanno of (dexp, styp)
//
| DElam1 of
( dvar, styp, dexp(*body*))
| DEfix1 of
( dvar, dvar, styp, dexp(*body*), styp)
//
(* ****** ****** *)

val STsint = STbas"sint"
val STbool = STbas"bool"

fun
styp_eval
(st0: styp): styp =
(
case st0 of
| STxyz(xyz) => (case !xyz of None => st0 | Some(st1) => st1)
)

fun
styp_funize
(st0: styp) =
let
val st0 = styp_eval(st0)
in
case st0 of
| STxyz(xyz) =>
let val st1 = STfun(stxyz_new(), stxyz_new()) in xyz := Some(st1); st1 end
| _(*non-STxyz*) => st0

(* ****** ****** *)

datatype tctx = 
|TCnil of ()
|TCcons of (dvar, styp, tctx)

fun
dexp_infer
(de0: dexp, env: tctx): styp =
(
case+ de0 of
| DEint _ => STsint
| DEbtf _ => STbool
|
DElam(x00, de1) =>
let
val st1 = stxyz_new() // create a new type variable
val env =
TCcons(x00, st1, env)
val
st2 = dexp_infer(de1, env)
in
  STfun(st1, st2)
end

|
DEapp(de1, de2)
let
val st1 = dexp_infer(de1, env)
val st2 = dexp_infer(de2, env)

val st1 = styp_funize(st1)

in
case st1 of
STfun(st11, st12) =>
let
val () = assert(unify(st2, st11)) in st12
end

)

(* ****** ****** *)

fun unify
(st1: styp, st2: sty): bool =
let
val st1 = styp_eval(st1)
val st2 = styp_eval(st2)
in
case st1 of
| STxyz(xyz) => ( xyz := Some(st2); true) // Fix: "occurs"-check needed!
| _ => (
case st2 of
| STxyz(xyz) => ( xyz := Some(st1); true) // Fix: "occurs"-check needed!
| _ =>
(
case (st1, st2) of
| (STfun(st11, st12), STfun(st21, st22)) => (unify(st11, st12) && unify(st21, st22))
| (STtup(st11, st12), STtup(st21, st22)) => (unify(st11, st12) && unify(st21, st22))
| (_, _) => false
)
)

end

(* ****** ****** *)

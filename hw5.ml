(*********************************************)
(* HW5: A Sound Static Type Checker for PROC *)
(*********************************************)

type exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

(* raise this exception when the program is determined to be ill-typed *)
exception TypeError

(* type *)
type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string

(* type equations are represented by a list of "equalities" (ty1 = ty2)  *)
type typ_eqn = (typ * typ) list

(* generate a fresh type variable *)
let tyvar_num = ref 0
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)
end

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with
| CONST n -> [(ty, TyInt)]
  | VAR x -> [(ty, TEnv.find tenv x)]
  | ADD (e1, e2) -> (ty, TyInt)::(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
  | SUB (e1, e2) -> (ty, TyInt)::(gen_equations tenv e1 TyInt)@(gen_equations tenv e2 TyInt)
  | ISZERO e -> (ty, TyBool)::(gen_equations tenv e TyInt)
  | IF (e, e1, e2) -> let a=fresh_tyvar () in 
                          (gen_equations tenv e1 TyBool)@(gen_equations tenv e2 a)@(gen_equations tenv e2 a)
  | LET (x, e1, e2) -> let a=fresh_tyvar () in
                          (gen_equations tenv e1 a)@(gen_equations (TEnv.extend (x,a) tenv) e2 ty)
  | PROC (x, e) -> let a=fresh_tyvar () in
                        let b=fresh_tyvar () in
                            (ty, TyFun (a, b))::(gen_equations (TEnv.extend (x,a) tenv) e b)
  | CALL (e1, e2) -> let a=fresh_tyvar () in
                         (gen_equations tenv e1 (TyFun(a, ty)))@(gen_equations tenv e2 a)

let solve : typ_eqn -> Subst.t
=fun eqn -> (let rec unifyall : typ_eqn -> Subst.t -> Subst.t
            =fun eqn s -> (match eqn with
            |[] -> s
            |(t1, t2)::tl -> (let s'=(let rec unify : typ -> typ -> Subst.t -> Subst.t
                                      =fun t1 t2 sub -> (match (t1, t2, sub) with
                                                        |(TyInt, TyInt, sub) -> sub
                                                        |(TyBool, TyBool, sub) -> sub
                                                        |(TyVar a, t, sub) -> (match (let rec finding : typ -> typ -> bool
                                                                      =fun ty1 ty2 -> (match ty2 with
                                                                                      |TyFun(ty1', ty2') -> if (ty1'=ty1 || ty2'=ty1) 
                                                                                                            then true 
                                                                                                            else (finding ty1 ty1')||(finding ty1 ty2')
                                                                                      |_ -> false)
                                                                                      in (finding (TyVar a) t)) with 
                                                                      |true -> raise TypeError
                                                                      |false -> (Subst.extend a t sub))
                                                        |(t, TyVar a, sub) -> (unify (TyVar a) t sub)
                                                        |(TyFun (t1, t2), TyFun (t1', t2'), sub) -> (let sub' = (unify t1 t1' sub) in
                                                                                                  let t1''= (Subst.apply t2 sub') in
                                                                                                  let t2''= (Subst.apply t2' sub') in
                                                                                                  (unify t1'' t2'' sub'))
                                                        |_ -> raise TypeError) in (unify (Subst.apply t1 s) (Subst.apply t2 s) s))
                              in (unifyall tl s')))
            in(unifyall eqn Subst.empty))

let typeof : exp -> typ 
=fun exp -> 
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
    ty
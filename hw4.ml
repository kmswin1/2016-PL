(*
   B Interpreter
*)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M(Loc.base,[])

  let rec replace_nth = fun l n c -> (*n번째 원소를 바꾼다*)
    match l with
    | h::t -> if n = 1 then c::t else h::(replace_nth t (n-1) c)
    | [] -> raise Not_allocated

  let load (M(boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V(v) -> v 
    | U -> raise Not_initialized

  let store (M(boundary,storage)) loc content =
    M(boundary, replace_nth storage (Loc.diff boundary loc) (V(content)))

  let alloc (M(boundary,storage)) = (boundary,M(Loc.increase boundary 1,U::storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E(fun x -> raise Not_bound)
  let lookup (E(env)) id = env id
  let bind (E(env)) id loc = E(fun x -> if x = id then loc else env x)
end

(*
 * B Interpreter
 *)
module type B_TYPE =
sig
  exception Error of string
  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp            (* sequence *)
  | IF of exp * exp * exp       (* if-then-else *)
  | WHILE of exp * exp          (* while loop *)
  | LETV of id * exp * exp      (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list      (* call by value *)
  | CALLR of id * id list       (* call by referenece *)
  | RECORD of (id * exp) list   (* record construction *)
  | FIELD of exp * id           (* access record field *)
  | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module B : B_TYPE =
struct
  exception Error of string

  type id = string
  type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
  | ASSIGNF of exp * id * exp   (* assign to record field *)
  | READ of id
  | WRITE of exp

  type program = exp

  type value =
  | Num of int
  | Bool of bool
  | Unit
  | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v = 
    match v with 
    | Num n -> n
    | Bool _ -> raise (Error "Bool type is used as Num type")
    | Unit -> raise (Error "Unit type is used as Num type")
    | Record _ -> raise (Error "Unit type is used as Num type")

  let value_bool v =
    match v with
    | Bool b -> b
    | Num _ -> raise (Error "Num type is used as Bool type")
    | Unit -> raise (Error "Unit type is used as Bool type")
    | Record _ -> raise (Error "Unit type is used as Bool type")

    let value_unit v =
    match v with 
    | Unit -> ()
    | Num _ -> raise (Error "Num type is used as Unit type")
    | Bool _ -> raise (Error "Bool type is used as Unit type")
    | Record _ -> raise (Error "Bool type is used as Unit type")

  let value_record v =
    match v with
    | Record r -> r
    | Num _ -> raise (Error "Num type is used as Record type")
    | Unit -> raise (Error "Unit type is used as Record type")
    | Bool _ -> raise (Error "Bool type is used as Record type")

  let env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "not allowed")) 
    with Env.Not_bound -> raise (Error "not bound")

  let env_proc e f =
    try
      (match Env.lookup e f with
        | Addr _ -> raise (Error "not allowed") 
      | Proc (id, exp, env) -> (id, exp, env))
    with Env.Not_bound -> raise (Error "not bound")
      
  let rec eval : memory -> env -> exp -> (value * memory) = 
    fun mem env e -> match e with
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | NUM i -> (Num i, mem)
    | UNIT -> (Unit, mem)
    | VAR x -> (Mem.load mem (env_loc env x), mem)
    | ADD (e1, e2) -> (match (eval mem env e1) with 
                     |(Num i, mem1) -> (match (eval mem1 env e2) with
                                     |(Num j, mem2) -> (Num (i+j), mem2)
                                     |_ -> raise (Error("non numeric values")))
                     |_ -> raise (Error"non numeric values"))
    | SUB (e1, e2) -> (match (eval mem env e1) with 
                     |(Num i, mem1) -> (match (eval mem1 env e2) with
                                     |(Num j, mem2) -> (Num (i-j), mem2)
                                     |_ -> raise (Error("non numeric values")))
                     |_ -> raise (Error"non numeric values"))
    | MUL (e1, e2) -> (match (eval mem env e1) with 
                     |(Num i, mem1) -> (match (eval mem1 env e2) with
                                     |(Num j, mem2) -> (Num (i*j), mem2)
                                     |_ -> raise (Error("non numeric values")))
                     |_ -> raise (Error"non numeric values"))
    | DIV (e1, e2) -> (match (eval mem env e1) with 
                     |(Num i, mem1) -> (match (eval mem1 env e2) with
                                     |(Num 0, mem2) -> raise (Error("cannot divide by zero"))
                                     |(Num j, mem2) -> (Num (i/j), mem2)
                                     |_ -> raise (Error("non numeric values")))
                     |_ -> raise (Error"non numeric values"))
    | EQUAL (e1, e2) -> (match (eval mem env e1) with
                      |(value1, mem1) ->(match (eval mem1 env e2) with
                                        |(value2, mem2) -> (match (value1, value2) with
                                                            |(Num i, Num j) -> if i=j then (Bool true, mem2) else (Bool false, mem2)
                                                            |(Bool true, Bool true) ->(Bool true, mem2)
                                                            |(Bool false, Bool false) -> (Bool true, mem2)
                                                            |(Unit, Unit) -> (Bool true, mem2)
                                                            |(_, _) -> (Bool false, mem2))))
    | LESS (e1, e2) -> (match (eval mem env e1) with
                      |(Num i, mem1) -> (match (eval mem1 env e2) with
                                        |(Num j, mem2) -> if i<j then (Bool true, mem2) else (Bool false, mem2)
                                        |_ -> raise (Error("non numeric value")))
                      | _ -> raise (Error("non numeric value")))
    | NOT e -> (match (eval mem env e) with
                     |(Bool true, mem1) -> (Bool false, mem1)
                     |(Bool false, mem1) -> (Bool true, mem1)
                     |_ -> raise (Error("Type error : non boolean type")))
    | SEQ (e1, e2) -> (match (eval mem env e1) with
                      |(value1, mem1) ->(match (eval mem1 env e2) with
                                       |(value2, mem2) -> (value2, mem2)))
    | IF (e, e1, e2) -> (match (eval mem env e) with
                      |(Bool true, mem1) -> (match (eval mem1 env e1) with
                                            |(value, mem2) -> (value, mem2))
                      |(Bool false, mem1) -> (match (eval mem1 env e2) with
                                            |(value, mem2) -> (value, mem2))
                      |(_, mem1) -> (raise (Error ("not boolean type"))))
    | WHILE (e1, e2) -> (match (eval mem env e1) with
                        |(Bool true, mem') -> (match (eval mem' env e2) with
                                             |(value1, mem1) -> match (eval mem1 env (WHILE (e1, e2))) with
                                                          |(value2, mem2) -> (value2, mem2))
                        |(Bool false, mem') -> (Unit, mem')
                        |(_, mem') -> raise (Error("Type error : e1 is not boolean")))
    | ASSIGN (x, e) -> (match (eval mem env e) with
                        |(value, mem') -> (value, Mem.store mem' (env_loc env x) value))
    | ASSIGNF (e1, x, e2) -> (match (eval mem env e1) with
                              |(Record r, mem1) -> (match (eval mem1 env e2) with
                                                    |(value, mem2)->(value, Mem.store mem2 (r x) value))
                              |(_, mem1) ->raise (Error ("not record")))
    | FIELD (e, x) -> (match (eval mem env e) with
                      |(Record r, mem') -> (Mem.load mem' (r x), mem')
                      |(_, mem') ->raise (Error ("not record")))
    | LETV (x, e1, e2) -> (match (eval mem env e1) with
                          |(value1, mem1) -> (match (Mem.alloc mem1) with
                                              |(l, mem2) -> (match (eval (Mem.store mem2 l value1) (Env.bind env x (Addr l)) e2) with
                                                                      |(value2, mem4) -> (value2, mem4))))
    | LETF (x, l, e1, e2) -> (match (eval mem (Env.bind env x (Proc (l, e1, env))) e2) with
                             |(value, mem') -> (value, mem'))
    | CALLV (f, l) -> (match (let rec evallist : exp list -> memory -> (value*memory) list
                                    =fun li me -> (match li with
                                                  |e1::tl -> (match (eval me env e1) with
                                                             |(v1, me1) -> (v1, me1)::evallist tl me1)
                                                  |[] -> []) in
                                                             (evallist l mem)) with
                      |vmlist -> (match (let rec returnlast : (value*memory) list -> (value*memory) 
                                                              = fun l -> (match l with
                                                                          |n::[] -> n
                                                                          |hd::tl -> returnlast tl) in (returnlast vmlist)) with
                                |(vt, mt) ->(match (env_proc env f) with
                                            |(xlist, e', env') -> (match (let rec cvbinding : (value*memory) list -> id list -> env -> memory -> env*memory
                                                                                                  =fun vmlist2 xlist2 en memresult -> (match (vmlist2, xlist2) with
                                                                                                                                      |((vv1, mm1)::vmtl, xh::xtl) -> (match (Mem.alloc memresult) with
                                                                                                                                                                      |(l1, memresult2) -> (match (Mem.store memresult2 l1 vv1) with
                                                                                                                                                                                          |memresult' -> cvbinding vmtl xtl (Env.bind en xh (Addr l1)) memresult'))
                                                                                                                                      |([], []) -> (en, memresult)
                                                                                                                                      |_ -> raise (Error ("cannot bind"))) in
                                                                                                                                                                          (cvbinding vmlist xlist (Env.bind env' f (Proc (xlist,e',env'))) mt)) with
                                                                       |(ef, mf) -> (match (eval mf ef e') with
                                                                                    |(value', memm) -> (value', memm))))))
    | CALLR (f, l) -> (match (env_proc env f) with
                      |(xlist, e, env') -> (match (let rec crbinding : id list -> id list -> env -> env -> env
                                                                      =fun xl yl en en' -> (match (xl, yl) with
                                                                                                  |(x1::xt, y1::yt) -> crbinding xt yt en (Env.bind en' x1 (Addr (env_loc en y1)))
                                                                                                  |([], []) -> en'
                                                                                                  |_ -> raise (Error ("cannot bind"))) in
                                                                                                                    crbinding xlist l env (Env.bind env' f (Proc (xlist,e,env')))) with
                                            |envresult -> (match (eval mem envresult e) with
                                                          |(value', mem') -> (value', mem'))))
    | RECORD l -> (match l with
                    | [] -> (Unit,mem)
                    | (x1,e1)::tl ->match (eval mem env e1) with 
                                       | (v1,mem1) -> match (Mem.alloc mem1) with
                                                      | (l,mem2) -> match (Mem.store mem2 l v1) with
                                                                            | (mem3) -> match (let rec funrec : (id -> Loc.t)->memory ->(id*exp)list->(id->Loc.t)*memory
                                                                                                              =fun re me tl2 -> match tl2 with
                                                                                                                               |[] -> (re,me)
                                                                                                                               |(x2,e2)::tl3-> match (eval me env e2) with
                                                                                                                                              |(v2,me1) -> match (Mem.alloc me1) with
                                                                                                                                                          |(l2,me2) -> (funrec (fun x-> if x=x2 then l2 else re x) (Mem.store me2 l2 v2) tl3) in
                                                                                                                                                                                                                                              (funrec (fun x-> if x=x1 then l else (raise (Error "cannot bind"))) mem3 tl)) with
                                                                                              |(lastfun,lastmem) ->(Record(lastfun),lastmem))
    | READ x -> let n = read_int () in 
                                    (Num n,(Mem.store mem (env_loc env x) (Num n)))
    | WRITE e ->(match (eval mem env e) with
                | (Num n, mem1) -> (print_endline (string_of_int n);
                                    (Num n, mem1)) 
                |(_, _) -> raise (Error ("not int type")))

  let run (mem, env, pgm) = 
    let (v,_) = eval mem env pgm in
    v
end
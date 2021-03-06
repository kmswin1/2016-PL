(*********************) (* Problem 1: filter *) (*********************) 
let rec filter pred lst = [] let rec filter pred lst = [] let rec filter pred lst = match lst with [] ->
[] |hd::tl -> if pred hd=true then hd::(filter pred tl) else filter pred tl;; 

(*********************) (* Problem 2: zipper *) (*********************) 
let rec zipper : int list * int list -> int list =fun (a,b) -> [] let rec zipper ((l1:int list), (l2:int list)) = match l1 with []
-> l2 |hd::tl -> hd::zipper (l2, tl);; 

(*******************) (* Problem 3: iter *) (*******************) let rec iter : int * (int -> int) -> (int -> int) =fun (n,f) ->
f let rec iter (n, (f:int->int)) p = match n with 0 -> p |_ -> f (iter (n-1, f) p);; 

(*********************) (* Problem 4: Diff *) (*********************) 
type aexp = | Const of int | Var of string | Power of string * int | Times of aexp list | Sum of aexp list let rec diff : aexp * string ->
aexp =fun (aexp,x) -> aexp let rec diff (aexp, string) = match aexp with Const n -> Const 0|Var x ->
if x=string then Const 1 else aexp|Power (x, n) ->
if x=string then Times [Const n; Power (x, n-1)] else aexp|Times l -> (match l with [] -> Const 0|hd::tl -> 
Sum([Times(diff(hd, string)::tl)]@[Times(hd::[diff(Times(tl), string)])]))|Sum l -> 
(match l with [] -> Const 0|hd::tl -> Sum([diff (hd, string)]@[diff (Sum (tl), string)]));;

(*************************) (* Problem 5: Calculator *) (*************************) 
type exp = X | INT of int | ADD of exp * exp | SUB of exp * exp | MUL of exp * exp | DIV of exp *exp | SIGMA of exp * exp * exp let calculator : exp -> int =fun e -> 0
let rec cal (exp, num)= match exp with X -> 
num|INT (n)-> n|ADD (exp1, exp2) -> (cal (exp1, num)) + (cal (exp2, num))|SUB (exp1, exp2) -> 
(cal (exp1, num)) - (cal (exp2, num))|MUL (exp1, exp2) -> (cal (exp1, num)) * (cal (exp2, num))|DIV (exp1, exp2) -> 
(cal (exp1, num)) / (cal (exp2, num))|SIGMA (exp1, exp2, exp3) -> (match exp1 with INT (m) -> 
if exp1=exp2 then cal (exp3, m) else cal (exp3, m)+cal (SIGMA (INT (m+1), exp2, exp3), m));;

(* exception Problem *) 
let rec calculator exp = match exp with X -> raise Problem|INT (n) -> n|ADD (exp1, exp2) -> 
calculator (exp1) + calculator (exp2)|SUB (exp1, exp2) -> calculator (exp1) - calculator (exp2)|MUL (exp1, exp2) -> 
calculator (exp1) * calculator (exp2)|DIV (exp1, exp2) -> calculator (exp1) / calculator (exp2)|SIGMA (exp1, exp2, exp3) -> 
(match calculator (exp1) with m -> if m=calculator(exp2) then cal (exp3, m) else cal (exp3, m)+calculator (SIGMA (INT (m+1), exp2 , exp3)));;

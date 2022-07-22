type id = string

type binOp = Plus | Mult | Minus | Lt

type exp = 
  | Var of id
  | ILit of int
  | BLit of bool
  | BinOp of binOp * exp * exp
  | IfExp of exp * exp * exp
  | LetExp of id * exp * exp

type exval = 
  | IntV of int
  | BoolV of bool
and dnval = exval

let exval_to_exp = function 
  | IntV i -> ILit i
  | BoolV b -> BLit b

type judgement = 
  | EvalExp of (id * exval) list * exp * exval
  | PlusExp of int * int * int 
  | MultExp of int * int * int
  | MinusExp of int * int * int
  | LtExp of int * int * bool

type rule = 
| Eint 
| Ebool 
| Evar1
| Evar2
| EifT 
| EifF 
| Eplus 
| Eminus 
| Etimes 
| Elt 
| Elet
| Bplus 
| Bminus 
| Btimes 
| Blt
type binOp = Plus | Mult | Minus | Lt

type exp = 
  | ILit of int
  | BLit of bool
  | BinOp of binOp * exp * exp
  | IfExp of exp * exp * exp
  | Error

type judgement = 
  | EvalExp of exp * exp
  | PlusExp of int * int * int 
  | MultExp of int * int * int
  | MinusExp of int * int * int
  | LtExp of int * int * bool

type rule = 
| Eint 
| Ebool 
| EifT 
| EifF 
| Eplus 
| Eminus 
| Etimes 
| Elt 
| Bplus 
| Bminus 
| Btimes 
| Blt
| EplusBoolL
| EplusBoolR
| EplusErrorL
| EplusErrorR
| EminusBoolL
| EminusBoolR
| EminusErrorL
| EminusErrorR
| EtimesBoolL
| EtimesBoolR
| EtimesErrorL
| EtimesErrorR
| EltBoolL
| EltBoolR
| EltErrorL
| EltErrorR
| EifInt
| EifError
| EifTError
| EifFError

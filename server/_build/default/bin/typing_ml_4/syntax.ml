type id = string

type binOp = Plus | Mult | Minus | Lt

type exp = 
  | Var of id
  | ILit of int
  | BLit of bool
  | BinOp of binOp * exp * exp
  | IfExp of exp * exp * exp
  | LetExp of id * exp * exp
  | LetRecExp of id * id * exp * exp
  | FunExp of id * exp
  | AppExp of exp * exp
  | NilExp
  | ConsExp of exp * exp
  | MatchExp of exp * exp * id * id * exp

type tyvar = int  (* 型変数の識別子を整数で表現 *)

type ty = 
  | TyInt
  | TyBool
  | TyVar of tyvar
  | TyFun of ty * ty 
  | TyList of ty

type judgement = 
  | TyExp of (id * ty) list * exp * ty

type rule = 
| Tint 
| Tbool 
| Tif
| Tplus 
| Tminus
| Ttimes
| Tlt 
| Tvar 
| Tlet
| Tfun
| Tapp
| Tletrec
| Tnil
| Tcons
| Tmatch
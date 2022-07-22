open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = try Parser.toplevel Lexer.main (Lexing.from_string root) with _ -> err "Parsing failed." 

type exval = 
  | IntV of int
  | BoolV of bool
and dnval = exval

let rec eval_exp = function
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | BinOp (binOp, e1, e2) -> 
    (match binOp, eval_exp e1, eval_exp e2 with
    | Plus, IntV arg1, IntV arg2 -> IntV (arg1 + arg2)
    | Mult, IntV arg1, IntV arg2 -> IntV (arg1 * arg2)
    | Minus, IntV arg1, IntV arg2 -> IntV (arg1 - arg2)
    | Lt, IntV arg1, IntV arg2 -> BoolV (arg1 < arg2)
    | _, _, _ -> err "No possible evaluation.")
  | IfExp (c, t, e) -> 
      (match eval_exp c with
      | BoolV b -> if b then eval_exp t else eval_exp e
      | _ -> err "No possible derivation.")

let rec create_dtree judgement =
  (match judgement with
  | EvalExp (e1, e2) -> 
      (match e1, e2 with
      | ILit i1, ILit i2 -> 
          if i1 = i2 then Tree ((judgement, Eint), Empty::[]) else err "No possible derivation."
      | BLit b1, BLit b2 -> 
          if b1 = b2 then Tree ((judgement, Ebool), Empty::[]) else err "No possible derivation."
      | IfExp (c, t, e), _ -> 
          let test = try eval_exp c with _ -> err "Evaluation failed." in 
          (match test with
          | BoolV b -> 
            if b then 
              let first = try eval_exp t with _ -> err "Evaluation failed." in 
              (match first, e2 with
              | IntV i1, ILit i2 -> 
                  if i1 = i2 
                    then 
                      let t1 = create_dtree (EvalExp (c, BLit true)) in 
                      let t2 = create_dtree (EvalExp (t, e2)) in
                      Tree ((judgement, EifT), t1::t2::[]) 
                    else err "No possible derivation."
              | BoolV b1, BLit b2 -> 
                  if b1 = b2 
                    then 
                      let t1 = create_dtree (EvalExp (c, BLit true)) in 
                      let t2 = create_dtree (EvalExp (t, e2)) in
                      Tree ((judgement, EifT), t1::t2::[]) 
                    else err "No possible derivation."
              | _, _ -> err "No possible derivation.")
            else
              let second = try eval_exp e with _ -> err "Evaluation failed." in 
              (match second, e2 with
              | IntV i1, ILit i2 -> 
                  if i1 = i2 
                    then 
                      let t1 = create_dtree (EvalExp (c, BLit false)) in 
                      let t2 = create_dtree (EvalExp (e, e2)) in
                      Tree ((judgement, EifF), t1::t2::[]) 
                    else err "No possible derivation."
              | BoolV b1, BLit b2 -> 
                  if b1 = b2 
                    then 
                      let t1 = create_dtree (EvalExp (c, BLit false)) in 
                      let t2 = create_dtree (EvalExp (e, e2)) in
                      Tree ((judgement, EifF), t1::t2::[]) 
                    else err "No possible derivation."
              | _, _ -> err "No possible derivation." )
          | _ -> err "No possible derivation.")
      | BinOp (binOp, l, r), _ -> 
          let left  = try eval_exp l with _ -> err "Evaluation failed." in 
          let right = try eval_exp r with _ -> err "Evaluation failed." in 
          (match left, right with
          | IntV i1, IntV i2 -> 
            (match binOp, e2 with
              | Plus, ILit i3 -> 
                  if i1 + i2 = i3
                    then
                      let t1 = create_dtree (EvalExp (l, ILit i1)) in 
                      let t2 = create_dtree (EvalExp (r, ILit i2)) in 
                      let t3 = create_dtree (PlusExp (i1, i2, i3)) in 
                      Tree ((judgement, Eplus), t1::t2::t3::[])
                    else err "No possible derivation."
              | Mult, ILit i3 ->
                  if i1 * i2 = i3
                    then
                      let t1 = create_dtree (EvalExp (l, ILit i1)) in 
                      let t2 = create_dtree (EvalExp (r, ILit i2)) in 
                      let t3 = create_dtree (MultExp (i1, i2, i3)) in 
                      Tree ((judgement, Etimes), t1::t2::t3::[])
                    else err "No possible derivation."
              | Minus, ILit i3 -> 
                  if i1 - i2 = i3
                    then
                      let t1 = create_dtree (EvalExp (l, ILit i1)) in 
                      let t2 = create_dtree (EvalExp (r, ILit i2)) in 
                      let t3 = create_dtree (MinusExp (i1, i2, i3)) in 
                      Tree ((judgement, Eminus), t1::t2::t3::[])
                    else err "No possible derivation."
              | Lt, BLit b3 ->
                  if (i1 < i2 && b3) || (i1 >= i2 && not b3)
                    then
                      let t1 = create_dtree (EvalExp (l, ILit i1)) in 
                      let t2 = create_dtree (EvalExp (r, ILit i2)) in 
                      let t3 = create_dtree (LtExp (i1, i2, b3)) in 
                      Tree ((judgement, Elt), t1::t2::t3::[])
                    else err "No possible derivation."
              | _, _ -> err "No possible derivation.")
          | _, _ -> err "No possible derivation.")
        | _, _ -> err "No possible derivation.")
  | PlusExp (n1, n2, n3) -> 
      if n1 + n2 = n3 
        then Tree ((judgement, Bplus), Empty::[])
        else err "No possible derivation."
  | MultExp (n1, n2, n3) -> 
      if n1 * n2 = n3 
        then Tree ((judgement, Btimes), Empty::[])
        else err "No possible derivation."
  | MinusExp (n1, n2, n3) -> 
      if n1 - n2 = n3
        then Tree ((judgement, Bminus), Empty::[])
        else err "No possible derivation."
  | LtExp (n1, n2, b) -> 
      if (n1 < n2 && b) || (n1 >= n2 && not b)
        then Tree ((judgement, Blt), Empty::[])
        else err "No possible derivation.")

let rec pp_exp exp = 
  (match exp with
  | ILit i -> string_of_int i
  | BLit b -> string_of_bool b
  | BinOp (binOp, l, r) -> 
    (match binOp with
    | Plus -> (pp_exp l) ^ " + " ^ (pp_exp r)
    | Mult -> (pp_exp l) ^ " * " ^ (pp_exp r)
      (* (match l, r with
      | Plus _, Plus _ -> "(" ^ (pp_exp l) ^ ")" ^ " * " ^ "(" ^ (pp_exp r) ^ ")"
      | Plus _, _ -> "(" ^ (pp_exp l) ^ ")" ^ " * " ^ (pp_exp r)
      | _, Plus _ -> (pp_exp l) ^ " * " ^ "(" ^ (pp_exp r) ^ ")"
      | _, _ -> (pp_exp l) ^ " * " ^ (pp_exp r)) *)
    | Minus -> (pp_exp l) ^ " - " ^ (pp_exp r)
    | Lt -> (pp_exp l) ^ " < " ^ (pp_exp r))
  | IfExp (c, t, e) -> 
    "if " ^ (pp_exp c) ^ " then " ^ (pp_exp t) ^ " else " ^ (pp_exp e))

let pp_judgement = function 
  | EvalExp (l, r)-> 
    let j = (pp_exp l) ^ " evalto " ^ (pp_exp r) in j
  | PlusExp (n1, n2, n3) -> 
    let j = (string_of_int n1) ^ " plus " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in j
  | MultExp (n1, n2, n3) -> 
    let j = (string_of_int n1) ^ " times " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in j
  | MinusExp (n1, n2, n3) -> 
    let j = (string_of_int n1) ^ " minus " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in j
  | LtExp (n1, n2, b3) -> 
    let j = (string_of_int n1) ^ " less than " ^ (string_of_int n2) ^ " is " ^ (string_of_bool b3) in j
    
let pp_derivation = function 
  | EvalExp (l, r), rule -> 
      let j = (pp_exp l) ^ " evalto " ^ (pp_exp r) in
      let r = match rule with 
        | Eint -> " by E-Int"
        | Ebool -> " by E-Bool"
        | EifT -> " by E-IfT"
        | EifF -> " by E-IfF"
        | Eplus -> " by E-Plus"
        | Eminus -> " by E-Minus" 
        | Etimes -> " by E-Times" 
        | Elt -> " by E-Lt" 
        | _ -> err "No possible derivation." 
      in j ^ r
  | PlusExp (n1, n2, n3), rule -> 
      let j = (string_of_int n1) ^ " plus " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in 
      let r = match rule with Bplus -> " by B-Plus" | _ -> err "No possible derivation." in j ^ r
  | MultExp (n1, n2, n3), rule -> 
      let j = (string_of_int n1) ^ " times " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in 
      let r = match rule with Btimes -> " by B-Times" | _ -> err "No possible derivation." in j ^ r
  | MinusExp (n1, n2, n3), rule -> 
      let j = (string_of_int n1) ^ " minus " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in 
      let r = match rule with Bminus -> " by B-Minus" | _ -> err "No possible derivation." in j ^ r
  | LtExp (n1, n2, b3), rule -> 
      let j = (string_of_int n1) ^ " less than " ^ (string_of_int n2) ^ " is " ^ (string_of_bool b3) in 
      let r = match rule with Blt -> " by B-Lt" | _ -> err "No possible derivation." in j ^ r
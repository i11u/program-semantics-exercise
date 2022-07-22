open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = try Parser.toplevel Lexer.main (Lexing.from_string root) with _ -> err "Parsing failed."

let lookup x env =
  try List.assoc x (List.rev env) with _ -> raise Not_found

let lookup_last x env = 
  let env_rev = List.rev env in 
  let (id, _) = try List.hd env_rev with _ -> err "List head is not found because it's empty." in 
  if x = id then true else false

let except_last env =
  let l_rev = List.rev env in let tl = List.tl l_rev in List.rev tl

let extend x v env = List.append env ((x, v)::[])

let rec eval_exp env exp = 
  (match exp with
  | Var x -> (try lookup x env with Not_found -> err ("Variable not bound." ^ x))
  | ILit i -> IntV i
  | BLit b -> BoolV b
  | BinOp (binOp, e1, e2) -> 
    (match binOp, eval_exp env e1, eval_exp env e2 with
    | Plus, IntV arg1, IntV arg2 -> IntV (arg1 + arg2)
    | Mult, IntV arg1, IntV arg2 -> IntV (arg1 * arg2)
    | Minus, IntV arg1, IntV arg2 -> IntV (arg1 - arg2)
    | Lt, IntV arg1, IntV arg2 -> BoolV (arg1 < arg2)
    | _, _, _ -> err "No possible evaluation.")
  | IfExp (c, t, e) -> 
      (match eval_exp env c with
      | BoolV b -> if b then eval_exp env t else eval_exp env e
      | _ -> err "No possible derivation.")
  | LetExp (id, e1, e2) -> 
      let v = eval_exp env e1 in
      let newenv = (id, v)::env
      in eval_exp newenv e2)

let rec create_dtree judgement =
  (match judgement with
  | EvalExp (env, e, v) -> 
      (match e, v with
      | ILit i1, IntV i2 -> 
          if i1 = i2 then Tree ((judgement, Eint), Empty::[]) else err "No possible derivation."
      | BLit b1, BoolV b2 -> 
          if b1 = b2 then Tree ((judgement, Ebool), Empty::[]) else err "No possible derivation."
      | Var x, _ -> 
          let v1 = try lookup x env with Not_found -> err ("Variable not bound." ^ x) in 
          (* 最後ならVar1, 最後でなければVar2を用いる *)
          let is_last = try lookup_last x env with Error s -> err s in 
          if is_last 
            then 
              if v1 = v
                then Tree ((judgement, Evar1), Empty::[]) 
                else err "Value of e1 does not match e2."
            else
              if v1 = v
                then let t1 = create_dtree (EvalExp ((except_last env), e, v)) in Tree ((judgement, Evar2), t1::[])
                else err "Value of e1 does not match e2."
      | IfExp (c, t, e), _ -> 
          let test = try eval_exp env c with _ -> err "Evaluation failed." in 
          (match test with
          | BoolV b -> 
            if b 
              then 
                let first = try eval_exp env t with _ -> err "Evaluation failed." in 
                if first = v
                  then 
                    let t1 = create_dtree (EvalExp (env, c, BoolV true)) in 
                    let t2 = create_dtree (EvalExp (env, t, v)) in
                    Tree ((judgement, EifT), t1::t2::[]) 
                  else err "No possible derivation."
              else
                let second = try eval_exp env e with _ -> err "Evaluation failed." in
                if second = v  
                  then 
                    let t1 = create_dtree (EvalExp (env, c, BoolV false)) in 
                    let t2 = create_dtree (EvalExp (env, e, v)) in
                    Tree ((judgement, EifF), t1::t2::[]) 
                  else err "No possible derivation."
          | _ -> err "No possible derivation.")
      | BinOp (binOp, l, r), _ -> 
          let left  = try eval_exp env l with _ -> err "Evaluation failed." in 
          let right = try eval_exp env r with _ -> err "Evaluation failed." in 
          (match left, right with
          | IntV i1, IntV i2 -> 
            (match binOp, v with
              | Plus, IntV i3 -> 
                  if i1 + i2 = i3
                    then
                      let t1 = create_dtree (EvalExp (env, l, IntV i1)) in 
                      let t2 = create_dtree (EvalExp (env, r, IntV i2)) in 
                      let t3 = create_dtree (PlusExp (i1, i2, i3)) in 
                      Tree ((judgement, Eplus), t1::t2::t3::[])
                    else err "No possible derivation."
              | Mult, IntV i3 ->
                  if i1 * i2 = i3
                    then
                      let t1 = create_dtree (EvalExp (env, l, IntV i1)) in 
                      let t2 = create_dtree (EvalExp (env, r, IntV i2)) in 
                      let t3 = create_dtree (MultExp (i1, i2, i3)) in 
                      Tree ((judgement, Etimes), t1::t2::t3::[])
                    else err "No possible derivation."
              | Minus, IntV i3 -> 
                  if i1 - i2 = i3
                    then
                      let t1 = create_dtree (EvalExp (env, l, IntV i1)) in 
                      let t2 = create_dtree (EvalExp (env, r, IntV i2)) in 
                      let t3 = create_dtree (MinusExp (i1, i2, i3)) in 
                      Tree ((judgement, Eminus), t1::t2::t3::[])
                    else err "No possible derivation."
              | Lt, BoolV b3 ->
                  if (i1 < i2 && b3) || (i1 >= i2 && not b3)
                    then
                      let t1 = create_dtree (EvalExp (env, l, IntV i1)) in 
                      let t2 = create_dtree (EvalExp (env, r, IntV i2)) in 
                      let t3 = create_dtree (LtExp (i1, i2, b3)) in 
                      Tree ((judgement, Elt), t1::t2::t3::[])
                    else err "No possible derivation."
              | _, _ -> err "No possible derivation.")
          | _, _ -> err "No possible derivation.")
      | LetExp (id, exp1, exp2), _ -> 
          let v1 = try eval_exp env exp1 with _ -> err "Evaluation failed." in 
          let v2 = try eval_exp (extend id v1 env) exp2 with _ -> err "Evaluation failed when env is extended by let-expression." in 
          if v2 = v
            then
              let t1 = create_dtree (EvalExp (env, exp1, v1)) in 
              let t2 = create_dtree (EvalExp ((extend id v1 env), exp2, v)) in 
              Tree ((judgement, Elet), t1::t2::[])
            else
              err (id ^ " is successfully bound by let-expression, but is evaluated to different value.")
      | _, _ -> err "create_dtree error during EvalExp.")
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
  | Var x -> x
  | BinOp (binOp, l, r) -> 
    (match binOp with
    | Plus -> (pp_exp l) ^ " + " ^ (pp_exp r)
    | Mult -> (pp_exp l) ^ " * " ^ (pp_exp r)
    | Minus -> (pp_exp l) ^ " - " ^ (pp_exp r)
    | Lt -> (pp_exp l) ^ " < " ^ (pp_exp r))
  | IfExp (c, t, e) -> 
    "if " ^ (pp_exp c) ^ " then " ^ (pp_exp t) ^ " else " ^ (pp_exp e)
  | LetExp (id, e1, e2) -> 
    "let " ^ id ^ " = " ^ (pp_exp e1) ^ " in " ^ (pp_exp e2))

let pp_value = function
  | IntV i -> string_of_int i
  | BoolV b -> string_of_bool b

let rec pp_env = function
  | [] -> ""
  | (id, v)::[] -> id ^ " = " ^ (pp_value v)
  | (id, v)::tl -> id ^ " = " ^ (pp_value v) ^ ", " ^ (pp_env tl)

let pp_judgement = function 
  | EvalExp (env, l, r)-> 
    let j = (pp_env env) ^ " |- " ^ (pp_exp l) ^ " evalto " ^ (pp_value r) in j
  | PlusExp (n1, n2, n3) -> 
    let j = (string_of_int n1) ^ " plus " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in j
  | MultExp (n1, n2, n3) -> 
    let j = (string_of_int n1) ^ " times " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in j
  | MinusExp (n1, n2, n3) -> 
    let j = (string_of_int n1) ^ " minus " ^ (string_of_int n2) ^ " is " ^ (string_of_int n3) in j
  | LtExp (n1, n2, b3) -> 
    let j = (string_of_int n1) ^ " less than " ^ (string_of_int n2) ^ " is " ^ (string_of_bool b3) in j
    
let pp_derivation = function 
  | EvalExp (env, l, r), rule -> 
      let j = (pp_env env) ^ " |- " ^ (pp_exp l) ^ " evalto " ^ (pp_value r) in
      let r = match rule with 
        | Eint -> " by E-Int"
        | Ebool -> " by E-Bool"
        | Evar1 -> " by E-Var1"
        | Evar2 -> " by E-Var2"
        | EifT -> " by E-IfT"
        | EifF -> " by E-IfF"
        | Eplus -> " by E-Plus"
        | Eminus -> " by E-Minus" 
        | Etimes -> " by E-Times" 
        | Elt -> " by E-Lt"
        | Elet -> " by E-Let"
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
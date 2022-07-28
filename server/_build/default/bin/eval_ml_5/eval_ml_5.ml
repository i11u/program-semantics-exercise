open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = try Parser.toplevel Lexer.main (Lexing.from_string root) with _ -> err "Parsing failed."

let lookup x env =
  (* Var1・Var2の判別に使うので、リストを反転させて先頭から束縛を見ていく *)
  try List.assoc x (List.rev env) with _ -> raise Not_found

let lookup_last x env = 
  let env_rev = List.rev env in 
  let (id, _) = try List.hd env_rev with _ -> err "List head is not found because it's empty." in 
  if x = id then true else false

let except_last env =
  let l_rev = List.rev env in let tl = List.tl l_rev in List.rev tl

let extend x v env = List.append env ((x, v)::[])

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
  | LetExp (x, e1, e2) -> 
    "let " ^ x ^ " = " ^ (pp_exp e1) ^ " in " ^ (pp_exp e2)
  | LetRecExp (x, y, e1, e2) -> 
    "let rec " ^ x ^ " = fun " ^ y ^ " -> " ^ (pp_exp e1) ^ " in " ^ (pp_exp e2)
  | FunExp (x, exp) -> 
    "fun " ^ x ^ " -> " ^ (pp_exp exp)
  | AppExp (e1, e2) -> 
    (match e2 with
    | AppExp _ | FunExp _ | BinOp _ | ConsExp _ -> (pp_exp e1) ^ " " ^ "(" ^ (pp_exp e2) ^ ")"
    |_ -> (pp_exp e1) ^ " " ^ (pp_exp e2))
  | NilExp -> "[]"
  | ConsExp (e1, e2) -> 
    (match e1 with | FunExp _ | ConsExp _ -> "(" ^ (pp_exp e1) ^ ")" | _ -> (pp_exp e1)) 
    ^ " :: " ^ (match e2 with | FunExp _ -> "(" ^ (pp_exp e2) ^ ")" | _ -> (pp_exp e2))
  | MatchExp (e1, e2, x, y, e3) -> 
    "match " ^ (pp_exp e1) ^ " with [] -> " ^ (pp_exp e2) ^ " | " ^ x ^ " :: " ^ y ^ " -> " ^ (pp_exp e3))

let rec pp_env = function
  | [] -> ""
  | (id, v)::[] -> id ^ " = " ^ (pp_value v) ^ (pp_env [])
  | (id, v)::tl -> id ^ " = " ^ (pp_value v) ^ ", " ^ (pp_env tl)

and pp_value = function
  | IntV i -> string_of_int i
  | BoolV b -> string_of_bool b
  | ProcV (x, exp, env') -> 
    "(" ^ (pp_env env') ^ ")" ^ "[fun " ^ x ^ " -> " ^ (pp_exp exp) ^ " ]" 
  | RecProcV (x, y, exp, env') -> 
    "(" ^ (pp_env env') ^ ")" ^ "[rec " ^ x ^ " = fun " ^ y ^ " -> " ^ (pp_exp exp) ^ " ]" 
  | NilV -> "[]"
  | ConsV (v1, v2) -> 
    (match v1 with | ProcV _ | RecProcV _ | ConsV _ -> "(" ^ (pp_value v1) ^ ")" | _ -> (pp_value v1)) 
    ^ " :: " 
    ^ (match v2 with | ProcV _ | RecProcV _ -> "(" ^ (pp_value v2) ^ ")" | _ -> (pp_value v2))

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
        | Evar -> " by E-Var"
        | EifT -> " by E-IfT"
        | EifF -> " by E-IfF"
        | Eplus -> " by E-Plus"
        | Eminus -> " by E-Minus" 
        | Etimes -> " by E-Times" 
        | Elt -> " by E-Lt"
        | Elet -> " by E-Let"
        | Efun -> " by E-Fun"
        | Eapp -> " by E-App"
        | Eletrec -> " by E-LetRec"
        | Eapprec -> " by E-AppRec"
        | Ematchnil -> " by E-MatchNil"
        | Ematchcons -> " by E-MatchCons"
        | Enil -> " by E-Nil"
        | Econs -> " by E-Cons"
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

let rec eval_exp env exp = 
  (match exp with
  | Var x -> (try lookup x env with Not_found -> err ("Variable not bound " ^ x ^ "."))
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
  | LetExp (x, e1, e2) -> 
      let v = eval_exp env e1 in
      let newenv = (x, v)::env
      in eval_exp newenv e2
  | LetRecExp (_, _, _, e2) -> 
      eval_exp env e2
  | FunExp (x, exp) -> 
      ProcV (x, exp, env)
  | AppExp (e1, e2) -> 
      let funval = try eval_exp env e1 with _ -> err ((pp_env env) ^ " and " ^ (pp_exp exp) ^ " and " ^ (pp_exp e1) ^ " and " ^ (pp_exp e2)) in 
      let arg = eval_exp env e2 in 
      (match funval with
      | ProcV (x, e, env') -> 
          let newenv = extend x arg env' in 
          eval_exp newenv e
      | RecProcV (x, y, e, env') ->
        let newenv = extend y arg (extend x funval env') in 
          eval_exp newenv e
      | _ -> err "No possible evaluation.")
  | NilExp -> NilV
  | ConsExp (e1, e2) -> 
      let v1 = eval_exp env e1 in 
      let v2 = eval_exp env e2 in 
      ConsV (v1, v2)
  | MatchExp (e1, e2, x, y, e3) -> 
      let p = eval_exp env e1 in 
      (match p with 
      | NilV -> 
          eval_exp env e2
      | ConsV (v1, v2) -> 
          eval_exp (extend y v2 (extend x v1 env)) e3
      | _ -> err "No possible evaluation."))

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
            if v1 = v
              then Tree ((judgement, Evar), Empty::[]) 
              else err "Value of e does not match v."
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
                let second = try eval_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_env env)) in
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
            let t1 = create_dtree (EvalExp (env, l, IntV i1)) in 
            let t2 = create_dtree (EvalExp (env, r, IntV i2)) in 
            (match binOp, v with
              | Plus, IntV i3 -> 
                  if i1 + i2 = i3
                    then
                      let t3 = create_dtree (PlusExp (i1, i2, i3)) in 
                      Tree ((judgement, Eplus), t1::t2::t3::[])
                    else err "No possible derivation."
              | Mult, IntV i3 ->
                  if i1 * i2 = i3
                    then
                      let t3 = create_dtree (MultExp (i1, i2, i3)) in 
                      Tree ((judgement, Etimes), t1::t2::t3::[])
                    else err "No possible derivation."
              | Minus, IntV i3 -> 
                  if i1 - i2 = i3
                    then
                      let t3 = create_dtree (MinusExp (i1, i2, i3)) in 
                      Tree ((judgement, Eminus), t1::t2::t3::[])
                    else err "No possible derivation."
              | Lt, BoolV b3 ->
                  if (i1 < i2 && b3) || (i1 >= i2 && not b3)
                    then
                      let t3 = create_dtree (LtExp (i1, i2, b3)) in 
                      Tree ((judgement, Elt), t1::t2::t3::[])
                    else err "No possible derivation."
              | _, _ -> err "No possible derivation.")
          | _, _ -> err "No possible derivation.")
      | LetExp (x, e1, e2), _ -> 
          let v1 = try eval_exp env e1 with _ -> err "Evaluation failed." in 
          let v2 = try eval_exp (extend x v1 env) e2 with _ -> err "Evaluation failed when env is extended by let-expression." in 
          if v2 = v
            then
              let t1 = create_dtree (EvalExp (env, e1, v1)) in 
              let t2 = create_dtree (EvalExp ((extend x v1 env), e2, v)) in 
              Tree ((judgement, Elet), t1::t2::[])
            else
              err (x ^ " is successfully bound by let-expression, but is evaluated to different value.")
      | LetRecExp (x, y, e1, e2), _ ->
          let v1 = try eval_exp (extend x (RecProcV (x, y, e1, env)) env) e2 with Error s -> err s in 
          if v1 = v
            then 
              let t1 = create_dtree (EvalExp ((extend x (RecProcV (x, y, e1, env)) env), e2, v)) in 
              Tree ((judgement, Eletrec), t1::[])
            else
              err (x ^ " is successfully bound by let-rec-expression, but is evaluated to different value.")
      | FunExp (x1, e1), ProcV (x2, e2, env') ->
          if x1 = x2 && e1 = e2 && env = env'
            then Tree ((judgement, Efun), Empty::[])
            else err "aaa"
      | AppExp (e1, e2), _ -> 
          let v1 = try eval_exp env e1 with _ -> err "Evaluation failed when evaluating funval of AppExp." in 
          let v2 = try eval_exp env e2 with _ -> err "Evaluation failed when evaluating arg of AppExp." in 
          (match v1 with
          | ProcV (x, e0, env') ->
            let v0 = try eval_exp (extend x v2 env') e0 with _ -> err "Evaluation failed when evaluating the final value of AppExp." in 
            if v0 = v
              then
                let t1 = create_dtree (EvalExp (env, e1, ProcV (x, e0, env'))) in 
                let t2 = create_dtree (EvalExp (env, e2, v2)) in 
                let t3 = create_dtree (EvalExp ((extend x v2 env'), e0, v)) in 
                Tree ((judgement, Eapp), t1::t2::t3::[])
              else err "create_dtree error in the assessment of E-App."
          | RecProcV (x, y, e0, env') -> 
            let v0 = try eval_exp (extend y v2 (extend x v1 env')) e0 with _ -> err ("Evaluation failed in the final value of AppRecExp. Current env is: " ^ (pp_env (extend y v2 env))) in
            if v0 = v
              then
                let t1 = create_dtree (EvalExp (env, e1, v1)) in 
                let t2 = create_dtree (EvalExp (env, e2, v2)) in 
                let t3 = create_dtree (EvalExp ((extend y v2 (extend x v1 env')), e0, v)) in 
                Tree ((judgement, Eapprec), t1::t2::t3::[])
              else err "create_dtree error in the assessment of E-AppRec."
          | _ -> err "Evaluation on funval of AppExp should go to ProcV, but different value is obtained.")
      | NilExp, NilV -> Tree ((judgement, Enil), Empty::[])
      | ConsExp (e1, e2), _ -> 
          let v1 = eval_exp env e1 in 
          let v2 = eval_exp env e2 in 
          if v = ConsV (v1, v2)
            then
              let t1 = create_dtree (EvalExp (env, e1, v1)) in 
              let t2 = create_dtree (EvalExp (env, e2, v2)) in 
              Tree ((judgement, Econs), t1::t2::[])
              else err "create_dtree error in the assessment of E-ConsExp."
      | MatchExp (e1, e2, x, y, e3), _ -> 
          let p = eval_exp env e1 in 
          (match p with
          | NilV -> 
              let result = eval_exp env e2 in 
              if result = v
                then
                  let t1 = create_dtree (EvalExp (env, e1, p)) in 
                  let t2 = create_dtree (EvalExp (env, e2, v)) in 
                  Tree ((judgement, Ematchnil), t1::t2::[])
                else 
                  err "create_dtree error during MatchExp."
          | ConsV (v1, v2) -> 
              let newenv = extend y v2 (extend x v1 env) in 
              let result = eval_exp newenv e3 in
              if result = v 
                then
                  let t1 = create_dtree (EvalExp (env, e1, p)) in 
                  let t2 = create_dtree (EvalExp (newenv, e3, v)) in 
                  Tree ((judgement, Ematchcons), t1::t2::[])
                else 
                  err "create_dtree error during MatchExp."
          | _ -> err "Pattern should go to NilV or ConsV.")
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

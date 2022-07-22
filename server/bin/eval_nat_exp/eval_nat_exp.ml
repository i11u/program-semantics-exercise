open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = try Parser.toplevel Lexer.main (Lexing.from_string root) with Error _ -> err ("Parsing failed.")
let rec eval_exp exp =
  (match exp with
  | Nat i -> i
  | Plus (e1, e2) -> (eval_exp e1) + (eval_exp e2)
  | Mult (e1, e2) -> (eval_exp e1) * (eval_exp e2))

let rec create_dtree judgement = 
  match judgement with
  | EvalExp (e, n) -> 
      (match e with
      | Nat i -> if i = n then Tree ((judgement, Econst), Empty::[]) else err "No possible derivation."
      | Plus (e1, e2) ->
        let n1 = eval_exp e1 and n2 = eval_exp e2 in  
        if n1 + n2 = n
          then
            let t1 = create_dtree (EvalExp (e1, n1)) in 
            let t2 = create_dtree (EvalExp (e2, n2)) in 
            let t3 = create_dtree (PlusExp (n1, n2, n)) in 
            Tree ((judgement, Eplus), t1::t2::t3::[])
          else err ("No possible derivation.")
      | Mult (e1, e2) -> 
        let n1 = eval_exp e1 and n2 = eval_exp e2 in  
        if n1 * n2 = n
          then
            let t1 = create_dtree (EvalExp (e1, n1)) in 
            let t2 = create_dtree (EvalExp (e2, n2)) in 
            let t3 = create_dtree (MultExp (n1, n2, n)) in 
            Tree ((judgement, Etimes), t1::t2::t3::[])
          else err "No possible derivation.")
  | PlusExp (n1, n2, n3) -> 
      (match n1, n2, n3 with
      | 0, _, _ -> 
          if n2 = n3 then Tree ((judgement, Pzero), Empty::[]) else err "No possible derivation."
      | _, _, _ -> 
          if n3 > 0 then 
            let t1 = create_dtree (PlusExp(n1-1, n2, n3-1)) in 
              Tree ((judgement, Psucc), t1::[]) 
            else err "No possible derivation.")
  | MultExp (n1, n2, n3) -> 
      (match n1, n2, n3 with
      | 0, _, _ -> 
          if n3 = 0 then Tree ((judgement, Tzero), Empty::[]) else err "No possible derivation."
      | _, _, _ -> 
          let n4 = (n1-1)*n2 in 
          let t1 = create_dtree (MultExp(n1-1, n2, n4)) in 
          let t2 = create_dtree (PlusExp(n2, n4, n3)) in 
            Tree ((judgement, Tsucc), t1::t2::[]))

let rec pp_nat nat =
  (match nat with
  | 0 -> "Z"
  | _ -> "S("^(pp_nat (nat-1))^")")

let rec pp_exp exp = 
  (match exp with
  | Nat i -> pp_nat i
  | Plus (e1, e2) -> (pp_exp e1) ^ " + " ^ (pp_exp e2)
  | Mult (e1, e2) ->
    (match e1, e2 with
    | Plus _, Plus _ -> "(" ^ (pp_exp e1) ^ ")" ^ " * " ^ "(" ^ (pp_exp e1) ^ ")"
    | Plus _, _ -> "(" ^ (pp_exp e1) ^ ")" ^ " * " ^ (pp_exp e2)
    | _, Plus _ -> (pp_exp e1) ^ " * " ^ "(" ^ (pp_exp e2) ^ ")"
    | _, _ -> (pp_exp e1) ^ " * " ^ (pp_exp e2)))

let pp_judgement = function 
  | EvalExp (e, n) -> 
      let j = (pp_exp e) ^ " evalto " ^ (pp_nat n) in j
  | PlusExp (n1, n2, n3) -> 
      let j = (pp_nat n1) ^ " plus " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in j
  | MultExp (n1, n2, n3) -> 
      let j = (pp_nat n1) ^ " times " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in j

let pp_derivation = function 
  | EvalExp (e, n), rule -> 
      let j = (pp_exp e) ^ " evalto " ^ (pp_nat n) in
      let r = match rule with Econst -> " by E-Const" | Eplus -> " by E-Plus" | Etimes -> " by E-Times" | _ -> err "No possible derivation." in j ^ r
  | PlusExp (n1, n2, n3), rule -> 
      let j = (pp_nat n1) ^ " plus " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in 
      let r = match rule with Pzero -> " by P-Zero" | Psucc -> " by P-Succ" | _ -> err "No possible derivation." in j ^ r
  | MultExp (n1, n2, n3), rule -> 
      let j = (pp_nat n1) ^ " times " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in 
      let r = match rule with Tzero -> " by T-Zero" | Tsucc -> " by T-Succ" | _ -> err "No possible derivation." in j ^ r

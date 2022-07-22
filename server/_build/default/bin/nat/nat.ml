open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = Parser.toplevel Lexer.main (Lexing.from_string root)

let rec create_dtree judgement = 
  match judgement with
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

let pp_judgement = function 
  | PlusExp (n1, n2, n3) -> 
    let j = (pp_nat n1) ^ " plus " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in j
  | MultExp (n1, n2, n3) -> 
    let j = (pp_nat n1) ^ " times " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in j

let pp_derivation = function 
  | PlusExp (n1, n2, n3), rule -> 
      let j = (pp_nat n1) ^ " plus " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in 
      let r = match rule with Pzero -> " by P-Zero" | Psucc -> " by P-Succ" | _ -> err "No possible derivation." in j ^ r
  | MultExp (n1, n2, n3), rule -> 
      let j = (pp_nat n1) ^ " times " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in 
      let r = match rule with Tzero -> " by T-Zero" | Tsucc -> " by T-Succ" | _ -> err "No possible derivation." in j ^ r
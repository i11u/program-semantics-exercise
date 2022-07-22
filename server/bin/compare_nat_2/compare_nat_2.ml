open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = Parser.toplevel Lexer.main (Lexing.from_string root)

let rec create_dtree judgement = 
  (match judgement with
  | LessThanExp (n1, n2) -> 
      match n1, n2 with
      | 0, _ -> 
        if n2 > 0 
          then Tree ((judgement, Lzero), Empty::[]) 
          else err ("No possible derivation.") 
      | _, _ -> 
        let t1 = create_dtree (LessThanExp(n1-1, n2-1)) in 
        Tree ((judgement, Lsuccsucc), t1::[]))

let rec pp_nat nat = 
  (match nat with
  | 0 -> "Z"
  | _ -> "S("^(pp_nat (nat-1))^")")

let pp_judgement = function 
  | LessThanExp (n1, n2) -> 
    let j = (pp_nat n1) ^ " is less than " ^ (pp_nat n2) in j

let pp_derivation = function 
| LessThanExp (n1, n2), rule -> 
    let j = (pp_nat n1) ^ " is less than " ^ (pp_nat n2) in 
    let r = match rule with Lzero -> " by L-Zero" | Lsuccsucc -> " by L-SuccSucc" in j ^ r

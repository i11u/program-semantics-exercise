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
      if n2 = n1 + 1 
        then Tree ((judgement, Lsucc), Empty::[])
        else 
          if n2 > n1 + 1
            then
              let t1 = create_dtree (LessThanExp(n1, n1+1)) in 
              let t2 = create_dtree (LessThanExp(n1+1, n2)) in
              Tree ((judgement, Ltrans), t1::t2::[])
            else err ("No possible derivation."))

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
    let r = match rule with Lsucc -> " by L-Succ" | Ltrans -> " by L-Trans" in j ^ r


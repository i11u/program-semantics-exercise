open Syntax
open Util

type judgement = Syntax.judgement

type rule = Syntax.rule

type derivation = judgement * rule

type dtree = Empty | Tree of derivation * dtree list

let judgement_from_string root = try Parser.toplevel Lexer.main (Lexing.from_string root) with _ -> err ("Parsing failed.")

let rec create_dtree judgement = 
  (match judgement with
  | ReduceExp _ -> Tree ((PlusExp (0, 0, 0), Pzero), Empty::[])
    (* (match e1 with
    | Plus (e11, e12) -> 
      (match e11, e12 with
      | Nat n1, Nat n2 -> 
          (match e2 with Nat n3 -> 
            if n1 + n2 = n3 
            then let t1 = create_dtree (PlusExp(n1, n2, n3)) in Tree ((judgement, Rplus), t1::[])
            else err ("No possible derivation.")
          | _ -> err ("No possible derivation."))
      | _, _ -> 
        (match e2 with
        | Plus (e21, e22) -> 
          if e11 = e21
            then 
              if e12 = e22 then err ("No possible derivation.") 
              else let t1 = create_dtree (ReduceExp (e12, e22)) in Tree ((judgement, Rplusr), t1::[])
            else
              if e12 = e22 then let t1 = create_dtree (ReduceExp (e11, e21)) in Tree ((judgement, Rplusl), t1::[])
              else err ("No possible derivation.")
        | _ -> err ("No possible derivation.")))
    | Mult (e11, e12) -> 
      (match e11, e12 with
      | Nat n1, Nat n2 -> 
          (match e2 with Nat n3 -> 
            if n1 * n2 = n3 
            then let t1 = create_dtree (MultExp(n1, n2, n3)) in Tree ((judgement, Rtimes), t1::[])
            else err ("No possible derivation.")
          | _ -> err ("No possible derivation."))
      | _, _ -> 
        (match e2 with
        | Mult (e21, e22) -> 
          if e11 = e21
            then 
              if e12 = e22 then err ("No possible derivation.") 
              else let t1 = create_dtree (ReduceExp (e12, e22)) in Tree ((judgement, Rtimesr), t1::[])
            else
              if e12 = e22 then let t1 = create_dtree (ReduceExp (e11, e21)) in Tree ((judgement, Rtimesl), t1::[])
              else err ("No possible derivation.")
        | _ -> err ("No possible derivation.")))
    | _ -> err ("No possible derivation.")) *)
  | DReduceExp _ -> Tree ((PlusExp(1, 1, 1), Pzero), Empty::[])
  | MReduceExp _ -> Tree ((PlusExp(1, 1, 1), Pzero), Empty::[])
  | PlusExp (n1, n2, n3) -> 
      (match n1, n2, n3 with
      | 0, _, _ -> 
          if n2 = n3 then Tree ((judgement, Pzero), Empty::[]) else err "No possible derivation."
      | _, _, _ -> 
          if n3 > 0 then 
            let t1 = create_dtree (PlusExp(n1-1, n2, n3-1)) in 
              Tree ((judgement, Psucc), t1::[]) 
            else err ("No possible derivation."))
  | MultExp (n1, n2, n3) -> 
      (match n1, n2, n3 with
      | 0, _, _ -> 
          if n3 = 0 then Tree ((judgement, Tzero), Empty::[]) else err "No possible derivation."
      | _, _, _ -> 
          let n4 = (n1-1)*n2 in 
          let t1 = create_dtree (MultExp(n1-1, n2, n4)) in 
          let t2 = create_dtree (PlusExp(n2, n4, n3)) in 
            Tree ((judgement, Tsucc), t1::t2::[])))

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

let pp_derivation = function 
  | ReduceExp (e1, e2), rule -> 
      let j = (pp_exp e1) ^ " ---> " ^ (pp_exp e2) in
      let r = match rule with 
        | Rplus -> " by R-Plus" 
        | Rtimes -> " by R-Times" 
        | Rplusl -> " by R-PlusL" 
        | Rplusr -> " by R-PlusR" 
        | Rtimesl -> " by R-TimesL" 
        | Rtimesr -> " by R-TimesR" 
        | _ -> err "No possible derivation." 
      in j ^ r
  | DReduceExp (e1, e2), rule -> 
      let j = (pp_exp e1) ^ " -d-> " ^ (pp_exp e2) in 
      let r = match rule with 
        | DRplus -> " by DR-Plus" 
        | DRtimes -> " by DR-Times" 
        | DRplusl -> " by DR-PlusL" 
        | DRplusr -> " by DR-PlusR" 
        | DRtimesl -> " by DR-TimesL" 
        | DRtimesr -> " by DR-TimesR" 
        | _ -> err "No possible derivation." 
      in j ^ r
  | MReduceExp (e1, e2), rule -> 
      let j = (pp_exp e1) ^ " -*-> " ^ (pp_exp e2) in 
      let r = match rule with 
        | MRzero -> " by MR-Zero" 
        | MRmulti -> " by MR-Multi" 
        | MRone -> " by MR-One" 
        | _ -> err "No possible derivation." 
      in j ^ r
  | PlusExp (n1, n2, n3), rule -> 
      let j = (pp_nat n1) ^ " plus " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in 
      let r = match rule with Pzero -> " by P-Zero" | Psucc -> " by P-Succ" | _ -> err "No possible derivation." in j ^ r
  | MultExp (n1, n2, n3), rule -> 
      let j = (pp_nat n1) ^ " times " ^ (pp_nat n2) ^ " is " ^ (pp_nat n3) in 
      let r = match rule with Tzero -> " by T-Zero" | Tsucc -> " by T-Succ" | _ -> err "No possible derivation." in j ^ r

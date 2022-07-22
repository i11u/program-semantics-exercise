open Util

module Derive(ProofSys: PROOF_SYS) = struct
  let derive_tree root = 
    let rec pp_dtree (dtree : ProofSys.dtree) = 
      (match dtree with
      | Empty -> ""
      | Tree (d, l) -> 
          let rec derive_from_list l =
            (match l with
            | [] -> ""
            | h::[] -> pp_dtree h;
            | h::t -> (pp_dtree h) ^ ";" ^ (derive_from_list t))
          in (ProofSys.pp_derivation d) ^ "{" ^ (derive_from_list l) ^ "}") in 
    try root |> ProofSys.judgement_from_string |> ProofSys.create_dtree |> pp_dtree with Error s -> s 
    (* try root |> ProofSys.judgement_from_string |> ProofSys.pp_judgement with Error s -> s  *)
end

let derive_tree s =
  (match s with
  | "Nat" -> let module D = Derive(Nat : PROOF_SYS) in D.derive_tree
  | "CompareNat1" -> let module D = Derive(Compare_nat_1 : PROOF_SYS) in D.derive_tree
  | "CompareNat2" -> let module D = Derive(Compare_nat_2 : PROOF_SYS) in D.derive_tree
  | "CompareNat3" -> let module D = Derive(Compare_nat_3 : PROOF_SYS) in D.derive_tree
  | "EvalNatExp" -> let module D = Derive(Eval_nat_exp : PROOF_SYS) in D.derive_tree
  (* | "ReduceNatExp" -> let module D = Derive(Reduce_nat_exp : PROOF_SYS) in D.derive_tree *)
  | "EvalML1" -> let module D = Derive(Eval_ml_1 : PROOF_SYS) in D.derive_tree
  | "EvalML1Err" -> let module D = Derive(Eval_ml_1_err : PROOF_SYS) in D.derive_tree
  | "EvalML2" -> let module D = Derive(Eval_ml_2 : PROOF_SYS) in D.derive_tree
  | "EvalML3" -> let module D = Derive(Eval_ml_3 : PROOF_SYS) in D.derive_tree
  | "EvalML4" -> let module D = Derive(Eval_ml_4 : PROOF_SYS) in D.derive_tree
  | _ -> err ("No such proof system: "^s))
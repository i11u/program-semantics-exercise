exception Error of string 

let err s = raise (Error s)

module type PROOF_SYS =
  sig
    type judgement
    type rule
    type derivation = judgement * rule
    type dtree = Empty | Tree of derivation * dtree list
    val judgement_from_string : string -> judgement
    val create_dtree : judgement -> dtree
    val pp_judgement : judgement -> string
    val pp_derivation : derivation -> string
  end
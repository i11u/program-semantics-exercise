open Opium

type t =
  { proofSysName : string
  ; root : string
  }

let resolve_lwt lwt =
  match Lwt.state lwt with
  | Lwt.Return x -> x
  | _ -> failwith "Could not resolve lwt."
;;

let yojson_of_t t = `Assoc [ "proofSysName", `String t.proofSysName; "root", `String t.root ]

let t_of_yojson yojson_lwt =
  let yojson = resolve_lwt yojson_lwt in 
  match yojson with
  | `Assoc [ "proofSysName", `String n; "root", `String r ] -> { proofSysName=n; root=r }
  | _ -> failwith "invalid request json"
;;

let json req = 
  let open Lwt.Syntax in 
  let+ res = try Request.to_json_exn req with _ -> failwith "Request body is not in JSON format." in 
  res
;;
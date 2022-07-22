open Opium

let headers = 
  ("Access-Control-Allow-Origin","http://www.fos.kuis.kyoto-u.ac.jp")::[]

let request_handler req = 
  let problem = req |> Problem.json |> Problem.t_of_yojson in 
  let (proofSysName, root) = (problem.Problem.proofSysName, problem.Problem.root) in 
  (* 本当は"result = Derive(getProofSys proofSysName).derive_treeのように、
     functorの引数に、モジュールを返す関数を入れて書きたかったが、できないようだ" *)
  let result = Derive.derive_tree proofSysName root in
  Response.make ~headers:(Headers.of_list headers) ~body:(`Assoc ["result", `String result] |> Yojson.Basic.pretty_to_string |> Body.of_string) () |> Lwt.return
;;

let _ =
  App.empty
  |> App.post "/" request_handler
  |> App.run_command
;;
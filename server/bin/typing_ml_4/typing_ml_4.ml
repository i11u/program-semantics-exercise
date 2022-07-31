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

and pp_ty = function 
  | TyVar i -> "'"^(Char.escaped (Char.chr (i+97)))
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyList t -> (pp_ty t) ^ " list"
  | TyFun (t1, t2) ->
    match t1 with TyFun _ -> "(" ^ (pp_ty t1) ^ ") -> " ^ (pp_ty t2) | _ -> (pp_ty t1) ^ " -> " ^ (pp_ty t2)

let rec pp_tyenv1 = function
  | [] -> ""
  | (id, t)::[] -> id ^ " : " ^ (pp_ty t) ^ (pp_tyenv1 [])
  | (id, t)::tl -> id ^ " : " ^ (pp_ty t) ^ ", " ^ (pp_tyenv1 tl)

let rec pp_tyenv = function
  | [] -> ""
  | (id, (_, t))::[] -> id ^ " : " ^ (pp_ty t) ^ (pp_tyenv [])
  | (id, (_, t))::tl -> id ^ " : " ^ (pp_ty t) ^ ", " ^ (pp_tyenv tl)

let pp_judgement = function 
  | TyExp (env, l, r)-> 
    let j = (pp_tyenv1 env) ^ " |- " ^ (pp_exp l) ^ " : " ^ (pp_ty r) in j
    
let pp_derivation = function 
  | TyExp (tyenv, l, r), rule -> 
      let j = (pp_tyenv1 tyenv) ^ " |- " ^ (pp_exp l) ^ " : " ^ (pp_ty r) in
      let r = match rule with 
        | Tint -> " by T-Int" 
        | Tbool -> " by T-Bool"
        | Tif -> " by T-If"
        | Tplus -> " by T-Plus"
        | Tminus -> " by T-Minus"
        | Ttimes -> " by T-Times"
        | Tlt -> " by T-Lt"
        | Tvar -> " by T-Var"
        | Tlet -> " by T-Let"
        | Tfun -> " by T-Fun"
        | Tapp -> " by T-App"
        | Tletrec -> " by T-LetRec"
        | Tnil -> " by T-Nil"
        | Tcons -> " by T-Cons"
        | Tmatch -> " by T-Match"
      in j ^ r

let rec pp_eqs eqs =
  (match eqs with
    [] -> ""
  | (ty1, ty2)::tl -> 
      (pp_ty ty1) ^ " = " ^ (pp_ty ty2) ^ ", " ^ (pp_eqs tl))

let rec pp_subst (subst : (tyvar * ty) list) =
  (match subst with
    [] -> ""
  | (ty1, ty2)::tl -> 
      (pp_ty (TyVar ty1)) ^ "=" ^ (pp_ty ty2) ^ ", " ^ (pp_subst tl))

let fresh_tyvar = 
  let counter = ref 0 in (* 次に返すべきtyvar型の値を参照で持っておいて *)
  let body () =
    let v = !counter in 
      counter := v + 1; v (* 呼び出されたら参照をインクリメントして、古いcounterの参照先の値を返す *)
  in body

(* tyに現れる自由な型変数の識別子（つまり、tyvar型の集合）を返す関数 *)
(* let rec freevar_ty ty = 
  (match ty with
      TyInt -> MySet.empty
    | TyBool -> MySet.empty
    | TyVar i -> MySet.singleton i
    | TyFun (ty1, ty2) -> MySet.union (freevar_ty ty1) (freevar_ty ty2)
    | TyList t -> freevar_ty t) *)
    
let rec occurs tx t = 
  if tx = t then true
  else 
    match t with
    | TyFun (t1, t2) -> (occurs tx t1) || (occurs tx t2)
    | TyList t' -> (occurs tx t')
    | _ -> false

(* 型代入を目的の式の型に適用し、式全体の型を得る関数 *)
let rec subst_type subst ty =
  (match ty with
      TyVar i ->
        let rec subst_ty i = function
            [] -> ty
          | ((id, typ)::tl) -> if id = i then typ else subst_ty id tl
        in subst_ty i subst
    | TyFun (ty1, ty2) -> TyFun (subst_type subst ty1, subst_type subst ty2)
    | _ -> ty)

(* 型代入を型の等式集合に変換する。型の等式制約ty1 = ty2は(ty1, ty2)というペアで表現し、
   等式集合はペアのリストで表現 *)
let eqs_of_subst s = List.map (fun (n, t) -> (TyVar n, t)) s

(* 型の等式集合に型代入を適用する関数 *)
let rec subst_ty subst ty =
  let rec subst_ty1 subst1 id =
    match subst1 with
    | [] -> TyVar id
    | (tx, t1) :: subst2 -> 
      if tx = id then t1
      else subst_ty1 subst2 id
    in match ty with
    | TyInt -> TyInt
    | TyBool -> TyBool
    | TyFun (t2, t3) -> TyFun (subst_ty subst t2, subst_ty subst t3)
    | TyVar id -> subst_ty1 subst id
    | TyList t' -> TyList (subst_ty subst t')

let subst_eqs subst eqs =
  List.map (fun (t1, t2) -> (subst_ty subst t1, subst_ty subst t2)) eqs 

(* 全ての制約の要素（型のペア）を同じ型にするような型代入を返し、存在しなければエラーを返す *)
let rec unify cstr =
  (match cstr with
    [] -> []
  | (ty1, ty2)::tl -> 
    if ty1 = ty2 then unify tl else
      (match ty1, ty2 with
        | TyFun (ty11, ty12), TyFun (ty21, ty22) -> unify ((ty11, ty21)::((ty12, ty22)::tl))
        | TyList t1', TyList t2' -> unify ((t1', t2')::tl)
        | TyVar id, ty | ty, TyVar id -> 
            (* idがtyの自由型変数ならばエラー（occur check） *)
            (* if (MySet.member id (freevar_ty ty)) then err ("unification error") else *)
            if (occurs (TyVar id) ty) then err ("unification error") else
            (* ty1, ty2に自由型変数idが存在するならばidにtyを代入する *)
            let sub = subst_ty [(id, ty)] in
            let s = unify (List.map (fun (t1, t2) -> (sub t1, sub t2)) cstr) in
            (id, subst_ty s ty)::(unify (subst_eqs [(id, ty)] cstr))
        | _, _ -> err ("unification error " ^ (pp_eqs cstr))))

let ty_prim op ty1 ty2 = match op with
    Plus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Mult -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Minus -> ([(ty1, TyInt); (ty2, TyInt)], TyInt)
  | Lt -> ([(ty1, TyInt); (ty2, TyInt)], TyBool)

module IntSet = Set.Make (struct type t = int let compare = compare end)

let rec free_tyvar = function
  | TyInt | TyBool -> IntSet.empty
  | TyVar n -> IntSet.singleton n
  | TyList t -> free_tyvar t
  | TyFun (t1, t2) -> IntSet.union (free_tyvar t1) (free_tyvar t2)

let mono_ty t = (IntSet.empty, t)

let poly_ty t env =
  let vs = List.fold_left (fun fvs (_, (vs, t)) ->
    IntSet.union fvs (IntSet.diff (free_tyvar t) vs)) IntSet.empty env in
  (IntSet.diff (free_tyvar t) vs, t)

let ty_exp env exp = 
  let e = List.map (fun (id, v) -> (id, (IntSet.empty, v))) env in 
  let rec ty_exp env exp = 
    (match exp with
    | ILit _ -> ([], TyInt)
    | BLit _ -> ([], TyBool)
    | IfExp (c, t, e) -> 
        let (s1, t1) = try ty_exp env c with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let (s2, t2) = try ty_exp env t with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let (s3, t3) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let eqs = (t1, TyBool) :: (t2, t3) :: (eqs_of_subst (s1 @ s2 @ s3)) in 
        let s4 = unify eqs in (s4, subst_ty s4 t2)
    | BinOp (binOp, e1, e2) -> 
        let (s1, t1) = try ty_exp env e1 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let (s2, t2) = try ty_exp env e2 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let (eqs3, ty) = ty_prim binOp t1 t2 in 
        let eqs = (eqs_of_subst s1) @ (eqs_of_subst s2) @ eqs3 in
        let s3 = unify eqs in (s3, subst_ty s3 ty)
    | Var x -> let (ns, t) = List.assoc x env in
      let s = IntSet.fold (fun n s -> (n, TyVar (fresh_tyvar ())) :: s) ns [] in 
      ([], subst_ty s t)
    | LetExp (id, e1, e2) -> 
        let (s1, t1) = ty_exp env e1 in
        let sub = subst_ty s1 in
        let env2 = List.map (fun (id, (vs, t)) -> (id, (vs, sub t))) env in
        let tysc = poly_ty t1 env2 in
        let (s2, t2) = ty_exp ((id, tysc) :: env) e2 in
        let s3 = unify (eqs_of_subst (s1 @ s2)) in
        (s3, subst_ty s3 t2)
    | FunExp (id, exp) -> 
        let domty = TyVar (fresh_tyvar ()) in 
        let (s, ranty) = ty_exp ((id, mono_ty domty) :: env) exp in 
        (s, TyFun (subst_ty s domty, ranty))
    | AppExp (e1, e2) -> 
        let (s1, t1) = try ty_exp env e1 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let (s2, t2) = try ty_exp env e2 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        (match t1, t2 with
        | TyFun (ty1, ty2), _ -> 
            let eqs = (ty1, t2) :: (t1, TyFun (ty1, ty2)) :: [] in 
            let s3 = unify eqs in 
            (s3, subst_ty s3 ty2)
        | TyVar _, _ -> 
            let domty = TyVar (fresh_tyvar ()) in 
            let eqs = (t1, TyFun (t2, domty)) :: ((eqs_of_subst s1) @ (eqs_of_subst s2)) in 
            let s3 = unify eqs in 
            (s3, subst_ty s3 domty)
        | _ -> err "Type of function does not match.")
    | LetRecExp (id1, id2, e1, e2) -> 
        let (v1, v2) = (fresh_tyvar (), fresh_tyvar ()) in
        let (s1, t1) = ty_exp ((id1, mono_ty (TyVar v1)) :: (id2, mono_ty (TyVar v2)) :: env) e1 in
        let s2 = unify ((TyVar (v1), TyFun (TyVar v2, t1)) :: eqs_of_subst s1) in
        let sub = subst_ty s2 in
        let env2 = List.map (fun (id, (vs, t)) -> (id, (vs, sub t))) env in
        let tysc = poly_ty (sub (TyVar v1)) env2 in
        let (s3, t3) = ty_exp ((id1, tysc) :: env) e2 in
        let s4 = unify (eqs_of_subst (s2 @ s3)) in
        (s4, subst_ty s4 t3)
    | NilExp -> 
        let elemty = TyVar (fresh_tyvar ()) in 
        ([], TyList elemty)
    | ConsExp (e1, e2) -> 
        let (s1, t1) = try ty_exp env e1 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let (s2, t2) = try ty_exp env e2 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv env)) in 
        let eqs = (t2, TyList t1) :: eqs_of_subst (s1 @ s2) in 
        let s = unify eqs in (s, subst_ty s t2)
    | MatchExp (e1, e2, x, y, e3) -> 
        let (s1, t1) = ty_exp env e1 in
        let (s2, t2) = ty_exp env e2 in
        let v = fresh_tyvar () in
        let (s3, t3) = ty_exp ((x, mono_ty (TyVar v)) :: (y, mono_ty (TyList (TyVar (v)))) :: env) e3 in
        let s4 = unify ((t1, TyList (TyVar (v))) :: (t2, t3) :: eqs_of_subst (s1 @ s2 @ s3)) in
        (s4, subst_ty s4 t2))
  in ty_exp e exp

let rec create_dtree judgement =
  (match judgement with
  | TyExp (env, e, t) -> 
      (match e, t with
      | ILit _, TyInt -> 
          Tree ((judgement, Tint), Empty::[])
      | BLit _, TyBool -> 
          Tree ((judgement, Tbool), Empty::[])
      | IfExp (c, l, r), _ -> 
          let (_, ty) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
          if ty = t
            then
              let t1 = create_dtree (TyExp (env, c, TyBool)) in 
              let t2 = create_dtree (TyExp (env, l, ty)) in
              let t3 = create_dtree (TyExp (env, r, ty)) in 
              Tree ((judgement, Tif), t1::t2::t3::[])
            else
              err "No possible derivation."
      | BinOp (binOp, l, r), _ -> 
          let (_, ty) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
          (match binOp with
            | Plus -> 
                if ty = TyInt
                  then
                    let t1 = create_dtree (TyExp (env, l, TyInt)) in 
                    let t2 = create_dtree (TyExp (env, r, TyInt)) in 
                    Tree ((judgement, Tplus), t1::t2::[])
                  else err "Type of e does not match t."
            | Mult -> 
                if ty = TyInt
                  then
                    let t1 = create_dtree (TyExp (env, l, TyInt)) in 
                    let t2 = create_dtree (TyExp (env, r, TyInt)) in 
                    Tree ((judgement, Ttimes), t1::t2::[])
                  else err "Type of e does not match t."
            | Minus -> 
              if ty = TyInt
                then
                  let t1 = create_dtree (TyExp (env, l, TyInt)) in 
                  let t2 = create_dtree (TyExp (env, r, TyInt)) in 
                  Tree ((judgement, Tminus), t1::t2::[])
                else err "Type of e does not match t."
            | Lt ->
                if ty = TyBool
                  then
                    let t1 = create_dtree (TyExp (env, l, TyInt)) in 
                    let t2 = create_dtree (TyExp (env, r, TyInt)) in 
                    Tree ((judgement, Tlt), t1::t2::[])
                  else err "Type of e does not match t.")
      | Var _, _ -> 
          let (_, ty) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
          if ty = t
            then Tree ((judgement, Tvar), Empty::[])
            else err "Type of e does not match t."
      | LetExp (x, e1, e2), _ -> 
          let (_, ty2) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
          if ty2 = t
            then
              let (_, ty1) = try ty_exp env e1 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
              let t1 = create_dtree (TyExp (env, e1, ty1)) in 
              let t2 = create_dtree (TyExp ((extend x ty1 env), e2, ty2)) in 
              Tree ((judgement, Tlet), t1::t2::[])
            else err "Type of e does not match t."
      | FunExp (x, exp), _ ->
          let (_, ty) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in
          if ty = t
            then
              (match ty with
              | TyFun (ty1, ty2) -> 
                  let t1 = create_dtree (TyExp ((extend x ty1 env), exp, ty2)) in 
                  Tree ((judgement, Tfun), t1::[])
              | _ -> err ("Type of e should be TyFun, but got " ^ (pp_ty ty)))
            else err ("Type of e does not match t. Expected type " ^ (pp_ty t) ^ ", but got " ^ (pp_ty ty))
      | AppExp (e1, e2), _ -> 
          let (_, ty2) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
          if ty2 = t
            then
              let (_, ty1) = try ty_exp env e2 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
              let t1 = create_dtree (TyExp (env, e1, TyFun (ty1, ty2))) in 
              let t2 = create_dtree (TyExp (env, e2, ty1)) in 
              Tree ((judgement, Tapp), t1::t2::[])
            else
              err "Type of e does not match t."
      (* | LetRecExp (x, y, e1, e2), _ ->
          let (_, ty) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in 
          if ty = t
            then
              let t1 = create_dtree (TyExp ((extend y ty1 (extend x TyFun (ty1, ty2) env)), e1, ty2)) in
              let t2 = create_dtree (TyExp ((extend x TyFun (ty1, ty2) env), e2, ty)) in 
              Tree ((judgement, Tletrec), t1::t2::[])
            else
              err "Type of e does not match t." *)
      | NilExp, TyList _ -> Tree ((judgement, Tnil), Empty::[])
      | ConsExp (e1, e2), _ -> 
          let (_, tyl) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in
          if tyl = t
            then
              (match tyl with
              | TyList ty -> 
                  let t1 = create_dtree (TyExp (env, e1, ty)) in 
                  let t2 = create_dtree (TyExp (env, e2, tyl)) in 
                  Tree ((judgement, Tcons), t1::t2::[])
              | _ -> err ("Type of e should be TyList, but got " ^ (pp_ty tyl)))
            else
              err ("Type of e does not match t." ^ (pp_ty tyl) ^ (pp_ty t))
      | MatchExp (e1, e2, x, y, e3), _ -> 
          let (_, ty) = try ty_exp env e with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in
          if ty = t
            then
              let (_, tyl') = try ty_exp env e1 with Error s -> err ("Error " ^ s ^ " Current env is: " ^ (pp_tyenv1 env)) in
              (match tyl' with
              | TyList ty' -> 
                let t1 = create_dtree (TyExp (env, e1, tyl')) in
                let t2 = create_dtree (TyExp (env, e2, ty)) in 
                let t3 = create_dtree (TyExp ((extend y ty' (extend x ty' env)), e3, ty)) in 
                Tree ((judgement, Tmatch), t1::t2::t3::[])
              | _ -> err ("Type of e should be TyList, but got " ^ (pp_ty tyl')))
            else
              err "Type of e does not match t."
      | _, _ -> err "create_dtree error during EvalExp."))

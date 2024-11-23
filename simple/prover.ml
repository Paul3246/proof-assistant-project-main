open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

type context = (var * ty) list

type sequent =  context * ty

exception Type_error

(*gives a string representation of a type*)
let rec string_of_ty ty =
  match ty with
  | TVar x -> x
  | TArr (ty1, ty2) ->
    Printf.sprintf "(%s ⇒ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | TPair (ty1, ty2) -> Printf.sprintf "(%s ∧ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | TUnit -> "(⊤)"
  | TCoprod (ty1, ty2) -> Printf.sprintf "(%s ∨ %s)" (string_of_ty ty1) (string_of_ty ty2)
  | TFalse -> "⊥"

(*gives a string representation of a term*)
let rec string_of_tm tm =
  match tm with
  | Var x -> x
  | App (tm1, tm2) ->
    Printf.sprintf "(%s %s)" (string_of_tm tm1) (string_of_tm tm2)
  | Abs (x, ty, tm) ->
    Printf.sprintf "(fun (%s : %s) -> %s)" x (string_of_ty ty) (string_of_tm tm)
  | Pair (tm1, tm2) ->
    Printf.sprintf "(%s, %s)" (string_of_tm tm1) (string_of_tm tm2)
  | Fst tm -> Printf.sprintf "(π₁ %s)" (string_of_tm tm)
  | Snd tm -> Printf.sprintf "(π₂ %s)" (string_of_tm tm)
  | Unit -> "()"
  | Left (tm, _) -> Printf.sprintf "(ιl %s)" (string_of_tm tm)
  | Right (_, tm) -> Printf.sprintf "(ιr %s)" (string_of_tm tm)
  | Case (tm1, tm2, tm3) ->
    Printf.sprintf "(case %s of %s | %s)" (string_of_tm tm1) (string_of_tm tm2) (string_of_tm tm3)
  | Absurd (tm, _) -> Printf.sprintf "(absurd %s)" (string_of_tm tm)

let rec infer_type ctx tm =
    match tm with
    | Var x ->begin
      match List.assoc_opt x ctx with
      | Some ty -> ty
      | None -> raise Type_error
    end
    | Abs(x, ty1, tm1) ->
      let ty' = infer_type ((x, ty1)::ctx) tm1 in
      TArr(ty1, ty')
    | App(tm1, tm2) ->begin
      match infer_type ctx tm1 with
      | TArr(ty1, ty2) ->
        check_type ctx tm2 ty1;
        ty2
      | _ -> raise Type_error
      end
    | Pair(tm1, tm2) ->
      TPair(infer_type ctx tm1, infer_type ctx tm2)
    | Fst tm ->begin
      match infer_type ctx tm with
      | TPair(ty1, _) -> ty1
      | _ -> raise Type_error
      end
    | Snd tm ->begin
      match infer_type ctx tm with
      | TPair(_, ty2) -> ty2
      | _ -> raise Type_error
      end
    | Unit -> TUnit
    | Left (tm, ty) -> TCoprod(infer_type ctx tm, ty)
    | Right (ty, tm) -> TCoprod(ty, infer_type ctx tm)
    | Case(tm1, tm2, tm3) ->begin
      match infer_type ctx tm1 with
      | TCoprod(ty1, ty2) ->
        let ty' = infer_type ctx tm2 in
        let ty'' = infer_type ctx tm3 in
        begin
        match ty', ty'' with
        | TArr(ty1', ty), TArr(ty2', ty') when ty1 = ty1' && ty2 = ty2' && ty = ty' -> ty
        | TArr(ty1', ty), TArr(ty2', ty') -> Printf.printf "%s\n" (string_of_ty ty); Printf.printf "%s\n" (string_of_ty ty'); Printf.printf "%s\n" (string_of_ty ty1); Printf.printf "%s\n" (string_of_ty ty1'); Printf.printf "%s\n" (string_of_ty ty2); Printf.printf "%s\n" (string_of_ty ty2'); raise Type_error
        | _ -> raise Type_error
        end
      | _ -> raise Type_error
      end
    | Absurd (tm, ty) ->begin
      match infer_type ctx tm with
      | TFalse -> ty
      | _ -> raise Type_error
      end
  and check_type ctx tm ty =
    if infer_type ctx tm = ty then () else raise Type_error

let string_of_ctx ctx =
  let rec aux ctx =
    match ctx with
    | [] -> ""
    | (x, ty)::ctx' -> if ctx' = [] then Printf.sprintf "%s : %s" x (string_of_ty ty) else Printf.sprintf "%s : %s , %s" x (string_of_ty ty) (aux ctx')
  in
  Printf.sprintf "%s" (aux ctx)

let string_of_seq seq =
  let ctx, ty = seq in
  Printf.sprintf "%s ⊢ %s" (string_of_ctx ctx) (string_of_ty ty)

let find x env =
  try List.assoc x env with Not_found -> raise Not_found

let fresh_var =
  let r = ref 0 in
  fun () -> incr r; Printf.sprintf "x%d" !r

let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
      (
        match a with
        | TArr (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
        |TPair (a, b) ->
          let ta = prove env a in
          let tb = prove env b in
          Pair (ta, tb)
        | TUnit -> Unit
        | _ ->
          error "Don't know how to introduce this."
      )
  | "exact" ->
      let t = tm_of_string arg in
      if infer_type env t <> a then error "Not the right type."
      else t
  | "elim" ->
      if arg = "" then error "Please provide an argument for elim." else
      let t = tm_of_string arg in
      let t_type = find arg env in
      (
        match t_type with
        | TArr (a', b) ->
          if a <> b then error "Not the right type."
          else
            let u = prove env a' in
            App (t, u)
        | TCoprod (a', b') ->
          let var_left = fresh_var () in
          let var_right = fresh_var () in
          let u = Abs(var_left, a', prove ((var_left, a')::env) a) in
          let v = Abs(var_right, b', prove ((var_right, b')::env) a) in
          Case (t, u, v)
        | TFalse -> Absurd (t, a)
        | _ -> error "Not the right type."
      )
  | "cut" ->
      let n_type = ty_of_string arg in
      let n_a = TArr (n_type, a) in
      let t = prove env n_a in
      let u = prove env n_type in
      App (t, u)
  | "fst" ->
    if arg = "" then error "Please provide an argument for fst." else
    let t = tm_of_string arg in
    let t_type = infer_type env t in
    (
      match t_type with
      | TPair (a', _) ->
        if a <> a' then error "Not the right type."
        else
          Fst t
      | _ -> error "Not the right type."
    )
  | "snd" ->
    if arg = "" then error "Please provide an argument for snd." else
    let t = tm_of_string arg in
    let t_type = infer_type env t in
    (
      match t_type with
      | TPair (_, b') ->
        if a <> b' then error "Not the right type."
        else
          Snd t
      | _ -> error "Not the right type."
    )
  | "left" ->
    begin match a with
    | TCoprod (a', b') ->
      let t = prove env a' in
      Left (t, b')
    | _ -> error "Not the right type."
    end
  | "right" ->
    begin match a with
    | TCoprod (a', b') ->
      let t = prove env b' in
      Right (a', t)
    | _ -> error "Not the right type."
    end
  | cmd -> error ("Unknown command: " ^ cmd)
          
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."

(*tests*)

(* let coprod_comm =
  Abs("x", TCoprod(TVar "A", TVar "B"), Case(Var "x", Abs("y", TVar "A", Right(TVar "B", Var"y")), Abs("y", TVar "B", Left(Var "y", TVar "A"))))

let proof = Abs("x", TPair(TVar "A", TArr(TVar "A", TFalse)), Absurd(App(Snd(Var "x"), Fst(Var "x")), TVar "B"))
(*test*)
let _ =
  let ty = TArr (TArr (TVar "A", TVar "B"), TArr(TVar "A", TVar "C")) in
  let tm = Abs ("f", TArr(TVar"A", TVar "B"), Abs ("x", TVar "A", App (Var "f", Var "x"))) in
  let tm2 = Abs ("f", TArr(TVar"A", TVar "B"), Abs ("g", TArr(TVar "B", TVar "C"), Abs ("x", TVar "A", App(Var"g",App(Var"f",Var"x"))))) in
  (* let tm3 = Abs ("f", TVar "A", Var "x") in *)
  (* let tm4 = Abs ("f", TVar "A", Abs ("x", TVar "B", App(Var "f", Var "x"))) in *)
  (* let tm5 = Abs ("f", TArr(TVar"A", TVar"B"), Abs ("x", TVar "B", App(Var "f", Var "x"))) in *)
  let tm6 = Abs ("x", TVar "A", Var "x") in
  let tm7 = Abs ("x", TPair(TVar "A", TVar "B"), Pair(Snd(Var "x"), Fst(Var "x"))) in
  let tm8 = Abs ("x", TArr (TUnit, TVar "A"), App(Var "x", Unit)) in
  (* let tm7 = Var "x" in *)
  Printf.printf "%s\n" (string_of_ty ty);
  Printf.printf "%s\n" (string_of_tm tm);
  Printf.printf "%s\n" (infer_type [] tm2 |> string_of_ty);
  (* Printf.printf "%s\n" (infer_type [] tm3 |> string_of_ty); *)
  (* Printf.printf "%s\n" (infer_type [] tm4 |> string_of_ty) *)
  (* Printf.printf "%s\n" (infer_type [] tm5 |> string_of_ty) *)
  Printf.printf "%s\n" (infer_type [] tm7 |> string_of_ty);
  Printf.printf "%s\n" (infer_type [] tm8 |> string_of_ty);
  assert (check_type [] tm6 (TArr (TVar"A", TVar"A")) = ());
  Printf.printf "%s\n" (infer_type [] coprod_comm |> string_of_ty);
  Printf.printf "%s\n" (infer_type [] proof |> string_of_ty);
  (* check_type [] tm6 (TArr (TVar"B", TVar"B")); *)
  (* check_type [] tm7 (TVar "A"); *)
  Printf.printf "%s\n" (string_of_ctx [("x", TPair(TVar "A", TVar "B")); ("y", TVar "A"); ("z", TCoprod(TVar "A", TVar "B"))]);
  Printf.printf "%s\n" (string_of_seq ([("x", TArr(TVar "A", TVar "B")); ("y", TVar "A")], TVar "B"))

let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
      Printf.printf
        "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

let () =
let l = [
  "t u v";
  "fun (x : A) -> t";
  "λ (x : A) → t";
  "(t , u)";
  "fst(t)";
  "snd(t)";
  "()";
  "case t of u | v";
  "left(t,B)";
  "right(A,t)";
  "absurd(t,A)"
]
in
List.iter
  (fun s ->
      Printf.printf
        "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
  ) l *)
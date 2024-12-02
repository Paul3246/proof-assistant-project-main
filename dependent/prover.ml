open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

(** Context. *)
type context = (var * (expr * expr option)) list

(** Exception. *)
exception Type_error of string

(* Fill me in! *)

let rec to_string = function
  | Type -> "Set"
  | Var x -> x
  | App (t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(%s %s)" s1 s2
  | Abs (x, t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(λ (%s : %s) → %s)" x s1 s2
  | Pi (x, t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(Π (%s : %s) → %s)" x s1 s2
  | Nat -> "ℕ"
  | Z -> "0"
  | S tm -> string_of_suc tm
  | Ind (t1, t2, t3, t4) ->
    let s1, s2, s3, s4 =
      (to_string t1, to_string t2, to_string t3, to_string t4)
    in
    Format.sprintf "(Ind %s %s %s %s)" s1 s2 s3 s4
  | Eq (t1, t2) ->
    let s1, s2 = (to_string t1, to_string t2) in
    Format.sprintf "(%s = %s)" s1 s2
  | Refl tm -> Format.sprintf "(Refl %s)" @@ to_string tm
  | J (t1, t2, t3, t4, t5) ->
    let s1, s2, s3, s4, s5 =
      (to_string t1, to_string t2, to_string t3, to_string t4, to_string t5)
    in
    Format.sprintf "(J %s %s %s %s %s)" s1 s2 s3 s4 s5

(** Provides a number of a term of form S S S S S Z *)
and string_of_suc t =
  let rec loop t n =
    match t with
    | Z -> Some n
    | S t -> loop t (n + 1)
    | _ -> None
  in
  match loop t 1 with
  | None -> Format.sprintf "(Suc %s)" @@ to_string t
  | Some n -> string_of_int n

let rec has_fv x lambda =
  match lambda with
  | Type -> false
  | Var y -> x = y
  | App (e1, e2) -> has_fv x e1 || has_fv x e2
  | Abs (y, t, e) -> if x = y then false else has_fv x t || has_fv x e
  | Pi (y, t, e) -> if x = y then false else has_fv x t || has_fv x e
  | Nat -> false
  | Z -> false
  | S e -> has_fv x e
  | Ind (n, z, s, e) -> has_fv x n || has_fv x z || has_fv x s || has_fv x e
  | Eq (e1, e2) -> has_fv x e1 || has_fv x e2
  | Refl e -> has_fv x e
  | J (a, m, d, e1, e2) -> has_fv x a || has_fv x m || has_fv x d || has_fv x e1 || has_fv x e2


let fresh_var =
  let r = ref 0 in
  fun () ->
    let v = Printf.sprintf "x%d" !r in
    r := !r + 1;
    v

let rec subst x t u =
  match u with
  | Type -> Type
  | Var y -> if x = y then t else Var y
  | App (u1, u2) -> App (subst x t u1, subst x t u2)
  | Abs (y, t', u') ->
    if has_fv y t then
      let y' = fresh_var () in
      let new_t' = subst y (Var y') t' in
      let new_u' = subst y (Var y') u' in
      Abs (y', subst x t new_t', subst x t new_u')
    else if x = y then
      Abs (y, t', u')
    else
      Abs (y, subst x t t', subst x t u')
  | Pi (y, t', u') ->
    if has_fv y t then
      let y' = fresh_var () in
      let new_t' = subst y (Var y') t' in
      let new_u' = subst y (Var y') u' in
      Pi (y', subst x t new_t', subst x t new_u')
    else if x = y then
      Pi (y, t', u')
    else
      Pi (y, subst x t t', subst x t u')
  | Nat -> Nat
  | Z -> Z
  | S e -> S (subst x t e)
  | Ind (n, z, s, e) -> Ind (subst x t n, subst x t z, subst x t s, subst x t e)
  | Eq (e1, e2) -> Eq (subst x t e1, subst x t e2)
  | Refl e -> Refl (subst x t e)
  | J (a, m, d, e1, e2) -> J (subst x t a, subst x t m, subst x t d, subst x t e1, subst x t e2)

let string_of_context ctx =
  let rec string_context' ctx =
    match ctx with
    | [] -> ""
    | (x, (t, None)) :: [] -> Printf.sprintf "%s : %s" x (to_string t)
    | (x, (t, Some e)) :: [] -> Printf.sprintf "%s : %s = %s" x (to_string t) (to_string e)
    | (x, (t, None)) :: ctx' -> Printf.sprintf "%s : %s, %s" x (to_string t) (string_context' ctx')
    | (x, (t, Some e)) :: ctx' -> Printf.sprintf "%s : %s = %s, %s" x (to_string t) (to_string e) (string_context' ctx')
  in string_context' ctx

let get_value ctx x =
  let rec get_value' ctx x =
    match ctx with
    | [] -> None
    | (y, (_, None)) :: ctx' -> if x = y then None else get_value' ctx' x
    | (y, (_, Some e)) :: ctx' -> if x = y then Some e else get_value' ctx' x
  in get_value' ctx x

let get_type ctx x =
  let rec get_type' ctx x =
    match ctx with
    | [] -> None
    | (y, (t, _)) :: ctx' -> if x = y then Some t else get_type' ctx' x
  in get_type' ctx x

let normalize ctx e =
  let rec normalize' ctx e =
    match e with
    | Type -> Type
    | Var x -> (match get_value ctx x with
        | None -> Var x
        | Some e' -> normalize' ctx e')
    | App (e1, e2) -> (match normalize' ctx e1 with
        | Abs (x, _, e) -> normalize' ctx (subst x (normalize' ctx e2) e)
        | e1' -> App (e1', normalize' ctx e2))
    | Abs (x, t, e) -> Abs (x, normalize' ctx t, normalize' ctx e)
    | Pi (x, t, e) -> Pi (x, normalize' ctx t, normalize' ctx e)
    | Nat -> Nat
    | Z -> Z
    | S e -> S (normalize' ctx e)
    | Ind (p, z, s, n) ->
        let p' = normalize' ctx p in
        let z' = normalize' ctx z in
        let s' = normalize' ctx s in
        let n' = normalize' ctx n in
        (match n' with
        | Z -> normalize' ctx z'
        | S ent -> normalize' ctx (App(App(s', ent), Ind(p', z', s', ent)))
        | _ -> Ind(p', z', s', n'))
    | Eq (e1, e2) -> Eq (normalize' ctx e1, normalize' ctx e2)
    | Refl e -> Refl (normalize' ctx e)
    | J (p, r, x, y, e) ->
      let p' = normalize' ctx p in
      let r' = normalize' ctx r in
      let x' = normalize' ctx x in
      let y' = normalize' ctx y in
      let e' = normalize' ctx e in
      (match e' with
      | Refl e when x' = y' && y' = e -> normalize' ctx (App (r', e))
      | _ -> J (p', r', x', y', e'))
  in normalize' ctx e

let alpha e1 e2 =
  let rec alpha' e1 e2 =
    match e1, e2 with
    | Type, Type -> true
    | Var x, Var y -> x = y
    | App (e1, e2), App (e1', e2') -> alpha' e1 e1' && alpha' e2 e2'
    | Abs (x, t, e), Abs (x', t', e') ->
      let y = fresh_var () in
      alpha' (subst x (Var y) e) (subst x' (Var y) e') && alpha' (subst x (Var y) t) (subst x' (Var y) t')
    | Pi (x, t, e), Pi (x', t', e') ->
      let y = fresh_var () in
      alpha' (subst x (Var y) e) (subst x' (Var y) e') && alpha' (subst x (Var y) t) (subst x' (Var y) t')
    | Nat, Nat -> true
    | Z, Z -> true
    | S e, S e' -> alpha' e e'
    | Ind (n, z, s, e), Ind (n', z', s', e') -> alpha' n n' && alpha' z z' && alpha' s s' && alpha' e e'
    | Eq (e1, e2), Eq (e1', e2') -> alpha' e1 e1' && alpha' e2 e2'
    | Refl e, Refl e' -> alpha' e e'
    | J (a, m, d, e1, e2), J (a', m', d', e1', e2') -> alpha' a a' && alpha' m m' && alpha' d d' && alpha' e1 e1' && alpha' e2 e2'
    | _ -> false
  in alpha' e1 e2

let conv ctx e1 e2 =
  alpha (normalize ctx e1) (normalize ctx e2)

let rec infer ctx e =
  match e with
  | Type -> Type
  | Var x -> (match get_type ctx x with
      | Some t -> t
      | None -> raise (Type_error (Printf.sprintf "Variable %s not found" x)))
  | App (e1, e2) ->
  (match infer ctx e1 with
    | Pi (x, t, e) ->
      let inferred_t = infer ctx e2 in
      if conv ctx inferred_t t then
        (* check ctx e2 t; *)
        subst x e2 e
      else
        let err = Printf.sprintf "Expected type %s but got type %s" (to_string t) (to_string inferred_t) in
        raise (Type_error err)
    | _ -> raise (Type_error "Expected a function type"))
  | Abs (x, t, e) ->
    (* let t' = infer ctx t in *)
    check ctx t Type;
    let ctx' = (x, (t, None)) :: ctx in
    let e' = infer ctx' e in
    Pi (x, t, e')
  | Pi (x, t, e) ->
    check ctx t Type;
    let ctx' = (x, (t, None)) :: ctx in
    check ctx' e Type;
    Type
  | Nat -> Type
  | Z -> Nat
  | S e ->
    check ctx e Nat;
    Nat
  | Ind (p, z, s, n) ->
    let inferred_p = infer ctx p in
    let inferred_z = infer ctx z in
    let inferred_s = infer ctx s in
    let inferred_n = infer ctx n in
    if not (conv ctx inferred_p (Pi ("", Nat, Type))) then
      raise (Type_error "Expected a predicate")
    else if not (conv ctx inferred_z (App (p, Z))) then
      raise (Type_error "Expected a proof of P(0)")
    else if not (conv ctx inferred_s (Pi ("n", Nat, Pi ("", App (p, Var "n"), App (p, S (Var "n")))))) then
      raise (Type_error "Expected a proof of P(n) -> P(S(n))")
    else if not (conv ctx inferred_n Nat) then
      raise (Type_error "Expected a natural number")
    else
      App (p, n)
  | Eq (e1, e2) ->
    let t1 = infer ctx e1 in
    let t2 = infer ctx e2 in
    if conv ctx t1 t2 then
      Type
    else
      let err = Printf.sprintf "Types %s and %s are not convertible" (to_string t1) (to_string t2) in
      raise (Type_error err)
  | Refl e ->
    let _ = infer ctx e in
    Eq(e, e)
  | J (p, r, x, y, e) ->
    let inferred_p = infer ctx p in
    let inferred_r = infer ctx r in
    let inferred_x = infer ctx x in
    let inferred_y = infer ctx y in
    let inferred_e = infer ctx e in
    (match inferred_p with
      |Pi(x', type_A, Pi(y', type_A', Pi(_, Eq(x'',y''), Type)))->
        if not (conv ctx type_A type_A') then
          raise (Type_error "in J, x and y must have the same type")
        else if not (conv ctx (Var x') x'') then
          raise (Type_error "in J, x and x' must be convertible")
        else if not (conv ctx (Var y') y'') then
          raise (Type_error "in J, y and y' must be convertible")
        else
          (match inferred_r with
            | Pi (_x', _type_a, Type)->
              (* if not (conv ctx type_a type_A) then
                raise (Type_error "in J, x must have the same type as x in Pi")
              else if not (conv ctx (Var x') x'') then
                raise (Type_error "in J, x must be convertible to x' in Pi")
              else if not (conv ctx x'' x''') then
                raise (Type_error "in J, x' must be convertible to x'' in Pi")
              else if not (conv ctx x''' x'''') then
                raise (Type_error "in J, x'' must be convertible to x''' in Pi")
              else if not (conv ctx p' p) then
                raise (Type_error "in J, p' must be convertible to p in Pi")
              else *)
                (
                  match inferred_x with
                  | typ_a ->
                    if not (conv ctx typ_a type_A) then
                      raise (Type_error "in J, x must have the same type as x in Pi")
                    else
                      (
                        match inferred_y with
                        | typ_b ->
                          if not (conv ctx typ_b type_A) then
                            raise (Type_error "in J, y must have the same type as x in Pi")
                          else
                            (
                              match inferred_e with
                              | Eq(a, b) ->
                                if not (conv ctx a x) then
                                  raise (Type_error "in J, a must be convertible to x")
                                else if not (conv ctx b y) then
                                  raise (Type_error "in J, b must be convertible to y")
                                else
                                  App(App(App(p, x), y), e)
                              |_ -> raise (Type_error "e must be of type Eq(a, b)")
                            )
                      )
                )
            |_ -> raise (Type_error "r must be of type Pi(x, A, App(App(App(p, x), x), Refl x))")
          )
        | _ -> raise (Type_error "p must be of type Pi(x, A, Pi(y, A, Pi(_, Eq(x, y), Type)))")
    )
and check ctx e t =
  let inferred_type = infer ctx e in
  if conv ctx inferred_type t then ()
  else
    let err = Printf.sprintf "Expected type %s but got type %s in check" (to_string t) (to_string inferred_type) in
    raise (Type_error err)

let () =
let env = ref [] in
let loop = ref true in
let file = open_out "interactive.proof" in
let split c s =
  try
    let n = String.index s c in
    String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
  with Not_found -> s, ""
in
while !loop do
  try
    print_string "? ";
    flush_all ();
    let cmd, arg =
      let cmd = input_line stdin in
      output_string file (cmd^"\n");
      print_endline cmd;
      split ' ' cmd
    in
    match cmd with
    | "assume" ->
      let x, sa = split ':' arg in
      let a = of_string sa in
      check !env a Type;
      env := (x,(a,None)) :: !env;
      print_endline (x^" assumed of type "^to_string a)
    | "define" ->
      let x, st = split '=' arg in
      let t = of_string st in
      let a = infer !env t in
      env := (x,(a,Some t)) :: !env;
      print_endline (x^" defined to "^to_string t^" of type "^to_string a)
    | "context" ->
      print_endline (string_of_context !env)
    | "type" ->
      let t = of_string arg in
      let a = infer !env t in
      print_endline (to_string t^" is of type "^to_string a)
    | "check" ->
      let t, a = split '=' arg in
      let t = of_string t in
      let a = of_string a in
      check !env t a;
      print_endline "Ok."
    | "eval" ->
      let t = of_string arg in
      let _ = infer !env t in
      print_endline (to_string (normalize !env t))
    | "exit" -> loop := false
    | "" | "#" -> ()
    | cmd -> print_endline ("Unknown command: "^cmd)
  with
  | End_of_file -> loop := false
  | Failure err -> print_endline ("Error: "^err^".")
  | Type_error err -> print_endline ("Typing error :"^err^".")
  | Parsing.Parse_error -> print_endline ("Parsing error.")
done;
print_endline "Bye."
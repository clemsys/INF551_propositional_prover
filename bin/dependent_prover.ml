type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string = function
  | Type -> "Type"
  | Var v -> v
  | App (f, x) -> "(" ^ to_string f ^ " " ^ to_string x ^ ")"
  | Abs (x, t, y) ->
      "(fun (" ^ x ^ " : " ^ to_string t ^ ") -> " ^ to_string y ^ ")"
  | Pi (x, a, b) -> "((" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string b ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S n -> "(S " ^ to_string n ^ ")"
  | Ind (p, z, s, n) ->
      "Ind" ^ to_string p ^ " " ^ to_string z ^ " " ^ to_string s ^ " "
      ^ to_string n ^ ")"
  | Eq (t, u) -> "(Eq " ^ to_string t ^ " " ^ to_string u ^ ")"
  | Refl t -> "(Refl " ^ to_string t ^ ")"
  | J (p, r, x, y, e) ->
      "(J " ^ to_string p ^ " " ^ to_string r ^ " " ^ to_string x ^ " "
      ^ to_string y ^ " " ^ to_string e ^ ")"

let fresh_var_counter = ref 0

let fresh_var () =
  fresh_var_counter := !fresh_var_counter + 1;
  "x" ^ string_of_int !fresh_var_counter

(* check whether v appears as a free variable in expression e *)
let rec has_fv x = function
  | Type -> false
  | Var y when y = x -> true
  | Var _ -> false
  | App (f, g) -> has_fv x f || has_fv x g
  | Abs (y, a, _) when y = x ->
      has_fv x a (* or false? would be odd if a contained x = y *)
  | Abs (_, a, t) -> has_fv x a || has_fv x t
  | Pi (y, a, _) when y = x ->
      has_fv x a (* or false? would be odd as well if a contained x = y *)
  | Pi (_, a, b) -> has_fv x a || has_fv x b
  | Nat -> false
  | Z -> false
  | S n -> has_fv x n
  | Ind (p, z, s, n) -> has_fv x p || has_fv x z || has_fv x s || has_fv x n
  | Eq (t, u) -> has_fv x t || has_fv x u
  | Refl t -> has_fv x t
  | J (p, r, z, y, e) ->
      has_fv x p || has_fv x r || has_fv x z || has_fv x y || has_fv x e

(* substitute x by u in e *)
let rec subst x u = function
  | Type -> Type
  | Var y when y = x -> u
  | Var y -> Var y
  | App (t, t') -> App (subst x u t, subst x u t')
  | Abs (y, a, t) when y = x || has_fv y u ->
      let z = fresh_var () in
      Abs (z, subst x u (subst y (Var z) a), subst x u (subst y (Var z) t))
  | Abs (y, a, t) -> Abs (y, subst x u a, subst x u t)
  | Pi (y, a, b) when y = x || has_fv y u ->
      let z = fresh_var () in
      Pi (z, subst x u (subst y (Var z) a), subst x u (subst y (Var z) b))
  | Pi (y, a, b) -> Pi (y, subst x u a, subst x u b)
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x u n)
  | Ind (p, i, h, n) -> Ind (subst x u p, subst x u i, subst x u h, subst x u n)
  | Eq (t, s) -> Eq (subst x u t, subst x u s)
  | Refl t -> Refl (subst x u t)
  | J (p, r, z, y, e) ->
      J (subst x u p, subst x u r, subst x u z, subst x u y, subst x u e)

type context = (var * (expr * expr option)) list

let rec string_of_context = function
  | [] -> ""
  | (x, (a, t)) :: q -> (
      (match q with [] -> "" | _ -> string_of_context q ^ "\n")
      ^ x ^ " : " ^ to_string a
      ^ match t with Some t -> " = " ^ to_string t | _ -> "")

(* we assume here that expressions are well typed, this function may perform multiple reductions at once *)
let rec red env = function
  | Type -> None
  | Var v -> ( try snd (List.assoc v env) with Not_found -> None)
  | App (Abs (x, _, y), u) -> Some (subst x u y)
  | App (r, s) -> (
      let rr = red env r and rs = red env s in
      match (rr, rs) with
      | None, None -> None
      | _, _ ->
          let r = match rr with Some r -> r | _ -> r
          and s = match rs with Some s -> s | _ -> s in
          Some (App (r, s)))
  | Abs (x, t, y) -> (
      let rt = red env t and ry = red ((x, (t, None)) :: env) y in
      match (rt, ry) with
      | None, None -> None
      | _, _ ->
          let t = match rt with Some t -> t | _ -> t
          and y = match ry with Some y -> y | _ -> y in
          Some (Abs (x, t, y)))
  | Pi (x, t, s) -> (
      let rt = red env t and rs = red ((x, (t, None)) :: env) s in
      match (rt, rs) with
      | None, None -> None
      | _, _ ->
          let t = match rt with Some t -> t | _ -> t
          and s = match rs with Some s -> s | _ -> s in
          Some (Pi (x, t, s)))
  | Nat -> None
  | Z -> None
  | S n -> (
      let r = red env n in
      match r with Some r -> Some (S r) | None -> None)
  | Ind (p, z, s, n) -> (
      let rp = red env p
      and rz = red env z
      and rs = red env s
      and rn = red env n in
      match (rp, rz, rs, rn) with
      | None, None, None, None -> (
          match n with
          | Z -> Some z
          | S n -> Some (App (App (s, n), Ind (p, z, s, n)))
          | _ -> None)
      | _, _, _, _ ->
          let p = match rp with Some p -> p | _ -> p
          and z = match rz with Some z -> z | _ -> z
          and s = match rs with Some s -> s | _ -> s
          and n = match rn with Some n -> n | _ -> n in
          Some (Ind (p, z, s, n)))
  | Eq (t, u) -> (
      let rt = red env t and ru = red env u in
      match (rt, ru) with
      | None, None -> None
      | _, _ ->
          let t = match rt with Some t -> t | _ -> t
          and u = match ru with Some u -> u | _ -> u in
          Some (Eq (t, u)))
  | Refl t -> (
      let t = red env t in
      match t with Some t -> Some (Refl t) | None -> None)
  | J (_, r, x, y, Refl z) when x = y && x = z -> Some (App (r, x))
  | J (p, r, x, y, e) -> (
      let rp = red env p
      and rr = red env r
      and rx = red env x
      and ry = red env y
      and re = red env e in
      match (rp, rr, rx, ry, re) with
      | None, None, None, None, None -> None
      | _, _, _, _, _ ->
          let p = match rp with Some p -> p | _ -> p
          and r = match rr with Some r -> r | _ -> r
          and x = match rx with Some x -> x | _ -> x
          and y = match ry with Some y -> y | _ -> y
          and e = match re with Some e -> e | _ -> e in
          red env (J (p, r, x, y, e)))

let rec normalize env t =
  match red env t with None -> t | Some s -> normalize env s

let rec alpha e f =
  match (e, f) with
  | Type, Type -> true
  | Var v, Var w -> v = w
  | App (f, g), App (f', g') -> alpha f f' && alpha g g'
  | Abs (x, a, t), Abs (x', a', t') when x = x' -> alpha a a' && alpha t t'
  | Abs (x, a, t), Abs (x', a', t') ->
      let y = fresh_var () in
      alpha
        (Abs (y, subst x (Var y) a, subst x (Var y) t))
        (Abs (y, subst x' (Var y) a', subst x' (Var y) t'))
  | Pi (x, a, b), Pi (x', a', b') when x = x' -> alpha a a' && alpha b b'
  | Pi (x, a, b), Pi (x', a', b') ->
      let y = fresh_var () in
      alpha
        (Pi (y, subst x (Var y) a, subst x (Var y) b))
        (Pi (y, subst x' (Var y) a', subst x' (Var y) b'))
  | Nat, Nat -> true
  | Z, Z -> true
  | S n, S m -> alpha n m
  | Ind (p, z, s, n), Ind (p', z', s', n') ->
      alpha p p' && alpha z z' && alpha s s' && alpha n n'
  | Eq (t, u), Eq (t', u') -> alpha t t' && alpha u u'
  | Refl t, Refl t' -> alpha t t'
  | J (p, r, x, y, g), J (p', r', x', y', g') ->
      alpha p p' && alpha r r' && alpha x x' && alpha y y' && alpha g g'
  | _, _ -> false

let conv env e f =
  let ne = normalize env e and nf = normalize env f in
  alpha ne nf

exception Type_error
exception Unbound_variable of var

let rec infer env = function
  | Type -> Type
  | Var x -> (
      try fst (List.assoc x env) with Not_found -> raise (Unbound_variable x))
  | App (t, u) -> (
      match infer env t with
      | Pi (x, a, b) ->
          let type_u = infer env u in
          if conv env a type_u then subst x u b else raise Type_error
      | _ -> raise Type_error)
  | Abs (x, a, t) ->
      let b = infer ((x, (a, None)) :: env) t in
      Pi (x, a, b)
  | Pi (_, _, _) -> Type
  | Nat -> Type
  | Z -> Nat
  | S n -> if conv env (infer env n) Nat then Nat else raise Type_error
  | Ind (p, z, s, n) ->
      let type_i = infer env z and type_n = infer env n in
      if conv env type_i (App (p, Z)) && conv env type_n Nat then
        match normalize env (infer env s) with
        | Pi (m, Nat, Pi (_, q, r)) ->
            let new_env = (m, (Nat, None)) :: env in
            if
              conv new_env (App (p, Var m)) q
              && conv new_env (App (p, S (Var m))) r
            then normalize env (App (p, n))
            else raise Type_error
        | _ -> raise Type_error
      else raise Type_error
  | Eq (t, u) ->
      if conv env (infer env t) (infer env u) then Type else raise Type_error
  | Refl t ->
      let _ = infer env t in
      Type
  | J (p, r, x, y, e) -> (
      match normalize env (infer env p) with
      | Pi (z, a, Pi (z', b, Pi (_, q, Type))) ->
          if
            conv env a b
            && conv
                 ((z, (a, None)) :: (z', (a, None)) :: env)
                 (Eq (Var z, Var z'))
                 q
            && conv env (infer env x) a
            && conv env (infer env y) b
            && conv env (infer env e) (Eq (x, y))
            && conv env (infer env r)
                 (Pi (z, a, App (App (App (p, Var z), Var z), Eq (Var z, Var z))))
          then Type
          else raise Type_error
      | _ -> raise Type_error)

let check env t a = if conv env (infer env t) a then () else raise Type_error

(***********************************)
(* Code copied from interaction.ml *)
(***********************************)

(** Parsing of expressions. *)
let () = Printexc.record_backtrace true

exception Parse_error

let lexer =
  Genlex.make_lexer
    [
      "(";
      ",";
      ")";
      "->";
      "=>";
      "fun";
      "Pi";
      ":";
      "Type";
      "Nat";
      "Z";
      "S";
      "Ind";
      "Eq";
      "Refl";
      "J";
    ]

let of_tk s =
  let must_kwd s k =
    match Stream.next s with
    | Genlex.Kwd k' when k' = k -> ()
    | _ -> raise Parse_error
  in
  let peek_kwd s k =
    match Stream.peek s with
    | Some (Genlex.Kwd k') when k' = k ->
        let _ = Stream.next s in
        true
    | _ -> false
  in
  let stream_is_empty s =
    try
      Stream.empty s;
      true
    with Stream.Failure -> false
  in
  let ident s =
    match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
  in
  let noapp =
    List.map
      (fun k -> Some (Genlex.Kwd k))
      [ ")"; "->"; "=>"; "fun"; "Pi"; ":"; "Type" ]
  in
  let rec e () = abs ()
  and abs () =
    if peek_kwd s "Pi" then (
      must_kwd s "(";
      let x = ident s in
      must_kwd s ":";
      let a = e () in
      must_kwd s ")";
      must_kwd s "->";
      let b = e () in
      Pi (x, a, b))
    else if peek_kwd s "fun" then (
      must_kwd s "(";
      let x = ident s in
      must_kwd s ":";
      let a = e () in
      must_kwd s ")";
      must_kwd s "->";
      let t = e () in
      Abs (x, a, t))
    else app ()
  and app () =
    let t = ref (arr ()) in
    while (not (stream_is_empty s)) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, base ())
    done;
    !t
  and arr () =
    let t = base () in
    if peek_kwd s "=>" then
      let u = e () in
      Pi ("_", t, u)
    else t
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "Type" -> Type
    | Genlex.Kwd "Nat" -> Nat
    | Genlex.Kwd "Z" -> Z
    | Genlex.Kwd "S" ->
        let t = base () in
        S t
    | Genlex.Kwd "Ind" ->
        let p = base () in
        let z = base () in
        let ps = base () in
        let n = base () in
        Ind (p, z, ps, n)
    | Genlex.Kwd "Eq" ->
        let t = base () in
        let u = base () in
        Eq (t, u)
    | Genlex.Kwd "Refl" ->
        let t = base () in
        Refl t
    | Genlex.Kwd "J" ->
        let p = base () in
        let r = base () in
        let x = base () in
        let y = base () in
        let e = base () in
        J (p, r, x, y, e)
    | Genlex.Kwd "(" ->
        let t = e () in
        must_kwd s ")";
        t
    | _ -> raise Parse_error
  in
  e ()

let of_string a = of_tk (lexer (Stream.of_string a))

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      ( String.trim (String.sub s 0 n),
        String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
    with Not_found -> (s, "")
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd ^ "\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
          let x, sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x, (a, None)) :: !env;
          print_endline (x ^ " assumed of type " ^ to_string a)
      | "define" ->
          let x, st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x, (a, Some t)) :: !env;
          print_endline
            (x ^ " defined to " ^ to_string t ^ " of type " ^ to_string a)
      | "context" -> print_endline (string_of_context !env)
      | "type" ->
          let t = of_string arg in
          let a = infer !env t in
          print_endline (to_string t ^ " is of type " ^ to_string a)
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
      | cmd -> print_endline ("Unknown command: " ^ cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: " ^ err ^ ".")
  done;
  print_endline "Bye."

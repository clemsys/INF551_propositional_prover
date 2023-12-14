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
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

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
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

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
  | Pi (y, a, b) -> Pi (y, subst x u a, subst y u b)
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

type context = (var * (expr * expr option)) list

let rec string_of_context = function
  | [] -> ""
  | (x, (a, t)) :: q -> (
      (match q with [] -> "" | _ -> string_of_context q ^ "\n")
      ^ x ^ " : " ^ to_string a
      ^ match t with Some t -> " = " ^ to_string t | _ -> "")

(* we assume here that expressions are well typed *)
let rec red env = function
  | Type -> None
  | Var v -> snd (List.assoc v env)
  | App (Abs (x, _, y), u) -> Some (subst x u y)
  | App (r, s) -> (
      let rr = red env r and ss = red env s in
      match (rr, ss) with
      | None, None -> None
      | None, Some s -> Some (App (r, s))
      | Some r, _ -> Some (App (r, s)))
  | Abs (x, t, y) -> (
      let rt = red env t and ry = red ((x, (t, None)) :: env) y in
      match (rt, ry) with
      | None, None -> None
      | None, Some ry -> Some (Abs (x, t, ry))
      | Some rt, _ -> Some (Abs (x, rt, y)))
  | Pi (x, t, s) -> (
      let rt = red env t and rs = red ((x, (Type, Some t)) :: env) s in
      match (rt, rs) with
      | None, None -> None
      | None, Some rs -> Some (Pi (x, t, rs))
      | Some rt, _ -> Some (Pi (x, rt, s)))
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

let rec normalize env t =
  match red env t with None -> t | Some s -> normalize env s

let rec alpha env e f =
  match (e, f) with
  | Type, Type -> true
  | Var v, Var w -> v = w
  | App (f, g), App (f', g') -> alpha env f f' && alpha env g g'
  | Abs (x, a, t), Abs (x', a', t') when x = x' ->
      alpha env a a' && alpha env t t'
  | Abs (x, a, t), Abs (x', a', t') ->
      let y = fresh_var () in
      alpha env
        (Abs (y, subst x (Var y) a, subst x (Var y) t))
        (Abs (y, subst x' (Var y) a', subst x' (Var y) t'))
  | Pi (x, a, b), Pi (x', a', b') when x = x' ->
      alpha env a a' && alpha env b b'
  | Pi (x, a, b), Pi (x', a', b') ->
      let y = fresh_var () in
      alpha env
        (Pi (y, subst x (Var y) a, subst x (Var y) b))
        (Pi (y, subst x' (Var y) a', subst x' (Var y) b'))
  | _, _ -> false

let conv env e f =
  let ne = normalize env e and nf = normalize env f in
  alpha env ne nf

exception Type_error
exception Unbound_variable of var

let rec infer env = function
  | Type -> Type
  | Var x -> (
      try fst (List.assoc x env) with Not_found -> raise (Unbound_variable x))
  | App (t, u) -> (
      match infer env t with
      | Pi (x, a, b) ->
          if infer env u <> a then raise Type_error else subst x u b
      | _ -> raise Type_error)
  | Abs (x, a, t) ->
      let b = infer ((x, (a, None)) :: env) t in
      Pi (x, a, b)
  | Pi (_, _, _) -> Type
  | Nat -> assert false
  | Z -> assert false
  | S _ -> assert false
  | Ind (_, _, _, _) -> assert false
  | Eq (_, _) -> assert false
  | Refl _ -> assert false
  | J (_, _, _, _, _) -> assert false

let check env t a = if infer env t <> a then raise Type_error else ()

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
    (* | e -> print_endline ("Error: "^Printexc.to_string e) *)
  done;
  print_endline "Bye."

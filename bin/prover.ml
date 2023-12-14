(* PART 1 *)

type tvar = string
(** Type variables. *)

type var = string
(** Term variables. *)

(** simple type *)
type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | True
  | Or of ty * ty
  | False
  | Nat

(** lambda-terms a la Church *)
type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Unit
  | Left of tm * ty
  | Right of ty * tm
  | Case of tm * var * tm * var * tm
  | Absurd of tm * ty
  | Zero
  | Suc of tm
  | Rec of tm * tm * tm

(* Question 1.3 *)
let rec string_of_ty = function
  | TVar v -> v
  | Imp (s, u) -> "(" ^ string_of_ty s ^ " => " ^ string_of_ty u ^ ")"
  | And (s, u) -> "(" ^ string_of_ty s ^ " /\\ " ^ string_of_ty u ^ ")"
  | True -> "T"
  | Or (s, u) -> "(" ^ string_of_ty s ^ " \\/ " ^ string_of_ty u ^ ")"
  | False -> "_"
  | Nat -> "Nat"

let () =
  let a = TVar "A" in
  let b = TVar "B" in
  let c = TVar "C" in
  let t = Imp (Imp (a, b), Imp (a, c)) in
  assert (string_of_ty t = "((A => B) => (A => C))")

let rec string_of_tm = function
  | Var v -> v
  | App (s, u) -> "(" ^ string_of_tm s ^ " " ^ string_of_tm u ^ ")"
  | Abs (v, vt, s) ->
      "(fun (" ^ v ^ " : " ^ string_of_ty vt ^ ") -> " ^ string_of_tm s ^ ")"
  | Pair (s, u) -> "(" ^ string_of_tm s ^ " , " ^ string_of_tm u ^ ")"
  | Fst s -> "fst(" ^ string_of_tm s ^ ")"
  | Snd s -> "snd(" ^ string_of_tm s ^ ")"
  | Unit -> "()"
  | Left (s, t) -> "left(" ^ string_of_ty t ^ "," ^ string_of_tm s ^ ")"
  | Right (t, s) -> "right(" ^ string_of_ty t ^ "," ^ string_of_tm s ^ ")"
  | Case (s, x, u, y, v) ->
      "(case " ^ string_of_tm s ^ " of " ^ x ^ " -> " ^ string_of_tm u ^ " | "
      ^ y ^ " -> " ^ string_of_tm v ^ ")"
  | Absurd (s, t) -> "absurd(" ^ string_of_tm s ^ "," ^ string_of_ty t ^ ")"
  | Zero -> "Zero"
  | Suc n -> "suc(" ^ string_of_tm n ^ ")"
  | Rec (t, u, f) ->
      "rec(" ^ string_of_tm t ^ "," ^ string_of_tm u ^ "," ^ string_of_tm f
      ^ ")"

let () =
  let a = TVar "A" in
  let b = TVar "B" in
  let ftype = Imp (a, b) in
  let t = Abs ("f", ftype, Abs ("x", a, App (Var "f", Var "x"))) in
  assert (string_of_tm t = "(fun (f : (A => B)) -> (fun (x : A) -> (f x)))")

type context = (string * ty) list

exception Type_error

(* Questions 1.4 and 1.5 *)
let rec infer_type env = function
  | Var x -> ( try List.assoc x env with Not_found -> raise Type_error)
  | Abs (x, a, t) -> Imp (a, infer_type ((x, a) :: env) t)
  | App (t, u) -> (
      match infer_type env t with
      | Imp (a, b) ->
          if infer_type env u <> a then raise Type_error;
          b
      | _ -> raise Type_error)
  | Pair (s, u) -> And (infer_type env s, infer_type env u)
  | Fst t -> (
      match infer_type env t with And (s, _) -> s | _ -> raise Type_error)
  | Snd t -> (
      match infer_type env t with And (_, u) -> u | _ -> raise Type_error)
  | Unit -> True
  | Left (s, t) -> Or (infer_type env s, t)
  | Right (t, s) -> Or (t, infer_type env s)
  | Case (s, x, u, y, v) -> (
      match infer_type env s with
      | Or (a, b) ->
          let u_type = infer_type ((x, a) :: env) u
          and v_type = infer_type ((y, b) :: env) v in
          if u_type <> v_type then raise Type_error;
          u_type
      | _ -> raise Type_error)
  | Absurd (_, t) -> t
  | Zero -> Nat
  | Suc s -> if infer_type env s = Nat then Nat else raise Type_error
  | Rec (t, u, f) -> (
      match f with
      | Abs (y, a, v) ->
          let t_type = infer_type env t and u_type = infer_type env u in
          let v_type = infer_type ((y, a) :: env) v in
          if not (t_type = Nat && u_type = v_type) then raise Type_error
          else v_type
      | _ -> raise Type_error)

and check_type env t t_type =
  if infer_type env t = t_type then () else raise Type_error

(* various tests *)
let () =
  let a = TVar "A" and b = TVar "B" and c = TVar "C" in
  let expected_type = Imp (Imp (a, b), Imp (Imp (b, c), Imp (a, c))) in
  let ftype = Imp (a, b) and gtype = Imp (b, c) in
  let t =
    Abs
      ( "f",
        ftype,
        Abs ("g", gtype, Abs ("x", a, App (Var "g", App (Var "f", Var "x")))) )
  in
  assert (infer_type [] t = expected_type)

let () =
  let t = Abs ("f", TVar "A", Var "x") in
  assert (
    try
      let _ = infer_type [] t in
      false
    with e -> ( match e with Type_error -> true | _ -> false))

let () =
  let t = Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  assert (
    try
      let _ = infer_type [] t in
      false
    with e -> ( match e with Type_error -> true | _ -> false))

let () =
  let ftype = Imp (TVar "A", TVar "B") in
  let t = Abs ("f", ftype, Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  assert (
    try
      let _ = infer_type [] t in
      false
    with e -> ( match e with Type_error -> true | _ -> false))

let () =
  let a = TVar "A" in
  let t = Abs ("x", a, Var "x") in
  let t_type = Imp (a, a) in
  assert (
    check_type [] t t_type;
    true)

let () =
  let b = TVar "B" in
  let t = Abs ("x", TVar "A", Var "x") in
  let t_type = Imp (b, b) in
  assert (
    try
      check_type [] t t_type;
      true
    with e -> ( match e with Type_error -> true | _ -> false))

let () =
  assert (
    try
      check_type [] (Var "x") (TVar "A");
      true
    with e -> ( match e with Type_error -> true | _ -> false))

(* proof of the commutativity of conjonction *)
let () =
  let a = TVar "A" and b = TVar "B" in
  let and_comm = Abs ("x", And (a, b), Pair (Snd (Var "x"), Fst (Var "x"))) in
  (* print_endline (string_of_ty (infer_type [] and_comm));
     print_endline (string_of_tm and_comm); *)
  assert (infer_type [] and_comm = Imp (And (a, b), And (b, a)))

(* proof that (T => A) => A *)
let () =
  let a = TVar "A" in
  let t = Abs ("x", Imp (True, a), App (Var "x", Unit)) in
  (* print_endline (string_of_ty (infer_type [] t));
     print_endline (string_of_tm t); *)
  assert (infer_type [] t = Imp (Imp (True, a), a))

(* proof of the commutativity of disjunction *)
let () =
  let a = TVar "A" and b = TVar "B" in
  let or_comm =
    Abs
      ( "z",
        Or (a, b),
        Case (Var "z", "x", Right (b, Var "x"), "y", Left (Var "y", a)) )
  in
  (* print_endline (string_of_ty (infer_type [] or_comm));
     print_endline (string_of_tm or_comm); *)
  assert (infer_type [] or_comm = Imp (Or (a, b), Or (b, a)))

(* proof that (A /\ (A => _)) => B *)
let () =
  let a = TVar "A" and b = TVar "B" in
  let t =
    Abs
      ( "x",
        And (a, Imp (a, False)),
        Absurd (App (Snd (Var "x"), Fst (Var "x")), b) )
  in
  (* print_endline (string_of_ty (infer_type [] t));
     print_endline (string_of_tm t); *)
  assert (infer_type [] t = Imp (And (a, Imp (a, False)), b))

(**************************************)
(* Parsing code copied from parser.ml *)
(**************************************)

let () = Printexc.record_backtrace true

exception Parse_error

let must_kwd s k =
  match Stream.next s with
  | Genlex.Kwd k' when k' = k -> ()
  | _ -> raise Parse_error

let peek_kwd s k =
  match Stream.peek s with
  | Some (Genlex.Kwd k') when k' = k ->
      let _ = Stream.next s in
      true
  | _ -> false

let stream_is_empty s =
  try
    Stream.empty s;
    true
  with Stream.Failure -> false

let ident s =
  match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error

let lexer =
  Genlex.make_lexer
    [
      "(";
      ")";
      "=>";
      "/\\";
      "\\/";
      "fun";
      "->";
      ",";
      ":";
      "fst";
      "snd";
      "T";
      "left";
      "right";
      "not";
      "case";
      "of";
      "|";
      "absurd";
      "_";
      "Nat";
    ]

let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then Imp (a, arr ()) else a
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then And (a, prod ()) else a
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then Or (a, sum ()) else a
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> TVar x
    | Genlex.Kwd "(" ->
        let a = ty () in
        must_kwd s ")";
        a
    | Genlex.Kwd "T" -> True
    | Genlex.Kwd "_" -> False
    | Genlex.Kwd "not" ->
        let a = base () in
        Imp (a, False)
    | Genlex.Kwd "Nat" -> Nat
    | _ -> raise Parse_error
  in
  ty ()

let tm_of_tk s =
  let noapp =
    List.map
      (fun k -> Some (Genlex.Kwd k))
      [ ")"; ","; "case"; "fun"; "of"; "->"; "|" ]
  in
  let ty () = ty_of_tk s in
  let rec tm () = app ()
  and app () =
    let t = ref (abs ()) in
    while (not (stream_is_empty s)) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
  and abs () =
    if peek_kwd s "fun" then (
      must_kwd s "(";
      let x = ident s in
      must_kwd s ":";
      let a = ty () in
      must_kwd s ")";
      must_kwd s "->";
      let t = tm () in
      Abs (x, a, t))
    else if peek_kwd s "case" then (
      let t = tm () in
      must_kwd s "of";
      let x = ident s in
      must_kwd s "->";
      let u = tm () in
      must_kwd s "|";
      let y = ident s in
      must_kwd s "->";
      let v = tm () in
      Case (t, x, u, y, v))
    else base ()
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "(" ->
        if peek_kwd s ")" then Unit
        else
          let t = tm () in
          if peek_kwd s "," then (
            let u = tm () in
            must_kwd s ")";
            Pair (t, u))
          else (
            must_kwd s ")";
            t)
    | Genlex.Kwd "fst" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ")";
        Fst t
    | Genlex.Kwd "snd" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ")";
        Snd t
    | Genlex.Kwd "left" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ",";
        let b = ty () in
        must_kwd s ")";
        Left (t, b)
    | Genlex.Kwd "right" ->
        must_kwd s "(";
        let a = ty () in
        must_kwd s ",";
        let t = tm () in
        must_kwd s ")";
        Right (a, t)
    | Genlex.Kwd "absurd" ->
        must_kwd s "(";
        let t = tm () in
        must_kwd s ",";
        let a = ty () in
        must_kwd s ")";
        Absurd (t, a)
    | _ -> raise Parse_error
  in
  tm ()

let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))

(* test for the parsing of types *)
let () =
  let l =
    [
      ("A => B", Imp (TVar "A", TVar "B"));
      ("A /\\ B", And (TVar "A", TVar "B"));
      ("T", True);
      ("A \\/ B", Or (TVar "A", TVar "B"));
      ("_", False);
      ("not A", Imp (TVar "A", False));
    ]
  in
  List.iter (fun (s, expected) -> assert (ty_of_string s = expected)) l

(* test for the parsing of terms *)
let () =
  let l =
    [
      ("t u", App (Var "t", Var "u"));
      ("fun (x : A) -> t", Abs ("x", TVar "A", Var "t"));
      ("(t , u)", Pair (Var "t", Var "u"));
      ("fst(t)", Fst (Var "t"));
      ("snd(t)", Snd (Var "t"));
      ("()", Unit);
      ("case t of x -> u | y -> v", Case (Var "t", "x", Var "u", "y", Var "v"));
      ("left(t,B)", Left (Var "t", TVar "B"));
      ("right(A,t)", Right (TVar "A", Var "t"));
      ("absurd(t,A)", Absurd (Var "t", TVar "A"));
    ]
  in
  List.iter (fun (s, expected) -> assert (tm_of_string s = expected)) l

(* string representation of contexts *)
let string_of_ctx c =
  String.concat " , "
    (List.map (function s, t -> s ^ " : " ^ string_of_ty t) c)

(* test *)
let () =
  let a = TVar "A" and b = TVar "B" in
  assert (
    string_of_ctx [ ("x", Imp (a, b)); ("y", And (a, b)); ("Z", True) ]
    = "x : (A => B) , y : (A /\\ B) , Z : T")

type sequent = context * ty

let string_of_seq (c, t) = string_of_ctx c ^ " |- " ^ string_of_ty t

(* test *)
let () =
  let a = TVar "A" and b = TVar "B" in
  assert (
    string_of_seq ([ ("x", Imp (a, b)); ("y", a) ], b)
    = "x : (A => B) , y : A |- B")

(**************************************************)
(* Interactive prover code copied from proving.ml *)
(**************************************************)

let log_filename = if Array.length Sys.argv > 1 then Sys.argv.(1) else "k.proof"
let log_channel = open_out log_filename

(* returns true if and only if env contains the type t *)
let type_in_context t env = List.mem t (List.map (function _, t1 -> t1) env)

let rec prove env a =
  print_endline (string_of_seq (env, a));
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    prove env a
  in
  let cmd, arg =
    let cmd = input_line stdin in
    output_string log_channel (cmd ^ "\n");
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    (c, a)
  in
  match cmd with
  | "intro" -> (
      match a with
      | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro."
          else
            let x = arg in
            let t = prove ((x, a) :: env) b in
            Abs (x, a, t)
      | And (a, b) ->
          let proof_a = prove env a in
          let proof_b = prove env b in
          Pair (proof_a, proof_b)
      | True -> Unit
      | Nat -> (
          match arg with
          | "zero" -> Zero
          | "suc" -> Suc (prove env Nat)
          | _ -> error "wrong argument")
      | _ -> error "Don't know how to introduce this.")
  | "exact" ->
      let t = tm_of_string arg in
      if infer_type env t <> a then error "Not the right type." else t
  | "elim" -> (
      try
        let arg_type = List.assoc arg env in
        match arg_type with
        | Imp (x, y) ->
            if y <> a then
              error (arg ^ " is not of type ... => " ^ string_of_ty a)
            else
              let t = prove env x in
              App (Var arg, t)
        | Or (x, y) ->
            let left_proof = prove ((arg, x) :: env) a in
            let right_proof = prove ((arg, y) :: env) a in
            Case (Var arg, arg, left_proof, arg, right_proof)
        | False -> Absurd (Var arg, a)
        | Nat ->
            print_endline
              ("Initialization: value of function for " ^ arg ^ " = Zero");
            let init_proof = prove env a in
            print_endline ("Heredity: function for suc " ^ arg);
            let hered_proof = prove env (Imp (a, a)) in
            Rec (Var arg, init_proof, hered_proof)
        | _ -> error (arg ^ " is not an implication")
      with _ -> error (arg ^ " is not in context"))
  | "cut" -> (
      try
        let lemma = ty_of_string arg in
        let global_proof = prove env (Imp (lemma, a)) in
        let lemma_proof = prove env lemma in
        App (global_proof, lemma_proof)
      with _ -> error ("could not parse argument " ^ arg))
  | "fst" -> (
      try
        let arg_type = List.assoc arg env in
        match arg_type with
        | And (x, _) ->
            if x <> a then error (arg ^ " is not of type " ^ string_of_ty x)
            else Fst (Var arg)
        | _ -> error (arg ^ " is not a conjuction")
      with _ -> error (arg ^ " is not in context"))
  | "snd" -> (
      try
        let arg_type = List.assoc arg env in
        match arg_type with
        | And (_, x) ->
            if x <> a then error (arg ^ " is not of type " ^ string_of_ty x)
            else Snd (Var arg)
        | _ -> error (arg ^ " is not a conjuction")
      with _ -> error (arg ^ " is not in context"))
  | "left" -> (
      match a with
      | Or (x, y) -> Left (prove env x, y)
      | _ -> error (string_of_ty a ^ " is not a disjunction"))
  | "right" -> (
      match a with
      | Or (x, y) -> Right (x, prove env y)
      | _ -> error (string_of_ty a ^ " is not a disjunction"))
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  output_string log_channel (a ^ "\n");
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string "Typechecking... ";
  flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";
  print_endline ("proof saved in " ^ log_filename)

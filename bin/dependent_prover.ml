type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
(* forget about the constructors below at first *)
(*| Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr *)

let rec to_string = function
  | Type -> "Type"
  | Var v -> v
  | App (f, x) -> "(" ^ to_string f ^ " " ^ to_string x ^ ")"
  | Abs (x, t, y) ->
      "(fun (" ^ x ^ " : " ^ to_string t ^ ") -> " ^ to_string y ^ ")"
  | Pi (x, a, b) -> "Pi(" ^ x ^ "," ^ to_string a ^ "," ^ to_string b ^ ")"

let fresh_var_counter = ref 0

let fresh_var () =
  fresh_var_counter := !fresh_var_counter + 1;
  "x" ^ string_of_int !fresh_var_counter

type var = string

type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
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

type context = (var * (expr * expr option)) list

let rec string_of_context = function
  | [] -> ""
  | (x, a, t) :: q ->
      x ^ " : " ^ to_string a
      ^ (match t with Some t -> " = " ^ to_string t | _ -> "")
      ^ "\n" ^ string_of_context q

let rec value_from_context v = function
  | [] -> None
  | (x, (_, Some t)) :: _ when x = v -> Some t
  | (x, (_, None)) :: _ when x = v -> None
  | (_, (_, _)) :: q -> value_from_context v q

let rec red env = function
  | Type -> None
  | Var v -> value_from_context v env
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

let rec normalize env t =
  match red env t with None -> t | Some s -> normalize env s

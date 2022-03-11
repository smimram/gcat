(** A term. *)
type t =
  | Var of string
  | Id of t
  | Comp of t * t
  | Cons of string * t list (** A constructor. *)

type term = t

let rec to_string = function
  | Var x -> x
  | Id t -> Printf.sprintf "id(%s)" (to_string t)
  | Comp (t, u) -> Printf.sprintf "%s; %s" (to_string t) (to_string u)
  | Cons (c, l) -> Printf.sprintf "%s(%s)" c (List.map to_string l |> String.concat ", ")

(** Equality on terms. *)
let conv (t : t) (u : t) =
  (* Handle axioms of categories. *)
  let rec normalize = function
    | Comp (Id _, u) -> normalize u
    | Comp (t, Id _) -> normalize t
    | Comp (Comp (t, u), v) -> normalize (Comp (t, Comp (u, v)))
    | Cons (c, l) -> Cons (c, List.map normalize l)
    | t -> t
  in
  normalize t = normalize u

(** A substitution. *)
type subst = (string * t) list

(** Apply a substitution. *)
let rec subst (s : subst) = function
  | Var x when List.mem_assoc x s -> List.assoc x s
  | Var _ as t -> t
  | Id t -> Id (subst s t)
  | Comp (t, u) -> Comp (subst s t, subst s u)
  | Cons (c, l) -> Cons (c, List.map (subst s) l)

module Type = struct
  (** A type. *)
  type t =
    | Obj (** An object. *)
    | Hom of term * term (** A morphism. *)
    | Eq of term * term (** An equality between parallel morphisms. *)
    | Cons of string * term list (** A constructor. *)

  let string_of_term = to_string

  let to_string = function
    | Obj -> "*"
    | Hom (a, b) -> Printf.sprintf "%s -> %s" (string_of_term a) (string_of_term b)
    | Eq (a, b) -> Printf.sprintf "%s == %s" (string_of_term a) (string_of_term b)
    | Cons (c, _) -> Printf.sprintf "%s(...)" c

  let subst (s : subst) = function
    | Obj -> Obj
    | Hom (t, u) -> Hom (subst s t, subst s u)
    | Eq (t, u) -> Eq (subst s t, subst s u)
    | Cons (c, l) -> Cons (c, List.map (subst s) l)
end

(** A context. *)
type context = (string * Type.t) list

(** Similar to a context but we can use constructors there. *)
type pattern = (t * Type.t) list

(** Type constructors with given parameters and type to which they can be casted. *)
let type_constructors : (string * (context * Type.t)) list =
  [
    "prod", (["x", Obj; "y", Obj], Obj)
  ]

let type_constructors = ref type_constructors

(** Term constructors. *)
let term_constructors : (string * (context * Type.t)) list =
  [
    "fst", (
      ["x", Obj; "y", Obj; "p", Cons ("prod", [Var "x"; Var "y"])],
      Hom (Var "p", Var "x")
    );
    "snd", (
      ["x", Obj; "y", Obj; "p", Cons ("prod", [Var "x"; Var "y"])],
      Hom (Var "p", Var "y")
    );
    "pairing", (
      ["x", Obj; "y", Obj; "z", Obj;
       "f", Hom (Var "x", Var "y");
       "g", Hom (Var "x", Var "z");
       "p", Cons ("prod", [Var "y"; Var "z"])],
      Hom (Var "x", Var "p")
    );
    "pairing-beta-l", (
      ["x", Obj; "y", Obj; "z", Obj;
       "f", Hom (Var "x", Var "y");
       "g", Hom (Var "x", Var "z");
       "p", Cons ("prod", [Var "y"; Var "z"])],
      Eq (
        Comp (
          Cons ("pairing", [Var "x"; Var "y"; Var "z"; Var "f"; Var "g"; Var "p"]),
          Cons ("fst", [Var "y"; Var "z"; Var "p"])
        ),
        Var "f"
      )
    );
    "pairing-beta-r", (
      ["x", Obj; "y", Obj; "z", Obj;
       "f", Hom (Var "x", Var "y");
       "g", Hom (Var "x", Var "z");
       "p", Cons ("prod", [Var "y"; Var "z"])],
      Eq (
        Comp (
          Cons ("pairing", [Var "x"; Var "y"; Var "z"; Var "f"; Var "g"; Var "p"]),
          Cons ("snd", [Var "y"; Var "z"; Var "p"])
        ),
        Var "g"
      )
    );
    "pairing-eta", (
      ["x", Obj; "y", Obj; "z", Obj;
       "f", Hom (Var "x", Var "y");
       "g", Hom (Var "x", Var "z");
       "p", Cons ("prod", [Var "y"; Var "z"]);
       "h", Hom (Var "x", Var "p")
      ],
      Eq (Var "h", Cons ("pairing", [Var "x"; Var "y"; Var "z"; Var "f"; Var "g"; Var "p"]))
    )
  ]

let term_constructors = ref term_constructors

(** Raise on typing error. *)
exception Typing

(** The subtyping relation. *)
let rec ( <: ) (a : Type.t) (b : Type.t) =
  (* TODO: recursively use convertibility on terms *)
  match a, b with
  | a, b when a = b -> ()
  | Cons (c, l), b ->
    (
      let p, a = List.assoc c !type_constructors in
      let s = List.map2 (fun t (x, _) -> x, t) l p in
      let a = Type.subst s a in
      a <: b
    )
  | _ -> raise Typing

(** Ensure that we have a type. *)
let rec check_type env (a : Type.t) =
  match a with
  | Obj -> ()
  | Hom (t, u) ->
    infer env t <: Obj;
    infer env u <: Obj
  | Eq (f, g) ->
    (
      match infer env f, infer env g with
      | Hom (a, b), Hom (a', b') when conv a a' && conv b b' -> ()
      | a, b ->
        Printf.printf "equality between %s and %s\n%!" (Type.to_string a) (Type.to_string b);
        raise Typing
    )
  | Cons (c, l) ->
    let a = match List.assoc_opt c !type_constructors with Some a -> a | None -> raise Typing in
    List.iter2 (fun t (_,a) -> check env t a) l (fst a)

(** Check that a term has a given type. *)
and check env t a =
  infer env t <: a

(** Infer the type of a term. *)
and infer env (t : t) : Type.t =
  match t with
  | Var x ->
    (
      match List.assoc_opt x env with
      | Some a -> a
      | None -> raise Typing
    )
  | Id t ->
    infer env t <: Obj;
    Hom (t, t)
  | Comp (t, u) ->
    (
      match infer env t, infer env u with
      | Hom (a, b), Hom (b', c) when conv b b' -> Hom (a, c)
      | _ -> raise Typing
    )
  | Cons (c, l) ->
    let e, a = match List.assoc_opt c !term_constructors with Some ea -> ea | None -> raise Typing in
    let _, s = List.fold_left2 (fun (env,s) t (x, a) -> infer env t <: a; (x,a)::env, (x,t)::s) (env, []) l e in
    Type.subst s a

(** Declarations. *)
module Decl = struct
  type t =
    | Type of string * context * Type.t
    | Term of string * context * Type.t

  let check (env : context) : t -> context = function
    | Type (c, l, a) ->
      let env = List.fold_left (fun env (x, a) -> check_type env a; (x,a)::env) env l in
      check_type env a;
      type_constructors := (c,(l,a)) :: !type_constructors;
      env
    | Term (c, l, a) ->
      let env = List.fold_left (fun env (x, a) -> check_type env a; (x,a)::env) env l in
      check_type env a;
      term_constructors := (c,(l,a)) :: !term_constructors;
      env

  module List = struct
    let check env d =
      List.fold_left check env d
  end
end

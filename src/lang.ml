(** A term. *)
type t =
  | Var of string
  | Id of t
  | Comp of t * t
  | Cons of string * t list (** A constructor. *)

type term = t


(** Equality on terms. *)
let conv (t : t) (u : t) =
  (* TODO: normalize comp *)
  t = u

module Type = struct
  (** A type. *)
  type t =
    | Obj (** An object. *)
    | Hom of term * term (** A morphism. *)
    | Eq of term * term (** An equality between parallel morphisms. *)
    | Cons of string * term list (** A constructor. *)
end

(** A context. *)
type context = (string * Type.t) list

(** Similar to a context but we can use constructors there. *)
type pattern = (t * Type.t) list

(** Object constructors: these are types which can be casted as objects. *)
let obj_constructors : (string * Type.t list) list =
  [
    ("prod", [Obj; Obj])
  ]

let type_constructors = obj_constructors

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

exception Typing

(** The subtyping relation. *)
let ( <: ) (a : Type.t) (b : Type.t) =
  (* TODO: recursively use convertibility on terms *)
  match a, b with
  | a, b when a = b -> ()
  | Cons (c, _), Obj when List.mem_assoc c obj_constructors -> ()
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
      | _ -> raise Typing
    )
  | Cons (c, l) ->
    let a = match List.assoc_opt c type_constructors with Some a -> a | None -> raise Typing in
    List.iter2 (fun t a -> check env t a) l a

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
    let e, a = match List.assoc_opt c term_constructors with Some ea -> ea | None -> raise Typing in
    let env', s = List.fold_left2 (fun s t (x, a) -> check env ) (env, []) l e in

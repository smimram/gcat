type pos = Lexing.position * Lexing.position

(** Terms. *)
module Term = struct
  type t =
    {
      pos : pos;
      term : term
    }

  and term =
    | Var of string
    | Id of t
    | Comp of t * t
    (* | Cons of string * t list (\** A constructor. *\) *)
    | Obj (** An object. *)
    | Hom of t * t (** A morphism. *)
    | Eq of t * t (** An equality between parallel morphisms. *)
    | Fun of string * t * t
    | Pi of string * t * t (** A pi type. *)
    | Sigma of string * t * (string * t) list (** A sigma type. *)
    | Record of t * (string * t) list
    | Type

  let make pos term = { pos; term }

  let pi pos args b =
    let rec aux = function
      | [] -> b
      | (x,a)::l -> make pos (Pi (x, a, aux l))
    in
    aux args

  let fct pos args t =
    let rec aux = function
      | [] -> t
      | (x,a)::l -> make pos (Fun (x, a, aux l))
    in
    aux args
end

type t =
  | Id of t
  | Comp of t list
  | Obj
  | Hom of t * t
  | Eq of t * t
  | Fun of string * environment * Term.t
  | Pi of string * t * environment * Term.t
  | Sigma of string * t * (string * t) list
  | Record of t * (string * t) list
  | Type

(** An environment. *)
and environment = (string * t) list

(** A typing context. *)
type context = (string * t) list

(** Evaluate a term to a value. *)
let rec eval (env : environment) (t : Term.t) : t =
  match t.term with
  | Var x -> List.assoc x env
  | Id t -> Id (eval env t)
  | Comp (t, u) ->
    (
      match eval env t, eval env u with
      | Id _, u -> u
      | t, Id _ -> t
      | Comp l, Comp l' -> Comp (l@l')
      | Comp l, u -> Comp (l@[u])
      | t, Comp l -> Comp (t::l)
      | t, u -> Comp [t;u]
    )
  | Obj -> Obj
  | Hom (t, u) -> Hom (eval env t, eval env u)
  | Eq (t, u) -> Eq (eval env t, eval env u)
  | Fun (x, _, t) -> Fun (x, env, t)
  | Pi (x, a, b) -> Pi (x, eval env a, env, b)
  | Sigma (x, a, l) -> Sigma (x, eval env a, List.map (fun (l, a) -> l, eval env a) l)
  | Record (t, l) -> Record (eval env t, List.map (fun (l, t) -> l, eval env t) l)
  | Type -> Type


(** Convertibility of terms. *)
let conv (t:t) (u:t) =
  t = u

exception Typing of pos * string

let rec check (env:environment) (tenv:context) (t:Term.t) (a:t) : Term.t =
  match t.term, a with
  (* | Fun (x, a, t)  *)
  | _ ->
    let t', a' = infer env tenv t in
    if not (conv a a') then raise (Typing (t.pos, "..."));
    t'

and infer env tenv t : Term.t * t =
  match t.term with
  | Type -> t, Type
  | _ -> ignore env; ignore tenv; assert false

(*
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

let type_constructors = ref []
let term_constructors = ref []

(** Raise on typing error. *)
exception Typing of string

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
  | _ -> raise (Typing "")

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
        raise (Typing (Printf.sprintf "equality between elements of types %s and %s%!" (Type.to_string a) (Type.to_string b)));
    )
  | Cons (c, l) ->
    let a = match List.assoc_opt c !type_constructors with Some a -> a | None -> raise (Typing "") in
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
      | None -> raise (Typing (Printf.sprintf "Variable not found: %s." x))
    )
  | Id t ->
    infer env t <: Obj;
    Hom (t, t)
  | Comp (t, u) ->
    (
      match infer env t, infer env u with
      | Hom (a, b), Hom (b', c) when conv b b' -> Hom (a, c)
      | _ -> raise (Typing "")
    )
  | Cons (c, l) ->
    let e, a = match List.assoc_opt c !term_constructors with Some ea -> ea | None -> raise (Typing "") in
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
      (c,a)::env

  module List = struct
    let check env d =
      List.fold_left check env d
  end
end
*)

module Decl = struct
  (** A declaration: name, type, value. *)
  type t = string * Term.t * Term.t

  let check d =
    let check env tenv ((x, a, t) : t) =
      let a = check env tenv a Type in
      let a = eval env a in
      let t = check env tenv t a in
      let t = eval env t in
      ((x,t)::env), ((x,a)::tenv)
    in
    ignore (List.fold_left (fun (env,tenv) -> check env tenv) ([],[]) d)
end

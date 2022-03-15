module Pos = struct
  type t = Lexing.position * Lexing.position

  let dummy : t = Lexing.dummy_pos, Lexing.dummy_pos

  let to_string (p1,p2) =
    let open Lexing in
    if p1.pos_lnum = p2.pos_lnum then Printf.sprintf "line %d, character %d-%d" p1.pos_lnum (p1.pos_cnum - p1.pos_bol) (p2.pos_cnum - p2.pos_bol)
    else Printf.sprintf "from line %d, character %d to line %d character %d" p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum (p2.pos_cnum - p2.pos_bol)
end

(** Terms. *)
module Term = struct
  type t =
    {
      pos : Pos.t;
      mutable term : term
    }

  and term =
    | Var of string
    | Id of t
    | Comp of t * t
    (* | Cons of string * t list (\** A constructor. *\) *)
    | Obj (** An object. *)
    | Hom of t * t (** A morphism. *)
    | Eq of t * t (** An equality between parallel morphisms. *)
    | App of t * t
    | Abs of string * t * t
    | Pi of string * t * t (** A pi type. *)
    | Sigma of (string * t) list (** A sigma type (record). *)
    | Record of (string * t) list
    | Field of t * string
    | Type
    | Hole

  let make pos term = { pos; term }

  let copy t = make t.pos t.term

  let app pos t l =
    let rec aux t = function
      | [] -> t
      | u::l -> aux (make pos (App (t, u))) l
    in
    aux t l

  let pi pos args b =
    let rec aux = function
      | [] -> b
      | (x,a)::l -> make pos (Pi (x, a, aux l))
    in
    aux args

  let fct pos args t =
    let rec aux = function
      | [] -> t
      | (x,a)::l -> make pos (Abs (x, a, aux l))
    in
    aux args

  let rec to_string t =
    match t.term with
    | Var x -> x
    | Id t -> Printf.sprintf "id(%s)" (to_string t)
    | Comp (t, u) -> Printf.sprintf "%s ; %s" (to_string t) (to_string u)
    | Obj -> "*"
    | Hom (t, u) -> Printf.sprintf "%s -> %s" (to_string t) (to_string u)
    | Eq (t, u) -> Printf.sprintf "%s == %s" (to_string t) (to_string u)
    | App _ ->
      let t, u =
        let rec aux l t =
          match t.term with
          | App (t, u) -> aux (u::l) t
          | _ -> t, l
        in
        aux [] t
      in
      Printf.sprintf "%s(%s)" (to_string t) (List.map to_string u |> String.concat ", ")
    | Abs (x, a, t) -> Printf.sprintf "fun (%s : %s) -> %s" x (to_string a) (to_string t)
    | Pi (x, a, b) -> Printf.sprintf "(%s : %s) => %s" x (to_string a) (to_string b)
    | Sigma l -> Printf.sprintf "{ %s }" (List.map (fun (l,a) -> l ^ " : " ^ to_string a) l |> String.concat ", ")
    | Record l -> Printf.sprintf "{%s}" (List.map (fun (l,t) -> l ^ " = " ^ to_string t) l |> String.concat ", ")
    | Field (t, "") -> Printf.sprintf "!%s" (to_string t)
    | Field (t, l) -> Printf.sprintf "%s.%s" (to_string t) l
    | Type -> "Type"
    | Hole -> "?"
end

type t =
  | Var of string
  | Id of t
  | Comp of t list
  | Obj
  | Hom of t * t
  | Eq of t * t
  | App of t * t list
  | Abs of string * environment * Term.t
  | Pi of string * t * environment * Term.t
  | Sigma of environment * (string * Term.t) list
  | Record of (string * t) list
  | Field of t * string
  | Type
  | Hole

(** An environment. *)
and environment = (string * t) list

(** A typing context. *)
type context = (string * t) list

(** Evaluate a term to a value. *)
let rec eval (env : environment) (t : Term.t) : t =
  (* Printf.printf "eval: %s\n%!" (Term.to_string t); *)
  (* Printf.printf "      [%s]\n%!" (env |> List.map fst |> String.concat ","); *)
  match t.term with
  | Var x ->
    (
      match List.assoc_opt x env with
      | Some v -> v
      | None -> failwith ("Variable not found during evaluation: " ^ x)
    )
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
  | App (t, u) ->
    let t = eval env t in
    let u = eval env u in
    (
      match t with
      | Abs (x, env, t) -> eval ((x,u)::env) t
      | App (t, tt) -> App (t, u::tt)
      | _ -> App (t, [u])
    )
  | Abs (x, _, t) -> Abs (x, env, t)
  | Pi (x, a, b) -> Pi (x, eval env a, env, b)
  | Sigma f -> Sigma (env, f)
  | Record l -> Record (List.map (fun (l, t) -> l, eval env t) l)
  | Field (t, l) ->
    (
      match eval env t with
      | Record f ->
        if l = "" then List.hd f |> snd
        else List.assoc l f
      | t -> Field (t, l)
    )
  | Type -> Type
  | Hole -> Hole

let fresh =
  let n = ref (-1) in
  fun () ->
    incr n; "_x" ^ string_of_int !n

let rec quote (t : t) : Term.t =
  let mk = Term.make Pos.dummy in
  match t with
  | Var x -> mk (Var x)
  | Id t -> mk (Id (quote t))
  | Comp (t::l) -> List.fold_left (fun t u -> mk (Term.Comp (t, quote u))) (quote t) l
  | Comp [] -> assert false
  | Obj -> mk Obj
  | Hom (t, u) -> mk (Hom (quote t, quote u))
  | Eq (t, u) -> mk (Eq (quote t, quote u))
  | App (t, uu) -> List.fold_right (fun u t -> mk (App (t, quote u))) uu (quote t)
  | Abs _ -> failwith "TODO: abs"
  | Pi (x, a, env, t) ->
    let x' = fresh () in
    mk (Pi (x', quote a, quote (eval ((x, Var x')::env) t)))
  | Sigma (env, f) ->
    let _, f = List.fold_left_map (fun env (l, a) -> (l, Var l)::env, (l, quote (eval env a))) env f in
    mk (Sigma f)
  | Record _ -> failwith "TODO: record"
  | Field (t, l) -> mk (Field (quote t, l))
  | Type -> mk Type
  | Hole -> mk Hole

let to_string t = Term.to_string (quote t)

(** Convertibility of terms. *)
let rec conv (t:t) (u:t) =
  match t, u with
  | _ when t = u -> true
  | Hole, _ | _, Hole -> true
  | Eq (t, u), Eq (t', u') -> conv t t' && conv u u'
  | Hom (t, u), Hom (t', u') -> conv t t' && conv u u'
  | _ -> false

exception Typing of Pos.t * string

let typing pos fmt = Printf.kprintf (fun s -> raise (Typing (pos, s))) fmt

let rec check (env:environment) (tenv:context) (t:Term.t) (a:t) =
  (* Printf.printf "check: %s : %s\n%!" (Term.to_string t) (to_string a); *)
  (* Printf.printf "       [%s]\n%!" (env |> List.map fst |> String.concat ", "); *)
  match t.term, a with
  | Abs (x, a, t), Pi (x', a', env', b) ->
    let a = eval env a in
    assert (conv a a');
    let b = eval ((x', Var x)::env') b in
    check ((x, Var x)::env) ((x, a)::tenv) t b
  | Record tt, Sigma (env', aa) ->
    let _ =
      List.fold_left2
        (fun (env,env',tenv) (l,u) (l',a) ->
           assert (l = l');
           let a = eval env' a in
           check env tenv u a;
           (l, eval env u)::env, (l, eval env u)::env', (l, a)::tenv
        ) (env,env',tenv) tt aa
    in
    ()
  | Hole, a ->
    Printf.printf "? : %s\n%!" (to_string a)
  | _ ->
    let a' = infer env tenv t in
    if not (conv a a') then
      (
        match a' with
        | Sigma _ ->
          (* We can implicitly cast a record as its main field. *)
          t.term <- Field (Term.copy t, ""); check env tenv t a
        | _ -> typing t.pos "Got %s but %s expected." (to_string a') (to_string a)
      )

and infer env tenv t : t =
  (* Printf.printf "infer: %s\n%!" (Term.to_string t); *)
  (* Printf.printf "       [%s]\n%!" (env |> List.map fst |> String.concat ", "); *)
  let t0 = t in
  match t.term with
  | Var x ->
    (
      match List.assoc_opt x tenv with
      | Some a -> a
      | None -> raise (Typing (t.pos, "Variable not found: " ^ x))
    )
  | Sigma f ->
    let _ = List.fold_left (fun (env, tenv) (l, a) -> check env tenv a Type; ((l, Var l)::env, (l, eval env a)::tenv)) (env, tenv) f in
    Type
  | Field (t, l) ->
    let tv = eval env t in
    (* Printf.printf "field of %s\n%!" (to_string tv); *)
    (
      match infer env tenv t with
      | Sigma (env, f) ->
        (* Resolve default field. *)
        let l =
          if l = "" then
            let l = List.hd f |> fst in
            t0.term <- Field (t, l);
            l
          else
            l
        in
        let rec aux (env,tenv) = function
          | (l', b)::_ when l' = l -> eval env b
          | (l, b)::f ->
            let b = eval env b in
            let env = (l, Field (tv, l))::env in
            let tenv = (l,b)::tenv in
            aux (env,tenv) f
          | [] -> assert false
        in
        aux (env,tenv) f
      | a -> typing t.pos "Record expected but got %s." (to_string a)
    )
  | App (t, u) ->
    (
      match infer env tenv t with
      | Pi (x, a, env', b) ->
        check env tenv u a;
        let u = eval env u in
        eval ((x,u)::env') b
      | _ -> typing t.pos "Function expected."
    )
  | Obj -> Type
  | Hom (t, u) ->
    check env tenv t Obj;
    check env tenv u Obj;
    Type
  | Eq (t, u) ->
    (
      match infer env tenv t with
      | Hom _ as a -> check env tenv u a
      | _ -> assert false
    );
    Type
  | Id t ->
    check env tenv t Obj;
    let t = eval env t in
    Hom (t, t)
  | Comp (t, u) ->
    (
      match infer env tenv t, infer env tenv u with
      | Hom (x, y), Hom (y', z) ->
        assert (conv y y');
        Hom (x, z)
      | _ -> assert false
    )
  | Pi (x, a, b) ->
    check env tenv a Type;
    check ((x,Var x)::env) ((x,eval env a)::tenv) b Type;
    Type
  | Type -> Type
  | _ -> assert false

let has_type env tenv t a =
  try ignore (check env tenv t a); true
  with Typing _ -> false

module Decl = struct
  (** A declaration: name, type, value. *)
  type t = string * Term.t * Term.t

  let check d =
    let check env tenv ((x, a, t) : t) =
      Printf.printf "def: %s\n%!" x;
      check env tenv a Type;
      let a = eval env a in
      check env tenv t a;
      let t = eval env t in
      ((x,t)::env), ((x,a)::tenv)
    in
    List.fold_left (fun (env,tenv) -> check env tenv) ([],[]) d
end

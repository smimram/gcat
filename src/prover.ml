let interactive = ref false
let fname = ref ""

open Lang

let () =
  Printexc.record_backtrace true;
  Arg.parse
    [
      "-i", Arg.Set interactive, "Interactive mode";
    ]
    (fun f -> fname := f) "prover [options] [file]";
  let env, tenv =
    if !fname = "" then [], [] else
      let ic = open_in !fname in
      let lexbuf = Lexing.from_channel ic in
      let decls =
        try
          Parser.main Lexer.token lexbuf
        with
        | Failure err ->
          let pos = (Lexing.lexeme_end_p lexbuf) in
          let err =
            Printf.sprintf
              "Lexing error at line %d, character %d: %s"
              pos.Lexing.pos_lnum
              (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
              err
          in
          failwith err
        | Parsing.Parse_error | Parser.Error ->
          let pos = (Lexing.lexeme_end_p lexbuf) in
          let err =
            Printf.sprintf
              "Parse error at word \"%s\", line %d, character %d."
              (Lexing.lexeme lexbuf)
              pos.Lexing.pos_lnum
              (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
          in
          failwith err
      in
      close_in ic;
      try Decl.check decls
      with Typing (pos, e) ->
        let bt = Printexc.get_raw_backtrace () in
        Printf.printf "\nTyping error at %s:\n%s\n\n%s\n%!" (Pos.to_string pos) e (Printexc.raw_backtrace_to_string bt);
        exit 1
  in
  let env = ref env in
  let tenv = ref tenv in
  let state = ref [] in
  let term t = Term.make Pos.dummy t in
  while !interactive do
    try
      Printf.printf "# %!";
      let cmd = input_line stdin in
      let cmd, args =
        let l = String.split_on_char ' ' cmd in
        List.hd l, List.tl l |> String.concat " "
      in
      (
        match cmd with
        | "assume" ->
          let x, a = Lexing.from_string args |> Parser.typed_variable Lexer.token in
          check !env !tenv a Type;
          let av = eval !env a in
          env := (x, Var x) :: !env;
          tenv := (x, eval !env a) :: !tenv;
          state := !state @ [term (Var x), (a, av)]
        | "match" ->
          let f = args in
          let f = term (Var f) in
          let rec search (f : Term.t) : Term.t list =
            match infer !env !tenv f with
            | Pi (_, a, _, _) ->
              let ff = List.filter_map (fun (t, (_, a')) -> if conv a' a then Some (term (App (f, t))) else None) !state in
              List.map search ff |> List.flatten
            | _ -> [f]
          in
          let ff = search f in
          List.iter (fun t -> Printf.printf "- %s\n%!" (Term.to_string t)) ff
        | cmd -> failwith ("Unknown command: " ^ cmd)
      );
      Printf.printf "OK: %s\n%!" (List.map (fun (t, (a, _)) -> Term.to_string t ^ " : " ^ Term.to_string a) !state |> String.concat ", ")
    with
    | End_of_file -> print_newline (); exit 0
    | e -> Printf.printf "Error: %s\n%!" (Printexc.to_string e)
  done

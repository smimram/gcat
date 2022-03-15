let interactive = ref false
let fname = ref ""

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
      try Lang.Decl.check decls
      with Lang.Typing (pos, e) ->
        let bt = Printexc.get_raw_backtrace () in
        Printf.printf "\nTyping error at %s:\n%s\n\n%s\n%!" (Lang.Pos.to_string pos) e (Printexc.raw_backtrace_to_string bt);
        exit 1
  in
  let env = ref env in
  let tenv = ref tenv in
  let state = ref [] in
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
          Lang.check !env !tenv a Lang.Type;
          env := (x, Var x) :: !env;
          tenv := (x, Lang.eval !env a) :: !tenv;
          state := !state @ [Lang.Var x, a]
        (* | "match" -> *)
          (* let x = args in *)
        | cmd -> Printf.printf "Unknown command: %s\n%!" cmd
      );
      Printf.printf "OK: %s\n%!" (List.map (fun (t, a) -> Lang.to_string t ^ " : " ^ Lang.Term.to_string a) !state |> String.concat ", ")
    with
    | End_of_file -> print_newline (); exit 0
    | e -> Printf.printf "Error: %s\n%!" (Printexc.to_string e)
  done

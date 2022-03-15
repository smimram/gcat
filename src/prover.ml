let () =
  Printexc.record_backtrace true;
  let fname = Sys.argv.(1) in
  let ic = open_in fname in
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
    let err = Printf.sprintf "Typing error at %s: %s." (Lang.Pos.to_string pos) e in
    failwith err

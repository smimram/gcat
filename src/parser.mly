%{
open Lang
%}

%token<string> IDENT
%token EOF

%start main
%type<Lang.t> main
%%

main:
   | def EOF { $1 }

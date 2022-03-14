%{
open Lang.Term

let decl pos name args a t : Lang.Decl.t =
  name, pi pos args a, fct pos args t
%}

%token LPAR RPAR LACC RACC
%token OBJ TO EQUALS ID SC
%token EQ COLON COMMA PIPE IMP
%token<string> IDENT
%token EOF

%right IMP
%nonassoc TO
%nonassoc EQUALS
%right SC
%nonassoc LPAR

%start main
%type<Lang.Decl.t list> main
%%

main:
   | decls EOF { $1 }

decls:
   | decl decls { $1::$2 }
   | { [] }

decl:
   | IDENT args COLON term EQ term { decl $loc $1 $2 $4 $6 }
   | IDENT args EQ term { decl $loc $1 $2 (make $loc Type) $4 }

args:
   | LPAR IDENT COLON term RPAR args { ($2,$4)::$6 }
   | { [] }

term:
   | IDENT { make $loc (Var $1) }
   | LACC IDENT COLON term PIPE sigma_fields RACC { make $loc (Sigma ($2, $4, $6)) }
   | OBJ { make $loc Obj }
   | args IMP term { pi $loc $1 $3 }
   | term TO term { make $loc (Hom ($1, $3)) }
   | term EQUALS term { make $loc (Eq ($1, $3)) }
   | term LPAR term RPAR { make $loc (App ($1, $3)) }
   | ID LPAR term RPAR { make $loc (Id ($3)) }
   | term SC term { make $loc (Comp ($1, $3)) }

sigma_fields:
  | IDENT COLON term COMMA sigma_fields { ($1,$3)::$5 }
  | IDENT COLON term { [$1,$3] }

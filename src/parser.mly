%{
open Lang.Term

let decl pos name args a t : Lang.Decl.t =
  name, pi pos args a, fct pos args t
%}

%token LPAR RPAR LACC RACC
%token OBJ TO EQUALS ID SC HOLE
%token EQ COLON COMMA IMP BANG DOT
%token<string> IDENT
%token EOF

%right IMP
%nonassoc TO
%nonassoc EQUALS
%right SC
%nonassoc BANG
%nonassoc LPAR
%left DOT

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
   | LACC sigma_fields RACC { make $loc (Sigma ($2)) }
   | LACC record_fields RACC { make $loc (Record ($2)) }
   | OBJ { make $loc Obj }
   | args IMP term { pi $loc $1 $3 }
   | term TO term { make $loc (Hom ($1, $3)) }
   | term EQUALS term { make $loc (Eq ($1, $3)) }
   | term LPAR terms RPAR { app $loc $1 $3 }
   | ID LPAR term RPAR { make $loc (Id ($3)) }
   | term SC term { make $loc (Comp ($1, $3)) }
   | HOLE { make $loc Hole }
   | BANG term { make $loc (Field ($2, "")) }
   | term DOT IDENT { make $loc (Field ($1, $3)) }

terms:
   | { [] }
   | term { [$1] }
   | term COMMA terms { $1::$3 }

sigma_fields:
  | IDENT COLON term COMMA sigma_fields { ($1,$3)::$5 }
  | IDENT COLON term { [$1,$3] }

record_fields:
  | IDENT EQ term COMMA record_fields { ($1,$3)::$5 }
  | IDENT EQ term { [$1,$3] }

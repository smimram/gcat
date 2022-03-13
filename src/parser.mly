%{
%}

%token LPAR RPAR
%token OBJ TO EQUALS SC
%token CONS COLON LCOLON COMMA
%token<string> IDENT
%token EOF

%right SC

%start main
%type<Lang.Decl.t list> main
%%

main:
   | decls EOF { $1 }

decls:
   | decl decls { $1::$2 }
   | { [] }

decl:
   | CONS IDENT args LCOLON typ { Type ($2, $3, $5) }
   | CONS IDENT args COLON typ { Term ($2, $3, $5) }

args:
   | LPAR IDENT COLON typ RPAR args { ($2,$4)::$6 }
   | { [] }

typ:
   | OBJ { Obj }
   | term TO term { Hom ($1, $3) }
   | IDENT LPAR terms RPAR { Cons ($1, $3) }
   | term EQUALS term { Eq ($1, $3) }

term:
   | IDENT { Var $1 }
   | IDENT LPAR terms RPAR { Cons ($1, $3) }
   | term SC term { Comp ($1, $3) }

terms:
   | { [] }
   | term { [$1] }
   | term COMMA terms { $1::$3 }

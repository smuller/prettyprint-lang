%{
    open Types

    let mk = mk ()
       
%}

%token <int> NUM
%token <string> STRING
%token <string> IDENT
%token TRUE FALSE UNIT NIL
%token TINT TSTRING TBOOL TUNIT TLIST
%token <string> TIDENT
%token PLUS MINUS TIMES DIV
%token CARAT
%token AND OR
%token COLON COMMA CONS
%token LT LE GT GE NE
%token EQUAL
%token IF THEN ELSE
%token MATCH WITH PIPE
%token LET REC IN
%token FUN ARROW
%token LPAREN RPAREN
%token SEMICOLON
%token EOF
%token APP
%token SPACE
%token NEWLINE

%right ARROW
%nonassoc COLON
%left COMMA
%left LT LE GT GE NE EQUAL
%left PLUS MINUS
%left TIMES DIV
%left AND OR
%left APP


%start main
%type <unit Types.expr> main

%%
main:
  expr NEWLINE                             { $1 }
;

expr:
  const                                    { mk (EConst $1) }
| IDENT                                    { mk (EVar $1) }
| infixop                                  { mk $1 }
| FUN IDENT ARROW expr                     { mk (EFun ($2, $4)) }
| IF expr THEN expr ELSE expr              { mk (EIf ($2, $4, $6)) }
| LET IDENT SPACE EQUAL expr IN expr       { mk (ELet ($2, None, $5, $7)) }
| LET REC IDENT SPACE dpat optannot SPACE EQUAL expr IN expr
                      { mk (ELetFun (true, $3, fst $5, snd $5, $6, $9, $11)) }
| LET IDENT dpat optannot EQUAL expr IN expr
                      { mk (ELetFun (false, $2, fst $3, snd $3, $4, $6, $8)) }
| LET LPAREN IDENT COMMA IDENT RPAREN EQUAL expr IN expr
                                           { mk (ELetPair ($3, $5, $8, $10)) }
| MATCH expr WITH NIL ARROW expr PIPE IDENT CONS IDENT ARROW expr
                                           { mk (EMatchList ($2, $6, $8, $10, $12)) }
| MATCH expr WITH PIPE NIL ARROW expr PIPE IDENT CONS IDENT ARROW expr
                                           { mk (EMatchList ($2, $7, $9, $11, $13)) }
| expr CONS expr                           { mk (ECons ($1, $3)) }
| LPAREN expr RPAREN                       { mk (EParen $2) }
| expr SPACE expr %prec APP                { mk (EApp ($1, $3)) }
| expr COLON typ                           { mk (EAnnot ($1, $3)) }
| expr COMMA expr %prec COMMA              { mk (EPair ($1, $3)) }
| SPACE expr                               { mk (ESpaceBefore $2) }
| expr SPACE                               { mk (ESpaceAfter $1) }
| NEWLINE expr                             { mk (ELinebreakBefore $2) }
//| expr NEWLINE                             { mk (ELinebreakAfter $1) }
;

dpat:
  IDENT                                    { ($1, None) }
| LPAREN IDENT COLON typ RPAREN            { ($2, Some $4) }
| IDENT COLON typ                          { ($1, Some $3) }

optannot:
  COLON typ                                { Some $2 }
|                                          { None }

const:
  NUM                                      { Num $1 }
| STRING                                   { String $1 }
| TRUE                                     { Bool true }
| FALSE                                    { Bool false }
| UNIT                                     { Unit }
| NIL                                      { Nil }
;

typ:
  TINT                                     { TInt }
| TSTRING                                  { TString }
| TBOOL                                    { TBool }
| TUNIT                                    { TUnit }
//| TIDENT                                   { TVar $1 }
| LPAREN typ RPAREN                        { $2 }
| typ TLIST                                { TList $1 }
| typ ARROW typ                            { TArrow ($1, $3) }
;


infixop:
  expr PLUS expr                           { EInfixop (Plus, $1, $3) }
| expr MINUS expr                          { EInfixop (Minus, $1, $3) }
| expr TIMES expr                          { EInfixop (Times, $1, $3) }
| expr DIV expr                            { EInfixop (Div, $1, $3) }
| expr CARAT expr                          { EInfixop (Concat, $1, $3) }
| expr AND expr                            { EInfixop (And, $1, $3) }
| expr OR expr                             { EInfixop (Or, $1, $3) }
| expr EQUAL expr                          { EInfixop (Eq, $1, $3) }
| expr LT expr                             { EInfixop (Lt, $1, $3) }
| expr LE expr                             { EInfixop (Le, $1, $3) }
| expr GT expr                             { EInfixop (Gt, $1, $3) }
| expr GE expr                             { EInfixop (Ge, $1, $3) }
| expr NE expr                             { EInfixop (Ne, $1, $3) }
;

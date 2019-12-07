%{
    open Grammar
%}

%token <string> VAR
%token OPEN CLOSE LAMBDA DOT EOF

%start main
%type <Grammar.expression> main

%%
main:

    expression EOF { $1 }



expression:

    expression rest { Appl ($1, $2) }
    | rest { $1 }



rest:
    
    LAMBDA VAR DOT expression { Abst (Id ($2), $4) }
    | OPEN expression CLOSE { $2 }
    | VAR { Var (Id ($1) ) }

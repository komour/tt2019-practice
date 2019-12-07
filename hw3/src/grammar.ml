type variable = 
    Id of string
;;

type expression = 
    | Var  of variable
    | Appl of expression * expression
    | Abst of variable * expression
;;

type types = 
    | Vart  of string
    | Impl  of types * types

let nil = Var (Id "nil");;
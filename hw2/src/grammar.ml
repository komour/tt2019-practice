type variable = 
    Id of string
;;

type expression = 
    | Var of variable
    | Appl of expression * expression
    | Abst of variable * expression
    | Rap of expression ref
;;

let nil = Var (Id "nil");;
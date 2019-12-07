type variable = 
    Id of string
;;

type expression = 
    | Var of variable
    | Appl of expression * expression
    | Abst of variable * expression
;;
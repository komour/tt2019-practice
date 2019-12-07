open Grammar
let rec print_expr expr = match expr with
    | Var (Id v)     -> v
    | Appl (t1, t2)  -> "(" ^ print_expr t1 ^ " " ^ print_expr t2 ^ ")"
    | Abst (Id x, t) -> "(\\" ^ x ^ "." ^ print_expr t ^ ")" 

let rec print_types types = match types with
    | Vart t        -> t
    | Impl (t1, t2) -> "(" ^ print_types t1 ^ " -> " ^ print_types t2 ^ ")"
open Grammar

module Set = Set.Make(String)

let rec print_expr expr = match expr with
    | Var (Id v)     -> v
    | Appl (t1, t2)  -> "(" ^ print_expr t1 ^ " " ^ print_expr t2 ^ ")"
    | Abst (Id x, t) -> "(\\" ^ x ^ "." ^ print_expr t ^ ")" 
    | Rap t          -> print_expr !t

let rec fill_set_with_vars_from_term term mySet = match term with
    | Abst (Id x, t) -> fill_set_with_vars_from_term t (Set.add x mySet)
    | Appl (t1, t2)  -> Set.union (fill_set_with_vars_from_term t1 mySet) (fill_set_with_vars_from_term t2 mySet)
    | Var (Id v)     -> Set.singleton v
    | Rap t          -> fill_set_with_vars_from_term !t mySet


(*




(>(\x.x) (\x.x)<)_rap 



*)
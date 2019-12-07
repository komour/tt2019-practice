open Grammar

let rec print_expr expr = match expr with
    | Var (Id v) -> v
    | Appl (t1, t2) -> "(" ^ print_expr t1 ^ " " ^ print_expr t2 ^ ")"
    | Abst (Id x, t) -> "(\\" ^ x ^ "." ^ print_expr t ^ ")"

let expr = Parser.main Lexer.main (Lexing.from_channel stdin)
;;  

print_endline (print_expr expr)
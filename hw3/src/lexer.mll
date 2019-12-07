{
    open Parser
}

let variable = ['a' - 'z'] + ['a' - 'z' '0' - '9' '\'']*
let space = [' ' '\t' '\r' '\n']

rule main = parse
    | space { main lexbuf }
    | "\\" { LAMBDA }
    | variable as v { VAR (v) }
    | "." { DOT }
    | "(" { OPEN }
    | ")" { CLOSE }
    | eof { EOF }
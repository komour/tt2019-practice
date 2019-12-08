open Grammar
let rec print_expr expr = match expr with
    | Var (Id v)     -> v
    | Appl (t1, t2)  -> "(" ^ print_expr t1 ^ " " ^ print_expr t2 ^ ")"
    | Abst (Id x, t) -> "(\\" ^ x ^ "." ^ print_expr t ^ ")" 

let rec print_types types = match types with
    | Vart t        -> t
    | Impl (t1, t2) -> "(" ^ print_types t1 ^ " -> " ^ print_types t2 ^ ")"


let get_set_with_free_vars term = 
	 let bad_map = Hashtbl.create 512 in
	  let rec surf term = 
		match term with
	    | Var (Id v)     -> if not (Hashtbl.mem bad_map v) then (Set.singleton v) else Set.empty
	    | Abst (Id x, t) -> Hashtbl.add bad_map x true;
	    					let ret = surf t in
	    					Hashtbl.remove bad_map x;
	    					ret
	    | Appl (t1, t2)  -> Set.union (surf t1) (surf t2)
	in surf term

let make_context free_set' types_map expr =
	let free_set = ref free_set' in
	try 
	(
	let context = ref "" in
	let rec surf expr =
	  match expr with
	  | Var ( Id v )            ->  if (Set.mem v !free_set) then begin
	  									free_set := Set.remove v !free_set;
	  									context := !context ^ v ^ " : " ^ (print_types(Hashtbl.find types_map v)) ^ ", "
	  								end

	  | Abst ( Id x, t )        -> surf t

	  | Appl ( _M, _N )         -> surf _M; surf _N
	in surf expr;
	String.sub !context 0 ((String.length !context) - 2)
	) with Invalid_argument e -> ""

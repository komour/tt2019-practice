open Grammar
open Utils
open Hashtbl

exception No_Type

let indent = "*   "

let input_expr = let ret = Parser.main Lexer.main (Lexing.from_channel stdin) in 
  (*print_string (print_expr ret); 
    print_string "\n";*)
  ret

let counter = ref 0
let lambda_counter = ref 0

let get_lambda_name () = 
  lambda_counter := !lambda_counter + 1;
  "l" ^ string_of_int !lambda_counter

let get_name () = 
  counter := !counter + 1;
  "t" ^ string_of_int !counter

let sub_term term prev_name new_tree =
  let rec do_sub tree = 
    match tree with
    | Vart v     -> if v = prev_name then new_tree else tree
    | Impl (tree1, tree2) -> Impl (do_sub tree1, do_sub tree2)
  in do_sub term

let change_map map prev_name new_tree =
  Hashtbl.iter 
  (
    fun key value ->
    (
      let new_type = sub_term value prev_name new_tree in 
        Hashtbl.remove map key;
        Hashtbl.add map key new_type
    )
  ) map
(* TODO: Think about add and remove (dublicate adding) *)

let no_type_checker var term =
  let rec checker tree =
  match tree with
  | Vart v              -> if v = var then raise No_Type
  | Impl (tree1, tree2) -> checker tree1; checker tree2
 in checker term 

let solve_system (term1, term2) = 
  let system_map = Hashtbl.create 512 in
  (* print_string ((print_types term1) ^ " " ^ (print_types term2) ^ "\n"); *)
  let counter = ref 0 in
  let rec rec_solve (tree1, tree2) =
    match (tree1, tree2) with 
    | (Vart a, tree)                -> if not (Hashtbl.mem system_map a) then begin Hashtbl.add system_map a tree;
                                       counter := !counter + 1;
                                       no_type_checker a tree end
    | (tree, Vart a)                -> if not (Hashtbl.mem system_map a) then begin Hashtbl.add system_map a tree;
                                       counter := !counter + 1;
                                       no_type_checker a tree end
    | (Impl(l1, r1), Impl(l2, r2))  -> rec_solve (l1, l2);
                                       rec_solve (r1, r2) 
    in rec_solve (term1, term2);
      (system_map, (!counter - 1))

let big_sub system_map term =
  let rec do_sub tree = 
    match tree with
    | Vart v              -> if Hashtbl.mem system_map v then Hashtbl.find system_map v else tree
    | Impl (tree1, tree2) -> Impl (do_sub tree1, do_sub tree2)
  in do_sub term



let a_lot_subs types_map system_map =
  Hashtbl.iter 
  (
    fun key value ->
    (
      let new_type = big_sub system_map value in 
        Hashtbl.remove types_map key;
        Hashtbl.add types_map key new_type
    )
  ) types_map

let solve expr = 
  
       try
       (
        let types_map = Hashtbl.create 512 in
        let lambda_map = Hashtbl.create 512 in
        let sys2_map = Hashtbl.create 512 in
          let rec type_inference expr = 
          (
            match expr with
            | Var ( Id v )            ->  if Hashtbl.mem types_map v then 
                                            Hashtbl.find types_map v 
                                          else
                                            let v_type = Vart ( get_name () ) in
                                            Hashtbl.add types_map v v_type;
                                            v_type


            | Abst ( Id x, t )        ->  let x_type = Vart( get_name () ) in
                                            Hashtbl.add types_map x x_type;
                                            let t_type = type_inference t in
                                              let new_lambda_name = get_lambda_name () in 
                                              let new_x_type = Hashtbl.find types_map x in
                                              (*print_string (print_types new_x_type);*)
                                              Hashtbl.add lambda_map new_lambda_name x;
                                              Hashtbl.remove types_map x;
                                              Hashtbl.add types_map new_lambda_name new_x_type;
                                                Impl (new_x_type, t_type)


            | Appl ( _M, _N )         ->  let m_type' = ref (type_inference _M) in
                                          let n_type = type_inference _N in
                                          let m_type = big_sub sys2_map !m_type' in
                                          (*print_string ("f: " ^ (print_types (Hashtbl.find types_map "f")) ^ "\n");*)
                                          (*m_type' := type_inference _M;
                                                                              let m_type = !m_type' in*)
                                          (*print_string ((print_types m_type) ^ " " ^ (print_types n_type) ^ "\n");*)
                                          let micro_inf (term1, term2) = 
                                              match (term1, term2) with  

                                              | (Vart a, tree)                 -> let b = Vart ( get_name () ) in
                                                                                  let new_a = Impl (tree, b) in
                                                                                    no_type_checker a tree;
                                                                                    change_map types_map a new_a; 
                                                                                    Hashtbl.remove sys2_map a;
                                                                                    Hashtbl.add sys2_map a new_a;
                                                                                    b
                                              | (Impl(t11, t12), Vart v)       -> no_type_checker v t11;
                                                                                  change_map types_map v t11;
                                                                                  Hashtbl.remove sys2_map v;
                                                                                  Hashtbl.add sys2_map v t11;
                                                                                  sub_term t12 v t11
                                            
                                                                                                    (* check if v in t11 *)
                                              | (Impl(tree1, res_type), tree2) -> let (system_map, count) = solve_system (tree1, tree2) in
                                                                                  for i = 0 to count do
                                                                                    a_lot_subs types_map system_map
                                                                                  done;
                                                                                  let res = ref res_type in
                                                                                  for i = 0 to count do
                                                                                    res := big_sub system_map !res
                                                                                  done;
                                                                                  !res



                                          in micro_inf ( m_type, n_type )

                                  
            ) in
          type_inference expr
       ) with No_Type -> Vart "Expression has no type\n"
;;

let print_indent n = 
  for i = 0 to (n - 1) do print_string indent done

let expr_type = solve input_expr;

let rec print_ans tree n =
  match tree with
  | Var ( Id v )            ->  print_indent n;
                                print_string (v ^ " : ");
                                print_string ((print_types (Hashtbl.find types_map v)) ^ " [rule #1]")

  | Abst ( Id x, t )        -> ()

  | Appl ( _M, _N )         -> ()
 
 in print_ans






















open Grammar
open Utils
open Hashtbl

let indent = "*   "

let input_expr = Parser.main Lexer.main (Lexing.from_channel stdin)
;;

let counter = ref 0
let lambda_counter = ref 0

let get_name () = 
  counter := !counter + 1;
  "t" ^ string_of_int !counter

let sub_term term prev_name new_tree =
  let rec do_sub tree = 
    match tree with
    | Vart prev_name      -> new_tree
    | Vart _              -> tree
    | Impl (tree1, tree2) -> Impl (do_sub tree1, do_sub tree2)
  in do_sub term

let rec change_map map prev_name new_tree =
  Hashtbl.iter 
  (
    fun key value ->
    (
      let new_type = sub_term value prev_name new_tree in 
        Hashtbl.remove map key;
        Hashtbl.add map key new_type
    )
  )
;;
(* TODO: Think about add and remove (dublicate adding) *)

let solve expr = 
  let types_map = Hashtbl.create 512 in
  let lambda_map = Hashtbl.create 512 in
    let rec type_inference expr = 
    (
      match expr with
      | Var ( Id v )            ->  let v_type = Vart ( get_name () ) in
                                    Hashtbl.add types_map v v_type;
                                    v_type


      | Abst ( Id x, t )        ->  let x_type = Vart( get_name () ) in 
                                       let t_type = type_inference t in
                                        Hashtbl.add types_map x x_type;
                                          Impl (Hashtbl.find types_map x, t_type)


      | Appl ( _M, _N )         ->        let m_type = type_inference _M in
                                          let n_type = type_inference _N in
                                          let rec rec_inf (term1, term2) = 
                                          (
                                            match (term1, term2) with
                                            | (Vart a, tree) -> let b = Vart ( get_name () ) in
                                                                let new_a = Impl (tree, b) in
                                                                  change_map types_map a new_a;
                                                                  b
                                          ) in rec_inf ( m_type, n_type ) 

                            
      ) in
    type_inference expr
;;


print_endline (print_types (solve input_expr))
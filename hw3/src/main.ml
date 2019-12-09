open Grammar
open Utils
open List

exception No_Type

let counter = ref 0
let lambda_counter = ref 0

let indent = "*   "

let print_indent n = 
  for i = 0 to (n - 1) do print_string indent done

let get_lambda_name () = 
  lambda_counter := !lambda_counter + 1;
  string_of_int !lambda_counter

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



let turniket = " |- "


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
                                            let new_lambda_name = get_lambda_name () in 
                                            (* print_string "\n\n\n"; print_string new_lambda_name; print_string "\n\n\n"; *)
                                            let t_type = type_inference t in
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
          let free_set = get_set_with_free_vars expr in
          let expr_type = type_inference expr in
          let context = make_context free_set types_map expr in
            lambda_counter := 0;
          let advanced = ref Set.empty in
          let binds = Hashtbl.create 512 in
            (* let binds2 = Hashtbl.create 512 in *)
            let rec get_all tree number = 
            match tree with
            | Var ( Id v )            -> if Hashtbl.mem binds v then begin
                                            (* print_string " (keke) "; *)
                                           Hashtbl.find types_map (Hashtbl.find binds v)
                                          end 
                                         else begin 
                                            (* print_string " (keke1) "; *)
                                          Hashtbl.find types_map v
                                        end
            | Appl ( _M, _N )         -> (
                                          let m_type = get_all _M number in
                                          (* print_string " keke "; *)
                                          match m_type with
                                          | Impl (_, res) -> res
                                        )
            | Abst ( Id x, t )        ->  let x_type = Hashtbl.find types_map (string_of_int number) in
                                          Hashtbl.add binds x (string_of_int number);
                                          let t_type = get_all t (number + 1) in
                                          Hashtbl.remove binds x;
                                          Impl(x_type, t_type)
            in
            let flag = ref true in
            let rec print_all expr n = (
              match expr with
              | Var ( Id v )            ->  print_indent n;
                                            print_string context;

                                           if ((String.length context) > 0) then
                                             Set.iter (fun abc -> 
                                              print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))  
                                            ) !advanced
                                            else begin
                                             flag := true;
                                             Set.iter (fun abc -> 
                                              if !flag then flag := false else print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))  
                                            ) !advanced end;

                                            print_string turniket;
                                            print_string (v ^ " : ");
                                            if not (Hashtbl.mem binds v) then
                                            print_string ((print_types (Hashtbl.find types_map v)) ^ " [rule #1]\n")
                                          else begin (* print_string " keke "; *)
                                            print_string ((print_types (Hashtbl.find types_map ( Hashtbl.find binds v ))) ^ " [rule #1]\n")
                                          end

              | Abst ( Id x, t )        -> let ocherednoy = get_lambda_name () in 
                                           print_indent n;
                                           print_string context;
                                           if ((String.length context) > 0) then
                                             Set.iter (fun abc -> 
                                              print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))  
                                            ) !advanced
                                            else begin
                                             flag := true;
                                             Set.iter (fun abc -> 
                                              if !flag then flag := false else print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))  
                                            ) !advanced end;

                                           print_string turniket;
                                           print_string ((print_expr expr) ^ " : ");
                                           print_string (print_types (get_all expr (int_of_string ocherednoy)));
                                           print_string " [rule #3]\n";
                                           Hashtbl.add binds x ocherednoy;
                                           advanced := Set.union (!advanced) (Set.singleton ocherednoy);
                                           print_all t (n + 1);
                                           advanced := Set.remove ocherednoy !advanced;
                                           Hashtbl.remove binds ocherednoy




              | Appl ( _M, _N )         -> print_indent n;
                                           print_string context;
                                           if ((String.length context) > 0) then
                                             Set.iter (fun abc -> 
                                              print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))  
                                            ) !advanced
                                            else begin
                                             flag := true;
                                             Set.iter (fun abc -> 
                                              if !flag then flag := false else print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))  
                                            ) !advanced end;
                                           print_string turniket;
                                           print_string ((print_expr expr) ^ " : ");
                                           print_string (print_types (get_all expr !lambda_counter));
                                           print_string " [rule #2]\n";
                                           print_all _M (n + 1);
                                           print_all _N (n + 1)


            ) in print_all expr 0
     ) with No_Type -> print_string "Expression has no type\n"
;;


let input_expr = Parser.main Lexer.main (Lexing.from_channel stdin)
;;

solve input_expr





















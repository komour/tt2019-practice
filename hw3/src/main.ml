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

let no_type_checker var term =
  let rec checker tree =
  match tree with
  | Vart v              -> if v = var then raise No_Type
  | Impl (tree1, tree2) -> checker tree1; checker tree2
 in
  let temp_checker tree = 
    match tree with
    | Vart v1 -> ()
    | _ -> checker tree

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
      (system_map, (!counter))

let big_sub system_map term =
  let was_change = ref true in
  let ret = ref term in
  let rec do_sub tree = 
    match tree with
    | Vart v              -> if Hashtbl.mem system_map v then begin was_change := true; Hashtbl.find system_map v end
                               else tree
    | Impl (tree1, tree2) -> Impl (do_sub tree1, do_sub tree2)
  in
  while !was_change do
    was_change := false;
    ret := do_sub !ret
  done;
  !ret



let a_lot_subs types_map system_map =
  let was_change = ref true in 
  while !was_change do
    was_change := false;
    Hashtbl.iter 
    (
      fun key value ->
      (
          let new_type = big_sub system_map value in 
            if (not (new_type = value)) then was_change := true else was_change := !was_change;
            Hashtbl.remove types_map key;
            Hashtbl.add types_map key new_type
      )
    ) types_map 
  done



let turniket = "|- "

let solve expr = 
     try
     (
      let types_map = Hashtbl.create 512 in
      let lambda_map = Hashtbl.create 512 in
      let counter_temp = ref 0 in
      (* let sys2_map = Hashtbl.create 512 in *)
      let binds = Hashtbl.create 512 in
            (* let binds2 = Hashtbl.create 512 in *)
            let rec get_all tree number = 
            match tree with
            | Var ( Id v )            -> if Hashtbl.mem binds v then begin
                                           Hashtbl.find types_map (Hashtbl.find binds v)
                                          end 
                                         else begin 
                                          Hashtbl.find types_map v
                                        end
            | Appl ( _M, _N )         -> (
                                          let m_type = get_all _M number in
                                          (* print_string (print_types m_type); *)
                                          (* print_string " keke \n"; *)
                                          match m_type with
                                          | Impl (_, res) -> res
                                        )
            | Abst ( Id x, t )        ->  let x_type = Hashtbl.find types_map (string_of_int (number+1)) in
                                          Hashtbl.add binds x (string_of_int (number+1));
                                          counter_temp := !counter_temp + 1;
                                          let t_type = get_all t (number + 1) in
                                          Hashtbl.remove binds x;
                                          Impl(x_type, t_type)
            in

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
                                            let t_type = type_inference t in
                                            let new_x_type = Hashtbl.find types_map x in
                                            Hashtbl.add lambda_map new_lambda_name x;
                                            Hashtbl.remove types_map x;
                                            Hashtbl.add types_map new_lambda_name new_x_type;
                                              Impl (new_x_type, t_type)




          | Appl ( _M, _N )         ->  let tempc = !lambda_counter in 
                                        counter_temp := 0;
                                        let m_type' = ref (type_inference _M) in
                                        let n_type = (type_inference _N) in
                                        let m_type = get_all _M (tempc) in
                                        (* print_string ((print_types m_type) ^ " kuka\n"); *)
                                        (* let n_type = get_all _N (tempc + !counter_temp) in *)
                                        (* if (tempc = 0) then print_string ( (print_types m_type) ^ "\n" ^ (print_types(n_type)) ^"\n"); *)
                                        let micro_inf (term1, term2) = 
                                            match (term1, term2) with  

                                            | (Vart a, tree)                 -> let b = Vart ( get_name () ) in
                                                                                let new_a = Impl (tree, b) in
                                                                                  no_type_checker a tree;
                                                                                  change_map types_map a new_a; 
                                                                                  b
                                            | (Impl(Vart v1, t12), Vart v2)  -> if (v1 = v2) then t12 else begin
                                                                                  change_map types_map v2 (Vart v1);
                                                                                  sub_term t12 v2 (Vart v1)
                                                                                end

                                            | (Impl(t11, t12), Vart v)       -> no_type_checker v t11;
                                                                                change_map types_map v t11;
                                                                                sub_term t12 v t11
                                          
                                                                                                  (* check if v in t11 *)
                                            | (Impl(tree1, res_type), tree2) -> let (system_map, count) = solve_system (tree1, tree2) in
                                                                                let res = ref res_type in
                                                                                (* for i = 0 to count do *)
                                                                                  a_lot_subs types_map system_map;
                                                                                  res := big_sub system_map !res;
                                                                                (* done; *)
                                                                                !res



                                        in micro_inf ( m_type, n_type )

                                
          ) in

          let flag = ref true in
          let free_set = get_set_with_free_vars expr in
          let expr_type = type_inference expr in
          let context = make_context free_set types_map expr in
            lambda_counter := 0;
          let advanced = ref Set.empty in

          (* let print_context = 
            let costyl_space = ref true in
             let costyl_space2 = ref false in 
             if ((String.length context) > 0) then begin 
                costyl_space := false;
               Set.iter (fun abc -> 
                print_string ", ";
                print_string (Hashtbl.find lambda_map abc);
                print_string " : ";
                print_string (print_types(Hashtbl.find types_map abc))
              ) !advanced;
                print_string " keke "   
               end
              else begin
               flag := true;
               Set.iter (fun abc -> 
                if !flag then flag := false else print_string ", ";
                print_string (Hashtbl.find lambda_map abc);
                print_string " : ";
                print_string (print_types(Hashtbl.find types_map abc));
                if !costyl_space then costyl_space2 := true
              ) !advanced end;
              if !costyl_space2 then print_string " "
            in *)

            let rec print_all expr n = (
              match expr with
              | Var ( Id v )            ->  print_indent n;
                                            print_string context;


                                           let costyl_space = ref true in
                                           let costyl_space2 = ref false in 
                                           if ((String.length context) > 0) then begin 
                                              costyl_space := false;
                                             Set.iter (fun abc -> 
                                              print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))
                                            ) !advanced;
                                              print_string " "   
                                             end
                                            else begin
                                             flag := true;
                                             Set.iter (fun abc -> 
                                              if !flag then flag := false else print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc));
                                              if !costyl_space then costyl_space2 := true
                                            ) !advanced end;
                                            if !costyl_space2 then print_string " ";
                                            (* print_context; *)

                                            print_string turniket;
                                            print_string (v ^ " : ");
                                            if not (Hashtbl.mem binds v) then
                                            print_string ((print_types (Hashtbl.find types_map v)) ^ " [rule #1]\n")
                                          else begin
                                            print_string ((print_types (Hashtbl.find types_map ( Hashtbl.find binds v ))) ^ " [rule #1]\n")
                                          end

              | Abst ( Id x, t )        -> let ocherednoy = get_lambda_name () in 
                                           print_indent n;
                                           print_string context;
                                           let costyl_space = ref true in
                                           let costyl_space2 = ref false in 
                                           if ((String.length context) > 0) then begin 
                                              costyl_space := false;
                                             Set.iter (fun abc -> 
                                              print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))
                                            ) !advanced;
                                              print_string " "   
                                             end
                                            else begin
                                             flag := true;
                                             Set.iter (fun abc -> 
                                              if !flag then flag := false else print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc));
                                              if !costyl_space then costyl_space2 := true
                                            ) !advanced end;
                                            if !costyl_space2 then print_string " ";
                                            (* print_context; *)
                                           print_string turniket;
                                           print_string ((print_expr expr) ^ " : ");
                                           print_string (print_types (get_all expr ((int_of_string ocherednoy)-1) ));
                                           print_string " [rule #3]\n";
                                           Hashtbl.add binds x ocherednoy;
                                           advanced := Set.union (!advanced) (Set.singleton ocherednoy);
                                           print_all t (n + 1);
                                           advanced := Set.remove ocherednoy !advanced;
                                           Hashtbl.remove binds ocherednoy




              | Appl ( _M, _N )         -> print_indent n;
                                           print_string context;
                                           let costyl_space = ref true in
                                           let costyl_space2 = ref false in 
                                           if ((String.length context) > 0) then begin 
                                              costyl_space := false;
                                             Set.iter (fun abc -> 
                                              print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc))
                                            ) !advanced;
                                              print_string " "   
                                             end
                                            else begin
                                             flag := true;
                                             Set.iter (fun abc -> 
                                              if !flag then flag := false else print_string ", ";
                                              print_string (Hashtbl.find lambda_map abc);
                                              print_string " : ";
                                              print_string (print_types(Hashtbl.find types_map abc));
                                              if !costyl_space then costyl_space2 := true
                                            ) !advanced end;
                                            if !costyl_space2 then print_string " ";
                                            (* print_context; *)
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





















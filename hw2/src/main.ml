open Grammar
open Hashtbl
open Scanf
open Utils
open String
open List

let counter = ref 0

let get_new_variable x = 
  counter := !counter + 1;
  "t" ^ string_of_int !counter

let rec derap expr =
  match expr with 
  | Rap t -> derap !t
  | _ -> expr

let tt2019 a' var' b' namesHashtbl' filledSet' =
  let namesHashtbl = namesHashtbl' in
    let filledSet = filledSet' in
      let b = b' in
        let var = var' in
          let rec breduce a flag = match a with
            | Appl (t1, t2)  -> Appl (breduce t1 flag, breduce t2 flag)
            | Abst (Id x, t) -> if x == var then Abst (Id x, breduce t false) else
                                if Set.mem x filledSet then
                                    let new_name = get_new_variable x in
                                     let add_to_hashtbl = Hashtbl.add namesHashtbl x new_name in
                                      let new_tsubtree = ref nil in 
                                        add_to_hashtbl;
                                        new_tsubtree := Abst (Id new_name, breduce t flag);
                                        Hashtbl.remove namesHashtbl x;
                                        !new_tsubtree;
                                else Abst (Id x, breduce t flag)
            | Var (Id v)     -> if Hashtbl.mem namesHashtbl v then
                                  Var (Id (Hashtbl.find namesHashtbl v)) 
                                else if flag && v = var then begin (* print_string ((print_expr b) ^ "_SUB\n"); *) b end else a
            | Rap t          -> breduce !t flag
          in breduce a' true





 let rect_redex_old tree flag = 
  let wasReduction = ref false in

    let rec rect_redex tree flag = 

       if !wasReduction then begin (* print_string "kek\n"; *) tree end else match tree with
        | Var (Id v)                 -> (*  print_string "Var (Id v)\n";  *) Var (Id v)
        | Rap t                      ->  (* print_string "Rap t\n"; *) let internal = rect_redex !t flag in
                                            if !wasReduction then begin t := derap internal (* ; print_string "flag was true\n" *)  end;
                                          Rap t 
        | Abst (Id x, t)             ->  (*  print_string "Abst (Id x, t)\n";  *)  Abst (Id x, rect_redex t flag)
        | Appl (Abst(Id x, t1), t2)  ->   (* print_string "Appl (Abst(Id x, t1), t2)\n";  *) 
                                          let namesHashtbl = Hashtbl.create 128 in
                                            let filledSet = Set.union (fill_set_with_vars_from_term t2 Set.empty) (Set.singleton x) in 
                                                let new_b = ( match t2 with 
                                                                | Rap t -> let t' = derap t2 in t := t'; t
                                                                | _     -> ref t2
                                                            )
                                                in 
                                                  flag := true; 
                                                  wasReduction := true;
                                                  tt2019 t1 x (Rap new_b) namesHashtbl filledSet
        | Appl (Rap t1, t2) ->  (* print_string "Appl (Rap t1, t2)\n";  *) (
          match !t1 with
            | Abst (Id x, t) ->  (* print_string "Abst (Id x, t): "; print_string ((print_expr !t1) ^ "\n"); *) let namesHashtbl = Hashtbl.create 128 in
                                  let filledSet = Set.union (fill_set_with_vars_from_term t2 Set.empty) (Set.singleton x) in 
                                    flag := true;
                                    wasReduction := true;
                                    let new_b = ( match t2 with
                                                    | Rap t -> let t' = derap t2 in t := t'; t
                                                    | _ -> ref t2
                                                ) 
                                  in tt2019 t x (Rap new_b) namesHashtbl filledSet

            | _              -> let new_tree1 = rect_redex !t1 flag in
                                          if !wasReduction then begin (* print_string "kek\n"; *) 
                                            let new_tree1' = derap new_tree1 in t1 := new_tree1'; Appl (Rap t1, t2) end 
                                          else begin (* print_string "lul\n";  *)
                                            Appl (Rap t1, rect_redex t2 flag) end
                                )
        | Appl (t1, t2)              ->   (* print_string "Appl (t1, t2) "; * print_string (print_expr t1); print_char '\n';   *)
          let new_tree1 = rect_redex t1 flag in
              if !wasReduction then Appl(new_tree1, t2) else
                Appl (t1, rect_redex t2 flag)

        in rect_redex tree flag

let rec one_step tree n k m = 
let flag = ref true in
  if ((n mod k) = 0 || n = m) then begin
      print_string (print_expr !tree);
      print_char '\n';
      flag := false;
    end;
  if n > m then tree else
    let has_redex = ref false in
    let new_tree = rect_redex_old !tree has_redex in
    (* print_string ((print_expr tree) ^ "_____prev\n"); *)
    if !has_redex then begin tree := new_tree; one_step (tree) (n + 1) k m end else 
      if !flag then begin 
          print_string (print_expr !tree);
          print_char '\n';
          tree;
        end
      else tree
;;

let km = split_on_char ' ' (read_line()) in
  let k = match km with
  | mm :: [kk] -> int_of_string kk in
  let m = match km with
  | mm :: [kk] -> int_of_string mm in
  let input_expr = ref (Parser.main Lexer.main (Lexing.from_string (read_line()))) in
    one_step input_expr 0 k m

(* 

10 1
(\x.x x x x)((\x.x)(\x.x)) 

*)
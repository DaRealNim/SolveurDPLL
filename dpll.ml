open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
       pour chaque élément de `list', appliquer `filter' :
           - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
    let rec aux list ret =
        match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
    in aux list []

    (* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
    | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

     (* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)

exception No_unit_clause of string;;
exception No_pure_lit of string;;

(* simplifie : int -> int list list -> int list list
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)

(*let simplifie i clauses =
    let rec filter_clause clause ret =
        match clause with
        | [] -> ret
        | lit :: tail ->
                if lit = (i * -1) then
                    filter_clause tail ret
            else
                filter_clause tail (lit::ret)
     in
    let rec filter_cnf clauses ret =
        match clauses with
        | [] -> ret
        | c :: tail ->
                if List.mem i c then
                    filter_cnf tail ret
            else if List.mem (i * -1) c then
                filter_cnf tail ((filter_clause c [])::ret)
            else
                filter_cnf tail (c::ret)
in
    filter_cnf clauses []
;;*)

let simplifie i clauses =
    let filter_neg x =
        if x = (i * -1) then
        None
        else
        Some x
in
    let rec filter clauses ret =
        match clauses with
        | [] -> ret
        | c :: tail ->
                if List.mem i c then
                    filter tail ret
        else
            filter tail (c::ret)
    in
    let i_negless_clauses = List.map (List.filter_map filter_neg) clauses in
    filter i_negless_clauses []
;;


(* let rec filter ret clause =
    match clause with
    | [] -> ret
    | lit :: tail ->
            if lit = i then
                []
                else if lit = (i * -1) then
                    filter ret tail
      else
          filter (lit::ret) tail
    in
        List.map (filter []);; works but gives out empty clauses, shit. *)

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
    (* l'ensemble vide de clauses est satisfiable *)
    if clauses = [] then Some interpretation else
        (* un clause vide est insatisfiable *)
        if mem [] clauses then None else
            (* branchement *)
            let l = hd (hd clauses) in
            let branche = solveur_split (simplifie l clauses) (l::interpretation) in
            match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

  (* tests *)
  (* let () = print_modele (solveur_split systeme []) *)
  (* let () = print_modele (solveur_split coloriage []) *)

  (* solveur dpll récursif *)

  (* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
    (* à compléter *)
    match clauses with
    | [] -> raise(No_unit_clause "Pas de clause unitaire")
    | x::xs -> if (List.length x) = 1
        then
            match x with
            | x::[] -> x
            | _ -> assert(false)
        else
            unitaire xs
;;



    (* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' *)
let pur clauses =
    let rec aux remaining =
        (*tests if a specific clause contains a pure litteral*)
        let rec checkClause clause =
            (*for each litteral in the clause*)
            match clause with
                (*if no litteral left, then no pure. return nothing*)
                | [] -> None
                (*go through all the clauses of the formula again.
                  build a list containing either "None" if the clause DOESN'T contain
                  the opposite of the litteral we're testing (so it could be pure)
                  or the faulting litteral if it exists
                  so if we're testing litteral 3 in formula [[1; 2; 3]; [2; 3]; [-3; 4; 5]]
                  we would get [None; None; -3]
                  all we have to do next is check if the list is full of None. If one of the
                  element isn't None, then it isn't pure, and we test the next litteral.
                  If all the elements are None, then the litteral is pure, return it.
              *)
                | y::ys -> let res = List.map (List.find_opt (fun x -> x = -y)) clauses
                    in let found = List.find_opt (fun x -> x != None) res
                    in if found != None then (checkClause ys) else (Some y)
        in
        (*for each remaining clauses*)
        match remaining with
        | [] -> raise(No_pure_lit "Pas de littéral pur")
        (*call checkclause on the clause*)
        | x::xs -> match (checkClause x) with
            (*if checkclause returns nothing then no pure litteral was found in this clause,
            so we continue with the next one*)
            | None -> (aux xs)
            (*else, then a pure litteral was found, return it*)
            | Some y -> y
    in
    aux clauses
;;


    (* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
		match clauses with
		| [] -> Some interpretation
		| c :: tail ->
			try
                let u = unitaire clauses in
				solveur_dpll_rec (simplifie u clauses) (u::interpretation)
			with No_unit_clause "Pas de clause unitaire" ->
                try
                    let p = pur clauses in
					solveur_dpll_rec (simplifie p clauses) (p::interpretation)
				with No_pure_lit "Pas de littéral pur" ->
                    try
                        (* On peut reprendre le code de solveur split, puisque celui ci sert a bifurquer sur
                        deux branches avec une interpretation du littéral vraie et une fausse, ce qui est
                        précisement ce qu'on doit faire à ce point de l'algorithme dpll*)
                        let l = hd c in
                        let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
                        match branche with
                        | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
                        | _    -> branche
                    with Failure _ -> None
                    (* try *)
    					(* let x = List.hd c in
    					solveur_dpll_rec (simplifie x clauses) (x::interpretation) *)
                    (* with Failure "hd" -> solveur_dpll_rec tail interpretation *)
;;


    (* tests *)
    (* let () = print_modele (solveur_dpll_rec systeme []) *)
    (* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
    let clauses = Dimacs.parse Sys.argv.(1) in
    print_modele (solveur_dpll_rec clauses [])

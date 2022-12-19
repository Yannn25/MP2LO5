open Printf

(* Définitions de terme, test et programme *)
type term = 
 | Const of int
 | Var of int
 | Add of term * term
 | Mult of term * term

type test = 
 | Equals of term * term
 | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string` 
   et `str_of_test : test -> string` qui convertissent des termes 
   et des tests en chaînes de caractères du format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
let rec str_of_term t =  
  match t with
  (*Pour les 'types' const et var on va tout simplement les convertir en String *)
  | Const c -> string_of_int c
  | Var v -> (x v)
  (*Sinon pour les types Add et Mult on va juste faire un appel recursive sur ses deux termes*)
  | Add (a, b) -> "(+ " ^str_of_term a ^" "^ str_of_term b^")" 
  | Mult (a, b) -> "(* " ^str_of_term a ^" "^ str_of_term b^")"


let str_of_test t = 
  match t with
  (*Pour notre fonction str_of_test on ce servira principalment de la fonction str_of_term*)
  | Equals (a, b) -> "(= " ^str_of_term a ^" "^ str_of_term b^")"
  | LessThan (a, b) -> "(< " ^str_of_term a ^" "^ str_of_term b^")"


let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne 
   de caractères qui exprime que le tuple (t1, ..., tk) est dans 
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne 
   "(Inv x1 10)".
   *)
let str_condition l = 
  (*on définie une fonction auxiliaire récursive qui va parcourir l'ensemble
    de notre list puis lancer notre fonction str_of_term sur chacun des termes*)
  let rec aux ll acc = 
    match ll with
    | [] -> acc ^ ")"
    | x :: sl -> aux sl (acc ^ " " ^ str_of_term x)
  in aux l "(Invar "  


(* Question 3. Écrire une fonction 
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".

  Par exemple, str_assert_forall 2 "< x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (< x1 x2)))".  *)

let str_assert s = "(assert " ^ s ^ ")"

let str_assert_forall n s = 
  let tmp = n in    (*Copie temporaire de notre variable n*)
    let make_x n = (*Fonction qui permet l'affichage de xn Int sur toutes les variables de s*)
    (*fonction récursive qui se charge d'appliquer le 'make_x'*)
      let rec boucle acc numb = 
        match numb with
        | 0 -> acc
        | numb -> 
          (*Dans le 1er cas on est sur la dernière variable a afficher
            Or que dans le second on est dans le cas par 'défaut' *)
            if numb = tmp then 
              boucle ( "("^ (x numb) ^ " Int)" ^ acc) (numb-1)
            else boucle ( "("^ (x numb) ^ " Int) " ^ acc) (numb-1)
      in 
        boucle "" n 
    in
      str_assert ( "(forall (" ^ make_x n ^")" ^ " (" ^ s ^ "))" )

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)

let smtlib_of_wa p = 

  (* fonction qui permet de vérifier la validité d'une condition*)
  let check_condition t = 
    match t with
    | Equals (a, b) -> a, b
    | LessThan (a, b) -> a, b in

  (* fonction qui permet de d'obtenir une liste contenant tous les termes allant jusqu'a n*)  
  let get_terms n =
    let rec boucle acc numb = 
      match numb with 
      | 0 -> acc 
      | _ -> boucle ( (Var numb) :: acc ) ( numb-1 )
    in boucle [] n in

  let declare_invariant n =
    "; synthèse d'invariant de programme\n"
    ^"; on déclare le symbole non interprété de relation Invar\n"
    ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in

  let loop_condition p =
    let list_to_str (list: term list): string = (*Transforme l'ensemble de notre liste de
      terme en une chaine de caractère avec une boucle recursive comme vu précédement*) 
      let rec boucle l acc = 
        match l with 
        | [] -> acc
        | x :: sl -> boucle sl (acc ^ str_of_term x)
      in boucle list ""
    in
    str_assert_forall p.nvars ("=> (and "
                              ^str_condition (get_terms p.nvars) (*la chaine des conditions*)
                               ^" "
                               ^""^
                               str_of_test(p.loopcond) (*la chaine des tests*)
                               ^") (Invar "^list_to_str p.mods
                               ^ ")") in
  let initial_condition p =
    "; la relation Invar est vraie initialement\n"
    ^str_assert (str_condition p.inits) in
  let assertion_condition p =
    let check = check_condition p.loopcond in (**)
    "; l'assertion finale est vérifiée\n"
      ^str_assert_forall p.nvars ("=> (and "
                                  ^str_condition (get_terms p.nvars) (* identique  *)
                                  ^" "
                                  ^"(>= "^
                                  str_of_term(fst(check)) (* fst renvoi le premier élement de notre check*)
                                  ^" "^str_of_term(snd(check))^")" (* tandis que snd renvoi le second élement de notre check*)
                                  ^""
                                  ^ ") "^str_of_test(p.assertion)) in
  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]


(*
    int i = 0;
    int v = 0;
    while (i < 3) {
      v = v + 3;
      i = i + 1;
    }
    assert v == 9;

*)

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}




(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)

   let p2 = (*Nous allons implémenter le programme JAVA suivant :
                  int i = 0;
                  int j = 1;
                  while( i < 10) {
                    i += 2;
                    j += 1;
                  } 
                  assert( j < 10) *)

  { nvars = 2;
    inits = [(Const 0) ; (Const 1)];
    mods = [Add ((Var 1), (Const 2)); Add ((Var 2), (Const 1))];
    loopcond = LessThan ((Var 1),(Const 10));
    assertion = LessThan ((Var 2),(Const 10)) }                  


let () = Printf.printf "%s\n\n\n%s" (smtlib_of_wa p1) (smtlib_of_wa p2)
(* Chirag Bansal 2018CS50402 *)


(* Exceptions *)

exception VariableNotFound
exception InvalidTerm
exception SymbolNotPresent
exception NotUnifiable

(* Type Definations *)

type symbol = string;;

type variable = string;;

type arity = int;;

type term = V of variable | Node of symbol * (term list);;

type lookup_table = (variable * int) list;;

type func = (symbol * arity);;

type signature = func list;;

type sub = (term * term);;

type substitution = sub list ;;

(* Give the vriable and value of item which is a variable,value tuple *)

let variableOfitem (item: variable * int): variable = match item with
	(variable,int) -> variable;;

let valueOfitem (item: variable * int): int = match item with
	(variable,int) -> int;;

(* This returns the arity of a func (or symbol) *)

let arity_of_function (f:func) : arity = match f with
	(symbol,arity) -> arity ;;

(* This returns the symbol from a func *)

let symbol_of_function (f: func) : symbol = match f with
	(symbol,arity) -> symbol;;

(* This given a signature checks whether the func exitsts or not , it also checks if the name i.e. symbol matches as well *)

let rec exist (elem:func) (lst:signature):bool = match lst with
  | [] -> false
  | hd::tl -> (elem = hd) || ((symbol_of_function elem) = (symbol_of_function hd)) || (exist elem tl);;


(* This checks if there are any duplicates in the signature *)

let rec dupExist (lst:signature):bool = match lst with
  | [] -> false
  | hd::tl -> (exist hd tl) || (dupExist tl);;

(* Checks whether the signature is correct or not *)

let rec check_sig (s:signature):bool = match s with
	| [] -> true
	| (x::xs) -> if (((arity_of_function x) < 0)) then false else if (dupExist s) then false else (check_sig xs);;

(* This returns the value of the variable from the look up table *)

let rec rho (v: variable) (tbl:lookup_table) : int = match tbl with
	| [] -> raise VariableNotFound
	| x::xs ->  if((variableOfitem x) == v) then (valueOfitem x) else (rho v xs);;

(* Given a lookup table of variables this *)

let rec inTable (v: variable) (tbl:lookup_table) : bool = match tbl with
	| [] -> false
	| x::xs ->  if((variableOfitem x) == v) then true else (inTable v xs);;

(* This tells whether the given symbol exits or not *)

let rec exist_symbol (sys: symbol) (lst:signature):bool = match lst with
  | [] -> false
  | hd::tl -> (sys = (symbol_of_function hd)) || (exist_symbol sys tl);;

(* Returns the arity of a symbol from the signature, signature is a list of func which is (symbol,arity) 

Note: There must be only one symbol with the same name*)

let rec arity_of_symbol (sym:symbol) (sign :signature) : arity = match sign with
	[] -> raise SymbolNotPresent
	| (x::xs) -> if ((symbol_of_function x) = sym) then (arity_of_function x) else (arity_of_symbol sym xs);;

(* Tells whether the term is well formed or not *)

let rec wfterm (t:term) (s:signature) : bool = match t with
	| V (variable) -> true
	| Node (symbol , term_list) -> (exist_symbol symbol s) && ((arity_of_symbol symbol s) = (List.length term_list));;


(* If there is a function that gives an int from a term it applies it to a term list *)

let rec map_to_int (f: term -> int) (term_list: term list) : int list = match term_list with
	[] -> []
	| (x::xs) -> (f x) :: (map_to_int f xs);;

(* This calculates the max int from an int list *)

let my_max (lis:int list) : int = match lis with
    [] -> 0
    | x::xs -> List.fold_left max x xs;;

(* Returns the height of the term(actually tree) *)

let rec ht (t:term) :int = match t with
	| V (variable) -> 1
	| Node (symbol,term_list) -> 1 + my_max (map_to_int ht term_list);;

(* This returns list of all the variables in the term *)

let rec vars (t: term) : variable list = 
	
	let rec map_to_variable (term_list: term list) : variable list = match term_list with
	[] -> []
	| (x::xs) -> (vars x) @ (map_to_variable xs) in

	match t with
		| V (variable) -> variable::[]
		| Node (symbol,term_list) -> (map_to_variable term_list);;

(* Tels if a variable exists in a variable list *)

let rec var_exist (v:variable) (var_list:variable list):bool = match var_list with
	| [] -> false
	| (x::xs) -> if(v = x) then true else (var_exist v xs);;

(* Finds the sum of an integer list *)

let rec sum (l:int list): int = match l with 
   [] -> 0 
  | hd::tl -> hd + (sum tl);;

(* This finds the size of the term *)

let rec size (t:term): int = match t with
	| V(variable) -> 1
	| Node(symbol,term_list) -> 1 + sum (map_to_int size term_list);;

(* Give the terms of a sub *)

let get_term (s:sub):term = match s with
	(term1,term2) -> term2;;

let get_term_initial (s:sub):term = match s with
	(term1,term2) -> term1;;

(* Given a term and substitution this returns theterm that will substitute it if it exists that is *)

let rec get_subst (t :term) (s:substitution): term = match s with
	[] -> t
	| (x::xs) -> if (t = (get_term_initial x)) then (get_term x) else (get_subst t xs);;

(* This substitutes the term with the term in the substitution, there is a helper function inside it that does the same for lists *)

let rec subst (t: term) (s: substitution): term = 

	let rec subst_list (term_list: term list) (s:substitution) : term list = match term_list with
	[] -> []
	| (x::xs) -> (subst x s)::(subst_list xs s) in

	match t with
	| V(variable) -> (get_subst (V(variable)) s)
	| Node(symbol,term_list) -> Node(symbol, (subst_list term_list s));;

(* Tells if there is a match of the term in the substitution *)

let rec match_exits (t:term) (s:substitution):bool = match s with
	| [] -> false
	| (x::xs) -> if (t = get_term_initial x) then true else (match_exits t xs);;

(* This function gives all the substitutions from tehe first substitution that did not get matched i.e. substituted agin *)
 
let rec get_unmatched_substituttion (s1:substitution) (s2:substitution) : substitution = match s1 with
	| [] -> []
	| (x::xs) -> if(match_exits (get_term x) s2) then (get_unmatched_substituttion xs s2) else x::(get_unmatched_substituttion xs s2);;

let return_sub (t1:term) (t2:term) : sub = (t1,t2);; 

(* This function gives all the substitutions from tehe first substitution that did get matched i.e. substituted agin *)

let rec get_matched_substitution (s1:substitution) (s2:substitution): substitution = match s1 with
	| [] -> []
	| (x::xs) -> if(match_exits (get_term x) s2) then (return_sub (get_term_initial x) (get_subst (get_term x) s2))::(get_matched_substitution xs s2) else (get_matched_substitution xs s2);;

(* This function tells whether there us a sub present in the substitution *)

let rec sub_present (s:sub) (subs:substitution):bool = match subs with
	| [] -> false
	| (x::xs) -> if(x = s) then true else (sub_present s xs);;

(* This appends two substitutions, if they don't have common terms *)

let rec append_substitution (s1:substitution) (s2:substitution):substitution = match s2 with
	|[] -> s1
	|(x::xs) -> if (sub_present x s1) then (append_substitution s1 xs) else x::(append_substitution s1 xs);;

(* The final composition function *)

let composition_of_substitution (s1:substitution) (s2:substitution) : substitution = append_substitution ((get_matched_substitution s1 s2)@(get_matched_substitution s1 s2)) s2;;


(* This calculates the most general unifier, there are thre cases where it shows an error, if the symbols are different in the node, if their list has different
length (if the term is not well formed) and if there is an infinite loop,in rest cases it creates a substitution containg the term*term list *)

let rec mgu (t1:term) (t2:term): substitution = 

	let rec mgu_list (t1:term list) (t2:term list): substitution = match (t1,t2) with
	| (x::xs,y::ys) -> composition_of_substitution (mgu x y) (mgu_list xs ys)
	| ([],[]) -> []
	| ([],x::xs) -> raise NotUnifiable
	| (x::xs,[]) -> raise NotUnifiable in

	match (t1,t2) with
    (Node(x,list1),Node(y,list2)) -> if (x <> y) || ((List.length list1) <> (List.length list2)) then raise NotUnifiable
    								else (mgu_list list1 list2)
    | (V(x),V(y)) -> ((return_sub t1 t2)::[])
	| (Node(sym,lst),V(x)) -> if(var_exist x (vars (Node(sym,lst)))) then raise NotUnifiable else ((return_sub t1 t2)::[])
	| (V(x),Node(sym,lst)) -> if(var_exist x (vars (Node(sym,lst)))) then raise NotUnifiable else ((return_sub t1 t2)::[]);;

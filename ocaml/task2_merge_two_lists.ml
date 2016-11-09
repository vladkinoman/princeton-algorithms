(*
*  [title]: Lab #2, variant-1, "Merging two lists"
* [author]: Beklenyshchev Vladislav, PK-12-2, DNU
*)

(********** !!general function and exception for both parts of work!! *********)

let compare a1 a2 = 
	if a1 <= a2 then true
	else false
;;

(* raised in merge and merge_structures*)
exception Different_orders;;

(*************************** FIRST part of work *******************************)
(*
* [description]: 
*		merge lists lx and ly in one list using increasing order
* [arguments]:
* 		lx - 1st list 
* 		ly - 2nd list
* [return value]: 
*		new list of combined lx and ly
*)
let rec merge_i lx ly =
	match lx with
	| [] -> ly
	| head_x::tail_x ->
		match ly with
		| [] -> lx
		| head_y::tail_y ->
			if head_x <= head_y then
				head_x::(merge_i tail_x ly)
			else head_y::(merge_i tail_y lx)
;;

(*
* [description]: 
*		this function find order of list l
* [arguments]:
*		compare_func - function which compare values of type 'a
* 		l - list
* [return value]: 
*		true  -> increasing order
*		false -> decreasing order
[hint]: 
*		function is called only by <merge> function!
*)
let rec find_list_order compare_func l =
	match l with
	| [] -> true
	| head::tail ->
		match tail with
		| [] -> true
		| headnext::tailnext ->
			if compare_func head headnext then
				find_list_order compare_func tail
			else false
;;

(*
* [description]: 
*		function merge lists lx and ly
* [arguments]:
* 		compare_func - function which compare values of type 'a
* 		sort_order 	 - required order of sorting with next values:
*					true  -> increasing order
*					false -> decreasing order
*		lx - fst list
*		ly - snd list
* [return value]: 
*		 new list as a result of merged lx and ly
* [hint]: 
*		function is called by <merge> and <merge_structures> functions!
*)
let rec merge_lists compare_func sort_order lx ly =
				match lx with
				| [] -> ly
				| head_x::tail_x ->
					match ly with
					| [] -> lx
					| head_y::tail_y ->
						if (sort_order == true) then
							if (compare_func head_x head_y) then
								head_x::(merge_lists compare_func sort_order tail_x ly)
							else head_y::(merge_lists compare_func sort_order lx tail_y)
						else
							if (compare_func head_x head_y) then
								head_y::(merge_lists compare_func sort_order lx tail_y)
							else head_x::(merge_lists compare_func sort_order tail_x ly)
;;


(*
* [description]: 
*		function find order of lists lx and ly and merge them
* [arguments]:
* 		compare_func - function for comparing items from lx and ly lists
*		lx - fst list
*		ly - snd list
* [return value]: 
*		new list as a result of merged lx and ly
*)
let merge compare_func lx ly =
	let order_lx = (find_list_order compare_func lx)
	and order_ly = (find_list_order compare_func ly) in
		if (order_lx == order_ly) then
			merge_lists compare_func order_lx lx ly
		else raise Different_orders  
;;

(************************ SECOND part of work ************************************)

type 'a list_t = 
{
	list_item: 'a list;
	func: 'a -> 'a -> bool;
 	order: bool;
};;

(*
* [description]: 
*		function added x item to l 'a list
* [arguments]:
* 		compare_func - function which compare values of type 'a
* 		sort_order 	 - required order of sorting with next values:
*					true  -> increasing order
*					false -> decreasing order
*		l - list for insertion
*		x - item 
* [return value]: 
*		sorted record of type list_t
* [hint]: 
*		function is called by <insert> and <sort> functions!
*)
let rec insert_item compare_func sort_order l x =
			match l with
			| [] -> [x]
			| head::tail ->
				if sort_order then
					(* increasing order*)
					if compare_func x head then 
						x::(head::tail)
					else head::(insert_item compare_func sort_order tail x)
				else  
					(* decreasing order*)
					if compare_func x head then 
						head::(insert_item compare_func sort_order tail x)
					else x::(head::tail)
;;

(*
* [description]: 
*		function added x item to list_struct of type list_t
* [arguments]:
*		list_struct - list record of type list_t
*		x - item to add in list_item of current list_struct
* [return value]: 
*		new list_struct of type list_t with inserted x
*)
let insert list_struct x =
{
	list_item = 
		insert_item list_struct.func list_struct.order list_struct.list_item x;
	func = list_struct.func;
	order = list_struct.order;
};;

(*
* [description]: 
*		function sort current list_t in specified order
* [arguments]:
*		compare_func - function which compare values of type 'a
* 		sort_order   - required order of sorting with next values:
*				true  -> increasing order
*				false -> decreasing order
* 		list_struct  - record of type list_t
* [return value]: 
*		sorted record of type list_t
*)
let sort compare_func sort_order list_struct =
{
	list_item = 
	(	
		let rec insertion_sort l =
		 match l with
		 | [] -> []
		 | head::tail -> 
		 	insert_item compare_func sort_order (insertion_sort tail) head
		in insertion_sort list_struct.list_item;
	);	
	func = compare_func;
	order = sort_order;
};;

(*
* [description]: 
*		merge two list_item lists in one new list_item and formes
*		new record of type list_t 
* [arguments]:
* 		lstruct_x - fst record of type list_t 
* 		lstruct_y - snd record of type list_t
* [return value]: 
*		record of type list_t
*)
let merge_structures lstruct_x lstruct_y =
{
	list_item =
		if (lstruct_x.order == lstruct_y.order) then
			merge_lists lstruct_x.func lstruct_x.order lstruct_x.list_item lstruct_y.list_item
		else raise Different_orders
	;	
	func = lstruct_x.func;
	order = lstruct_x.order;
};;

(************************ TESTS for part #1 ***************************)

let l1 = [1;2;5;8];;
let l2 = [4;6];;
let l3 = [7;4;1];;
let l4 = [8;6;4;3];;
let s1 = ["Vlad"; "Tanya"; "Anya"];;
let s2 = ["Vlad";"Ruslan";"Nastya"];;
let s3 = ["Vlad"; "Vaad"; "Anya"];;
let s4 = ["Vlad"; "Vanya";"Vaad"];;

(************************ TESTS for part #2 ***************************)

(*example for increasing order*)
let list_struct1 = 
{
	list_item = [1;3;6];
	func = compare;
	order = true;
};;

let list_struct2 = 
{
	list_item = [2;8;9;10;56];
	func = compare;
	order = true;
};;

(*example for decreasing order*)
let list_struct3 = 
{
	list_item = [7;4;1];
	func = compare;
	order = false;
};;

let list_struct4 = 
{
	list_item = [100;29;17;3;1];
	func = compare;
	order = false;
};;
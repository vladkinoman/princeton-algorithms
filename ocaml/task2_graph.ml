type 'a graph = ('a * 'a list) list;;

(* примеры задания различных графов*)
let (gr_int: int graph) = [(1, [2; 3]); (2, []); (3, [4; 5]); (4, []); (5, [])];;
let (gr_to_zero: int graph) = [(0, []); (1,[0]);(2,[0]);(3,[0]);(4,[0]);(5,[0])];;
let (gr_string : string graph) = [("qw1", ["qw2"]); ("qw2", ["qw3"]); ("qw3", [])];;
let (gr_float : float graph) = [(1.2, [2.3]); (2.3, [3.4]); (3.4, [])];;
let (gr_char : char graph) = [('a', ['b']); ('b', ['c']); ('c', [])];;

(* не совсем корректные варианты как по мне, но тоже работающие *)
(* недостатком в них вижу отсутсвие пустых списков смежности у других вершин
let (g1: int graph)  = [(1, [2; 3]); (3, [4; 5])];;
let (g2: int graph) = [(1, [7; 3; 4]); (3, [4; 5])];;
*)

(* проверяем есть ли элемент item в списке смежности кортежа vtx_tuple  *)
let rec is_exist (vtx_tuple: 'a * 'a list) (item: 'a) =
	match vtx_tuple with
	| (_, []) -> false
	| (vtx_curr, head::tail) ->
		match head = item with
		| true -> true
		| false -> is_exist (vtx_curr, tail) item
;;

let rec insert_vtx (g: 'a graph) (vtx: 'a) =
	match g with
	| [] -> [(vtx,[])]
	| g_head::g_tail -> 
		match g_head with
		| (vtx_curr,_) when vtx_curr = vtx -> g
		| _ -> g_head::(insert_vtx g_tail vtx)
;;

let insert_edge (g: 'a graph) (vtx_from: 'a) (vtx_to: 'a) =
 	let rec rec_insert_edge g vtx_from vtx_to =
 		match g with
 		| [] ->
 			(rec_insert_edge (insert_vtx g vtx_from) vtx_from vtx_to)
 		| g_head::g_tail -> 
  			match g_head with
  			| (vtx_curr, adj_list) when (vtx_curr = vtx_from) ->
  				if is_exist (vtx_curr, adj_list) vtx_to then g
  				else (vtx_curr, vtx_to::adj_list)::g_tail
  			|_ ->
    			g_head::(rec_insert_edge g_tail vtx_from vtx_to)
 	in insert_vtx(rec_insert_edge g vtx_from vtx_to) vtx_to
;;

let rec has_edges_to (g: 'a graph) (vtx: 'a) =
	match g with
	| [] -> []
	| g_head::g_tail -> 
		match g_head with
		| (vtx_curr, adj_list) when vtx_curr = vtx -> adj_list
		| _ -> has_edges_to g_tail vtx
;;

let rec has_edges_from (g: 'a graph) (vtx: 'a) =
	match g with
	| [] -> []
	| g_head::g_tail ->
		match g_head with
		| (vtx_curr, adj_list) when (is_exist (vtx_curr, adj_list) vtx) ->
			vtx_curr::(has_edges_from g_tail vtx)
		| _ -> has_edges_from g_tail vtx
;;
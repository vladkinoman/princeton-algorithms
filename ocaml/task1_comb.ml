open Printf

let rec get_data x i =
	if i < (Array.length Sys.argv - 1) 
		then get_data (((int_of_string Sys.argv.(i)),(int_of_string Sys.argv.(i + 1)))::x) (i+2)
	else x
;;

let print_input_data =
	let i = ref 1 in
	printf "input: [";
	while !i<(Array.length Sys.argv - 1) do
		printf "(%i, %i);" (int_of_string Sys.argv.(!i)) (int_of_string Sys.argv.(!i+1));
		i := !i + 2
	done;
	printf "]\n";
;;

let rev list =
    let rec aux acc = function
      | [] -> acc
      | h::t -> aux (h::acc) t in
    aux [] list
;;

(* reverse for get original view (as in input) *)
let list_of_tuples = rev (get_data [] 1);;
(*.................. main solution ......................*)

let rec fact x =
	if x <= 1 then 1
	else x * fact (x-1)
;;

let comb n m =
	if n == m then 1
	else if n > m then (fact n) / ((fact m) * (fact (n - m)))
	else (fact m) / ((fact n) * (fact (m - n)))
;;

let rec combine xlist =
	match xlist with
	| [] -> []
	| (c1,c2)::xtail ->
		begin let c_res = (comb c1 c2) in
		c_res::(combine xtail);
		end
;;

(* combine our list with empty list *)
let result_l = 
	combine list_of_tuples
;;
	
(*................. end of main solution ..................*)

let print_results = 
		printf "output: [";
		List.iter (printf "%i;") result_l;
		printf "]\n";
;;

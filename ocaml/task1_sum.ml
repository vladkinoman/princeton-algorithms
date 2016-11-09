open Printf

let sum a b =
(a + b);;

let () = 
		printf "%i\n" (sum (int_of_string Sys.argv.(1)) (int_of_string Sys.argv.(2)))
		;;

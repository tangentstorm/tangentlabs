(* to actually run it, do this:

   ocamlmktop -o ocaml-graphics.exe graphics.cma
   ocaml-graphics grtest2.ml

*)

Random.self_init ();;
Graphics.open_graph "640x480";;

let rec iterate r x_init i =
  if i = 1 then x_init
  else
    let x = iterate r x_init (i-1) in
      r *. x *.(1.0 -. x)
;;

for x = 0 to 639 do
  let r = 4.0 *. (float x) /. 640.0 in
    for i = 0 to 39 do
      let x_init = Random.float 1.0 in
      let x_final = iterate r x_init 500 in 
      let y = int_of_float (x_final *. 480.) in
	Graphics.plot x y
    done
done;;

read_line();;

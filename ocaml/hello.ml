

(* this was going to be hello world in OCaml 
 * but instead it's junk from here:
 * http://www.ocaml-tutorial.org/
 *)

let average a b =
  a +. b /. 2.0;;

let average a b =
  let sum = a +. b in
    sum /. 2.0;;

let f a b =
  (a +. b) +. (a +. b) ** 2.0
;;

let f a b =
  let x = a +. b in
    x +. x ** 2.0
;;

let my_ref = ref 0;;

type foo = 
    Nothing 
  | Int of int
  | Pair of int * int
  | String of string
;;

let foo1 = Nothing
let foo2 = Int 3
let foo3 = Pair (4, 5)
let foo4 = String "hello world"


type expr = 
    Plus of expr * expr
  | Minus of expr * expr
  | Times of expr * expr
  | Divide of expr * expr
  | Value of string 
;;

let rec to_string e =
  match e with
      Plus (left, right) -> "(" ^ (to_string left) ^ " + " ^ (to_string right) ^ ")"
    | Minus (left, right)  -> "(" ^ (to_string left) ^ " - " ^ (to_string right) ^ ")"
    | Times (left, right)  -> "(" ^ (to_string left) ^ " * " ^ (to_string right) ^ ")"
    | Divide (left, right) -> "(" ^ (to_string left) ^ " / " ^ (to_string right) ^ ")"
    | Value v -> v
;;

let print_expr e =
  print_endline (to_string e);;

let arity1 a =
  "arity 1"

let arity2 a b =
  "arity 2"

type lock_bad = Open | Close;;
type door_bad = Open | Close;;

type lock = [ `Open | `Closed ];;
type door = [ `Open | `Closed ];;

let print_lock st =
  match st with
      `Open -> print_endline "The lock is open"
    | `Closed -> print_endline "The lock is closed"
;;


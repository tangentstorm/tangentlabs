(* BASIC interpreter from http://caml.inria.fr/pub/docs/oreilly-book/html/book-ora058.html *)

(* abstract syntax **************************************************)

type unaOp = UMINUS | NOT ;;
type binOp = PLUS | MINUS | MULT | DIV | MOD | EQ | LT | LE | GT | GE | DIFF | AND | OR ;;
type expr = 
    ExpInt of int
  | ExpVar of string
  | ExpStr of string
  | ExpUnr of unaOp * expr
  | ExpBin of expr * binOp * expr
;;
type command =
    Rem of string
  | Goto of int
  | Print of expr
  | Input of string
  | If of expr * int
  | Let of string * expr
;;
type line = { num : int ; cmd : command } ;;
type program = line list ;;
type phrase = Line of line | List | Run | PEnd ;;

let priority_una = function NOT -> 1 | UMINUS -> 7
let priority_bin = function
    MULT | DIV -> 6
  | PLUS | MINUS -> 5
  | MOD -> 4
  | EQ | LT | LE | GT | GE | DIFF -> 3
  | AND | OR -> 2 
;;


(* pretty printing **************************************************)

let pp_bin = function
    PLUS -> "+" | MINUS -> "-"  | MULT -> "*"  | DIV -> "/" | MOD -> "%"
  | EQ -> "="  | LT -> "<"  | GT -> ">" | LE -> "<=" | GE -> ">=" | DIFF -> "<>" 
  | AND -> "&" | OR -> "|" ;;

let pp_una = function UMINUS -> "-" | NOT -> "!" ;;

let paren x = "(" ^ x ^ ")" ;;

let pp_expr =
  (* pretty print left side of expression *)
  let rec ppl pri = function
      ExpInt n -> (string_of_int n)
    | ExpVar v -> v
    | ExpStr s -> "\"" ^ s ^ "\""
    | ExpUnr (op, e) ->
	let res = (pp_una op) ^ (ppl (priority_una op) e)
	in if pri=0 then res else paren res
    | ExpBin (e1, op, e2) ->
	let pr2 = priority_bin op
	in let res = (ppl pr2 e1) ^ (pp_bin op) ^ (ppr pr2 e2)
	in if pr2 >= pri then res else paren res
  and ppr pri exp = match exp with
  (* pretty print right side of expression.
     the only difference is the > vs >=  *)
      ExpBin (e1, op, e2) ->
	let pr2 = priority_bin op
	in let res = (ppl pr2 e1) ^ (pp_bin op) ^ (ppr pr2 e2)
	in if pr2 > pri then res else paren res
    | _ -> ppl pri exp
  in ppl 0
;;

let pp_command = function
    Rem s -> "REM " ^ s
  | Goto n -> "GOTO " ^ (string_of_int n)
  | Print e -> "PRINT " ^ (pp_expr e)
  | Input v -> "INPUT " ^ v
  | If (e, n) -> "IF " ^ (pp_expr e) ^ " THEN " ^ (string_of_int n)
  | Let (v, e) -> "LET " ^ v ^ " = " ^ (pp_expr e) 
;;

let pp_line l = (string_of_int l.num) ^ "  " ^ (pp_command l.cmd) ;;


(* lexer ************************************************************)

type lexeme =
    LInt of int
  | LIdent of string
  | LSymbol of string
  | LString of string
  | LEnd ;;

type string_lexer = { string:string; mutable current:int; size:int } ;;

let init_lex s = { string=s; current=0; size=String.length s } ;;

let forward cl = cl.current <- cl.current + 1 ;;
let forward_n cl n = cl.current <- cl.current + n ;;
let extract pred cl = 
  let st = cl.string and pos = cl.current in
  let rec ext n = if n < cl.size && (pred st.[n]) then ext (n+1) else n in
  let res = ext pos in
    cl.current <- res ; 
    String.sub cl.string pos (res-pos)
;;

let extract_int = 
  let is_int = function '0' .. '9' -> true | _ -> false
  in function cl -> int_of_string (extract is_int cl)
;;

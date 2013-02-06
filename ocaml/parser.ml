(* full parser tutorial from http://brion.inria.fr/gallium/index.php/Full_parser_tutorial *)


open Camlp4.PreCast ;;

(* AST *)

type 'loc expr = 
  | Var of string * 'loc 
  | String of string * 'loc ;;
 
type 'loc stmt =
  | Def of string * 'loc expr * 'loc
  | Print of 'loc expr list * 'loc ;;


(* Translation *)

let expr_of_expr = function
  | Var (v, _loc) -> <:expr< $lid:v$ >>
  | String (s, _loc) -> <:expr< $str:s$ >> ;;

let concat_exprs _loc = function
  | [] -> failwith "concat_exprs"
  | e::es -> List.fold_left (fun e e' -> <:expr< $e$ ^ " " ^ $e'$  >>) e es ;;

let str_item_of_stmt = function
  | Def (v, e, _loc) -> <:str_item< let $lid:v$ = $expr_of_expr e$ ;; >>
  | Print (es, _loc) -> 
      let es = List.map expr_of_expr es in
	<:str_item< print_endline $concat_exprs _loc es$ ;; >> ;;


(* Parser *)
let expr = Gram.Entry.mk "expr" ;;
let stmt = Gram.Entry.mk "stmt" ;;

EXTEND Gram
expr: [
  [ v = LIDENT -> Var (v, _loc)
  | s = STRING -> String (s, _loc) ]];
stmt: [
  [ "def"; v = LIDENT; "="; e = expr -> Def (v, e, _loc)
  | "print"; es = LIST1 expr SEP "," -> Print (es, _loc) ]];
END ;;

Gram.Entry.clear Syntax.str_item ;;
EXTEND Gram
  Syntax.str_item : [ [ s = stmt -> str_item_of_stmt s ] ];
END ;;


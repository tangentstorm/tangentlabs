theory CartoucheDemo
  imports Main
begin
ML {*
(* test_parser is just a definition of a silly example parser. It parses text of the form "123 * \<open>x+y\<close>"
   where 123 is an arbitrary natural, and x+y a term. test_parser is of type term context_parser.
   The parser returns a term that is a list 123 copies of x+y.
   If you have constructed a "term parser" instead, you can either convert it using Scan.lift, 
   or modify the definition of parse_cartouche below slightly. 
 *)
fun sym_parser sym = Parse.sym_ident
      :-- (fn s => if s=sym then Scan.succeed () else Scan.fail) >> #1;

val test_parser = Scan.lift Parse.nat
  --| Scan.lift (sym_parser "*" || Parse.reserved "x")
  -- Args.term
  >> (fn (n,t) => replicate n t |> HOLogic.mk_list dummyT)

(* parse_cartouche: This function takes the cartouche that should be parsed (as a plain string
   without markup), together with its position. (All this information can be extracted using the 
   information available to a parse translation, see cartouch_tr below.) *)
fun parse_cartouche ctx (cartouche:string) (pos:Position.T) : term = 
  let 
    (* This extracts the content of the cartouche as a "Symbol_Pos.T list".
       One posibility to continue from here would be to write a parser that works
       on "Symbol_Pos.T list". However, most of the predefined parsers expect 
       "Token.T list" (a single token may consist of several symbols, e.g., 123 is one token). *)
    val content = Symbol_Pos.cartouche_content (Symbol_Pos.explode (cartouche, pos))

    (* Translate content into a "Token.T list". *)
    val toks = content |> Source.of_list (* Create a "Source.source" containing the symbols *)

    val toks = toks
      |> Token.tokenize Keyword.empty_keywords  {strict = true}
      |> Source.exhaust (* Translate the source into a list of tokens *)
      |> (fn src => src @ [Token.eof]) (* Add an eof to the end of the token list, to enable Parse.eof below *)
    (* A conversion function that produces error messages. The ignored argument here
       contains the context and the list of remaining tokens, if needed for constructing
       the message. *)

    fun errmsg (_,SOME msg) = msg
      | errmsg (_,NONE) = fn _ => "Syntax error"
    (* Apply the parser "test_parser". We additionally combine it with Parse.eof to ensure that 
       the parser parses the whole text (till EOF). And we use Scan.!! to convert parsing failures 
       into parsing errors, and Scan.error to report parsing errors to the toplevel. *)
    val (term,_) = Scan.error (Scan.!! errmsg (test_parser --| Scan.lift Parse.eof)) (Context.Proof ctx,toks)
in term end


(* A parse translation that translates cartouches using test_parser. The code is very close to 
   the examples from Cartouche_Examples.thy. It takes a given cartouche-subterm, gets its 
   position, and calls parse_cartouche to do the translation to a term. *)
fun cartouche_tr (ctx:Proof.context) args =
    let fun err () = raise TERM ("cartouche_tr", args) in
      (case args of
        [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => c $ (parse_cartouche ctx s pos) $ p
          | NONE => err ())
      | _ => err ())
    end;
*}

(* Define a syntax for calling our translation. In this case, the syntax is "MY \<open>to-be-parsed\<close>" *)
syntax "_my_syntax" :: "cartouche_position \<Rightarrow> 'a" ("MY_")
(* Binds our parse translation to that syntax. *)
parse_translation \<open>[(@{syntax_const "_my_syntax"}, cartouche_tr)]\<close>

term "(MY \<open>3 * \<open>b+c\<close>\<close>, 2)" (* Should parse as ([b+c,b+c,b+c],2) *)
term "(MY \<open>10 x \<open>q\<close>\<close>, 2)" (* Should parse as ([q, q, q, q, q, q, q, q, q, q], 2) *)
term "(MY \<open>3 * \<open>MY \<open>3 * \<open>b+c\<close>\<close>\<close>\<close>, 2)" (* Things can be nested! *)

end
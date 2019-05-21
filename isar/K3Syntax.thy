theory K3Syntax
  imports Main
keywords
 "k3" :: diag
begin

datatype K3Term =
  K3EMPTY | INT int | NUM | LAM


ML \<open>
  Outer_Syntax.command @{command_keyword k3} ""
    (Parse.cartouche >> (fn s =>
      Toplevel.keep (fn _ => writeln s)))
\<close>

k3 \<open>hello\<close>




ML {*

(*  fun k3_int s = Const(Syntax.const @{const_syntax INT} $ s, @{typ K3Term})
 *)
val t = Syntax.const "Hello"



fun k3_parse "" = Const(@{const_syntax "K3EMPTY"}, @{typ K3Term})
  | k3_parse s = Syntax.const @{const_syntax INT} $ Syntax.const s

fun k3_tr content args =
    let fun err () = raise TERM ("k3_translate", args) in
      (case args of
        [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => c $ k3_parse (content (s, pos)) $ p
          | NONE => err ())
      | _ => err ())
    end;
*}

syntax "_k3_string" :: "cartouche_position \<Rightarrow> K3Term" ("k3 _")
parse_translation \<open>[
   (@{syntax_const "_k3_string"}, 
    K (k3_tr (Symbol_Pos.cartouche_content o Symbol_Pos.explode)))
]\<close>

term "k3 \<open>{x+1}\<close>" 

end
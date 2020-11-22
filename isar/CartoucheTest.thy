theory CartoucheTest
  imports Main
begin

datatype K3 = KNUL | KSTR string


ML \<open>
  local
    fun mk_char (s, pos) =
      let
        val c =
          if Symbol.is_ascii s then ord s
          else if s = "\<newline>" then 10
          else error ("String literal contains illegal symbol: " ^ quote s ^ Position.here pos);
      in list_comb (Syntax.const @{const_syntax Char}, String_Syntax.mk_bits_syntax 8 c) end;

    fun mk_str [] = Const (@{const_syntax Nil}, @{typ string})
      | mk_str (s :: ss) =
          Syntax.const @{const_syntax Cons} $ mk_char s $ mk_str ss;

    fun mk_k3 [] = Const(@{const_syntax KNUL}, @{typ K3})
      | mk_k3 s  = Syntax.const @{const_syntax KSTR} $ mk_str s;

  in
    fun k3_tr content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ mk_k3 (content (s, pos)) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>

syntax "_cartouche_string" :: \<open>cartouche_position \<Rightarrow> K3\<close>  ("k3_")
parse_translation \<open>
  [(@{syntax_const "_cartouche_string"},
    K (k3_tr (Symbol_Pos.cartouche_content o Symbol_Pos.explode)))]
\<close>

term \<open>k3\<open>\<close>\<close>
term \<open>k3\<open>abc\<close>\<close>
term \<open>k3\<open>\<newline>\<close>\<close>





end
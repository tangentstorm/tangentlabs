theory Exponents
imports Main
begin

(* these first few lines just give "my" names to some predefined rules *)
lemma rMulComm: "(a*b ::nat) = (b*a ::nat)"
by (rule Groups.ab_semigroup_mult_class.mult.commute)

lemma rExpMul: "((a^b)^c ::int) = (a^(b*c) ::int)"
by (rule Int.zpower_zpower)

(* and now for the proof: *)
theorem "((a^b)^c ::int) = ((a^c)^b :: int)"
proof -
  have  "(a^b)^c = a^(b*c)" by (simp only: rExpMul)
  hence "   ...  = a^(c*b)" by (simp only: rMulComm)
  thus  "(a^b)^c = (a^c)^b" by (simp only: rExpMul)
qed

end


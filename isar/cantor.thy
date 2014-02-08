theory cantor
imports Main
begin

(* these are all different ways to write the same proof. from: 
 * http://isabelle.in.tum.de/dist/Isabelle2013/doc/prog-prove.pdf
 * original proof was by g.cantor *)

lemma "\<not> surj(f::'a \<Rightarrow>'a set)"
  proof
    assume 0 : "surj f"
    from 0 have 1 : "\<forall>A. \<exists>a. A = f a" by blast
    from 1 have 2 : "\<exists>a. {x. x \<notin> f x} = f a" by blast
    from 2 show False by blast
  qed

lemma "\<not> surj(f::'a \<Rightarrow>'a set)"
  proof
    assume "surj f"
    from this have "\<forall>A. \<exists>a. A = f a" by (auto simp: surj_def)
    from this have "\<exists>a. {x. x \<notin> f x} = f a" by blast
    from this show False by blast
  qed

lemma "\<not> surj(f::'a \<Rightarrow>'a set)"
  proof
    assume "surj f"
    hence "\<forall>A. \<exists>a. A = f a" by (auto simp: surj_def)
    hence "\<exists>a. {x. x \<notin> f x} = f a" by blast
    thus False by blast
  qed

lemma
  fixes f::"'a \<Rightarrow> 'a set"
  assumes s:"surj f"
  shows "False"
proof -
  have "\<exists> a. {x. x \<notin> f x} = f a" using s 
    by  (auto simp: surj_def)
  thus "False" by blast
qed



end

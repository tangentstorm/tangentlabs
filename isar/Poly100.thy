(* Isar Proofs (eventually) for two of the theorems from http://www.cs.ru.nl/~freek/100/

   #13 Polyhedron Formula (F + V - E = 2)     (TODO)
   #50 The Number of Platonic Solids
       (core logic is proven, except for a missing duplicate argument)

*)
theory Poly100
  imports Main "HOL-Analysis.Polytope"
begin

(* ------------------------------------------------------------------------ *)
section \<open>The Polyhedron Formula\<close>
(* ------------------------------------------------------------------------ *)

definition edges where
  "edges p = {e. e edge_of p}"
definition vertices where
  "vertices p = {v. v face_of p \<and> aff_dim v = 0}"
definition faces where
  "faces p = {v. v face_of p \<and> aff_dim v = 2}"

locale convex_polyhedron =
  fixes p assumes "solid p" and "aff_dim p = 3"
begin

definition F where "F = card(faces p)"
definition V where "V = card(vertices p)"
definition E where "E = card(edges p)"

theorem polyhedron_formula:
  shows "F + V - E = 2"
  (* Reference: HOL light proof (really list of tactics) in
     https://github.com/jrh13/hol-light/blob/master/100/platonic.ml *)
proof -
  show ?thesis sorry
qed

end


(* ------------------------------------------------------------------------ *)
section \<open>The Platonic Solids\<close>
(* ------------------------------------------------------------------------ *)

text \<open>There are exactly five platonic solids. The following theorem enumerates
      them by their Schläfli pairs \<open>(s,m)\<close>, using the polyhedron formula above.\<close>

theorem (in convex_polyhedron) PLATONIC_SOLIDS:
  fixes s::nat \<comment> \<open>number of sides on each face\<close>
    and m::nat \<comment> \<open>number of faces that meet at each vertex\<close>
  assumes "s \<ge> 3"  \<comment> \<open>faces must have at least 3 sides\<close>
      and "m \<ge> 3"  \<comment> \<open>at least three faces must meet at each vertex\<close>
      and "E>0"
      and eq0: "s * F = 2 * E"
      and eq1: "m * V = 2 * E"
    shows "(s,m) \<in> {(3,3), (3,4), (3,5), (4,3), (5,3)}"
proof -
  \<comment> \<open>Following Euler, as explained here:
      https://www.mathsisfun.com/geometry/platonic-solids-why-five.html\<close>
  have iq0: "1/s + 1/m > 1/2"
  proof -
    have f:"F = 2*E/s" using `s \<ge> 3` eq0 `E>0`
      by (metis mult_eq_0_iff neq0_conv nonzero_mult_div_cancel_left of_nat_eq_0_iff of_nat_mult zero_neq_numeral)
    have v:"V = 2*E/m" using `m \<ge> 3` eq1 `E>0`
      by (metis mult_eq_0_iff neq0_conv nonzero_mult_div_cancel_left of_nat_eq_0_iff of_nat_mult zero_neq_numeral)
    have  "F + V - E = 2" using polyhedron_formula .
    hence "(2*E/s) + (2*E/m) - E = 2" using f v by simp
    hence "E/s + E/m - E/2 = 1" by simp
    hence "E * (1/s + 1/m - 1/2) = 1" by argo
    hence "(1/s + 1/m - 1/2) = 1/E" using `E>0`
      by (simp add: linordered_field_class.sign_simps(24) nonzero_eq_divide_eq)
    moreover from `E>0` have "1/E>0" by simp
    ultimately show ?thesis using `E>0` by argo
  qed
  hence "s \<le> 5" and "m \<le> 5"
  proof -
    show "s\<le>5" proof (rule ccontr)
      assume "\<not>s\<le>5"
      hence "s > 5" by simp
      hence "1/s < 1/5" by simp
      hence "1/5 + 1/m > 1/2" using iq0 by linarith
      hence "1/m > 3/10" by simp
      hence "m < 10/3" using less_imp_inverse_less by fastforce
      hence "m \<le> 3" by simp
      moreover have "m\<noteq>3" proof
        assume "m=3"
        with iq0 have "1/s + 1/3 > 1/2" by auto
        hence "1/s > 1/2 - 1/3" by simp
        hence "1/s > 1/6" by simp
        hence "s < 6" using div_by_1 floor_of_nat linorder_not_le by fastforce
        with `s > 5` show False by simp
      qed
      ultimately have "m<3" by simp
      hence "False" using `m\<ge>3` by auto
      thus "\<not>s\<le>5 \<Longrightarrow> False" by simp
    qed
  next
    show "m\<le>5" \<comment> \<open>!HELP!: same argument as above, swapping m and s\<close>  sorry
  qed
  hence "s\<le>5 \<and> m\<le>5" using assms by auto
  hence "s \<in> {3,4,5}" and "m \<in> {3,4,5}" using assms by auto
  hence "(s,m) \<in> {3,4,5} \<times> {3,4,5}" by auto
  moreover have "(s,m) \<notin> {(4,4), (5,4), (4,5), (5,5)}" proof -
    have sm: "1/s + 1/m > 1/2" using iq0 by blast
    \<comment> \<open>!HELP! all of these are essentially the same. How can I simplify this?\<close>
    have 44: "(s,m) \<noteq> (4,4)" proof
      assume a44: "(s,m) = (4,4)" hence "1/s+1/m\<ge>1/2" using sm by simp
      thus False using a44 iq0 by auto qed
    have 54: "(s,m) \<noteq> (5,4)" proof
      assume a54: "(s,m) = (5,4)" hence "1/s+1/m\<ge>1/2" using sm by simp
      thus False using a54 iq0 by auto qed
    have 45: "(s,m) \<noteq> (4,5)" proof
      assume a45: "(s,m) = (4,5)" hence "1/s+1/m\<ge>1/2" using sm by simp
      thus False using a45 iq0 by auto qed
    have 55: "(s,m) \<noteq> (5,5)" proof
      assume a55: "(s,m) = (5,5)" hence "1/s+1/m\<ge>1/2" using sm by simp
      thus False using a55 iq0 by auto qed
    from 44 54 45 55 show ?thesis by auto
  qed
  ultimately show "(s,m) \<in> {(3,3), (3,4), (3,5), (4,3), (5,3)}" by auto
qed

end

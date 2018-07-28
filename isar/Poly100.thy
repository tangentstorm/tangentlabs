(* Isar Proofs (eventually) for two of the theorems from http://www.cs.ru.nl/~freek/100/

   #13 Polyhedron Formula (F + V - E = 2)     (TODO)
   #50 The Number of Platonic Solids
       (core argument is proven. assumptions are not)

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
  fixes p assumes "polytope p" "aff_dim p = 3"
begin

definition F where "F = card(faces p)"
definition V where "V = card(vertices p)"
definition E where "E = card(edges p)"

theorem polyhedron_formula:
  shows "F + V - E = 2"
  sorry

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

  \<comment>\<open>First, redefine F and V in terms of sides and meets:\<close>
  from eq0 `s\<ge>3` have f: "F = 2*E/s"
    by (metis nonzero_mult_div_cancel_left not_numeral_le_zero of_nat_eq_0_iff of_nat_mult)
  from eq1 `m\<ge>3` have v: "V = 2*E/m"
    by (metis nonzero_mult_div_cancel_left not_numeral_le_zero of_nat_eq_0_iff of_nat_mult)

  \<comment>\<open>Next, rewrite Euler's formula as inequality \<open>iq0\<close> in those terms:\<close>
  from polyhedron_formula have "F + V - E = 2" .
  with f v have "(2*E/s) + (2*E/m) - E = 2" by simp
  hence "E/s + E/m - E/2 = 1" by simp
  hence "E * (1/s + 1/m - 1/2) = 1" by argo
  with `E>0` have "1/s + 1/m - 1/2 = 1/E"
    by (simp add: linordered_field_class.sign_simps(24) nonzero_eq_divide_eq)
  with `E>0` have iq0: "1/s + 1/m > 1/2" by (smt of_nat_0_less_iff zero_less_divide_1_iff)

  \<comment>\<open>Lower bounds for \<open>{s,m}\<close> provide upper bounds for \<open>{1/s, 1/m}\<close>\<close>
  with `s\<ge>3` `m\<ge>3` have "1/s \<le> 1/3" "1/m \<le> 1/3" by auto

  \<comment>\<open>Plugging these into \<open>iq0\<close>, we calculate upper bounds for \<open>{s,m}\<close>\<close>
  with iq0 have "1/s > 1/6" "1/m > 1/6" by linarith+
  hence "s < 6" "m < 6" using not_less by force+

  \<comment>\<open>This gives us 9 possible combinations for the pair \<open>(s,m)\<close>.\<close>
  with `s\<ge>3` `m\<ge>3` have "s \<in> {3,4,5}" "m \<in> {3,4,5}" by auto
  hence "(s,m) \<in> {3,4,5} \<times> {3,4,5}" by auto

  \<comment>\<open>However, four of these fail to satisfy our inequality.\<close>
  moreover from iq0 have "1/s + 1/m > 1/2" .
  hence "(s,m) \<notin> {(4,4), (5,4), (4,5), (5,5)}" by auto
  ultimately show "(s,m) \<in> {(3,3), (3,4), (3,5), (4,3), (5,3)}" by auto
qed

text \<open>So far, this proof shows that if these relationships between {s,m,F,V} hold,
  then a platonic solid must have one of these five combinations for (s,m).
  We have not yet shown the converse -- that the five remaining pairs actually do
  represent valid polyhedra.

  We also haven't shown that eq0 and eq1 actually describe convex polyhedra. These
  should be theorems, not assumptions.

  Probably even, \<open>s\<ge>3\<close>, \<open>m\<ge>3\<close>, and \<open>E>0\<close> can be derived from more basic facts. I will
  have to study Polytope.thy a bit more.\<close>


end

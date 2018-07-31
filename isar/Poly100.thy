(* Isar Proofs (eventually) for three theorems from http://www.cs.ru.nl/~freek/100/

   #13 Polyhedron Formula (F + V - E = 2)
   #50 The Number of Platonic Solids
   #92 Pick's theorem
*)
theory Poly100
  imports Main "HOL-Analysis.Polytope"
begin

(* ------------------------------------------------------------------------ *)
section \<open>Syntax helpers\<close>
(* ------------------------------------------------------------------------ *)

definition d_faces ("(_ d'_faces _)" [85,85] 80) where
  "n d_faces p = {f. f face_of p \<and> aff_dim f = n}"

definition d_face_count ("(_ d'_face'_count _)" [85,85] 80) where
  "n d_face_count p = card(n d_faces p)"

definition verts where "verts p = 0 d_faces p"
definition edges where "edges p = 1 d_faces p"
definition faces where "faces p = 2 d_faces p"


(* ------------------------------------------------------------------------ *)
section \<open>The Euler characteristic.\<close>
(* ------------------------------------------------------------------------ *)

definition euler_char where
  "euler_char p = (\<Sum>n=0..aff_dim p. (-1)^(nat n) * n d_face_count p)"


subsection \<open>Euler characteristic for empty set.\<close>

lemma empty_face_count:
  "(-1) d_face_count p = 1"
proof -
  let ?F = "(-1) d_faces p"
  have "?F = {f. f face_of p \<and> aff_dim f = -1}" by (simp add: d_faces_def)
  hence "?F = {f. f face_of p \<and> f = {}}" by (simp add: aff_dim_empty)
  hence f: "?F = {{}}" by auto
  have "(-1) d_face_count p = card(?F)" by (simp add: d_face_count_def)
  with f show "(-1) d_face_count p = 1" by simp
qed

lemma ec_empty_0:
  "euler_char {} = 0"
proof -
  have "euler_char {} = (\<Sum>n= 0..-1. (-1)^(nat n) * n d_face_count {})"
    by (simp add: euler_char_def)
  thus "euler_char {} = 0" by auto
qed

subsection \<open>Simplex helpers.\<close>

lemma simplex_self_face:
  assumes "n simplex S" shows "S face_of S"
  using assms convex_simplex face_of_refl by auto


lemma n_simplex_only_n_face:
  assumes "n simplex S" shows "n d_faces S = {S}"
proof
  let ?F = "n d_faces S"
  have "?F \<subseteq> {f. f face_of S \<and> aff_dim f = n}" using d_faces_def by auto
  hence "?F \<subseteq> {f. f face_of S}" by auto
  thus "?F \<subseteq> {S}" by (smt aff_dim_simplex assms convex_simplex
      d_faces_def face_of_aff_dim_lt insertCI mem_Collect_eq simplex_def subsetI)
next
  show "{S} \<subseteq> n d_faces S"
    using assms(1) simplex_self_face aff_dim_simplex d_faces_def by blast
qed

subsection \<open>Euler characteristic for a single point, aka a 0 simplex.\<close>

lemma euler_simplex_0:
  assumes "0 simplex S"
  shows "euler_char S = 1"
proof -
  have dim: "aff_dim S = 0" by (simp add: aff_dim_simplex assms)
  have cnt: "0 d_face_count S = 1" using n_simplex_only_n_face
    by (simp add: n_simplex_only_n_face assms d_face_count_def)

  \<comment> \<open>Now plug these results into the definition, and calculate.\<close>
  have "euler_char S = (\<Sum>n=0..aff_dim S. (-1)^(nat n) * n d_face_count S)"
    by (fact euler_char_def)
  also have "... = ((-1)^0 * (0 d_face_count S))"  using dim by simp
  also have "... = (0 d_face_count S)" by simp
  finally show "euler_char S = 1" using cnt by simp
qed

subsection \<open>Euler characteristic for an n-Simplex.\<close>


subsection \<open>Now Euler-Poincare for a a general full-dimensional polytope.\<close>

theorem euler_poincare:
  assumes "polytope p" and "aff_dim p = d"
  shows "euler_char p = 1"
  sorry

(* ------------------------------------------------------------------------ *)
section \<open>The Polyhedron Formula\<close>
(* ------------------------------------------------------------------------ *)
text \<open>The polyhedron formula is the Euler relation in 3 dimensions.\<close>


locale convex_polyhedron =
  fixes p assumes "polytope p" and "aff_dim p = 3"
begin

definition F where "F = card(faces p)"
definition V where "V = card(verts p)"
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


(* ------------------------------------------------------------------------ *)
section \<open>Pick's Theorem\<close>
(* ------------------------------------------------------------------------ *)

text \<open>Another consequence of Euler's formula is Pick's theorem, which describes
  the area of a polygon whose vertices all lie on the integer lattice points of the
  plane. (In other words for each vertex, the coordinates x,y on the plane are both
  integers.)

  We can prove it by triangulating the polygon such that each triangle has 0
  interior lattice points, and the boundary of each triangle is a lattice point.

  Then, assuming the area of each such triangle is 1/2, we can just divide the
  number of faces F by 2. (except one face is the plane itself, so we say A=(F-1)/2.
\<close>

theorem pick0: "B = 3 \<and> I = 0 \<longrightarrow> A = 1/2"
  \<comment> \<open>TODO: prove the area of a primitive triangle is 1/2. \<close>
  oops


theorem funkenbusch:
  fixes I::int and B::int \<comment> \<open>number of interior and boundary points\<close>
  shows "E = 3*I + 2*B - 3"
    \<comment> \<open>informal proof due to Funkenbusch:
       "From Euler's Formula to Pick's Formula Using an Edge Theorem"
       http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.475.919&rep=rep1&type=pdf

   (still thinking about how to formalize this.)

  The theorem counts the number of edges in the triangularization, inductively.

  0. (Base case): B=3, I=0 \<longrightarrow> E=3  (a single triangle)
       E' = 3*I' + 2*B' - 3
       E' = 3*0  + 2*3  - 3

  1. I'=I+1 \<longrightarrow> E'=E+3     : new interior point subdivides a triangle into 3 parts, adding 3 edges
    true because the formula contains the term  E = 3*I + ...

  2. B'=B+(1-x) \<longrightarrow> E'=E+(2+x) : new boundary point adds 2 edges to boundary. but this also
                                 moves \<open>X\<ge>0\<close> old boundary points into the interior, and have to draw
                                 an edge from the new point to each of them, too.
    E' = 3*I' + 2*B' - 3
    E' = 3*(I+x) + 2*(B+1-x) -3
    E' = 3I +3x + 2B + 2 - 2x - 3
    E' = 3I + 2B + x - 1
    E + (2+x) = 3I + 2B + x - 1
    E = 3I + 2B - 3 \<close>
  oops


theorem pick's_theorem:
  fixes I::int and B::int \<comment> \<open>number of interior and boundary points\<close>
    and V::int and E::int and F::int \<comment> \<open>edges, vertices, and faces (triangles + the plane)\<close>
  assumes "B\<ge>3" \<comment> \<open>So we have a polygon\<close>
    and euler: "V - E + F = 2" \<comment> \<open>Euler's theorem\<close>
    and verts: "V = I + B"  \<comment> \<open>Each point has become a vertex in the triangularization graph\<close>
    and edges: "E = 3*I + 2*B - 3" \<comment> \<open>Funkenbusch's edge theorem, above\<close>
    and area: "A = (F-1)/2" \<comment> \<open>coming soon...\<close>
  shows "A = I + B/2 - 1"
proof -
  from euler have "V - E + F = 2" .
  with verts have "(I + B) - E + F = 2" by simp
  with edges have "(I + B) - (3*I + 2*B - 3) + F = 2" by simp
  hence "(I + B) - (3*I + 2*B - 3) + F = 2" by simp
  hence "F = 2 * I + B - 1" by simp
  hence "F-1 = 2*I + B - 2" by simp
  hence "(F-1)/2 = I + B/2 -1" by simp
  with area show "A = I + B/2 - 1" by auto
qed

end

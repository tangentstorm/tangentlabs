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

definition facets ("(_ facets _)" [85,85] 80) where
  "n facets p = {f. f face_of p \<and> aff_dim f = n}"

definition verts where "verts p = 0 facets p"
definition edges where "edges p = 1 facets p"
definition faces where "faces p = 2 facets p"


(* ------------------------------------------------------------------------ *)
section \<open>The Euler characteristic.\<close>
(* ------------------------------------------------------------------------ *)

definition euler_char where
  "euler_char p = (\<Sum>d=0..aff_dim p. (-1) ^ card(d facets p))"

text \<open>The following proof follows the HOL-Light implementation by John Harrison at
      https://github.com/jrh13/hol-light/blob/master/100/polyhedron.ml\<close>

subsection \<open>Interpret which "side" of a hyperplane a point is on.\<close>

default_sort "real_inner"

type_synonym 'v hyperplane = "'v \<times> real"
type_synonym 'v arrangement = "('v hyperplane) set"

fun hyperplane_side :: "'v hyperplane \<Rightarrow> 'v  \<Rightarrow> real" where
  "hyperplane_side (a, b) x = sgn (a \<bullet> x - b)"

subsection \<open>Equivalence relation imposed by hyperplane arrangement.\<close>

definition hyperplane_equiv  :: "'v arrangement \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "hyperplane_equiv A x y \<equiv> \<forall>h\<in>A. hyperplane_side h x = hyperplane_side h y"

lemma hyperplane_equiv_refl:
  "hyperplane_equiv A x x"
  by (smt hyperplane_equiv_def)

lemma hyperplane_equiv_sym:
  "hyperplane_equiv A x y \<equiv> hyperplane_equiv A y x"
  by (smt hyperplane_equiv_def)

lemma hyperplane_equiv_trans:
  "hyperplane_equiv A x y \<and> hyperplane_equiv A y z \<Longrightarrow> hyperplane_equiv A x z"
  by (smt hyperplane_equiv_def)

lemma hyperplane_equiv_union:
  "hyperplane_equiv (A\<union>B) x y \<equiv>
   hyperplane_equiv A x y \<and> hyperplane_equiv B x y"
  by (smt Un_iff hyperplane_equiv_def)

subsection \<open>Cells of a hyperplane arrangement\<close>

\<comment> \<open>Harrison seems to define hyperplane_cell as a partially applied function,
   and then immediately proves a lemma that shows it's a set. Maybe this is some
   kind of magic thing in HOL/Light? I'll use the set definition directly and
   hope for the best.\<close>

definition hyperplane_cell :: "'v arrangement \<Rightarrow> ('v set) \<Rightarrow> bool" where
  "hyperplane_cell A c \<equiv> \<exists>x. c = {y. hyperplane_equiv A x y}"

\<^cancel>\<open>lemma hyperplane_cell:   \<comment> \<open>Do I need this?\<close>
  "hyperplane_cell A c \<equiv> (\<exists>x. c = {y. hyperplane_equiv A x y})"
  by (fact hyperplane_cell_def)\<close>

lemma not_hyperplane_cell_empty: "\<not> hyperplane_cell A {}"
  using hyperplane_cell_def hyperplane_equiv_refl by fastforce

lemma nonempty_hyperplane_cell: "hyperplane_cell A c \<Longrightarrow> \<not>(c = {})"
  using hyperplane_cell_def hyperplane_equiv_refl by fastforce

\<comment> \<open>This is saying the union of all hyperplane cells in the arrangement is the entire
   real^N space. I am somewhat impressed that sledgehammer managed to prove this, once I
   broke it down into sub-cases.\<close>
lemma unions_hyperplane_cells: "\<Union> {c. hyperplane_cell A c} = UNIV"
proof
  show "\<Union> {c. hyperplane_cell A c} \<subseteq> UNIV" by simp
next
  show "UNIV \<subseteq> \<Union> {c. hyperplane_cell A c}"
    by (metis (mono_tags, hide_lams) UnionI hyperplane_cell_def hyperplane_equiv_refl mem_Collect_eq subsetI)
qed

lemma disjoint_hyperplane_cells:
  assumes "hyperplane_cell A c1" and "hyperplane_cell A c2" and "\<not>(c1=c2)"
  shows "disjoint {c1, c2}"
  sorry

lemma disjoint_hyperplane_cells_eq:
  "hyperplane_cell A c1 \<and> hyperplane_cell A c2 \<Longrightarrow> (disjoint {c1,c2} \<equiv> \<not>(c1=c2))"
  sorry

lemma hyperplane_cell_empty: "hyperplane_cell {} c \<equiv> c = UNIV"
  by (simp add: hyperplane_cell_def hyperplane_equiv_def)

lemma hyperplane_cell_sing_cases:
  assumes "hyperplane_cell {(a,b)} c"
  shows "c = {x. a \<bullet> x = b} \<or>
         c = {x. a \<bullet> x < b} \<or>
         c = {x. a \<bullet> x > b}"
  sorry

\<^cancel>\<open>
let HYPERPLANE_CELL_SING = prove
 (`!a b c.
        hyperplane_cell {(a,b)} c <=>
        if a = vec 0 then c = (:real^N)
        else c = {x | a dot x = b} \/
             c = {x | a dot x < b} \/
             c = {x | a dot x > b}`,

let HYPERPLANE_CELL_UNION = prove
 (`!A B c:real^N->bool.
        hyperplane_cell (A UNION B) c <=>
        ~(c = {}) /\
        ?c1 c2. hyperplane_cell A c1 /\
                hyperplane_cell B c2 /\
                c = c1 INTER c2`,

let FINITE_HYPERPLANE_CELLS = prove
 (`!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c}`,

let FINITE_RESTRICT_HYPERPLANE_CELLS = prove
 (`!P A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cell A c /\ P c}`,

let FINITE_SET_OF_HYPERPLANE_CELLS = prove
 (`!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> FINITE C`,

let PAIRWISE_DISJOINT_HYPERPLANE_CELLS = prove
 (`!A C. (!c. c IN C ==> hyperplane_cell A c)
         ==> pairwise DISJOINT C`,

let HYPERPLANE_CELL_INTER_OPEN_AFFINE = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> ?s t. open s /\ affine t /\ c = s INTER t`,

let HYPERPLANE_CELL_RELATIVELY_OPEN = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> open_in (subtopology euclidean (affine hull c)) c`,

let HYPERPLANE_CELL_RELATIVE_INTERIOR = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c
        ==> relative_interior c = c`,

let HYPERPLANE_CELL_CONVEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> convex c`,

let HYPERPLANE_CELL_INTERS = prove
 (`!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c) /\
         ~(C = {}) /\ ~(INTERS C = {})
         ==> hyperplane_cell A (INTERS C)`,

let HYPERPLANE_CELL_INTER = prove
 (`!A s t:real^N->bool.
        hyperplane_cell A s /\ hyperplane_cell A t /\ ~(s INTER t = {})
        ==> hyperplane_cell A (s INTER t)`,
\<close>


subsection \<open>A cell complex is considered to be a union of such cells\<close>

\<^cancel>\<open>
let hyperplane_cellcomplex = new_definition
 `hyperplane_cellcomplex A s <=>
        ?t. (!c. c IN t ==> hyperplane_cell A c) /\
            s = UNIONS t`;;


let HYPERPLANE_CELLCOMPLEX_EMPTY = prove
 (`!A:real^N#real->bool. hyperplane_cellcomplex A {}`,

let HYPERPLANE_CELL_CELLCOMPLEX = prove
 (`!A c:real^N->bool. hyperplane_cell A c ==> hyperplane_cellcomplex A c`,

let HYPERPLANE_CELLCOMPLEX_UNIONS = prove
 (`!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (UNIONS C)`

let HYPERPLANE_CELLCOMPLEX_UNION = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s UNION t)`

let HYPERPLANE_CELLCOMPLEX_UNIV = prove
 (`!A. hyperplane_cellcomplex A (:real^N)`

let HYPERPLANE_CELLCOMPLEX_INTERS = prove
 (`!A C. (!s:real^N->bool. s IN C ==> hyperplane_cellcomplex A s)
         ==> hyperplane_cellcomplex A (INTERS C)`,

let HYPERPLANE_CELLCOMPLEX_INTER = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s INTER t)`

let HYPERPLANE_CELLCOMPLEX_COMPL = prove
 (`!A s. hyperplane_cellcomplex A s
         ==> hyperplane_cellcomplex A ((:real^N) DIFF s)`,

let HYPERPLANE_CELLCOMPLEX_DIFF = prove
 (`!A s t.
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex A t
        ==> hyperplane_cellcomplex A (s DIFF t)`,

let HYPERPLANE_CELLCOMPLEX_MONO = prove
 (`!A B s:real^N->bool.
        hyperplane_cellcomplex A s /\ A SUBSET B
        ==> hyperplane_cellcomplex B s`,

let FINITE_HYPERPLANE_CELLCOMPLEXES = prove
 (`!A. FINITE A ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c}`,

let FINITE_RESTRICT_HYPERPLANE_CELLCOMPLEXES = prove
 (`!P A. FINITE A
         ==> FINITE {c:real^N->bool | hyperplane_cellcomplex A c /\ P c}`,

let FINITE_SET_OF_HYPERPLANE_CELLS = prove
 (`!A C. FINITE A /\ (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c)
         ==> FINITE C`,

let CELL_SUBSET_CELLCOMPLEX = prove
 (`!A s c:real^N->bool.
        hyperplane_cell A c /\ hyperplane_cellcomplex A s
        ==> (c SUBSET s <=> ~(DISJOINT c s))`,
\<close>

subsection \<open>Euler Characteristic\<close>

\<^cancel>\<open>
let euler_characteristic = new_definition
 `euler_characteristic A (s:real^N->bool) =
        sum {c | hyperplane_cell A c /\ c SUBSET s}
            (\c. (-- &1) pow (num_of_int(aff_dim c)))`;;

let EULER_CHARACTERISTIC_EMPTY = prove
 (`euler_characteristic A {} = &0`,

let EULER_CHARACTERISTIC_CELL_UNIONS = prove
 (`!A C. (!c:real^N->bool. c IN C ==> hyperplane_cell A c)
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. (-- &1) pow (num_of_int(aff_dim c)))`

let EULER_CHARACTERISTIC_CELL = prove
 (`!A c. hyperplane_cell A c
         ==> euler_characteristic A c =  (-- &1) pow (num_of_int(aff_dim c))`,

let EULER_CHARACTERISTIC_CELLCOMPLEX_UNION = prove
 (`!A s t:real^N->bool.
        FINITE A /\
        hyperplane_cellcomplex A s /\
        hyperplane_cellcomplex A t /\
        DISJOINT s t
        ==> euler_characteristic A (s UNION t) =
            euler_characteristic A s + euler_characteristic A t`,

let EULER_CHARACTERISTIC_CELLCOMPLEX_UNIONS = prove
 (`!A C. FINITE A /\
         (!c:real^N->bool. c IN C ==> hyperplane_cellcomplex A c) /\
         pairwise DISJOINT C
         ==> euler_characteristic A (UNIONS C) =
             sum C (\c. euler_characteristic A c)`,

let EULER_CHARACTERISTIC = prove
 (`!A s:real^N->bool.
        FINITE A
        ==> euler_characteristic A s =
            sum (0..dimindex(:N))
                (\d. (-- &1) pow d *
                     &(CARD {c | hyperplane_cell A c /\ c SUBSET s /\
                                 aff_dim c = &d}))`,
\<close>

subsection \<open>Show that the characteristic is invariant w.r.t. hyperplane arrangement.\<close>

\<^cancel>\<open>
let HYPERPLANE_CELLS_DISTINCT_LEMMA = prove
 (`!a b. {x | a dot x = b} INTER {x | a dot x < b} = {} /\
         {x | a dot x = b} INTER {x | a dot x > b} = {} /\
         {x | a dot x < b} INTER {x | a dot x = b} = {} /\
         {x | a dot x < b} INTER {x | a dot x > b} = {} /\
         {x | a dot x > b} INTER {x | a dot x = b} = {} /\
         {x | a dot x > b} INTER {x | a dot x < b} = {}`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let EULER_CHARACTERSTIC_LEMMA = prove
 (`!A h s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> euler_characteristic (h INSERT A) s = euler_characteristic A s`,


let EULER_CHARACTERSTIC_INVARIANT = prove
 (`!A B h s:real^N->bool.
        FINITE A /\ FINITE B /\
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex B s
        ==> euler_characteristic A s = euler_characteristic B s`,
  SUBGOAL_THEN
   `!A s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s
        ==> !B. FINITE B
                ==> euler_characteristic (A UNION B) s =
                    euler_characteristic A s`

let EULER_CHARACTERISTIC_INCLUSION_EXCLUSION = prove
 (`!A s:(real^N->bool)->bool.
        FINITE A /\ FINITE s /\ (!k. k IN s ==> hyperplane_cellcomplex A k)
        ==> euler_characteristic A (UNIONS s) =
            sum {t | t SUBSET s /\ ~(t = {})}
                (\t. (-- &1) pow (CARD t + 1) *
                     euler_characteristic A (INTERS t))`,
\<close>

subsection \<open>Euler-type relation for full-dimensional proper polyhedral cones.\<close>

\<^cancel>\<open>

let EULER_POLYHEDRAL_CONE = prove
 (`!s. polyhedron s /\ conic s /\ ~(interior s = {}) /\ ~(s = (:real^N))
       ==> sum (0..dimindex(:N))
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of s /\ aff_dim f = &d })) = &0`,

\<comment> \<open> ! HOL/Light proof is gigantic...\<close>\<close>


subsection \<open>Euler-Poincare relation for special (n-1)-dimensional polytope.\<close>

\<^cancel>\<open>let EULER_POINCARE_LEMMA = prove
 (`!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &1}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
\<comment> \<open>another gigantic proof\<close>

let EULER_POINCARE_SPECIAL = prove
 (`!p:real^N->bool.
        2 <= dimindex(:N) /\ polytope p /\ affine hull p = {x | x$1 = &0}
        ==> sum (0..dimindex(:N)-1)
               (\d. (-- &1) pow d *
                    &(CARD {f | f face_of p /\ aff_dim f = &d })) = &1`,
\<close>

subsection \<open>Now Euler-Poincare for a a general full-dimensional polytope.\<close>

theorem euler_poincare_full:
  assumes "polytope p" and "affine_dim p d"
  shows "(\<Sum>k=0..d. (-1)^k * card(k facets p)) = 1"
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

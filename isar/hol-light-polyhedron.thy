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


lemma euler_poincare_lemma:
  assumes "polytope p" and "aff_dim p \<le> 2"
      and "affine hull p = {x. x$1 =1 }"
  shows "euler_char p = 1"
  sorry

lemma euser_poincare_special:
  assumes "polytope p" and "aff_dim p \<le> 2"
     and "affine hull p = {x. x$1 = 0}"
  shows "euler_char p = 1"
  sorry



section \<open>Euler characteristic\<close>

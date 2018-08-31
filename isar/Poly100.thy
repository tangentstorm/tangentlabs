(* Isar Proofs (eventually) for three theorems from http://www.cs.ru.nl/~freek/100/

   #13 Polyhedron Formula (F + V - E = 2)
   #50 The Number of Platonic Solids
   #92 Pick's theorem
*)
theory Poly100
  imports Main "HOL.Binomial" "HOL-Analysis.Polytope"
begin

(* ------------------------------------------------------------------------ *)
section \<open>Vocabulary (Syntax helpers)\<close>
(* ------------------------------------------------------------------------ *)

definition d_faces ("(_ d'_faces _)" [85,85] 80) where
  "n d_faces p = {f. f face_of p \<and> aff_dim f = n}"

definition d_face_count ("(_ d'_face'_count _)" [85,85] 80) where
  "n d_face_count p = card(n d_faces p)"

definition verts where "verts p = 0 d_faces p"
definition edges where "edges p = 1 d_faces p"
definition surfs where "surfs p = 2 d_faces p"

definition facets where "facets p = ((aff_dim p)-1) d_faces p"

\<comment> \<open>\<open>facets p\<close> should be identical to \<open>{f. facet_of p}\<close> but \<open>facet_of\<close> has an
    unnecessary restriction that {} isn't a facet. I wonder if maybe dimensions
    can't be negative in HOL-light: the polytope theory validates all the way to
    the end if the \<open>f\<noteq>{}\<close> restriction is removed.\<close>
lemma "facets p - {{}} \<equiv> {f. f facet_of p}"
  unfolding facets_def d_faces_def facet_of_def
  by (smt Collect_cong Collect_empty_eq Diff_empty Diff_insert0 Diff_insert_absorb
          aff_dim_empty mem_Collect_eq mk_disjoint_insert singletonI singleton_conv)

(* ------------------------------------------------------------------------ *)
section \<open>Simplex Theory.\<close>
(* ------------------------------------------------------------------------ *)


lemma facet_of_simplex_simplex:
  assumes "n simplex S" "F facet_of S" "n\<ge>0"
  shows "(n-1) simplex F"
\<comment> \<open>Polytope.thy defines @{thm simplex_insert_dimplus1} which demonstrates that you can
   add an affine-independent point to a simplex and create a higher-dimensional simplex
   (e.g: adding a point off the plane to a triangle yields a tetrahedron.) This lemma
   lets us work in the opposite direction, to show each n-dimensional simplex is
   composed of (n-1) simplices.\<close>
proof -
  \<comment> \<open>\<open>C1\<close> is the set of affine-independent vertices required by @{const simplex}. \<close>
  obtain C1 where C: "finite C1" "\<not>(affine_dependent C1)" "int(card C1) = n+1"
    and S: "S = convex hull C1" using assms unfolding Polytope.simplex by force

  \<comment> \<open>Isolate the vertex from \<open>C1\<close> that isn't in F, and call the remaining set \<open>C\<close>.\<close>
  then obtain A where "A\<in>C1" and "A\<notin>F"
    by (metis affine_dependent_def affine_hull_convex_hull assms(2)
        facet_of_convex_hull_affine_independent_alt hull_inc)
  then obtain C where "C = C1 - {A}" by simp

  \<comment> \<open>Finally, show that \<open>F\<close> and \<open>C\<close> together meet the definition of an (n-1) simplex.\<close>
  show ?thesis unfolding Polytope.simplex
  proof (intro exI conjI)

    \<comment> \<open>The first couple statements show that the remaining vertices of \<open>C\<close>
        are the extreme points of an \<open>n-1\<close> dimensional simplex. These all follow
        trivially from the idea that we're just removing one vertex from a set that
        already had the required properties.\<close>
    show "finite C" by (simp add: C(1) \<open>C = C1 - {A}\<close>)
    show "\<not> affine_dependent C" by (simp add: C(2) \<open>C = C1 - {A}\<close> affine_independent_Diff)
    show "int (card C) = (n-1) + 1"
      using C \<open>A \<in> C1\<close> \<open>C = C1 - {A}\<close> affine_independent_card_dim_diffs by fastforce

    show "F = convex hull C"
      \<comment> \<open>This is the tricky one. Intuitively, it's obvious that once we removed vertex A,
         there's one facet left, and it's the simplex defined by the remaining vertices.
         It's not obvious (to me, anyway) exactly how to derive this fact from the definitions.
         Thankfully, as long as we point her in the right direction, Isabelle is happy to work
         through the details of proofs that would normally be left as an exercise for the reader.\<close>
    proof
      \<comment> \<open>Briefly, a \<open>facet_of\<close> and a \<open>convex hull\<close> are both sets, so to prove equality, we just
         show that each is a subset of the other. Sledgehammer found a proof for the first
         statement in a matter of seconds.\<close>
      show "F \<subseteq> convex hull C"
        by (metis C(2) Diff_subset S \<open>A \<in> C1\<close> \<open>A \<notin> F\<close> \<open>C = C1 - {A}\<close> assms(2)
            facet_of_convex_hull_affine_independent hull_inc hull_mono insert_Diff subset_insert)
    next
      \<comment> \<open>The opposite direction was harder to prove. My plan had been to convince Isabelle
          that since C is the minimal set of affine-independent vertices, then removing any one
          would drop \<open>aff_dim C\<close> by 1. But we already know \<open>F\<subseteq>convex hull C\<close>, and (although we
          haven't proven it here), \<open>aff_dim C = aff_dim F\<close>. So if there were any point \<open>p\<in>C \<and> p\<notin>F\<close>,
          we would also have \<open>aff_dim C < aff_dim F\<close>, and hence a contradiction. The facts
          referenced by these sledgehammer-generated proofs suggest it found a way to derive
          a similar idea, but directly, without resorting to proof by contradicition.\<close>
      have"C \<subseteq> F"
        by (metis C(2) S \<open>A \<in> C1\<close> \<open>A \<notin> F\<close> \<open>C = C1 - {A}\<close> assms(2)
            facet_of_convex_hull_affine_independent hull_inc insertE insert_Diff subsetI)
      thus "convex hull C \<subseteq> F"
        by (metis C(2) S assms(2) convex_convex_hull facet_of_convex_hull_affine_independent hull_minimal)
    qed
  qed
qed


text \<open>The proof above was a lot of work. I wanted to generalize it to arbitrary faces, which
      made me realize that the set \<open>C\<close> in the definition of @{thm simplex} corresponds to
      the union of all vertex faces. (A vertex in polytope-land is a set containing one point,
      but simplices are defined in terms of the points themselves). So I found it helpful
      to create a definition that mirrors the definition of @{thm simplex}, but lets me
      assign a name to set of these points themselves. Since @{thm simplex} refers to this
      set as \<open>C\<close>, I decided it probably stood for \<open>corners\<close>, and so...\<close>

definition corners_of ("_ corners'_of _" [80, 80] 85) where
  "C corners_of S \<equiv> finite C \<and> (\<not>affine_dependent C) \<and>
                 (int(card C) = aff_dim S + 1) \<and>
                 (S=convex hull C)"

definition corners where
  "corners S = (THE C. C corners_of S)" if "n simplex S"


context
  fixes n :: int
    and S :: "'a::euclidean_space set"
  assumes nS: "n simplex S" and "n\<ge>-1"
begin

lemma corners_exist:
  shows "\<exists>C. C corners_of S"
  unfolding corners_of_def
  using Polytope.simplex aff_dim_simplex nS by blast

lemma corners_equiv:
  assumes "C0 corners_of S" and "C1 corners_of S"
  shows "C0 = C1"
  unfolding simplex_def corners_of_def
  by (metis assms corners_of_def extreme_point_of_convex_hull_affine_independent subsetI subset_antisym)

lemma corners_unique:
  shows "\<exists>!C. C corners_of S"
  using nS corners_exist corners_equiv by blast

lemma corners_are_corners_of:
  "(C = corners S) \<equiv> C corners_of S"
  by (smt nS corners_def corners_unique theI')


text \<open>Once we have a name for these points, metis is able able to untangle th
      different terminologies used in the definition of polytopes, faces, and
      simplices, and show what we really wanted to say with much less manual work:\<close>

lemma face_of_simplex_simplex:
  assumes F: "F face_of S" and k: "aff_dim F = k"
  shows "k simplex F"
proof -
  from nS obtain SC where SC: "SC corners_of S" using corners_of_def simplex_def
    by (metis (no_types, hide_lams) aff_dim_affine_independent
        aff_dim_convex_hull aff_independent_finite)
  with F obtain FC where FC: "FC corners_of F"
    by (metis (no_types, hide_lams) aff_dim_affine_independent
        aff_dim_convex_hull aff_independent_finite
        affine_independent_subset corners_of_def
        face_of_convex_hull_affine_independent)
  thus "k simplex F"  by (metis FC corners_of_def k simplex_def)
qed





subsection \<open>Count of faces\<close>

text \<open>We will show that \<open>k d_face_count S = (n+1) choose (k+1)\<close> for all \<open>n simplex S\<close>,
    as there are (n+1) corners, and each k-dimensional face encloses (k+1) of them.\<close>


subsubsection "correspondence between faces and sets of corners"


lemma sub_corners_simplex_face:
  \<comment> \<open>Any subset of the corners of a simplex is sufficient to form a new simplex.\<close>
  assumes C: "C \<subseteq> corners S" and k: "int(card C) = k+1"
  obtains F where "F = convex hull C" and "F face_of S" and "k simplex F"
proof
  obtain C1 where C1: "C1 corners_of S" using corners_exist by auto
  from C1 have CC1: "C \<subseteq> C1" by (metis C corners_def corners_unique nS theI)
  let ?F = "convex hull C"
  show 0: "?F = convex hull C" by simp
  thus 1: "?F face_of S" using C1 CC1 corners_of_def
    by (metis face_of_convex_hull_affine_independent)
  show 2: "k simplex ?F" unfolding simplex_def
  proof (intro exI conjI)
    show "\<not> affine_dependent C"
      using C1 CC1 affine_independent_subset corners_of_def by blast
    show "int (card C) = k + 1" by (fact k)
    show "?F = convex hull C" by (fact 0)
  qed
qed



lemma ex1_corresponding_face:
  assumes C: "C \<subseteq> corners S"
  shows "\<exists>!F. F = convex hull C \<and> F face_of S \<and> (int(card C)-1) simplex F"
proof -
  let ?k = "(int(card C)-1)"
  have "card C = ?k+1" by auto
  with C obtain F where "F = convex hull C \<and> F face_of S \<and> ?k simplex F"
    using sub_corners_simplex_face by blast
  thus ?thesis by blast
qed


definition corresponding_face where
  "corresponding_face C \<equiv> (THE F. F = convex hull C \<and> F face_of S \<and> (int(card C)-1) simplex F)"
  if "C \<subseteq> corners S"


lemma corresponding_face:
  assumes "C \<subseteq> corners S"
  shows "(F = corresponding_face C) \<equiv>
         (F = convex hull C \<and> F face_of S \<and> (int(card C)-1) simplex F)"
  using assms corresponding_face_def ex1_corresponding_face
  by (smt the_equality)


subsubsection "More simplex helpers."

text "Here are few lemmas I thought I'd need while I was building up to the proof above."


lemma card_simplex_corners0:
  assumes S: "n simplex S" and C: "C corners_of S"
  shows "int(card C) = n+1"
\<comment> \<open>Once I defined corresponding corners, metis can figure this out on its own.\<close>
proof -
  from S have "aff_dim S = n" by (simp add: aff_dim_simplex)
  thus "int(card C) = n + 1" using corners_of_def C by auto
qed


lemma simplex_corners_of_face:
  assumes "n simplex S" and F: "F face_of S"
    and SC: "SC corners_of S" and FC: "FC corners_of F"
  shows "FC \<subseteq> SC"
proof
  fix x assume "x\<in>FC"
  with F FC SC show "x\<in>SC" using corners_of_def
    by (metis (full_types) extreme_point_of_face
        extreme_point_of_convex_hull_affine_independent)
qed

lemma simplex_face_of_corners:
  assumes "n simplex S"
      and "SC corners_of S" and "FC corners_of F"
      and "FC \<subseteq> SC"
  shows "F face_of S"
  by (metis assms(2) assms(3) assms(4) corners_of_def face_of_convex_hull_affine_independent)


lemma obtain_corners:
  assumes "n simplex S"
  obtains C where "C corners_of S"
  by (metis (no_types, hide_lams) aff_dim_affine_independent aff_dim_convex_hull aff_independent_finite assms corners_of_def simplex_def)


lemma corners_face_equiv:
  assumes "SC corners_of S" and "FC corners_of F"
  shows "(FC \<subseteq> SC     \<and> int(card FC) = k+1)
       \<equiv> (F face_of S \<and> aff_dim F = k)"
  by (smt nS assms corners_of_def simplex_corners_of_face simplex_face_of_corners)



subsection \<open>mapping a set of corners to its corresponding face\<close>


lemma simplex_self_face:
  \<comment> \<open>Any simplex is a face of itself.\<close>
  "S face_of S" using nS convex_simplex face_of_refl by auto


lemma n_simplex_only_n_face:
  \<comment> \<open>The only n dimensional face of an n simplex S is S itself.\<close>
  shows "n d_faces S = {S}"
proof
  let ?F = "n d_faces S"
  have "?F \<subseteq> {f. f face_of S \<and> aff_dim f = n}" using d_faces_def by auto
  hence "?F \<subseteq> {f. f face_of S}" by auto
  thus "?F \<subseteq> {S}" by (smt nS aff_dim_simplex convex_simplex
      d_faces_def face_of_aff_dim_lt insertCI mem_Collect_eq simplex_def subsetI)
  show "{S} \<subseteq> n d_faces S"
    using nS simplex_self_face aff_dim_simplex d_faces_def by blast
qed



subsection "---- proven simplex stuff but probably garbage ------"

lemma ex1_face_corners:
  assumes "F face_of S"
  shows "\<exists>!c. c = corners F"
  by simp



lemma unique_face:
  assumes "F face_of S" and "c0 corners_of F" and "c1 corners_of F"
  shows "c0 = c1"
  using Poly100.corners_equiv assms face_of_simplex_simplex simplex_dim_ge by blast


lemma unique_corners:
  assumes "C \<subseteq> corners S"
      and "F0 face_of S \<and> F0 = convex hull C"
      and "F1 face_of S \<and> F1 = convex hull C"
      and "F face_of S" and "c0 corners_of F" and "c1 corners_of F"
  shows "c0 = c1"
  using Poly100.corners_equiv assms face_of_simplex_simplex simplex_dim_ge by blast



subsection "---- unproven simplex stuff ------"


lemma corner_face_equiv:
  assumes "SC corners_of S"
    and "c0 \<subseteq> SC" and "f0 = corresponding_face c0"
    and "c1 \<subseteq> SC" and "f1 = corresponding_face c1"
  shows "c0 = c1 \<longleftrightarrow> f0 = f1"
proof
  show "c0 = c1 \<Longrightarrow> f0 = f1" by (simp add: assms(3) assms(5))
  show "f0 = f1 \<Longrightarrow> c0 = c1"
    using nS assms
          corners_def corners_of_def Poly100.corners_unique
          corresponding_face ex1_corresponding_face the_equality
    by (metis (no_types, lifting)
          simplex_dim_ge
          aff_dim_affine_independent  aff_dim_convex_hull
          aff_independent_finite affine_independent_subset)
qed

\<^cancel>\<open>

  \<comment> \<open>TODO: make this proof explicit. it takes a really long time to run.\<close>

  lemma exists_corresponding_corners:
    assumes "F face_of S"
    shows "\<exists>!C. C \<subseteq> corners S \<and> F = corresponding_face C"
    using nS assms simplex_dim_ge
         face_of_simplex_simplex simplex_corners_of_face
         corners_def corners_of_def Poly100.corners_unique
         corresponding_face unique_corresponding_face the_equality
         aff_dim_affine_independent aff_dim_convex_hull
         aff_independent_finite affine_independent_subset
    by (metis (no_types, lifting))
\<close>

\<^cancel>\<open> recall:
  "corresponding_face C \<equiv> (THE F. F = convex hull C \<and> F face_of S \<and> (int(card C)-1) simplex F)"
  if "C \<subseteq> corners S" \<close>

definition corresponding_corners0 where
  "corresponding_corners0 F \<equiv> (THE C. F = corresponding_face C)"
  if "F face_of S"

definition corresponding_corners1 where
  "corresponding_corners1 F \<equiv> (THE C. C \<subseteq> corners S \<and> F = convex hull C)"
  if "F face_of S"


definition corresponding_corners where
  "corresponding_corners F \<equiv> (THE C. C \<subseteq> corners S \<and> F = corresponding_face C)"
  if "F face_of S"


lemma unique_aff_dim_convex_hull:
  assumes 0: "\<not>affine_dependent C0"
      and 1: "\<not>affine_dependent C1"
      and 2: "convex hull C0 = convex hull C1"
      and 3: "aff_dim C0 = aff_dim C1"
    shows "C0 = C1"
  by (metis 0 1 2 subsetI subset_antisym
      extreme_point_of_convex_hull_affine_independent)

lemma simplex_face_equiv:
  assumes F: "F face_of S"
      and "C0 \<subseteq> corners S"
      and "C1 \<subseteq> corners S"
      and "convex hull C0 = convex hull C1"
    shows "C0 = C1"
  using nS assms unique_aff_dim_convex_hull face_of_simplex_simplex
  by (metis aff_dim_convex_hull affine_independent_subset corners_are_corners_of corners_of_def)


\<comment> \<open>this parallels @{thm ex1_corresponding_face}\<close>
lemma ex1_corresponding_corners:
  assumes F: "F face_of S"
  shows "\<exists>!C. C \<subseteq> corners S \<and> F = corresponding_face C"
proof -
  obtain FC where FC: "FC \<subseteq> corners S \<and> F = convex hull FC"
    using nS F face_of_simplex_simplex
    by (metis (no_types, lifting) aff_dim_affine_independent
          aff_dim_convex_hull aff_independent_finite assms
          corners_def corners_of_def corners_unique
          simplex_corners_of_face simplex_def the_equality)
  obtain FC' where CF: "FC' \<subseteq> corners S \<and> F = corresponding_face FC'"
    using FC corresponding_face by auto
  thus "\<exists>!C. C \<subseteq> corners S \<and> F = corresponding_face C"
    by (metis corner_face_equiv corners_def corners_unique nS the_equality)
qed


lemma face_corners_are_simplex_corners:
  assumes F: "F face_of S"
  shows "corners F \<subseteq> corners S" unfolding corners_def
  by (meson nS F Poly100.corners_are_corners_of
            face_of_simplex_simplex simplex_corners_of_face simplex_dim_ge)

lemma corresponding_corners:
  assumes F: "F face_of S"
  shows "(C = corresponding_corners F)
     \<longleftrightarrow> (C \<subseteq> corners S \<and> F = corresponding_face C)"
proof -
  from F show ?thesis
  by (smt corners_def
      Poly100.corners_exist corners_unique
      corresponding_corners_def ex1_corresponding_corners
      corresponding_face simplex_dim_ge the_equality)
qed

lemma corner_face_inj:
  assumes C0: "C0 \<subseteq> corners S" and F0: "F0 = corresponding_face C0"
      and C1: "C1 \<subseteq> corners S" and F1: "F1 = corresponding_face C1"
  shows "C0 = C1 \<longleftrightarrow> F0 = F1"
  using nS assms corresponding_corners corresponding_face by metis

lemma corresponding_face_inj:
  "inj_on (corresponding_face) {C. C \<subseteq> corners S}"
  using corner_face_equiv corners_are_corners_of inj_on_def by fastforce

lemma corresponding_face_bij:
  shows "bij_betw (corresponding_face) {fc. fc \<subseteq> corners S} {f. f face_of S}"
proof -
  let ?ps = "{fc. fc \<subseteq> corners S}" \<comment> \<open>power set of corners\<close>
  let ?fs = "{f. f face_of S}" \<comment> \<open>set of all faces\<close>

  have 0: "inj_on (corresponding_face) ?ps"
    using  corner_face_inj inj_on_def by (metis (no_types) mem_Collect_eq)
  have 1: "\<forall>f\<in>?fs. \<exists>c\<in>?ps. f = corresponding_face c"
    using ex1_corresponding_corners by blast

  have 2: "inj_on (corresponding_corners) ?fs"
    by (smt corresponding_corners inj_on_def mem_Collect_eq)
  have 3: "\<forall>c\<in>?ps. \<exists>f\<in>?fs. c = corresponding_corners f"
    by (metis corresponding_corners corresponding_face mem_Collect_eq)

  from 0 1 2 3 have  "(corresponding_face)`?ps = ?fs"
    using corresponding_corners by auto
  thus ?thesis using corresponding_face_inj inj_on_imp_bij_betw by fastforce
qed


lemma corresponding_face_card_inj:
  assumes C0: "C0 \<subseteq> corners S \<and> card C0 = n" and F0: "F0 = corresponding_face C0"
      and C1: "C1 \<subseteq> corners S \<and> card C1 = n" and F1: "F1 = corresponding_face C1"
    shows "C0 = C1 \<longleftrightarrow> F0 = F1"
  using nS assms corresponding_corners corresponding_face by metis


lemma card_corners_and_faces:
  shows "card {fc. fc \<subseteq> corners S} = card {f. f face_of S}"
  using bij_betw_same_card corresponding_face_bij by auto


lemma card_simplex_corners:
  "card(corresponding_corners S) = n+1"
  by (metis nS aff_dim_simplex corresponding_corners corresponding_face
          diff_add_cancel simplex_self_face)

lemma corners_are_corresponding:
  assumes "F face_of S"
  shows "corners F = corresponding_corners F"
  by (metis (no_types, hide_lams) Poly100.corners_are_corners_of assms
      corners_of_def corresponding_corners corresponding_face nS
      simplex_corners_of_face simplex_dim_ge)

lemma corners_of_are_corresponding:
  assumes "F face_of S"
  shows "FC corners_of F \<longleftrightarrow> FC = corresponding_corners F"
  by (metis (full_types) Poly100.corners_are_corners_of Poly100.face_of_simplex_simplex assms corners_are_corresponding nS simplex_dim_ge)

lemma corners_of_face_are_corners:
  assumes "F face_of S"
  shows "FC = corners F \<longleftrightarrow> FC corners_of F"
  by (metis assms corners_of_are_corresponding corners_def face_of_simplex_simplex the_equality)


lemma face_subset_equiv:
  "F face_of S \<longleftrightarrow> (\<exists>k. k simplex F \<and> corners F \<subseteq> corners S)"
\<comment> \<open>TODO: why doesn't this follow automatically from @{thm corners_face_equiv}
       or @{thm corresponding_corners}?\<close>
\<comment> \<open>TODO: maybe I can define \<open>is_simplex\<close> and not have to worry about the dimension?
    currently, it's required for the second "show" step of the proof\<close>
proof
  define sc where sc: "sc = corners S"
  define fc where fc: "fc = corners F"
  from nS sc have sc_of: "sc corners_of S" using corners_of_face_are_corners simplex_self_face by auto
  show "F face_of S \<Longrightarrow> (\<exists>k. k simplex F \<and> fc \<subseteq> sc)"
  proof -
    assume F: "F face_of S"   define k where k: "k = aff_dim F"
    from F fc have "fc corners_of F" using corners_of_face_are_corners by auto
    with F sc_of have "fc \<subseteq> sc" using simplex_corners_of_face using nS by blast
    moreover from F k have "k simplex F" using face_of_simplex_simplex by auto
    ultimately have "k simplex F \<and> fc \<subseteq> sc" by auto
    thus ?thesis ..
  qed
  show "(\<exists>k. k simplex F \<and> fc \<subseteq> sc) \<Longrightarrow> F face_of S"
  by (metis Poly100.corners_are_corners_of corners_of_def ex1_corresponding_face fc sc simplex_dim_ge)
qed

lemma card_corresponding_corners:
  assumes "F face_of S"
  shows "card(corresponding_corners F) = (aff_dim F)+1"
  using assms face_of_simplex_simplex card_simplex_corners
    by (metis (no_types, hide_lams)  add.commute assms corners_of_are_corresponding corners_of_def )


lemma finite_corners: "finite (corners S)"
  using corners_are_corners_of corners_of_def by auto


lemma subset_choose:
  assumes "finite X"
  shows "card {Y. Y \<subseteq> X \<and> card(Y) = k} = ((card X) choose k)"
  using assms Binomial.n_subsets by auto


lemma card_faces_and_subsets:
  "{(f,c). f face_of S  \<and> c = corresponding_corners f} =
   {(f,c). c \<subseteq> corners S \<and> f = corresponding_face c }"
  by (metis corresponding_corners corresponding_face)

lemma faces_and_subsets_dim:
  assumes "k \<ge> -1"
  shows "(f face_of S \<and> c = corresponding_corners f \<and> aff_dim f = k)
    \<longleftrightarrow>  (c \<subseteq> corners S \<and> f = corresponding_face c \<and> card c = nat(k+1))"
  by (smt aff_dim_simplex assms corresponding_corners corresponding_face int_nat_eq of_nat_eq_iff)

lemma card_faces_and_subsets_dim:
  assumes "k \<ge> -1"
  shows "{(f,c). f face_of S \<and> c = corresponding_corners f \<and> aff_dim f = k}
       = {(f,c). c \<subseteq> corners S \<and> f = corresponding_face c \<and> card c = nat(k+1)}"
  using assms card_faces_and_subsets faces_and_subsets_dim by auto


\<comment> \<open>same as @{thm corresponding_face_bij}, but this time add the cardinality predicates}\<close>
lemma corresponding_face_dim_bij:
  shows "bij_betw (corresponding_face) {c. c \<subseteq> corners S \<and> card c = k}
                                       {f. f face_of S \<and> aff_dim f = int(k)-1 }"
proof -
  let ?cs = "{c. c \<subseteq> corners S \<and> card c = k }"
  let ?fs = "{f. f face_of S \<and> aff_dim f = int(k)-1 }"
  let ?cf = "corresponding_face"

  have 0: "inj_on (?cf) ?cs"
    using  corresponding_face_card_inj inj_on_def
    by (metis (mono_tags, lifting) corresponding_face_inj inj_onD inj_onI mem_Collect_eq)
  have 1: "\<forall>f\<in>?fs. \<exists>c\<in>?cs. f = ?cf c"
    by (smt aff_dim_affine_independent aff_dim_convex_hull aff_dim_simplex
            affine_independent_subset corners_are_corners_of
            corners_of_def corners_unique corresponding_face
            ex1_corresponding_face ex1_corresponding_corners
            mem_Collect_eq nat_int)
  have 2: "inj_on (corresponding_corners) ?fs"
    by (smt corresponding_corners inj_on_def mem_Collect_eq)
  have 3: "\<forall>c\<in>?cs. \<exists>f\<in>?fs. c = corresponding_corners f"
    using Poly100.faces_and_subsets_dim mem_Collect_eq nS
    by (smt aff_dim_simplex corresponding_corners corresponding_face)
  from 0 1 2 3 have 4: "(?cf)`?cs = ?fs" using corresponding_corners by auto
  hence "inj_on ?cf ?cs \<Longrightarrow> (?cf)`?cs = ?fs \<Longrightarrow> bij_betw ?cf ?cs ?fs"
    using bij_betw_imageI[of ?cf ?cs ?fs] by simp
  with 0 4 show "bij_betw (?cf) ?cs ?fs" by blast
qed


lemma card_simplex_faces:
  assumes "k \<ge> -1"
  shows "k d_face_count S = (nat(n+1) choose nat(k+1))"
proof -
  define nc where nc: "nc = nat(k+1)"
  have k1nc: "k+1 = nc" using assms nc by auto
  have "k d_face_count S = card {f. f face_of S \<and> aff_dim f = k}"
    unfolding d_face_count_def d_faces_def ..
  also have "... = card {c. c \<subseteq> corners S \<and> card(c) = nc}"
  proof -
    have "\<forall>n. card {A. A \<subseteq> corners S \<and> card A = n} = card {A. A face_of S \<and> aff_dim A = int n - 1}"
      using bij_betw_same_card corresponding_face_dim_bij by blast
    moreover have "int nc = 1 + k" by (metis add.commute k1nc)
    ultimately show ?thesis by simp
  qed
  also have  "... = (card (corners S) choose nc)"
    using nc finite_corners Binomial.n_subsets by simp
  finally show "k d_face_count S = (nat(n+1) choose nc)"
    by (metis card_simplex_corners0 corners_are_corners_of nS nat_int)
qed


end

(* ------------------------------------------------------------------------ *)
section \<open>The Euler characteristic for Simplices.\<close>
(* ------------------------------------------------------------------------ *)

text "The Euler characteristic is the alternating sum \<open>-x\<^sub>-\<^sub>1 + x\<^sub>0 - x\<^sub>1 + x\<^sub>2 \<dots> \<plusminus> x\<^sub>n\<close>
      of the number of n-dimensional faces."

definition euler_char where
  "euler_char p = (\<Sum>k\<le>nat(aff_dim p+1). (-1::int)^k * (int(k)-1) d_face_count p)"

text \<open>For example, in a triangle, we have:

    k | n  |\<open>x\<^sub>n\<close>|
    --+----+----+------------
    0 | -1 | 1  | empty face
    1 |  0 | 3  | vertices
    2 |  1 | 3  | edges
    3 |  2 | 1  | surface

The alternating sum of \<open>x\<^sub>n\<close> (and therefore the Euler characteristic) is:  -(1) + 3 - 3 + 1 = 0\<close>



subsection \<open>The empty face\<close>

text \<open>The empty set is considered to be a face of any polytope,
      and its affine dimension is -1, but we don't actually count
      it in the sum.\<close>

lemma "S = {} \<longleftrightarrow> aff_dim S = -1"
  by (fact Convex_Euclidean_Space.aff_dim_empty)

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

subsection \<open>Euler characteristic for an n-Simplex.\<close>


text \<open>From all the simplex work above, we have a bijection between
faces of an n-simplex and subsets of its n+1 corners.\<close>

text \<open>There are (n+1 choose k) ways to select k corners, so there are
(n+1 choose k) distinct faces with aff_dim (k-1).\<close>

text \<open>When we plug these numbers into the Euler relation, we get a sequence that
always sums to 0.\<close>

text \<open>However, we have a small off-by-one error to contend with:
  @{thm Binomial.choose_alternating_sum} requires \<open>n>0\<close> when it would
  really apply to \<open>n\<ge>0\<close>... So we have to prove the 0 case separately.\<close>

text \<open>This actually worked out okay for me: getting these two cases to
    both work out to zero forced me to rework and clarify a whole lot of
    the theory behind counting simplex corners.\<close>

lemma euler_0simplex_eq0:
  assumes "0 simplex S"
  shows "euler_char S = 0"
proof -
  have neg1: "(-1) d_face_count S = 1"
    by (simp add: empty_face_count)
  have zero: "0 d_face_count S = 1"
    by (simp add: n_simplex_only_n_face assms d_face_count_def)
  define N1 where N: "N1 = nat(0+1)"

  \<comment> \<open>Now plug these results into the definition, and calculate.\<close>
  hence "euler_char S = (\<Sum>k\<le>N1. (-1::int)^k * (int(k)-1) d_face_count S)"
    by (metis (full_types) aff_dim_simplex assms euler_char_def)
  also have "... = (-1::int)^0 * (int(0)-1) d_face_count S
                 + (-1::int)^1 * (int(1)-1) d_face_count S"
    using N by simp
  finally show "euler_char S = 0" using neg1 zero by simp
qed

lemma euler_nsimplex_eq0:
  assumes "n simplex S" "n\<ge>0"
  shows "euler_char S = 0"
proof -
  define N1 where N1: "N1 = nat(n+1)"
  hence "euler_char S = (\<Sum>k\<le>N1. (-1::int)^k * (int(k)-1) d_face_count S)"
    using N1 assms aff_dim_simplex assms euler_char_def by blast
  also have "... = (\<Sum>k\<le>N1. (-1::int)^k * (N1 choose k))"
    using assms N1 card_simplex_faces
    by (smt One_nat_def Suc_nat_eq_nat_zadd1 add.right_neutral add_Suc_right int_nat_eq nat_int sum.cong)
  finally show "euler_char S = 0"
    using N1 Binomial.choose_alternating_sum by (smt assms(2) nat_0_iff neq0_conv sum.cong)
qed


section \<open>Simplication\<close>

text \<open>is_simplicate. v. To make a system more complex so that the use of the system is easier or simpler.\<close>

text \<open>In this case, I'm also using the word to mean the process of forming a simplical complex
or triangulation.\<close>

text \<open>Note that @{theory "HOL-Analysis.Polytope"} already provides several lemmas for
talking about this idea:

  @{thm cell_subdivision_lemma}
  @{thm cell_complex_subdivision_exists}
  @{thm simplicial_complex_def}
  @{thm triangulation_def}

We'll make use of this machinery below, but in particular, we want to set things
up so we can reason inductively about the process, showing that at any step along
the way, some particular property holds.

(We will use this induction-by-triangulation tactic twice in this paper:
first to prove that the euler characteristic is 0 for all polyhedra, and then
later to derive Pick's theorem for the area of a polygon on \<open>\<int>\<^sup>2\<close>.\<close>


text \<open>We define the concept of a cutting a polyhedron (really any ordered set) into two parts:\<close>

text \<open>In particular, we want to cut our space (and any unlucky polyhedra that happen to be
     in it) by means of a hyperplane. A hyperplane is just the n-dimensional equivalent
     of a plane that cuts a 3d space into two halves. (Or a line that cuts a plane, etc.)

    TODO: describe inner product, and what this set notation means. \<close>

subsection "definitions"

default_sort euclidean_space

definition is_simplex where
  "is_simplex p \<equiv> (\<exists>n. n simplex p)"

lemma is_simplex [simp]:
  "is_simplex p \<longrightarrow> (\<exists>n. n simplex p)"
  using is_simplex_def by auto

typedef (overloaded) 'a Polytope
  = "{p::'a set. polytope p}"
  using polytope_empty by auto

typedef (overloaded) 'a Simplex
  = "{s::'a set. polytope s \<and> is_simplex s}"
  using is_simplex_def polytope_sing by fastforce

(* https://stackoverflow.com/questions/26860637/how-type-casting-is-possible-in-isabelle *)
consts cast_simplex_polytope :: "'a Simplex \<Rightarrow> 'a Polytope"
consts cast_polytope_set :: "'a Polytope \<Rightarrow> 'a set"
declare
  [[coercion_enabled]]
  [[coercion cast_simplex_polytope]]
  [[coercion cast_polytope_set]]

typedef (overloaded) 'a hyperplane
  = "{h::'a set. \<exists>a b. h = {x. a \<bullet>x = b}}"
  by blast

definition cut_of ("_ cut'_of _" [70,70] 75) where
  "H cut_of P \<equiv> ({x\<in>P. x\<le>H}, {x\<in>P. x\<ge>H})"

typedef (overloaded) 'a cut_fn
  = "{fn::('a Polytope \<Rightarrow> 'a hyperplane). True}"
  by blast

declare
  [[typedef_overloaded]]

datatype ('a,'c) Plex
  = Simp "'a Simplex"
  | Join 'c "('a,'c) Plex" "('a,'c) Plex"

fun plex :: "('a, 'c) Plex \<Rightarrow> 'a set" where
  "plex (Simp x) = x" |
  "plex (Join _ a b) = plex a \<union> plex b"

fun is_simplicate :: "('a,'c) Plex \<Rightarrow> bool" where
  "is_simplicate (Simp x) = True" |
  "is_simplicate (Join _ a b) \<longleftrightarrow> (is_simplicate a) \<and> (is_simplicate b)
                \<and> (\<exists>!f. f facet_of plex a \<and> f facet_of plex b)"

typedef (overloaded) ('a,'c) simplication
  = "{cp::('a,'c) Plex. is_simplicate cp}"
  by (meson mem_Collect_eq is_simplicate.simps(1))

definition simplicates :: "('a,'c) Plex \<Rightarrow> 'a Polytope \<Rightarrow> bool" ("_ simplicates _" [80,80] 85) where
  "X simplicates Y \<longleftrightarrow> (is_simplicate X) \<and> (plex X = Y)"

locale cplex =
  fixes cut:: "'a set \<Rightarrow> 'cut"
    and app:: "'cut \<Rightarrow> 'a set \<Rightarrow> ('a set \<times> 'a set)"
    and glu:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_ \<triangle> _" [60,60] 65)
 assumes inv: "(\<exists>c. app c x = (a,b)) \<longleftrightarrow> (a \<triangle> b = x)"
begin

  lemma induct0:
    assumes k: "polytope k" "aff_dim k = d"
        and 0: "\<And>s. d simplex s \<Longrightarrow> P(s)"
        and 1: "P(a) \<and> P(b) \<Longrightarrow> P(a \<triangle> b)"
      shows "P(k)"
  proof (cases "is_simplex k")
    case True
      then have "is_simplex k" .
      hence "d simplex k" using is_simplex[of k] k aff_dim_simplex by blast
      with 0[of k] show ?thesis by simp
  next
    case False
      fix a b assume "(a,b) = app (cut k) k"
    \<comment> \<open>Here is where I need induction to magically kick in...
       Somehow I have to be able to show that for any polytope,
       I can eventually keep cutting it and obtain nothing
      but simplices.\<close>
  oops

  lemma induct1:
    assumes 0: "d simplex s \<Longrightarrow> P(s)"
        and 1: "P(a) \<Longrightarrow> P(a \<triangle> b)"
        and k: "polytope k" "aff_dim k = d"
    shows "P(cplex_of cut k x)"
  sorry

end



lemma induct_plex [case_names simp join]:
  assumes "\<And>s. P(plex(Simp s))"
      and "\<And>a b f. P(plex a) \<and> P(plex b) \<Longrightarrow> P(plex(Join f a b))"
    shows "c simplicates k \<Longrightarrow> P(k)"
sorry


text \<open>The following is nonsense and doesn't work. I'm just trying to figure out the general structure
   of what I want to be able to say.\<close>
(*
consts neat :: "'a set \<Rightarrow> bool"
lemma test_induct_plex:
  assumes "d simplex s \<Longrightarrow> neat s"
     and "c simplicates k"
  shows "neat k"
proof (induction k rule:induct_plex)
    case (simp s)
    then show ?case sorry
  next
    case (join a b f)
    then show ?case sorry
  qed
qed
*)

subsection\<open>Half-spaces\<close>

text\<open>A polyhedron (and therefore a polytope) is the intersection of a finite set of half-spaces.\<close>

definition halfspaces_of :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" ("_ halfspaces'_of _" [60,60] 65) where
  "HF halfspaces_of S \<equiv> finite HF \<and>
                      S = (affine hull S) \<inter> \<Inter> HF \<and>
                      (\<forall>h \<in> HF. \<exists>a b. a\<noteq>0 \<and> h = {x. a \<bullet> x \<le> b})"

lemma polyhedron_halfspaces:
  assumes "polyhedron T" obtains HF where "HF halfspaces_of T"
  by (metis assms halfspaces_of_def polyhedron_Int_affine)

lemma polytope_halfspaces:
  assumes "polytope T" obtains HF where "HF halfspaces_of T"
  by (metis assms polyhedron_halfspaces polytope_imp_polyhedron)

theorem extending_hyperplanes:
  assumes "polyhedron T" "F facet_of T" "HF halfspaces_of F" "HT halfspaces_of T"
  shows "HF \<subseteq> HT"
  using assms face_of_def face_of_polyhedron_polyhedron face_of_polyhedron_explicit
  unfolding halfspaces_of_def polyhedron_def facet_of_def
  oops


text\<open>The important feature here is that a point is an element of the polyhedron if and only if
     that point is in all of the polyhedron's half-spaces.\<close>

theorem aff_elements_of_halfspaces:
  assumes "HF halfspaces_of S" "x\<in>(affine hull S)"
  shows "x\<in>S \<longleftrightarrow> (\<forall>h\<in>HF. x\<in>h)"
  by (metis assms halfspaces_of_def Int_iff Inter_iff)

text\<open>In particular, if some point P is co-hyperplanar with of a facet of polytope S
     (and thus an element of one of its half-spaces), but \<open>P\<notin>S\<close>, then we can deduce
     the existence of some other half-space of S that doesn't contain P either.\<close>

corollary pointless_halfspace: \<comment> \<open> ;) \<close>
  assumes "HF halfspaces_of T" "H\<^sub>0 \<in> HF" "P\<in>(affine hull T) \<and> P\<in>H\<^sub>0 \<and> P\<notin>T"
  obtains H\<^sub>1 where "H\<^sub>1\<in>HF \<and> P\<notin>H\<^sub>1"
  using assms aff_elements_of_halfspaces by metis

subsection\<open>Adjacent facets\<close>

definition adjacent_by :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  ("_ _ adjacent'_by _" [60,60,60] 65) where
  "x y adjacent_by f \<equiv> x\<noteq>y \<and> f facet_of x \<and> f facet_of y"

definition adjacent :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "adjacent x y \<equiv> (\<exists>f. x y adjacent_by f)"

lemma adjacent_facet_exists:
  assumes T:"polytope T"
      and F:"F facet_of T" and E:"E facet_of F"
  shows "\<exists>F'. F F' adjacent_by E"
  \<comment> \<open>Every edge of a polygon shares a vertex with another edge,
      every face of a 3d polytope shares an edge with another face, etc.\<close>
proof -
  from T have phT: "polyhedron T" using polytope_imp_polyhedron by auto
  from F E have E0:"E face_of T" using face_of_trans facet_of_imp_face_of by blast
  moreover have E1:"E \<noteq> {} \<and> E\<noteq>T " using E F facet_of_def by auto
  ultimately have E2:"E = \<Inter>{F'. F' facet_of T \<and> E \<subseteq> F'}"
    using phT face_of_polyhedron by blast
  then obtain Fs where Fs:"Fs = {F'. F' facet_of T \<and> E \<subseteq> F'} \<and> E=\<Inter>Fs" by auto
  then obtain F' where F':"F'\<in>Fs \<and> F'\<noteq>F"
    by (metis E Inf_greatest facet_of_imp_subset facet_of_irrefl order_refl subset_antisym)
  hence "E facet_of F'"
    by (smt Collect_mem_eq Collect_mono_iff E F Fs E0 E1 E2
        equalityE face_of_face facet_of_def facet_of_imp_face_of le_Inf_iff)
  hence "F'\<noteq>F \<and> (E facet_of F') \<and> (F' facet_of T)" using F' Fs by blast
  with E show ?thesis using adjacent_by_def by blast
qed


lemma adjacent_faces_simplex:
  "d simplex S \<equiv> \<forall>x\<in>facets S. \<forall>y\<in>facets S. (x\<noteq>y \<longleftrightarrow> adjacent x y)"
  sorry

lemma count_adjacent_faces:
  assumes "polytope T" "F facet_of T"
  shows "card(facets F) = card {x\<in>facets T. adjacent x F}"
  sorry



proposition polyhedron_facets:
  assumes "polytope K" and "aff_dim K = d"
  shows "card (facets K) \<ge> d+1"
  sorry

corollary simplex_facets:
  "d simplex K \<equiv> polytope K \<and> aff_dim K = d \<and> card (facets K) = d+1"
  sorry


lemma verts_exist:
  assumes T:"polytope T" "aff_dim T > 1"
      and F:"F facet_of T"
    shows "\<exists>V. V\<in>verts F"
  unfolding verts_def d_faces_def
  sorry


lemma verts_transitive:
  assumes "F facet_of T" "V \<in> verts F"
  shows "V \<in> verts T"
  unfolding verts_def facet_of_def using assms
  by (metis (no_types, lifting) d_faces_def face_of_face facet_of_imp_face_of mem_Collect_eq verts_def)

subsection \<open>Tverberg's Method\<close>

text \<open>Adapted from \<^emph>\<open>How to cut a convex polytope into simplices\<close> by Helge Tverberg\<close>

lemma tv1a:
  assumes cp: "polytope K" and d:"aff_dim K = d"
  fixes F assumes "F \<in> faces K"
  shows "is_simplex K \<or> d\<ge>2"
proof (cases "d<2")
  case True hence "is_simplex K"
    using is_simplex_def cp d polytope_lowdim_imp_simplex by fastforce
  thus ?thesis ..
next
  case False thus ?thesis by simp
qed

lemma tv1:
  assumes T: "polytope T"  "\<not> is_simplex T"
  shows "\<exists>F\<^sub>1 F\<^sub>2 V. V \<in> verts T \<and> F\<^sub>1\<noteq>F\<^sub>2 \<and>
          F\<^sub>1 facet_of T \<and> \<not>(V \<subseteq> F\<^sub>1) \<and>
          F\<^sub>2 facet_of T \<and> \<not>(V \<subseteq> F\<^sub>2)"
proof -   (* TODO: induction on "card(facets)" *)

  (* -- direct translation from tverberg to psuedocode -- *)

  (* if card(facets) < 4 then k is already a simplex *)
  (* else *) let ?dim = "aff_dim T"
  consider
    (1) "\<exists>v\<in>verts T. of_nat(card {f. f facet_of T \<and> v\<in>verts f}) > aff_dim T" |
    (2) "\<forall>v\<in>verts T. of_nat(card {f. f facet_of T \<and> v\<in>verts f}) = aff_dim T"
    sorry
  then have ?thesis proof (cases)
    case 1
      \<comment> \<open>have H separating P from other vertices of K\<close>
      \<comment> \<open>hence intersection HK of of H and K
            and HK is a (d-1)-polytope
            and HK is not a simplex
            and HK has fewer facets than K\<close>
      \<comment> \<open>hence dissection of HKD HK by cuts in H (by induction hypothesis)\<close>
      \<comment> \<open>then for each d-2 hyperplane in HKD, extend to the d-1 hyperplane through P\<close>
      \<comment> \<open>then obtain a dissection of K into polytopes K0..Kn\<close>
      \<comment> \<open>for each Ki in K0..Kn:
            Ki is a (d) polytope
            Ki has fewer facets than K\<close>
      \<comment> \<open>hence we can break it down recursively\<close>
    then show ?thesis sorry
  next
    case 2  \<comment> \<open>At each vertex of K only d facets meet\<close>
      \<^cancel>\<open>obtain F1 F2 P by induction\<close>
    then show ?thesis sorry
  qed

  (* -- meanwhile, structure of what i have to show -- *)
  from T have dim1: "aff_dim T > 1"
    using aff_dim_negative_iff tv1a by fastforce
  hence dim0: "aff_dim T > 0" by auto
  with T obtain F0 where F0: "F0 facet_of T"
    using polytope_facet_exists by blast
  with T dim1 obtain V where  V:"V \<in> verts F0"
    using verts_exist by blast

  obtain F\<^sub>1 where "F\<^sub>1 facet_of T" and "\<not>(V \<subseteq> F\<^sub>1)" sorry
  obtain F\<^sub>2 where "F\<^sub>2 facet_of T" and "F\<^sub>2 \<noteq> F\<^sub>1" and "\<not>(V \<subseteq> F\<^sub>2)" sorry

  from F0 V have "V \<in> verts T" using verts_transitive by auto
  moreover have "F\<^sub>1 facet_of T" and "\<not>V \<subseteq> F\<^sub>1" sorry
  moreover have "F\<^sub>2 facet_of T" and "\<not>V \<subseteq> F\<^sub>2" sorry
  moreover have "F\<^sub>1 \<noteq> F\<^sub>2" and "\<not>V \<subseteq> F\<^sub>2" sorry
  ultimately show ?thesis by blast
qed

\<^cancel>\<open>
    \<comment> \<open>facet F is a d-simplex. Therefore, it is adjacent to at least d other facets.
       These facets have other vertices (else they would only be facets of F, not of K).
       So there must be at least one vertex in K that isn't in F. Suppose there is exactly
       one. Then the other facets must also be simplices and must all meet at that vertex.
      But then K would be a simplex, and we assumed it wasn't, so there must be more than
      one vertex.



 Suppose
       d=2 and thus the other 2 facets are triangles. Then the only vertex of K not in F is
          \<close>
  fix F2 assume "F2 facet_of K" and "adjacent F1 F2"
  have "(\<exists>x\<subseteq>K. \<not>(x\<subseteq>F) \<and> \<not>(x\<subseteq>F2))" proof (rule ccontr)
    assume "\<not>(\<exists>x\<subseteq>K. \<not>(x\<subseteq>F) \<and> \<not>(x\<subseteq>F2))"
    hence "(\<forall>x\<subseteq>K. x\<subseteq>F \<or> x\<subseteq>F2)" by simp
    hence "is_simplex K" using \<open>F2 facet_of K\<close> assms(3) facet_of_imp_subset by fastforce
    with `\<not> is_simplex K` show "False" by simp
  qed
  from this obtain F3::"'a set" where "F3\<subseteq>K  \<and> \<not>(F3\<subseteq>F) \<and> \<not>(F3\<subseteq>F2)" by auto
  hence "F3 face_of K" by auto
  then have "\<exists>v. v\<in>F3" by blast
  hence assumes "compact S" "convex S" "S \<noteq> {}"
  from this obtain v where "v\<in>F3" by auto
  hence "aff_dim {v} = 0" using aff_dim_def by auto
  moreover have "{v} face_of F3" using face_of_def try0 by auto
(*    -- this is what i really want to show... (but the simpler proof above doesn't
      -- translate directly. (why not?)
      -- somehow i just need to go from a subset existing
      -- to the actual vertex so I can obtain (capital) V.
  moreover have "(\<exists>V\<in> verts K. \<not>(V\<subseteq>F) \<and> \<not>(V\<subseteq>F2))" proof (rule ccontr)
    assume "\<not>(\<exists>V\<in> verts K. \<not>(V\<subseteq>F) \<and> \<not>(V\<subseteq>F2))"
    hence "(\<forall>V\<in>verts K. V\<subseteq>F \<or> V\<subseteq>F2)" by simp
    hence "(\<forall>V\<in>verts K. V\<subseteq>K \<and> (V\<subseteq>F \<or> V\<subseteq>F2))"
      by (meson assms(3) calculation(1) dual_order.trans facet_of_imp_subset)
    hence "is_simplex K" using \<open>F2 facet_of K\<close> assms(3) facet_of_imp_subset is_simplex_def by blast
    with `\<not> is_simplex K` show "False" by simp
  qed
*)
  ultimately show ?thesis using that by auto
next
  case False
  then obtain V FF1 FF2
        where "V \<in> verts F"
          and "FF1 facet_of F" and "\<not>(V \<subseteq> FF1)"
          and "FF2 facet_of F" and "\<not>(V \<subseteq> FF2)"
      (* show that this is possible by induction from case True *) sorry
  hence "V \<in> verts K" using `V \<in> verts F` sorry
  then obtain F1 F2
        where "F1 facet_of K" and "\<not>(V \<subseteq> F1)"
          and "F2 facet_of K" and "\<not>(V \<subseteq> F2)"
      (* show that this is possible by induction from case True *) sorry
  with that show thesis using `V \<in> verts K` by simp
oops
\<close>


(* Induction from a lower bound other than zero, inspired by Manuel Eberl
https://stackoverflow.com/questions/41384146/proof-by-induction-with-three-base-cases-isabelle *)

lemma nat_induct_lower_bound [case_names lte step]:
  assumes lte:  "\<And>n. n \<le> k \<Longrightarrow> P n"  and step: "\<And>n. n \<ge> k \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
proof (induction n rule: less_induct)
  case (less x)
  have stmt: "\<lbrakk>k \<le> x - 1; x - 1 < x\<rbrakk> \<Longrightarrow> P (Suc (x - 1))" using step[OF _ less.IH[of "x-1"]] .
  then show ?case proof (cases "n\<le>k")
    case True then show ?thesis using stmt lte by force
  next
    case False then show ?thesis using stmt lte step by force
  qed
qed

\<^cancel>\<open>
theorem tverberg_dissection:
  assumes "convex K" "polytope K" "f = card (facets K)"
  obtains T where "T simplicates K"
    \<comment> \<open>Tverberg's main theorem will go here.\<close>
proof (induction f rule: nat_induct_lower_bound[of "3"])
  case (lte n)
  hence "is_simplex K"
    using facets_def is_simplex_def assms polytope_lowdim_imp_simplex
    sorry
  then show ?case sorry
next
  case (step n)
  then show ?case sorry
oops
\<close>

section \<open>Euler Characteristic for a a general full-dimensional polytope.\<close>

\<comment> \<open>

Now we know the euler characteristic for all simplices. Then, following
Tverberg or Euler or possibly just Polytope.thy, we will show that:

  a) the euler characterstic of a polytope = 0 provided it's 0 for
     the two sections you get when you slice it with a hyperplane.

  b) any polytope can be cut into simplices

\<close>

text \<open>Now we want to show that at each step along the way, the
euler characteristic remains unchange.
Putting these two things together with our proof of the characteristic
for simplices, we can then show that it holds for any polytope.\<close>

theorem euler_poincare:
  assumes "polytope p" and "aff_dim p = d"
  shows "euler_char p = 1"
  sorry

(* ------------------------------------------------------------------------ *)
section \<open>The Polyhedron Formula\<close>
(* ------------------------------------------------------------------------ *)
text \<open>The polyhedron formula is the Euler relation in 3 dimensions.\<close>

\<comment> \<open>
The euler characteristic is 0 for all non-empty simplices,
but (at least for the polyhedron forumla) we will ignore the empty
face and the face that consists of the whole simplex. That's where
the 2 comes from)
\<close>

locale convex_polyhedron =
  fixes p assumes "polytope p" and "aff_dim p = 3"
begin

definition F where "F = card(surfs p)"
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

print_context

end

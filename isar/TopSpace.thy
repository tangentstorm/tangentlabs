(* Topological Spaces
   Based on "A Bridge to Advanced Mathematics" by Dennis Sentilles
   Translated to Isar by Michal J Wallace *)
theory TopSpace
  imports Main
begin

text \<open>A topological space (X,T) is a pair where X is a set whose elements
are called the "points" of the topological space, and T is a fixed collection of
subsets of X called neighborhoods, with the following properties:\<close>

locale topspace =
    fixes X :: "'a set"
    fixes T :: "('a set) set"
    assumes A1 [simp]: "x\<in>X \<equiv> \<exists>N\<in>T. x\<in>N"
    assumes A2 [simp]: "U\<in>T \<and> V\<in>T \<and> x\<in>(U\<inter>V) \<Longrightarrow> \<exists>N\<in>T. x\<in>N \<and> N\<subseteq>(U\<inter>V)"
begin

  text \<open>A set N\<in>T which contains p\<in>X is called a neighborhood of p.\<close>

  definition nhs :: "'a \<Rightarrow> ('a set) set"
    where "nhs p \<equiv> {N\<in>T. p\<in>N}"

  text \<open>If A\<subset>X in topological space (X,T), then p\<in>X is called a \<^bold>\<open>limit point\<close>
    of A if the intersection of every neighborhood of p with A is non-empty.\<close>

  definition limpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.1 *)
    where [simp]: "limpt A p \<equiv> A\<in>T \<and> p\<in>X \<and> (A \<inter> (\<Inter> {N\<in>T. p\<in>N}) \<noteq> {})"

  text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called an \<^bold>\<open>interior point\<close>
    of A if at least one neighborhood of a is contained entirely within A.\<close>

  definition intpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.2 *)
    where [simp]: "intpt A p \<equiv> A\<in>T \<and> p\<in>A \<and> (\<exists>N\<in>T. N\<subset>A)"

  definition boundpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.3 *)
    where "boundpt A p \<equiv> (limpt A p) \<and> (limpt (X-A) p)"

  definition "open" :: "'a set \<Rightarrow> bool" (* def 4.2.4a *)
    where "open A \<equiv> (\<forall>p\<in>A. (intpt A p))"

  definition closed :: "'a set \<Rightarrow> bool" (* def 4.2.4b *)
    where [simp]: "closed A \<equiv> A\<in>T \<and> open (X-A)"

  corollary c426: "True" (* cor 4.2.6 *) oops
  corollary c427: "True" (* cor 4.2.7 *) oops

  text \<open>THEOREM 4.2.5: A set \<open>A\<in>X\<close> in a topological space "\<open>(X,T)\<close> is closed
        iff every limit point of \<open>A\<close> belongs to \<open>A\<close>. Hence, if \<open>\<exists>\<close> a limit point
        of \<open>A\<close> not in \<open>A\<close>, then \<open>A\<close> is not closed. Conversely, if \<open>A\<close> is not
        closed, then  \<open>\<exists>\<close> a limit point of \<open>A\<close> not in \<open>A\<close>.\<close>

  theorem t425a: assumes "closed A" and "limpt A p" shows "p \<in> A"
    proof (rule ccontr)
      assume "p\<notin>A"
      with `limpt A p` have "p\<in>(X-A)" by simp
      moreover from `closed A` have "open (X-A)" by simp
      ultimately have "intpt (X-A) p" using open_def by blast
      \<comment> \<open>that is, there's a neighborhood, \<open>N\<in>T\<close> of p such that \<open>N\<subseteq>(X-A)\<close> \<close>
      with A2 `p\<in>(X-A)` obtain N where "p\<in>N" and "N\<in>T" and "N\<subseteq>(X-A)"
        by (meson intpt_def order_refl)
      then have "N\<inter>A={}" by auto   \<comment> \<open>which contradicts the definition of a limit point.\<close>
      moreover have "N\<inter>A\<noteq>{}" using `limpt A p` `p\<in>N` `N\<in>T` limpt_def by auto
      ultimately show "False" by simp
    qed
end

section \<open>notes to self\<close>

  text \<open> i had originally translated the theorem like so: \<close>

    lemma (in topspace) "closed A \<Longrightarrow> {p\<in>X. limpt A p} \<subseteq>  A"
      proof
      oops

  text \<open> but it's simpler to just write this: \<close>

    lemma (in topspace) "closed A \<and> limpt A p \<longrightarrow> p \<in> A"
      proof -
      oops

  text \<open>but even simpler to write this.
       (compare subgoals in the output panel with the cursor placed directly after the word "proof")\<close>
    lemma (in topspace) assumes "closed A" and "limpt A p"  shows "p \<in> A"
      proof
      oops

  text \<open> but in the end, Sentilles used a proof by contradiction,
         so the actual proof goal was just "False".\<close>

end

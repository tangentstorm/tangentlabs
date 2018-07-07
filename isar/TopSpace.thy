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
    where [simp]: "nhs p \<equiv> {N\<in>T. p\<in>N}"

  text \<open>If \<open>A\<subseteq>X\<close> in topological space \<open>(X,T)\<close>, then \<open>p\<in>X\<close> is called a \<^bold>\<open>limit point\<close>
    of \<open>A\<close> if the intersection of every neighborhood of \<open>p\<close> with \<open>A\<close> is non-empty.
    In loose geometrical terms, \<open>p\<close> is either a point in \<open>A\<close> or as close as possible
    to \<open>A\<close> without actually being in it.\<close>

  definition limpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.1 *)
    where [simp]: "limpt A p \<equiv> A\<in>T \<and> p\<in>X \<and> (A\<inter>(\<Inter>nhs p) \<noteq> {})"

  text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called an \<^bold>\<open>interior point\<close>
    of A if at least one neighborhood of a is contained entirely within A.\<close>

  definition intpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.2 *)
    where [simp]: "intpt A p \<equiv> A\<in>T \<and> p\<in>A \<and> (\<exists>N\<in>T. N\<subset>A)"

  definition boundpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.3 *)
    where "boundpt A p \<equiv> (limpt A p) \<and> (limpt (X-A) p)"

  definition "open" :: "'a set \<Rightarrow> bool" (* def 4.2.4a *)
    where "open A \<equiv> (\<forall>p\<in>A. intpt A p)"

  definition closed :: "'a set \<Rightarrow> bool" (* def 4.2.4b *)
    where [simp, intro]: "closed A \<longleftrightarrow> A\<in>T \<and> open (X-A)"

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

  lemma nhT: assumes "p\<in>X" shows "(\<Inter> nhs p) \<in> T"
    proof -
      define NS where "NS = nhs p"
      from `p\<in>X` A1 obtain N0 where "p\<in>N0" and "N0\<in>T" by auto
      hence "N0 \<in> nhs p" by simp
      then show ?thesis proof (cases "NS = {N0}")
        case True then show ?thesis using NS_def by auto
      next
        case False
        then obtain N1 where "N1\<in>NS" and "N1\<in>T" and "N0\<noteq>N1" using NS_def \<open>N0 \<in> nhs p\<close> by auto
        hence "p\<in>N0\<inter>N1" by (simp add: NS_def \<open>p \<in> N0\<close>)
        then obtain N01 where "N01\<in>T" and "N01\<subseteq>(N0\<inter>N1)" using `N0\<in>T` `N1\<in>T` A2 by meson
        oops
        text \<open>I suspect the above is probably true, but to prove it, i would need an
induction rule on sets, where I keep removing intersecting items from NS until it's empty.
This is probably possible in Isar, but I don't yet know how to express it.\<close>

  lemma
    assumes "A\<in>T" "x\<in>X" and "\<not>(limpt A x)"
    obtains N where "N\<in>T" and "N\<inter>A={}"
  proof -
    \<comment> "Start with the (negated) definition of \<open>limpt A x\<close>"
    from limpt_def have "\<not>(limpt A x) \<equiv> \<not>(A\<in>T \<and> x\<in>X \<and> (A\<inter>(\<Inter> {N\<in>T. x\<in>N}) \<noteq> {}))" by simp
    \<comment> "Distributing \<not> over \<and> gives us three possibilities \<dots>"
    also have "\<dots> \<equiv> (A\<notin>T) \<or> (x\<notin>X) \<or> (A\<inter>(\<Inter> nhs x) = {})" by simp
    \<comment> "\<dots> But our assumptions rule out the first two."
    finally have "\<dots> \<equiv> A\<inter>(\<Inter> nhs x) = {}" using assms by auto
    hence "A\<inter>(\<Inter> nhs x) = {}" using assms by auto
    then obtain N where "N\<in>T" and "N\<inter>A={}" sorry
    oops    (* have "\<exists>N. N\<in>T \<and> N\<inter>A={}" proof *)


    text\<open>this lemma suffers from the same problem. however:
 if i replaced \<open>A\<inter>(\<Inter> nhs p\<close> with \<open>\<forall> N \<in> nhs p. A\<inter>N\<noteq>{} \<close>, then I wouldn't
have to deal with the minimal intersection at all: I would only need to obtain
one example of N. (And in this second attempt, that would be automatic by
negating the \<open>\<forall>\<close>... So I will try this tomorrow.\<close>


  theorem t425b: assumes a1:"\<And>p. limpt A p \<longrightarrow> p \<in> A" shows "closed A"
  proof -
     \<comment> \<open>open(x-A) means any point in X-A is an interior point of X-A.\<close>
     fix x assume "x\<in>(X-A)" hence "x\<notin>A" by auto
     with a1 have  "\<not>(limpt A x)" by blast
     then obtain N where "N\<in>T" and "N\<inter>A={}" sorry
     next show "closed A" using assms sorry
   qed
       \<comment> \<open>
By def 4.2.1, this means there is a neighborhood N\<in>T of x whose intersection with A is empty.
In other words, N\<subset>X-A.
But this means X-A is open by def 4.24.\<close>

    text \<open>\<^bold>\<open>COROLLARY 4.2.6\<close>
      A subset \<open>A\<close> of a topological space \<open>(X,T)\<close> is closed if \<open>A\<close> contains its boundary.\<close>
    corollary c426: "True" (* cor 4.2.6 *) oops

    text \<open>\<^bold>\<open>COROLLARY 4.2.7\<close>
     In any topological space \<open>(X,T)\<close>, both \<open>X\<close> and \<open>{}\<close> are closed sets,
     and both are empty sets.\<close>
  corollary c427: "True" (* cor 4.2.7 *) oops
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

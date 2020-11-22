theory TopSpace_etc
  imports TopSpace
begin

section \<open>notes to self\<close>

text \<open> i had originally translated the theorem like so: \<close>

lemma (in topspace) "closed A \<Longrightarrow> {p\<in>X. limpt A p} \<subseteq>  A"
  proof
  oops

text \<open> but it's simpler to just write this: \<close>

lemma (in topspace) "closed A \<and> limpt A p \<longrightarrow> p \<in> A"
  proof -
  oops

text \<open>It's even simpler to write this:
  (compare subgoals in the output panel with the cursor placed directly after the word "proof")\<close>

lemma (in topspace) assumes "closed A" and "limpt A p"  shows "p \<in> A"
  proof
  oops

text \<open>In the end, Sentilles used proof by contradiction, so the actual goal was just "False".\<close>

section \<open>conjectures\<close>

  lemma (in topspace) nhT_conjecture: assumes "p\<in>X" shows "(\<Inter> nhs p) \<in> T"
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
     text \<open>I suspect the above might be true, but I'm not sure. I was trying to prove this
as when the definition of limpt included the phrase \<open>A\<inter>(\<Inter>nhs p)\<noteq>{}\<close>. This form seems to require
something like an induction rule on sets, where I keep removing intersecting items from
NS until it's empty. This is probably possible in Isar, but I don't yet know how to express it.
Since then, I've re-formulated \<open>limpt\<close> using \<open>(\<forall>N\<in>nhs p. (A\<inter>N) \<noteq> {})\<close> which turned out to
be much easier to work with. I am leaving this as a conjecture for me to work on in the future.\<close>


\<comment> \<open>A user in a mathoverflow thread claims that open sets are usually
   defined as being those that are in T. However, my current definitions are
   not sufficient to enforce this.  https://math.stackexchange.com/a/157738/34877\<close>
lemma (in topspace)
  assumes "A\<subseteq>X" "open A" "A\<noteq>{}"
  shows "A\<in>T"
  try \<comment> "It tries and fails. "
  oops

end
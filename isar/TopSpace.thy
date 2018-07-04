(* Topological Spaces
   Based on "A Bridge to Advanced Mathematics" by Dennis Sentilles
   Translated to Isar by Michal J Wallace *)
theory TopSpace
  imports Main
begin

text \<open>A topological space (X,T) is a pair where X is a set whose elements 
are called the "points" of the topological space, and T is a fixed collection of
subsets of X called neighborhoods, with the following properties:\<close>

class topspace =
    fixes X :: "'a set"
    fixes T :: "('a set) set"
    assumes A1: "x\<in>X \<Longrightarrow> \<exists>N\<in>T. x\<in>N"
    assumes A2: "(U\<in>T) \<and> (V\<in>T) \<and> (x \<in> (U\<inter>V)) \<Longrightarrow> \<exists>N. x\<in>N \<and> N\<subseteq>(U\<inter>V)"
  begin

    text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called a \<^bold>\<open>limit point\<close>
      of A if the intersection of every neighborhood of x with A is non-empty.\<close>

    definition limpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "limpt A p \<equiv> (A\<subset>X) \<and> (p\<in>X) \<and> ((A \<inter> \<Inter>T) \<noteq> {})"

    text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called an \<^bold>\<open>interior point\<close> 
      of A if at least one neighborhood of a is contained entirely within A.\<close>

    definition intpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "intpt A p \<equiv> (A\<subset>X) \<and> (p\<in>A) \<and> (\<exists>N\<in>T. N\<subset>A)"

    definition boundpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "boundpt A p \<equiv> (limpt A p) \<and> (limpt (X-A) p)"

    definition "open" :: "'a set \<Rightarrow> bool"
      where "open A \<equiv> (\<forall>p\<in>A. (intpt A p))"
      (* where "open A \<longleftrightarrow> A = {a\<in>A. intpt A a}" *)

    definition closed :: "'a set \<Rightarrow> bool"
      where "closed A \<equiv> open (X-A)"

  theorem assumes "closed A" and "limpt A p"  shows "p \<in> A"
  proof (rule ccontr)
    assume "p\<notin>A"
    have "open (X-A)"
      using `closed A` closed_def by simp
    obtain N where "N\<in>T" and "p\<in>N" and "N\<subset>(X-A)"
      using Inf_lower(* "x \<in> A \<Longrightarrow> \<Sqinter>A \<le> x" *)
        and `open (X-A)` open_def intpt_def 
        and `limpt A p` limpt_def by auto
    hence "N\<inter>A = {}" by auto
    moreover have "N\<inter>A \<noteq> {}"
      using DiffD2  (*  "c \<in> A - B \<Longrightarrow> c \<in> B \<Longrightarrow> P" *)
        and \<open>N\<in>T\<close> `limpt A p` limpt_def by auto
    ultimately show "False" by simp
  qed







   (* misc notes to self... *)

    (* i had originally translated the theorem like so: *)
    lemma (in topspace) "closed A \<Longrightarrow> {p\<in>X. limpt A p} \<subseteq>  A"
      proof   oops
  
    (* simpler to just write this: *)
    lemma (in topspace) "closed A \<and> limpt A p \<longrightarrow> p \<in> A"
      proof -
        show ?thesis using Inf_lower Int_Diff closed_def intpt_def limpt_def open_def by auto
      qed
  
    (* but even simpler to write this. (compare subgoals in the output panel) *) 
    lemma (in topspace) assumes "closed A" and "limpt A p"  shows "p \<in> A"
      proof     oops
  
    (* but sentilles used a proof by contradiction, 
       so in the end the goal to prove was just "False". *)

end

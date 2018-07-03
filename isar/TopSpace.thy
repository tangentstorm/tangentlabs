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
      where "limpt A p \<longleftrightarrow> (A\<subset>X) \<and> (p\<in>X) \<and> ((A \<inter> \<Inter>T) \<noteq> {})"

    text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called an \<^bold>\<open>interior point\<close> 
      of A if at least one neighborhood of a is contained entirely within A.\<close>

    definition intpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "intpt A p \<longleftrightarrow> (A\<subset>X) \<and> (p\<in>A) \<and> (\<exists>N\<in>T. N\<subset>A)"

    definition boundpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "boundpt A p \<longleftrightarrow> (limpt A p) \<and> (limpt (X-A) p)"

    definition "open" :: "'a set \<Rightarrow> bool"
      where "open A = (\<forall>p\<in>A. (intpt A p))"
      (* where "open A \<longleftrightarrow> A = {a\<in>A. intpt A a}" *)

    definition closed :: "'a set \<Rightarrow> bool"
      where "closed A \<longleftrightarrow> open (X-A)"

  theorem "closed A \<and> limpt A p \<longrightarrow> p \<in> A"
    using Inf_lower Int_Diff closed_def intpt_def limpt_def open_def by auto

  (* theorem "closed A \<longleftrightarrow> {p\<in>X. limpt A p} \<subseteq> A" *)
    (* proof - *)
      (* fix p assume a0:"closed A" *)
      (* show g:"limpt A p \<longrightarrow> p\<in>A" *)
        (* proof - *)
          (* assume p:"(limpt A p) \<and> (p\<notin>A)" *)
          (* thus "False" sorry *)
        
          (* hence "p \<in> (X-A)"                using limpt_def by auto *)
          (* have  "open (X-A)"               using a0 closed_def by auto *)
          (* then obtain N where n0:"N\<in>T \<and> p\<in>N \<and> N\<subset>(X-A)" using DiffD2 intpt_def limpt_def open_def p by auto   *)
          (* hence n1:"N\<inter>A ={}"                 by auto *)
          (* also have n2:"N\<inter>A \<noteq> {}" using Inf_lower n0 calculation limpt_def p by auto *)
          (* show g sledgehammer *)

      (* thus "closed A \<Longrightarrow> {p\<in>X. limpt A p} \<subseteq> A" by auto *)
    (* (*proof (rule ccontr) sorry*) *)
    (* next show "{p\<in>X. limpt A p} \<subseteq> A \<Longrightarrow> closed A" sorry *)
    (* qed *)

end

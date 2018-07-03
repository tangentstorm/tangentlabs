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
    assumes A2: "\<lbrakk> U\<in>T; V\<in>T; x \<in> (U\<inter>V) \<rbrakk> \<Longrightarrow> \<exists>N. x\<in>N \<and> N\<subseteq>(U\<inter>V)"
  begin

    text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called a \<^bold>\<open>limit point\<close>
      of A if the intersection of every neighborhood of x with A is non-empty.\<close>

    definition limpoint :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "limpoint A x \<longleftrightarrow> (\<exists>y. y \<in> A \<inter> \<Inter>T)"

    text \<open>If A\<subset>X in topological space (X,T), then x\<in>X is called an \<^bold>\<open>interior point\<close> 
      of A if at least one neighborhood of a is contained entirely within A.\<close>

    definition intpoint :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
      where "intpoint A x \<longleftrightarrow> (A\<subset>X) \<and> (x\<in>A) \<and> (\<exists>N\<in>T. N\<subset>A)"

end

end

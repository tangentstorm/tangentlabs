theory QSort
imports Main
begin

(* first, define some rules about what it means to be sorted. *)

fun sorted :: "'a::ord list \<Rightarrow> bool" where
   "sorted [] = True"
 | "sorted [x] = True"
 | "sorted (x#y#zs) = ((x \<le> y) \<and> sorted (y#zs))"

 
lemma sorted_lt:
  assumes "sorted (x#y#zs)"
  shows "x \<le> y" using assms by auto

lemma sorted_behead:
  assumes "sorted (y#zs)"
  shows "sorted zs" using assms by (induction zs; auto)

lemma sorted_cons:
  fixes x y zs 
  assumes "x\<le>y" and "sorted (y#zs)"
  shows "sorted (x#y#zs)" using assms by auto
 
lemma lt_trans:
  fixes x y z
  assumes "(x \<le> y)" and "(y \<le> z)" 
  shows "(x \<le> z)"
  sorry

lemma sorted_nip:
  fixes x y zs z zz
  assumes a0:"sorted (x#y#zs)" and a1:"zs=(z#zz)"
  shows "sorted (x#zs)" using assms
proof -
  have "sorted zs"
    proof -
      from a0 have "sorted (y#zs)" by (rule sorted_behead)
      thus ?thesis by (rule sorted_behead)
    qed

  also have "x\<le>z"
    proof -
      have "x\<le>y" and "y\<le>z" using a0 a1 by auto
      thus ?thesis by (rule lt_trans)
    qed
    
  thus ?thesis using assms by (auto)
qed


lemma sorted_head_shrink:
  fixes x y zs z zz
  assumes "x \<le> y" and "sorted (y#zs)" and zz:"zs=(z#zz)"
  shows "sorted (x#zs)"
proof -
  have "sorted (x#y#zs)" using assms by auto
  from this and zz show ?thesis by (rule sorted_nip)
qed



(* rules about the minimum item in a list (and particularly a sorted list) *)

lemma minxy [simp]:
  assumes "x \<le> y" shows "(min x y) = x"
  using assms by (simp only: min_def; auto)
 
fun listmin :: "'a::ord list \<Rightarrow> 'a" where
   "listmin [] = undefined"
 | "listmin [x] = x"
 | "listmin (x#xs) = min x (listmin xs)"

lemma [simp]: "listmin [x,y] = min x y" by auto

lemma assumes "sorted (x#y#zs)" shows "listmin (x#y#zs) = x" using assms
by (induction zs arbitrary: x y rule: listmin.induct; auto)

lemma assumes "sorted (x#xs)" shows "listmin (x#xs) = x" using assms
by (induction xs arbitrary: x rule: listmin.induct; auto)

(* same for max item *)

lemma gt_vs_le:
  fixes x y
  assumes "x > y"
  shows "\<not>(x \<le> y)"
  sorry (* I have no idea yet why this isn't proved automatically :/ *)

lemma maxxy [simp]:
  fixes x y assumes "x > y"
  shows "(max x y) = x"
  using assms
proof -
  have  "(max x y)= (if x \<le> y then y else x)" by (rule max_def)
  hence "(max x y)= (if False then y else x)" using assms by (simp only: gt_vs_le)
  then show ?thesis by auto
qed

fun listmax :: "'a::ord list \<Rightarrow> 'a" where
   "listmax [] = undefined"
 | "listmax [x] = x"
 | "listmax (x#xs) = max x (listmax xs)"

lemma [simp]: "listmax [x,y] = max x y" by auto

lemma sorted_concat:
  assumes "sorted (y0#ys)"
      and "sorted xs"
      and "listmax(x) < y0"
    shows "sorted (xs @ ys)"
    sorry (* TODO *)


(* and now, the (functional-style) quicksort: *)

fun qsort :: "'a::ord list \<Rightarrow> 'a list" where 
   "qsort [] = []"
 | "qsort (x#ys) = (qsort [y \<leftarrow> ys. y<x]) @ (x # qsort [y \<leftarrow> ys. y \<ge> x])"

value "qsort [ 5, 9, 2, 3, 4 ] :: int list"



lemma "sorted (qsort [])" by auto
lemma "sorted (qsort [x])" by auto

theorem "sorted (qsort (x#ys))"
sorry

(* proof (induct ys rule: qsort.induct)
  show "sorted (qsort [x])" by auto
next
  let ?lt = "[y \<leftarrow> ys. y < x]"
  let ?ge = "[y \<leftarrow> ys. y \<ge> x]"
  have  q0: "qsort (x#ys) = (qsort ?lt) @ (x # qsort ?ge)" by auto
  sorry
qed *)



end

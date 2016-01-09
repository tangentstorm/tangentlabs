theory SumOfRange
imports Main
begin

fun sum :: "nat list \<Rightarrow> nat" where
   "sum xs = foldl (op+) 0 xs"

fun egnar :: "nat \<Rightarrow> nat list" where
   "egnar x = (if x \<le> 0 then [] else x # egnar (x-1))"

fun range :: "nat \<Rightarrow> nat list" where
   "range x = rev (egnar x)"

fun sr :: "nat \<Rightarrow> nat" where
   "sr n = (if n\<le>0 then 0 else n + (sr (n-1)))"
   
theorem sum_range_0 [simp]: "sum (range 0) = 0"
by auto
   
theorem sum_range [simp]: "n > 0 \<Longrightarrow> sum (range n) = n + sum (range (n-1))"
by (induction n; auto)

theorem srsimp [simp]: "n > 0 \<Longrightarrow> sum (range n) = sr n"
by (induction n; auto)

theorem sr2 [simp]: "n > 0 \<Longrightarrow> 2 * (sr n) = n * (n + 1)"
by (induction n; auto)


theorem
  assumes "n > 0"
  shows "sum (range n) = (n * (n+1)) div 2" (is "?x = _")
proof -
  have  "     ?x =     sr n"       using assms by (simp only: srsimp)
  hence " 2 * ?x = 2 * sr n"       by auto
  hence " 2 * ?x = n * (n + 1)"    using assms by (simp only: sr2)
  thus ?thesis by auto
qed

end

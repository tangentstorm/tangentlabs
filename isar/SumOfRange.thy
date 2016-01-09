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


theorem "n > 0 \<Longrightarrow> sum (range n) = (n * (n+1)) div 2"
 proof -
  let ?x =  "sum (range n)"
  have  "n>0 \<Longrightarrow>     ?x =     sr n"          by (simp only: srsimp)
  hence "n>0 \<Longrightarrow> 2 * ?x = 2 * sr n"          by auto
  hence "n>0 \<Longrightarrow> 2 * ?x = n * (n + 1)"       by (simp only: sr2)
  hence "n>0 \<Longrightarrow>     ?x = n * (n + 1) div 2" by auto
  thus ?thesis by auto
qed

end

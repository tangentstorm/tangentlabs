(* from programming and proving manual, p 9 *)
theory progprove2
imports Main
begin

datatype 'a list = Nil | Cons 'a "'a list"
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil"
| "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev(Cons True (Cons False Nil))"

lemma app_nil2 [simp]: "app xs Nil=xs"
  apply(induction xs)
  apply(auto)
  done
lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs);
  apply(auto);
  done
lemma rev_app[simp]: "rev (app xs ys) = app(rev ys) (rev xs)"
  apply (induction xs)
  apply(auto)
  done
theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply (induction xs)
  apply (auto)
  done

(* p 31 ----------------------------------------*)
fun even :: "nat \<Rightarrow> bool" where
   "even 0 = True"
 | "even (Suc 0) = False"
 | "even (Suc (Suc n)) = even n"


end

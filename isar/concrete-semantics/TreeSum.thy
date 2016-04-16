theory TreeSum
imports Main
begin

(* exercise 2.6 from Concrete Semantics *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
   "contents Tip = []"
 | "contents (Node a b c) = (contents a) @ (b # (contents c))"
 
fun treesum :: "int tree \<Rightarrow> int" where
   "treesum Tip = 0"
 | "treesum (Node a b c) = (treesum a) + b + (treesum c)"
 
theorem "treesum xt = listsum (contents xt)"
by (induction; auto)

end

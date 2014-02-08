(* from programming and proving manual *)
theory progprove1
imports Main
begin
  (* page 6 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc(add m n)"

lemma "add m 0 = m"
  apply(induction m)
  apply(auto)
done

end

(* Simple Group Theory
   based on exercises and definitions in chapter 2.5 of
   "A Bridge to Advanced Mathematics" by Dennis Sentilles *)
theory Group
  imports Main
begin

(* "Main" uses "\<circ>" for function composition, so hide it. *)
no_notation comp (infixl "\<circ>" 55)

(* "locale" lets us define what a group is. *)
locale group =
  fixes op :: "'g \<Rightarrow> 'g \<Rightarrow> 'g" (infix "\<circ>" 60)
  fixes id :: "'g" ("\<ee>")
  fixes iv :: "'g \<Rightarrow> 'g"  ("(_\<acute>)" [71] 70)
  assumes A1: "((a=b) \<and> (c=d)) = ((a \<circ> b) = (c \<circ> d))"
      and A2: "(a \<circ> b) \<circ> c = a \<circ> (b \<circ> c)"
      and A3: "a \<circ> \<ee> = a"
      and A4: "a \<circ> a\<acute> = \<ee>"

  begin (* the following theorems are defined inside the locale *)

  theorem T1: "a \<circ> c = b \<circ> c \<longrightarrow> a = b"
    proof
      assume "a \<circ> c = b \<circ> c"
      hence  "(a \<circ> c) \<circ> c\<acute> = (b \<circ> c) \<circ> c\<acute>" by (simp only: A1)
      hence  "a \<circ> (c \<circ> c\<acute>) = b \<circ> (c \<circ> c\<acute>)" by (simp only: A2)
      thus   "a = b"                       by (simp only: A4 A3)
    qed

  theorem T2: "c\<acute> \<circ> c = \<ee>"
    proof -
      define b where "b = c\<acute>"
      have  "(c\<acute> \<circ> c) \<circ> c\<acute>  = (c\<acute> \<circ> c) \<circ> c\<acute>"  by auto
      hence "c\<acute> \<circ> (c \<circ> c\<acute>)  = c\<acute> \<circ> (c \<circ> c\<acute>)"  by (simp only: A2)
      hence "c\<acute> \<circ> (c \<circ> c\<acute>)  = c\<acute>"             by (simp only: A3 A4)
      hence "(c\<acute> \<circ> (c \<circ> c\<acute>)) \<circ> b\<acute> = c\<acute> \<circ> b\<acute>"  by auto
      hence "(c\<acute> \<circ> (c \<circ> b)) \<circ> b\<acute> = b \<circ> b\<acute>"    by (simp only: b_def)
      hence "(c\<acute> \<circ> c) \<circ> (b \<circ> b\<acute>) = b \<circ> b\<acute>"    by (simp only: A2)
      hence "(c\<acute> \<circ> c) \<circ> \<ee> = \<ee>"                by (simp only: A4)
      thus  "(c\<acute> \<circ> c) = \<ee>"                    by (simp only: A3)
    qed

  section "problems"

  theorem P1: "\<ee> \<circ> a = a"
    proof -
      have   "\<ee> \<circ> a = \<ee> \<circ> a"           by auto
      hence  "\<ee> \<circ> a  = (a \<circ> a\<acute>) \<circ> a"   by (simp only: A4)
      hence  "\<ee> \<circ> a  = a \<circ> (a\<acute> \<circ> a)"   by (simp only: A2)
      thus   "\<ee> \<circ> a  = a"              by (simp only: T2 A3)
    qed

  theorem P2: "c \<circ> b = \<ee> \<longrightarrow> b = c\<acute>"
    proof
      assume "c \<circ> b = \<ee>"
      hence  "c\<acute> \<circ> (c \<circ> b) = c\<acute> \<circ> \<ee>"  by auto
      hence  "(c\<acute> \<circ> c) \<circ> b = c\<acute> \<circ> \<ee>"  by (simp only: A2)
      hence  "\<ee> \<circ> b = c\<acute> \<circ> \<ee>"        by (simp only: T2)
      thus   "b = c\<acute>"                by (simp only: P1 A3)
    qed

  (* I initially copied problem 2 wrong, so here's a free theorem. *)
  theorem P2x: "c \<circ> b = \<ee> \<longrightarrow> c = b\<acute>"
    proof
      assume "c \<circ> b = \<ee>"
      hence  "(c \<circ> b) \<circ> b\<acute> = \<ee> \<circ> b\<acute>"  by auto
      hence  "c \<circ> (b \<circ> b\<acute>) = \<ee> \<circ> b\<acute>"  by (simp only: A2)
      hence  "c \<circ> \<ee>  = \<ee> \<circ> b\<acute>"        by (simp only: A4)
      thus   "c = b\<acute>"                by (simp only: A3 P1)
    qed

  theorem P3: "\<exists>x. a \<circ> x = b"
    proof
      have "(a \<circ> a\<acute>) \<circ> b = b" by (simp only: A4 P1)
      thus "a \<circ> (a\<acute> \<circ> b) = b" by (simp only: A2)
    qed

  text \<open>This next one shows that \<ee> is unique in the group:
        That is, any element b that behaves like \<ee> must be \<ee>.\<close>
  theorem P4: "a \<circ> b = a \<longrightarrow> b = \<ee>"
    proof
      assume "(a \<circ> b) = a"
      hence "a\<acute> \<circ> (a \<circ> b) = a\<acute> \<circ> a" by auto
      hence "(a\<acute> \<circ> a) \<circ> b = a\<acute> \<circ> a" by (simp only: A2)
      hence "\<ee> \<circ> b = \<ee>" by (simp only: T2)
      thus  "b = \<ee>" by (simp only: P1)
    qed

  theorem P5: "(a\<acute>)\<acute> = a"
    proof -
      define b where "b = a\<acute>"
      hence "b \<circ> a = a\<acute> \<circ> a" by auto
      hence "b \<circ> a = \<ee>"      by (simp only: T2)
      hence "a = b\<acute>"         by (simp only: P2)
      hence  "a = (a\<acute>)\<acute>"     by (simp only: b_def)
      thus ?thesis by auto
    qed

  end (* group locale *)
end (* theory *)

(* Topological Spaces
   Based on "A Bridge to Advanced Mathematics" by Dennis Sentilles
   Translated to Isar by Michal J Wallace *)
theory TopSpace
  imports Main
begin

section \<open>axioms\<close>

text \<open>A topological space (X,T) is a pair where X is a set whose elements
are called the "points" of the topological space, and T is a fixed collection of
subsets of X called neighborhoods, with the following properties:\<close>

locale topspace =
    fixes X :: "'a set"
    fixes T :: "('a set) set"
    assumes A1 [simp]: "x\<in>X \<equiv> \<exists>N\<in>T. x\<in>N"
    assumes A2 [simp]: "U\<in>T \<and> V\<in>T \<and> x\<in>(U\<inter>V) \<Longrightarrow> \<exists>N\<in>T. x\<in>N \<and> N\<subseteq>(U\<inter>V)"
begin

section \<open>limits, boundaries, and open and closed sets\<close>

  text \<open>A set N\<in>T which contains p\<in>X is called a neighborhood of p.\<close>

  definition nhs :: "'a \<Rightarrow> ('a set) set"
    where [simp]: "nhs p \<equiv> {N\<in>T. p\<in>N}"

  text \<open>If \<open>A\<subseteq>X\<close> in topological space \<open>(X,T)\<close>, then \<open>p\<in>X\<close> is called a \<^bold>\<open>limit point\<close>
    of \<open>A\<close> if the intersection of every neighborhood of \<open>p\<close> with \<open>A\<close> is non-empty.
    In loose geometrical terms, \<open>p\<close> is either a point in \<open>A\<close> or as close as possible
    to \<open>A\<close> without actually being in it.\<close>

  definition limpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.1 *)
    where [simp]: "limpt A p \<equiv> A\<subseteq>X \<and> p\<in>X \<and> (\<forall>N\<in>nhs p. (A\<inter>N) \<noteq> {})"

  text \<open>If \<open>A\<subset>X\<close> in topological space \<open>(X,T)\<close>, then \<open>x\<in>X\<close> is called an \<^bold>\<open>interior point\<close>
    of \<open>A\<close> if at least one neighborhood of \<open>x\<close> is contained entirely within \<open>A\<close>.\<close>

  definition intpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.2 *)
    where [simp]: "intpt A p \<equiv> A\<subseteq>X \<and> p\<in>A \<and> (\<exists>N\<in>nhs p. N\<subseteq>A)"

  definition boundpt :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (* def 4.2.3 *)
    where "boundpt A p \<equiv> (limpt A p) \<and> (limpt (X-A) p)"

  definition "open" :: "'a set \<Rightarrow> bool" (* def 4.2.4a *)
    where "open A \<equiv> (\<forall>p\<in>A. intpt A p)"

  definition closed :: "'a set \<Rightarrow> bool" (* def 4.2.4b *)
    where [simp, intro]: "closed A \<longleftrightarrow> open (X-A)"

  text \<open>THEOREM 4.2.5: A set \<open>A\<in>X\<close> in a topological space "\<open>(X,T)\<close> is closed
        iff every limit point of \<open>A\<close> belongs to \<open>A\<close>. Hence, if \<open>\<exists>\<close> a limit point
        of \<open>A\<close> not in \<open>A\<close>, then \<open>A\<close> is not closed. Conversely, if \<open>A\<close> is not
        closed, then  \<open>\<exists>\<close> a limit point of \<open>A\<close> not in \<open>A\<close>.\<close>

  theorem t425a: assumes "closed A" and "limpt A p" shows "p \<in> A"
    proof (rule ccontr)
      assume "p\<notin>A"
      with `limpt A p` have "p\<in>(X-A)" by simp
      moreover from `closed A` have "open (X-A)" by simp
      ultimately have "intpt (X-A) p" using open_def by blast
      \<comment> \<open>that is, there's a neighborhood, \<open>N\<in>T\<close> of p such that \<open>N\<subseteq>(X-A)\<close> \<close>
      with A2 `p\<in>(X-A)` obtain N where "p\<in>N" and "N\<in>T" and "N\<subseteq>(X-A)" by auto
      then have "N\<inter>A={}" by auto   \<comment> \<open>which contradicts the definition of a limit point.\<close>
      moreover have "N\<inter>A\<noteq>{}" using `limpt A p` `p\<in>N` `N\<in>T` limpt_def by auto
      ultimately show "False" by simp
    qed

    text \<open>To prove the converse in Isar, I needed to make use of the following lemma,
  which says that if some \<open>x\<in>X\<close> is not a limit point of \<open>A\<subseteq>X\<close> then there must be some
  neighborhood \<open>N\<close> of \<open>x\<close> that does not intersect \<open>A\<close> at all.\<close>
  lemma non_limpt_nh:
    assumes "A\<subseteq>X" "x\<in>X" and "\<not>(limpt A x)"
    obtains N where "N\<in>nhs x" and "N\<inter>A={}"
  proof -
    \<comment> "Start with the (negated) definition of \<open>limpt A x\<close>"
    from limpt_def have "\<not>(limpt A x) \<equiv> \<not>(A\<subseteq>X \<and> x\<in>X \<and> (\<forall>N\<in>nhs x. (A\<inter>N) \<noteq> {}))" by simp
    \<comment> "Distributing \<not> over \<and> gives us three possibilities \<dots>"
    also have "\<dots> \<equiv> \<not>(A\<subseteq>X) \<or> (x\<notin>X) \<or> (\<exists>N\<in>nhs x. A\<inter>N={})" by simp
    \<comment> "\<dots> But our assumptions rule out the first two."
    finally have "\<dots> \<equiv> \<exists>N\<in>nhs x. A\<inter>N = {}" using assms by auto
    with `\<not>(limpt A x)` obtain N where "N\<in>nhs x" and "N\<inter>A={}" by auto
    then show ?thesis using that by auto
  qed

  text \<open>Now we can prove the second part of theorem 4.2.5: if \<open>A\<close> contains all its limit
        points, then A is closed.\<close>
  theorem t425b: assumes a0: "A\<subseteq>X" and a1: "\<forall>p. limpt A p \<longrightarrow> p\<in>A" shows "closed A"
    \<comment> \<open>Quoting Sentilles here (replacing his syntax with isar's and using my variable names:\<close>
    \<comment> \<open>"To show \<open>A\<close> is closed, we must argue that \<open>X-A\<close> is open."\<close>
    \<comment> \<open>"That is, that any point of \<open>X-A\<close> is an interior point of \<open>X-A\<close>."\<close>
       \<comment> \<open>"Suppose \<open>x\<in>X-A\<close>. Then \<open>x\<notin>A\<close>."\<close>
       \<comment> \<open>"Since \<open>A\<close> contains all its limit points, then \<open>x\<close> is not a limit point of \<open>A\<close>."\<close>
       \<comment> \<open>"By [\<open>limpt_def\<close>] this means there is a neighborhood \<open>N\<in>T\<close> of \<open>x\<close>
            whose intersection with \<open>A\<close> is empty. In other words, \<open>N\<subseteq>(X-A)\<close>."\<close>
       \<comment> \<open>"But this means \<open>X-A\<close> is open by [\<open>open_def\<close>]."\<close>
       \<comment> \<open>"This is what we wished to prove."\<close>
    proof -
      have "\<forall>x\<in>(X-A). intpt (X-A) x" proof
        fix x assume "x\<in>(X-A)" hence "x\<notin>A" by auto
        have  "\<not>(limpt A x)" using a1 \<open>x\<notin>A\<close> by auto
        with `x \<in> X-A` obtain N where "N\<in>nhs x" and "N\<inter>A={}" using a0 non_limpt_nh by blast
        hence "N\<subseteq>X-A" by auto
        with `N\<in>nhs x` show "intpt (X-A) x" by auto
      qed
      hence "open (X-A)" using open_def by simp
      thus "closed A" by simp
    qed


  text \<open>\<^bold>\<open>COROLLARY 4.2.6\<close>
      A subset \<open>A\<subseteq>X\<close> of a topological space \<open>(X,T)\<close> is closed if \<open>A\<close> contains its boundary.\<close>

  text \<open>
    The last theorem shows that if \<open>A\<subseteq>X\<close> contains all its limit points, then it's closed.
    Can we show that if \<open>A\<close> contains all its boundary points, it must contain all
    its limit points?

    First, many of the limit points are interior points, right? From intpt_def,
    it seems like all interior points are limit points... right?
\<close>

  lemma int_lim:
    assumes "A\<subseteq>X" "intpt A p" shows "limpt A p"
    using assms ball_empty intpt_def by auto

  text \<open>
    It seems so. (We won't actually need that lemma, so I'll just trust the proof.
    Isabelle generated when i typed the word 'try' after the `shows` clause.)

    Anyway, back to the question of whether \<open>A\<close> containing its boundary implies
    that it contains all its limit points.

    Assume \<open>A\<subseteq>X\<close> contains its boundary points, and let \<open>p\<close> be a limit point of \<open>A\<close>
       If \<open>p\<close> is an interior point, then \<open>p\<in>A\<close>.
       else if it's a boundary point, then \<open>p\<in>A\<close> by assumption.
       else ... well, what would that even mean?

    The final case would be a limit point that is neither an interior point
    nor a boundary point. It's hard for me to imagine such a thing, so maybe no
    such thing exists.

    If it doesn't exist, then we've covered all our bases, and the corollary
    can be proven just by formalizing the argument above.

    So... let's try to show that if \<open>limpt A p \<Longrightarrow> (intpt A p) \<or> (boundpt A p)\<close>.
    We know all boundary points are limit points by definition, and all interior
    points are limit points from the lemma above, so really we only need to show
    that a limit point that isn't one of those two things must be the other.

    Here's the proof I came up with:
\<close>

  lemma bnd_ext_lim: assumes "A\<subseteq>X" "limpt A p" "~intpt A p" shows "boundpt A p"
  proof -
    from `limpt A p` have "p\<in>X" by simp
    moreover have "\<forall>N\<in>nhs p. (X-A)\<inter>N\<noteq>{}"
      proof
        fix N assume "N\<in>nhs p"
        from `\<not>intpt A p` `A\<subseteq>X` have "p\<notin>A \<or> \<not>(\<exists>N\<in>nhs p. N\<subseteq>A)" by auto
        then consider "p\<in>(X-A)" | "(\<forall>N\<in>nhs p. \<not>N\<subseteq>A)" by auto
        thus"(X-A)\<inter>N\<noteq>{}" proof (cases)
          case 1 then show ?thesis using \<open>N \<in> nhs p\<close> by fastforce
        next
          case 2 then have "\<not>N\<subseteq>A" using \<open>N \<in> nhs p\<close> by blast
          thus ?thesis using \<open>N \<in> nhs p\<close> by fastforce
        qed
     qed
     moreover from `A\<subseteq>X` have "(X-A) \<subseteq>X" by auto
     ultimately have "limpt (X-A) p" by simp
     thus "boundpt A p" using `limpt A p` boundpt_def by blast
   qed

  text \<open>I'll let Isabelle prove to itself that the two cases are mutually exclusive:\<close>
  lemma lim_bnd_xor_int: assumes "limpt A p" shows "(boundpt A p) \<noteq> (intpt A p)"
    using assms bnd_ext_lim boundpt_def by auto

  text \<open>Now we can show what we really wanted to show:\<close>

  corollary c426:  (* cor 4.2.6 *)
    assumes ax: "A\<subseteq>X"
        and ap: "\<forall>p. boundpt A p \<longrightarrow> p\<in>A"
    shows "closed A"
    proof -
      have "\<And>p. limpt A p \<longrightarrow> p\<in>A" proof
        fix p assume "limpt A p"
        consider (0) "boundpt A p"
               | (1) "intpt A p"
          using \<open>limpt A p\<close> lim_bnd_xor_int by auto
        then show "p\<in>A" using ap intpt_def by auto
      qed
      thus "closed A" using ax t425b by simp
    qed

  text \<open>\<^bold>\<open>COROLLARY 4.2.7\<close>
     In any topological space \<open>(X,T)\<close>, both \<open>X\<close> and \<open>{}\<close> are closed sets,
     and both are empty sets.\<close>

    \<comment> "The first two statements can be proved directly from the definition of 'open':"
    corollary open_empty: "open {}"      using open_def by auto
    corollary open_univ: "open X"        using open_def by fastforce
    \<comment> "Once we have those two, the others two are obvious:"
    corollary closed_univ: "closed X"    using open_empty by simp
    corollary closed_empty: "closed {}"  using open_univ by simp


section \<open>The closure of a set\<close>

definition closure :: "'a set \<Rightarrow> 'a set" (* def 4.3.1 *)
  where "closure A \<equiv> {x. limpt A x}"


text \<open>Theorem 4.3.2: For any set \<open>A\<close> in topological space \<open>X\<close>, \<open>closure A\<close> is closed.
Furthermore, one always has \<open>A \<subseteq> closure A\<close>\<close>

theorem t432: assumes "A\<subseteq>X" shows "closed (closure A)" sorry

corollary c433: assumes "A\<subseteq>X" and "closed A" shows "A = closure A" sorry

corollary c434: assumes "closed B" "A\<subseteq>B" shows "(closure A) \<subseteq> B" sorry

section "Topology and Set Theory"

theorem t441a: assumes "open S0" "open S1" shows "open (S0 \<inter> S1)" sorry
theorem t441b: assumes "closed S0" "closed S1" shows "closed (S0 \<union> S1)" sorry
text \<open>theorem t441c: the union of any collection of open sets is open\<close>
text \<open>theorem t441d: the intersection of any collection of closed sets is closed\<close>


text \<open>theorem 442: if A and B are subsets of a topspace (X,T) then 
  1. closure(A\<union>B) = (closure A) \<union> (closure B)
  2. closure(A\<inter>B) = (closure A) \<inter> (closure B)\<close>

text \<open>theorem 443. If \<open>A\<noteq>{}\<close> is a bounded set of real numbers in \<R>, and \<R> is given the usual
topology, then \<open>sup A\<in> closure A\<close>. Hence, if \<open>A\<close> is closed, then \<open>sup A\<in>A\<close>\<close>

section \<open>4.5 connectedness in a topological space\<close>

section \<open>4.6 the general theory of connected sets\<close>


end (* locale topspace *)

end (* theory TopSpace *)

theory ACN_Methods
  imports ACN_Sec2 "HOL-Eisbach.Eisbach"
begin

section \<open>Proof methods\<close>

text \<open>
  Recurring proof patterns of the later sections, packaged as rules and Eisbach methods:
  \<^item> @{text eta_upper}: an upper bound \<open>\<eta>(G) \<le> k\<close> from an explicit labeling;
  \<^item> @{text eta_ge_2}, @{text eta_eq_2}: the lower bound \<open>\<eta>(G) \<ge> 2\<close> from Observation 1;
  \<^item> @{text sum_edge_cases}: the edge condition on graphs with vertices \<open>Inl i\<close> and \<open>Inr j\<close>;
  \<^item> @{text neighborhood_eq}: computing a neighborhood;
  \<^item> @{text mod3_cases}, @{text mod6_cases}: arithmetic with \<open>div\<close> and \<open>mod\<close> by a constant, by cases on the residue.
\<close>

subsection \<open>Bounds on \<open>\<eta>\<close>\<close>

context fin_sgraph
begin

lemma eta_le_coloring:
  assumes "0 < k" "labeling k f" "\<And>x y. vert_adj x y \<Longrightarrow> sumN f x \<noteq> sumN f y"
  shows "eta \<le> k"
  using assms by (intro eta_le) (auto simp: additive_coloring_def)

lemma eta_ge_2:
  assumes "vert_adj u v" "degree u = degree v"
  shows "2 \<le> eta"
proof -
  have "eta \<noteq> 1" using assms observation_1 by blast
  then show ?thesis using eta_pos by simp
qed

lemma eta_eq_2: "eta \<le> 2 \<Longrightarrow> vert_adj u v \<Longrightarrow> degree u = degree v \<Longrightarrow> eta = 2"
  using eta_ge_2 by fastforce

end

text \<open>
  \<open>eta_upper rule: G.eta_le_coloring\<close> reduces \<open>G.eta \<le> k\<close> to the labeling condition and the edge
  condition; the goal \<open>0 < k\<close> is closed by \<open>simp\<close> when possible.
\<close>

method eta_upper uses rule = (rule rule, (simp; fail)?)

subsection \<open>Edges on a sum type\<close>

lemma sum_edge_cases:
  assumes "R x y" and sym: "\<And>a b. R a b \<longleftrightarrow> R b a" and rr: "\<And>i j. \<not> R (Inr i) (Inr j)"
    and Qsym: "\<And>a b. Q a b \<Longrightarrow> Q b a"
    and ll: "\<And>i j. R (Inl i) (Inl j) \<Longrightarrow> Q (Inl i) (Inl j)"
    and lr: "\<And>i j. R (Inl i) (Inr j) \<Longrightarrow> Q (Inl i) (Inr j)"
  shows "Q x y"
proof (cases x; cases y)
  fix i j assume "x = Inr i" "y = Inl j"
  then have "R (Inl j) (Inr i)" using assms(1) sym by simp
  then show ?thesis using lr Qsym \<open>x = Inr i\<close> \<open>y = Inl j\<close> by blast
qed (use assms in auto)

text \<open>
  For a goal \<open>G.sumN f x \<noteq> G.sumN f y\<close> with \<open>adj: G.vert_adj x y\<close>, \<open>sum_edge_cases\<close> leaves two
  goals: an edge between \<open>Inl i\<close> and \<open>Inl j\<close>, and an edge between \<open>Inl i\<close> and \<open>Inr j\<close>. The fact
  \<open>rr\<close> says that there are no edges between \<open>Inr\<close> vertices; \<open>sym\<close> is the symmetry of adjacency.
\<close>

method sum_edge_cases uses adj sym rr =
  (match conclusion in "fin_sgraph.sumN V E f x \<noteq> fin_sgraph.sumN V E f y"
      for V :: "('a + 'b) set" and E f x y \<Rightarrow>
    \<open>rule sum_edge_cases[where Q = "\<lambda>a b. fin_sgraph.sumN V E f a \<noteq> fin_sgraph.sumN V E f b"
        and R = "ulgraph.vert_adj E" and x = x and y = y, OF adj sym rr], fastforce\<close>)

subsection \<open>Neighborhoods\<close>

lemma set_eq_sum_cases:
  "(\<And>i. Inl i \<in> A \<longleftrightarrow> Inl i \<in> B) \<Longrightarrow> (\<And>i. Inr i \<in> A \<longleftrightarrow> Inr i \<in> B) \<Longrightarrow> A = B"
  by (rule set_eqI, case_tac x) auto

text \<open>
  \<open>neighborhood_eq nb: G.in_neighborhood_iff simps: adj_lemmas dests: \<dots>\<close> proves \<open>G.neighborhood v = S\<close>
  vertex by vertex (by constructor for sum types). The membership rules \<open>nb\<close> are unfolded before
  the simplifier runs, so that they still match the locale's vertex set.
\<close>

method neighborhood_eq uses nb simps dests =
  ((rule set_eq_sum_cases | rule set_eqI); unfold Un_iff insert_iff nb; auto simp: simps dest: dests)

subsection \<open>Arithmetic by residues\<close>

text \<open>
  \<open>presburger\<close> is slow on goals with several \<open>div\<close> terms. \<open>mod3_cases m\<close> and \<open>mod6_cases m\<close> instead split a natural
  number into \<open>n * t + c\<close> for each residue \<open>c < n\<close> (\<open>n \<in> {3, 6}\<close>), and the simp rules
  @{text div_mod_lin} evaluate the divisions and remainders that appear.
\<close>

lemma mod3_cases:
  fixes m :: nat
  obtains t where "m = 3 * t" | t where "m = 3 * t + 1" | t where "m = 3 * t + 2"
proof -
  have m: "m = 3 * (m div 3) + m mod 3" by simp
  have "m mod 3 < 3" by simp
  then consider "m mod 3 = 0" | "m mod 3 = 1" | "m mod 3 = 2" by linarith
  then show ?thesis
  proof cases
    case 1 then show ?thesis using that(1)[of "m div 3"] m by simp
  next
    case 2 then show ?thesis using that(2)[of "m div 3"] m by simp
  next
    case 3 then show ?thesis using that(3)[of "m div 3"] m by simp
  qed
qed

lemma mod6_cases:
  fixes m :: nat
  obtains t where "m = 6 * t" | t where "m = 6 * t + 1" | t where "m = 6 * t + 2"
    | t where "m = 6 * t + 3" | t where "m = 6 * t + 4" | t where "m = 6 * t + 5"
proof -
  have m: "m = 6 * (m div 6) + m mod 6" by simp
  have "m mod 6 < 6" by simp
  then consider "m mod 6 = 0" | "m mod 6 = 1" | "m mod 6 = 2" | "m mod 6 = 3" | "m mod 6 = 4" | "m mod 6 = 5"
    by linarith
  then show ?thesis
  proof cases
    case 1 then show ?thesis using that(1)[of "m div 6"] m by simp
  next
    case 2 then show ?thesis using that(2)[of "m div 6"] m by simp
  next
    case 3 then show ?thesis using that(3)[of "m div 6"] m by simp
  next
    case 4 then show ?thesis using that(4)[of "m div 6"] m by simp
  next
    case 5 then show ?thesis using that(5)[of "m div 6"] m by simp
  next
    case 6 then show ?thesis using that(6)[of "m div 6"] m by simp
  qed
qed

lemma div_mod_lin:
  "(3 * t + c) div 3 = t + c div 3" "(6 * t + c) div 3 = 2 * t + c div 3"
  "(6 * t + c) div 2 = 3 * t + c div 2" "(2 * t + c) div 2 = t + c div 2"
  "(6 * t + c) mod 6 = c mod 6" "(6 * t + c) mod 3 = c mod 3" "(6 * t + c) mod 2 = c mod 2"
  "(3 * t + c) mod 3 = c mod 3" "(2 * t + c) mod 2 = c mod 2"
  "(3 * t) div 3 = t" "(6 * t) div 3 = 2 * t" "(6 * t) div 2 = 3 * t"
  "(6 * t) mod 6 = 0" "(6 * t) mod 3 = 0" "(6 * t) mod 2 = 0" "(3 * t) mod 3 = 0"
  for t c :: nat
  by simp_all (simp_all add: mod_add_left_eq[symmetric] div_mult_self2 mult.assoc[symmetric] mod_mult_right_eq)

method mod3_cases for m :: nat uses simps =
  (cases m rule: mod3_cases; simp add: div_mod_lin simps; arith?)

method mod6_cases for m :: nat uses simps =
  (cases m rule: mod6_cases; simp add: div_mod_lin simps; arith?)


end

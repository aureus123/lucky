theory ACN_Basics
  imports
    "Undirected_Graph_Theory.Undirected_Graph_Basics"
    "HOL-Library.Nat_Bijection"
begin

section \<open>Basic notions (Section 1 of the paper)\<close>

text \<open>
  Graphs are finite simple graphs given by the locale @{locale fin_sgraph} of the AFP entry
  \<^emph>\<open>Undirected Graph Theory\<close> (C. Edmonds): a vertex set \<open>V\<close> and a set \<open>E\<close> of 2-element
  edges. \<open>vert_adj u v\<close> means \<open>{u, v} \<in> E\<close>, \<open>neighborhood v\<close> is the open neighborhood
  \<open>N(v)\<close> and \<open>degree v = card (neighborhood v)\<close>.
\<close>

subsection \<open>Edges of complete graphs\<close>

lemma all_edges_doubleton: "{x, y} \<in> all_edges U \<longleftrightarrow> x \<in> U \<and> y \<in> U \<and> x \<noteq> y"
  by (auto simp: all_edges_def card_insert_if)

lemma sum_Inl: "sum (case_sum f g) (Inl ` A) = sum f A"
  by (simp add: sum.reindex)

lemma sum_Inr: "sum (case_sum f g) (Inr ` A) = sum g A"
  by (simp add: sum.reindex)

subsection \<open>Ceiling division\<close>

definition cdiv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "cdiv a b = (a + b - 1) div b"

lemma cdiv_le_iff:
  assumes "0 < b"
  shows "cdiv a b \<le> k \<longleftrightarrow> a \<le> k * b"
proof -
  have "cdiv a b \<le> k \<longleftrightarrow> (a + b - 1) div b < Suc k"
    by (simp add: cdiv_def less_Suc_eq_le)
  also have "\<dots> \<longleftrightarrow> a + b - 1 < Suc k * b"
    using assms by (simp add: div_less_iff_less_mult)
  also have "\<dots> \<longleftrightarrow> a \<le> k * b"
    using assms by simp linarith
  finally show ?thesis .
qed

lemma le_cdiv_iff:
  assumes "0 < b"
  shows "k \<le> cdiv a b \<longleftrightarrow> (k = 0 \<or> (k - 1) * b < a)"
proof (cases k)
  case (Suc j)
  have "Suc j \<le> cdiv a b \<longleftrightarrow> \<not> cdiv a b \<le> j" by auto
  also have "\<dots> \<longleftrightarrow> \<not> a \<le> j * b" using cdiv_le_iff[OF assms] by simp
  finally show ?thesis using Suc by auto
qed simp

lemma cdiv_ceiling:
  assumes "0 < b"
  shows "cdiv a b = nat \<lceil>real a / real b\<rceil>"
proof -
  have "cdiv a b \<le> k \<longleftrightarrow> nat \<lceil>real a / real b\<rceil> \<le> k" for k
  proof -
    have "nat \<lceil>real a / real b\<rceil> \<le> k \<longleftrightarrow> real a / real b \<le> real k"
      by (simp add: nat_le_iff ceiling_le_iff)
    also have "\<dots> \<longleftrightarrow> real a \<le> real k * real b"
      using assms by (simp add: divide_le_eq)
    also have "\<dots> \<longleftrightarrow> a \<le> k * b" by (metis of_nat_le_iff of_nat_mult)
    finally show ?thesis using cdiv_le_iff[OF assms] by simp
  qed
  then show ?thesis by (metis order.refl order.antisym)
qed

context fin_sgraph
begin

subsection \<open>Neighborhoods\<close>

text \<open>The degree is used through @{text degree_eq} below, not through the library's simp rules.\<close>

declare alt_degree_def [simp del] degree_no_loops [simp del]

lemma not_vert_adj_self: "\<not> vert_adj v v"
  using singleton_not_edge by (simp add: vert_adj_def)

lemma vert_adj_neq: "vert_adj u v \<Longrightarrow> u \<noteq> v"
  using not_vert_adj_self by auto

lemma in_neighborhood_iff: "w \<in> neighborhood v \<longleftrightarrow> vert_adj v w"
  unfolding neighborhood_def using vert_adj_imp_inV by auto

lemma neighborhood_subset: "neighborhood v \<subseteq> V"
  unfolding neighborhood_def by auto

lemma not_in_own_neighborhood: "v \<notin> neighborhood v"
  using in_neighborhood_iff not_vert_adj_self by blast

lemma finite_neighborhood: "finite (neighborhood v)"
  by (rule fin_neighbourhood)

lemma degree_eq: "degree v = card (neighborhood v)"
  by (simp add: alt_degree_def card_incident_sedges_neighborhood)

lemma vert_adj_edge: "vert_adj u v \<longleftrightarrow> {u, v} \<in> E"
  by (simp add: vert_adj_def)

subsection \<open>Labelings and additive colorings\<close>

text \<open>\<open>sumN f v\<close> is the paper's \<open>f(N(v))\<close>.\<close>

definition sumN :: "('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> nat" where
  "sumN f v = (\<Sum>w\<in>neighborhood v. f w)"

text \<open>A labeling \<open>f : V \<rightarrow> [k]\<close>; its values outside \<open>V\<close> are irrelevant.\<close>

definition labeling :: "nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "labeling k f \<longleftrightarrow> (\<forall>v\<in>V. 1 \<le> f v \<and> f v \<le> k)"

definition additive_coloring :: "nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "additive_coloring k f \<longleftrightarrow> labeling k f \<and> (\<forall>u v. vert_adj u v \<longrightarrow> sumN f u \<noteq> sumN f v)"

text \<open>
  The additive chromatic number \<open>\<eta>(G)\<close>: the least positive \<open>k\<close> with an additive \<open>k\<close>-coloring
  (as in Czerwi\'nski, Grytczuk and \.Zelazny, \<^emph>\<open>least positive integer\<close>; it only matters for
  the graph without vertices).
\<close>

definition eta :: nat where
  "eta = (LEAST k. 0 < k \<and> (\<exists>f. additive_coloring k f))"

lemma sumN_cong: "(\<And>v. v \<in> V \<Longrightarrow> f v = g v) \<Longrightarrow> sumN f u = sumN g u"
  unfolding sumN_def using neighborhood_subset by (intro sum.cong) auto

lemma sumN_const_1: "sumN (\<lambda>_. 1) v = degree v"
  by (simp add: sumN_def degree_eq)

lemma labeling_mono: "labeling k f \<Longrightarrow> k \<le> k' \<Longrightarrow> labeling k' f"
  unfolding labeling_def by auto

lemma additive_coloring_mono: "additive_coloring k f \<Longrightarrow> k \<le> k' \<Longrightarrow> additive_coloring k' f"
  unfolding additive_coloring_def using labeling_mono by blast

text \<open>Every graph has an additive coloring: label the vertices with distinct powers of two.\<close>

lemma exists_additive_coloring: "\<exists>k f. 0 < k \<and> additive_coloring k f"
proof -
  obtain g :: "'a \<Rightarrow> nat" and n where g: "g ` V = {i. i < n}" "inj_on g V"
    using finite_imp_inj_to_nat_seg[OF finV] by blast
  define f where "f v = (2::nat) ^ g v" for v
  have lab: "labeling (2 ^ n) f"
    unfolding labeling_def f_def
  proof
    fix v assume "v \<in> V"
    then have "g v < n" using g(1) by auto
    then show "1 \<le> (2::nat) ^ g v \<and> (2::nat) ^ g v \<le> 2 ^ n" by simp
  qed
  have enc: "sumN f v = set_encode (g ` neighborhood v)" for v
  proof -
    have "inj_on g (neighborhood v)" using g(2) neighborhood_subset by (rule inj_on_subset)
    then show ?thesis
      unfolding sumN_def set_encode_def f_def by (simp add: sum.reindex)
  qed
  have "sumN f u \<noteq> sumN f v" if "vert_adj u v" for u v
  proof
    assume "sumN f u = sumN f v"
    then have "g ` neighborhood u = g ` neighborhood v"
      by (simp add: enc set_encode_eq finite_neighborhood)
    then have "neighborhood u = neighborhood v"
      using g(2) neighborhood_subset inj_on_image_eq_iff by metis
    moreover have "v \<in> neighborhood u" using that in_neighborhood_iff by blast
    ultimately show False using not_in_own_neighborhood by blast
  qed
  then show ?thesis using lab unfolding additive_coloring_def by (intro exI[of _ "2 ^ n"]) auto
qed

lemma eta_witness: "0 < eta \<and> (\<exists>f. additive_coloring eta f)"
  unfolding eta_def by (rule LeastI_ex) (use exists_additive_coloring in blast)

lemma eta_pos: "0 < eta"
  using eta_witness by blast

lemma eta_attained: obtains f where "additive_coloring eta f"
  using eta_witness by blast

lemma eta_le: "0 < k \<Longrightarrow> additive_coloring k f \<Longrightarrow> eta \<le> k"
  unfolding eta_def by (metis (mono_tags, lifting) Least_le)

lemma eta_greatest:
  assumes "\<And>k f. 0 < k \<Longrightarrow> additive_coloring k f \<Longrightarrow> m \<le> k"
  shows "m \<le> eta"
  using assms eta_witness by blast

lemma eta_eqI:
  assumes "0 < k" "additive_coloring k f"
    and "\<And>k' f'. 0 < k' \<Longrightarrow> additive_coloring k' f' \<Longrightarrow> k \<le> k'"
  shows "eta = k"
  using assms eta_le eta_greatest by (metis order.antisym)

text \<open>An additive coloring gives distinct labels to true twins (used by Observation 2).\<close>

definition true_twins :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "true_twins u v \<longleftrightarrow> u \<in> V \<and> v \<in> V \<and> insert u (neighborhood u) = insert v (neighborhood v)"

subsection \<open>Acyclic orientations and topological additive numberings\<close>

text \<open>
  An orientation of \<open>G\<close> is a set \<open>A\<close> of arcs containing, for every edge, exactly one of its two
  directions. The paper speaks of digraphs \<open>D\<close> representing an acyclic orientation of \<open>G\<close>; here
  \<open>D\<close> is \<open>(V, A)\<close>, so \<open>N_D(v) = N(v)\<close>.
\<close>

definition orientation :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "orientation A \<longleftrightarrow> (\<forall>u v. (u, v) \<in> A \<longrightarrow> vert_adj u v)
     \<and> (\<forall>u v. vert_adj u v \<longrightarrow> (u, v) \<in> A \<or> (v, u) \<in> A)
     \<and> (\<forall>u v. (u, v) \<in> A \<longrightarrow> (v, u) \<notin> A)"

definition acyclic_orientation :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "acyclic_orientation A \<longleftrightarrow> orientation A \<and> acyclic A"

definition top_add_numbering :: "('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "top_add_numbering A k f \<longleftrightarrow> labeling k f \<and> (\<forall>(u, v)\<in>A. sumN f u < sumN f v)"

text \<open>\<open>\<eta>_t(D)\<close>, which is \<open>\<infinity>\<close> when there is no topological additive numbering.\<close>

definition eta_t :: "('a \<times> 'a) set \<Rightarrow> enat" where
  "eta_t A = (INF k\<in>{k. 0 < k \<and> (\<exists>f. top_add_numbering A k f)}. enat k)"

lemma eta_t_le: "0 < k \<Longrightarrow> top_add_numbering A k f \<Longrightarrow> eta_t A \<le> enat k"
  unfolding eta_t_def by (rule INF_lower) auto

lemma eta_t_attained:
  assumes "eta_t A \<noteq> \<infinity>"
  obtains k f where "eta_t A = enat k" "0 < k" "top_add_numbering A k f"
proof -
  let ?K = "enat ` {k. 0 < k \<and> (\<exists>f. top_add_numbering A k f)}"
  have "?K \<noteq> {}"
  proof
    assume "?K = {}"
    then have "eta_t A = Inf {}" unfolding eta_t_def by (metis (no_types))
    then show False using assms by (simp add: top_enat_def)
  qed
  then have "Inf ?K \<in> ?K" unfolding Inf_enat_def by (metis LeastI ex_in_conv)
  then obtain k where "k \<in> {k. 0 < k \<and> (\<exists>f. top_add_numbering A k f)}" "Inf ?K = enat k"
    by blast
  then show ?thesis using that unfolding eta_t_def by blast
qed

text \<open>The additive coloring induced by the sums: every edge goes from the smaller to the larger sum.\<close>

definition induced_orientation :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set" where
  "induced_orientation f = {(u, v). vert_adj u v \<and> sumN f u < sumN f v}"

lemma induced_orientation_trancl:
  "(u, v) \<in> (induced_orientation f)\<^sup>+ \<Longrightarrow> sumN f u < sumN f v"
  by (induction rule: trancl_induct) (auto simp: induced_orientation_def)

lemma induced_orientation_acyclic:
  assumes "additive_coloring k f"
  shows "acyclic_orientation (induced_orientation f)"
proof -
  have "sumN f u < sumN f v \<or> sumN f v < sumN f u" if "vert_adj u v" for u v
    using assms that unfolding additive_coloring_def by (meson linorder_neqE_nat)
  then have "orientation (induced_orientation f)"
    unfolding orientation_def induced_orientation_def by (auto simp: vert_adj_sym)
  moreover have "acyclic (induced_orientation f)"
    unfolding acyclic_def using induced_orientation_trancl by blast
  ultimately show ?thesis by (simp add: acyclic_orientation_def)
qed

lemma induced_orientation_top_add_numbering:
  assumes "additive_coloring k f"
  shows "top_add_numbering (induced_orientation f) k f"
  using assms unfolding top_add_numbering_def additive_coloring_def induced_orientation_def by auto

lemma top_add_numbering_additive_coloring:
  assumes "orientation A" "top_add_numbering A k f"
  shows "additive_coloring k f"
  unfolding additive_coloring_def
proof (intro conjI allI impI)
  show "labeling k f" using assms(2) by (simp add: top_add_numbering_def)
next
  fix u v assume "vert_adj u v"
  then have "(u, v) \<in> A \<or> (v, u) \<in> A" using assms(1) by (simp add: orientation_def)
  then show "sumN f u \<noteq> sumN f v" using assms(2) unfolding top_add_numbering_def by fastforce
qed

lemma eta_le_eta_t: "orientation A \<Longrightarrow> enat eta \<le> eta_t A"
proof (cases "eta_t A = \<infinity>")
  case False
  assume A: "orientation A"
  obtain k f where "eta_t A = enat k" "0 < k" "top_add_numbering A k f"
    using eta_t_attained[OF False] by blast
  then show ?thesis using eta_le top_add_numbering_additive_coloring[OF A] by auto
qed simp

text \<open>\<open>\<eta>(G) = min {\<eta>_t(D) : D represents an acyclic orientation of G}\<close>.\<close>

theorem eta_min_eta_t: "enat eta = (INF A\<in>{A. acyclic_orientation A}. eta_t A)"
proof (rule order.antisym)
  show "enat eta \<le> (INF A\<in>{A. acyclic_orientation A}. eta_t A)"
    using eta_le_eta_t by (auto simp: acyclic_orientation_def intro: INF_greatest)
next
  obtain f where f: "additive_coloring eta f" by (rule eta_attained)
  let ?A = "induced_orientation f"
  have "(INF A\<in>{A. acyclic_orientation A}. eta_t A) \<le> eta_t ?A"
    using induced_orientation_acyclic[OF f] by (auto intro: INF_lower)
  also have "\<dots> \<le> enat eta"
    using eta_t_le[OF eta_pos induced_orientation_top_add_numbering[OF f]] .
  finally show "(INF A\<in>{A. acyclic_orientation A}. eta_t A) \<le> enat eta" .
qed

subsection \<open>Cliques and the chromatic number\<close>

definition clique :: "'a set \<Rightarrow> bool" where
  "clique Q \<longleftrightarrow> Q \<subseteq> V \<and> (\<forall>u\<in>Q. \<forall>v\<in>Q. u \<noteq> v \<longrightarrow> vert_adj u v)"

text \<open>
  The chromatic number, defined as in the AFP entry \<^emph>\<open>Girth Chromatic\<close> (L. Noschinski) but for
  an arbitrary vertex type: the least number of classes of a partition of \<open>V\<close> into nonempty
  independent sets. Theory \<open>ACN_Chromatic\<close> proves that both definitions agree on graphs with
  natural vertices.
\<close>

definition vertex_colorings :: "'a set set set" where
  "vertex_colorings = {C. \<Union>C = V \<and> (\<forall>c1\<in>C. \<forall>c2\<in>C. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {}) \<and>
    (\<forall>c\<in>C. c \<noteq> {} \<and> (\<forall>u\<in>c. \<forall>v\<in>c. {u, v} \<notin> E))}"

definition chi :: enat where
  "chi = (INF C\<in>vertex_colorings. enat (card C))"

lemma clique_adj: "clique Q \<Longrightarrow> u \<in> Q \<Longrightarrow> v \<in> Q \<Longrightarrow> u \<noteq> v \<Longrightarrow> vert_adj u v"
  by (simp add: clique_def)

lemma clique_subset: "clique Q \<Longrightarrow> Q \<subseteq> V"
  by (simp add: clique_def)

lemma clique_insert:
  assumes "clique Q" "v \<in> V" "\<And>u. u \<in> Q \<Longrightarrow> vert_adj u v"
  shows "clique (insert v Q)"
  unfolding clique_def
proof (intro conjI ballI impI)
  show "insert v Q \<subseteq> V" using assms(1,2) clique_subset by blast
next
  fix x y assume "x \<in> insert v Q" "y \<in> insert v Q" "x \<noteq> y"
  then consider "x = v" "y \<in> Q" | "y = v" "x \<in> Q" | "x \<in> Q" "y \<in> Q" by blast
  then show "vert_adj x y"
  proof cases
    case 1 then show ?thesis using assms(3)[of y] vert_adj_sym by simp
  next
    case 2 then show ?thesis using assms(3)[of x] by simp
  next
    case 3 then show ?thesis using clique_adj[OF assms(1)] \<open>x \<noteq> y\<close> by simp
  qed
qed

lemma clique_le_chi:
  assumes "clique Q"
  shows "enat (card Q) \<le> chi"
  unfolding chi_def
proof (rule INF_greatest)
  fix C assume C: "C \<in> vertex_colorings"
  then have cover: "\<Union>C = V" and indep: "\<And>c u v. c \<in> C \<Longrightarrow> u \<in> c \<Longrightarrow> v \<in> c \<Longrightarrow> {u, v} \<notin> E"
    unfolding vertex_colorings_def by auto
  have "\<forall>q\<in>Q. \<exists>c\<in>C. q \<in> c" using assms cover unfolding clique_def by auto
  then obtain h where h: "\<And>q. q \<in> Q \<Longrightarrow> h q \<in> C \<and> q \<in> h q" by metis
  have "inj_on h Q"
  proof (rule inj_onI)
    fix p q assume "p \<in> Q" "q \<in> Q" "h p = h q"
    then show "p = q"
      using h indep assms unfolding clique_def vert_adj_def by metis
  qed
  moreover have "finite C"
  proof -
    have "C \<subseteq> Pow V" using cover by auto
    then show ?thesis using finV by (meson finite_Pow_iff finite_subset)
  qed
  ultimately have "card Q \<le> card C" using h by (intro card_inj_on_le) auto
  then show "enat (card Q) \<le> enat (card C)" by simp
qed

end

end

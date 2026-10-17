theory ACN_Sec3
  imports ACN_Sec2
begin

section \<open>Join with complete graphs (Section 3)\<close>

subsection \<open>Observation 2: true twins\<close>

context fin_sgraph
begin

lemma sum_closed_neighborhood:
  "(\<Sum>w\<in>insert v (neighborhood v). f w) = f v + sumN f v"
  using not_in_own_neighborhood finite_neighborhood by (simp add: sumN_def)

lemma true_twins_labels_differ:
  assumes "additive_coloring k f" "true_twins u v" "u \<noteq> v"
  shows "f u \<noteq> f v"
proof
  assume eq: "f u = f v"
  have N: "insert u (neighborhood u) = insert v (neighborhood v)"
    using assms(2) by (simp add: true_twins_def)
  then have "v \<in> insert u (neighborhood u)" by simp
  then have "v \<in> neighborhood u" using assms(3) by simp
  then have adj: "vert_adj u v" by (simp add: in_neighborhood_iff)
  have "f u + sumN f u = f v + sumN f v"
    using sum_closed_neighborhood[of f u] sum_closed_neighborhood[of f v] N by simp
  then have "sumN f u = sumN f v" using eq by simp
  then show False using assms(1) adj by (simp add: additive_coloring_def)
qed

theorem observation_2:
  assumes T: "T \<subseteq> V" and twins: "\<And>u v. u \<in> T \<Longrightarrow> v \<in> T \<Longrightarrow> true_twins u v"
  shows "card T \<le> eta"
proof (rule eta_greatest)
  fix k f assume "0 < k" "additive_coloring k f"
  then have "inj_on f T"
    using true_twins_labels_differ twins by (meson inj_onI)
  moreover have "f ` T \<subseteq> {1..k}"
    using \<open>additive_coloring k f\<close> T by (auto simp: additive_coloring_def labeling_def)
  ultimately have "card T \<le> card {1..k}" by (metis card_image card_mono finite_atLeastAtMost)
  then show "card T \<le> k" by simp
qed

lemma degree_le_max_degree: "v \<in> V \<Longrightarrow> degree v \<le> max_degree"
  unfolding max_degree_def using finV by (intro Max_ge) auto

end

subsection \<open>The join \<open>G \<or> K_q\<close>\<close>

definition join_edges :: "'a edge set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a edge set" where
  "join_edges E V U = E \<union> all_edges U \<union> {{v, u} | v u. v \<in> V \<and> u \<in> U}"

text \<open>\<open>G = (V, E)\<close> and the complete graph on the set \<open>U\<close> of \<open>q\<close> new vertices.\<close>

locale join_complete = G: fin_sgraph V E for V :: "'a set" and E +
  fixes U :: "'a set"
  assumes finU: "finite U" and disj: "U \<inter> V = {}"
begin

lemma cross_doubleton:
  "{x, y} \<in> {{v, u} | v u. v \<in> V \<and> u \<in> U} \<longleftrightarrow> (x \<in> V \<and> y \<in> U) \<or> (x \<in> U \<and> y \<in> V)"
  by (auto simp: doubleton_eq_iff)

lemma join_fin_sgraph: "fin_sgraph (V \<union> U) (join_edges E V U)"
proof -
  have edge: "e \<subseteq> V \<union> U \<and> card e = 2" if e: "e \<in> join_edges E V U" for e
  proof -
    consider "e \<in> E" | "e \<in> all_edges U" | v u where "e = {v, u}" "v \<in> V" "u \<in> U"
      using e unfolding join_edges_def by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using G.wellformed G.two_edges by auto
    next
      case 2
      then show ?thesis by (auto simp: all_edges_def)
    next
      case 3
      then have "v \<noteq> u" using disj by blast
      then show ?thesis using 3 by auto
    qed
  qed
  show ?thesis
  proof unfold_locales
    show "\<And>e. e \<in> join_edges E V U \<Longrightarrow> e \<subseteq> V \<union> U" using edge by blast
    show "\<And>e. e \<in> join_edges E V U \<Longrightarrow> card e = 2" using edge by blast
    show "finite (V \<union> U)" using G.finV finU by simp
  qed
qed

sublocale J: fin_sgraph "V \<union> U" "join_edges E V U"
  by (rule join_fin_sgraph)

abbreviation q :: nat where "q \<equiv> card U"

lemma J_adj_iff: "J.vert_adj x y \<longleftrightarrow> G.vert_adj x y \<or> (x \<in> U \<and> y \<in> U \<and> x \<noteq> y)
    \<or> (x \<in> V \<and> y \<in> U) \<or> (x \<in> U \<and> y \<in> V)"
  unfolding J.vert_adj_edge G.vert_adj_edge
  unfolding join_edges_def Un_iff all_edges_doubleton cross_doubleton by blast

lemma J_neighborhood_V: "v \<in> V \<Longrightarrow> J.neighborhood v = G.neighborhood v \<union> U"
  using disj G.vert_adj_imp_inV G.not_vert_adj_self
  by (auto simp: J.in_neighborhood_iff G.in_neighborhood_iff J_adj_iff)

lemma J_neighborhood_U: "u \<in> U \<Longrightarrow> J.neighborhood u = (U - {u}) \<union> V"
  using disj G.vert_adj_imp_inV
  by (auto simp: J.in_neighborhood_iff J_adj_iff)

lemma J_sumN_V:
  assumes "v \<in> V"
  shows "J.sumN f v = G.sumN f v + sum f U"
proof -
  have "G.neighborhood v \<inter> U = {}" using G.neighborhood_subset disj by blast
  then show ?thesis
    unfolding J.sumN_def G.sumN_def J_neighborhood_V[OF assms]
    using G.finite_neighborhood finU by (simp add: sum.union_disjoint)
qed

lemma J_sumN_U:
  assumes "u \<in> U"
  shows "J.sumN f u + f u = sum f U + sum f V"
proof -
  have fin: "finite (U - {u})" "finite V" using finU G.finV by auto
  have "J.sumN f u = sum f (U - {u}) + sum f V"
    unfolding J.sumN_def J_neighborhood_U[OF assms]
    using disj fin by (intro sum.union_disjoint) auto
  moreover have "sum f U = f u + sum f (U - {u})"
    using assms finU by (simp add: sum.remove)
  ultimately show ?thesis by simp
qed

lemma J_sumN_V_complement:
  assumes "v \<in> V"
  shows "J.sumN f v + sum f (V - G.neighborhood v) = sum f U + sum f V"
proof -
  have "sum f V = G.sumN f v + sum f (V - G.neighborhood v)"
    unfolding G.sumN_def using G.neighborhood_subset G.finV
    by (metis sum.subset_diff add.commute)
  then show ?thesis using J_sumN_V[OF assms] by simp
qed

text \<open>Theorem 2: \<open>\<eta>(G \<or> K_q) = max {\<eta>(G), q}\<close> for \<open>q \<le> n - \<Delta> - 1\<close>.\<close>

theorem theorem_2:
  assumes q_le: "q \<le> card V - G.max_degree - 1"
  shows "J.eta = max G.eta q"
proof (rule order.antisym)
  \<comment> \<open>an additive coloring of the join\<close>
  obtain f where f: "G.additive_coloring G.eta f" by (rule G.eta_attained)
  obtain g :: "'a \<Rightarrow> nat" and m where g: "g ` U = {i. i < m}" "inj_on g U"
    using finite_imp_inj_to_nat_seg[OF finU] by blast
  have m: "m = q" using g by (metis card_Collect_less_nat card_image)
  define f' where "f' x = (if x \<in> U then g x + 1 else f x)" for x
  let ?k = "max G.eta q"
  have f'V: "f' v = f v" if "v \<in> V" for v using that disj by (auto simp: f'_def)
  have f'U: "1 \<le> f' u \<and> f' u \<le> q" if "u \<in> U" for u
    using that g m by (auto simp: f'_def Suc_le_eq)
  have labV: "1 \<le> f v \<and> f v \<le> G.eta" if "v \<in> V" for v
    using f that by (simp add: G.additive_coloring_def G.labeling_def)
  have GsumN: "G.sumN f' v = G.sumN f v" for v using f'V by (rule G.sumN_cong)
  have "J.additive_coloring ?k f'"
    unfolding J.additive_coloring_def
  proof (intro conjI allI impI)
    show "J.labeling ?k f'"
      unfolding J.labeling_def using f'U labV f'V by fastforce
  next
    fix x y assume xy: "J.vert_adj x y"
    consider "G.vert_adj x y" | "x \<in> U" "y \<in> U" "x \<noteq> y" | "x \<in> V" "y \<in> U" | "x \<in> U" "y \<in> V"
      using xy J_adj_iff by blast
    then show "J.sumN f' x \<noteq> J.sumN f' y"
    proof cases
      case 1
      then have "x \<in> V" "y \<in> V" using G.vert_adj_imp_inV by auto
      then show ?thesis
        using 1 f J_sumN_V GsumN by (auto simp: G.additive_coloring_def)
    next
      case 2
      then have "f' x \<noteq> f' y" using g(2) by (auto simp: f'_def inj_on_def)
      then show ?thesis using J_sumN_U[OF 2(1), of f'] J_sumN_U[OF 2(2), of f'] by auto
    next
      case 3
      have less: "J.sumN f' x < J.sumN f' y" if v: "x \<in> V" and u: "y \<in> U" for x y
      proof -
        have "U \<noteq> {}" using u by blast
        then have "1 \<le> q" using finU by (simp add: Suc_le_eq card_gt_0_iff)
        then have "q + G.max_degree + 1 \<le> card V" using q_le by linarith
        moreover have "G.degree x \<le> G.max_degree" using v by (rule G.degree_le_max_degree)
        moreover have "card (V - G.neighborhood x) = card V - G.degree x"
          using G.neighborhood_subset G.finite_neighborhood by (simp add: G.degree_eq card_Diff_subset)
        moreover have "card (V - G.neighborhood x) \<le> sum f' (V - G.neighborhood x)"
          using f'V labV by (metis (no_types, lifting) DiffD1 card_eq_sum sum_mono)
        ultimately have "q < sum f' (V - G.neighborhood x)" by linarith
        then have "f' y < sum f' (V - G.neighborhood x)" using f'U[OF u] by linarith
        then show ?thesis using J_sumN_U[OF u, of f'] J_sumN_V_complement[OF v, of f'] by linarith
      qed
      then show ?thesis using 3 by (metis less_irrefl)
    next
      case 4
      have "J.sumN f' y < J.sumN f' x"
      proof -
        have "U \<noteq> {}" using 4 by blast
        then have "1 \<le> q" using finU by (simp add: Suc_le_eq card_gt_0_iff)
        then have "q + G.max_degree + 1 \<le> card V" using q_le by linarith
        moreover have "G.degree y \<le> G.max_degree" using 4 by (intro G.degree_le_max_degree)
        moreover have "card (V - G.neighborhood y) = card V - G.degree y"
          using G.neighborhood_subset G.finite_neighborhood by (simp add: G.degree_eq card_Diff_subset)
        moreover have "card (V - G.neighborhood y) \<le> sum f' (V - G.neighborhood y)"
          using f'V labV by (metis (no_types, lifting) DiffD1 card_eq_sum sum_mono)
        ultimately have "q < sum f' (V - G.neighborhood y)" by linarith
        then have "f' x < sum f' (V - G.neighborhood y)" using f'U[OF 4(1)] by linarith
        then show ?thesis using J_sumN_U[OF 4(1), of f'] J_sumN_V_complement[OF 4(2), of f'] by linarith
      qed
      then show ?thesis by simp
    qed
  qed
  then show "J.eta \<le> ?k" using G.eta_pos by (intro J.eta_le) auto
next
  \<comment> \<open>optimality: \<open>U\<close> is a set of true twins, and a coloring of the join restricts to \<open>G\<close>\<close>
  have "q \<le> J.eta"
  proof (rule J.observation_2)
    show "U \<subseteq> V \<union> U" by blast
  next
    fix u v assume "u \<in> U" "v \<in> U"
    then show "J.true_twins u v"
      unfolding J.true_twins_def using J_neighborhood_U by auto
  qed
  moreover have "G.eta \<le> J.eta"
  proof (rule J.eta_greatest)
    fix k f assume "0 < k" "J.additive_coloring k f"
    then have "G.additive_coloring k f"
      unfolding G.additive_coloring_def J.additive_coloring_def G.labeling_def J.labeling_def
      using J_sumN_V G.vert_adj_imp_inV J_adj_iff by (metis UnCI add_right_cancel)
    then show "G.eta \<le> k" using \<open>0 < k\<close> by (rule G.eta_le[rotated])
  qed
  ultimately show "max G.eta q \<le> J.eta" by simp
qed

text \<open>\<open>\<chi>(G \<or> K_q) \<ge> \<chi>(G) + q\<close> (the paper uses equality), so the conjecture is inherited.\<close>

lemma J_chi_ge: "G.chi + enat q \<le> J.chi"
  unfolding J.chi_def
proof (rule INF_greatest)
  fix C assume C: "C \<in> J.vertex_colorings"
  then have cover: "\<Union>C = V \<union> U"
    and disjC: "\<And>c1 c2. c1 \<in> C \<Longrightarrow> c2 \<in> C \<Longrightarrow> c1 \<noteq> c2 \<Longrightarrow> c1 \<inter> c2 = {}"
    and ne: "\<And>c. c \<in> C \<Longrightarrow> c \<noteq> {}"
    and indep: "\<And>c x y. c \<in> C \<Longrightarrow> x \<in> c \<Longrightarrow> y \<in> c \<Longrightarrow> {x, y} \<notin> join_edges E V U"
    unfolding J.vertex_colorings_def by auto
  have indepJ: "\<not> J.vert_adj x y" if "c \<in> C" "x \<in> c" "y \<in> c" for c x y
    using indep[OF that] by (simp add: J.vert_adj_def)
  have finC: "finite C"
  proof -
    have "C \<subseteq> Pow (V \<union> U)" using cover by auto
    then show ?thesis using J.finV by (meson finite_Pow_iff finite_subset)
  qed
  define CU where "CU = {c \<in> C. c \<inter> U \<noteq> {}}"
  define CV where "CV = C - CU"
  \<comment> \<open>each class meeting \<open>U\<close> is the class of exactly one vertex of \<open>U\<close>\<close>
  have "\<forall>u\<in>U. \<exists>c\<in>C. u \<in> c" using cover by blast
  then obtain cls where cls: "\<And>u. u \<in> U \<Longrightarrow> cls u \<in> C \<and> u \<in> cls u" by metis
  have "bij_betw cls U CU"
  proof (rule bij_betwI')
    fix x y assume "x \<in> U" "y \<in> U"
    then show "cls x = cls y \<longleftrightarrow> x = y"
      using cls indepJ J_adj_iff by metis
  next
    fix x assume "x \<in> U" then show "cls x \<in> CU" using cls by (auto simp: CU_def)
  next
    fix c assume "c \<in> CU"
    then obtain u where u: "u \<in> c" "u \<in> U" "c \<in> C" by (auto simp: CU_def)
    then have "cls u = c" using cls disjC by blast
    then show "\<exists>u\<in>U. c = cls u" using u by blast
  qed
  then have cardCU: "card CU = q" by (simp add: bij_betw_same_card)
  \<comment> \<open>the other classes color \<open>G\<close>\<close>
  have "CV \<in> G.vertex_colorings"
    unfolding G.vertex_colorings_def
  proof (intro CollectI conjI ballI impI)
    show "\<Union>CV = V"
    proof
      show "\<Union>CV \<subseteq> V" using cover by (auto simp: CV_def CU_def)
    next
      show "V \<subseteq> \<Union>CV"
      proof
        fix v assume v: "v \<in> V"
        then obtain c where c: "c \<in> C" "v \<in> c" using cover by blast
        have "c \<notin> CU"
        proof
          assume "c \<in> CU"
          then obtain u where "u \<in> c" "u \<in> U" by (auto simp: CU_def)
          then show False using indepJ[OF c(1) c(2)] J_adj_iff v by blast
        qed
        then show "v \<in> \<Union>CV" using c by (auto simp: CV_def)
      qed
    qed
  next
    fix c1 c2 assume "c1 \<in> CV" "c2 \<in> CV" "c1 \<noteq> c2"
    then show "c1 \<inter> c2 = {}" using disjC by (auto simp: CV_def)
  next
    fix c assume "c \<in> CV"
    then show "c \<noteq> {}" using ne by (auto simp: CV_def)
  next
    fix c x y assume "c \<in> CV" "x \<in> c" "y \<in> c"
    then show "{x, y} \<notin> E" using indep[of c x y] by (auto simp: CV_def join_edges_def)
  qed
  then have "G.chi \<le> enat (card CV)" unfolding G.chi_def by (rule INF_lower)
  moreover have "card C = card CV + card CU"
  proof -
    have "CU \<subseteq> C" by (auto simp: CU_def)
    then have "card CV = card C - card CU" "card CU \<le> card C"
      using finC by (simp_all add: CV_def card_Diff_subset finite_subset card_mono)
    then show ?thesis by simp
  qed
  ultimately show "G.chi + enat q \<le> enat (card C)"
    using cardCU by (metis add_right_mono plus_enat_simps(1))
qed

corollary theorem_2_conjecture:
  assumes "q \<le> card V - G.max_degree - 1" "enat G.eta \<le> G.chi"
  shows "enat J.eta \<le> J.chi"
proof -
  have "enat (max G.eta q) \<le> G.chi + enat q"
  proof (cases "G.eta \<le> q")
    case True
    then show ?thesis by (simp add: max_def)
  next
    case False
    then show ?thesis using assms(2) by (simp add: max_def) (meson le_iff_add order.trans)
  qed
  then show ?thesis using theorem_2[OF assms(1)] J_chi_ge by (metis order.trans)
qed

end

end

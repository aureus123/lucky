theory ACN_Sec4_Spiders
  imports ACN_Sec4
begin

section \<open>Headless spiders (Section 4, Proposition 3)\<close>

text \<open>
  The clique vertices \<open>u_i\<close> are @{term "Inl i"} and the stable vertices \<open>v_i\<close> are @{term "Inr i"},
  for \<open>i \<in> {1..q}\<close>. A labeling is @{term "case_sum fu fv"}: \<open>fu i = f(u_i)\<close>, \<open>fv i = f(v_i)\<close>.
\<close>

definition spider_verts :: "nat \<Rightarrow> (nat + nat) set" where
  "spider_verts q = Inl ` {1..q} \<union> Inr ` {1..q}"

definition thin_edges :: "nat \<Rightarrow> (nat + nat) edge set" where
  "thin_edges q = all_edges (Inl ` {1..q}) \<union> {{Inl i, Inr i} | i. i \<in> {1..q}}"

definition thick_edges :: "nat \<Rightarrow> (nat + nat) edge set" where
  "thick_edges q = all_edges (Inl ` {1..q}) \<union> {{Inl i, Inr j} | i j. i \<in> {1..q} \<and> j \<in> {1..q} \<and> i \<noteq> j}"

lemma thin_fin_sgraph: "fin_sgraph (spider_verts q) (thin_edges q)"
  by unfold_locales (auto simp: spider_verts_def thin_edges_def all_edges_def)

lemma thick_fin_sgraph: "fin_sgraph (spider_verts q) (thick_edges q)"
  by unfold_locales (auto simp: spider_verts_def thick_edges_def all_edges_def)

subsection \<open>Thin spiders\<close>

locale thin_spider =
  fixes q :: nat
  assumes q2: "2 \<le> q"
begin

sublocale G: fin_sgraph "spider_verts q" "thin_edges q" by (rule thin_fin_sgraph)

lemma adj_ll: "G.vert_adj (Inl i) (Inl j) \<longleftrightarrow> i \<in> {1..q} \<and> j \<in> {1..q} \<and> i \<noteq> j"
  unfolding G.vert_adj_edge unfolding thin_edges_def by (auto simp: all_edges_doubleton doubleton_eq_iff)

lemma adj_lr: "G.vert_adj (Inl i) (Inr j) \<longleftrightarrow> i \<in> {1..q} \<and> i = j"
  unfolding G.vert_adj_edge unfolding thin_edges_def by (auto simp: all_edges_def doubleton_eq_iff)

lemma adj_rr: "\<not> G.vert_adj (Inr i) (Inr j)"
  unfolding G.vert_adj_edge unfolding thin_edges_def by (auto simp: all_edges_def doubleton_eq_iff)

lemma N_l: "i \<in> {1..q} \<Longrightarrow> G.neighborhood (Inl i) = Inl ` ({1..q} - {i}) \<union> {Inr i}"
  by (rule set_eqI, case_tac x) (auto simp: G.in_neighborhood_iff adj_ll adj_lr)

lemma N_r: "i \<in> {1..q} \<Longrightarrow> G.neighborhood (Inr i) = {Inl i}"
  by (rule set_eqI, case_tac x) (auto simp: G.in_neighborhood_iff adj_rr adj_lr G.vert_adj_sym[of "Inr i"])

lemma sum_l: "i \<in> {1..q} \<Longrightarrow> G.sumN (case_sum fu fv) (Inl i) + fu i = sum fu {1..q} + fv i"
proof -
  assume i: "i \<in> {1..q}"
  have "G.sumN (case_sum fu fv) (Inl i) = sum fu ({1..q} - {i}) + fv i"
    unfolding G.sumN_def N_l[OF i] by (subst sum.union_disjoint) (auto simp: sum_Inl)
  moreover have "sum fu {1..q} = fu i + sum fu ({1..q} - {i})" using i by (simp add: sum.remove)
  ultimately show ?thesis by simp
qed

lemma sum_r: "i \<in> {1..q} \<Longrightarrow> G.sumN (case_sum fu fv) (Inr i) = fu i"
  by (simp add: G.sumN_def N_r)

lemma degree_l: "i \<in> {1..q} \<Longrightarrow> G.degree (Inl i) = q"
proof -
  assume i: "i \<in> {1..q}"
  have "G.degree (Inl i) + 1 = q + 1"
    using sum_l[OF i, of "\<lambda>_. 1" "\<lambda>_. 1"] G.sumN_const_1 by simp
  then show ?thesis by simp
qed

lemma clique: "G.clique (Inl ` {1..q})"
  unfolding G.clique_def by (auto simp: spider_verts_def adj_ll)

end

theorem proposition_3_thin:
  assumes "2 \<le> q"
  shows "fin_sgraph.eta (spider_verts q) (thin_edges q) = cdiv (q + 1) 2"
proof -
  interpret thin_spider q using assms(1) by unfold_locales
  let ?r = "cdiv (q + 1) 2"
  have r: "?r = (q + 2) div 2" by (simp add: cdiv_def)
  show ?thesis
  proof (rule order.antisym)
    \<comment> \<open>lower bound: Corollary 2 with \<open>d(u_i) = q\<close>\<close>
    have deg: "G.degree ` (Inl ` {1..q} :: (nat + nat) set) = {q}"
    proof
      show "G.degree ` (Inl ` {1..q} :: (nat + nat) set) \<subseteq> {q}"
      proof (rule image_subsetI)
        fix x :: "nat + nat" assume "x \<in> Inl ` {1..q}"
        then obtain i where "i \<in> {1..q}" "x = Inl i" by blast
        then show "G.degree x \<in> {q}" using degree_l[of i] by simp
      qed
      have "G.degree (Inl 1 :: nat + nat) = q" using degree_l assms(1) by simp
      moreover have "(Inl 1 :: nat + nat) \<in> Inl ` {1..q}" using assms(1) by simp
      ultimately show "{q} \<subseteq> G.degree ` (Inl ` {1..q} :: (nat + nat) set)" by (metis empty_subsetI image_eqI insert_subset)
    qed
    have "card (Inl ` {1..q} :: (nat + nat) set) = q" by (simp add: card_image)
    then show "?r \<le> G.eta"
      using G.corollary_2[OF clique] deg assms(1) by (auto simp: eval_nat_numeral)
  next
    show "G.eta \<le> ?r"
    proof (cases "q = 2")
      case True
      define f where "f = case_sum (\<lambda>i::nat. 1::nat) (\<lambda>i::nat. if i = 2 then 2 else 1)"
      have "G.eta \<le> 2"
      proof (eta_upper rule: G.eta_le_coloring)
        show "G.labeling 2 f" by (auto simp: G.labeling_def f_def split: sum.split)
      next
        fix x y assume xy: "G.vert_adj x y"
        have q12: "i = 1 \<or> i = 2" if "i \<in> {1..q}" for i using that True by auto
        have Sl: "G.sumN f (Inl i) = 2 + (if i = 2 then 1 else 0)" if "i \<in> {1..q}" for i
          using sum_l[of i "\<lambda>i. 1::nat" "\<lambda>i. if i = 2 then 2 else 1"] that True
          by (simp add: f_def eval_nat_numeral)
        have Sr: "G.sumN f (Inr i) = 1" if "i \<in> {1..q}" for i
          using sum_r[of i "\<lambda>i. 1::nat"] that True by (simp add: f_def)
        show "G.sumN f x \<noteq> G.sumN f y"
        proof (sum_edge_cases adj: xy sym: G.vert_adj_sym rr: adj_rr)
          fix i j assume ll: "G.vert_adj (Inl i) (Inl j)"
          have ij: "i \<in> {1..q}" "j \<in> {1..q}" "i \<noteq> j" using ll by (simp_all add: adj_ll)
          show "G.sumN f (Inl i) \<noteq> G.sumN f (Inl j)" using Sl[OF ij(1)] Sl[OF ij(2)] q12[OF ij(1)] q12[OF ij(2)] ij(3) by auto
        next
          fix i j assume lr: "G.vert_adj (Inl i) (Inr j)"
          have ij: "i \<in> {1..q}" "j \<in> {1..q}" using lr by (auto simp: adj_lr)
          show "G.sumN f (Inl i) \<noteq> G.sumN f (Inr j)" using Sl[OF ij(1)] Sr[OF ij(2)] by auto
        qed
      qed
      then show ?thesis using True r by auto
    next
      case False
      then have q3: "3 \<le> q" using assms(1) by simp
      let ?r' = "(q + 2) div 2"
      define fu where "fu i = (if i \<le> ?r' then ?r' - i + 1 else q - i + 1)" for i
      define fv where "fv i = (if i \<le> ?r' then 1 else (q + 1) div 2)" for i
      have key: "fv i + ?r' = fu i + i" if "i \<in> {1..q}" for i
        using that by (auto simp: fu_def fv_def)
      have lab_u: "1 \<le> fu i \<and> fu i \<le> ?r'" if "i \<in> {1..q}" for i using that by (auto simp: fu_def)
      have lab_v: "1 \<le> fv i \<and> fv i \<le> ?r'" if "i \<in> {1..q}" for i using that q3 by (auto simp: fv_def)
      have r2: "2 \<le> ?r'" using q3 by simp
      have FU: "2 * ?r' \<le> sum fu {1..q}"
      proof -
        have "{1, 2, q} \<subseteq> {1..q}" using q3 by auto
        then have "sum fu {1, 2, q} \<le> sum fu {1..q}" by (intro sum_mono2) auto
        moreover have "sum fu {1, 2, q} = fu 1 + fu 2 + fu q" using q3 by simp
        moreover have "fu 1 = ?r'" "fu 2 = ?r' - 1" "fu q = 1" using r2 q3 by (auto simp: fu_def)
        ultimately show ?thesis using r2 by linarith
      qed
      let ?f = "case_sum fu fv"
      have su: "G.sumN ?f (Inl i) + ?r' = sum fu {1..q} + i" if "i \<in> {1..q}" for i
        using sum_l[OF that, of fu fv] key[OF that] by linarith
      have "G.eta \<le> ?r'"
      proof (eta_upper rule: G.eta_le_coloring)
        show "G.labeling ?r' ?f"
          unfolding G.labeling_def using lab_u lab_v by (auto simp: spider_verts_def)
      next
        fix x y assume xy: "G.vert_adj x y"
        have uv: "G.sumN ?f (Inr i) < G.sumN ?f (Inl i)" if "i \<in> {1..q}" for i
          using su[OF that] sum_r[OF that, of fu fv] lab_u[OF that] FU that by auto
        show "G.sumN ?f x \<noteq> G.sumN ?f y"
        proof (sum_edge_cases adj: xy sym: G.vert_adj_sym rr: adj_rr)
          fix i j assume ll: "G.vert_adj (Inl i) (Inl j)"
          have ij: "i \<in> {1..q}" "j \<in> {1..q}" "i \<noteq> j" using ll by (simp_all add: adj_ll)
          show "G.sumN ?f (Inl i) \<noteq> G.sumN ?f (Inl j)" using su[OF ij(1)] su[OF ij(2)] ij(3) by auto
        next
          fix i j assume lr: "G.vert_adj (Inl i) (Inr j)"
          have ij: "i \<in> {1..q}" "j = i" using lr by (simp_all add: adj_lr)
          show "G.sumN ?f (Inl i) \<noteq> G.sumN ?f (Inr j)" using uv[OF ij(1)] ij(2) by auto
        qed
      qed
      then show ?thesis using r r2 by auto
    qed
  qed
qed

subsection \<open>Thick spiders\<close>

locale thick_spider =
  fixes q :: nat
  assumes q2: "2 \<le> q"
begin

sublocale G: fin_sgraph "spider_verts q" "thick_edges q" by (rule thick_fin_sgraph)

lemma adj_ll: "G.vert_adj (Inl i) (Inl j) \<longleftrightarrow> i \<in> {1..q} \<and> j \<in> {1..q} \<and> i \<noteq> j"
  unfolding G.vert_adj_edge unfolding thick_edges_def by (auto simp: all_edges_doubleton doubleton_eq_iff)

lemma adj_lr: "G.vert_adj (Inl i) (Inr j) \<longleftrightarrow> i \<in> {1..q} \<and> j \<in> {1..q} \<and> i \<noteq> j"
  unfolding G.vert_adj_edge unfolding thick_edges_def by (auto simp: all_edges_def doubleton_eq_iff)

lemma adj_rr: "\<not> G.vert_adj (Inr i) (Inr j)"
  unfolding G.vert_adj_edge unfolding thick_edges_def by (auto simp: all_edges_def doubleton_eq_iff)

lemma N_l: "i \<in> {1..q} \<Longrightarrow> G.neighborhood (Inl i) = Inl ` ({1..q} - {i}) \<union> Inr ` ({1..q} - {i})"
  by (rule set_eqI, case_tac x) (auto simp: G.in_neighborhood_iff adj_ll adj_lr)

lemma N_r: "j \<in> {1..q} \<Longrightarrow> G.neighborhood (Inr j) = Inl ` ({1..q} - {j})"
  by (rule set_eqI, case_tac x) (auto simp: G.in_neighborhood_iff adj_rr adj_lr G.vert_adj_sym[of "Inr j"])

lemma sum_l:
  assumes "i \<in> {1..q}"
  shows "G.sumN (case_sum fu fv) (Inl i) + fu i + fv i = sum fu {1..q} + sum fv {1..q}"
proof -
  have "G.sumN (case_sum fu fv) (Inl i) = sum fu ({1..q} - {i}) + sum fv ({1..q} - {i})"
    unfolding G.sumN_def N_l[OF assms] by (subst sum.union_disjoint) (auto simp: sum_Inl sum_Inr)
  moreover have "sum fu {1..q} = fu i + sum fu ({1..q} - {i})" "sum fv {1..q} = fv i + sum fv ({1..q} - {i})"
    using assms by (simp_all add: sum.remove)
  ultimately show ?thesis by simp
qed

lemma sum_r:
  assumes "j \<in> {1..q}"
  shows "G.sumN (case_sum fu fv) (Inr j) + fu j = sum fu {1..q}"
proof -
  have "G.sumN (case_sum fu fv) (Inr j) = sum fu ({1..q} - {j})"
    unfolding G.sumN_def N_r[OF assms] by (simp add: sum_Inl)
  then show ?thesis using assms by (simp add: sum.remove)
qed

end

theorem proposition_3_thick:
  assumes "2 \<le> q"
  shows "fin_sgraph.eta (spider_verts q) (thick_edges q) = cdiv (q + 1) 2"
proof -
  interpret thick_spider q using assms by unfold_locales
  let ?r = "(q + 2) div 2"
  have r: "cdiv (q + 1) 2 = ?r" by (simp add: cdiv_def)
  have "?r \<le> G.eta"
  proof (rule G.eta_greatest)
    \<comment> \<open>pigeonhole: \<open>f(u_i) + f(v_i)\<close> takes \<open>q\<close> distinct values in \<open>[2, 2k]\<close>\<close>
    fix k f assume "0 < k" "G.additive_coloring k f"
    then have lab: "\<And>x. x \<in> spider_verts q \<Longrightarrow> 1 \<le> f x \<and> f x \<le> k"
      and add: "\<And>x y. G.vert_adj x y \<Longrightarrow> G.sumN f x \<noteq> G.sumN f y"
      by (auto simp: G.additive_coloring_def G.labeling_def)
    define g where "g i = f (Inl i) + f (Inr i)" for i
    have f_eq: "f = case_sum (\<lambda>i. f (Inl i)) (\<lambda>i. f (Inr i))" by (auto split: sum.split)
    have "inj_on g {1..q}"
    proof (rule inj_onI)
      fix i j assume ij: "i \<in> {1..q}" "j \<in> {1..q}" "g i = g j"
      show "i = j"
      proof (rule ccontr)
        assume "i \<noteq> j"
        then have "G.sumN f (Inl i) \<noteq> G.sumN f (Inl j)" using add adj_ll ij by blast
        moreover have "G.sumN f (Inl i) + g i = G.sumN f (Inl j) + g j"
          using sum_l[OF ij(1), of "\<lambda>i. f (Inl i)" "\<lambda>i. f (Inr i)"]
            sum_l[OF ij(2), of "\<lambda>i. f (Inl i)" "\<lambda>i. f (Inr i)"] f_eq
          by (simp add: g_def add.assoc)
        ultimately show False using ij(3) by simp
      qed
    qed
    moreover have "g ` {1..q} \<subseteq> {2..2 * k}"
    proof
      fix x assume "x \<in> g ` {1..q}"
      then obtain i where i: "i \<in> {1..q}" "x = g i" by blast
      then have "Inl i \<in> spider_verts q" "Inr i \<in> spider_verts q" by (auto simp: spider_verts_def)
      then have "1 \<le> f (Inl i) \<and> f (Inl i) \<le> k" "1 \<le> f (Inr i) \<and> f (Inr i) \<le> k" using lab by blast+
      then show "x \<in> {2..2 * k}" using i by (simp add: g_def)
    qed
    ultimately have "card {1..q} \<le> card {2..2 * k}" by (metis card_image card_mono finite_atLeastAtMost)
    then show "?r \<le> k" using \<open>0 < k\<close> by simp
  qed
  moreover have "G.eta \<le> ?r"
  proof (cases "q = 2")
    case True
    define f where "f = case_sum (\<lambda>i::nat. 1::nat) (\<lambda>i::nat. if i = 1 then 2 else 1)"
    have "G.eta \<le> 2"
    proof (eta_upper rule: G.eta_le_coloring)
      show "G.labeling 2 f" by (auto simp: G.labeling_def f_def split: sum.split)
    next
      fix x y assume xy: "G.vert_adj x y"
      have q12: "i = 1 \<or> i = 2" if "i \<in> {1..q}" for i using that True by auto
      have Sl: "G.sumN f (Inl i) = (if i = 1 then 2 else 3)" if "i \<in> {1..q}" for i
        using sum_l[of i "\<lambda>i. 1::nat" "\<lambda>i. if i = 1 then 2 else 1"] that True
        by (auto simp: f_def eval_nat_numeral atLeastAtMostSuc_conv)
      have Sr: "G.sumN f (Inr i) = 1" if "i \<in> {1..q}" for i
        using sum_r[of i "\<lambda>i. 1::nat" "\<lambda>i. if i = 1 then 2 else 1"] that True
        by (auto simp: f_def eval_nat_numeral atLeastAtMostSuc_conv)
      show "G.sumN f x \<noteq> G.sumN f y"
      proof (sum_edge_cases adj: xy sym: G.vert_adj_sym rr: adj_rr)
        fix i j assume ll: "G.vert_adj (Inl i) (Inl j)"
        have ij: "i \<in> {1..q}" "j \<in> {1..q}" "i \<noteq> j" using ll by (simp_all add: adj_ll)
        show "G.sumN f (Inl i) \<noteq> G.sumN f (Inl j)" using Sl[OF ij(1)] Sl[OF ij(2)] q12[OF ij(1)] q12[OF ij(2)] ij(3) by auto
      next
        fix i j assume lr: "G.vert_adj (Inl i) (Inr j)"
        have ij: "i \<in> {1..q}" "j \<in> {1..q}" using lr by (auto simp: adj_lr)
        show "G.sumN f (Inl i) \<noteq> G.sumN f (Inr j)" using Sl[OF ij(1)] Sr[OF ij(2)] by auto
      qed
    qed
    then show ?thesis using True by auto
  next
    case False
    then have q3: "3 \<le> q" using assms by simp
    define fu where "fu i = (if i \<le> ?r then i else ?r)" for i
    define fv where "fv i = (if i \<le> ?r then 1 else i - ?r + 1)" for i
    let ?f = "case_sum fu fv"
    have key: "fu i + fv i = i + 1" for i by (simp add: fu_def fv_def)
    have lab_u: "1 \<le> fu i \<and> fu i \<le> ?r" if "i \<in> {1..q}" for i using that q3 by (auto simp: fu_def)
    have lab_v: "1 \<le> fv i \<and> fv i \<le> ?r" if "i \<in> {1..q}" for i using that by (auto simp: fv_def)
    have FV: "q + 1 \<le> sum fv {1..q}"
    proof -
      have "sum fv {1..q} = fv q + sum fv ({1..q} - {q})" using q3 by (simp add: sum.remove)
      moreover have "card ({1..q} - {q}) \<le> sum fv ({1..q} - {q})"
        using lab_v by (metis (no_types, lifting) DiffD1 card_eq_sum sum_mono)
      moreover have "card ({1..q} - {q}) = q - 1" using q3 by simp
      moreover have "?r < q" using q3 by presburger
      then have "2 \<le> fv q" by (simp add: fv_def)
      ultimately show ?thesis using q3 by linarith
    qed
    have su: "G.sumN ?f (Inl i) + i + 1 = sum fu {1..q} + sum fv {1..q}" if "i \<in> {1..q}" for i
      using sum_l[OF that, of fu fv] key[of i] by linarith
    have sv: "G.sumN ?f (Inr j) + fu j = sum fu {1..q}" if "j \<in> {1..q}" for j
      using sum_r[OF that] .
    have "G.eta \<le> ?r"
    proof (eta_upper rule: G.eta_le_coloring)
      show "G.labeling ?r ?f" unfolding G.labeling_def using lab_u lab_v by (auto simp: spider_verts_def)
    next
      fix x y assume xy: "G.vert_adj x y"
      have uv: "G.sumN ?f (Inr j) < G.sumN ?f (Inl i)" if "i \<in> {1..q}" "j \<in> {1..q}" for i j
        using su[OF that(1)] sv[OF that(2)] lab_u[OF that(2)] FV that(1) by auto
      show "G.sumN ?f x \<noteq> G.sumN ?f y"
      proof (sum_edge_cases adj: xy sym: G.vert_adj_sym rr: adj_rr)
        fix i j assume ll: "G.vert_adj (Inl i) (Inl j)"
        have ij: "i \<in> {1..q}" "j \<in> {1..q}" "i \<noteq> j" using ll by (simp_all add: adj_ll)
        show "G.sumN ?f (Inl i) \<noteq> G.sumN ?f (Inl j)" using su[OF ij(1)] su[OF ij(2)] ij(3) by auto
      next
        fix i j assume lr: "G.vert_adj (Inl i) (Inr j)"
        have ij: "i \<in> {1..q}" "j \<in> {1..q}" using lr by (simp_all add: adj_lr)
        show "G.sumN ?f (Inl i) \<noteq> G.sumN ?f (Inr j)" using uv[OF ij(1) ij(2)] by auto
      qed
    qed
    then show ?thesis using q3 by auto
  qed
  ultimately show ?thesis using r by simp
qed

end

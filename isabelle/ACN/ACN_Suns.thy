theory ACN_Suns
  imports ACN_Sec4
begin

section \<open>Suns\<close>

text \<open>
  A sun is built from a graph with vertices @{term "Inl ` B"} and edges \<open>BE\<close>, where
  \<open>u_i = Inl i\<close> for \<open>i \<in> {1..m} \<subseteq> B\<close>: add the vertices \<open>v_i = Inr i\<close> and the edges
  \<open>u_i v_{i-1}\<close> and \<open>u_i v_i\<close> (with \<open>v_0 = v_m\<close>). Labelings are @{term "case_sum fu fv"}.
\<close>

definition sprev :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sprev m i = (if i = 1 then m else i - 1)"

definition snext :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "snext m i = (if i = m then 1 else Suc i)"

definition sun_verts :: "nat \<Rightarrow> nat set \<Rightarrow> (nat + nat) set" where
  "sun_verts m B = Inl ` B \<union> Inr ` {1..m}"

definition sun_edges :: "nat \<Rightarrow> (nat + nat) edge set \<Rightarrow> (nat + nat) edge set" where
  "sun_edges m BE = BE \<union> {{Inl i, Inr i} | i. i \<in> {1..m}} \<union> {{Inl i, Inr (sprev m i)} | i. i \<in> {1..m}}"

locale sun_graph =
  fixes m :: nat and B :: "nat set" and BE :: "(nat + nat) edge set"
  assumes m3: "3 \<le> m" and finB: "finite B" and B: "{1..m} \<subseteq> B"
    and BE_wf: "\<And>e. e \<in> BE \<Longrightarrow> e \<subseteq> Inl ` B \<and> card e = 2"
begin

lemma sprev_in: "i \<in> {1..m} \<Longrightarrow> sprev m i \<in> {1..m}"
  and snext_in: "i \<in> {1..m} \<Longrightarrow> snext m i \<in> {1..m}"
  and sprev_snext: "i \<in> {1..m} \<Longrightarrow> sprev m (snext m i) = i"
  and snext_sprev: "i \<in> {1..m} \<Longrightarrow> snext m (sprev m i) = i"
  and sprev_neq: "i \<in> {1..m} \<Longrightarrow> sprev m i \<noteq> i"
  and snext_neq: "i \<in> {1..m} \<Longrightarrow> snext m i \<noteq> i"
  using m3 by (auto simp: sprev_def snext_def)

lemma sprev_eq_iff: "i \<in> {1..m} \<Longrightarrow> j \<in> {1..m} \<Longrightarrow> j = sprev m i \<longleftrightarrow> i = snext m j"
  using m3 by (auto simp: sprev_def snext_def)

lemma sun_fin_sgraph: "fin_sgraph (sun_verts m B) (sun_edges m BE)"
proof -
  have edge: "e \<subseteq> sun_verts m B \<and> card e = 2" if e: "e \<in> sun_edges m BE" for e
  proof -
    consider "e \<in> BE" | i where "e = {Inl i, Inr i}" "i \<in> {1..m}"
      | i where "e = {Inl i, Inr (sprev m i)}" "i \<in> {1..m}"
      using e unfolding sun_edges_def by blast
    then show ?thesis
    proof cases
      case 1 then show ?thesis using BE_wf unfolding sun_verts_def by blast
    next
      case 2 then show ?thesis using B unfolding sun_verts_def by auto
    next
      case 3 then show ?thesis using B sprev_in unfolding sun_verts_def by auto
    qed
  qed
  show ?thesis
  proof unfold_locales
    show "\<And>e. e \<in> sun_edges m BE \<Longrightarrow> e \<subseteq> sun_verts m B" using edge by blast
    show "\<And>e. e \<in> sun_edges m BE \<Longrightarrow> card e = 2" using edge by blast
    show "finite (sun_verts m B)" using finB by (simp add: sun_verts_def)
  qed
qed

sublocale S: fin_sgraph "sun_verts m B" "sun_edges m BE" by (rule sun_fin_sgraph)

sublocale Bs: fin_sgraph "Inl ` B" BE
  by unfold_locales (use BE_wf finB in auto)

lemma BE_Inl: "e \<in> BE \<Longrightarrow> x \<in> e \<Longrightarrow> \<exists>i. x = Inl i"
  using BE_wf by blast

lemma adj_ll: "S.vert_adj (Inl i) (Inl j) \<longleftrightarrow> Bs.vert_adj (Inl i) (Inl j)"
  unfolding S.vert_adj_edge Bs.vert_adj_edge unfolding sun_edges_def by (auto simp: doubleton_eq_iff)

lemma adj_rr: "\<not> S.vert_adj (Inr i) (Inr j)"
proof
  assume "S.vert_adj (Inr i) (Inr j)"
  then have "{Inr i, Inr j} \<in> sun_edges m BE" by (simp add: S.vert_adj_edge)
  then show False unfolding sun_edges_def using BE_Inl[of "{Inr i, Inr j}" "Inr i"]
    by (auto simp: doubleton_eq_iff)
qed

lemma adj_lr_prev: "S.vert_adj (Inl i) (Inr j) \<longleftrightarrow> i \<in> {1..m} \<and> (j = i \<or> j = sprev m i)"
  proof
    assume "S.vert_adj (Inl i) (Inr j)"
    then have "{Inl i, Inr j} \<in> sun_edges m BE" by (simp add: S.vert_adj_edge)
    then show "i \<in> {1..m} \<and> (j = i \<or> j = sprev m i)"
      unfolding sun_edges_def using BE_Inl[of "{Inl i, Inr j}" "Inr j"] by (auto simp: doubleton_eq_iff)
  next
    assume "i \<in> {1..m} \<and> (j = i \<or> j = sprev m i)"
    then have "{Inl i, Inr j} \<in> sun_edges m BE" unfolding sun_edges_def by blast
    then show "S.vert_adj (Inl i) (Inr j)" by (simp add: S.vert_adj_edge)
  qed

lemma adj_lr: "S.vert_adj (Inl i) (Inr j) \<longleftrightarrow> j \<in> {1..m} \<and> (i = j \<or> i = snext m j)"
proof -
  have "S.vert_adj (Inl i) (Inr j) \<longleftrightarrow> i \<in> {1..m} \<and> (j = i \<or> j = sprev m i)" by (rule adj_lr_prev)
  also have "\<dots> \<longleftrightarrow> j \<in> {1..m} \<and> (i = j \<or> i = snext m j)"
    using sprev_eq_iff sprev_in snext_in sprev_snext by metis
  finally show ?thesis .
qed

lemma adj_rl: "S.vert_adj (Inr j) (Inl i) \<longleftrightarrow> j \<in> {1..m} \<and> (i = j \<or> i = snext m j)"
  using adj_lr S.vert_adj_sym by blast

lemma N_r:
  assumes "j \<in> {1..m}"
  shows "S.neighborhood (Inr j) = {Inl j, Inl (snext m j)}"
  by (neighborhood_eq nb: S.in_neighborhood_iff simps: adj_rl adj_rr assms[simplified])

lemma N_l:
  assumes "i \<in> {1..m}"
  shows "S.neighborhood (Inl i) = Bs.neighborhood (Inl i) \<union> {Inr i, Inr (sprev m i)}"
proof (rule set_eqI)
  fix x show "x \<in> S.neighborhood (Inl i) \<longleftrightarrow> x \<in> Bs.neighborhood (Inl i) \<union> {Inr i, Inr (sprev m i)}"
  proof (cases x)
    case (Inl j) then show ?thesis unfolding Inl Un_iff S.in_neighborhood_iff Bs.in_neighborhood_iff by (simp add: adj_ll)
  next
    case (Inr j)
    have "Inr j \<notin> Bs.neighborhood (Inl i)" using Bs.neighborhood_subset by blast
    then show ?thesis
      unfolding Inr S.in_neighborhood_iff adj_lr_prev using assms by auto
  qed
qed

lemma N_hub:
  assumes "i \<notin> {1..m}"
  shows "S.neighborhood (Inl i) = Bs.neighborhood (Inl i)"
proof (rule set_eqI)
  fix x show "x \<in> S.neighborhood (Inl i) \<longleftrightarrow> x \<in> Bs.neighborhood (Inl i)"
  proof (cases x)
    case (Inl j) then show ?thesis unfolding Inl Un_iff S.in_neighborhood_iff Bs.in_neighborhood_iff by (simp add: adj_ll)
  next
    case (Inr j)
    have "Inr j \<notin> Bs.neighborhood (Inl i)" using Bs.neighborhood_subset by blast
    then show ?thesis unfolding Inr S.in_neighborhood_iff adj_lr using assms snext_in by auto
  qed
qed

lemma sumN_r:
  assumes "j \<in> {1..m}"
  shows "S.sumN (case_sum fu fv) (Inr j) = fu j + fu (snext m j)"
proof -
  have "Inl j \<noteq> Inl (snext m j)" using snext_neq[OF assms] by auto
  then show ?thesis unfolding S.sumN_def N_r[OF assms] by simp
qed

lemma sumN_l:
  assumes "i \<in> {1..m}"
  shows "S.sumN f (Inl i) = Bs.sumN f (Inl i) + f (Inr i) + f (Inr (sprev m i))"
proof -
  have "Bs.neighborhood (Inl i) \<inter> {Inr i, Inr (sprev m i)} = {}" using Bs.neighborhood_subset by blast
  moreover have "Inr i \<noteq> Inr (sprev m i)" using sprev_neq[OF assms] by auto
  ultimately show ?thesis
    unfolding S.sumN_def Bs.sumN_def N_l[OF assms]
    using Bs.finite_neighborhood by (simp add: sum.union_disjoint)
qed

lemma sumN_hub: "i \<notin> {1..m} \<Longrightarrow> S.sumN f (Inl i) = Bs.sumN f (Inl i)"
  by (simp add: S.sumN_def Bs.sumN_def N_hub)

lemma degree_l: "i \<in> {1..m} \<Longrightarrow> S.degree (Inl i) = Bs.degree (Inl i) + 2"
  using sumN_l[of i "\<lambda>_. 1"] S.sumN_const_1 Bs.sumN_const_1 by simp

lemma degree_r: "j \<in> {1..m} \<Longrightarrow> S.degree (Inr j) = 2"
  using sumN_r[of j "\<lambda>_. 1" "\<lambda>_. 1"] S.sumN_const_1 by simp

end

end

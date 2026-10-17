theory ACN_Sec5
  imports ACN_Suns ACN_Sec2
begin

section \<open>Other suns (Section 5, Proposition 5)\<close>

text \<open>
  The cycle sun \<open>CS_m\<close> is the sun of the circuit \<open>u_1 \<dots> u_m\<close>; the wheel sun \<open>WS_m\<close> adds the hub
  \<open>w = Inl 0\<close>, adjacent to every \<open>u_i\<close>.
\<close>

definition cs_base :: "nat \<Rightarrow> (nat + nat) edge set" where
  "cs_base m = {{Inl i, Inl (snext m i)} | i. i \<in> {1..m}}"

definition ws_base :: "nat \<Rightarrow> (nat + nat) edge set" where
  "ws_base m = cs_base m \<union> {{Inl 0, Inl i} | i. i \<in> {1..m}}"

lemma parity_pred: "1 \<le> (i::nat) \<Longrightarrow> even (i - 1) \<longleftrightarrow> odd i"
  by (cases i) auto

subsection \<open>The labeling of the appendix and its sums\<close>

definition cs_fu :: "nat \<Rightarrow> nat" where "cs_fu i = (if odd i then 2 else 1)"

definition cs_fv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "cs_fv m j = (if j = 1 \<and> odd m then 2 else 1)"

text \<open>The values of \<open>f(N(u_i))\<close> (in \<open>CS_m\<close>) and \<open>f(N(v_j))\<close> computed in the appendix.\<close>

definition csU :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "csU m i = (if even m then (if odd i then 4 else 6)
     else if i = 1 then 6 else if i = 2 then 7 else if i = m then 5 else if odd i then 4 else 6)"

definition csV :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "csV m j = (if odd m \<and> j = m then 4 else 3)"

context
  fixes m :: nat
  assumes m4: "4 \<le> m"
begin

lemma snext_lt: "i < m \<Longrightarrow> snext m i = Suc i" and snext_m: "snext m m = 1"
  and sprev_gt: "1 < i \<Longrightarrow> sprev m i = i - 1" and sprev_1: "sprev m 1 = m"
  using m4 by (auto simp: snext_def sprev_def)

lemma cs_sum_u:
  assumes i: "i \<in> {1..m}"
  shows "cs_fu (snext m i) + cs_fu (sprev m i) + cs_fv m i + cs_fv m (sprev m i) = csU m i"
proof -
  consider "i = 1" | "i = m" | "1 < i" "i < m" using i by fastforce
  then show ?thesis
  proof cases
    case 1
    then have "snext m i = 2" "sprev m i = m" using snext_lt[of 1] sprev_1 m4 by simp_all
    then show ?thesis using 1 m4 by (simp add: cs_fu_def cs_fv_def csU_def)
  next
    case 2
    then have "snext m i = 1" "sprev m i = m - 1" using snext_m sprev_gt[of m] m4 by simp_all
    moreover have "even (m - 1) \<longleftrightarrow> odd m" using m4 by (simp add: parity_pred)
    moreover have "m - 1 \<noteq> 1" "m \<noteq> 1" "m \<noteq> 2" using m4 by simp_all
    ultimately show ?thesis using 2 by (simp add: cs_fu_def cs_fv_def csU_def)
  next
    case 3
    then have "snext m i = Suc i" "sprev m i = i - 1" using snext_lt sprev_gt by simp_all
    moreover have "even (i - 1) \<longleftrightarrow> odd i" using 3 by (simp add: parity_pred)
    moreover have "i - 1 = 1 \<longleftrightarrow> i = 2" using 3 by auto
    ultimately show ?thesis using 3 by (auto simp: cs_fu_def cs_fv_def csU_def)
  qed
qed

lemma cs_sum_v:
  assumes j: "j \<in> {1..m}"
  shows "cs_fu j + cs_fu (snext m j) = csV m j"
proof (cases "j = m")
  case True
  then show ?thesis using snext_m by (simp add: cs_fu_def csV_def)
next
  case False
  then have "snext m j = Suc j" using j snext_lt by simp
  then show ?thesis using False by (simp add: cs_fu_def csV_def)
qed

lemma csU_range: "i \<in> {1..m} \<Longrightarrow> 4 \<le> csU m i \<and> csU m i \<le> 7"
  by (simp add: csU_def)

lemma csV_range: "csV m j \<le> 4" by (simp add: csV_def)

lemma csU_next: "i \<in> {1..m} \<Longrightarrow> csU m i \<noteq> csU m (snext m i)"
proof -
  assume i: "i \<in> {1..m}"
  consider "i = m" | "i < m" using i by fastforce
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using snext_m m4 by (auto simp: csU_def)
  next
    case 2
    then have "snext m i = Suc i" by (rule snext_lt)
    moreover have "odd m \<Longrightarrow> 5 \<le> m" using m4 by presburger
    ultimately show ?thesis using 2 i by (auto simp: csU_def)
  qed
qed

text \<open>On the vertices of a \<open>v_j\<close>: \<open>f(N(v_j)) < f(N(u))\<close> for its two neighbors \<open>u_j\<close>, \<open>u_{j+1}\<close>.\<close>

lemma csV_less:
  assumes j: "j \<in> {1..m}"
  shows "csV m j < csU m j" "csV m j < csU m (snext m j)"
proof -
  have "csV m j < csU m j" using j m4 by (auto simp: csV_def csU_def)
  moreover have "csV m j < csU m (snext m j)"
  proof (cases "j = m")
    case True
    then show ?thesis using snext_m by (simp add: csV_def csU_def)
  next
    case False
    then show ?thesis using j snext_lt[of j] by (auto simp: csV_def csU_def)
  qed
  ultimately show "csV m j < csU m j" "csV m j < csU m (snext m j)" by auto
qed

lemma cs_fu_sum: "sum cs_fu {1..n} = n + (n + 1) div 2"
  by (induction n) (auto simp: cs_fu_def)

end

subsection \<open>Cycle suns\<close>

locale cycle_sun = sun_graph m "{1..m}" "cs_base m" for m :: nat +
  assumes m4: "4 \<le> m"
begin

lemma adj_uu: "S.vert_adj (Inl i) (Inl j) \<longleftrightarrow> i \<in> {1..m} \<and> j \<in> {1..m} \<and> (j = snext m i \<or> j = sprev m i)"
proof -
  have "S.vert_adj (Inl i) (Inl j) \<longleftrightarrow> (i \<in> {1..m} \<and> j = snext m i) \<or> (j \<in> {1..m} \<and> i = snext m j)"
    unfolding adj_ll Bs.vert_adj_edge unfolding cs_base_def by (auto simp: doubleton_eq_iff)
  note A = this
  have conv: "(j \<in> {1..m} \<and> i = snext m j) \<longleftrightarrow> (i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = sprev m i)"
  proof
    assume a: "j \<in> {1..m} \<and> i = snext m j"
    then show "i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = sprev m i" using snext_in sprev_snext by auto
  next
    assume a: "i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = sprev m i"
    then show "j \<in> {1..m} \<and> i = snext m j" using snext_sprev by auto
  qed
  have conv2: "(i \<in> {1..m} \<and> j = snext m i) \<longleftrightarrow> (i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = snext m i)"
    using snext_in by auto
  show ?thesis using A unfolding conv conv2 by blast
qed

lemma Bs_N:
  assumes i: "i \<in> {1..m}"
  shows "Bs.neighborhood (Inl i) = {Inl (snext m i), Inl (sprev m i)}"
  by (neighborhood_eq nb: Bs.in_neighborhood_iff
      simps: adj_ll[symmetric] adj_uu snext_in[OF i, simplified] sprev_in[OF i, simplified] i[simplified]
      dests: Bs.vert_adj_imp_inV)


lemma sum_u:
  assumes i: "i \<in> {1..m}"
  shows "S.sumN (case_sum fu fv) (Inl i) = fu (snext m i) + fu (sprev m i) + fv i + fv (sprev m i)"
proof -
  have "snext m i \<noteq> sprev m i" using i m4 by (auto simp: snext_def sprev_def)
  then have "Bs.sumN (case_sum fu fv) (Inl i) = fu (snext m i) + fu (sprev m i)"
    unfolding Bs.sumN_def Bs_N[OF i] by simp
  then show ?thesis using sumN_l[OF i] by simp
qed

end

subsection \<open>Wheel suns\<close>

locale wheel_sun = sun_graph m "{0..m}" "ws_base m" for m :: nat +
  assumes m4: "4 \<le> m"
begin

lemma adj_uu: "S.vert_adj (Inl i) (Inl j) \<longleftrightarrow>
    (i \<in> {1..m} \<and> j \<in> {1..m} \<and> (j = snext m i \<or> j = sprev m i))
    \<or> (i = 0 \<and> j \<in> {1..m}) \<or> (j = 0 \<and> i \<in> {1..m})"
proof -
  have "S.vert_adj (Inl i) (Inl j) \<longleftrightarrow> (i \<in> {1..m} \<and> j = snext m i) \<or> (j \<in> {1..m} \<and> i = snext m j)
      \<or> (i = 0 \<and> j \<in> {1..m}) \<or> (j = 0 \<and> i \<in> {1..m})"
    unfolding adj_ll Bs.vert_adj_edge unfolding ws_base_def cs_base_def by (auto simp: doubleton_eq_iff)
  note A = this
  have conv: "(j \<in> {1..m} \<and> i = snext m j) \<longleftrightarrow> (i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = sprev m i)"
  proof
    assume a: "j \<in> {1..m} \<and> i = snext m j"
    then show "i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = sprev m i" using snext_in sprev_snext by auto
  next
    assume a: "i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = sprev m i"
    then show "j \<in> {1..m} \<and> i = snext m j" using snext_sprev by auto
  qed
  have conv2: "(i \<in> {1..m} \<and> j = snext m i) \<longleftrightarrow> (i \<in> {1..m} \<and> j \<in> {1..m} \<and> j = snext m i)"
    using snext_in by auto
  show ?thesis using A unfolding conv conv2 by blast
qed

lemma Bs_N:
  assumes i: "i \<in> {1..m}"
  shows "Bs.neighborhood (Inl i) = {Inl (snext m i), Inl (sprev m i), Inl 0}"
proof -
  have i0: "i \<noteq> 0" using i by simp
  show ?thesis
    by (neighborhood_eq nb: Bs.in_neighborhood_iff
        simps: adj_ll[symmetric] adj_uu snext_in[OF i, simplified] sprev_in[OF i, simplified] i[simplified] i0
        dests: Bs.vert_adj_imp_inV)
qed


lemma adj_w: "S.vert_adj (Inl 0) (Inl j) \<longleftrightarrow> j \<in> {1..m}"
  by (simp add: adj_uu)

lemma Bs_N0: "Bs.neighborhood (Inl 0) = Inl ` {1..m}"
  by (neighborhood_eq nb: Bs.in_neighborhood_iff simps: adj_ll[symmetric] adj_w dests: Bs.vert_adj_imp_inV)


lemma sum_u:
  assumes i: "i \<in> {1..m}"
  shows "S.sumN (case_sum fu fv) (Inl i) = fu (snext m i) + fu (sprev m i) + fu 0 + fv i + fv (sprev m i)"
proof -
  have "snext m i \<noteq> sprev m i" "snext m i \<noteq> 0" "sprev m i \<noteq> 0"
    using i m4 by (auto simp: snext_def sprev_def)
  then have "Bs.sumN (case_sum fu fv) (Inl i) = fu (snext m i) + fu (sprev m i) + fu 0"
    unfolding Bs.sumN_def Bs_N[OF i] by simp
  then show ?thesis using sumN_l[OF i] by simp
qed

lemma sum_w: "S.sumN (case_sum fu fv) (Inl 0) = sum fu {1..m}"
  using sumN_hub[of 0] unfolding Bs.sumN_def Bs_N0 by (simp add: sum_Inl)

end

subsection \<open>Proposition 5\<close>

theorem proposition_5_cycle:
  assumes m4: "4 \<le> m"
  shows "fin_sgraph.eta (sun_verts m {1..m}) (sun_edges m (cs_base m)) = 2"
proof -
  interpret cycle_sun m
    using m4 by unfold_locales (auto simp: cs_base_def snext_def)
  let ?f = "case_sum cs_fu (cs_fv m)"
  have su: "S.sumN ?f (Inl i) = csU m i" if "i \<in> {1..m}" for i
    using sum_u[OF that] cs_sum_u[OF m4 that] by simp
  have sv: "S.sumN ?f (Inr j) = csV m j" if "j \<in> {1..m}" for j
    using sumN_r[OF that] cs_sum_v[OF m4 that] by simp
  have "S.eta \<le> 2"
  proof (eta_upper rule: S.eta_le_coloring)
    show "S.labeling 2 ?f" unfolding S.labeling_def by (auto simp: cs_fu_def cs_fv_def split: sum.split)
  next
    fix x y assume xy: "S.vert_adj x y"
    show "S.sumN ?f x \<noteq> S.sumN ?f y"
    proof (sum_edge_cases adj: xy sym: S.vert_adj_sym rr: adj_rr)
      fix i j assume ll: "S.vert_adj (Inl i) (Inl j)"
      then have ij: "i \<in> {1..m}" "j \<in> {1..m}" "j = snext m i \<or> j = sprev m i" using ll adj_uu by simp_all
      then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inl j)"
        using su csU_next[OF m4 ij(1)] csU_next[OF m4 ij(2)] snext_sprev[OF ij(1)] by auto
    next
      fix i j assume lr: "S.vert_adj (Inl i) (Inr j)"
      then have "j \<in> {1..m}" "i = j \<or> i = snext m j" using lr adj_lr by simp_all
      then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inr j)" using su sv csV_less[OF m4] snext_in by (metis less_irrefl)
    qed
  qed
  then have le2: "S.eta \<le> 2" by simp
  have adj: "S.vert_adj (Inl 1) (Inl 2)" using m4 adj_uu snext_lt[OF m4, of 1] by simp
  have deg: "S.degree (Inl 1) = S.degree (Inl 2)"
    using sum_u[of 1 "\<lambda>_. 1" "\<lambda>_. 1"] sum_u[of 2 "\<lambda>_. 1" "\<lambda>_. 1"] S.sumN_const_1 m4 by simp
  show ?thesis using S.eta_eq_2[OF le2 adj deg] .
qed

theorem proposition_5_wheel:
  assumes m4: "4 \<le> m"
  shows "fin_sgraph.eta (sun_verts m {0..m}) (sun_edges m (ws_base m)) = 2"
proof -
  interpret wheel_sun m
    using m4 by unfold_locales (auto simp: ws_base_def cs_base_def snext_def)
  have adj: "S.vert_adj (Inl 1) (Inl 2)" using m4 adj_uu snext_lt[OF m4, of 1] by simp
  have deg: "S.degree (Inl 1) = S.degree (Inl 2)"
    using sum_u[of 1 "\<lambda>_. 1" "\<lambda>_. 1"] sum_u[of 2 "\<lambda>_. 1" "\<lambda>_. 1"] S.sumN_const_1 m4 by simp
  have "S.eta \<le> 2"
  proof (cases "m = 5")
    case False
    \<comment> \<open>the labeling of \<open>CS_m\<close> plus \<open>f(w) = 1\<close> (\<open>cs_fu 0 = 1\<close>)\<close>
    let ?f = "case_sum cs_fu (cs_fv m)"
    have su: "S.sumN ?f (Inl i) = csU m i + 1" if "i \<in> {1..m}" for i
      using sum_u[OF that] cs_sum_u[OF m4 that] by (simp add: cs_fu_def)
    have sv: "S.sumN ?f (Inr j) = csV m j" if "j \<in> {1..m}" for j
      using sumN_r[OF that] cs_sum_v[OF m4 that] by simp
    have sw: "S.sumN ?f (Inl 0) = m + (m + 1) div 2" using sum_w cs_fu_sum[OF m4, of m] by simp
    have w_neq: "S.sumN ?f (Inl 0) \<noteq> S.sumN ?f (Inl i)" if "i \<in> {1..m}" for i
    proof (cases "m = 4")
      case True
      then show ?thesis using su[OF that] sw by (simp add: csU_def)
    next
      case F: False
      then have "9 \<le> m + (m + 1) div 2" using m4 False by linarith
      then show ?thesis using su[OF that] sw csU_range[OF m4 that] by simp
    qed
    have "S.eta \<le> 2"
    proof (eta_upper rule: S.eta_le_coloring)
      show "S.labeling 2 ?f" unfolding S.labeling_def by (auto simp: cs_fu_def cs_fv_def split: sum.split)
    next
      fix x y assume xy: "S.vert_adj x y"
      show "S.sumN ?f x \<noteq> S.sumN ?f y"
      proof (sum_edge_cases adj: xy sym: S.vert_adj_sym rr: adj_rr)
        fix i j assume ll: "S.vert_adj (Inl i) (Inl j)"
        then have "(i \<in> {1..m} \<and> j \<in> {1..m} \<and> (j = snext m i \<or> j = sprev m i))
            \<or> (i = 0 \<and> j \<in> {1..m}) \<or> (j = 0 \<and> i \<in> {1..m})" using ll adj_uu by simp
        then consider (a) "i \<in> {1..m}" "j \<in> {1..m}" "j = snext m i \<or> j = sprev m i"
          | (b) "i = 0" "j \<in> {1..m}" | (c) "j = 0" "i \<in> {1..m}" by blast
        then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inl j)"
        proof cases
          case a
          note ij = a
          then show ?thesis
            using su csU_next[OF m4 ij(1)] csU_next[OF m4 ij(2)] snext_sprev[OF ij(1)] by auto
        next
          case b then show ?thesis using w_neq by simp
        next
          case c then show ?thesis using w_neq by metis
        qed
      next
        fix i j assume lr: "S.vert_adj (Inl i) (Inr j)"
        then have "j \<in> {1..m}" "i = j \<or> i = snext m j" using lr adj_lr by simp_all
        then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inr j)" using su sv csV_less[OF m4] snext_in by (metis less_SucI less_irrefl Suc_eq_plus1)
      qed
    qed
    then show ?thesis by simp
  next
    case True
    \<comment> \<open>the special labeling of \<open>WS_5\<close>\<close>
    define fu where "fu i = (if i = 3 \<or> i = 5 \<or> i = 0 then 2 else 1::nat)" for i :: nat
    define fv where "fv j = (if j \<le> 3 then 2 else 1::nat)" for j :: nat
    let ?f = "case_sum fu fv"
    have sn: "snext m 1 = 2" "snext m 2 = 3" "snext m 3 = 4" "snext m 4 = 5" "snext m 5 = 1"
      and sp: "sprev m 1 = 5" "sprev m 2 = 1" "sprev m 3 = 2" "sprev m 4 = 3" "sprev m 5 = 4"
      using True by (simp_all add: snext_def sprev_def)
    have su: "S.sumN ?f (Inl i) = (if i = 5 then 6 else if odd i then 8 else 9)" if "i \<in> {1..m}" for i
    proof -
      have "i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5" using that True by auto
      then show ?thesis using sum_u[OF that, of fu fv] sn sp by (auto simp: fu_def fv_def)
    qed
    have sv: "S.sumN ?f (Inr j) = (if j = 1 then 2 else 3)" if "j \<in> {1..m}" for j
    proof -
      have "j = 1 \<or> j = 2 \<or> j = 3 \<or> j = 4 \<or> j = 5" using that True by auto
      then show ?thesis using sumN_r[OF that, of fu fv] sn by (auto simp: fu_def)
    qed
    have sw: "S.sumN ?f (Inl 0) = 7"
      using sum_w[of fu fv] True by (simp add: fu_def numeral_eq_Suc atLeastAtMostSuc_conv)
    have "S.eta \<le> 2"
    proof (eta_upper rule: S.eta_le_coloring)
      show "S.labeling 2 ?f" unfolding S.labeling_def by (auto simp: fu_def fv_def split: sum.split)
    next
      fix x y assume xy: "S.vert_adj x y"
      show "S.sumN ?f x \<noteq> S.sumN ?f y"
      proof (sum_edge_cases adj: xy sym: S.vert_adj_sym rr: adj_rr)
        fix i j assume ll: "S.vert_adj (Inl i) (Inl j)"
        then have "(i \<in> {1..m} \<and> j \<in> {1..m} \<and> (j = snext m i \<or> j = sprev m i))
            \<or> (i = 0 \<and> j \<in> {1..m}) \<or> (j = 0 \<and> i \<in> {1..m})" using ll adj_uu by simp
        then consider (a) "i \<in> {1..m}" "j \<in> {1..m}" "j = snext m i \<or> j = sprev m i"
          | (b) "i = 0" "j \<in> {1..m}" | (c) "j = 0" "i \<in> {1..m}" by blast
        then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inl j)"
        proof cases
          case a
          note ij = a
          have "i = 1 \<or> i = 2 \<or> i = 3 \<or> i = 4 \<or> i = 5" using ij True by auto
          then show ?thesis using su[OF ij(1)] su[OF ij(2)] ij(3) sn sp by auto
        next
          case b then show ?thesis using su sw by auto
        next
          case c then show ?thesis using su sw by auto
        qed
      next
        fix i j assume lr: "S.vert_adj (Inl i) (Inr j)"
        then have "j \<in> {1..m}" "i = j \<or> i = snext m j" using lr adj_lr by simp_all
        then have "i \<in> {1..m}" using snext_in by auto
        then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inr j)" using su[OF \<open>i \<in> {1..m}\<close>] sv[OF \<open>j \<in> {1..m}\<close>] by auto
      qed
    qed
    then show ?thesis by simp
  qed
  then show ?thesis using S.eta_eq_2 adj deg by blast
qed

end

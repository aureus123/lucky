theory ACN_Sec3_Families
  imports ACN_Sec3
begin

section \<open>Fans, windmills and wheels (Section 3)\<close>

context fin_sgraph
begin

lemma max_degree_le: "V \<noteq> {} \<Longrightarrow> (\<And>v. v \<in> V \<Longrightarrow> degree v \<le> d) \<Longrightarrow> max_degree \<le> d"
  unfolding max_degree_def using finV by (subst Max_le_iff) auto

end

context join_complete
begin

text \<open>Joining one vertex to a graph without universal vertices keeps \<open>\<eta>\<close>.\<close>

corollary theorem_2_K1:
  assumes "U = {w}" "G.max_degree + 2 \<le> card V"
  shows "J.eta = G.eta"
proof -
  have "q \<le> card V - G.max_degree - 1" using assms by simp
  then show ?thesis using theorem_2 G.eta_pos assms(1) by simp
qed

end

subsection \<open>Paths and fans\<close>

text \<open>The path on the vertices \<open>0, \<dots>, N - 1\<close>; the paper's \<open>P_{n+1}\<close> is \<open>N = n + 1\<close>.\<close>

definition path_edges :: "nat \<Rightarrow> nat edge set" where
  "path_edges N = {{i, Suc i} | i. Suc i < N}"

lemma path_fin_sgraph: "fin_sgraph {..<N} (path_edges N)"
  by unfold_locales (auto simp: path_edges_def)

locale path_graph =
  fixes N :: nat
begin

sublocale P: fin_sgraph "{..<N}" "path_edges N" by (rule path_fin_sgraph)

lemma adj_iff: "P.vert_adj i j \<longleftrightarrow> (j = Suc i \<and> j < N) \<or> (i = Suc j \<and> i < N)"
  unfolding P.vert_adj_edge unfolding path_edges_def by (simp add: doubleton_eq_iff) blast

lemma neighborhood_eq:
  assumes "i < N"
  shows "P.neighborhood i = (if 0 < i then {i - 1} else {}) \<union> (if Suc i < N then {Suc i} else {})"
  using assms by (auto simp: P.in_neighborhood_iff adj_iff)

lemma sumN_eq:
  assumes "i < N"
  shows "P.sumN f i = (if 0 < i then f (i - 1) else 0) + (if Suc i < N then f (Suc i) else 0)"
  unfolding P.sumN_def neighborhood_eq[OF assms] by (cases i) auto

lemma degree_eq: "i < N \<Longrightarrow> P.degree i = (if 0 < i then 1 else 0) + (if Suc i < N then 1 else 0)"
  using sumN_eq[of i "\<lambda>_. 1"] P.sumN_const_1 by simp

lemma path_eta:
  assumes "4 \<le> N"
  shows "P.eta = 2"
proof -
  have adj: "P.vert_adj 1 2" "P.degree 1 = P.degree 2" using assms by (simp_all add: adj_iff degree_eq)
  have "P.eta \<le> 2"
  proof -
    define f where "f i = (if even i \<or> i = N - 1 then 2 else 1::nat)" for i
    have "P.eta \<le> 2"
    proof (eta_upper rule: P.eta_le_coloring)
      show "P.labeling 2 f" by (simp add: P.labeling_def f_def)
    next
      fix i j assume "P.vert_adj i j"
      then consider "j = Suc i" "Suc i < N" | "i = Suc j" "Suc j < N" by (auto simp: adj_iff)
      then show "P.sumN f i \<noteq> P.sumN f j"
      proof cases
        case 1
        then show ?thesis using assms by (simp add: sumN_eq f_def) presburger
      next
        case 2
        then show ?thesis using assms by (simp add: sumN_eq f_def) presburger
      qed
    qed
    then show ?thesis by simp
  qed
  then show ?thesis using P.eta_eq_2 adj by blast
qed

lemma path_max_degree:
  assumes "1 \<le> N"
  shows "P.max_degree \<le> 2"
proof (rule P.max_degree_le)
  show "{..<N} \<noteq> {}" using assms by (metis lessThan_iff empty_iff less_le_trans zero_less_one)
qed (auto simp: degree_eq)

end

text \<open>The fan \<open>F_n = P_{n+1} \<or> K_1\<close>, with apex \<open>n + 1\<close>.\<close>

theorem fan:
  assumes "3 \<le> n"
  shows "fin_sgraph.eta ({..<Suc n} \<union> {Suc n}) (join_edges (path_edges (Suc n)) {..<Suc n} {Suc n}) = 2"
proof -
  interpret path_graph "Suc n" .
  interpret join_complete "{..<Suc n}" "path_edges (Suc n)" "{Suc n}" by unfold_locales auto
  have "J.eta = P.eta" using path_max_degree assms by (intro theorem_2_K1) auto
  then show ?thesis using path_eta assms by simp
qed

subsection \<open>Windmills\<close>

text \<open>\<open>m K_p\<close>: \<open>m\<close> disjoint copies of \<open>K_p\<close>; the vertex \<open>(i, j)\<close> is the \<open>j\<close>-th vertex of copy \<open>i\<close>.\<close>

definition copies_edges :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) edge set" where
  "copies_edges m p = {{(i, j), (i, j')} | i j j'. i < m \<and> j < p \<and> j' < p \<and> j \<noteq> j'}"

lemma copies_fin_sgraph: "fin_sgraph ({..<m} \<times> {..<p}) (copies_edges m p)"
  by unfold_locales (auto simp: copies_edges_def)

locale copies_graph =
  fixes m p :: nat
begin

sublocale K: fin_sgraph "{..<m} \<times> {..<p}" "copies_edges m p" by (rule copies_fin_sgraph)

lemma adj_iff: "K.vert_adj x y \<longleftrightarrow> fst x = fst y \<and> fst x < m \<and> snd x < p \<and> snd y < p \<and> snd x \<noteq> snd y"
  unfolding K.vert_adj_edge unfolding copies_edges_def by (cases x; cases y) (auto simp: doubleton_eq_iff)

lemma neighborhood_eq: "x \<in> {..<m} \<times> {..<p} \<Longrightarrow> K.neighborhood x = {fst x} \<times> ({..<p} - {snd x})"
  by (cases x) (auto simp: K.in_neighborhood_iff adj_iff)

lemma copies_eta:
  assumes "1 \<le> m" "1 \<le> p"
  shows "K.eta = p"
proof (rule order.antisym)
  define f where "f x = Suc (snd x)" for x :: "nat \<times> nat"
  have sum: "K.sumN f x + f x = (\<Sum>j<p. Suc j)" if "x \<in> {..<m} \<times> {..<p}" for x
  proof -
    have "(\<Sum>j<p. Suc j) = Suc (snd x) + (\<Sum>j\<in>{..<p} - {snd x}. Suc j)"
      using that by (auto simp: sum.remove)
    moreover have "K.sumN f x = (\<Sum>j\<in>{..<p} - {snd x}. Suc j)"
    proof -
      have "{fst x} \<times> ({..<p} - {snd x}) = Pair (fst x) ` ({..<p} - {snd x})" by auto
      then show ?thesis
        unfolding K.sumN_def neighborhood_eq[OF that] f_def by (simp add: sum.reindex inj_on_def)
    qed
    ultimately show ?thesis by (simp add: f_def)
  qed
  have "K.eta \<le> p"
  proof (eta_upper rule: K.eta_le_coloring)
    show "K.labeling p f" by (auto simp: K.labeling_def f_def)
  next
    fix x y assume xy: "K.vert_adj x y"
    then have "x \<in> {..<m} \<times> {..<p}" "y \<in> {..<m} \<times> {..<p}" "f x \<noteq> f y"
      by (auto simp: adj_iff f_def mem_Times_iff)
    then show "K.sumN f x \<noteq> K.sumN f y" using sum by (metis add_left_cancel add.commute)
  next
    show "0 < p" using assms by simp
  qed
  then show "K.eta \<le> p" using assms by simp
next
  have "card ({0::nat} \<times> {..<p}) \<le> K.eta"
  proof (rule K.observation_2)
    show "{0::nat} \<times> {..<p} \<subseteq> {..<m} \<times> {..<p}" using assms by auto
  next
    fix x y assume "x \<in> {0::nat} \<times> {..<p}" "y \<in> {0::nat} \<times> {..<p}"
    then show "K.true_twins x y"
      using assms unfolding K.true_twins_def by (auto simp: neighborhood_eq)
  qed
  then show "p \<le> K.eta" by (simp add: card_cartesian_product)
qed

lemma copies_degree: "x \<in> {..<m} \<times> {..<p} \<Longrightarrow> K.degree x = p - 1"
  by (cases x) (simp add: K.degree_eq neighborhood_eq card_cartesian_product)

end

text \<open>The windmill \<open>W_n^m = m K_{n-1} \<or> K_1\<close> (\<open>n \<ge> 3\<close>, \<open>m \<ge> 2\<close>), with center \<open>(m, 0)\<close>.\<close>

theorem windmill:
  assumes "3 \<le> n" "2 \<le> m"
  shows "fin_sgraph.eta ({..<m} \<times> {..<n - 1} \<union> {(m, 0)})
           (join_edges (copies_edges m (n - 1)) ({..<m} \<times> {..<n - 1}) {(m, 0)}) = n - 1"
proof -
  interpret copies_graph m "n - 1" .
  interpret join_complete "{..<m} \<times> {..<n - 1}" "copies_edges m (n - 1)" "{(m, 0)}"
    by unfold_locales auto
  have "K.max_degree \<le> n - 2"
  proof (rule K.max_degree_le)
    show "{..<m} \<times> {..<n - 1} \<noteq> {}" using assms by (auto simp: lessThan_empty_iff)
  next
    fix v assume "v \<in> {..<m} \<times> {..<n - 1}"
    then show "K.degree v \<le> n - 2" using copies_degree[of v] by simp
  qed
  moreover have "card ({..<m} \<times> {..<n - 1}) = m * (n - 1)" by (simp add: card_cartesian_product)
  moreover have "n - 2 + 2 \<le> m * (n - 1)"
  proof -
    have "2 * (n - 1) \<le> m * (n - 1)" using assms by simp
    then show ?thesis using assms by linarith
  qed
  ultimately have "J.eta = K.eta" by (intro theorem_2_K1) auto
  then show ?thesis using copies_eta assms by simp
qed

subsection \<open>Circuits and wheels\<close>

text \<open>The circuit \<open>C_n\<close> on \<open>0, \<dots>, n - 1\<close>, with successor and predecessor modulo \<open>n\<close>.\<close>

definition csucc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "csucc n i = (if Suc i = n then 0 else Suc i)"

definition cpred :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "cpred n i = (if i = 0 then n - 1 else i - 1)"

definition cycle_edges :: "nat \<Rightarrow> nat edge set" where
  "cycle_edges n = {{i, csucc n i} | i. i < n}"

lemma cycle_fin_sgraph: "2 \<le> n \<Longrightarrow> fin_sgraph {..<n} (cycle_edges n)"
  by unfold_locales (auto simp: cycle_edges_def csucc_def)

locale cycle_graph =
  fixes n :: nat
  assumes n3: "3 \<le> n"
begin

sublocale C: fin_sgraph "{..<n}" "cycle_edges n" using n3 by (intro cycle_fin_sgraph) simp

lemma csucc_lt: "i < n \<Longrightarrow> csucc n i < n" and cpred_lt: "i < n \<Longrightarrow> cpred n i < n"
  using n3 by (auto simp: csucc_def cpred_def)

lemma csucc_eq_iff: "i < n \<Longrightarrow> j < n \<Longrightarrow> i = csucc n j \<longleftrightarrow> j = cpred n i"
  using n3 by (auto simp: csucc_def cpred_def)

lemma adj_iff: "C.vert_adj i j \<longleftrightarrow> i < n \<and> j < n \<and> (j = csucc n i \<or> j = cpred n i)"
proof -
  have "C.vert_adj i j \<longleftrightarrow> (i < n \<and> j = csucc n i) \<or> (j < n \<and> i = csucc n j)"
    unfolding C.vert_adj_edge unfolding cycle_edges_def by (simp add: doubleton_eq_iff) blast
  also have "\<dots> \<longleftrightarrow> i < n \<and> j < n \<and> (j = csucc n i \<or> i = csucc n j)"
    using csucc_lt by blast
  also have "\<dots> \<longleftrightarrow> i < n \<and> j < n \<and> (j = csucc n i \<or> j = cpred n i)"
    using csucc_eq_iff by blast
  finally show ?thesis .
qed

lemma neighborhood_eq: "i < n \<Longrightarrow> C.neighborhood i = {csucc n i, cpred n i}"
  using csucc_lt cpred_lt by (auto simp: C.in_neighborhood_iff adj_iff)

lemma csucc_neq_cpred: "i < n \<Longrightarrow> csucc n i \<noteq> cpred n i"
  using n3 by (auto simp: csucc_def cpred_def)

lemma sumN_eq: "i < n \<Longrightarrow> C.sumN f i = f (csucc n i) + f (cpred n i)"
  unfolding C.sumN_def by (simp add: neighborhood_eq csucc_neq_cpred)

lemma cycle_degree: "i < n \<Longrightarrow> C.degree i = 2"
  using sumN_eq[of i "\<lambda>_. 1"] C.sumN_const_1 by simp

lemma cycle_max_degree: "C.max_degree \<le> 2"
  using n3 by (intro C.max_degree_le) (auto simp: cycle_degree lessThan_empty_iff)

lemma cpred_csucc: "i < n \<Longrightarrow> cpred n (csucc n i) = i"
  and csucc_cpred: "i < n \<Longrightarrow> csucc n (cpred n i) = i"
  using n3 by (auto simp: csucc_def cpred_def)

text \<open>Even circuits are regular bipartite, so Corollary 1 applies.\<close>

lemma eta_even:
  assumes "even n"
  shows "C.eta = 2"
proof (rule C.corollary_1)
  show "{i. i < n \<and> even i} \<inter> {i. i < n \<and> odd i} = {}" by auto
  show "{i. i < n \<and> even i} \<union> {i. i < n \<and> odd i} = {..<n}" by auto
next
  fix i j assume "C.vert_adj i j"
  then show "i \<in> {i. i < n \<and> even i} \<longleftrightarrow> j \<in> {i. i < n \<and> odd i}"
    using assms n3 by (auto simp: adj_iff csucc_def cpred_def split: if_split_asm)
next
  show "\<And>u v. u \<in> {..<n} \<Longrightarrow> v \<in> {..<n} \<Longrightarrow> C.degree u = C.degree v" by (simp add: cycle_degree)
  have "{0, csucc n 0} \<in> cycle_edges n"
    unfolding cycle_edges_def by (rule CollectI, rule exI[of _ 0]) (use n3 in simp)
  then show "cycle_edges n \<noteq> {}" by blast
qed

text \<open>Proposition 1: \<open>\<eta>(C_n) = 3\<close> for odd \<open>n \<ge> 5\<close>.\<close>

theorem proposition_1:
  assumes odd: "odd n" and n5: "5 \<le> n"
  shows "C.eta = 3"
proof (rule order.antisym)
  \<comment> \<open>the labeling of the appendix; vertex \<open>k\<close> is the paper's \<open>v_{k+1}\<close>\<close>
  define f where "f k = (if k = 0 then 2 else if k = 2 then 3 else if k \<le> 4 then 1
      else if odd k then 1 else 3::nat)" for k :: nat
  define S where "S k = (if k = 0 then (if n = 5 then 2 else 4) else if k = 1 then 5 else if k = 2 then 2
      else if k = 3 then 4 else if k = n - 1 then 3 else if even k then 2 else if k = 5 then 4 else 6::nat)"
    for k :: nat
  have last: "n - 1 \<noteq> 0" "n - 1 \<noteq> 1" "n - 1 \<noteq> 2" "n - 1 \<noteq> 3" using n5 by linarith+
  have succ: "k < n - 1 \<Longrightarrow> csucc n k = Suc k" "csucc n (n - 1) = 0" for k
    using n5 by (auto simp: csucc_def)
  have pred: "0 < k \<Longrightarrow> cpred n k = k - 1" "cpred n 0 = n - 1" for k
    by (auto simp: cpred_def)
  have sumS: "C.sumN f k = S k" if kn: "k < n" for k
  proof -
    have "C.sumN f k = f (csucc n k) + f (cpred n k)" using that by (rule sumN_eq)
    also have "\<dots> = S k"
    proof -
      have fodd: "f j = 1" if "odd j" "3 \<le> j" for j using that by (auto simp: f_def)
      have feven: "f j = 3" if "even j" "6 \<le> j" for j using that by (auto simp: f_def)
      have n1: "even (n - 1)" "odd (n - 2)" using odd n5 by presburger+
      consider "k = n - 1" | "k = 0" | "k = 1" | "k = 2" | "k = 3" | "k = 4" "k < n - 1"
        | "k = 5" "k < n - 1" | "6 \<le> k" "k < n - 1"
        using kn by linarith
      then show ?thesis
      proof cases
        case 1
        then have "S k = 3" using last by (simp add: S_def)
        moreover have "f (n - 2) = 1" using fodd n1 n5 by simp
        moreover have "csucc n k = 0" "cpred n k = n - 2" using 1 succ(2) pred(1) n5 by simp_all
        ultimately show ?thesis by (simp add: f_def)
      next
        case 2
        have "f (n - 1) = (if n = 5 then 1 else 3)"
        proof (cases "n = 5")
          case True
          then show ?thesis by (simp add: f_def)
        next
          case False
          then have "6 \<le> n - 1" using n5 odd by presburger
          then show ?thesis using feven n1 False by simp
        qed
        then show ?thesis using 2 n5 by (simp add: succ pred S_def f_def)
      next
        case 3 then show ?thesis using n5 by (simp add: succ pred S_def f_def)
      next
        case 4 then show ?thesis using n5 by (simp add: succ pred S_def f_def)
      next
        case 5 then show ?thesis using n5 by (simp add: succ pred S_def f_def)
      next
        case 6 then show ?thesis using n5 by (simp add: succ pred S_def f_def)
      next
        case 7
        have "f 6 = 3" by (simp add: f_def)
        then show ?thesis using 7 by (simp add: succ pred S_def f_def)
      next
        case 8
        then have k: "csucc n k = Suc k" "cpred n k = k - 1" "k \<noteq> n - 1" "k \<noteq> 5"
          by (simp_all add: succ pred)
        show ?thesis
        proof (cases "even k")
          case True
          then have "odd (Suc k)" "odd (k - 1)" using 8 by presburger+
          then have "f (Suc k) = 1" "f (k - 1) = 1" using 8 fodd by simp_all
          then show ?thesis using True k 8 by (simp add: S_def)
        next
          case False
          then have "even (Suc k)" "even (k - 1)" "6 \<le> k - 1" using 8 by presburger+
          then have "f (Suc k) = 3" "f (k - 1) = 3" using 8 feven by simp_all
          then show ?thesis using False k 8 by (simp add: S_def)
        qed
      qed
    qed
    finally show ?thesis .
  qed
  have "C.eta \<le> 3"
  proof (eta_upper rule: C.eta_le_coloring)
    show "C.labeling 3 f" by (simp add: C.labeling_def f_def)
  next
    fix i j assume "C.vert_adj i j"
    then have ij: "i < n" "j < n" "j = csucc n i \<or> i = csucc n j"
      using adj_iff csucc_eq_iff by auto
    have Sgen: "S k = (if even k then 2 else if k = 5 then 4 else 6)" if "4 \<le> k" "k < n - 1" for k
      using that by (simp add: S_def)
    have Slast: "S (n - 1) = 3" using last by (simp add: S_def)
    have neq: "S k \<noteq> S (csucc n k)" if "k < n" for k
    proof (cases "k = n - 1")
      case True
      then show ?thesis using Slast succ(2) by (simp add: S_def)
    next
      case False
      then have k: "k < n - 1" "csucc n k = Suc k" using that succ(1) by simp_all
      consider "k \<le> 3" | "4 \<le> k" "Suc k = n - 1" | "4 \<le> k" "Suc k < n - 1" using k by linarith
      then show ?thesis
      proof cases
        case 1
        then show ?thesis using k n5 by (auto simp: S_def numeral_eq_Suc le_Suc_eq)
      next
        case 2
        then show ?thesis using k Slast Sgen[of k] by auto
      next
        case 3
        then show ?thesis using k Sgen[of k] Sgen[of "Suc k"] by auto
      qed
    qed
    show "C.sumN f i \<noteq> C.sumN f j"
      using ij neq sumS by (metis)
  qed
  then show "C.eta \<le> 3" by simp
next
  \<comment> \<open>lower bound: no additive 2-coloring\<close>
  show "3 \<le> C.eta"
  proof (rule ccontr)
    assume "\<not> 3 \<le> C.eta"
    then have "C.eta \<le> 2" by simp
    obtain f where "C.additive_coloring C.eta f" by (rule C.eta_attained)
    then have f: "C.additive_coloring 2 f" using \<open>C.eta \<le> 2\<close> by (rule C.additive_coloring_mono)
    define s where "s k = C.sumN f k" for k
    have lab: "f k \<in> {1, 2}" if "k < n" for k
    proof -
      have "1 \<le> f k \<and> f k \<le> 2" using f that by (simp add: C.additive_coloring_def C.labeling_def)
      then show ?thesis by (cases "f k = 1") auto
    qed
    have s: "s k = f (csucc n k) + f (cpred n k)" if "k < n" for k
      using that by (simp add: s_def sumN_eq)
    have adj_neq: "s k \<noteq> s (csucc n k)" if "k < n" for k
      using f that csucc_lt by (simp add: s_def C.additive_coloring_def adj_iff)
    define b where "b k \<longleftrightarrow> s k < s (csucc n k)" for k
    \<comment> \<open>two consecutive arcs point the same way, otherwise the orientation alternates around an odd circuit\<close>
    have "\<exists>k<n. b (cpred n k) = b k"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have alt: "b (csucc n k) \<noteq> b k" if "k < n" for k
        using that csucc_lt cpred_csucc by metis
      have par: "b k = (if even k then b 0 else \<not> b 0)" if "k < n" for k
        using that
      proof (induction k)
        case (Suc k)
        then have "csucc n k = Suc k" by (simp add: csucc_def)
        then show ?case using Suc alt[of k] by auto
      qed simp
      have "even (n - 1)" using odd by presburger
      then have "b (n - 1) = b 0" using par[of "n - 1"] n5 by simp
      moreover have "b (csucc n (n - 1)) \<noteq> b (n - 1)" using alt n5 by simp
      moreover have "csucc n (n - 1) = 0" using n5 by (simp add: csucc_def)
      ultimately show False by simp
    qed
    then obtain k where k: "k < n" "b (cpred n k) = b k" by blast
    let ?p = "cpred n k" and ?s = "csucc n k"
    have p: "?p < n" "csucc n ?p = k" and sn: "?s < n" "cpred n ?s = k"
      using k cpred_lt csucc_lt csucc_cpred cpred_csucc by auto
    have range: "s j \<in> {2, 3, 4}" if "j < n" for j
      using s[OF that] lab[OF csucc_lt[OF that]] lab[OF cpred_lt[OF that]] by auto
    have "s ?p \<noteq> s k" "s k \<noteq> s ?s" using adj_neq[OF p(1)] adj_neq[OF k(1)] p(2) by auto
    then have mono: "(s ?p < s k \<and> s k < s ?s) \<or> (s ?s < s k \<and> s k < s ?p)"
      using k(2) p(2) by (auto simp: b_def)
    then have "(s ?p = 2 \<and> s ?s = 4) \<or> (s ?s = 2 \<and> s ?p = 4)"
      using range[OF p(1)] range[OF k(1)] range[OF sn(1)] by auto
    moreover have "s ?p = f k + f (cpred n ?p)" using s[OF p(1)] p(2) by simp
    moreover have "s ?s = f (csucc n ?s) + f k" using s[OF sn(1)] sn(2) by simp
    ultimately show False
      using lab[OF k(1)] lab[OF cpred_lt[OF p(1)]] lab[OF csucc_lt[OF sn(1)]] by auto
  qed
qed

end

text \<open>The wheel \<open>W_n = C_n \<or> K_1\<close> (\<open>n \<ge> 4\<close>), with hub \<open>n\<close>.\<close>

theorem wheel:
  assumes "4 \<le> n"
  shows "fin_sgraph.eta ({..<n} \<union> {n}) (join_edges (cycle_edges n) {..<n} {n}) =
           (if even n then 2 else 3)"
proof -
  interpret cycle_graph n using assms by unfold_locales simp
  interpret join_complete "{..<n}" "cycle_edges n" "{n}" by unfold_locales auto
  have "J.eta = C.eta" using cycle_max_degree assms by (intro theorem_2_K1) auto
  moreover have "odd n \<Longrightarrow> 5 \<le> n" using assms by presburger
  ultimately show ?thesis using eta_even proposition_1 by auto
qed

end

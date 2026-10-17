theory ACN_Sec4
  imports ACN_Sec3
begin

section \<open>Split graphs (Section 4)\<close>

subsection \<open>Theorem 3: an upper bound for split graphs\<close>

text \<open>
  A split graph with clique \<open>Q\<close> and stable set \<open>S\<close>; \<open>Q\<close> is maximal, i.e. no vertex of \<open>S\<close> is
  adjacent to all of \<open>Q\<close>.
\<close>

locale split_graph = fin_sgraph +
  fixes Q S :: "'a set"
  assumes split_part: "Q \<union> S = V" "Q \<inter> S = {}"
    and split_clique: "clique Q"
    and split_stable: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> \<not> vert_adj a b"
    and split_maximal: "\<And>v. v \<in> S \<Longrightarrow> \<exists>u\<in>Q. \<not> vert_adj u v"
begin

lemma finQ: "finite Q" and finS: "finite S"
  using split_part finV by (metis finite_Un)+

lemma neighborhood_Q:
  assumes "u \<in> Q"
  shows "neighborhood u = (Q - {u}) \<union> (neighborhood u \<inter> S)"
proof -
  have "Q - {u} \<subseteq> neighborhood u"
  proof
    fix x assume "x \<in> Q - {u}"
    then have "vert_adj u x" using clique_adj[OF split_clique assms, of x] by auto
    then show "x \<in> neighborhood u" by (simp add: in_neighborhood_iff)
  qed
  moreover have "neighborhood u \<subseteq> Q \<union> S" using neighborhood_subset split_part by blast
  ultimately show ?thesis using not_in_own_neighborhood by blast
qed

lemma neighborhood_S: "v \<in> S \<Longrightarrow> neighborhood v \<subseteq> Q"
  using neighborhood_subset split_part split_stable in_neighborhood_iff by blast

abbreviation r :: "'a \<Rightarrow> nat" where "r u \<equiv> card (neighborhood u \<inter> S)"

lemma degree_Q:
  assumes "u \<in> Q"
  shows "degree u + 1 = card Q + r u"
proof -
  have "degree u = card (Q - {u}) + r u"
    unfolding degree_eq using finQ finS
    by (subst neighborhood_Q[OF assms]) (auto intro!: card_Un_disjoint simp: split_part(2) [symmetric])
  then show ?thesis using assms finQ by (simp add: card_Diff_singleton) (metis Suc_pred card_gt_0_iff empty_iff)
qed

lemma sumN_Q:
  assumes "u \<in> Q" "\<And>w. w \<in> S \<Longrightarrow> f w = c"
  shows "sumN f u + f u = sum f Q + c * r u"
proof -
  have disj: "(Q - {u}) \<inter> (neighborhood u \<inter> S) = {}" using split_part(2) by blast
  have "sumN f u = sum f (Q - {u}) + sum f (neighborhood u \<inter> S)"
    unfolding sumN_def using finQ finS disj by (subst neighborhood_Q[OF assms(1)]) (simp add: sum.union_disjoint)
  moreover have "sum f (neighborhood u \<inter> S) = c * r u" using assms(2) by simp
  moreover have "sum f Q = f u + sum f (Q - {u})" using assms(1) finQ by (simp add: sum.remove)
  ultimately show ?thesis by simp
qed

lemma int_eq_aux: "(a::nat) + c * b = d + c * e \<Longrightarrow> int a - int d = int c * (int e - int b)"
proof -
  assume "a + c * b = d + c * e"
  then have "int a + int c * int b = int d + int c * int e" by (metis of_nat_add of_nat_mult)
  then show ?thesis by (simp add: algebra_simps)
qed

theorem theorem_3:
  assumes T: "T \<subseteq> Q" "T \<noteq> {}" and degT: "inj_on degree T"
  shows "eta \<le> card Q - card T + 1"
proof -
  let ?c = "card Q - card T + 1"
  have finT: "finite T" using T finQ finite_subset by blast
  have cardQT: "card (Q - T) = card Q - card T" using T finT by (simp add: card_Diff_subset)
  obtain h :: "'a \<Rightarrow> nat" and k where h: "h ` (Q - T) = {i. i < k}" "inj_on h (Q - T)"
    using finite_imp_inj_to_nat_seg[of "Q - T"] finQ by blast
  have k: "k = card Q - card T" using h cardQT by (metis card_Collect_less_nat card_image)
  define f where "f x = (if x \<in> Q - T then h x + 1 else ?c)" for x
  have fQT: "1 \<le> f x \<and> f x < ?c" if x: "x \<in> Q - T" for x
  proof -
    have "h x < k" using h(1) x by blast
    then show ?thesis using x k by (simp add: f_def)
  qed
  have fc: "f x = ?c" if "x \<notin> Q - T" for x unfolding f_def using that by (rule if_not_P)
  have fS: "f w = ?c" if "w \<in> S" for w using that split_part fc by blast
  have flab: "1 \<le> f x \<and> f x \<le> ?c" for x
  proof (cases "x \<in> Q - T")
    case True
    then show ?thesis using fQT[OF True] by simp
  next
    case False
    then show ?thesis using fc[OF False] by simp
  qed
  have sQ: "sumN f u + f u = sum f Q + ?c * r u" if "u \<in> Q" for u using sumN_Q[OF that fS] .
  have sS: "sumN f v + 1 \<le> sum f Q" if vS: "v \<in> S" for v
  proof -
    obtain u0 where u0: "u0 \<in> Q" "\<not> vert_adj u0 v" using split_maximal[OF vS] by blast
    then have "neighborhood v \<subseteq> Q - {u0}"
      using neighborhood_S[OF vS] by (auto simp: in_neighborhood_iff vert_adj_sym)
    then have "sumN f v \<le> sum f (Q - {u0})" unfolding sumN_def using finQ by (intro sum_mono2) auto
    moreover have "sum f Q = f u0 + sum f (Q - {u0})" using u0 finQ by (simp add: sum.remove)
    ultimately show ?thesis using flab[of u0] by linarith
  qed
  have "eta \<le> ?c"
  proof (eta_upper rule: eta_le_coloring)
    show "labeling ?c f" using flab by (simp add: labeling_def)
  next
    fix x y assume xy: "vert_adj x y"
    then have xyV: "x \<in> Q \<union> S" "y \<in> Q \<union> S" using vert_adj_imp_inV split_part by auto
    have QS: "sumN f v < sumN f u" if "u \<in> Q" "v \<in> S" "vert_adj u v" for u v
    proof -
      have "v \<in> neighborhood u \<inter> S" using that by (simp add: in_neighborhood_iff)
      then have "1 \<le> r u" using finS by (metis card_gt_0_iff empty_iff finite_Int One_nat_def Suc_leI)
      then have "?c * 1 \<le> ?c * r u" by (rule mult_le_mono2)
      then have "?c \<le> ?c * r u" by simp
      then have "sum f Q \<le> sumN f u" using sQ[OF that(1)] flab[of u] by linarith
      then show ?thesis using sS[OF that(2)] by linarith
    qed
    show "sumN f x \<noteq> sumN f y"
    proof (cases "x \<in> Q \<and> y \<in> Q")
      case True
      show ?thesis
      proof
        assume eq: "sumN f x = sumN f y"
        have xy_neq: "x \<noteq> y" using xy vert_adj_neq by blast
        have xQ: "x \<in> Q" and yQ: "y \<in> Q" using True by auto
        have N: "f x + ?c * r y = f y + ?c * r x" using sQ[OF xQ] sQ[OF yQ] eq by linarith
        have I: "int (f x) - int (f y) = int ?c * (int (r x) - int (r y))"
          using int_eq_aux[OF N] .
        show False
        proof (cases "r x = r y")
          case True
          then have fxy: "f x = f y" using I by simp
          have "x \<in> T \<and> y \<in> T"
          proof (cases "x \<in> T"; cases "y \<in> T")
            assume "x \<notin> T" "y \<notin> T"
            then have "h x = h y" using fxy xQ yQ by (simp add: f_def)
            then show ?thesis using h(2) \<open>x \<notin> T\<close> \<open>y \<notin> T\<close> xQ yQ xy_neq by (meson DiffI inj_onD)
          next
            assume "x \<notin> T" "y \<in> T"
            then show ?thesis using fxy fQT[of x] fc[of y] xQ by simp
          next
            assume "x \<in> T" "y \<notin> T"
            then show ?thesis using fxy fQT[of y] fc[of x] yQ by simp
          qed simp
          moreover have "degree x = degree y" using degree_Q[OF xQ] degree_Q[OF yQ] True by simp
          ultimately show False using degT xy_neq by (meson inj_on_eq_iff)
        next
          case False
          then have "1 \<le> \<bar>int (r x) - int (r y)\<bar>" by linarith
          then have "int ?c * 1 \<le> int ?c * \<bar>int (r x) - int (r y)\<bar>" by (intro mult_left_mono) simp_all
          then have "int ?c \<le> \<bar>int (f x) - int (f y)\<bar>" using I by (simp add: abs_mult)
          moreover have "\<bar>int (f x) - int (f y)\<bar> < int ?c" using flab[of x] flab[of y] by linarith
          ultimately show False by linarith
        qed
      qed
    next
      case False
      then consider "x \<in> Q" "y \<in> S" | "x \<in> S" "y \<in> Q" | "x \<in> S" "y \<in> S" using xyV by blast
      then show ?thesis
      proof cases
        case 1 then show ?thesis using QS xy by (metis less_irrefl)
      next
        case 2 then show ?thesis using QS xy vert_adj_sym by (metis less_irrefl)
      next
        case 3 then show ?thesis using split_stable xy by blast
      qed
    qed
  qed
  then show ?thesis by simp
qed

text \<open>With \<open>|T| = 1\<close>: \<open>\<eta>(G) \<le> |Q| \<le> \<chi>(G)\<close>, so the conjecture holds for split graphs.\<close>

corollary theorem_3_conjecture:
  assumes "V \<noteq> {}"
  shows "eta \<le> card Q" "enat eta \<le> chi"
proof -
  have "Q \<noteq> {}" using assms split_part split_maximal by blast
  then obtain u where u: "u \<in> Q" by blast
  have "eta \<le> card Q - card {u} + 1" using u by (intro theorem_3) auto
  moreover have "1 \<le> card Q" using u finQ by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)
  ultimately show "eta \<le> card Q" by simp
  then show "enat eta \<le> chi" using clique_le_chi[OF split_clique] by (meson enat_ord_simps(1) order.trans)
qed

end

text \<open>Any split partition can be made maximal by moving one vertex, so the conjecture holds for all split graphs.\<close>

lemma (in fin_sgraph) split_graph_conjecture:
  assumes part: "Q \<union> S = V" "Q \<inter> S = {}" and cl: "clique Q"
    and st: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> \<not> vert_adj a b" and ne: "V \<noteq> {}"
  shows "enat eta \<le> chi"
proof (cases "\<forall>v\<in>S. \<exists>u\<in>Q. \<not> vert_adj u v")
  case True
  interpret split_graph V E Q S using assms True by unfold_locales auto
  show ?thesis using theorem_3_conjecture ne by blast
next
  case False
  then obtain v where v: "v \<in> S" "\<And>u. u \<in> Q \<Longrightarrow> vert_adj u v" by blast
  interpret split_graph V E "insert v Q" "S - {v}"
  proof unfold_locales
    show "insert v Q \<union> (S - {v}) = V" "insert v Q \<inter> (S - {v}) = {}" using part v by auto
    show "clique (insert v Q)"
      using cl v part by (intro clique_insert) auto
    show "\<And>a b. a \<in> S - {v} \<Longrightarrow> b \<in> S - {v} \<Longrightarrow> \<not> vert_adj a b" using st by blast
    show "\<And>w. w \<in> S - {v} \<Longrightarrow> \<exists>u\<in>insert v Q. \<not> vert_adj u w" using st v(1) by blast
  qed
  show ?thesis using theorem_3_conjecture ne by blast
qed

subsection \<open>Proposition 2: complete splits\<close>

locale complete_split = fin_sgraph +
  fixes Q S :: "'a set"
  assumes cs_part: "Q \<union> S = V" "Q \<inter> S = {}"
    and cs_clique: "clique Q"
    and cs_stable: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> \<not> vert_adj a b"
    and cs_full: "\<And>u v. u \<in> Q \<Longrightarrow> v \<in> S \<Longrightarrow> vert_adj u v"
    and cs_Q: "Q \<noteq> {}" and cs_S: "2 \<le> card S"
begin

theorem proposition_2: "eta = card Q"
proof (rule order.antisym)
  obtain u where u: "u \<in> Q" using cs_Q by blast
  obtain v where v: "v \<in> S" using cs_S by fastforce
  have finS: "finite S" using cs_S by (metis card.infinite not_numeral_le_zero)
  have finQ: "finite Q" using cs_part finV by (metis finite_Un)
  interpret sp: split_graph V E "insert v Q" "S - {v}"
  proof unfold_locales
    show "insert v Q \<union> (S - {v}) = V" "insert v Q \<inter> (S - {v}) = {}" using cs_part v by auto
    show "clique (insert v Q)"
      using cs_clique cs_full v cs_part by (intro clique_insert) auto
    show "\<And>a b. a \<in> S - {v} \<Longrightarrow> b \<in> S - {v} \<Longrightarrow> \<not> vert_adj a b" using cs_stable by blast
    show "\<And>w. w \<in> S - {v} \<Longrightarrow> \<exists>u\<in>insert v Q. \<not> vert_adj u w" using cs_stable v by blast
  qed
  have Nu: "neighborhood u = (Q - {u}) \<union> S"
  proof
    show "neighborhood u \<subseteq> (Q - {u}) \<union> S"
      using neighborhood_subset cs_part not_in_own_neighborhood by blast
    show "(Q - {u}) \<union> S \<subseteq> neighborhood u"
    proof
      fix x assume "x \<in> (Q - {u}) \<union> S"
      then have "vert_adj u x" using clique_adj[OF cs_clique u, of x] cs_full[OF u, of x] by blast
      then show "x \<in> neighborhood u" by (simp add: in_neighborhood_iff)
    qed
  qed
  have Nv: "neighborhood v = Q"
  proof
    show "neighborhood v \<subseteq> Q"
    proof
      fix w assume "w \<in> neighborhood v"
      then have "w \<in> V" "vert_adj v w" using neighborhood_subset in_neighborhood_iff by auto
      then show "w \<in> Q" using cs_stable v cs_part by blast
    qed
    show "Q \<subseteq> neighborhood v"
      using v cs_full vert_adj_sym in_neighborhood_iff by blast
  qed
  have "degree u = card Q - 1 + card S"
    unfolding degree_eq Nu using finQ finS cs_part u by (subst card_Un_disjoint) (auto simp: card_Diff_singleton)
  moreover have "degree v = card Q" by (simp add: degree_eq Nv)
  ultimately have "degree u \<noteq> degree v" using cs_S cs_Q finQ by (simp add: card_gt_0_iff)
  moreover have "u \<noteq> v" using u v cs_part by blast
  ultimately have "inj_on degree {u, v}" by auto
  then have "eta \<le> card (insert v Q) - card {u, v} + 1" using u by (intro sp.theorem_3) auto
  moreover have "v \<notin> Q" using v cs_part by blast
  moreover have "0 < card Q" using u finQ card_gt_0_iff by blast
  ultimately show "eta \<le> card Q" using finQ \<open>u \<noteq> v\<close> by simp
next
  show "card Q \<le> eta"
  proof (rule observation_2)
    show "Q \<subseteq> V" using cs_part by blast
  next
    fix x y assume "x \<in> Q" "y \<in> Q"
    have N: "insert w (neighborhood w) = V" if w: "w \<in> Q" for w
    proof
      show "insert w (neighborhood w) \<subseteq> V" using w cs_part neighborhood_subset by blast
      show "V \<subseteq> insert w (neighborhood w)"
      proof
        fix x assume "x \<in> V"
        then consider "x \<in> Q" | "x \<in> S" using cs_part by blast
        then have "x = w \<or> vert_adj w x"
          by cases (use clique_adj[OF cs_clique w] cs_full[OF w] in blast)+
        then show "x \<in> insert w (neighborhood w)" by (auto simp: in_neighborhood_iff)
      qed
    qed
    show "true_twins x y"
      using N \<open>x \<in> Q\<close> \<open>y \<in> Q\<close> cs_part by (auto simp: true_twins_def)
  qed
qed

end

subsection \<open>Lemma 3 and Corollary 2: a lower bound from cliques\<close>

text \<open>
  Lemma 3 is Proposition 1 of Marenco, Mydlarz and Severín (ref. [6]); it is the assumption of
  this locale. For a clique \<open>Q\<close> of an acyclic orientation, the smallest and largest vertices of
  \<open>Q\<close> in a topological order are the source \<open>q_F\<close> and the sink \<open>q_L\<close> of \<open>Q\<close>.
\<close>

locale MMS15_lemma3 = fin_sgraph +
  assumes lemma_3:
    "acyclic_orientation A \<Longrightarrow> clique Q \<Longrightarrow> qF \<in> Q \<Longrightarrow> qL \<in> Q \<Longrightarrow>
      (\<And>q. q \<in> Q - {qF} \<Longrightarrow> (qF, q) \<in> A) \<Longrightarrow> (\<And>q. q \<in> Q - {qL} \<Longrightarrow> (q, qL) \<in> A) \<Longrightarrow>
      enat (cdiv (degree qF + 1) (degree qL + 2 - card Q)) \<le> eta_t A"
begin

lemma clique_degree: "clique Q \<Longrightarrow> q \<in> Q \<Longrightarrow> card Q \<le> degree q + 1"
proof -
  assume "clique Q" "q \<in> Q"
  have "Q - {q} \<subseteq> neighborhood q"
  proof
    fix x assume "x \<in> Q - {q}"
    then have "vert_adj q x" using clique_adj[OF \<open>clique Q\<close> \<open>q \<in> Q\<close>, of x] by auto
    then show "x \<in> neighborhood q" by (simp add: in_neighborhood_iff)
  qed
  then have "card (Q - {q}) \<le> degree q" unfolding degree_eq using finite_neighborhood by (rule card_mono[rotated])
  moreover have "finite Q" using clique_subset[OF \<open>clique Q\<close>] finV finite_subset by blast
  ultimately show "card Q \<le> degree q + 1" using \<open>q \<in> Q\<close> by (simp add: card_Diff_singleton)
qed

lemma cdiv_mono:
  assumes "a \<le> a'" "0 < b'" "b' \<le> b"
  shows "cdiv a b \<le> cdiv a' b'"
proof -
  have "a' \<le> cdiv a' b' * b'" using cdiv_le_iff[OF assms(2), of a' "cdiv a' b'"] by simp
  then have "a \<le> cdiv a' b' * b" using assms by (meson le_trans mult_le_mono2)
  then show ?thesis using assms(2,3) cdiv_le_iff by simp
qed

corollary corollary_2:
  assumes cl: "clique Q" and ne: "Q \<noteq> {}"
  shows "cdiv (Min (degree ` Q) + 1) (Max (degree ` Q) + 2 - card Q) \<le> eta"
proof -
  have finQ: "finite Q" using clique_subset[OF cl] finV finite_subset by blast
  obtain f where f: "additive_coloring eta f" by (rule eta_attained)
  let ?A = "induced_orientation f"
  let ?s = "sumN f"
  have inj: "inj_on ?s Q"
    using f clique_adj[OF cl] unfolding inj_on_def additive_coloring_def by blast
  obtain qF where qF: "qF \<in> Q" "?s qF = Min (?s ` Q)" using finQ ne by (metis Min_in finite_imageI image_iff image_is_empty)
  obtain qL where qL: "qL \<in> Q" "?s qL = Max (?s ` Q)" using finQ ne by (metis Max_in finite_imageI image_iff image_is_empty)
  have src: "(qF, q) \<in> ?A" if "q \<in> Q - {qF}" for q
  proof -
    have "?s qF \<le> ?s q" using qF finQ that by simp
    moreover have "?s qF \<noteq> ?s q" using inj qF that by (metis DiffD1 DiffD2 inj_on_eq_iff singletonI)
    moreover have "vert_adj qF q" using clique_adj[OF cl qF(1)] that by blast
    ultimately show ?thesis by (simp add: induced_orientation_def)
  qed
  have snk: "(q, qL) \<in> ?A" if "q \<in> Q - {qL}" for q
  proof -
    have "?s q \<le> ?s qL" using qL finQ that by simp
    moreover have "?s q \<noteq> ?s qL" using inj qL that by (metis DiffD1 DiffD2 inj_on_eq_iff singletonI)
    moreover have "vert_adj q qL" using clique_adj[OF cl _ qL(1)] that by blast
    ultimately show ?thesis by (simp add: induced_orientation_def)
  qed
  have "enat (cdiv (degree qF + 1) (degree qL + 2 - card Q)) \<le> eta_t ?A"
    using lemma_3[OF induced_orientation_acyclic[OF f] cl qF(1) qL(1)] src snk by blast
  also have "\<dots> \<le> enat eta" using eta_t_le[OF eta_pos induced_orientation_top_add_numbering[OF f]] .
  finally have "cdiv (degree qF + 1) (degree qL + 2 - card Q) \<le> eta" by simp
  moreover have "cdiv (Min (degree ` Q) + 1) (Max (degree ` Q) + 2 - card Q)
      \<le> cdiv (degree qF + 1) (degree qL + 2 - card Q)"
  proof (rule cdiv_mono)
    show "Min (degree ` Q) + 1 \<le> degree qF + 1" using qF(1) finQ by simp
    show "0 < degree qL + 2 - card Q" using clique_degree[OF cl qL(1)] by simp
    have "degree qL \<le> Max (degree ` Q)" using qL(1) finQ by simp
    then show "degree qL + 2 - card Q \<le> Max (degree ` Q) + 2 - card Q" by (intro diff_le_mono) simp
  qed
  ultimately show ?thesis by simp
qed

end

end

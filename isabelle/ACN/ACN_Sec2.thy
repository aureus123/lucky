theory ACN_Sec2
  imports ACN_Basics
begin

section \<open>Regular bipartite and complete multipartite graphs (Section 2)\<close>

context fin_sgraph
begin

subsection \<open>Observation 1, Lemma 1 and Corollary 1\<close>

theorem observation_1: "eta = 1 \<longleftrightarrow> (\<forall>u v. vert_adj u v \<longrightarrow> degree u \<noteq> degree v)"
proof
  assume "eta = 1"
  then obtain f where f: "additive_coloring 1 f" using eta_attained by metis
  then have "\<And>v. v \<in> V \<Longrightarrow> f v = 1" by (auto simp: additive_coloring_def labeling_def)
  then have "sumN f v = degree v" for v using sumN_cong[of f "\<lambda>_. 1"] sumN_const_1 by metis
  then show "\<forall>u v. vert_adj u v \<longrightarrow> degree u \<noteq> degree v"
    using f by (auto simp: additive_coloring_def)
next
  assume "\<forall>u v. vert_adj u v \<longrightarrow> degree u \<noteq> degree v"
  then have "additive_coloring 1 (\<lambda>_. 1)"
    unfolding additive_coloring_def labeling_def sumN_const_1 by simp
  then have "eta \<le> 1" by (intro eta_le) simp_all
  then show "eta = 1" using eta_pos by simp
qed

text \<open>
  A bipartite graph with stable sets \<open>U\<close> and \<open>W\<close> (the paper's \<open>U\<close> and \<open>V\<close>): every edge has one
  end in each set.
\<close>

lemma lemma_1:
  assumes part: "U \<inter> W = {}" "U \<union> W = V"
    and bip: "\<And>u v. vert_adj u v \<Longrightarrow> u \<in> U \<longleftrightarrow> v \<in> W"
    and deg: "\<And>v u. v \<in> W \<Longrightarrow> u \<in> neighborhood v \<Longrightarrow> degree u < 2 * degree v"
  shows "eta = (if \<forall>u v. vert_adj u v \<longrightarrow> degree u \<noteq> degree v then 1 else 2)"
proof -
  define f where "f v = (if v \<in> U then 2 else 1::nat)" for v
  have NU: "neighborhood u \<subseteq> W" if "u \<in> U" for u
    using that bip by (auto simp: in_neighborhood_iff)
  have NW: "neighborhood v \<subseteq> U" if "v \<in> W" for v
  proof
    fix w assume "w \<in> neighborhood v"
    then have "vert_adj v w" "w \<in> V" using in_neighborhood_iff neighborhood_subset by auto
    then show "w \<in> U" using bip[of v w] that part by blast
  qed
  have sU: "sumN f u = degree u" if "u \<in> U" for u
  proof -
    have "sumN f u = (\<Sum>w\<in>neighborhood u. 1)"
      unfolding sumN_def f_def using NU[OF that] part(1) by (intro sum.cong) auto
    then show ?thesis by (simp add: degree_eq)
  qed
  have sW: "sumN f v = 2 * degree v" if "v \<in> W" for v
  proof -
    have "sumN f v = (\<Sum>w\<in>neighborhood v. 2)"
      unfolding sumN_def f_def using NW[OF that] by (intro sum.cong) auto
    then show ?thesis by (simp add: degree_eq)
  qed
  have edge: "sumN f u < sumN f v" if "u \<in> U" "v \<in> W" "vert_adj u v" for u v
  proof -
    have "u \<in> neighborhood v" using that(3) by (simp add: in_neighborhood_iff vert_adj_sym)
    then show ?thesis using sU[OF that(1)] sW[OF that(2)] deg[OF that(2)] by simp
  qed
  have "additive_coloring 2 f"
    unfolding additive_coloring_def
  proof (intro conjI allI impI)
    show "labeling 2 f" by (simp add: labeling_def f_def)
  next
    fix u v assume uv: "vert_adj u v"
    then have "u \<in> V" "v \<in> V" using vert_adj_imp_inV by auto
    then consider "u \<in> U" "v \<in> W" | "u \<in> W" "v \<in> U"
      using bip[OF uv] part by blast
    then show "sumN f u \<noteq> sumN f v"
      using edge uv vert_adj_sym by (cases; metis less_irrefl)
  qed
  then have le2: "eta \<le> 2" by (intro eta_le) simp_all
  show ?thesis
  proof (cases "\<forall>u v. vert_adj u v \<longrightarrow> degree u \<noteq> degree v")
    case True
    then show ?thesis using observation_1 by simp
  next
    case False
    then have "eta \<noteq> 1" using observation_1 by simp
    then show ?thesis using False le2 eta_pos by simp
  qed
qed

corollary corollary_1:
  assumes part: "U \<inter> W = {}" "U \<union> W = V"
    and bip: "\<And>u v. vert_adj u v \<Longrightarrow> u \<in> U \<longleftrightarrow> v \<in> W"
    and reg: "\<And>u v. u \<in> V \<Longrightarrow> v \<in> V \<Longrightarrow> degree u = degree v"
    and edges: "E \<noteq> {}"
  shows "eta = 2"
proof -
  have deg: "degree u < 2 * degree v" if "v \<in> W" "u \<in> neighborhood v" for v u
  proof -
    have "0 < degree v"
      using that(2) finite_neighborhood by (auto simp: degree_eq card_gt_0_iff)
    moreover have "degree u = degree v"
      using that part neighborhood_subset reg by blast
    ultimately show ?thesis by simp
  qed
  obtain e where "e \<in> E" using edges by blast
  then obtain a b where "e = {a, b}" "a \<noteq> b" using two_edges card_2_iff by metis
  moreover have "a \<in> V" "b \<in> V" using wellformed[OF \<open>e \<in> E\<close>] \<open>e = {a, b}\<close> by auto
  ultimately have "vert_adj a b" "degree a = degree b"
    using \<open>e \<in> E\<close> reg[of a b] by (simp_all add: vert_adj_def)
  then have "\<not> (\<forall>u v. vert_adj u v \<longrightarrow> degree u \<noteq> degree v)" by blast
  then show ?thesis using lemma_1[OF part bip deg] by simp
qed

end

subsection \<open>The sequence \<open>s_i\<close> and the bound \<open>max \<lceil>s_i / |V_i|\<rceil>\<close>\<close>

text \<open>
  For the part sizes \<open>n_1, \<dots>, n_r\<close> (a list, indexed from 0), \<open>s_r = n_r\<close> and
  \<open>s_i = max {1 + s_{i+1}, n_i}\<close>.
\<close>

fun sseq :: "nat list \<Rightarrow> nat list" where
  "sseq [] = []"
| "sseq [n] = [n]"
| "sseq (n # m # ns) = (let t = sseq (m # ns) in max (Suc (hd t)) n # t)"

definition mp_bound :: "nat list \<Rightarrow> nat" where
  "mp_bound ns = Max (set (map2 cdiv (sseq ns) ns))"

lemma length_sseq: "length (sseq ns) = length ns"
  by (induction ns rule: sseq.induct) (simp_all add: Let_def)

text \<open>Closed form: \<open>s_i = max {n_t + (t - i) : i \<le> t}\<close>, stated as a bound.\<close>

lemma sseq_le_iff:
  "i < length ns \<Longrightarrow> sseq ns ! i \<le> x \<longleftrightarrow> (\<forall>t. i \<le> t \<longrightarrow> t < length ns \<longrightarrow> ns ! t + (t - i) \<le> x)"
proof (induction ns arbitrary: i x rule: sseq.induct)
  case 1
  then show ?case by simp
next
  case (2 n)
  then show ?case by auto
next
  case (3 n m ns)
  let ?t = "sseq (m # ns)"
  have len: "length ?t = Suc (length ns)" by (simp add: length_sseq)
  have hd: "hd ?t = ?t ! 0" using len by (cases ?t) auto
  show ?case
  proof (cases i)
    case 0
    have "sseq (n # m # ns) ! i \<le> x \<longleftrightarrow> Suc (?t ! 0) \<le> x \<and> n \<le> x"
      using 0 hd by (simp add: Let_def)
    also have "Suc (?t ! 0) \<le> x \<longleftrightarrow>
        (\<forall>t. t < length (m # ns) \<longrightarrow> (m # ns) ! t + Suc t \<le> x)"
    proof (cases x)
      case 0
      then show ?thesis by auto
    next
      case (Suc y)
      have "?t ! 0 \<le> y \<longleftrightarrow> (\<forall>t. t < length (m # ns) \<longrightarrow> (m # ns) ! t + t \<le> y)"
        using "3.IH"[of 0 y] by simp
      then show ?thesis using Suc by simp
    qed
    also have "\<dots> \<and> n \<le> x \<longleftrightarrow>
        (\<forall>t. i \<le> t \<longrightarrow> t < length (n # m # ns) \<longrightarrow> (n # m # ns) ! t + (t - i) \<le> x)"
    proof
      assume H: "(\<forall>t. t < length (m # ns) \<longrightarrow> (m # ns) ! t + Suc t \<le> x) \<and> n \<le> x"
      show "\<forall>t. i \<le> t \<longrightarrow> t < length (n # m # ns) \<longrightarrow> (n # m # ns) ! t + (t - i) \<le> x"
      proof (intro allI impI)
        fix t assume "i \<le> t" "t < length (n # m # ns)"
        then show "(n # m # ns) ! t + (t - i) \<le> x"
          using H 0 by (cases t) auto
      qed
    next
      assume H: "\<forall>t. i \<le> t \<longrightarrow> t < length (n # m # ns) \<longrightarrow> (n # m # ns) ! t + (t - i) \<le> x"
      show "(\<forall>t. t < length (m # ns) \<longrightarrow> (m # ns) ! t + Suc t \<le> x) \<and> n \<le> x"
      proof (intro conjI allI impI)
        fix t assume "t < length (m # ns)"
        then show "(m # ns) ! t + Suc t \<le> x" using H[rule_format, of "Suc t"] 0 by simp
      next
        show "n \<le> x" using H[rule_format, of 0] 0 by simp
      qed
    qed
    finally show ?thesis .
  next
    case (Suc j)
    then have j: "j < length (m # ns)" using "3.prems" by simp
    have "sseq (n # m # ns) ! i = ?t ! j" using Suc by (simp add: Let_def)
    also have "\<dots> \<le> x \<longleftrightarrow> (\<forall>t. j \<le> t \<longrightarrow> t < length (m # ns) \<longrightarrow> (m # ns) ! t + (t - j) \<le> x)"
      using "3.IH"[OF j] .
    also have "\<dots> \<longleftrightarrow>
        (\<forall>t. i \<le> t \<longrightarrow> t < length (n # m # ns) \<longrightarrow> (n # m # ns) ! t + (t - i) \<le> x)"
    proof
      assume H: "\<forall>t. j \<le> t \<longrightarrow> t < length (m # ns) \<longrightarrow> (m # ns) ! t + (t - j) \<le> x"
      show "\<forall>t. i \<le> t \<longrightarrow> t < length (n # m # ns) \<longrightarrow> (n # m # ns) ! t + (t - i) \<le> x"
      proof (intro allI impI)
        fix t assume "i \<le> t" "t < length (n # m # ns)"
        then obtain t' where "t = Suc t'" "j \<le> t'" "t' < length (m # ns)"
          using Suc by (cases t) auto
        then show "(n # m # ns) ! t + (t - i) \<le> x" using H Suc by simp
      qed
    next
      assume H: "\<forall>t. i \<le> t \<longrightarrow> t < length (n # m # ns) \<longrightarrow> (n # m # ns) ! t + (t - i) \<le> x"
      show "\<forall>t. j \<le> t \<longrightarrow> t < length (m # ns) \<longrightarrow> (m # ns) ! t + (t - j) \<le> x"
      proof (intro allI impI)
        fix t assume "j \<le> t" "t < length (m # ns)"
        then show "(m # ns) ! t + (t - j) \<le> x" using H[rule_format, of "Suc t"] Suc by simp
      qed
    qed
    finally show ?thesis .
  qed
qed

lemma sseq_ge: "i < length ns \<Longrightarrow> ns ! i \<le> sseq ns ! i"
  using sseq_le_iff[of i ns "sseq ns ! i"] by (metis add_0_right diff_self_eq_0 order.refl)

lemma set_map2_nth:
  assumes "length xs = length ys"
  shows "set (map2 f xs ys) = (\<lambda>i. f (xs ! i) (ys ! i)) ` {..<length ys}"
proof -
  have "map2 f xs ys = map (\<lambda>i. f (xs ! i) (ys ! i)) [0..<length ys]"
    using assms by (intro nth_equalityI) auto
  then show ?thesis by (simp add: atLeast0LessThan)
qed

lemma mp_bound_alt: "mp_bound ns = Max ((\<lambda>i. cdiv (sseq ns ! i) (ns ! i)) ` {..<length ns})"
  unfolding mp_bound_def set_map2_nth[OF length_sseq] ..

text \<open>
  The bound is at most \<open>k\<close> iff \<open>s_i \<le> k n_i\<close> for all \<open>i\<close>, i.e. iff
  \<open>n_t + (t - i) \<le> k n_i\<close> whenever \<open>i \<le> t\<close>.
\<close>

lemma mp_bound_le_iff:
  assumes "ns \<noteq> []" "\<forall>n\<in>set ns. 0 < n"
  shows "mp_bound ns \<le> k \<longleftrightarrow> (\<forall>i t. i \<le> t \<longrightarrow> t < length ns \<longrightarrow> ns ! t + (t - i) \<le> k * ns ! i)"
proof -
  have pos: "0 < ns ! i" if "i < length ns" for i using assms(2) that by simp
  have "mp_bound ns \<le> k \<longleftrightarrow> (\<forall>i < length ns. cdiv (sseq ns ! i) (ns ! i) \<le> k)"
    unfolding mp_bound_alt using assms(1) by (subst Max_le_iff) auto
  also have "\<dots> \<longleftrightarrow> (\<forall>i < length ns. sseq ns ! i \<le> k * ns ! i)"
    using cdiv_le_iff pos by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>i t. i \<le> t \<longrightarrow> t < length ns \<longrightarrow> ns ! t + (t - i) \<le> k * ns ! i)"
  proof (intro iffI allI impI)
    fix i t assume H: "\<forall>i < length ns. sseq ns ! i \<le> k * ns ! i" and it: "i \<le> t" "t < length ns"
    then have i: "i < length ns" by simp
    then show "ns ! t + (t - i) \<le> k * ns ! i" using H sseq_le_iff[OF i] it by blast
  next
    fix i assume H: "\<forall>i t. i \<le> t \<longrightarrow> t < length ns \<longrightarrow> ns ! t + (t - i) \<le> k * ns ! i"
      and i: "i < length ns"
    show "sseq ns ! i \<le> k * ns ! i" using H sseq_le_iff[OF i] by blast
  qed
  finally show ?thesis .
qed

text \<open>
  The ordering by decreasing size gives the least bound among all orderings of the same sizes.
  This replaces the second half of the paper's proof of Theorem 1, whose step "\<open>i \<ge> j\<close>" does not
  hold in general (see the README). Take \<open>i \<le> t\<close> in the sorted list. The parts with sizes between
  \<open>n_t\<close> and \<open>n_i\<close> occupy at least \<open>t - i + 1\<close> positions of the other list; if \<open>a\<close> and \<open>b\<close> are the first and last of
  them, then \<open>b - a \<ge> t - i\<close>, and the bound for the other list at \<open>(a, b)\<close> gives the bound for the
  sorted list at \<open>(i, t)\<close>.
\<close>

lemma mp_bound_sorted_le:
  assumes sorted: "sorted_wrt (\<ge>) ns" and perm: "mset ms = mset ns"
    and ne: "ns \<noteq> []" and pos: "\<forall>n\<in>set ns. 0 < n"
  shows "mp_bound ns \<le> mp_bound ms"
proof -
  let ?k = "mp_bound ms"
  have set_eq: "set ms = set ns" and len: "length ms = length ns"
    using perm mset_eq_setD mset_eq_length by blast+
  have ms_ne: "ms \<noteq> []" and ms_pos: "\<forall>n\<in>set ms. 0 < n" using ne pos set_eq by auto
  have H: "ms ! b + (b - a) \<le> ?k * ms ! a" if "a \<le> b" "b < length ms" for a b
    using mp_bound_le_iff[OF ms_ne ms_pos, of ?k] that by simp
  have "ns ! t + (t - i) \<le> ?k * ns ! i" if it: "i \<le> t" "t < length ns" for i t
  proof -
    define P where "P x \<longleftrightarrow> ns ! t \<le> x \<and> x \<le> ns ! i" for x
    define J where "J = {j. j < length ms \<and> P (ms ! j)}"
    have mono: "ns ! b \<le> ns ! a" if "a \<le> b" "b < length ns" for a b
      using sorted that by (cases "a = b") (auto simp: sorted_wrt_iff_nth_less)
    have "{i..t} \<subseteq> {j. j < length ns \<and> P (ns ! j)}"
      using it mono by (auto simp: P_def)
    then have "card {i..t} \<le> card {j. j < length ns \<and> P (ns ! j)}"
      by (intro card_mono) simp_all
    then have "Suc t - i \<le> card {j. j < length ns \<and> P (ns ! j)}" by simp
    also have "\<dots> = length (filter P ns)" by (simp add: length_filter_conv_card)
    also have "\<dots> = size (filter_mset P (mset ns))" by (simp flip: mset_filter)
    also have "\<dots> = size (filter_mset P (mset ms))" by (simp add: perm)
    also have "\<dots> = length (filter P ms)" by (simp flip: mset_filter)
    also have "\<dots> = card J" by (simp add: length_filter_conv_card J_def)
    finally have cardJ: "Suc t - i \<le> card J" .
    have finJ: "finite J" by (simp add: J_def)
    then have "J \<noteq> {}" using cardJ it by auto
    define a b where "a = Min J" and "b = Max J"
    have aJ: "a \<in> J" and bJ: "b \<in> J" using finJ \<open>J \<noteq> {}\<close> by (simp_all add: a_def b_def)
    have "J \<subseteq> {a..b}" using finJ by (auto simp: a_def b_def)
    then have "card J \<le> Suc b - a" using card_mono[of "{a..b}" J] by simp
    then have ba: "t - i \<le> b - a" using cardJ by linarith
    have ab: "a \<le> b" using aJ \<open>J \<subseteq> {a..b}\<close> by auto
    have "ns ! t + (t - i) \<le> ms ! b + (b - a)" using bJ ba by (simp add: J_def P_def)
    also have "\<dots> \<le> ?k * ms ! a" using H ab bJ by (simp add: J_def)
    also have "\<dots> \<le> ?k * ns ! i" using aJ by (simp add: J_def P_def)
    finally show ?thesis .
  qed
  then have "mp_bound ns \<le> ?k" using mp_bound_le_iff[OF ne pos] by blast
  then show ?thesis .
qed

text \<open>The paper's bound \<open>s_i \<le> |V_i| (r - i + 1)\<close> (indices from 0 here) and \<open>\<eta>(G) \<le> r\<close>.\<close>

lemma sseq_le_mult:
  assumes "sorted_wrt (\<ge>) ns" "\<forall>n\<in>set ns. 0 < n" "i < length ns"
  shows "sseq ns ! i \<le> ns ! i * (length ns - i)"
proof -
  have "ns ! t + (t - i) \<le> ns ! i * (length ns - i)" if "i \<le> t" "t < length ns" for t
  proof -
    have "ns ! t \<le> ns ! i" using assms(1) that by (cases "i = t") (auto simp: sorted_wrt_iff_nth_less)
    moreover have "1 \<le> ns ! i" using assms(2) nth_mem[OF assms(3)] by (simp add: Suc_le_eq)
    moreover have "t - i \<le> length ns - i - 1" using that by simp
    ultimately have "ns ! t + (t - i) \<le> ns ! i + ns ! i * (length ns - i - 1)"
      by (metis add_le_mono mult_1 mult_le_mono1 le_trans)
    also have "\<dots> = ns ! i * (length ns - i)"
      using assms(3) by (cases "length ns - i") (auto simp: algebra_simps)
    finally show ?thesis .
  qed
  then show ?thesis using sseq_le_iff[OF assms(3)] by blast
qed

lemma mp_bound_le_length:
  assumes "sorted_wrt (\<ge>) ns" "ns \<noteq> []" "\<forall>n\<in>set ns. 0 < n"
  shows "mp_bound ns \<le> length ns"
proof -
  have S: "sseq ns ! i \<le> length ns * ns ! i" if "i < length ns" for i
  proof -
    have "ns ! i * (length ns - i) \<le> ns ! i * length ns" by simp
    then show ?thesis using sseq_le_mult[OF assms(1,3) that] by (metis mult.commute order_trans)
  qed
  have "ns ! t + (t - i) \<le> length ns * ns ! i" if "i \<le> t" "t < length ns" for i t
  proof -
    have i: "i < length ns" using that by simp
    show ?thesis using sseq_le_iff[OF i] S[OF i] that by blast
  qed
  then show ?thesis using mp_bound_le_iff[OF assms(2,3)] by blast
qed

text \<open>The sequence \<open>s_i\<close> is strictly decreasing, and \<open>s_i \<le> K n_i\<close> for the bound \<open>K\<close>.\<close>

lemma sseq_Suc_less:
  assumes "Suc i < length ns"
  shows "sseq ns ! Suc i < sseq ns ! i"
proof -
  have i: "i < length ns" using assms by simp
  have H: "ns ! t + (t - i) \<le> sseq ns ! i" if "i \<le> t" "t < length ns" for t
    using sseq_le_iff[OF i, of "sseq ns ! i"] that by blast
  have "ns ! t + (t - Suc i) \<le> sseq ns ! i - 1" if "Suc i \<le> t" "t < length ns" for t
  proof -
    have "ns ! t + (t - i) \<le> sseq ns ! i" using H that by simp
    then show ?thesis using that by arith
  qed
  then have "sseq ns ! Suc i \<le> sseq ns ! i - 1" using sseq_le_iff[OF assms] by blast
  moreover have "1 \<le> sseq ns ! i" using H[of "Suc i"] assms by simp
  ultimately show ?thesis by linarith
qed

lemma sseq_less:
  assumes "i < j" "j < length ns"
  shows "sseq ns ! j < sseq ns ! i"
  using assms
proof (induction j)
  case (Suc j)
  then show ?case using sseq_Suc_less[of j ns] by (cases "i = j") (auto intro: less_trans)
qed simp

lemma sseq_le_mp_bound:
  assumes "ns \<noteq> []" "\<forall>n\<in>set ns. 0 < n" "i < length ns"
  shows "sseq ns ! i \<le> mp_bound ns * ns ! i"
  using mp_bound_le_iff[OF assms(1,2), of "mp_bound ns"] sseq_le_iff[OF assms(3)] assms(3) by blast

lemma mp_bound_pos:
  assumes "ns \<noteq> []" "\<forall>n\<in>set ns. 0 < n"
  shows "0 < mp_bound ns"
proof -
  have "0 < ns ! 0" "ns ! 0 \<le> sseq ns ! 0" using assms sseq_ge[of 0 ns] by auto
  moreover have "sseq ns ! 0 \<le> mp_bound ns * ns ! 0" using sseq_le_mp_bound[OF assms, of 0] assms by simp
  ultimately show ?thesis by (metis gr0I mult_0 not_le)
qed

text \<open>A set of \<open>n\<close> vertices can be labeled from \<open>[K]\<close> with any sum between \<open>n\<close> and \<open>K n\<close>.\<close>

lemma exists_labeling_sum:
  assumes "finite P"
  shows "card P \<le> T \<Longrightarrow> T \<le> K * card P \<Longrightarrow> \<exists>g. (\<forall>v\<in>P. 1 \<le> g v \<and> g v \<le> K) \<and> sum g P = T"
  using assms
proof (induction P arbitrary: T rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x P)
  define a where "a = min K (T - card P)"
  have card: "card (insert x P) = Suc (card P)" using insert by simp
  have K: "0 < K" using insert.prems card by (cases K) auto
  have a: "1 \<le> a" "a \<le> K" using insert.prems card K by (auto simp: a_def)
  have "card P \<le> T - a" "T - a \<le> K * card P"
    using insert.prems card a by (auto simp: a_def min_def)
  then obtain g where g: "\<forall>v\<in>P. 1 \<le> g v \<and> g v \<le> K" "sum g P = T - a" using insert.IH by blast
  define g' where "g' v = (if v = x then a else g v)" for v
  have "sum g' P = sum g P" using insert(2) by (intro sum.cong) (auto simp: g'_def)
  then have "sum g' (insert x P) = a + (T - a)" using insert g by (simp add: g'_def)
  moreover have "a \<le> T" using insert.prems card a by (auto simp: a_def)
  ultimately show ?case using g a by (intro exI[of _ g']) (auto simp: g'_def)
qed

subsection \<open>Complete multipartite graphs\<close>

context fin_sgraph
begin

text \<open>\<open>G\<close> is complete multipartite with the parts listed in \<open>Ps\<close> (the paper's \<open>V_1, \<dots>, V_r\<close>).\<close>

definition complete_multipartite :: "'a set list \<Rightarrow> bool" where
  "complete_multipartite Ps \<longleftrightarrow> distinct Ps \<and> {} \<notin> set Ps \<and> disjoint (set Ps) \<and> \<Union>(set Ps) = V \<and>
     (\<forall>u v. vert_adj u v \<longleftrightarrow> (\<exists>P\<in>set Ps. \<exists>Q\<in>set Ps. P \<noteq> Q \<and> u \<in> P \<and> v \<in> Q))"

text \<open>An orientation is monotone for the order \<open>Ps\<close> of the parts if all arcs go forward.\<close>

definition monotone :: "('a \<times> 'a) set \<Rightarrow> 'a set list \<Rightarrow> bool" where
  "monotone A Ps \<longleftrightarrow> (\<forall>(u, v)\<in>A. \<exists>i j. i < j \<and> j < length Ps \<and> u \<in> Ps ! i \<and> v \<in> Ps ! j)"

lemma cm_distinct: "complete_multipartite Ps \<Longrightarrow> distinct Ps"
  and cm_nonempty: "complete_multipartite Ps \<Longrightarrow> P \<in> set Ps \<Longrightarrow> P \<noteq> {}"
  and cm_disjoint: "complete_multipartite Ps \<Longrightarrow> P \<in> set Ps \<Longrightarrow> Q \<in> set Ps \<Longrightarrow> P \<noteq> Q \<Longrightarrow> P \<inter> Q = {}"
  and cm_union: "complete_multipartite Ps \<Longrightarrow> \<Union>(set Ps) = V"
  and cm_adj: "complete_multipartite Ps \<Longrightarrow>
     vert_adj u v \<longleftrightarrow> (\<exists>P\<in>set Ps. \<exists>Q\<in>set Ps. P \<noteq> Q \<and> u \<in> P \<and> v \<in> Q)"
  unfolding complete_multipartite_def disjoint_def by blast+

lemma complete_multipartite_perm:
  assumes "complete_multipartite Ps" "mset Qs = mset Ps"
  shows "complete_multipartite Qs"
proof -
  have "set Qs = set Ps" "length Qs = length Ps"
    using assms(2) mset_eq_setD mset_eq_length by blast+
  moreover have "distinct Qs"
    using assms by (metis complete_multipartite_def mset_eq_imp_distinct_iff)
  ultimately show ?thesis using assms(1) by (simp add: complete_multipartite_def)
qed

lemma part_index_unique:
  assumes "complete_multipartite Ps" "i < length Ps" "j < length Ps" "u \<in> Ps ! i" "u \<in> Ps ! j"
  shows "i = j"
proof (rule ccontr)
  assume "i \<noteq> j"
  then have "Ps ! i \<noteq> Ps ! j" using assms(1-3) by (simp add: complete_multipartite_def nth_eq_iff_index_eq)
  then have "Ps ! i \<inter> Ps ! j = {}"
    using assms(1-3) by (auto simp: complete_multipartite_def disjoint_def)
  then show False using assms(4,5) by blast
qed

lemma part_card_pos:
  assumes "complete_multipartite Ps" "P \<in> set Ps"
  shows "0 < card P"
proof -
  have "P \<subseteq> V" "P \<noteq> {}" using assms by (auto simp: complete_multipartite_def)
  then show ?thesis using finV by (simp add: card_gt_0_iff finite_subset)
qed

text \<open>The orientation from earlier to later parts.\<close>

definition forward_orientation :: "'a set list \<Rightarrow> ('a \<times> 'a) set" where
  "forward_orientation Ps = {(u, v). \<exists>i j. i < j \<and> j < length Ps \<and> u \<in> Ps ! i \<and> v \<in> Ps ! j}"

lemma forward_orientation_iff:
  "(u, v) \<in> forward_orientation Ps \<longleftrightarrow> (\<exists>i j. i < j \<and> j < length Ps \<and> u \<in> Ps ! i \<and> v \<in> Ps ! j)"
  by (simp add: forward_orientation_def)

lemma acyclic_rank:
  assumes "\<And>u v. (u, v) \<in> A \<Longrightarrow> h u < (h v :: nat)"
  shows "acyclic A"
proof -
  have "(u, v) \<in> A\<^sup>+ \<Longrightarrow> h u < h v" for u v
    by (induction rule: trancl_induct) (use assms in \<open>auto dest: less_trans\<close>)
  then show ?thesis unfolding acyclic_def by blast
qed

lemma forward_orientation:
  assumes cm: "complete_multipartite Ps"
  shows "acyclic_orientation (forward_orientation Ps)" "monotone (forward_orientation Ps) Ps"
proof -
  define idx where "idx u = (THE i. i < length Ps \<and> u \<in> Ps ! i)" for u
  have idx: "idx u = i" if "i < length Ps" "u \<in> Ps ! i" for u i
    unfolding idx_def using that part_index_unique[OF cm] by (intro the_equality) auto
  have arc: "idx u < idx v" if uv: "(u, v) \<in> forward_orientation Ps" for u v
  proof -
    obtain i j where "i < j" "j < length Ps" "u \<in> Ps ! i" "v \<in> Ps ! j"
      using uv unfolding forward_orientation_iff by blast
    then show ?thesis using idx[of i u] idx[of j v] by simp
  qed
  have "orientation (forward_orientation Ps)"
    unfolding orientation_def
  proof (intro conjI allI impI)
    fix u v assume "(u, v) \<in> forward_orientation Ps"
    then obtain i j where "i < j" "j < length Ps" "u \<in> Ps ! i" "v \<in> Ps ! j"
      unfolding forward_orientation_iff by blast
    moreover have "Ps ! i \<noteq> Ps ! j"
      using cm \<open>i < j\<close> \<open>j < length Ps\<close> by (simp add: complete_multipartite_def nth_eq_iff_index_eq)
    moreover have "Ps ! i \<in> set Ps" "Ps ! j \<in> set Ps" using \<open>i < j\<close> \<open>j < length Ps\<close> by simp_all
    ultimately show "vert_adj u v" using cm_adj[OF cm, of u v] by blast
  next
    fix u v assume "vert_adj u v"
    then obtain P Q where "P \<in> set Ps" "Q \<in> set Ps" "P \<noteq> Q" "u \<in> P" "v \<in> Q"
      using cm by (auto simp: complete_multipartite_def)
    then obtain i j where "i < length Ps" "j < length Ps" "u \<in> Ps ! i" "v \<in> Ps ! j" "i \<noteq> j"
      by (metis in_set_conv_nth)
    then show "(u, v) \<in> forward_orientation Ps \<or> (v, u) \<in> forward_orientation Ps"
      unfolding forward_orientation_iff by (cases "i < j") (blast, metis linorder_neqE_nat)
  next
    fix u v assume "(u, v) \<in> forward_orientation Ps"
    then show "(v, u) \<notin> forward_orientation Ps" using arc by (meson less_asym)
  qed
  moreover have "acyclic (forward_orientation Ps)" using arc by (rule acyclic_rank)
  ultimately show "acyclic_orientation (forward_orientation Ps)"
    by (simp add: acyclic_orientation_def)
  show "monotone (forward_orientation Ps) Ps"
    unfolding monotone_def using forward_orientation_iff by blast
qed

text \<open>One vertex from each part forms a clique, so \<open>\<chi>(G) \<ge> r\<close>.\<close>

lemma complete_multipartite_chi:
  assumes cm: "complete_multipartite Ps"
  shows "enat (length Ps) \<le> chi"
proof -
  define pick where "pick P = (SOME x. x \<in> P)" for P :: "'a set"
  have pick: "pick P \<in> P" if "P \<in> set Ps" for P
    using cm_nonempty[OF cm that] unfolding pick_def by (meson ex_in_conv someI_ex)
  have inj: "inj_on pick (set Ps)"
  proof (rule inj_onI)
    fix P Q assume PQ: "P \<in> set Ps" "Q \<in> set Ps" "pick P = pick Q"
    then have "pick P \<in> P \<inter> Q" using pick[OF PQ(1)] pick[OF PQ(2)] PQ(3) by simp
    then show "P = Q" using cm_disjoint[OF cm PQ(1,2)] by blast
  qed
  have "clique (pick ` set Ps)"
    unfolding clique_def
  proof (intro conjI ballI impI)
    show "pick ` set Ps \<subseteq> V" using pick cm_union[OF cm] by blast
  next
    fix x y assume "x \<in> pick ` set Ps" "y \<in> pick ` set Ps" "x \<noteq> y"
    then obtain P Q where "P \<in> set Ps" "Q \<in> set Ps" "x = pick P" "y = pick Q" "P \<noteq> Q" by blast
    then show "vert_adj x y" using pick cm_adj[OF cm] by blast
  qed
  then have "enat (card (pick ` set Ps)) \<le> chi" by (rule clique_le_chi)
  moreover have "card (pick ` set Ps) = length Ps"
    using inj cm_distinct[OF cm] by (simp add: card_image distinct_card)
  ultimately show ?thesis by simp
qed

end

text \<open>
  Lemma 2 is Proposition 3 of Marenco, Mydlarz and Severín (ref. [6]), together with the
  characterization of the complete multipartite digraphs that have a topological additive
  numbering. Both are proved here, following [6]: in a complete multipartite graph,
  \<open>f(N(w)) = f(V) - f(V_j)\<close> for \<open>w \<in> V_j\<close>, so only the sums \<open>f(V_j)\<close> of the parts matter.
\<close>

context fin_sgraph
begin

lemma cm_part_exists:
  assumes "complete_multipartite Ps" "v \<in> V"
  obtains i where "i < length Ps" "v \<in> Ps ! i"
  using assms cm_union[OF assms(1)] by (metis UnionE in_set_conv_nth)

lemma cm_neighborhood:
  assumes cm: "complete_multipartite Ps" and j: "j < length Ps" "w \<in> Ps ! j"
  shows "neighborhood w = V - Ps ! j"
proof
  show "neighborhood w \<subseteq> V - Ps ! j"
  proof
    fix x assume "x \<in> neighborhood w"
    then have x: "x \<in> V" "vert_adj w x" using neighborhood_subset in_neighborhood_iff by auto
    then obtain P Q where "P \<in> set Ps" "Q \<in> set Ps" "P \<noteq> Q" "w \<in> P" "x \<in> Q" using cm_adj[OF cm] by blast
    moreover have "P = Ps ! j" using j \<open>P \<in> set Ps\<close> \<open>w \<in> P\<close> cm_disjoint[OF cm] nth_mem by blast
    ultimately show "x \<in> V - Ps ! j" using x cm_disjoint[OF cm] by blast
  qed
next
  show "V - Ps ! j \<subseteq> neighborhood w"
  proof
    fix x assume x: "x \<in> V - Ps ! j"
    then obtain i where i: "i < length Ps" "x \<in> Ps ! i" using cm_part_exists[OF cm] by blast
    then have "Ps ! i \<noteq> Ps ! j" using x by auto
    then have "vert_adj w x" using cm_adj[OF cm] i j nth_mem by blast
    then show "x \<in> neighborhood w" by (simp add: in_neighborhood_iff)
  qed
qed

lemma cm_sumN:
  assumes "complete_multipartite Ps" "j < length Ps" "w \<in> Ps ! j"
  shows "sumN f w + sum f (Ps ! j) = sum f V"
proof -
  have "Ps ! j \<subseteq> V" using cm_union[OF assms(1)] assms(2) nth_mem by blast
  then show ?thesis unfolding sumN_def cm_neighborhood[OF assms] using finV
    by (metis add.commute sum.subset_diff)
qed

lemma cm_arc_forward:
  assumes cm: "complete_multipartite Ps" and A: "orientation A" and mono: "monotone A Ps"
    and ij: "i < j" "j < length Ps" and u: "u \<in> Ps ! i" and w: "w \<in> Ps ! j"
  shows "(u, w) \<in> A"
proof -
  have "Ps ! i \<noteq> Ps ! j" using cm_distinct[OF cm] ij by (simp add: nth_eq_iff_index_eq)
  moreover have "Ps ! i \<in> set Ps" "Ps ! j \<in> set Ps" using ij by simp_all
  ultimately have "vert_adj u w" using cm_adj[OF cm, of u w] u w by blast
  then have "(u, w) \<in> A \<or> (w, u) \<in> A" using A by (simp add: orientation_def)
  moreover have "(w, u) \<notin> A"
  proof
    assume "(w, u) \<in> A"
    then obtain i' j' where "i' < j'" "j' < length Ps" "w \<in> Ps ! i'" "u \<in> Ps ! j'"
      using mono by (auto simp: monotone_def)
    then have "i' = j" "j' = i" using part_index_unique[OF cm] ij u w by (meson less_trans)+
    then show False using ij \<open>i' < j'\<close> by simp
  qed
  ultimately show ?thesis by blast
qed

text \<open>Lower bound: the part sums of any topological additive numbering decrease strictly.\<close>

lemma lemma_2_lower:
  assumes cm: "complete_multipartite Ps" and ne: "Ps \<noteq> []" and A: "orientation A"
    and mono: "monotone A Ps" and f: "top_add_numbering A k f" and k: "0 < k"
  shows "mp_bound (map card Ps) \<le> k"
proof -
  let ?ns = "map card Ps"
  let ?t = "\<lambda>i. sum f (Ps ! i)"
  have pos: "\<forall>n\<in>set ?ns. 0 < n" using part_card_pos[OF cm] by auto
  have nonempty: "Ps ! i \<noteq> {}" if "i < length Ps" for i using cm_nonempty[OF cm] that nth_mem by blast
  have sub: "Ps ! i \<subseteq> V" if "i < length Ps" for i using cm_union[OF cm] that nth_mem by blast
  have fin: "finite (Ps ! i)" if "i < length Ps" for i using sub[OF that] finV finite_subset by blast
  have lab: "1 \<le> f v \<and> f v \<le> k" if "v \<in> V" for v using f that by (simp add: top_add_numbering_def labeling_def)
  have dec: "?t j < ?t i" if ij: "i < j" "j < length Ps" for i j
  proof -
    have "Ps ! i \<noteq> {}" "Ps ! j \<noteq> {}" using nonempty ij by auto
    then obtain u w where uw: "u \<in> Ps ! i" "w \<in> Ps ! j" by blast
    then have "(u, w) \<in> A" using cm_arc_forward[OF cm A mono ij] by blast
    then have "sumN f u < sumN f w" using f by (auto simp: top_add_numbering_def)
    moreover have "sumN f u + ?t i = sum f V" using cm_sumN[OF cm _ uw(1)] ij by simp
    moreover have "sumN f w + ?t j = sum f V" using cm_sumN[OF cm ij(2) uw(2)] by simp
    ultimately show ?thesis by linarith
  qed
  have tge: "card (Ps ! i) \<le> ?t i" "?t i \<le> k * card (Ps ! i)" if "i < length Ps" for i
    using sum_mono[of "Ps ! i" "\<lambda>_. 1" f] sum_mono[of "Ps ! i" f "\<lambda>_. k"] lab sub[OF that]
    by (auto simp: mult.commute)
  have gap: "?t t + (t - i) \<le> ?t i" if "i \<le> t" "t < length Ps" for i t
    using that
  proof (induction t)
    case (Suc t)
    then show ?case
    proof (cases "i = Suc t")
      case False
      then have "?t (Suc t) < ?t t" using dec Suc.prems by simp
      then show ?thesis using Suc False by (simp add: Suc_diff_le)
    qed simp
  qed simp
  have "?ns ! t + (t - i) \<le> k * ?ns ! i" if "i \<le> t" "t < length ?ns" for i t
    using tge[of t] tge[of i] gap[of i t] that by simp
  then show ?thesis using mp_bound_le_iff[of ?ns k] ne pos by simp
qed

text \<open>Upper bound: label each part \<open>V_i\<close> with sum \<open>s_i\<close>.\<close>

lemma lemma_2_upper:
  assumes cm: "complete_multipartite Ps" and ne: "Ps \<noteq> []" and mono: "monotone A Ps"
  shows "\<exists>f. top_add_numbering A (mp_bound (map card Ps)) f"
proof -
  let ?ns = "map card Ps"
  let ?K = "mp_bound ?ns"
  let ?s = "sseq ?ns"
  have pos: "\<forall>n\<in>set ?ns. 0 < n" using part_card_pos[OF cm] by auto
  have ne': "?ns \<noteq> []" using ne by simp
  have sub: "Ps ! i \<subseteq> V" if "i < length Ps" for i using cm_union[OF cm] that nth_mem by blast
  have "\<forall>i<length Ps. \<exists>g. (\<forall>v\<in>Ps ! i. 1 \<le> g v \<and> g v \<le> ?K) \<and> sum g (Ps ! i) = ?s ! i"
  proof (intro allI impI)
    fix i assume i: "i < length Ps"
    have "card (Ps ! i) \<le> ?s ! i" using sseq_ge[of i ?ns] i by simp
    moreover have "?s ! i \<le> ?K * card (Ps ! i)" using sseq_le_mp_bound[OF ne' pos, of i] i by simp
    ultimately show "\<exists>g. (\<forall>v\<in>Ps ! i. 1 \<le> g v \<and> g v \<le> ?K) \<and> sum g (Ps ! i) = ?s ! i"
      using exists_labeling_sum[of "Ps ! i"] sub[OF i] finV finite_subset by blast
  qed
  then obtain G where G: "\<And>i. i < length Ps \<Longrightarrow> (\<forall>v\<in>Ps ! i. 1 \<le> G i v \<and> G i v \<le> ?K) \<and> sum (G i) (Ps ! i) = ?s ! i"
    by metis
  define idx where "idx v = (THE i. i < length Ps \<and> v \<in> Ps ! i)" for v
  have idx: "idx v = i" if "i < length Ps" "v \<in> Ps ! i" for v i
    unfolding idx_def using that part_index_unique[OF cm] by (intro the_equality) auto
  define f where "f v = G (idx v) v" for v
  have fsum: "sum f (Ps ! i) = ?s ! i" if "i < length Ps" for i
  proof -
    have "sum f (Ps ! i) = sum (G i) (Ps ! i)" using idx that by (intro sum.cong) (auto simp: f_def)
    then show ?thesis using G[OF that] by simp
  qed
  have "top_add_numbering A ?K f"
    unfolding top_add_numbering_def labeling_def
  proof (rule conjI; rule ballI)
    fix v assume "v \<in> V"
    then obtain i where "i < length Ps" "v \<in> Ps ! i" using cm_part_exists[OF cm] by blast
    then show "1 \<le> f v \<and> f v \<le> ?K" using G idx by (simp add: f_def)
  next
    fix a assume "a \<in> A"
    then obtain u w where a: "a = (u, w)" by (cases a)
    then obtain i j where ij: "i < j" "j < length Ps" "u \<in> Ps ! i" "w \<in> Ps ! j"
      using mono \<open>a \<in> A\<close> by (auto simp: monotone_def)
    have "?s ! j < ?s ! i" using sseq_less[of i j ?ns] ij by simp
    then show "case a of (u, w) \<Rightarrow> sumN f u < sumN f w"
      using cm_sumN[OF cm _ ij(3), of f] cm_sumN[OF cm ij(2,4), of f] fsum ij a by fastforce
  qed
  then show ?thesis by blast
qed

theorem lemma_2_value:
  assumes "complete_multipartite Ps" "Ps \<noteq> []" "acyclic_orientation A" "monotone A Ps"
  shows "eta_t A = enat (mp_bound (map card Ps))"
proof -
  have A: "orientation A" using assms(3) by (simp add: acyclic_orientation_def)
  have pos: "\<forall>n\<in>set (map card Ps). 0 < n" using part_card_pos[OF assms(1)] by auto
  obtain f where f: "top_add_numbering A (mp_bound (map card Ps)) f"
    using lemma_2_upper[OF assms(1,2,4)] by blast
  have K: "0 < mp_bound (map card Ps)" using mp_bound_pos pos assms(2) by simp
  have "eta_t A \<le> enat (mp_bound (map card Ps))" using eta_t_le[OF K f] .
  moreover have "eta_t A \<noteq> \<infinity>" using calculation by (cases "eta_t A") auto
  then obtain k g where "eta_t A = enat k" "0 < k" "top_add_numbering A k g"
    using eta_t_attained by blast
  then have "enat (mp_bound (map card Ps)) \<le> eta_t A"
    using lemma_2_lower[OF assms(1,2) A assms(4)] by simp
  ultimately show ?thesis by simp
qed

theorem lemma_2_finite_iff:
  assumes cm: "complete_multipartite Ps" and ne: "Ps \<noteq> []" and A: "acyclic_orientation A"
  shows "eta_t A \<noteq> \<infinity> \<longleftrightarrow> (\<exists>Qs. mset Qs = mset Ps \<and> monotone A Qs)"
proof
  assume "eta_t A \<noteq> \<infinity>"
  then obtain k f where "0 < k" and f: "top_add_numbering A k f" using eta_t_attained by blast
  have O: "orientation A" using A by (simp add: acyclic_orientation_def)
  let ?key = "\<lambda>P. sum f P"
  \<comment> \<open>an arc from part \<open>P\<close> to part \<open>Q\<close> means \<open>f(P) > f(Q)\<close>\<close>
  have arc_key: "?key Q < ?key P"
    if a: "(u, w) \<in> A" "P \<in> set Ps" "Q \<in> set Ps" "u \<in> P" "w \<in> Q" for u w P Q
  proof -
    obtain i where i: "i < length Ps" "Ps ! i = P" using a(2) by (metis in_set_conv_nth)
    obtain j where j: "j < length Ps" "Ps ! j = Q" using a(3) by (metis in_set_conv_nth)
    have "sumN f u < sumN f w" using f a(1) by (auto simp: top_add_numbering_def)
    moreover have "sumN f u + sum f P = sum f V" using cm_sumN[OF cm i(1), of u f] i(2) a(4) by simp
    moreover have "sumN f w + sum f Q = sum f V" using cm_sumN[OF cm j(1), of w f] j(2) a(5) by simp
    ultimately show ?thesis by linarith
  qed
  have key_inj: "inj_on ?key (set Ps)"
  proof (rule inj_onI)
    fix P Q assume PQ: "P \<in> set Ps" "Q \<in> set Ps" "?key P = ?key Q"
    show "P = Q"
    proof (rule ccontr)
      assume "P \<noteq> Q"
      obtain u w where "u \<in> P" "w \<in> Q" using cm_nonempty[OF cm] PQ by (meson ex_in_conv)
      then have "vert_adj u w" using cm_adj[OF cm] PQ \<open>P \<noteq> Q\<close> by blast
      then have "(u, w) \<in> A \<or> (w, u) \<in> A" using O by (simp add: orientation_def)
      then show False using arc_key PQ \<open>u \<in> P\<close> \<open>w \<in> Q\<close> by (metis less_irrefl)
    qed
  qed
  define Qs where "Qs = rev (sort_key ?key Ps)"
  have mset: "mset Qs = mset Ps" by (simp add: Qs_def)
  have setQ: "set Qs = set Ps" using mset by (metis mset_eq_setD)
  have sortedQ: "sorted_wrt (\<ge>) (map ?key Qs)"
    unfolding Qs_def rev_map[symmetric] sorted_wrt_rev using sorted_sort_key[of ?key Ps]
    by simp
  have "monotone A Qs"
    unfolding monotone_def
  proof (intro ballI, clarify)
    fix u w assume uw: "(u, w) \<in> A"
    then have "vert_adj u w" using O by (simp add: orientation_def)
    then obtain P Q where PQ: "P \<in> set Ps" "Q \<in> set Ps" "P \<noteq> Q" "u \<in> P" "w \<in> Q" using cm_adj[OF cm] by blast
    then obtain i j where ij: "i < length Qs" "Qs ! i = P" "j < length Qs" "Qs ! j = Q"
      using setQ by (metis in_set_conv_nth)
    have "?key Q < ?key P" using arc_key[OF uw PQ(1,2,4,5)] .
    then have "i < j"
    proof (rule contrapos_pp)
      assume "\<not> i < j"
      then consider "i = j" | "j < i" by linarith
      then show "\<not> ?key Q < ?key P"
      proof cases
        case 1 then show ?thesis using ij PQ(3) by simp
      next
        case 2
        have "(map ?key Qs) ! i \<le> (map ?key Qs) ! j"
          using sortedQ[unfolded sorted_wrt_iff_nth_less, rule_format, of j i] 2 ij by simp
        then show ?thesis using ij by simp
      qed
    qed
    then show "\<exists>i j. i < j \<and> j < length Qs \<and> u \<in> Qs ! i \<and> w \<in> Qs ! j" using ij PQ by blast
  qed
  then show "\<exists>Qs. mset Qs = mset Ps \<and> monotone A Qs" using mset by blast
next
  assume "\<exists>Qs. mset Qs = mset Ps \<and> monotone A Qs"
  then obtain Qs where Qs: "mset Qs = mset Ps" "monotone A Qs" by blast
  have "Qs \<noteq> []" using Qs(1) ne by auto
  then show "eta_t A \<noteq> \<infinity>"
    using lemma_2_value[OF complete_multipartite_perm[OF cm Qs(1)] _ A Qs(2)] by simp
qed

theorem theorem_1:
  assumes cm: "complete_multipartite Ps" and ne: "Ps \<noteq> []"
    and sorted: "sorted_wrt (\<ge>) (map card Ps)"
  shows "eta = mp_bound (map card Ps)" and "eta \<le> length Ps"
proof -
  let ?ns = "map card Ps"
  have pos: "\<forall>n\<in>set ?ns. 0 < n" using part_card_pos[OF cm] by auto
  have ns_ne: "?ns \<noteq> []" using ne by simp
  have upper: "eta \<le> mp_bound ?ns"
  proof -
    have "enat eta \<le> eta_t (forward_orientation Ps)"
      using forward_orientation(1)[OF cm] by (intro eta_le_eta_t) (simp add: acyclic_orientation_def)
    also have "\<dots> = enat (mp_bound ?ns)"
      using lemma_2_value[OF cm ne forward_orientation[OF cm]] .
    finally show ?thesis by simp
  qed
  have "enat (mp_bound ?ns) \<le> eta_t A" if A: "acyclic_orientation A" for A
  proof (cases "eta_t A = \<infinity>")
    case False
    then obtain Qs where Qs: "mset Qs = mset Ps" "monotone A Qs"
      using lemma_2_finite_iff[OF cm ne A] by blast
    have cmQ: "complete_multipartite Qs" using complete_multipartite_perm[OF cm Qs(1)] .
    have neQ: "Qs \<noteq> []" using Qs(1) ne by auto
    have "eta_t A = enat (mp_bound (map card Qs))"
      using lemma_2_value[OF cmQ neQ A Qs(2)] .
    moreover have "mp_bound ?ns \<le> mp_bound (map card Qs)"
      using Qs(1) by (intro mp_bound_sorted_le[OF sorted _ ns_ne pos]) (simp add: mset_map)
    ultimately show ?thesis by simp
  qed simp
  then have "enat (mp_bound ?ns) \<le> (INF A\<in>{A. acyclic_orientation A}. eta_t A)"
    by (auto intro: INF_greatest)
  then have "mp_bound ?ns \<le> eta" by (subst (asm) eta_min_eta_t[symmetric]) simp
  then show eq: "eta = mp_bound ?ns" using upper by simp
  show "eta \<le> length Ps" using eq mp_bound_le_length[OF sorted ns_ne pos] by simp
qed

text \<open>The paper's formula, with real division and ceiling.\<close>

lemma mp_bound_ceiling:
  assumes "\<forall>n\<in>set ns. 0 < n" "ns \<noteq> []"
  shows "mp_bound ns = Max ((\<lambda>i. nat \<lceil>real (sseq ns ! i) / real (ns ! i)\<rceil>) ` {..<length ns})"
  unfolding mp_bound_alt using assms by (intro arg_cong[where f = Max] image_cong) (simp_all add: cdiv_ceiling)

corollary theorem_1_conjecture:
  assumes "complete_multipartite Ps" "Ps \<noteq> []" "sorted_wrt (\<ge>) (map card Ps)"
  shows "enat eta \<le> chi"
  using theorem_1(2)[OF assms] complete_multipartite_chi[OF assms(1)] by (meson enat_ord_simps(1) order.trans)

end

end

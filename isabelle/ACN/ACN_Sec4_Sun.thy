theory ACN_Sec4_Sun
  imports ACN_Suns
begin

section \<open>Complete suns (Section 4, Proposition 4)\<close>

subsection \<open>The labeling of the appendix\<close>

text \<open>
  All quantities are natural numbers: \<open>r = \<lceil>(m+2)/3\<rceil> = (m+4) div 3\<close>, \<open>\<lceil>x/3\<rceil> = (x+2) div 3\<close>,
  and \<open>\<p>(m) = \<lceil>m/2\<rceil> + 1\<close>. \<open>ks_q\<close> is the paper's permutation \<open>\<q>\<close>.
\<close>

definition ks_r :: "nat \<Rightarrow> nat" where "ks_r m = (m + 4) div 3"

definition ks_q :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ks_q m i = (if i = 1 then 1 else if i \<le> m div 2 + 1 then 2 * (i - 1) else 3 + 2 * (m - i))"

definition ks_pm :: "nat \<Rightarrow> nat" where "ks_pm m = (m + 1) div 2 + 1"

definition ks_fu :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ks_fu m i = (if m mod 3 = 2 \<and> i = ks_pm m then ks_r m else ks_q m i div 3 + 1)"

definition ks_fv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "ks_fv m i = (if i = 1 \<or> m div 2 + 2 \<le> i then ks_r m + 1 - (ks_q m i + 2) div 3
     else if m mod 6 = 2 \<and> i = ks_pm m then 2 else ks_r m + 1 - (ks_q m i + 4) div 3)"

text \<open>Identities used in the cases \<open>m \<equiv> 2, 5 (mod 6)\<close> of the claim below.\<close>

lemma S4: "(m::nat) mod 6 = 2 \<Longrightarrow> m + 3 = 2 * ((m + 4) div 3) + (m + 2) div 3"
  by (mod6_cases m)

lemma S2: "(m::nat) mod 6 = 2 \<Longrightarrow> m + 1 = (m + 4) div 3 + (m + 1) div 3 + (m - 1) div 3"
  by (mod6_cases m)

lemma S3:
  assumes c: "(m::nat) mod 6 = 5"
  shows "m + 2 = (m + 4) div 3 + (m + 2) div 3 + (m + 3) div 3"
proof -
  define t where "t = m div 6"
  have mt: "m = 6 * t + 5" using c div_mult_mod_eq[of m 6] unfolding t_def by linarith
  have "m + 4 = 3 * (2 * t + 3)" "m + 2 = 3 * (2 * t + 2) + 1" "m + 3 = 3 * (2 * t + 2) + 2" using mt by simp_all
  then have "(m + 4) div 3 = 2 * t + 3" "(m + 2) div 3 = 2 * t + 2" "(m + 3) div 3 = 2 * t + 2"
    by (simp_all only: div_mod_lin)
  then show ?thesis using mt by simp
qed

context
  fixes m :: nat
  assumes m3: "3 \<le> m"
begin

abbreviation (input) "h \<equiv> m div 2"
abbreviation (input) "r \<equiv> ks_r m"

lemma pm_even: "even m \<Longrightarrow> ks_pm m = h + 1"
  and pm_odd: "odd m \<Longrightarrow> ks_pm m = h + 2"
  unfolding ks_pm_def by presburger+

lemma pm_ge: "h + 1 \<le> ks_pm m" and pm_le: "ks_pm m \<le> h + 2"
  using pm_even pm_odd by (cases "even m"; simp)+

lemma mod6_even: "m mod 6 = 2 \<Longrightarrow> even m" and mod6_mod3: "m mod 6 = 2 \<Longrightarrow> m mod 3 = 2"
  and mod3_even: "m mod 3 = 2 \<Longrightarrow> even m \<Longrightarrow> m mod 6 = 2"
  by presburger+

lemma r_ge2: "2 \<le> r" using m3 unfolding ks_r_def by simp

lemma q1: "ks_q m 1 = 1" by (simp add: ks_q_def)

lemma q_mid: "2 \<le> i \<Longrightarrow> i \<le> h + 1 \<Longrightarrow> ks_q m i = 2 * (i - 1)"
  by (simp add: ks_q_def)

lemma q_last: "h + 2 \<le> i \<Longrightarrow> ks_q m i = 3 + 2 * (m - i)"
  by (simp add: ks_q_def)

lemma q_range: "i \<in> {1..m} \<Longrightarrow> 1 \<le> ks_q m i \<and> ks_q m i \<le> m"
  unfolding ks_q_def by (simp split: if_split) presburger

lemma fu_gen: "\<not> (m mod 3 = 2 \<and> i = ks_pm m) \<Longrightarrow> ks_fu m i = ks_q m i div 3 + 1"
  unfolding ks_fu_def by auto

lemma fu_special: "m mod 3 = 2 \<Longrightarrow> ks_fu m (ks_pm m) = r"
  by (simp add: ks_fu_def)

lemma fv_out: "i = 1 \<or> h + 2 \<le> i \<Longrightarrow> ks_fv m i = r + 1 - (ks_q m i + 2) div 3"
  unfolding ks_fv_def by auto

lemma fv_mid: "2 \<le> i \<Longrightarrow> i \<le> h + 1 \<Longrightarrow> \<not> (m mod 6 = 2 \<and> i = ks_pm m) \<Longrightarrow>
    ks_fv m i = r + 1 - (ks_q m i + 4) div 3"
  unfolding ks_fv_def by auto

lemma fv_special: "m mod 6 = 2 \<Longrightarrow> ks_fv m (ks_pm m) = 2"
proof -
  assume "m mod 6 = 2"
  then have "ks_pm m = h + 1" using pm_even mod6_even by blast
  moreover have "2 \<le> h + 1" using m3 by simp
  ultimately show ?thesis unfolding ks_fv_def using \<open>m mod 6 = 2\<close> by auto
qed

lemma div3_le_r: "x \<le> m + 4 \<Longrightarrow> x div 3 \<le> r"
  unfolding ks_r_def by (simp add: div_le_mono)

lemma ks_q_range: "i \<in> {1..m} \<Longrightarrow> 1 \<le> ks_q m i \<and> ks_q m i \<le> m"
  by (rule q_range)

lemma ks_q_inj:
  assumes "i \<in> {1..m}" "j \<in> {1..m}" "ks_q m i = ks_q m j"
  shows "i = j"
proof -
  have parity: "odd (ks_q m k) \<longleftrightarrow> k = 1 \<or> h + 2 \<le> k" if "k \<in> {1..m}" for k
    using that unfolding ks_q_def by auto
  consider "i = 1" | "2 \<le> i" "i \<le> h + 1" | "h + 2 \<le> i"
    using assms(1) by (cases "i = 1"; cases "h + 2 \<le> i") auto
  then show ?thesis
  proof cases
    case 1
    then have qj: "ks_q m j = 1" using assms q1 by simp
    then have "j = 1 \<or> h + 2 \<le> j" using parity[OF assms(2)] by simp
    then show ?thesis using q_last[of j] qj 1 by auto
  next
    case 2
    then have "even (ks_q m i)" using parity[OF assms(1)] by simp
    then have "even (ks_q m j)" using assms(3) by simp
    then have "2 \<le> j" "j \<le> h + 1" using parity[OF assms(2)] assms(2) by auto
    then show ?thesis using 2 assms q_mid by simp
  next
    case 3
    then have "odd (ks_q m i)" using parity[OF assms(1)] by simp
    then have "odd (ks_q m j)" using assms(3) by simp
    then have "j = 1 \<or> h + 2 \<le> j" using parity[OF assms(2)] by simp
    then show ?thesis
    proof
      assume "j = 1"
      then show ?thesis using 3 assms q1 q_last by simp
    next
      assume "h + 2 \<le> j"
      then show ?thesis using 3 assms q_last by simp
    qed
  qed
qed

lemma ks_fu_range:
  assumes "i \<in> {1..m}"
  shows "1 \<le> ks_fu m i \<and> ks_fu m i \<le> r"
proof (cases "m mod 3 = 2 \<and> i = ks_pm m")
  case True
  then show ?thesis using fu_special r_ge2 by auto
next
  case False
  have "ks_q m i \<le> m + 4" using q_range[OF assms] by simp
  moreover have "ks_q m i div 3 + 1 = (ks_q m i + 3) div 3" by simp
  ultimately have "ks_q m i div 3 + 1 \<le> r"
    using q_range[OF assms] div3_le_r[of "ks_q m i + 3"] by simp
  then show ?thesis using fu_gen[OF False] by simp
qed

lemma ks_fv_range:
  assumes "i \<in> {1..m}"
  shows "1 \<le> ks_fv m i \<and> ks_fv m i \<le> r"
proof -
  have qr: "1 \<le> ks_q m i" "ks_q m i \<le> m" using q_range[OF assms] by auto
  have "1 \<le> i" using assms by simp
  then consider "i = 1 \<or> h + 2 \<le> i" | "2 \<le> i" "i \<le> h + 1" "\<not> (m mod 6 = 2 \<and> i = ks_pm m)"
    | "m mod 6 = 2" "i = ks_pm m" by force
  then show ?thesis
  proof cases
    case 1
    have "1 \<le> (ks_q m i + 2) div 3" using qr by simp
    moreover have "(ks_q m i + 2) div 3 \<le> r" using qr by (intro div3_le_r) simp
    ultimately show ?thesis using fv_out[OF 1] by arith
  next
    case 2
    have "ks_q m i \<le> m" using qr by simp
    then have "(ks_q m i + 4) div 3 \<le> r" by (intro div3_le_r) simp
    moreover have "1 \<le> (ks_q m i + 4) div 3" by simp
    ultimately show ?thesis using fv_mid[OF 2] by arith
  next
    case 3
    then show ?thesis using fv_special r_ge2 by simp
  qed
qed

lemma ks_fu_m: "2 \<le> ks_fu m m"
proof -
  have h2: "2 * h \<le> m" "m \<le> 2 * h + 1" by simp_all
  have "m = 3" if "m = ks_pm m"
  proof (cases "even m")
    case True
    then show ?thesis using pm_even[OF True] that h2 m3 by linarith
  next
    case False
    then have "2 * h + 1 = m" by (rule odd_two_times_div_two_succ)
    then show ?thesis using pm_odd[OF False] that by linarith
  qed
  then have "\<not> (m mod 3 = 2 \<and> m = ks_pm m)" by auto
  moreover have "ks_q m m = 3" using m3 q_last[of m] by simp
  ultimately show ?thesis using fu_gen by simp
qed

text \<open>
  The paper's claim \<open>f(v_i) = 2r - \<q>(i) + f(u_i) - f(v_{i-1})\<close>, by the cases of the appendix. In the
  case \<open>m \<equiv> 2 (mod 6)\<close>, \<open>i = \<lfloor>m/2\<rfloor> + 1\<close>, the paper takes \<open>r = m/3 + 1\<close>; in fact \<open>r = (m+4)/3\<close>, so
  \<open>f(v_{i-1}) = 2\<close> (not 1) and \<open>f(v_i) = 2 = 3r - m - f(v_{i-1})\<close>.
\<close>

lemma div3_lin: "((a::nat) + 3 * t) div 3 = a div 3 + t"
  by simp

lemma ident_mid':
  "2 * ((j::nat) + 1) = (2 * j + 4) div 3 + (2 * j + 2) div 3 + 2 * j div 3 + 1"
proof -
  define t c where "t = j div 3" and "c = j mod 3"
  have j: "j = 3 * t + c" and c: "c < 3" by (simp_all add: t_def c_def)
  have "2 * j + 4 = (2 * c + 4) + 3 * (2 * t)" "2 * j + 2 = (2 * c + 2) + 3 * (2 * t)"
    "2 * j = 2 * c + 3 * (2 * t)" using j by simp_all
  then have A: "(2 * j + 4) div 3 = (2 * c + 4) div 3 + 2 * t"
    and B: "(2 * j + 2) div 3 = (2 * c + 2) div 3 + 2 * t"
    and C: "2 * j div 3 = 2 * c div 3 + 2 * t" by (simp_all only: div3_lin)
  consider "c = 0" | "c = 1" | "c = 2" using c by linarith
  then show ?thesis by cases (simp only: A B C, simp add: j)+
qed

lemma ident_mid:
  assumes "1 \<le> (i::nat)"
  shows "2 * i = (2 * i + 2) div 3 + 2 * i div 3 + (2 * i - 2) div 3 + 1"
proof -
  obtain j where "i = j + 1" using assms by (metis add.commute le_Suc_ex plus_1_eq_Suc)
  moreover have "2 * (j + 1) + 2 = 2 * j + 4" "2 * (j + 1) = 2 * j + 2" "2 * (j + 1) - 2 = 2 * j" by simp_all
  ultimately show ?thesis using ident_mid'[of j] by simp
qed

lemma ident_last: "2 * (k::nat) + 4 = (2 * k + 5) div 3 + (2 * k + 7) div 3 + (2 * k + 3) div 3"
  by (mod3_cases k simps: distrib_left mult.assoc[symmetric])

lemma div3_of: "(x::nat) = a + 3 * b \<Longrightarrow> x div 3 = a div 3 + b"
  by simp

lemma m6: obtains t where "m = 6 * t + m mod 6"
  using div_mult_mod_eq[of m 6] by (metis mult.commute)

lemma S1:
  assumes "m mod 6 \<in> {0, 1, 3, 4}"
  shows "m + m mod 2 = (m + 1 + m mod 2) div 3 + (m - m mod 2 + 4) div 3 + (m - 1 + m mod 2) div 3"
proof -
  obtain t where mt0: "m = 6 * t + m mod 6" by (rule m6)
  have "m mod 2 = m mod 6 mod 2" by (simp add: mod_mod_cancel)
  from assms consider "m mod 6 = 0" | "m mod 6 = 1" | "m mod 6 = 3" | "m mod 6 = 4" by auto
  then show ?thesis
  proof cases
    case 1
    then have mt: "m = 6 * t" "m mod 2 = 0" using mt0 \<open>m mod 2 = _\<close> by simp_all
    then have t: "1 \<le> t" using m3 by simp
    have e: "m + 1 + m mod 2 = 1 + 3 * (2 * t)" "m - m mod 2 + 4 = 1 + 3 * (2 * t + 1)"
      "m - 1 + m mod 2 = 2 + 3 * (2 * t - 1)" using mt t by simp_all
    have "(m + 1 + m mod 2) div 3 = 2 * t" "(m - m mod 2 + 4) div 3 = 2 * t + 1"
      "(m - 1 + m mod 2) div 3 = 2 * t - 1" using div3_of[OF e(1)] div3_of[OF e(2)] div3_of[OF e(3)] by simp_all
    then show ?thesis using mt t by simp
  next
    case 2
    then have mt: "m = 6 * t + 1" "m mod 2 = 1" using mt0 \<open>m mod 2 = _\<close> by simp_all
    have e: "m + 1 + m mod 2 = 0 + 3 * (2 * t + 1)" "m - m mod 2 + 4 = 1 + 3 * (2 * t + 1)"
      "m - 1 + m mod 2 = 1 + 3 * (2 * t)" using mt by simp_all
    have "(m + 1 + m mod 2) div 3 = 2 * t + 1" "(m - m mod 2 + 4) div 3 = 2 * t + 1"
      "(m - 1 + m mod 2) div 3 = 2 * t" using div3_of[OF e(1)] div3_of[OF e(2)] div3_of[OF e(3)] by simp_all
    then show ?thesis using mt by simp
  next
    case 3
    then have mt: "m = 6 * t + 3" "m mod 2 = 1" using mt0 \<open>m mod 2 = _\<close> by simp_all
    have e: "m + 1 + m mod 2 = 2 + 3 * (2 * t + 1)" "m - m mod 2 + 4 = 0 + 3 * (2 * t + 2)"
      "m - 1 + m mod 2 = 0 + 3 * (2 * t + 1)" using mt by simp_all
    have "(m + 1 + m mod 2) div 3 = 2 * t + 1" "(m - m mod 2 + 4) div 3 = 2 * t + 2"
      "(m - 1 + m mod 2) div 3 = 2 * t + 1" using div3_of[OF e(1)] div3_of[OF e(2)] div3_of[OF e(3)] by simp_all
    then show ?thesis using mt by simp
  next
    case 4
    then have mt: "m = 6 * t + 4" "m mod 2 = 0" using mt0 \<open>m mod 2 = _\<close> by simp_all
    have e: "m + 1 + m mod 2 = 2 + 3 * (2 * t + 1)" "m - m mod 2 + 4 = 2 + 3 * (2 * t + 2)"
      "m - 1 + m mod 2 = 0 + 3 * (2 * t + 1)" using mt by simp_all
    have "(m + 1 + m mod 2) div 3 = 2 * t + 1" "(m - m mod 2 + 4) div 3 = 2 * t + 2"
      "(m - 1 + m mod 2) div 3 = 2 * t + 1" using div3_of[OF e(1)] div3_of[OF e(2)] div3_of[OF e(3)] by simp_all
    then show ?thesis using mt by simp
  qed
qed

lemma lin4: "(m::nat) + 3 = 2 * r + X \<Longrightarrow> X \<le> r + 1 \<Longrightarrow> 2 + (r + 1 - X) + m = 2 * r + r"
  by arith

lemma lin5a: "Q + 2 = r + A + C \<Longrightarrow> (A::nat) \<le> r + 1 \<Longrightarrow> (r + 1 - A) + 2 + Q = 2 * r + (C + 1)"
  by arith

lemma lin5b: "Q + 2 = r + A + B \<Longrightarrow> (A::nat) \<le> r + 1 \<Longrightarrow> B \<le> r + 1 \<Longrightarrow>
    (r + 1 - A) + (r + 1 - B) + Q = 2 * r + r"
  by arith

lemma lin5c: "Q + 1 = A + B + C \<Longrightarrow> (A::nat) \<le> r + 1 \<Longrightarrow> B \<le> r + 1 \<Longrightarrow>
    (r + 1 - A) + (r + 1 - B) + Q = 2 * r + (C + 1)"
  by arith

lemma lin_mid: "(A::nat) \<le> r \<Longrightarrow> B \<le> r \<Longrightarrow> 2 * i = A + B + C + 1 \<Longrightarrow> 3 \<le> i \<Longrightarrow>
    (r + 1 - A) + (r + 1 - B) + (2 * i - 2) = 2 * r + (C + 1)"
  by arith

lemma lin_last: "(X::nat) \<le> r \<Longrightarrow> Y \<le> r \<Longrightarrow> 2 * k + 4 = X + Y + Z \<Longrightarrow>
    (r + 1 - X) + (r + 1 - Y) + (2 * k + 3) = 2 * r + (Z + 1)"
  by arith

lemma ks_claim:
  assumes i: "i \<in> {1..m}"
  shows "ks_fv m i + ks_fv m (sprev m i) + ks_q m i = 2 * r + ks_fu m i"
proof -
  have pm3: "3 \<le> ks_pm m" using m3 by (simp add: ks_pm_def)
  consider "i = 1" | "i = 2" | "3 \<le> i" "i \<le> h + 1" "\<not> (m mod 6 = 2 \<and> i = h + 1)"
    | "m mod 6 = 2" "i = h + 1" | "i = h + 2" | "h + 3 \<le> i" "i \<le> m"
    using i by (cases "i = 1"; cases "i = 2"; cases "i \<le> h + 1"; cases "m mod 6 = 2 \<and> i = h + 1";
        cases "i = h + 2") auto
  then show ?thesis
  proof cases
    case 1
    have "sprev m i = m" using 1 by (simp add: sprev_def)
    moreover have "ks_q m m = 3" using m3 q_last[of m] by simp
    moreover have "ks_fv m m = r" using fv_out[of m] m3 \<open>ks_q m m = 3\<close> by simp
    moreover have "ks_fv m 1 = r" using fv_out[of 1] q1 by simp
    moreover have "ks_fu m 1 = 1" using fu_gen[of 1] pm3 q1 by simp
    ultimately show ?thesis using 1 q1 by simp
  next
    case 2
    have "sprev m i = 1" using 2 by (simp add: sprev_def)
    moreover have "2 \<le> h + 1" using m3 by simp
    then have "ks_q m 2 = 2" using q_mid[of 2] by simp
    moreover have "ks_fv m 2 = r - 1" using fv_mid[of 2] \<open>2 \<le> h + 1\<close> pm3 \<open>ks_q m 2 = 2\<close> by simp
    moreover have "ks_fv m 1 = r" using fv_out[of 1] q1 by simp
    moreover have "ks_fu m 2 = 1" using fu_gen[of 2] pm3 \<open>ks_q m 2 = 2\<close> by simp
    ultimately show ?thesis using 2 r_ge2 by simp
  next
    case 3
    have prev: "sprev m i = i - 1" using 3 by (simp add: sprev_def)
    have nsp: "\<not> (m mod 6 = 2 \<and> i = ks_pm m)" using 3 pm_even mod6_even by metis
    have "\<not> (m mod 3 = 2 \<and> i = ks_pm m)"
    proof (cases "even m")
      case True then show ?thesis using nsp mod3_even by blast
    next
      case False then show ?thesis using 3 pm_odd by simp
    qed
    note nsp = nsp this
    have nsp': "\<not> (m mod 6 = 2 \<and> i - 1 = ks_pm m)" using 3 pm_ge by linarith
    have qi: "ks_q m i = 2 * i - 2" using q_mid[of i] 3 by simp
    have qi1: "ks_q m (i - 1) = 2 * i - 4" using q_mid[of "i - 1"] 3 by simp
    have fvi: "ks_fv m i = r + 1 - (2 * i + 2) div 3" using fv_mid[of i] 3 nsp qi by simp
    have fvi1: "ks_fv m (i - 1) = r + 1 - 2 * i div 3" using fv_mid[of "i - 1"] 3 nsp' qi1 by simp
    have fui: "ks_fu m i = (2 * i - 2) div 3 + 1" using fu_gen nsp qi by simp
    have b1: "(2 * i + 2) div 3 \<le> r" using 3 by (intro div3_le_r) simp
    have b2: "2 * i div 3 \<le> r" using 3 by (intro div3_le_r) simp
    have "1 \<le> i" using 3 by simp
    show ?thesis unfolding prev qi fvi fvi1 fui by (rule lin_mid[OF b1 b2 ident_mid[OF \<open>1 \<le> i\<close>]]) (use 3 in simp)
  next
    case 4
    have h4: "4 \<le> h" using 4 m3 by presburger
    have pm: "ks_pm m = i" using 4 pm_even mod6_even by simp
    have hm: "2 * h = m" using mod6_even[OF 4(1)] by simp
    have prev: "sprev m i = h" using 4 h4 by (simp add: sprev_def)
    have qi: "ks_q m i = m" using q_mid[of i] 4 h4 hm by simp
    have nsp': "\<not> (m mod 6 = 2 \<and> h = ks_pm m)" using pm 4 by simp
    have qh: "ks_q m h = m - 2" using q_mid[of h] h4 hm by simp
    have q4: "ks_q m h + 4 = m + 2" using qh m3 by simp
    have "ks_fv m h = r + 1 - (ks_q m h + 4) div 3" using fv_mid[of h] h4 nsp' by simp
    then have fvh: "ks_fv m h = r + 1 - (m + 2) div 3" unfolding q4 .
    have fvi: "ks_fv m i = 2" using fv_special 4 pm by simp
    have fui: "ks_fu m i = r" using fu_special mod6_mod3 4 pm by metis
    have b: "(m + 2) div 3 \<le> r + 1" unfolding ks_r_def by (simp add: div_le_mono)
    show ?thesis unfolding prev qi fvh fvi fui
      using lin4[OF S4[OF 4(1), folded ks_r_def] b] by (simp add: add.commute)
  next
    case 5
    have hm: "2 * h + m mod 2 = m" by simp
    have prev: "sprev m i = h + 1" using 5 by (simp add: sprev_def)
    have Q0: "ks_q m i = 3 + 2 * (m - (h + 2))" using q_last[of i] 5 by simp
    have "m mod 2 \<le> 1" by simp
    then have "3 + 2 * (m - (h + 2)) = m - 1 + m mod 2" using hm m3 by arith
    then have Q: "ks_q m i = m - 1 + m mod 2" using Q0 by simp
    have "1 \<le> h" using m3 by simp
    then have "ks_q m (h + 1) = 2 * h" using q_mid[of "h + 1"] by simp
    then have qh: "ks_q m (h + 1) = m - m mod 2" using hm by arith
    have fvi: "ks_fv m i = r + 1 - (m + 1 + m mod 2) div 3"
      using fv_out[of i] 5 Q m3 by (simp add: add.assoc)
    have "m mod 2 < 2" by simp
    then have "m + 1 + m mod 2 \<le> m + 4" by linarith
    then have "(m + 1 + m mod 2) div 3 \<le> (m + 4) div 3" by (rule div_le_mono)
    then have bA: "(m + 1 + m mod 2) div 3 \<le> r + 1" unfolding ks_r_def by simp
    show ?thesis
    proof (cases "m mod 6 = 2")
      case True
      have pm: "ks_pm m = h + 1" using True pm_even mod6_even by simp
      have even: "m mod 2 = 0" using mod6_even[OF True] by simp
      have fvh: "ks_fv m (h + 1) = 2" using fv_special True pm by simp
      have fui: "ks_fu m i = (m - 1) div 3 + 1" using fu_gen[of i] pm 5 Q even by simp
      show ?thesis unfolding prev fvi fvh fui Q even
        using lin5a[of "m - 1" "(m + 1) div 3" "(m - 1) div 3"] S2[OF True] bA even m3
        by (simp add: ks_r_def)
    next
      case False
      have nsp: "\<not> (m mod 6 = 2 \<and> h + 1 = ks_pm m)" using False by simp
      have q4: "ks_q m (h + 1) + 4 = m - m mod 2 + 4" using qh m3 by simp
      have "ks_fv m (h + 1) = r + 1 - (ks_q m (h + 1) + 4) div 3" using fv_mid[of "h + 1"] m3 nsp by simp
      then have fvh: "ks_fv m (h + 1) = r + 1 - (m - m mod 2 + 4) div 3" unfolding q4 .
      have "(m - m mod 2 + 4) div 3 \<le> (m + 4) div 3" by (rule div_le_mono) simp
      then have bB: "(m - m mod 2 + 4) div 3 \<le> r + 1" unfolding ks_r_def by simp
      show ?thesis
      proof (cases "m mod 3 = 2 \<and> i = ks_pm m")
        case True
        have "\<not> even m"
        proof
          assume "even m"
          then have "ks_pm m = h + 1" by (rule pm_even)
          then show False using True 5 by simp
        qed
        then have odd: "m mod 2 = 1" by (simp add: odd_iff_mod_2_eq_one)
        have c5: "m mod 6 = 5" using True odd by presburger
        have fui: "ks_fu m i = r" using True fu_special by simp
        show ?thesis unfolding prev fvi fvh fui Q odd
          using lin5b[of m "(m + 2) div 3" "(m + 3) div 3"] S3[OF c5] bA bB odd m3
          by (simp add: ks_r_def)
      next
        case nsp2: False
        have "\<not> (m mod 3 = 2 \<and> odd m)"
        proof
          assume a: "m mod 3 = 2 \<and> odd m"
          then have "ks_pm m = i" using pm_odd 5 by simp
          then show False using nsp2 a by simp
        qed
        then have "m mod 6 = 0 \<or> m mod 6 = 1 \<or> m mod 6 = 3 \<or> m mod 6 = 4" using False by presburger
        then have c: "m mod 6 \<in> {0, 1, 3, 4}" by auto
        have fui: "ks_fu m i = (m - 1 + m mod 2) div 3 + 1" using fu_gen nsp2 Q by simp
        have e: "m - 1 + m mod 2 + 1 = (m + 1 + m mod 2) div 3 + (m - m mod 2 + 4) div 3 + (m - 1 + m mod 2) div 3"
          using S1[OF c] m3 by simp
        show ?thesis unfolding prev fvi fvh fui Q by (rule lin5c[OF e bA bB])
      qed
    qed
  next
    case 6
    define k where "k = m - i"
    have prev: "sprev m i = i - 1" using 6 by (simp add: sprev_def)
    have qi: "ks_q m i = 2 * k + 3" using q_last[of i] 6 by (simp add: k_def)
    have qi1: "ks_q m (i - 1) = 2 * k + 5" using q_last[of "i - 1"] 6 by (simp add: k_def)
    have fvi: "ks_fv m i = r + 1 - (2 * k + 5) div 3" using fv_out[of i] 6 qi by simp
    have "h + 2 \<le> i - 1" using 6 by simp
    then have fvi1_0: "ks_fv m (i - 1) = r + 1 - (ks_q m (i - 1) + 2) div 3" using fv_out[of "i - 1"] by blast
    have q7: "ks_q m (i - 1) + 2 = 2 * k + 7" using qi1 by simp
    have fvi1: "ks_fv m (i - 1) = r + 1 - (2 * k + 7) div 3" using fvi1_0 unfolding q7 .
    have nsp: "\<not> (m mod 3 = 2 \<and> i = ks_pm m)" using 6 pm_le by linarith
    have fui: "ks_fu m i = (2 * k + 3) div 3 + 1" using fu_gen nsp qi by simp
    have "i - 1 \<in> {1..m}" using 6 by auto
    then have "ks_q m (i - 1) \<le> m" using q_range by blast
    then have b: "(2 * k + 7) div 3 \<le> r" "(2 * k + 5) div 3 \<le> r" using qi1 by (simp_all add: div3_le_r)
    show ?thesis unfolding prev qi fvi fvi1 fui by (rule lin_last[OF b(2) b(1) ident_last])
  qed
qed

end

subsection \<open>Proposition 4\<close>

text \<open>The complete sun \<open>KS_m\<close>: the base graph is the clique on \<open>u_1, \<dots>, u_m\<close>.\<close>

definition ks_base :: "nat \<Rightarrow> (nat + nat) edge set" where
  "ks_base m = all_edges (Inl ` {1..m})"

locale complete_sun = sun_graph m "{1..m}" "ks_base m" for m :: nat
begin

lemma adj_uu: "S.vert_adj (Inl i) (Inl j) \<longleftrightarrow> i \<in> {1..m} \<and> j \<in> {1..m} \<and> i \<noteq> j"
  unfolding adj_ll Bs.vert_adj_edge unfolding ks_base_def all_edges_doubleton by auto

lemma m3': "3 \<le> m" by (rule m3)

lemma Bs_N:
  assumes "i \<in> {1..m}"
  shows "Bs.neighborhood (Inl i) = Inl ` ({1..m} - {i})"
  by (neighborhood_eq nb: Bs.in_neighborhood_iff Bs.vert_adj_edge simps: ks_base_def all_edges_doubleton assms[simplified])

lemma Bs_sum:
  assumes "i \<in> {1..m}"
  shows "Bs.sumN (case_sum fu fv) (Inl i) + fu i = sum fu {1..m}"
proof -
  have "Bs.sumN (case_sum fu fv) (Inl i) = sum fu ({1..m} - {i})"
    unfolding Bs.sumN_def Bs_N[OF assms] by (simp add: sum_Inl)
  then show ?thesis using assms by (simp add: sum.remove)
qed

lemma clique: "S.clique (Inl ` {1..m})"
  unfolding S.clique_def
proof (intro conjI ballI impI)
  show "Inl ` {1..m} \<subseteq> sun_verts m {1..m}" by (auto simp: sun_verts_def)
next
  fix x y :: "nat + nat" assume "x \<in> Inl ` {1..m}" "y \<in> Inl ` {1..m}" "x \<noteq> y"
  then show "S.vert_adj x y" by (auto simp: adj_uu)
qed

lemma degree_u: "i \<in> {1..m} \<Longrightarrow> S.degree (Inl i) = m + 1"
proof -
  assume i: "i \<in> {1..m}"
  have "Bs.degree (Inl i) = m - 1" unfolding Bs.degree_eq Bs_N[OF i] using i by (simp add: card_image)
  then show ?thesis using degree_l[OF i] m3' by simp
qed

end

theorem proposition_4:
  assumes m3: "3 \<le> m"
  shows "fin_sgraph.eta (sun_verts m {1..m}) (sun_edges m (ks_base m)) = cdiv (m + 2) 3"
proof -
  interpret complete_sun m using m3 by unfold_locales (auto simp: ks_base_def all_edges_def)
  have r: "cdiv (m + 2) 3 = ks_r m" by (simp add: cdiv_def ks_r_def)
  show ?thesis
  proof (rule order.antisym)
    let ?Q = "Inl ` {1..m} :: (nat + nat) set"
    have deg: "S.degree ` ?Q = {m + 1}"
    proof
      show "S.degree ` ?Q \<subseteq> {m + 1}"
      proof (rule image_subsetI)
        fix x assume "x \<in> ?Q"
        then obtain i where "i \<in> {1..m}" "x = Inl i" by blast
        then show "S.degree x \<in> {m + 1}" using degree_u[of i] by simp
      qed
      have "(Inl 1 :: nat + nat) \<in> ?Q" using m3 by simp
      moreover have "S.degree (Inl 1 :: nat + nat) = m + 1" using degree_u m3 by simp
      ultimately show "{m + 1} \<subseteq> S.degree ` ?Q" by (metis empty_subsetI image_eqI insert_subset)
    qed
    have "card ?Q = m" by (simp add: card_image)
    moreover have "?Q \<noteq> {}" using m3 by simp
    ultimately have "cdiv (Min (S.degree ` ?Q) + 1) (Max (S.degree ` ?Q) + 2 - card ?Q) \<le> S.eta"
      using S.corollary_2[OF clique] by blast
    then show "cdiv (m + 2) 3 \<le> S.eta" using deg \<open>card ?Q = m\<close> by (simp add: eval_nat_numeral)
  next
    let ?r = "ks_r m"
    let ?fu = "ks_fu m" and ?fv = "ks_fv m"
    let ?f = "case_sum ?fu ?fv"
    have r2: "2 \<le> ?r" using r_ge2[OF m3] .
    have FU: "m + 1 \<le> sum ?fu {1..m}"
    proof -
      have "sum ?fu {1..m} = ?fu m + sum ?fu ({1..m} - {m})" using m3 by (simp add: sum.remove)
      moreover have "card ({1..m} - {m}) \<le> sum ?fu ({1..m} - {m})"
        using ks_fu_range[OF m3] by (metis (no_types, lifting) DiffD1 card_eq_sum sum_mono)
      moreover have "card ({1..m} - {m}) = m - 1" using m3 by simp
      ultimately show ?thesis using ks_fu_m[OF m3] m3 by linarith
    qed
    have su: "S.sumN ?f (Inl i) + ks_q m i = sum ?fu {1..m} + 2 * ?r" if i: "i \<in> {1..m}" for i
    proof -
      have "S.sumN ?f (Inl i) = Bs.sumN ?f (Inl i) + ?fv i + ?fv (sprev m i)" using sumN_l[OF i] by simp
      then show ?thesis using Bs_sum[OF i, of ?fu ?fv] ks_claim[OF m3 i] by linarith
    qed
    have sv: "S.sumN ?f (Inr j) \<le> 2 * ?r" if j: "j \<in> {1..m}" for j
      using sumN_r[OF j, of ?fu ?fv] ks_fu_range[OF m3 j] ks_fu_range[OF m3 snext_in[OF j]] by simp
    have "S.eta \<le> ?r"
    proof (eta_upper rule: S.eta_le_coloring)
      show "S.labeling ?r ?f"
        unfolding S.labeling_def unfolding sun_verts_def using ks_fu_range[OF m3] ks_fv_range[OF m3] by auto
    next
      fix x y assume xy: "S.vert_adj x y"
      have uv: "S.sumN ?f (Inr j) < S.sumN ?f (Inl i)" if i: "i \<in> {1..m}" and j: "j \<in> {1..m}" for i j
        using su[OF i] sv[OF j] ks_q_range[OF m3 i] FU by linarith
      show "S.sumN ?f x \<noteq> S.sumN ?f y"
      proof (sum_edge_cases adj: xy sym: S.vert_adj_sym rr: adj_rr)
        fix i j assume ll: "S.vert_adj (Inl i) (Inl j)"
        then have ij: "i \<in> {1..m}" "j \<in> {1..m}" "i \<noteq> j" using ll adj_uu by simp_all
        then have "ks_q m i \<noteq> ks_q m j" using ks_q_inj[OF m3] by blast
        then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inl j)" using su[OF ij(1)] su[OF ij(2)] by auto
      next
        fix i j assume lr: "S.vert_adj (Inl i) (Inr j)"
        then have "j \<in> {1..m}" "i = j \<or> i = snext m j" using lr adj_lr by simp_all
        then have "i \<in> {1..m}" "j \<in> {1..m}" using snext_in by auto
        then show "S.sumN ?f (Inl i) \<noteq> S.sumN ?f (Inr j)" using uv by fastforce
      qed
    next
      show "0 < ?r" using r2 by simp
    qed
    then show "S.eta \<le> cdiv (m + 2) 3" using r r2 by auto
  qed
qed

end

/-
  Section 3: fans, windmills and wheels, and Proposition 1 (odd cycles).
  Paths and cycles are Mathlib's `pathGraph` and `cycleGraph` on `Fin n`; the vertex `k` is the
  paper's v_{k+1}.  Labelings of these graphs are given by functions on the indices.
-/
import ACN.Sec3

set_option linter.unusedSectionVars false

open Finset

/-! ## Sums over neighborhoods in graphs on `Fin N` -/

namespace ACN

theorem sum_range_ite_or {N a b : ℕ} (F : ℕ → ℕ) (hab : a ≠ b) :
    ∑ k ∈ range N, (if k = a ∨ k = b then F k else 0) =
      (if a < N then F a else 0) + (if b < N then F b else 0) := by
  have : ∀ k, (if k = a ∨ k = b then F k else 0) =
      (if k = a then F k else 0) + (if k = b then F k else 0) := by
    intro k; split_omega
  rw [sum_congr rfl fun k _ => this k, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp only [mem_range]

end ACN

namespace SimpleGraph

open ACN

/-- f(N(i)) in a graph on `Fin N` whose adjacency is a predicate on the indices. -/
theorem sumN_fin {N : ℕ} {H : SimpleGraph (Fin N)} [DecidableRel H.Adj] (P : ℕ → Prop)
    [DecidablePred P] (i : Fin N) (hP : ∀ j : Fin N, H.Adj i j ↔ P j.val) (F : ℕ → ℕ) :
    H.sumN (fun j => F j.val) i = ∑ k ∈ range N, if P k then F k else 0 := by
  rw [sumN_eq_sum_ite, ← Fin.sum_univ_eq_sum_range (fun k => if P k then F k else 0) N]
  exact sum_congr rfl fun j _ => if_congr (hP j) rfl rfl

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Joining one vertex to a graph without universal vertices keeps η. -/
theorem theorem_2_K1 (h : G.maxDegree + 2 ≤ Fintype.card V) : (G.joinK (Fin 1)).eta = G.eta := by
  rw [theorem_2 (by simp only [Fintype.card_fin]; omega), Fintype.card_fin]
  exact max_eq_left G.eta_pos

/-! ## Paths and fans -/

/-- f(N(i)) in the path P_N. -/
theorem pathGraph_sumN {N : ℕ} (F : ℕ → ℕ) (i : Fin N) :
    (pathGraph N).sumN (fun j => F j.val) i =
      (if 0 < i.val then F (i.val - 1) else 0) + (if i.val + 1 < N then F (i.val + 1) else 0) := by
  rcases Nat.eq_zero_or_pos i.val with h0 | h0
  · rw [sumN_fin (fun k => k = 1) i (fun j => by rw [pathGraph_adj]; omega), sum_ite_eq']
    simp [h0]
  · rw [sumN_fin (fun k => k = i.val - 1 ∨ k = i.val + 1) i (fun j => by rw [pathGraph_adj]; omega),
      sum_range_ite_or F (by omega)]
    have : i.val - 1 < N := by omega
    simp only [this, h0, ite_true]

theorem pathGraph_degree {N : ℕ} (i : Fin N) :
    (pathGraph N).degree i = (if 0 < i.val then 1 else 0) + (if i.val + 1 < N then 1 else 0) := by
  rw [← sumN_one, ← pathGraph_sumN (fun _ => 1) i]

theorem pathGraph_maxDegree (N : ℕ) : (pathGraph N).maxDegree ≤ 2 :=
  maxDegree_le_of_forall_degree_le _ _ fun i => by rw [pathGraph_degree]; split_omega

/-- η(P_N) = 2 for N ≥ 4 (the paper uses the bound for trees of ref. [5]). Labeling: 2 on the
even vertices and on the last one, 1 elsewhere. -/
theorem pathGraph_eta {N : ℕ} (hN : 4 ≤ N) : (pathGraph N).eta = 2 := by
  let F : ℕ → ℕ := fun j => if j % 2 = 0 ∨ j = N - 1 then 2 else 1
  let S : ℕ → ℕ := fun a =>
    (if 0 < a then F (a - 1) else 0) + (if a + 1 < N then F (a + 1) else 0)
  have hS : ∀ a, a + 1 < N → S a ≠ S (a + 1) := by
    intro a ha
    simp only [S, F]
    split_omega
  have le2 : (pathGraph N).eta ≤ 2 := by
    refine eta_le_of_labeling (f := fun j => F j.val) two_pos
      (fun j => by simp only [F]; split_omega) fun i j hij => ?_
    rw [pathGraph_sumN, pathGraph_sumN]
    rcases pathGraph_adj.1 hij with h | h
    · rw [← h]; exact hS _ (h ▸ j.2)
    · rw [← h]; exact (hS _ (h ▸ i.2)).symm
  refine eta_eq_two (u := ⟨1, by omega⟩) (v := ⟨2, by omega⟩) le2 (pathGraph_adj.2 (by simp))
    ?_
  rw [pathGraph_degree, pathGraph_degree]
  dsimp only
  split_omega

/-- Fans: η(F_n) = η(P_{n+1} ∨ K_1) = 2 for n ≥ 3. -/
theorem fan {n : ℕ} (hn : 3 ≤ n) : ((pathGraph (n + 1)).joinK (Fin 1)).eta = 2 := by
  rw [theorem_2_K1 (by have := pathGraph_maxDegree (n + 1); simp only [Fintype.card_fin]; omega),
    pathGraph_eta (by omega)]

/-! ## Windmills -/

/-- m K_p: m disjoint copies of K_p; the vertex (i, j) is the j-th vertex of copy i. -/
def copiesK (m p : ℕ) : SimpleGraph (Fin m × Fin p) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

instance (m p : ℕ) : DecidableRel (copiesK m p).Adj :=
  fun x y => inferInstanceAs (Decidable (x.1 = y.1 ∧ x.2 ≠ y.2))

section copies

variable {m p : ℕ}

theorem copiesK_adj {x y : Fin m × Fin p} : (copiesK m p).Adj x y ↔ x.1 = y.1 ∧ x.2 ≠ y.2 :=
  .rfl

/-- The vertices of the copy of `x`. -/
def copyOf (x : Fin m × Fin p) : Finset (Fin m × Fin p) :=
  univ.map ⟨fun j => (x.1, j), fun _ _ h => (Prod.mk.inj h).2⟩

theorem insert_neighborFinset_copiesK (x : Fin m × Fin p) :
    insert x ((copiesK m p).neighborFinset x) = copyOf x := by
  ext y
  simp only [mem_insert, mem_neighborFinset, copiesK_adj, copyOf, mem_map, mem_univ, true_and]
  constructor
  · rintro (h | ⟨h1, -⟩)
    · exact ⟨x.2, by subst h; rfl⟩
    · exact ⟨y.2, Prod.ext h1 rfl⟩
  · rintro ⟨j, rfl⟩
    by_cases h : x.2 = j
    · left; subst h; rfl
    · right; exact ⟨rfl, h⟩

theorem copiesK_sumN (f : Fin m × Fin p → ℕ) (x : Fin m × Fin p) :
    (copiesK m p).sumN f x + f x = ∑ j, f (x.1, j) := by
  have := (copiesK m p).sum_insert_neighborFinset f x
  rw [insert_neighborFinset_copiesK, copyOf, sum_map] at this
  change ∑ j, f (x.1, j) = f x + (copiesK m p).sumN f x at this
  omega

theorem copiesK_degree (x : Fin m × Fin p) : (copiesK m p).degree x = p - 1 := by
  have := copiesK_sumN (fun _ => 1) x
  simp only [sumN_one, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  omega

/-- η(m K_p) = p. -/
theorem copiesK_eta (hm : 0 < m) (hp : 0 < p) : (copiesK m p).eta = p := by
  apply le_antisymm
  · refine eta_le_of_labeling (f := fun x => x.2.val + 1) hp (fun x => ⟨Nat.succ_pos _, x.2.2⟩)
      fun x y hxy heq => ?_
    have h1 := copiesK_sumN (fun x => x.2.val + 1) x
    have h2 := copiesK_sumN (fun x => x.2.val + 1) y
    have h3 : x.2.val ≠ y.2.val := fun h => hxy.2 (Fin.ext h)
    rw [hxy.1] at h1
    omega
  · let x0 : Fin m × Fin p := (⟨0, hm⟩, ⟨0, hp⟩)
    have := observation_2 (G := copiesK m p) (copyOf x0) fun u hu v hv => by
      simp only [copyOf, mem_map, mem_univ, true_and] at hu hv
      obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      simp only [TrueTwins, insert_neighborFinset_copiesK, copyOf]
      rfl
    simpa [copyOf] using this

end copies

/-- Windmills: η(W_n^m) = η(m K_{n-1} ∨ K_1) = n - 1 for n ≥ 3, m ≥ 2. -/
theorem windmill {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) :
    ((copiesK m (n - 1)).joinK (Fin 1)).eta = n - 1 := by
  have hdeg : (copiesK m (n - 1)).maxDegree ≤ n - 2 :=
    maxDegree_le_of_forall_degree_le _ _ fun x => by rw [copiesK_degree]; omega
  have hcard : n - 2 + 2 ≤ m * (n - 1) := by
    have : 2 * (n - 1) ≤ m * (n - 1) := Nat.mul_le_mul_right _ hm
    omega
  rw [theorem_2_K1 (by simp only [Fintype.card_prod, Fintype.card_fin]; omega),
    copiesK_eta (by omega) (by omega)]

/-! ## Cycles and wheels -/

end SimpleGraph

namespace ACN

/-- Successor modulo n. -/
def csucc (n i : ℕ) : ℕ := if i + 1 = n then 0 else i + 1

/-- Predecessor modulo n. -/
def cpred (n i : ℕ) : ℕ := if i = 0 then n - 1 else i - 1

section cyc

variable {n : ℕ}

theorem csucc_lt (hn : 1 ≤ n) {i : ℕ} (hi : i < n) : csucc n i < n := by
  unfold csucc; split_omega

theorem cpred_lt (hn : 1 ≤ n) {i : ℕ} (hi : i < n) : cpred n i < n := by
  unfold cpred; split_omega

theorem cpred_csucc (i : ℕ) : cpred n (csucc n i) = i := by
  unfold csucc cpred; split_omega

theorem csucc_of_lt {i : ℕ} (h : i + 1 < n) : csucc n i = i + 1 := by
  unfold csucc; split_omega

theorem cpred_of_pos {i : ℕ} (h : 0 < i) : cpred n i = i - 1 := by
  unfold cpred; split_omega

theorem csucc_cpred {i : ℕ} (hi : i < n) : csucc n (cpred n i) = i := by
  unfold csucc cpred; split_omega

theorem csucc_ne_cpred (hn : 3 ≤ n) (i : ℕ) : csucc n i ≠ cpred n i := by
  unfold csucc cpred; split_omega

/-- ((n - b) + a) % n = 1 iff a is the successor of b modulo n. -/
theorem sub_mod_eq_one_iff (hn : 2 ≤ n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    (n - b + a) % n = 1 ↔ a = csucc n b := by
  unfold csucc
  rcases le_or_gt b a with h | h
  · rw [show n - b + a = (a - b) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    split_omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    split_omega

end cyc

end ACN

namespace SimpleGraph

open ACN

section cycles

variable {n : ℕ}

theorem cycleGraph_adj_iff (hn : 3 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔ j.val = csucc n i.val ∨ j.val = cpred n i.val := by
  rw [cycleGraph_adj', Fin.val_sub, Fin.val_sub, sub_mod_eq_one_iff (by omega) i.2 j.2,
    sub_mod_eq_one_iff (by omega) j.2 i.2]
  constructor
  · rintro (h | h)
    · right; rw [h, cpred_csucc]
    · left; exact h
  · rintro (h | h)
    · right; exact h
    · left; rw [h, csucc_cpred i.2]

/-- f(N(i)) in the cycle C_n. -/
theorem cycleGraph_sumN (hn : 3 ≤ n) (F : ℕ → ℕ) (i : Fin n) :
    (cycleGraph n).sumN (fun j => F j.val) i = F (csucc n i.val) + F (cpred n i.val) := by
  rw [sumN_fin (fun k => k = csucc n i.val ∨ k = cpred n i.val) i (cycleGraph_adj_iff hn i),
    sum_range_ite_or F (csucc_ne_cpred hn _)]
  simp only [csucc_lt (by omega) i.2, cpred_lt (by omega) i.2, ite_true]

theorem cycleGraph_degree (hn : 3 ≤ n) (i : Fin n) : (cycleGraph n).degree i = 2 := by
  rw [← sumN_one]
  exact cycleGraph_sumN hn (fun _ => 1) i

theorem cycleGraph_maxDegree (hn : 3 ≤ n) : (cycleGraph n).maxDegree ≤ 2 :=
  maxDegree_le_of_forall_degree_le _ _ fun i => (cycleGraph_degree hn i).le

/-- Even cycles are regular bipartite, so Corollary 1 applies. -/
theorem cycleGraph_eta_even (hn : 3 ≤ n) (heven : Even n) : (cycleGraph n).eta = 2 := by
  have hn2 : n % 2 = 0 := Nat.even_iff.1 heven
  refine corollary_1 (univ.filter fun j : Fin n => j.val % 2 = 0)
    (univ.filter fun j : Fin n => j.val % 2 = 1) ?_ ?_ ?_ ?_
    (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) ?_
  · rw [disjoint_filter]; intro j _ h; omega
  · intro v; simp only [mem_filter, mem_univ, true_and]; omega
  · intro u v huv
    simp only [mem_filter, mem_univ, true_and]
    rcases (cycleGraph_adj_iff hn u v).1 huv with h | h <;> rw [h] <;> simp only [csucc, cpred] <;>
      split_omega
  · intro u v; rw [cycleGraph_degree hn, cycleGraph_degree hn]
  · rw [cycleGraph_adj_iff hn]; left; simp [csucc]; omega

/-- The labeling of the appendix for odd cycles; the vertex k is the paper's v_{k+1}. -/
def p1F (k : ℕ) : ℕ :=
  if k = 0 then 2 else if k = 2 then 3 else if k ≤ 4 then 1 else if k % 2 = 1 then 1 else 3

/-- The sums f(N(v_{k+1})) of that labeling. -/
def p1S (n k : ℕ) : ℕ :=
  if k = 0 then (if n = 5 then 2 else 4) else if k = 1 then 5 else if k = 2 then 2
  else if k = 3 then 4 else if k = n - 1 then 3 else if k % 2 = 0 then 2
  else if k = 5 then 4 else 6

theorem p1F_big {j : ℕ} (h : 5 ≤ j) : p1F j = if j % 2 = 1 then 1 else 3 := by
  unfold p1F; split_omega

theorem p1S_big {k : ℕ} (h : 6 ≤ k) :
    p1S n k = if k = n - 1 then 3 else if k % 2 = 0 then 2 else 6 := by
  unfold p1S; split_omega

theorem p1_sum (hodd : n % 2 = 1) (h5 : 5 ≤ n) {k : ℕ} (hk : k < n) :
    p1F (csucc n k) + p1F (cpred n k) = p1S n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [csucc_of_lt (by omega), show cpred n 0 = n - 1 by simp [cpred]]
    unfold p1F p1S; split_omega
  · rw [cpred_of_pos hk0]
    rcases Nat.lt_or_ge (k + 1) n with hk1 | hk1
    · rw [csucc_of_lt hk1]
      rcases Nat.lt_or_ge k 6 with h | h
      · interval_cases k <;> simp only [p1F, p1S] <;> split_omega
      · rw [p1F_big (by omega), p1F_big (by omega), p1S_big h]; split_omega
    · have e1 : p1S n k = 3 := by unfold p1S; split_omega
      have e2 : p1F (k - 1) = 1 := by unfold p1F; split_omega
      rw [show csucc n k = 0 by simp [csucc]; omega, e1, e2]
      rfl

theorem p1_ne (hodd : n % 2 = 1) (h5 : 5 ≤ n) {k : ℕ} (hk : k < n) :
    p1S n k ≠ p1S n (csucc n k) := by
  rcases Nat.lt_or_ge (k + 1) n with hk1 | hk1
  · rw [csucc_of_lt hk1]
    unfold p1S; split_omega
  · rw [show csucc n k = 0 by simp [csucc]; omega]
    unfold p1S; split_omega

/-- Proposition 1: η(C_n) = 3 for odd n ≥ 5. -/
theorem proposition_1 (hodd : Odd n) (h5 : 5 ≤ n) : (cycleGraph n).eta = 3 := by
  have hn : n % 2 = 1 := Nat.odd_iff.1 hodd
  apply le_antisymm
  · refine eta_le_of_labeling (f := fun j => p1F j.val) (by norm_num)
      (fun j => by show 1 ≤ p1F j.val ∧ p1F j.val ≤ 3; unfold p1F; split_omega) fun i j hij => ?_
    rw [cycleGraph_sumN (by omega), cycleGraph_sumN (by omega), p1_sum hn h5 i.2, p1_sum hn h5 j.2]
    rcases (cycleGraph_adj_iff (by omega) i j).1 hij with h | h
    · rw [h]; exact p1_ne hn h5 i.2
    · have : i.val = csucc n j.val := by rw [h, csucc_cpred i.2]
      rw [this]; exact (p1_ne hn h5 j.2).symm
  · -- no additive 2-coloring: two consecutive arcs point the same way, since the orientation
    -- cannot alternate around an odd cycle; this forces a sum 2 and a sum 4 next to f(v) = 1
    -- and f(v) = 2 at once
    by_contra hlt
    push Not at hlt
    obtain ⟨f, hf⟩ := (cycleGraph n).eta_attained
    have hf2 := hf.mono (show (cycleGraph n).eta ≤ 2 by omega)
    let g : ℕ → ℕ := fun k => if h : k < n then f ⟨k, h⟩ else 0
    have hfg : f = fun j => g j.val := funext fun j => by simp [g, j.2]
    have lab : ∀ k < n, 1 ≤ g k ∧ g k ≤ 2 := fun k hk => by simpa [g, hk] using hf2.1 ⟨k, hk⟩
    let s : ℕ → ℕ := fun k => g (csucc n k) + g (cpred n k)
    have hs : ∀ k (hk : k < n), (cycleGraph n).sumN f ⟨k, hk⟩ = s k := fun k hk => by
      rw [hfg, cycleGraph_sumN (by omega)]
    have adj_ne : ∀ k < n, s k ≠ s (csucc n k) := by
      intro k hk
      have hk' := csucc_lt (by omega) hk
      rw [← hs k hk, ← hs _ hk']
      exact hf2.2 _ _ ((cycleGraph_adj_iff (by omega) _ _).2 (Or.inl rfl))
    let b : ℕ → Bool := fun k => decide (s k < s (csucc n k))
    have hex : ∃ k < n, b (cpred n k) = b k := by
      by_contra hno
      push Not at hno
      have step : ∀ k, k + 1 < n → b (k + 1) = !b k := by
        intro k hk
        have := hno (k + 1) hk
        rw [show cpred n (k + 1) = k by unfold cpred; split_omega] at this
        cases hb : b k <;> cases hb' : b (k + 1) <;> simp_all
      have par : ∀ k, k < n → b k = if k % 2 = 0 then b 0 else !b 0 := by
        intro k
        induction k with
        | zero => intro; simp
        | succ k ih =>
          intro hk
          rw [step k hk, ih (by omega)]
          split_ifs <;> first | omega | simp
      have h1 := par (n - 1) (by omega)
      rw [ite_eq_left (by omega)] at h1
      have h2 := hno 0 (by omega)
      rw [show cpred n 0 = n - 1 by simp [cpred], h1] at h2
      exact h2 rfl
    obtain ⟨k, hk, hb⟩ := hex
    have hp := cpred_lt (by omega) hk
    have hsk := csucc_lt (by omega) hk
    have e1 : csucc n (cpred n k) = k := csucc_cpred hk
    have e2 : cpred n (csucc n k) = k := cpred_csucc k
    have n1 := adj_ne _ hp
    have n2 := adj_ne _ hk
    rw [e1] at n1
    have hsp : s (cpred n k) = g k + g (cpred n (cpred n k)) := by simp only [s, e1]
    have hss : s (csucc n k) = g (csucc n (csucc n k)) + g k := by simp only [s, e2]
    have l1 := lab k hk
    have l2 := lab _ (cpred_lt (by omega) hp)
    have l3 := lab _ (csucc_lt (by omega) hsk)
    have l4 := lab _ (csucc_lt (by omega) hk)
    have l5 := lab _ hp
    have hsk_def : s k = g (csucc n k) + g (cpred n k) := rfl
    simp only [b, e1, decide_eq_decide] at hb
    omega

end cycles

/-- Wheels: η(W_n) = η(C_n ∨ K_1) = 2 for even n ≥ 4 and 3 for odd n ≥ 5. -/
theorem wheel {n : ℕ} (hn : 4 ≤ n) :
    ((cycleGraph n).joinK (Fin 1)).eta = if Even n then 2 else 3 := by
  rw [theorem_2_K1 (by have := cycleGraph_maxDegree (n := n) (by omega); simp; omega)]
  split_ifs with h
  · exact cycleGraph_eta_even (by omega) h
  · exact proposition_1 (Nat.not_even_iff_odd.1 h) (by
      have := Nat.not_even_iff_odd.1 h; rcases this with ⟨k, hk⟩; omega)

end SimpleGraph

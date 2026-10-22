/-
  Section 2: regular bipartite and complete multipartite graphs.
  Observation 1, Lemma 1, Corollary 1, Lemma 2 (ref. [6], Prop. 3, proved here) and Theorem 1.
-/
import ACN.Basics

set_option linter.unusedSectionVars false

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Observation 1, Lemma 1 and Corollary 1 -/

/-- Observation 1: η(G) = 1 iff adjacent vertices have different degrees. -/
theorem observation_1 : G.eta = 1 ↔ ∀ u v, G.Adj u v → G.degree u ≠ G.degree v := by
  constructor
  · intro h u v huv
    obtain ⟨f, hf⟩ := G.eta_attained
    rw [h] at hf
    have h1 : ∀ v, f v = 1 := fun v => le_antisymm (hf.1 v).2 (hf.1 v).1
    have hs : ∀ x, G.sumN f x = G.degree x := fun x => by rw [sumN_congr h1, sumN_one]
    simpa [hs] using hf.2 u v huv
  · intro h
    have : G.eta ≤ 1 := eta_le_of_labeling (f := fun _ => 1) one_pos (fun _ => ⟨le_rfl, le_rfl⟩)
      (fun u v huv => by simpa [sumN_one] using h u v huv)
    exact le_antisymm this G.eta_pos

theorem two_le_eta {u v : V} (huv : G.Adj u v) (hd : G.degree u = G.degree v) : 2 ≤ G.eta := by
  have h1 : G.eta ≠ 1 := fun h => observation_1.1 h u v huv hd
  have := G.eta_pos
  omega

/-- η(G) = 2 from η(G) ≤ 2 and an edge whose ends have equal degrees. -/
theorem eta_eq_two {u v : V} (h2 : G.eta ≤ 2) (huv : G.Adj u v) (hd : G.degree u = G.degree v) :
    G.eta = 2 :=
  le_antisymm h2 (two_le_eta huv hd)

open Classical in
/-- Lemma 1: a bipartite graph with stable sets `U` and `W` (the paper's U and V), where
d(u) < 2 d(v) for every v ∈ W and u ∈ N(v). Labeling: 2 on U, 1 on W. -/
theorem lemma_1 (U W : Finset V) (hdisj : Disjoint U W) (hcover : ∀ v, v ∈ U ∨ v ∈ W)
    (hbip : ∀ u v, G.Adj u v → (u ∈ U ↔ v ∈ W))
    (hdeg : ∀ v u, v ∈ W → G.Adj v u → G.degree u < 2 * G.degree v) :
    G.eta = if ∀ u v, G.Adj u v → G.degree u ≠ G.degree v then 1 else 2 := by
  let f : V → ℕ := fun v => if v ∈ U then 2 else 1
  have inW : ∀ v, v ∉ U → v ∈ W := fun v hv => (hcover v).resolve_left hv
  have notU : ∀ v, v ∈ W → v ∉ U := fun v hv hu => Finset.disjoint_left.1 hdisj hu hv
  have sU : ∀ u ∈ U, G.sumN f u = G.degree u := by
    intro u hu
    rw [← sumN_one]
    refine sum_congr rfl fun w hw => ?_
    have : w ∈ W := (hbip u w ((mem_neighborFinset _ _ _).1 hw)).1 hu
    simp [f, notU w this]
  have sW : ∀ v ∈ W, G.sumN f v = 2 * G.degree v := by
    intro v hv
    have : ∀ w ∈ G.neighborFinset v, f w = 2 := by
      intro w hw
      have hvw := (mem_neighborFinset _ _ _).1 hw
      have : w ∈ U := (hbip w v hvw.symm).2 hv
      simp [f, this]
    rw [sumN, sum_congr rfl this, sum_const, card_neighborFinset_eq_degree, smul_eq_mul,
      mul_comm]
  have edge : ∀ u v, u ∈ U → v ∈ W → G.Adj u v → G.sumN f u < G.sumN f v := by
    intro u v hu hv huv
    rw [sU u hu, sW v hv]
    exact hdeg v u hv huv.symm
  have le2 : G.eta ≤ 2 := by
    refine eta_le_of_labeling (f := f) two_pos (fun v => ?_) fun u v huv => ?_
    · by_cases hv : v ∈ U <;> simp [f, hv]
    · by_cases hu : u ∈ U
      · exact (edge u v hu ((hbip u v huv).1 hu) huv).ne
      · have hv : v ∈ U := by
          by_contra hv
          exact hu ((hbip u v huv).2 (inW v hv))
        exact (edge v u hv (inW u hu) huv.symm).ne'
  split_ifs with h
  · exact observation_1.2 h
  · push Not at h
    obtain ⟨u, v, huv, hd⟩ := h
    exact eta_eq_two le2 huv hd

/-- Corollary 1: a regular bipartite graph with at least one edge has η(G) = 2. -/
theorem corollary_1 (U W : Finset V) (hdisj : Disjoint U W) (hcover : ∀ v, v ∈ U ∨ v ∈ W)
    (hbip : ∀ u v, G.Adj u v → (u ∈ U ↔ v ∈ W)) (hreg : ∀ u v, G.degree u = G.degree v)
    {a b : V} (hab : G.Adj a b) : G.eta = 2 := by
  classical
  have hdeg : ∀ v u, v ∈ W → G.Adj v u → G.degree u < 2 * G.degree v := by
    intro v u _ hvu
    have : 0 < G.degree v := G.degree_pos_iff_exists_adj v |>.2 ⟨u, hvu⟩
    rw [hreg u v]
    omega
  rw [lemma_1 U W hdisj hcover hbip hdeg]
  split_ifs with h
  · exact absurd (hreg a b) (h a b hab)
  · rfl

end SimpleGraph

/-! ## The sequence s_i and the bound max ⌈s_i / |V_i|⌉

For part sizes `n : Fin r → ℕ` (the paper's |V_1|, …, |V_r|, indexed from 0),
s_{r-1} = n_{r-1} and s_i = max {1 + s_{i+1}, n_i}. -/

namespace ACN

variable {r : ℕ}

/-- The sequence s_i of Lemma 2 and Theorem 1. -/
def sseq (n : Fin r → ℕ) (i : Fin r) : ℕ :=
  if h : i.val + 1 < r then max (sseq n ⟨i.val + 1, h⟩ + 1) (n i) else n i
termination_by r - i.val

/-- The bound max_i ⌈s_i / n_i⌉. -/
def mpBound (n : Fin r → ℕ) : ℕ := univ.sup fun i => cdiv (sseq n i) (n i)

/-- Closed form, lower half: n_t + (t - i) ≤ s_i for t ≥ i. -/
theorem le_sseq (n : Fin r → ℕ) (i t : Fin r) (hit : i ≤ t) :
    n t + (t.val - i.val) ≤ sseq n i := by
  rw [sseq]
  split_ifs with h
  · rcases eq_or_lt_of_le hit with rfl | hlt
    · simp
    · rw [Fin.lt_def] at hlt
      have e : ((⟨i.val + 1, h⟩ : Fin r) : ℕ) = i.val + 1 := rfl
      have := le_sseq n ⟨i.val + 1, h⟩ t (by simp only [Fin.le_def]; omega)
      omega
  · have : t = i := Fin.ext (by have := t.2; simp only [Fin.le_def] at hit; omega)
    subst this; simp
termination_by r - i.val

/-- Closed form, upper half: s_i = n_t + (t - i) for some t ≥ i. -/
theorem exists_sseq_eq (n : Fin r → ℕ) (i : Fin r) :
    ∃ t, i ≤ t ∧ sseq n i = n t + (t.val - i.val) := by
  rw [sseq]
  split_ifs with h
  · obtain ⟨t, ht, he⟩ := exists_sseq_eq n ⟨i.val + 1, h⟩
    simp only [Fin.le_def] at ht
    have e : ((⟨i.val + 1, h⟩ : Fin r) : ℕ) = i.val + 1 := rfl
    rcases le_total (sseq n ⟨i.val + 1, h⟩ + 1) (n i) with hle | hle
    · exact ⟨i, le_rfl, by simp [max_eq_right hle]⟩
    · exact ⟨t, by simp only [Fin.le_def]; omega, by rw [max_eq_left hle, he]; omega⟩
  · exact ⟨i, le_rfl, by simp⟩
termination_by r - i.val

theorem sseq_le_iff (n : Fin r → ℕ) (i : Fin r) (x : ℕ) :
    sseq n i ≤ x ↔ ∀ t, i ≤ t → n t + (t.val - i.val) ≤ x := by
  constructor
  · exact fun h t ht => (le_sseq n i t ht).trans h
  · intro h
    obtain ⟨t, ht, he⟩ := exists_sseq_eq n i
    rw [he]; exact h t ht

theorem le_sseq_self (n : Fin r → ℕ) (i : Fin r) : n i ≤ sseq n i := by
  simpa using le_sseq n i i le_rfl

/-- The sequence s_i is strictly decreasing. -/
theorem sseq_lt (n : Fin r → ℕ) {i j : Fin r} (hij : i < j) : sseq n j < sseq n i := by
  obtain ⟨t, ht, he⟩ := exists_sseq_eq n j
  have := le_sseq n i t (hij.le.trans ht)
  rw [Fin.lt_def] at hij; rw [Fin.le_def] at ht
  omega

/-- The bound is at most k iff n_t + (t - i) ≤ k n_i whenever i ≤ t. -/
theorem mpBound_le_iff {n : Fin r → ℕ} (hpos : ∀ i, 0 < n i) (k : ℕ) :
    mpBound n ≤ k ↔ ∀ i t, i ≤ t → n t + (t.val - i.val) ≤ k * n i := by
  simp only [mpBound, Finset.sup_le_iff, mem_univ, true_implies, cdiv_le_iff (hpos _),
    sseq_le_iff]

theorem sseq_le_mpBound {n : Fin r → ℕ} (hpos : ∀ i, 0 < n i) (i : Fin r) :
    sseq n i ≤ mpBound n * n i :=
  (cdiv_le_iff (hpos i)).1 (le_sup (f := fun i => cdiv (sseq n i) (n i)) (mem_univ i))

theorem mpBound_pos {n : Fin r → ℕ} (hpos : ∀ i, 0 < n i) (hr : 0 < r) : 0 < mpBound n := by
  have h1 := le_sseq_self n ⟨0, hr⟩
  have h2 := sseq_le_mpBound hpos ⟨0, hr⟩
  have h3 := hpos ⟨0, hr⟩
  by_contra h
  simp only [not_lt, nonpos_iff_eq_zero] at h
  rw [h, zero_mul] at h2
  omega

/-- The ordering by decreasing size gives the least bound among all orderings of the same
sizes.  This replaces the second half of the paper's proof of Theorem 1, whose step "i ≥ j"
does not hold in general (see the README).  Take i ≤ t in the sorted order.  The parts with
sizes between n_t and n_i occupy at least t - i + 1 positions of the other order; if a and b
are the first and last of them, then b - a ≥ t - i, and the bound for the other order at
(a, b) gives the bound for the sorted order at (i, t). -/
theorem mpBound_sorted_le {n : Fin r → ℕ} (hanti : Antitone n) (hpos : ∀ i, 0 < n i)
    (σ : Equiv.Perm (Fin r)) : mpBound n ≤ mpBound (n ∘ σ) := by
  set k := mpBound (n ∘ σ)
  have H := (mpBound_le_iff (n := n ∘ σ) (fun i => hpos _) k).1 le_rfl
  rw [mpBound_le_iff hpos]
  intro i t hit
  let P : ℕ → Prop := fun x => n t ≤ x ∧ x ≤ n i
  let J := univ.filter fun j => P (n (σ j))
  have hcard : (univ.filter fun j => P (n j)).card = J.card :=
    (Finset.card_equiv σ (by intro j; simp [J])).symm
  have hIcc : Icc i t ⊆ univ.filter fun j => P (n j) := by
    intro j hj
    rw [mem_Icc] at hj
    simp only [mem_filter, mem_univ, true_and, P]
    exact ⟨hanti hj.2, hanti hj.1⟩
  have hJ : t.val + 1 - i.val ≤ J.card := by
    rw [← hcard, ← Fin.card_Icc]; exact card_le_card hIcc
  have hne : J.Nonempty := by
    rw [← Finset.card_pos]; rw [Fin.le_def] at hit; omega
  set a := J.min' hne
  set b := J.max' hne
  have ha : a ∈ J := J.min'_mem hne
  have hb : b ∈ J := J.max'_mem hne
  have hJab : J ⊆ Icc a b := fun j hj => mem_Icc.2 ⟨J.min'_le j hj, J.le_max' j hj⟩
  have hab : a ≤ b := J.min'_le b hb
  have hcardab : J.card ≤ b.val + 1 - a.val := by
    rw [← Fin.card_Icc]; exact card_le_card hJab
  simp only [mem_filter, mem_univ, true_and, J, P] at ha hb
  have h1 := H a b hab
  simp only [Function.comp] at h1
  have h2 : k * n (σ a) ≤ k * n i := Nat.mul_le_mul_left _ ha.2
  rw [Fin.le_def] at hit hab
  omega

/-- The paper's bound s_i ≤ |V_i| (r - i) (indices from 0), hence η(G) ≤ r. -/
theorem mpBound_le_card {n : Fin r → ℕ} (hanti : Antitone n) (hpos : ∀ i, 0 < n i) :
    mpBound n ≤ r := by
  rw [mpBound_le_iff hpos]
  intro i t hit
  have h1 : n t ≤ n i := hanti hit
  have h2 : 1 ≤ n i := hpos i
  have h3 : t.val - i.val ≤ (r - 1) * n i :=
    (show t.val - i.val ≤ r - 1 by have := t.2; omega).trans (Nat.le_mul_of_pos_right _ h2)
  have h4 : r * n i = n i + (r - 1) * n i := by
    have : r = (r - 1) + 1 := by have := t.2; omega
    conv_lhs => rw [this]
    ring
  omega

/-- The paper's formula, with real division and ceiling. -/
theorem mpBound_eq_ceil {n : Fin r → ℕ} (hpos : ∀ i, 0 < n i) :
    mpBound n = univ.sup fun i => ⌈(sseq n i : ℝ) / n i⌉₊ := by
  simp only [mpBound, cdiv_eq_ceil (hpos _)]

/-- A set of vertices can be labeled from [K] with any sum between its size and K times it. -/
theorem exists_labeling_sum {V : Type*} [DecidableEq V] (P : Finset V) {T K : ℕ}
    (h1 : P.card ≤ T) (h2 : T ≤ K * P.card) :
    ∃ g : V → ℕ, (∀ v ∈ P, 1 ≤ g v ∧ g v ≤ K) ∧ ∑ v ∈ P, g v = T := by
  induction P using Finset.induction_on generalizing T with
  | empty => exact ⟨fun _ => 0, by simp, by simp at h2 ⊢; omega⟩
  | insert x P hx ih =>
    rw [card_insert_of_notMem hx, mul_add, mul_one] at h2
    rw [card_insert_of_notMem hx] at h1
    have hP : P.card ≤ K * P.card := Nat.le_mul_of_pos_left _ (by
      rcases Nat.eq_zero_or_pos K with h | h
      · rw [h] at h2; omega
      · exact h)
    have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · rw [h] at h2; omega
      · exact h
    set a := min K (T - P.card)
    have ha1 : 1 ≤ a := by simp only [a]; omega
    have haK : a ≤ K := min_le_left _ _
    have hamin : a = K ∨ a = T - P.card := by simp only [a]; omega
    have hale : a ≤ T - P.card := min_le_right _ _
    obtain ⟨g, hg, hs⟩ := ih (T := T - a) (by omega) (by omega)
    refine ⟨Function.update g x a, fun v hv => ?_, ?_⟩
    · rcases mem_insert.1 hv with rfl | hvP
      · simp [ha1, haK]
      · have hne : v ≠ x := fun h => by subst h; exact hx hvP
        rw [Function.update_of_ne hne]; exact hg v hvP
    · have hsum : ∑ v ∈ P, Function.update g x a v = ∑ v ∈ P, g v :=
        sum_congr rfl fun v hv => Function.update_of_ne (fun h => by subst h; exact hx hv) _ _
      rw [sum_insert hx, Function.update_self, hsum, hs]
      omega

end ACN

/-! ## Complete multipartite graphs -/

namespace SimpleGraph

open ACN

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {r : ℕ}

variable (G) in
/-- `G` is complete multipartite with parts `Ps 0, …, Ps (r-1)` (the paper's V_1, …, V_r). -/
structure IsCompleteMultipartiteWith (Ps : Fin r → Finset V) : Prop where
  nonempty : ∀ i, (Ps i).Nonempty
  disjoint : ∀ i j, i ≠ j → Disjoint (Ps i) (Ps j)
  cover : ∀ v, ∃ i, v ∈ Ps i
  adj : ∀ u v, G.Adj u v ↔ ∃ i j, i ≠ j ∧ u ∈ Ps i ∧ v ∈ Ps j

/-- An orientation is monotone for the order `Ps` of the parts if all arcs go forward. -/
def IsMonotone (A : V → V → Prop) (Ps : Fin r → Finset V) : Prop :=
  ∀ u v, A u v → ∃ i j, i < j ∧ u ∈ Ps i ∧ v ∈ Ps j

namespace IsCompleteMultipartiteWith

variable {Ps : Fin r → Finset V} (cm : G.IsCompleteMultipartiteWith Ps)
include cm

theorem part_unique {u : V} {i j : Fin r} (hi : u ∈ Ps i) (hj : u ∈ Ps j) : i = j := by
  by_contra h
  exact Finset.disjoint_left.1 (cm.disjoint i j h) hi hj

theorem card_pos (i : Fin r) : 0 < (Ps i).card := Finset.card_pos.2 (cm.nonempty i)

theorem comp_perm (σ : Equiv.Perm (Fin r)) : G.IsCompleteMultipartiteWith (Ps ∘ σ) where
  nonempty i := cm.nonempty _
  disjoint i j h := cm.disjoint _ _ (σ.injective.ne h)
  cover v := by obtain ⟨i, hi⟩ := cm.cover v; exact ⟨σ.symm i, by simpa using hi⟩
  adj u v := by
    rw [cm.adj]
    constructor
    · rintro ⟨i, j, hij, hu, hv⟩
      exact ⟨σ.symm i, σ.symm j, by simpa using hij, by simpa using hu, by simpa using hv⟩
    · rintro ⟨i, j, hij, hu, hv⟩
      exact ⟨σ i, σ j, σ.injective.ne hij, hu, hv⟩

theorem neighborFinset_eq {w : V} {j : Fin r} (hw : w ∈ Ps j) :
    G.neighborFinset w = univ \ Ps j := by
  ext x
  rw [mem_neighborFinset, cm.adj, mem_sdiff]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨i, k, hik, hi, hk⟩ hx
    rw [cm.part_unique hi hw] at hik
    exact hik (cm.part_unique hx hk)
  · intro hx
    obtain ⟨k, hk⟩ := cm.cover x
    exact ⟨j, k, fun h => hx (h ▸ hk), hw, hk⟩

/-- f(N(w)) = f(V) - f(V_j) for w ∈ V_j: only the part sums matter. -/
theorem sumN_add {w : V} {j : Fin r} (hw : w ∈ Ps j) (f : V → ℕ) :
    G.sumN f w + ∑ x ∈ Ps j, f x = ∑ x, f x := by
  rw [sumN, cm.neighborFinset_eq hw]
  exact sum_sdiff (subset_univ _)

/-- The part of a vertex. -/
noncomputable def idx (v : V) : Fin r := (cm.cover v).choose

theorem mem_idx (v : V) : v ∈ Ps (cm.idx v) := (cm.cover v).choose_spec

theorem idx_eq {v : V} {i : Fin r} (hv : v ∈ Ps i) : cm.idx v = i :=
  cm.part_unique (cm.mem_idx v) hv

theorem adj_of_ne {u v : V} {i j : Fin r} (hij : i ≠ j) (hu : u ∈ Ps i) (hv : v ∈ Ps j) :
    G.Adj u v :=
  (cm.adj u v).2 ⟨i, j, hij, hu, hv⟩

theorem arc_forward {A : V → V → Prop} (hA : G.IsOrientation A) (hm : IsMonotone A Ps)
    {i j : Fin r} (hij : i < j) {u w : V} (hu : u ∈ Ps i) (hw : w ∈ Ps j) : A u w := by
  rcases hA.2.1 u w (cm.adj_of_ne hij.ne hu hw) with h | h
  · exact h
  · obtain ⟨i', j', hij', hw', hu'⟩ := hm w u h
    rw [cm.part_unique hw' hw, cm.part_unique hu' hu] at hij'
    exact absurd (hij.trans hij') (lt_irrefl _)

end IsCompleteMultipartiteWith

/-- An orientation with a strictly increasing rank is acyclic. -/
theorem not_transGen_of_rank {A : V → V → Prop} (rk : V → ℕ) (h : ∀ u v, A u v → rk u < rk v)
    (v : V) : ¬ Relation.TransGen A v v := by
  have : ∀ a b, Relation.TransGen A a b → rk a < rk b := by
    intro a b hab
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact fun hv => lt_irrefl _ (this v v hv)

/-- The orientation from earlier to later parts. -/
def forwardOrientation (Ps : Fin r → Finset V) (u v : V) : Prop :=
  ∃ i j, i < j ∧ u ∈ Ps i ∧ v ∈ Ps j

theorem forwardOrientation_spec {Ps : Fin r → Finset V} (cm : G.IsCompleteMultipartiteWith Ps) :
    G.IsAcyclicOrientation (forwardOrientation Ps) ∧ IsMonotone (forwardOrientation Ps) Ps := by
  have arc : ∀ u v, forwardOrientation Ps u v → (cm.idx u).val < (cm.idx v).val := by
    rintro u v ⟨i, j, hij, hu, hv⟩
    rw [cm.idx_eq hu, cm.idx_eq hv]; exact hij
  refine ⟨⟨⟨?_, ?_, ?_⟩, not_transGen_of_rank _ arc⟩, fun u v h => h⟩
  · rintro u v ⟨i, j, hij, hu, hv⟩
    exact cm.adj_of_ne hij.ne hu hv
  · intro u v huv
    obtain ⟨i, j, hij, hu, hv⟩ := (cm.adj u v).1 huv
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl ⟨i, j, h, hu, hv⟩
    · exact Or.inr ⟨j, i, h, hv, hu⟩
  · intro u v h h'
    exact lt_asymm (arc u v h) (arc v u h')

/-- One vertex from each part forms a clique, so χ(G) ≥ r. -/
theorem IsCompleteMultipartiteWith.card_le_chromaticNumber {Ps : Fin r → Finset V}
    (cm : G.IsCompleteMultipartiteWith Ps) : (r : ℕ∞) ≤ G.chromaticNumber := by
  let pick : Fin r → V := fun i => (cm.nonempty i).choose
  have hpick : ∀ i, pick i ∈ Ps i := fun i => (cm.nonempty i).choose_spec
  have inj : Function.Injective pick := fun i j h =>
    cm.part_unique (hpick i) (by rw [h]; exact hpick j)
  have hcl : G.IsClique ((univ.image pick : Finset V) : Set V) := by
    intro x hx y hy hxy
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact cm.adj_of_ne (fun h => hxy (by rw [h])) (hpick i) (hpick j)
  have := hcl.card_le_chromaticNumber
  rwa [card_image_of_injective _ inj, card_univ, Fintype.card_fin] at this

/-! ## Lemma 2 (ref. [6], Prop. 3)

In a complete multipartite graph, f(N(w)) = f(V) - f(V_j) for w ∈ V_j, so only the sums f(V_j)
of the parts matter. -/

variable {Ps : Fin r → Finset V}

/-- Lower bound: the part sums of a topological additive numbering decrease strictly along a
monotone orientation. -/
theorem lemma_2_lower (cm : G.IsCompleteMultipartiteWith Ps) {A : V → V → Prop}
    (hA : G.IsOrientation A) (hm : IsMonotone A Ps) {k : ℕ} {f : V → ℕ}
    (hf : G.TopAddNumbering A k f) : mpBound (fun i => (Ps i).card) ≤ k := by
  let t : Fin r → ℕ := fun i => ∑ x ∈ Ps i, f x
  have dec : ∀ i j, i < j → t j < t i := by
    intro i j hij
    obtain ⟨u, hu⟩ := cm.nonempty i
    obtain ⟨w, hw⟩ := cm.nonempty j
    have h1 := hf.2 u w (cm.arc_forward hA hm hij hu hw)
    have h2 := cm.sumN_add hu f
    have h3 := cm.sumN_add hw f
    simp only [t]; omega
  have gap : ∀ d (i j : Fin r), j.val = i.val + d → t j + d ≤ t i := by
    intro d
    induction d with
    | zero => intro i j h; rw [Fin.ext h]; simp
    | succ d ih =>
      intro i j h
      let j' : Fin r := ⟨i.val + d, by have := j.2; omega⟩
      have := ih i j' rfl
      have := dec j' j (by rw [Fin.lt_def]; simp only [j']; omega)
      omega
  have lab : ∀ i, (Ps i).card ≤ t i ∧ t i ≤ k * (Ps i).card := by
    intro i
    constructor
    · rw [card_eq_sum_ones]; exact sum_le_sum fun v _ => (hf.1 v).1
    · rw [mul_comm, ← smul_eq_mul, ← sum_const]; exact sum_le_sum fun v _ => (hf.1 v).2
  rw [mpBound_le_iff cm.card_pos]
  intro i j hij
  have := gap (j.val - i.val) i j (by rw [Fin.le_def] at hij; omega)
  have := lab i
  have := lab j
  omega

/-- Upper bound: label each part V_i with sum s_i. -/
theorem lemma_2_upper (cm : G.IsCompleteMultipartiteWith Ps) {A : V → V → Prop}
    (hm : IsMonotone A Ps) :
    ∃ f, G.TopAddNumbering A (mpBound fun i => (Ps i).card) f := by
  set n : Fin r → ℕ := fun i => (Ps i).card
  set K := mpBound n
  have hg : ∀ i, ∃ g : V → ℕ, (∀ v ∈ Ps i, 1 ≤ g v ∧ g v ≤ K) ∧ ∑ v ∈ Ps i, g v = sseq n i :=
    fun i => exists_labeling_sum (Ps i) (le_sseq_self n i) (sseq_le_mpBound cm.card_pos i)
  choose g hg using hg
  let f : V → ℕ := fun v => g (cm.idx v) v
  have fsum : ∀ i, ∑ v ∈ Ps i, f v = sseq n i := by
    intro i
    rw [← (hg i).2]
    exact sum_congr rfl fun v hv => by simp only [f, cm.idx_eq hv]
  refine ⟨f, fun v => (hg _).1 v (cm.mem_idx v), fun u w huw => ?_⟩
  obtain ⟨i, j, hij, hu, hw⟩ := hm u w huw
  have h1 := cm.sumN_add hu f
  have h2 := cm.sumN_add hw f
  have h3 := sseq_lt n hij
  rw [fsum] at h1 h2
  omega

/-- Lemma 2: for a monotone acyclic orientation, η_t(D) = max ⌈s_i / |V_i|⌉. -/
theorem lemma_2_value (cm : G.IsCompleteMultipartiteWith Ps) (hr : 0 < r) {A : V → V → Prop}
    (hA : G.IsAcyclicOrientation A) (hm : IsMonotone A Ps) :
    G.etaT A = mpBound fun i => (Ps i).card := by
  obtain ⟨f, hf⟩ := lemma_2_upper cm hm
  have hle := etaT_le (mpBound_pos cm.card_pos hr) hf
  have hne : G.etaT A ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  obtain ⟨k, g, hk, -, hg⟩ := etaT_attained hne
  refine le_antisymm hle ?_
  rw [hk]
  exact_mod_cast lemma_2_lower cm hA.1 hm hg

/-- Lemma 2: η_t(D) < ∞ iff the orientation is monotone for some ordering of the parts. -/
theorem lemma_2_finite_iff (cm : G.IsCompleteMultipartiteWith Ps) (hr : 0 < r)
    {A : V → V → Prop} (hA : G.IsAcyclicOrientation A) :
    G.etaT A ≠ ⊤ ↔ ∃ σ : Equiv.Perm (Fin r), IsMonotone A (Ps ∘ σ) := by
  constructor
  · intro h
    obtain ⟨k, f, -, -, hf⟩ := etaT_attained h
    let key : Fin r → ℕ := fun i => ∑ x ∈ Ps i, f x
    -- an arc from part i to part j means key j < key i
    have arc_key : ∀ u w i j, A u w → u ∈ Ps i → w ∈ Ps j → key j < key i := by
      intro u w i j huw hu hw
      have h1 := hf.2 u w huw
      have h2 := cm.sumN_add hu f
      have h3 := cm.sumN_add hw f
      simp only [key]; omega
    obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin r),
        Monotone ((fun i => OrderDual.toDual (key i)) ∘ σ) :=
      ⟨_, Tuple.monotone_sort fun i => OrderDual.toDual (key i)⟩
    refine ⟨σ, fun u w huw => ?_⟩
    obtain ⟨i, j, -, hu, hw⟩ := (cm.adj u w).1 (hA.1.1 u w huw)
    refine ⟨σ.symm i, σ.symm j, ?_, by simpa using hu, by simpa using hw⟩
    by_contra hle
    push Not at hle
    have := hmono hle
    simp only [Function.comp, Equiv.apply_symm_apply, OrderDual.toDual_le_toDual] at this
    exact absurd (arc_key u w i j huw hu hw) (not_lt.2 this)
  · rintro ⟨σ, hσ⟩
    rw [lemma_2_value (cm.comp_perm σ) hr hA hσ]
    simp

/-! ## Theorem 1 -/

/-- Theorem 1: for a complete r-partite graph with parts |V_1| ≥ … ≥ |V_r|,
η(G) = max ⌈s_i / |V_i|⌉ and η(G) ≤ r. -/
theorem theorem_1 (cm : G.IsCompleteMultipartiteWith Ps) (hr : 0 < r)
    (hsorted : Antitone fun i => (Ps i).card) :
    G.eta = mpBound (fun i => (Ps i).card) ∧ G.eta ≤ r := by
  set n : Fin r → ℕ := fun i => (Ps i).card
  have upper : G.eta ≤ mpBound n := by
    have hf := forwardOrientation_spec cm
    have := eta_le_etaT hf.1.1
    rw [lemma_2_value cm hr hf.1 hf.2] at this
    exact_mod_cast this
  have lower : (mpBound n : ℕ∞) ≤ G.eta := by
    rw [eta_eq_iInf_etaT]
    refine le_iInf₂ fun A hA => ?_
    by_cases h : G.etaT A = ⊤
    · simp [h]
    · obtain ⟨σ, hσ⟩ := (lemma_2_finite_iff cm hr hA).1 h
      rw [lemma_2_value (cm.comp_perm σ) hr hA hσ]
      exact_mod_cast mpBound_sorted_le hsorted cm.card_pos σ
  have eq : G.eta = mpBound n := le_antisymm upper (by exact_mod_cast lower)
  exact ⟨eq, eq ▸ mpBound_le_card hsorted cm.card_pos⟩

/-- The conjecture η(G) ≤ χ(G) holds for complete multipartite graphs. -/
theorem theorem_1_conjecture (cm : G.IsCompleteMultipartiteWith Ps) (hr : 0 < r)
    (hsorted : Antitone fun i => (Ps i).card) : (G.eta : ℕ∞) ≤ G.chromaticNumber :=
  (Nat.cast_le.2 (theorem_1 cm hr hsorted).2).trans cm.card_le_chromaticNumber

end SimpleGraph

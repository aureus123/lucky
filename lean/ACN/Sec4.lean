/-
  Section 4: split graphs.
  Theorem 3, the conjecture for split graphs, Proposition 2 (complete splits), Lemma 3 (ref. [6],
  Prop. 1, proved here) and Corollary 2.
-/
import ACN.Sec3

set_option linter.unusedSectionVars false

open Finset

namespace SimpleGraph

open ACN

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Cliques -/

theorem IsClique.adj_of_mem {Q : Finset V} (hQ : G.IsClique (Q : Set V)) {u v : V} (hu : u ∈ Q)
    (hv : v ∈ Q) (huv : u ≠ v) : G.Adj u v :=
  hQ (mem_coe.2 hu) (mem_coe.2 hv) huv

theorem IsClique.erase_subset_neighborFinset {Q : Finset V} (hQ : G.IsClique (Q : Set V))
    {q : V} (hq : q ∈ Q) : Q.erase q ⊆ G.neighborFinset q := fun x hx => by
  rw [mem_erase] at hx
  exact (mem_neighborFinset _ _ _).2 (hQ.adj_of_mem hq hx.2 hx.1.symm)

/-- |Q| ≤ d(q) + 1 for q in a clique Q. -/
theorem IsClique.card_le_degree {Q : Finset V} (hQ : G.IsClique (Q : Set V)) {q : V}
    (hq : q ∈ Q) : Q.card ≤ G.degree q + 1 := by
  have := card_le_card (hQ.erase_subset_neighborFinset hq)
  rw [card_erase_of_mem hq, card_neighborFinset_eq_degree] at this
  omega

/-! ## Theorem 3: an upper bound for split graphs -/

variable (G) in
/-- A split graph with clique `Q` and stable set `S`; `Q` is maximal, i.e. no vertex of `S` is
adjacent to all of `Q`. -/
structure IsSplitWith (Q S : Finset V) : Prop where
  cover : ∀ v, v ∈ Q ∨ v ∈ S
  disjoint : Disjoint Q S
  clique : G.IsClique (Q : Set V)
  stable : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b
  maximal : ∀ v ∈ S, ∃ u ∈ Q, ¬ G.Adj u v

namespace IsSplitWith

variable {Q S : Finset V} (sp : G.IsSplitWith Q S)
include sp

theorem not_mem_S {v : V} (hv : v ∈ Q) : v ∉ S := fun h => Finset.disjoint_left.1 sp.disjoint hv h

theorem neighborFinset_S {v : V} (hv : v ∈ S) : G.neighborFinset v ⊆ Q := fun w hw => by
  rcases sp.cover w with h | h
  · exact h
  · exact absurd ((mem_neighborFinset _ _ _).1 hw) (sp.stable v hv w h)

/-- N(u) = (Q - u) ∪ (N(u) ∩ S) for u ∈ Q. -/
theorem neighborFinset_Q {u : V} (hu : u ∈ Q) :
    G.neighborFinset u = Q.erase u ∪ (G.neighborFinset u ∩ S) := by
  ext x
  simp only [mem_union, mem_erase, mem_inter]
  constructor
  · intro hx
    rcases sp.cover x with h | h
    · exact Or.inl ⟨fun hxu => G.irrefl (hxu ▸ (mem_neighborFinset _ _ _).1 hx), h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hxu, hx⟩ | ⟨hx, -⟩)
    · exact (mem_neighborFinset _ _ _).2 (sp.clique.adj_of_mem hu hx (Ne.symm hxu))
    · exact hx

theorem disjoint_erase_inter (u : V) : Disjoint (Q.erase u) (G.neighborFinset u ∩ S) :=
  Finset.disjoint_left.2 fun _ hx hx' =>
    sp.not_mem_S (mem_erase.1 hx).2 (mem_inter.1 hx').2

/-- d(u) + 1 = |Q| + r(u) for u ∈ Q, where r(u) = |N(u) ∩ S|. -/
theorem degree_Q {u : V} (hu : u ∈ Q) :
    G.degree u + 1 = Q.card + (G.neighborFinset u ∩ S).card := by
  have hc : (G.neighborFinset u).card = (Q.erase u).card + (G.neighborFinset u ∩ S).card := by
    rw [← card_union_of_disjoint (sp.disjoint_erase_inter u), ← sp.neighborFinset_Q hu]
  rw [← card_neighborFinset_eq_degree, hc, card_erase_of_mem hu]
  have := card_pos.2 ⟨u, hu⟩
  omega

/-- f(N(u)) + f(u) = f(Q) + c r(u) for u ∈ Q, when f = c on S. -/
theorem sumN_Q {u : V} (hu : u ∈ Q) {f : V → ℕ} {c : ℕ} (hc : ∀ w ∈ S, f w = c) :
    G.sumN f u + f u = ∑ x ∈ Q, f x + c * (G.neighborFinset u ∩ S).card := by
  have h1 : G.sumN f u = ∑ x ∈ Q.erase u, f x + ∑ x ∈ G.neighborFinset u ∩ S, f x := by
    rw [← sum_union (sp.disjoint_erase_inter u), ← sp.neighborFinset_Q hu, sumN]
  rw [h1, sum_congr rfl fun w hw => hc w (mem_inter.1 hw).2, sum_const, smul_eq_mul, mul_comm,
    ← sum_erase_add _ _ hu]
  omega

/-- Theorem 3: if T ⊆ Q and the degrees in T are pairwise distinct, then
η(G) ≤ |Q| - |T| + 1.  Labeling: 1, …, q - t on Q - T, and q - t + 1 on T ∪ S.  (The paper
assumes T ≠ ∅; the proof does not need it.) -/
theorem theorem_3 {T : Finset V} (hTQ : T ⊆ Q)
    (hdeg : Set.InjOn (fun v => G.degree v) (T : Set V)) : G.eta ≤ Q.card - T.card + 1 := by
  set c := Q.card - T.card + 1
  have hcard : (Q \ T).card = Q.card - T.card := card_sdiff_of_subset hTQ
  let e := (Q \ T).equivFin
  let f : V → ℕ := fun x => if hx : x ∈ Q \ T then (e ⟨x, hx⟩ : ℕ) + 1 else c
  have fQT : ∀ x (hx : x ∈ Q \ T), f x = (e ⟨x, hx⟩ : ℕ) + 1 := fun x hx => dite_eq_left hx
  have fc : ∀ x, x ∉ Q \ T → f x = c := fun x hx => dite_eq_right hx
  have flt : ∀ x ∈ Q \ T, f x < c := fun x hx => by
    rw [fQT x hx]; have := (e ⟨x, hx⟩).2; omega
  have flab : ∀ x, 1 ≤ f x ∧ f x ≤ c := by
    intro x
    by_cases hx : x ∈ Q \ T
    · rw [fQT x hx]; have := flt x hx; omega
    · rw [fc x hx]; omega
  have fS : ∀ w ∈ S, f w = c := fun w hw => fc w fun h => sp.not_mem_S (mem_sdiff.1 h).1 hw
  have sQ : ∀ u ∈ Q, G.sumN f u + f u = ∑ x ∈ Q, f x + c * (G.neighborFinset u ∩ S).card :=
    fun u hu => sp.sumN_Q hu fS
  have sS : ∀ v ∈ S, G.sumN f v + 1 ≤ ∑ x ∈ Q, f x := by
    intro v hv
    obtain ⟨u0, hu0, hnadj⟩ := sp.maximal v hv
    have hsub : G.neighborFinset v ⊆ Q.erase u0 := fun w hw =>
      mem_erase.2 ⟨fun h => hnadj (h ▸ ((mem_neighborFinset _ _ _).1 hw).symm),
        sp.neighborFinset_S hv hw⟩
    have h1 : G.sumN f v ≤ ∑ x ∈ Q.erase u0, f x := sum_le_sum_of_subset hsub
    have h2 := sum_erase_add Q f hu0
    have := (flab u0).1
    omega
  -- an edge between Q and S goes from S to Q
  have QS : ∀ u v, u ∈ Q → v ∈ S → G.Adj u v → G.sumN f v < G.sumN f u := by
    intro u v hu hv huv
    have hr : 1 ≤ (G.neighborFinset u ∩ S).card :=
      card_pos.2 ⟨v, mem_inter.2 ⟨(mem_neighborFinset _ _ _).2 huv, hv⟩⟩
    have hcr : c ≤ c * (G.neighborFinset u ∩ S).card := Nat.le_mul_of_pos_right _ hr
    have := sQ u hu
    have := sS v hv
    have := (flab u).2
    omega
  refine eta_le_of_labeling (f := f) (by omega) flab fun x y hxy heq => ?_
  rcases sp.cover x with hx | hx <;> rcases sp.cover y with hy | hy
  · -- both in Q
    have hne : x ≠ y := G.ne_of_adj hxy
    have h1 := sQ x hx
    have h2 := sQ y hy
    set rx := (G.neighborFinset x ∩ S).card
    set ry := (G.neighborFinset y ∩ S).card
    rcases lt_trichotomy rx ry with hr | hr | hr
    · have : c * rx + c ≤ c * ry := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
      have := flab x; have := flab y
      omega
    · -- equal sums and equal r: equal labels, so both are in T and have equal degrees
      have hf : f x = f y := by rw [hr] at h1; omega
      have hxT : x ∈ T ∧ y ∈ T := by
        by_contra hnot
        rw [not_and_or] at hnot
        by_cases hxQT : x ∈ Q \ T
        · by_cases hyQT : y ∈ Q \ T
          · rw [fQT x hxQT, fQT y hyQT] at hf
            have := e.injective (a₁ := ⟨x, hxQT⟩) (a₂ := ⟨y, hyQT⟩) (Fin.ext (by omega))
            exact hne (congrArg Subtype.val this)
          · rw [fc y hyQT] at hf; have := flt x hxQT; omega
        · have hxT : x ∈ T := by simp only [mem_sdiff, not_and, not_not] at hxQT; exact hxQT hx
          have hyQT : y ∈ Q \ T := mem_sdiff.2 ⟨hy, hnot.resolve_left (not_not.2 hxT)⟩
          rw [fc x hxQT] at hf; have := flt y hyQT; omega
      have hd : G.degree x = G.degree y := by
        have := sp.degree_Q hx; have := sp.degree_Q hy; omega
      exact hne (hdeg (mem_coe.2 hxT.1) (mem_coe.2 hxT.2) hd)
    · have : c * ry + c ≤ c * rx := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
      have := flab x; have := flab y
      omega
  · exact absurd heq (QS x y hx hy hxy).ne'
  · exact absurd heq (QS y x hy hx hxy.symm).ne
  · exact sp.stable x hx y hy hxy

/-- With |T| = 1: η(G) ≤ |Q| ≤ χ(G), so the conjecture holds for split graphs. -/
theorem theorem_3_conjecture [Nonempty V] :
    G.eta ≤ Q.card ∧ (G.eta : ℕ∞) ≤ G.chromaticNumber := by
  obtain ⟨u, hu⟩ : Q.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    rcases sp.cover v with h | h
    · exact ⟨v, h⟩
    · obtain ⟨u, hu, -⟩ := sp.maximal v h; exact ⟨u, hu⟩
  have h := sp.theorem_3 (T := {u}) (singleton_subset_iff.2 hu) (by simp)
  rw [card_singleton, Nat.sub_add_cancel (card_pos.2 ⟨u, hu⟩)] at h
  exact ⟨h, (Nat.cast_le.2 h).trans sp.clique.card_le_chromaticNumber⟩

end IsSplitWith

/-- The conjecture holds for every split graph: a split partition can be made maximal by moving
one vertex from S to Q. -/
theorem split_graph_conjecture [Nonempty V] {Q S : Finset V} (cover : ∀ v, v ∈ Q ∨ v ∈ S)
    (disj : Disjoint Q S) (cl : G.IsClique (Q : Set V)) (st : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) :
    (G.eta : ℕ∞) ≤ G.chromaticNumber := by
  by_cases hmax : ∀ v ∈ S, ∃ u ∈ Q, ¬ G.Adj u v
  · exact (IsSplitWith.theorem_3_conjecture ⟨cover, disj, cl, st, hmax⟩).2
  · push Not at hmax
    obtain ⟨v, hv, hall⟩ := hmax
    have sp : G.IsSplitWith (insert v Q) (S.erase v) := by
      refine ⟨fun w => ?_, ?_, ?_, fun a ha b hb => st a (mem_of_mem_erase ha) b
        (mem_of_mem_erase hb), fun w hw => ⟨v, mem_insert_self v Q, st v hv w
        (mem_of_mem_erase hw)⟩⟩
      · by_cases h : w = v
        · exact Or.inl (h ▸ mem_insert_self v Q)
        · rcases cover w with h' | h'
          · exact Or.inl (mem_insert_of_mem h')
          · exact Or.inr (mem_erase.2 ⟨h, h'⟩)
      · rw [Finset.disjoint_insert_left]
        exact ⟨fun h => (mem_erase.1 h).1 rfl, Finset.disjoint_of_subset_right (erase_subset v S) disj⟩
      · rw [coe_insert]
        exact cl.insert fun u hu _ => (hall u hu).symm
    exact sp.theorem_3_conjecture.2

/-! ## Proposition 2: complete splits -/

/-- Proposition 2: a complete split graph (a clique Q' with |Q'| ≥ 1, a stable set S' with
|S'| ≥ 2, and all edges between them) has η(G) = |Q'|. -/
theorem proposition_2 {Q S : Finset V} (cover : ∀ v, v ∈ Q ∨ v ∈ S) (disj : Disjoint Q S)
    (cl : G.IsClique (Q : Set V)) (st : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (full : ∀ u ∈ Q, ∀ v ∈ S, G.Adj u v) (hQ : Q.Nonempty) (hS : 2 ≤ S.card) :
    G.eta = Q.card := by
  obtain ⟨u, hu⟩ := hQ
  obtain ⟨v, hv⟩ : S.Nonempty := card_pos.1 (by omega)
  have hvQ : v ∉ Q := fun h => Finset.disjoint_left.1 disj h hv
  have hNu : G.neighborFinset u = Q.erase u ∪ S := by
    ext x
    simp only [mem_neighborFinset, mem_union, mem_erase]
    constructor
    · intro h
      rcases cover x with hx | hx
      · exact Or.inl ⟨fun hxu => G.irrefl (hxu ▸ h), hx⟩
      · exact Or.inr hx
    · rintro (⟨hxu, hx⟩ | hx)
      · exact cl.adj_of_mem hu hx (Ne.symm hxu)
      · exact full u hu x hx
  have hNv : G.neighborFinset v = Q := by
    ext x
    rw [mem_neighborFinset]
    constructor
    · intro h
      rcases cover x with hx | hx
      · exact hx
      · exact absurd h (st v hv x hx)
    · intro hx; exact (full x hx v hv).symm
  apply le_antisymm
  · have sp : G.IsSplitWith (insert v Q) (S.erase v) := by
      refine ⟨fun w => ?_, ?_, ?_, fun a ha b hb => st a (mem_of_mem_erase ha) b
        (mem_of_mem_erase hb), fun w hw => ⟨v, mem_insert_self v Q, st v hv w
        (mem_of_mem_erase hw)⟩⟩
      · by_cases h : w = v
        · exact Or.inl (h ▸ mem_insert_self v Q)
        · rcases cover w with h' | h'
          · exact Or.inl (mem_insert_of_mem h')
          · exact Or.inr (mem_erase.2 ⟨h, h'⟩)
      · rw [Finset.disjoint_insert_left]
        exact ⟨fun h => (mem_erase.1 h).1 rfl, Finset.disjoint_of_subset_right (erase_subset v S) disj⟩
      · rw [coe_insert]
        exact cl.insert fun w hw _ => (full w hw v hv).symm
    have hdu : G.degree u = Q.card - 1 + S.card := by
      rw [← card_neighborFinset_eq_degree, hNu,
        card_union_of_disjoint (Finset.disjoint_of_subset_left (erase_subset u Q) disj),
        card_erase_of_mem hu]
    have hdv : G.degree v = Q.card := by rw [← card_neighborFinset_eq_degree, hNv]
    have huv : u ≠ v := fun h => hvQ (h ▸ hu)
    have hQpos := card_pos.2 ⟨u, hu⟩
    have h := sp.theorem_3 (T := {u, v}) (by
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact mem_insert_of_mem hu
        · rw [mem_singleton.1 hx]; exact mem_insert_self v Q)
      (by
        intro x hx y hy hxy
        simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · rfl
        · simp only at hxy; rw [hdu, hdv] at hxy; omega
        · simp only at hxy; rw [hdu, hdv] at hxy; omega
        · rfl)
    rw [card_insert_of_notMem hvQ, card_pair huv] at h
    omega
  · -- the vertices of Q are pairwise true twins: N[w] = V for w ∈ Q
    have hN : ∀ w ∈ Q, insert w (G.neighborFinset w) = univ := by
      intro w hw
      ext x
      simp only [mem_insert, mem_neighborFinset, mem_univ, iff_true]
      by_cases hxw : x = w
      · exact Or.inl hxw
      · rcases cover x with hx | hx
        · exact Or.inr (cl.adj_of_mem hw hx (Ne.symm hxw))
        · exact Or.inr (full w hw x hx)
    exact observation_2 Q fun a ha b hb => by simp only [TrueTwins, hN a ha, hN b hb]

/-! ## Lemma 3 (ref. [6], Prop. 1) and Corollary 2

For a clique Q of an acyclic orientation, q_F and q_L are the source and the sink of Q, i.e. the
smallest and largest vertices of Q in a topological order. -/

/-- Lemma 3: η_t(D) ≥ ⌈(d(q_F) + 1) / (d(q_L) - |Q| + 2)⌉.  The proof of [6]: for a topological
additive k-numbering f and q ∈ Q, let Y_q = f(N(q) - Q) - f(q).  Then f(N(q)) = f(Q) + Y_q, so the
Y_q are |Q| distinct integers between Y_{q_F} ≥ |N(q_F) - Q| - k and Y_{q_L} ≤ k |N(q_L) - Q| - 1. -/
theorem lemma_3 {A : V → V → Prop} (hA : G.IsAcyclicOrientation A) {Q : Finset V}
    (cl : G.IsClique (Q : Set V)) {qF qL : V} (hqF : qF ∈ Q) (hqL : qL ∈ Q)
    (src : ∀ q ∈ Q, q ≠ qF → A qF q) (snk : ∀ q ∈ Q, q ≠ qL → A q qL) :
    (cdiv (G.degree qF + 1) (G.degree qL + 2 - Q.card) : ℕ∞) ≤ G.etaT A := by
  by_cases htop : G.etaT A = ⊤
  · simp [htop]
  obtain ⟨k, f, hk, -, hf⟩ := etaT_attained htop
  rw [hk]
  apply Nat.cast_le.2
  let Y : V → ℤ := fun q => (∑ x ∈ G.neighborFinset q \ Q, f x : ℕ) - (f q : ℤ)
  have hNQ : ∀ q ∈ Q, G.neighborFinset q ∩ Q = Q.erase q := by
    intro q hq
    ext x
    simp only [mem_inter, mem_erase, mem_neighborFinset]
    constructor
    · rintro ⟨h, hx⟩; exact ⟨fun hxq => G.irrefl (hxq ▸ h), hx⟩
    · rintro ⟨hxq, hx⟩; exact ⟨cl.adj_of_mem hq hx (Ne.symm hxq), hx⟩
  have SY : ∀ q ∈ Q, (G.sumN f q : ℤ) = (∑ x ∈ Q, f x : ℕ) + Y q := by
    intro q hq
    have h1 : G.sumN f q = ∑ x ∈ G.neighborFinset q ∩ Q, f x +
        ∑ x ∈ G.neighborFinset q \ Q, f x := (sum_inter_add_sum_sdiff _ _ _).symm
    rw [hNQ q hq] at h1
    have h2 := sum_erase_add Q f hq
    simp only [Y]
    omega
  have Ylt : ∀ u ∈ Q, ∀ v ∈ Q, A u v → Y u < Y v := by
    intro u hu v hv huv
    have := hf.2 u v huv
    have := SY u hu
    have := SY v hv
    omega
  have inj : Set.InjOn Y (Q : Set V) := by
    intro u hu v hv h
    by_contra hne
    rcases hA.1.2.1 u v (cl.adj_of_mem hu hv hne) with h' | h'
    · exact absurd h (Ylt u hu v hv h').ne
    · exact absurd h (Ylt v hv u hu h').ne'
  have range : Q.image Y ⊆ Icc (Y qF) (Y qL) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hy
    rw [mem_Icc]
    constructor
    · by_cases h : q = qF
      · rw [h]
      · exact (Ylt qF hqF q hq (src q hq h)).le
    · by_cases h : q = qL
      · rw [h]
      · exact (Ylt q hq qL hqL (snk q hq h)).le
  have hspread : (Q.card : ℤ) ≤ Y qL - Y qF + 1 := by
    have := card_le_card range
    rw [card_image_of_injOn inj, Int.card_Icc] at this
    have := card_pos.2 ⟨qF, hqF⟩
    omega
  have lab := hf.1
  -- |N(q) - Q| + |Q| = d(q) + 1
  have cardNQ : ∀ q ∈ Q, (G.neighborFinset q \ Q).card + Q.card = G.degree q + 1 := by
    intro q hq
    have h1 := card_sdiff_add_card_inter (G.neighborFinset q) Q
    rw [hNQ q hq, card_erase_of_mem hq, card_neighborFinset_eq_degree] at h1
    have := card_pos.2 ⟨q, hq⟩
    omega
  set a := (G.neighborFinset qF \ Q).card
  set c := (G.neighborFinset qL \ Q).card
  have hYF : (a : ℤ) - k ≤ Y qF := by
    have h1 : a ≤ ∑ x ∈ G.neighborFinset qF \ Q, f x :=
      (card_eq_sum_ones _).trans_le (sum_le_sum fun x _ => (lab x).1)
    have := (lab qF).2
    simp only [Y]
    omega
  have hYL : Y qL ≤ (k * c : ℕ) - 1 := by
    have h1 : ∑ x ∈ G.neighborFinset qL \ Q, f x ≤ k * c :=
      (sum_le_sum fun x _ => (lab x).2).trans_eq (by rw [sum_const, smul_eq_mul, mul_comm])
    have := (lab qL).1
    simp only [Y]
    omega
  have h1 := cardNQ qF hqF
  have h2 := cardNQ qL hqL
  have key : G.degree qF + 1 ≤ k * (c + 1) := by
    rw [Nat.mul_succ]
    have : ((G.degree qF + 1 : ℕ) : ℤ) ≤ (k * c : ℕ) + k := by push_cast; omega
    exact_mod_cast this
  rw [show G.degree qL + 2 - Q.card = c + 1 by omega]
  exact (cdiv_le_iff (by omega)).2 key

/-- Corollary 2: if d₁, d₂ are the smallest and largest degrees of a clique Q, then
η(G) ≥ ⌈(d₁ + 1) / (d₂ - |Q| + 2)⌉. -/
theorem corollary_2 {Q : Finset V} (cl : G.IsClique (Q : Set V)) (hQ : Q.Nonempty) :
    cdiv (Q.inf' hQ (fun v => G.degree v) + 1) (Q.sup' hQ (fun v => G.degree v) + 2 - Q.card) ≤
      G.eta := by
  obtain ⟨f, hf⟩ := G.eta_attained
  obtain ⟨qF, hqF, hmin⟩ := Q.exists_min_image (G.sumN f) hQ
  obtain ⟨qL, hqL, hmax⟩ := Q.exists_max_image (G.sumN f) hQ
  have hne : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → G.sumN f u ≠ G.sumN f v :=
    fun u hu v hv huv => hf.2 u v (cl.adj_of_mem hu hv huv)
  have src : ∀ q ∈ Q, q ≠ qF → G.inducedOrientation f qF q := fun q hq h =>
    ⟨cl.adj_of_mem hqF hq (Ne.symm h), lt_of_le_of_ne (hmin q hq) (hne qF hqF q hq (Ne.symm h))⟩
  have snk : ∀ q ∈ Q, q ≠ qL → G.inducedOrientation f q qL := fun q hq h =>
    ⟨cl.adj_of_mem hq hqL h, lt_of_le_of_ne (hmax q hq) (hne q hq qL hqL h)⟩
  have h3 := lemma_3 (inducedOrientation_acyclic hf) cl hqF hqL src snk
  have h4 := etaT_le G.eta_pos (inducedOrientation_topAddNumbering hf)
  have h5 : cdiv (G.degree qF + 1) (G.degree qL + 2 - Q.card) ≤ G.eta := by
    exact_mod_cast h3.trans h4
  refine le_trans (cdiv_mono ?_ ?_ ?_) h5
  · have := inf'_le (fun v => G.degree v) hqF
    omega
  · have := cl.card_le_degree hqL; omega
  · have := le_sup' (fun v => G.degree v) hqL
    omega

/-- Corollary 2 when all the vertices of the clique have the same degree d. -/
theorem corollary_2_of_degree_eq {Q : Finset V} (cl : G.IsClique (Q : Set V)) (hQ : Q.Nonempty)
    {d : ℕ} (hd : ∀ v ∈ Q, G.degree v = d) : cdiv (d + 1) (d + 2 - Q.card) ≤ G.eta := by
  obtain ⟨v, hv⟩ := hQ
  have h1 : Q.inf' ⟨v, hv⟩ (fun v => G.degree v) = d :=
    le_antisymm ((inf'_le _ hv).trans (hd v hv).le) (le_inf' _ _ fun w hw => (hd w hw).ge)
  have h2 : Q.sup' ⟨v, hv⟩ (fun v => G.degree v) = d :=
    le_antisymm (sup'_le _ _ fun w hw => (hd w hw).le) ((hd v hv).ge.trans (le_sup' (fun v => G.degree v) hv))
  have := corollary_2 cl ⟨v, hv⟩
  rwa [h1, h2] at this

end SimpleGraph

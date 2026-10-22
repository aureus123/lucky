/-
  Section 3: join with complete graphs.
  Observation 2 (true twins), Theorem 2 (η(G ∨ K_q) = max {η(G), q}), χ(G ∨ K_q) ≥ χ(G) + q,
  and the conjecture for G ∨ K_q.
-/
import ACN.Sec2

set_option linter.unusedSectionVars false

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Observation 2: true twins -/

theorem TrueTwins.adj {u v : V} (h : G.TrueTwins u v) (huv : u ≠ v) : G.Adj u v := by
  have : v ∈ insert u (G.neighborFinset u) := by rw [TrueTwins] at h; rw [h]; exact mem_insert_self _ _
  rcases mem_insert.1 this with h' | h'
  · exact absurd h'.symm huv
  · exact (mem_neighborFinset _ _ _).1 h'

/-- An additive coloring gives different labels to true twins. -/
theorem AdditiveColoring.ne_of_trueTwins {k : ℕ} {f : V → ℕ} (hf : G.AdditiveColoring k f)
    {u v : V} (h : G.TrueTwins u v) (huv : u ≠ v) : f u ≠ f v := by
  intro heq
  have h1 := G.sum_insert_neighborFinset f u
  have h2 := G.sum_insert_neighborFinset f v
  rw [TrueTwins] at h
  rw [h] at h1
  exact hf.2 u v (TrueTwins.adj h huv) (by omega)

/-- Observation 2: if the vertices of `T` are pairwise true twins, then η(G) ≥ |T|. -/
theorem observation_2 (T : Finset V) (hT : ∀ u ∈ T, ∀ v ∈ T, G.TrueTwins u v) :
    T.card ≤ G.eta := by
  refine le_eta fun k f _ hf => ?_
  have inj : Set.InjOn f T := fun u hu v hv h => by
    by_contra hne; exact hf.ne_of_trueTwins (hT u hu v hv) hne h
  calc T.card = (T.image f).card := (card_image_of_injOn inj).symm
    _ ≤ (Icc 1 k).card := card_le_card fun x hx => by
        obtain ⟨u, -, rfl⟩ := mem_image.1 hx; exact mem_Icc.2 (hf.1 u)
    _ = k := by simp

/-! ## The join G ∨ H -/

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The join G ∨ H: the disjoint union of G and H plus all edges between them. -/
def join (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inr a, .inr b => H.Adj a b
    | _, _ => True
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp only at h ⊢ <;> exact h.symm⟩
  loopless := ⟨by rintro (a | a) h <;> simp only at h; exacts [G.irrefl h, H.irrefl h]⟩

section join

variable (H : SimpleGraph W)

@[simp] theorem join_adj_inl_inl (a b : V) : (G.join H).Adj (.inl a) (.inl b) ↔ G.Adj a b := .rfl
@[simp] theorem join_adj_inr_inr (a b : W) : (G.join H).Adj (.inr a) (.inr b) ↔ H.Adj a b := .rfl
@[simp] theorem join_adj_inl_inr (a : V) (b : W) : (G.join H).Adj (.inl a) (.inr b) := trivial
@[simp] theorem join_adj_inr_inl (a : W) (b : V) : (G.join H).Adj (.inr a) (.inl b) := trivial

instance [DecidableRel H.Adj] : DecidableRel (G.join H).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inr a, .inr b => inferInstanceAs (Decidable (H.Adj a b))
  | .inl _, .inr _ => isTrue trivial
  | .inr _, .inl _ => isTrue trivial

end join

/-! ## Theorem 2: η(G ∨ K_q) = max {η(G), q} for q ≤ n - Δ - 1

The complete graph K_q is `⊤ : SimpleGraph W` with q = |W|. -/

section theorem2

/-- G ∨ K_q, with K_q the complete graph on `W` (q = |W|). -/
abbrev joinK (G : SimpleGraph V) (W : Type*) : SimpleGraph (V ⊕ W) := G.join (⊤ : SimpleGraph W)

theorem sum_ite_ne_add {α : Type*} [Fintype α] [DecidableEq α] (u : α) (g : α → ℕ) :
    (∑ w, if u ≠ w then g w else 0) + g u = ∑ w, g w := by
  rw [← sum_filter, filter_ne, sum_erase_add _ _ (mem_univ u)]

theorem joinK_sumN_inl (f : V ⊕ W → ℕ) (v : V) :
    (G.joinK W).sumN f (.inl v) = G.sumN (f ∘ .inl) v + ∑ w, f (.inr w) := by
  rw [sumN_eq_sum_ite, Fintype.sum_sum_type, sumN_eq_sum_ite]
  simp

theorem joinK_sumN_inr (f : V ⊕ W → ℕ) (u : W) :
    (G.joinK W).sumN f (.inr u) + f (.inr u) = ∑ v, f (.inl v) + ∑ w, f (.inr w) := by
  rw [sumN_eq_sum_ite, Fintype.sum_sum_type]
  simp only [join_adj_inr_inl, ite_true, join_adj_inr_inr, top_adj]
  have := sum_ite_ne_add u (fun w => f (Sum.inr w))
  omega

/-- In G ∨ K_q every edge between V and W goes from the smaller to the larger sum, when f is
an additive coloring of G on V and labels W with [q], and q ≤ n - Δ - 1. -/
theorem joinK_sumN_lt (hq : Fintype.card W ≤ Fintype.card V - G.maxDegree - 1)
    {f : V ⊕ W → ℕ} (hV : ∀ v, 1 ≤ f (.inl v)) (hW : ∀ w, f (.inr w) ≤ Fintype.card W)
    (v : V) (u : W) : (G.joinK W).sumN f (.inl v) < (G.joinK W).sumN f (.inr u) := by
  have h1 := joinK_sumN_inl (G := G) f v
  have h2 := joinK_sumN_inr (G := G) f u
  have hcard : 1 ≤ Fintype.card W := Fintype.card_pos_iff.2 ⟨u⟩
  have hdeg := G.degree_le_maxDegree v
  have hsplit : G.sumN (f ∘ .inl) v + ∑ x ∈ univ \ G.neighborFinset v, f (.inl x) =
      ∑ x, f (.inl x) := by
    rw [sumN, add_comm]; exact sum_sdiff (subset_univ _)
  have hrest : Fintype.card V - G.degree v ≤ ∑ x ∈ univ \ G.neighborFinset v, f (.inl x) := by
    rw [← card_neighborFinset_eq_degree, ← card_univ, ← card_sdiff_of_subset (subset_univ _)]
    rw [card_eq_sum_ones]; exact sum_le_sum fun x _ => hV x
  have := hW u
  omega

/-- Theorem 2: η(G ∨ K_q) = max {η(G), q} for q ≤ n - Δ - 1. -/
theorem theorem_2 (hq : Fintype.card W ≤ Fintype.card V - G.maxDegree - 1) :
    (G.joinK W).eta = max G.eta (Fintype.card W) := by
  apply le_antisymm
  · -- an additive coloring of the join: an optimal f on G, and 1, …, q on K_q
    obtain ⟨f, hf⟩ := G.eta_attained
    let e := Fintype.equivFin W
    let f' : V ⊕ W → ℕ := Sum.elim f fun w => e w + 1
    have hW : ∀ w, f' (.inr w) ≤ Fintype.card W := fun w => (e w).2
    have hlt := joinK_sumN_lt hq (f := f') (fun v => (hf.1 v).1) hW
    refine eta_le_of_labeling (f := f') (lt_max_of_lt_left G.eta_pos) ?_ ?_
    · rintro (v | w)
      · exact ⟨(hf.1 v).1, (hf.1 v).2.trans (le_max_left _ _)⟩
      · exact ⟨by simp [f'], (hW w).trans (le_max_right _ _)⟩
    · rintro (a | a) (b | b) h
      · simp only [joinK_sumN_inl, ne_eq, add_left_inj]
        exact hf.2 a b h
      · exact (hlt a b).ne
      · exact (hlt b a).ne'
      · have h1 := joinK_sumN_inr (G := G) f' a
        have h2 := joinK_sumN_inr (G := G) f' b
        have hab : (e a : ℕ) ≠ e b := fun h' => h (e.injective (Fin.ext h'))
        have hfa : f' (.inr a) = e a + 1 := rfl
        have hfb : f' (.inr b) = e b + 1 := rfl
        omega
  · refine max_le ?_ ?_
    · -- an additive coloring of the join restricts to an additive coloring of G
      refine le_eta fun k f hk hf => eta_le (f := f ∘ Sum.inl) hk ⟨fun v => hf.1 _, fun a b h => ?_⟩
      have := hf.2 _ _ ((join_adj_inl_inl _ a b).2 h)
      rwa [joinK_sumN_inl, joinK_sumN_inl, ne_eq, add_left_inj] at this
    · -- the vertices of K_q are pairwise true twins
      have := observation_2 (G := G.joinK W) (univ.map ⟨Sum.inr, Sum.inr_injective⟩) ?_
      · simpa using this
      · have hN : ∀ a : W, insert (Sum.inr a) ((G.joinK W).neighborFinset (.inr a)) = univ := by
          intro a
          ext (x | x)
          · simp
          · simp only [mem_insert, Sum.inr.injEq, mem_neighborFinset, join_adj_inr_inr, top_adj,
              mem_univ, iff_true]
            exact (eq_or_ne x a).imp id Ne.symm
        intro u hu v hv
        obtain ⟨a, -, rfl⟩ := mem_map.1 hu
        obtain ⟨b, -, rfl⟩ := mem_map.1 hv
        simp only [Function.Embedding.coeFn_mk, TrueTwins, hN]

/-- χ(G ∨ K_q) ≥ χ(G) + q (the paper uses equality). -/
theorem chromaticNumber_joinK :
    G.chromaticNumber + Fintype.card W ≤ (G.joinK W).chromaticNumber := by
  show _ ≤ ⨅ n ∈ Set.ofPred (G.joinK W).Colorable, (n : ℕ∞)
  refine le_iInf₂ fun m hm => ?_
  obtain ⟨C⟩ : (G.joinK W).Colorable m := hm
  let S : Finset (Fin m) := univ.image fun w => C (.inr w)
  have hS : S.card = Fintype.card W := by
    rw [card_image_of_injective, card_univ]
    intro a b h
    by_contra hab
    exact C.valid ((join_adj_inr_inr _ a b).2 hab) h
  let C' : G.Coloring ↥(univ \ S) :=
    Coloring.mk (fun v => ⟨C (.inl v), by
        simp only [mem_sdiff, mem_univ, true_and, S, mem_image, not_exists]
        exact fun w h => C.valid (join_adj_inr_inl _ w v) h⟩)
      fun {a b} h heq => C.valid ((join_adj_inl_inl _ a b).2 h) (congrArg Subtype.val heq)
  have hle := C'.colorable.chromaticNumber_le
  rw [Fintype.card_coe, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
    hS] at hle
  have hqm : Fintype.card W ≤ m := hS ▸ (card_le_univ S).trans (by simp)
  calc G.chromaticNumber + Fintype.card W ≤ ((m - Fintype.card W : ℕ) : ℕ∞) + Fintype.card W :=
        by gcongr
    _ = m := by rw [← Nat.cast_add, Nat.sub_add_cancel hqm]

/-- If the conjecture holds for G, it holds for G ∨ K_q. -/
theorem theorem_2_conjecture (hq : Fintype.card W ≤ Fintype.card V - G.maxDegree - 1)
    (h : (G.eta : ℕ∞) ≤ G.chromaticNumber) :
    ((G.joinK W).eta : ℕ∞) ≤ (G.joinK W).chromaticNumber := by
  rw [theorem_2 hq]
  refine le_trans ?_ chromaticNumber_joinK
  rcases le_total G.eta (Fintype.card W) with hle | hle
  · rw [max_eq_right hle]; exact le_add_self
  · rw [max_eq_left hle]; exact h.trans le_self_add

end theorem2

end SimpleGraph

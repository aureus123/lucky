/-
  Section 1 of D. Severín, On the additive chromatic number of several families of graphs
  (Inf. Process. Lett. 158, 2020): additive colorings, the additive chromatic number η,
  acyclic orientations, topological additive numberings, η_t, and η(G) = min η_t(D).

  A graph is a Mathlib `SimpleGraph` on a finite type `V`; all vertices of the type are
  vertices of the graph.  `G.neighborFinset v` is N(v) and `G.degree v` is d(v).
-/
import ACN.Tactics

set_option linter.unusedSectionVars false

open Finset

/-! ## Ceiling division -/

namespace ACN

/-- `cdiv a b = ⌈a / b⌉` for natural numbers. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem cdiv_le_iff {a b k : ℕ} (hb : 0 < b) : cdiv a b ≤ k ↔ a ≤ k * b := by
  unfold cdiv
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hb, Nat.succ_mul]
  omega

theorem le_cdiv_iff {a b k : ℕ} (hb : 0 < b) : k ≤ cdiv a b ↔ k = 0 ∨ (k - 1) * b < a := by
  rcases k with _ | j
  · simp
  · have := (cdiv_le_iff (a := a) (k := j) hb).not
    simp only [not_le] at this
    simp only [Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, false_or]
    omega

theorem cdiv_mono {a a' b b' : ℕ} (ha : a ≤ a') (hb' : 0 < b') (hb : b' ≤ b) :
    cdiv a b ≤ cdiv a' b' := by
  have h1 : a' ≤ cdiv a' b' * b' := (cdiv_le_iff hb').1 le_rfl
  exact (cdiv_le_iff (lt_of_lt_of_le hb' hb)).2
    (ha.trans (h1.trans (Nat.mul_le_mul_left _ hb)))

/-- `cdiv` is the paper's ⌈a/b⌉ with real division. -/
theorem cdiv_eq_ceil {a b : ℕ} (hb : 0 < b) : cdiv a b = ⌈(a : ℝ) / b⌉₊ := by
  apply le_antisymm
  · rw [cdiv_le_iff hb]
    have h := Nat.le_ceil ((a : ℝ) / b)
    rw [div_le_iff₀ (by exact_mod_cast hb)] at h
    exact_mod_cast h
  · rw [Nat.ceil_le, div_le_iff₀ (by exact_mod_cast hb)]
    exact_mod_cast (cdiv_le_iff hb).1 le_rfl

end ACN

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Labelings and additive colorings -/

/-- `G.sumN f v` is the paper's f(N(v)). -/
def sumN (f : V → ℕ) (v : V) : ℕ := ∑ w ∈ G.neighborFinset v, f w

/-- A labeling f : V → [k]. -/
def Labeling (k : ℕ) (f : V → ℕ) : Prop := ∀ v, 1 ≤ f v ∧ f v ≤ k

/-- An additive k-coloring: adjacent vertices have different sums over their neighborhoods. -/
def AdditiveColoring (k : ℕ) (f : V → ℕ) : Prop :=
  Labeling k f ∧ ∀ u v, G.Adj u v → G.sumN f u ≠ G.sumN f v

variable {G}

theorem sumN_congr {f g : V → ℕ} (h : ∀ v, f v = g v) (u : V) : G.sumN f u = G.sumN g u := by
  simp [sumN, h]

theorem sumN_one (v : V) : G.sumN (fun _ => 1) v = G.degree v := by
  simp [sumN, card_neighborFinset_eq_degree]

/-- f(N(v)) as a sum over all vertices. -/
theorem sumN_eq_sum_ite (f : V → ℕ) (v : V) :
    G.sumN f v = ∑ w, if G.Adj v w then f w else 0 := by
  rw [sumN, neighborFinset_eq_filter, sum_filter]

/-- f(N(v)) from an explicit neighborhood. -/
theorem sumN_of_adj_iff {v : V} (s : Finset V) (h : ∀ w, G.Adj v w ↔ w ∈ s) (f : V → ℕ) :
    G.sumN f v = ∑ w ∈ s, f w := by
  rw [sumN]; congr 1; ext w; rw [mem_neighborFinset, h]

/-- f(N[v]) = f(v) + f(N(v)). -/
theorem sum_insert_neighborFinset (f : V → ℕ) (v : V) :
    ∑ w ∈ insert v (G.neighborFinset v), f w = f v + G.sumN f v := by
  rw [sum_insert (by simp), sumN]

theorem Labeling.mono {k k' : ℕ} {f : V → ℕ} (h : Labeling k f) (hk : k ≤ k') : Labeling k' f :=
  fun v => ⟨(h v).1, (h v).2.trans hk⟩

theorem AdditiveColoring.mono {k k' : ℕ} {f : V → ℕ} (h : G.AdditiveColoring k f) (hk : k ≤ k') :
    G.AdditiveColoring k' f :=
  ⟨h.1.mono hk, h.2⟩

variable (G)

/-- Every graph has an additive coloring: label the vertices with distinct powers of two. -/
theorem exists_additiveColoring : ∃ k, 0 < k ∧ ∃ f, G.AdditiveColoring k f := by
  let e : V ↪ ℕ := (Fintype.equivFin V).toEmbedding.trans Fin.valEmbedding
  let f : V → ℕ := fun v => 2 ^ e v
  have he : ∀ v, e v < Fintype.card V := fun v => ((Fintype.equivFin V) v).2
  refine ⟨2 ^ Fintype.card V, by positivity, f, fun v => ⟨Nat.one_le_two_pow, ?_⟩, ?_⟩
  · exact Nat.pow_le_pow_right (by norm_num) (he v).le
  · intro u v huv heq
    have enc : ∀ x, G.sumN f x = Finset.equivBitIndices.symm ((G.neighborFinset x).map e) := by
      intro x; simp [sumN, f]
    rw [enc, enc, Equiv.apply_eq_iff_eq, Finset.map_inj] at heq
    have : v ∈ G.neighborFinset u := (mem_neighborFinset _ _ _).2 huv
    rw [heq] at this
    exact G.irrefl ((mem_neighborFinset _ _ _).1 this)

/-! ## The additive chromatic number -/

open Classical in
/-- η(G): the least positive k with an additive k-coloring. -/
noncomputable def eta : ℕ := Nat.find G.exists_additiveColoring

theorem eta_spec : 0 < G.eta ∧ ∃ f, G.AdditiveColoring G.eta f := by
  classical
  exact Nat.find_spec G.exists_additiveColoring

theorem eta_pos : 0 < G.eta := G.eta_spec.1

theorem eta_attained : ∃ f, G.AdditiveColoring G.eta f := G.eta_spec.2

variable {G}

theorem eta_le {k : ℕ} {f : V → ℕ} (hk : 0 < k) (hf : G.AdditiveColoring k f) : G.eta ≤ k := by
  classical
  exact Nat.find_min' G.exists_additiveColoring ⟨hk, f, hf⟩

theorem le_eta {m : ℕ} (h : ∀ k f, 0 < k → G.AdditiveColoring k f → m ≤ k) : m ≤ G.eta := by
  obtain ⟨f, hf⟩ := G.eta_attained
  exact h _ f G.eta_pos hf

/-- An upper bound η(G) ≤ k from an explicit labeling. -/
theorem eta_le_of_labeling {k : ℕ} {f : V → ℕ} (hk : 0 < k) (hl : Labeling k f)
    (hs : ∀ u v, G.Adj u v → G.sumN f u ≠ G.sumN f v) : G.eta ≤ k :=
  eta_le hk ⟨hl, hs⟩

/-! ## Acyclic orientations and topological additive numberings

An orientation of G is a relation `A` that contains, for every edge, exactly one of its two
directions.  The paper's digraph D representing it has the same vertices, so N_D(v) = N(v). -/

variable (G)

/-- `A` is an orientation of `G`. -/
def IsOrientation (A : V → V → Prop) : Prop :=
  (∀ u v, A u v → G.Adj u v) ∧ (∀ u v, G.Adj u v → A u v ∨ A v u) ∧ ∀ u v, A u v → ¬ A v u

/-- `A` is an acyclic orientation of `G`. -/
def IsAcyclicOrientation (A : V → V → Prop) : Prop :=
  G.IsOrientation A ∧ ∀ v, ¬ Relation.TransGen A v v

/-- A topological additive k-numbering of the digraph `A`. -/
def TopAddNumbering (A : V → V → Prop) (k : ℕ) (f : V → ℕ) : Prop :=
  Labeling k f ∧ ∀ u v, A u v → G.sumN f u < G.sumN f v

open Classical in
/-- η_t(D), which is ∞ when there is no topological additive numbering. -/
noncomputable def etaT (A : V → V → Prop) : ℕ∞ :=
  if h : ∃ k, 0 < k ∧ ∃ f, G.TopAddNumbering A k f then (Nat.find h : ℕ∞) else ⊤

variable {G}

theorem etaT_le {A : V → V → Prop} {k : ℕ} {f : V → ℕ} (hk : 0 < k)
    (hf : G.TopAddNumbering A k f) : G.etaT A ≤ k := by
  classical
  have h : ∃ k, 0 < k ∧ ∃ f, G.TopAddNumbering A k f := ⟨k, hk, f, hf⟩
  rw [etaT, dite_eq_left h]
  exact_mod_cast Nat.find_min' h ⟨hk, f, hf⟩

theorem etaT_attained {A : V → V → Prop} (h : G.etaT A ≠ ⊤) :
    ∃ (k : ℕ) (f : V → ℕ), G.etaT A = k ∧ 0 < k ∧ G.TopAddNumbering A k f := by
  classical
  by_cases hex : ∃ k, 0 < k ∧ ∃ f, G.TopAddNumbering A k f
  · obtain ⟨hk, f, hf⟩ := Nat.find_spec hex
    exact ⟨_, f, by rw [etaT, dite_eq_left hex], hk, hf⟩
  · exact absurd (by rw [etaT, dite_eq_right hex]) h

/-- The orientation induced by the sums: every edge goes from the smaller to the larger sum. -/
def inducedOrientation (f : V → ℕ) (u v : V) : Prop := G.Adj u v ∧ G.sumN f u < G.sumN f v

theorem inducedOrientation_acyclic {k : ℕ} {f : V → ℕ} (hf : G.AdditiveColoring k f) :
    G.IsAcyclicOrientation (G.inducedOrientation f) := by
  refine ⟨⟨fun u v h => h.1, fun u v h => ?_, fun u v h h' => ?_⟩, fun v hv => ?_⟩
  · rcases Nat.lt_or_gt_of_ne (hf.2 u v h) with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h.symm, h'⟩
  · exact absurd h.2 (not_lt.2 h'.2.le)
  · have : ∀ a b, Relation.TransGen (G.inducedOrientation f) a b → G.sumN f a < G.sumN f b := by
      intro a b hab
      induction hab with
      | single h => exact h.2
      | tail _ h ih => exact ih.trans h.2
    exact lt_irrefl _ (this v v hv)

theorem inducedOrientation_topAddNumbering {k : ℕ} {f : V → ℕ} (hf : G.AdditiveColoring k f) :
    G.TopAddNumbering (G.inducedOrientation f) k f :=
  ⟨hf.1, fun _ _ h => h.2⟩

theorem TopAddNumbering.additiveColoring {A : V → V → Prop} {k : ℕ} {f : V → ℕ}
    (hA : G.IsOrientation A) (hf : G.TopAddNumbering A k f) : G.AdditiveColoring k f := by
  refine ⟨hf.1, fun u v h heq => ?_⟩
  rcases hA.2.1 u v h with h' | h'
  · exact absurd heq (hf.2 u v h').ne
  · exact absurd heq (hf.2 v u h').ne'

theorem eta_le_etaT {A : V → V → Prop} (hA : G.IsOrientation A) : (G.eta : ℕ∞) ≤ G.etaT A := by
  by_cases h : G.etaT A = ⊤
  · simp [h]
  · obtain ⟨k, f, hk, hk0, hf⟩ := etaT_attained h
    rw [hk]
    exact_mod_cast eta_le hk0 (hf.additiveColoring hA)

variable (G)

/-- η(G) = min {η_t(D) : D represents an acyclic orientation of G}. -/
theorem eta_eq_iInf_etaT :
    (G.eta : ℕ∞) = ⨅ (A : V → V → Prop) (_ : G.IsAcyclicOrientation A), G.etaT A := by
  apply le_antisymm
  · exact le_iInf₂ fun A hA => eta_le_etaT hA.1
  · obtain ⟨f, hf⟩ := G.eta_attained
    exact iInf₂_le_of_le _ (inducedOrientation_acyclic hf)
      (etaT_le G.eta_pos (inducedOrientation_topAddNumbering hf))

/-! ## True twins -/

/-- `u` and `v` are true twins: N[u] = N[v]. -/
def TrueTwins (u v : V) : Prop := insert u (G.neighborFinset u) = insert v (G.neighborFinset v)

end SimpleGraph

/-
  Section 4: headless spiders (Proposition 3).

  Spiders and suns are graphs on `α ⊕ β`: a graph `G` on `α` plus a stable set `β`, attached by a
  relation `R`.  For spiders of order q, the clique vertices u_i are `inl i` and the stable
  vertices v_i are `inr i`, with `i : Fin q` (the paper's index is i + 1).
-/
import ACN.Sec4

set_option linter.unusedSectionVars false

open Finset

namespace SimpleGraph

open ACN

/-! ## A graph with a stable set attached -/

section extend

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- `G.extend R`: the graph `G` on `α`, plus the stable set `β`, with `inl a` adjacent to `inr b`
iff `R a b`. -/
def extend (G : SimpleGraph α) (R : α → β → Prop) : SimpleGraph (α ⊕ β) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inl a, .inr b => R a b
    | .inr b, .inl a => R a b
    | .inr _, .inr _ => False
  symm := ⟨by
    rintro (a | a) (b | b) h <;> simp only at h ⊢
    · exact h.symm
    · exact h
    · exact h⟩
  loopless := ⟨by rintro (a | a) h <;> simp only at h; exact G.irrefl h⟩

variable (G : SimpleGraph α) (R : α → β → Prop)

@[simp] theorem extend_adj_inl_inl (a b : α) : (G.extend R).Adj (.inl a) (.inl b) ↔ G.Adj a b :=
  .rfl
@[simp] theorem extend_adj_inl_inr (a : α) (b : β) : (G.extend R).Adj (.inl a) (.inr b) ↔ R a b :=
  .rfl
@[simp] theorem extend_adj_inr_inl (b : β) (a : α) : (G.extend R).Adj (.inr b) (.inl a) ↔ R a b :=
  .rfl
@[simp] theorem extend_adj_inr_inr (a b : β) : ¬ (G.extend R).Adj (.inr a) (.inr b) := id

instance [DecidableRel G.Adj] [∀ a b, Decidable (R a b)] : DecidableRel (G.extend R).Adj
  | .inl a, .inl b => inferInstanceAs (Decidable (G.Adj a b))
  | .inl a, .inr b => inferInstanceAs (Decidable (R a b))
  | .inr b, .inl a => inferInstanceAs (Decidable (R a b))
  | .inr _, .inr _ => isFalse id

variable [DecidableRel G.Adj] [∀ a b, Decidable (R a b)]

theorem extend_sumN_inl (f : α ⊕ β → ℕ) (a : α) :
    (G.extend R).sumN f (.inl a) = G.sumN (f ∘ .inl) a + ∑ b, if R a b then f (.inr b) else 0 := by
  rw [sumN_eq_sum_ite, Fintype.sum_sum_type, sumN_eq_sum_ite]
  simp

theorem extend_sumN_inr (f : α ⊕ β → ℕ) (b : β) :
    (G.extend R).sumN f (.inr b) = ∑ a, if R a b then f (.inl a) else 0 := by
  rw [sumN_eq_sum_ite, Fintype.sum_sum_type]
  simp

end extend

/-- f(N(a)) + f(a) = f(V) in a complete graph. -/
theorem top_sumN_add {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℕ) (a : α) :
    (⊤ : SimpleGraph α).sumN g a + g a = ∑ x, g x := by
  rw [sumN_eq_sum_ite]
  simpa using sum_ite_ne_add a g

/-! ## Thin and thick headless spiders -/

/-- The thin headless spider of order q: u_i adjacent to v_i. -/
abbrev thinSpider (q : ℕ) : SimpleGraph (Fin q ⊕ Fin q) :=
  (⊤ : SimpleGraph (Fin q)).extend fun i j => i = j

/-- The thick headless spider of order q: u_i adjacent to v_j for i ≠ j. -/
abbrev thickSpider (q : ℕ) : SimpleGraph (Fin q ⊕ Fin q) :=
  (⊤ : SimpleGraph (Fin q)).extend fun i j => i ≠ j

section spiders

variable {q : ℕ}

theorem thin_sumN_inl (f : Fin q ⊕ Fin q → ℕ) (i : Fin q) :
    (thinSpider q).sumN f (.inl i) + f (.inl i) = ∑ a, f (.inl a) + f (.inr i) := by
  rw [extend_sumN_inl, sum_ite_eq]
  have := top_sumN_add (f ∘ Sum.inl) i
  simp only [Function.comp, mem_univ, ite_true] at this ⊢
  omega

theorem thin_sumN_inr (f : Fin q ⊕ Fin q → ℕ) (j : Fin q) :
    (thinSpider q).sumN f (.inr j) = f (.inl j) := by
  rw [extend_sumN_inr, sum_ite_eq']
  simp

theorem thick_sumN_inl (f : Fin q ⊕ Fin q → ℕ) (i : Fin q) :
    (thickSpider q).sumN f (.inl i) + f (.inl i) + f (.inr i) =
      ∑ a, f (.inl a) + ∑ b, f (.inr b) := by
  rw [extend_sumN_inl]
  have h1 := top_sumN_add (f ∘ Sum.inl) i
  have h2 := sum_ite_ne_add i fun b => f (.inr b)
  simp only [Function.comp] at h1 h2 ⊢
  omega

theorem thick_sumN_inr (f : Fin q ⊕ Fin q → ℕ) (j : Fin q) :
    (thickSpider q).sumN f (.inr j) + f (.inl j) = ∑ a, f (.inl a) := by
  rw [extend_sumN_inr]
  have := sum_ite_ne_add j fun a => f (.inl a)
  simp only [ne_comm (a := j)] at this
  omega

/-- The clique u_1, …, u_q. -/
def spiderClique (q : ℕ) : Finset (Fin q ⊕ Fin q) := univ.map ⟨Sum.inl, Sum.inl_injective⟩

theorem spiderClique_isClique {R : Fin q → Fin q → Prop} [∀ a b, Decidable (R a b)] :
    ((⊤ : SimpleGraph (Fin q)).extend R).IsClique (spiderClique q : Set (Fin q ⊕ Fin q)) := by
  intro x hx y hy hxy
  simp only [spiderClique, coe_map, Function.Embedding.coeFn_mk, coe_univ, Set.image_univ,
    Set.mem_range] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  simpa using hxy

theorem card_spiderClique : (spiderClique q).card = q := by simp [spiderClique]

/-- A labeling given by functions of the paper's indices: f(u_i) = fu i, f(v_i) = fv i. -/
def spLab (fu fv : ℕ → ℕ) : Fin q ⊕ Fin q → ℕ := Sum.elim (fun i => fu (i.val + 1)) fun i => fv (i.val + 1)

@[simp] theorem spLab_inl (fu fv : ℕ → ℕ) (i : Fin q) : spLab fu fv (.inl i) = fu (i.val + 1) := rfl
@[simp] theorem spLab_inr (fu fv : ℕ → ℕ) (i : Fin q) : spLab fu fv (.inr i) = fv (i.val + 1) := rfl

theorem spLab_labeling {k : ℕ} {fu fv : ℕ → ℕ} (hu : ∀ i, 1 ≤ i → i ≤ q → 1 ≤ fu i ∧ fu i ≤ k)
    (hv : ∀ i, 1 ≤ i → i ≤ q → 1 ≤ fv i ∧ fv i ≤ k) : Labeling k (spLab (q := q) fu fv) := by
  rintro (i | i)
  · exact hu _ (by omega) i.2
  · exact hv _ (by omega) i.2

/-- Three values of a sum over the vertices: f(1) + f(2) + f(q) ≤ ∑ f for q ≥ 3. -/
theorem three_le_sum (hq : 3 ≤ q) (g : ℕ → ℕ) :
    g 1 + g 2 + g q ≤ ∑ i : Fin q, g (i.val + 1) := by
  let a : Fin q := ⟨0, by omega⟩
  let b : Fin q := ⟨1, by omega⟩
  let c : Fin q := ⟨q - 1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]; omega
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]; omega
  have := sum_le_sum_of_subset (f := fun i : Fin q => g (i.val + 1)) (subset_univ {a, b, c})
  rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton] at this
  simp only [a, b, c, zero_add, Nat.reduceAdd, show q - 1 + 1 = q by omega] at this
  omega

theorem one_le_sum_erase (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ i → i ≤ q → 1 ≤ g i) (a : Fin q) :
    q - 1 ≤ ∑ i ∈ univ.erase a, g (i.val + 1) := by
  have : (univ.erase a).card = q - 1 := by simp
  rw [← this, card_eq_sum_ones]
  exact sum_le_sum fun i _ => hg _ (by omega) i.2

/-- Proposition 3, thin spiders: η = ⌈(q + 1)/2⌉ for q ≥ 2. -/
theorem proposition_3_thin (hq : 2 ≤ q) : (thinSpider q).eta = cdiv (q + 1) 2 := by
  have hr : cdiv (q + 1) 2 = (q + 2) / 2 := by simp [cdiv]
  apply le_antisymm
  · rw [hr]
    rcases Nat.eq_or_lt_of_le hq with rfl | hq3
    · -- q = 2: f(u_i) = 1, f(v_1) = 1, f(v_2) = 2
      let fv : ℕ → ℕ := fun i => if i = 2 then 2 else 1
      refine eta_le_of_labeling (f := spLab (fun _ => 1) fv) (by norm_num)
        (spLab_labeling (by intros; omega) (by intros; simp only [fv]; split_omega)) ?_
      have S : ∀ i : Fin 2, (thinSpider 2).sumN (spLab (fun _ => 1) fv) (.inl i) =
          1 + fv (i.val + 1) := by
        intro i; have := thin_sumN_inl (spLab (fun _ => 1) fv) i; simp at this; omega
      rintro (i | i) (j | j) h
      · simp only [extend_adj_inl_inl, top_adj] at h
        rw [S, S]; fin_cases i <;> fin_cases j <;> simp_all [fv]
      · simp only [extend_adj_inl_inr] at h; subst h
        rw [S, thin_sumN_inr]; simp only [spLab_inl, fv]; split_omega
      · simp only [extend_adj_inr_inl] at h; subst h
        rw [S, thin_sumN_inr]; simp only [spLab_inl, fv]; split_omega
      · exact absurd h (extend_adj_inr_inr _ _ _ _)
    · -- q ≥ 3: the labeling of the appendix, with r = ⌊(q + 2)/2⌋
      set r := (q + 2) / 2
      let fu : ℕ → ℕ := fun i => if i ≤ r then r - i + 1 else q - i + 1
      let fv : ℕ → ℕ := fun i => if i ≤ r then 1 else (q + 1) / 2
      let f := spLab (q := q) fu fv
      have key : ∀ i, 1 ≤ i → i ≤ q → fv i + r = fu i + i := by
        intro i _ _; simp only [fu, fv]; split_omega
      have FU : 2 * r ≤ ∑ i : Fin q, fu (i.val + 1) := by
        have := three_le_sum (q := q) (by omega) fu
        have h1 : fu 1 = r := by simp only [fu]; split_omega
        have h2 : fu 2 = r - 1 := by simp only [fu]; split_omega
        have h3 : fu q = 1 := by simp only [fu]; split_omega
        omega
      have su : ∀ i : Fin q, (thinSpider q).sumN f (.inl i) + r =
          ∑ a : Fin q, fu (a.val + 1) + (i.val + 1) := by
        intro i
        have h1 : (thinSpider q).sumN f (.inl i) + fu (i.val + 1) =
            ∑ a : Fin q, fu (a.val + 1) + fv (i.val + 1) := thin_sumN_inl f i
        have := key (i.val + 1) (by omega) i.2
        omega
      refine eta_le_of_labeling (f := f) (k := r) (by omega)
        (spLab_labeling (by intro i _ _; simp only [fu]; split_omega)
          (by intro i _ _; simp only [fv]; split_omega)) ?_
      have uv : ∀ i : Fin q, (thinSpider q).sumN f (.inr i) < (thinSpider q).sumN f (.inl i) := by
        intro i
        rw [thin_sumN_inr]
        have := su i
        have : fu (i.val + 1) ≤ r := by simp only [fu]; split_omega
        change fu (i.val + 1) < _
        omega
      rintro (i | i) (j | j) h
      · simp only [extend_adj_inl_inl, top_adj] at h
        have := su i; have := su j
        have : i.val ≠ j.val := fun h' => h (Fin.ext h')
        omega
      · simp only [extend_adj_inl_inr] at h; subst h; exact (uv _).ne'
      · simp only [extend_adj_inr_inl] at h; subst h; exact (uv _).ne
      · exact absurd h (extend_adj_inr_inr _ _ _ _)
  · -- lower bound: Corollary 2 on the clique u_1, …, u_q, where d(u_i) = q
    have hd : ∀ v ∈ spiderClique q, (thinSpider q).degree v = q := by
      intro v hv
      simp only [spiderClique, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk] at hv
      obtain ⟨i, rfl⟩ := hv
      have := thin_sumN_inl (fun _ => 1) i
      rw [sumN_one] at this
      simp at this
      omega
    have := corollary_2_of_degree_eq spiderClique_isClique
      ⟨.inl ⟨0, by omega⟩, by simp [spiderClique]⟩ hd
    rwa [card_spiderClique, show q + 2 - q = 2 by omega] at this

/-- Proposition 3, thick spiders: η = ⌈(q + 1)/2⌉ for q ≥ 2. -/
theorem proposition_3_thick (hq : 2 ≤ q) : (thickSpider q).eta = cdiv (q + 1) 2 := by
  have hr : cdiv (q + 1) 2 = (q + 2) / 2 := by simp [cdiv]
  rw [hr]
  apply le_antisymm
  · rcases Nat.eq_or_lt_of_le hq with rfl | hq3
    · -- q = 2: f(u_i) = 1, f(v_1) = 2, f(v_2) = 1
      let fv : ℕ → ℕ := fun i => if i = 1 then 2 else 1
      refine eta_le_of_labeling (f := spLab (fun _ => 1) fv) (by norm_num)
        (spLab_labeling (by intros; omega) (by intros; simp only [fv]; split_omega)) ?_
      have Su : ∀ i : Fin 2, (thickSpider 2).sumN (spLab (fun _ => 1) fv) (.inl i) + 1 +
          fv (i.val + 1) = 5 := by
        intro i; have := thick_sumN_inl (spLab (fun _ => 1) fv) i; simpa [Fin.sum_univ_two, fv]
          using this
      have Sv : ∀ j : Fin 2, (thickSpider 2).sumN (spLab (fun _ => 1) fv) (.inr j) = 1 := by
        intro j; have := thick_sumN_inr (spLab (fun _ => 1) fv) j; simp at this; omega
      rintro (i | i) (j | j) h
      · simp only [extend_adj_inl_inl, top_adj] at h
        have := Su i; have := Su j
        fin_cases i <;> fin_cases j <;> simp_all [fv]
      · rw [Sv]; have := Su i
        have : fv (i.val + 1) ≤ 2 := by simp only [fv]; split_omega
        omega
      · rw [Sv]; have := Su j
        have : fv (j.val + 1) ≤ 2 := by simp only [fv]; split_omega
        omega
      · exact absurd h (extend_adj_inr_inr _ _ _ _)
    · -- q ≥ 3: the labeling of the appendix
      set r := (q + 2) / 2
      let fu : ℕ → ℕ := fun i => if i ≤ r then i else r
      let fv : ℕ → ℕ := fun i => if i ≤ r then 1 else i - r + 1
      let f := spLab (q := q) fu fv
      have key : ∀ i, fu i + fv i = i + 1 := by intro i; simp only [fu, fv]; split_omega
      have FV : q + 1 ≤ ∑ i : Fin q, fv (i.val + 1) := by
        let a : Fin q := ⟨q - 1, by omega⟩
        have h1 := sum_erase_add univ (fun i : Fin q => fv (i.val + 1)) (mem_univ a)
        have h2 := one_le_sum_erase fv (by intro i _ _; simp only [fv]; split_omega) a
        have h3 : fv (a.val + 1) ≥ 2 := by simp only [a, fv]; split_omega
        omega
      have su : ∀ i : Fin q, (thickSpider q).sumN f (.inl i) + (i.val + 1) + 1 =
          ∑ a : Fin q, fu (a.val + 1) + ∑ a : Fin q, fv (a.val + 1) := by
        intro i
        have h1 : (thickSpider q).sumN f (.inl i) + fu (i.val + 1) + fv (i.val + 1) =
            ∑ a : Fin q, fu (a.val + 1) + ∑ a : Fin q, fv (a.val + 1) := thick_sumN_inl f i
        have := key (i.val + 1)
        omega
      have sv : ∀ j : Fin q, (thickSpider q).sumN f (.inr j) + fu (j.val + 1) =
          ∑ a : Fin q, fu (a.val + 1) := fun j => thick_sumN_inr f j
      refine eta_le_of_labeling (f := f) (k := r) (by omega)
        (spLab_labeling (by intro i _ _; simp only [fu]; split_omega)
          (by intro i _ _; simp only [fv]; split_omega)) ?_
      have uv : ∀ i j : Fin q, (thickSpider q).sumN f (.inr j) < (thickSpider q).sumN f (.inl i) := by
        intro i j
        have := su i; have := sv j
        have : 1 ≤ fu (j.val + 1) := by simp only [fu]; split_omega
        have := i.2
        omega
      rintro (i | i) (j | j) h
      · simp only [extend_adj_inl_inl, top_adj] at h
        have := su i; have := su j
        have : i.val ≠ j.val := fun h' => h (Fin.ext h')
        omega
      · exact (uv i j).ne'
      · exact (uv j i).ne
      · exact absurd h (extend_adj_inr_inr _ _ _ _)
  · -- lower bound: f(u_i) + f(v_i) takes q distinct values in [2, 2k]
    refine le_eta fun k f hk hf => ?_
    let g : Fin q → ℕ := fun i => f (.inl i) + f (.inr i)
    have inj : Function.Injective g := by
      intro i j h
      by_contra hij
      have h1 := thick_sumN_inl f i
      have h2 := thick_sumN_inl f j
      exact hf.2 (.inl i) (.inl j) (by simpa using hij) (by simp only [g] at h; omega)
    have hrange : univ.image g ⊆ Icc 2 (2 * k) := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      have := hf.1 (.inl i); have := hf.1 (.inr i)
      simp only [mem_Icc, g]; omega
    have := card_le_card hrange
    rw [card_image_of_injective _ inj, card_univ, Fintype.card_fin, Nat.card_Icc] at this
    omega

end spiders

end SimpleGraph

/-
  Section 4: suns, and complete suns (Proposition 4).

  A sun is built from a graph `B` on `β` and the vertices u_1, …, u_m of `B` (an injection
  `u : Fin m → β`): add the vertices v_j (`inr j`) and the edges u_j v_j and u_{j+1} v_j (indices
  modulo m).  The paper's index is j + 1.
-/
import ACN.Sec3Families
import ACN.Sec4Spiders

set_option linter.unusedSectionVars false

open Finset

/-! ## Successor and predecessor in `Fin m` -/

namespace ACN

variable {m : ℕ}

/-- j + 1 modulo m. -/
def finNext (j : Fin m) : Fin m := ⟨csucc m j.val, csucc_lt (by have := j.2; omega) j.2⟩

/-- j - 1 modulo m. -/
def finPrev (j : Fin m) : Fin m := ⟨cpred m j.val, cpred_lt (by have := j.2; omega) j.2⟩

theorem finPrev_finNext (j : Fin m) : finPrev (finNext j) = j := Fin.ext (cpred_csucc _)

theorem finNext_finPrev (j : Fin m) : finNext (finPrev j) = j := Fin.ext (csucc_cpred j.2)

theorem finNext_ne (hm : 2 ≤ m) (j : Fin m) : finNext j ≠ j := by
  intro h; have := congrArg Fin.val h; revert this; simp only [finNext, csucc]; split_omega

theorem finPrev_ne (hm : 2 ≤ m) (j : Fin m) : finPrev j ≠ j := by
  intro h; have := congrArg Fin.val h; revert this; simp only [finPrev, cpred]; split_omega

theorem finNext_eq_iff {i j : Fin m} : i = finNext j ↔ j = finPrev i := by
  constructor
  · rintro rfl; rw [finPrev_finNext]
  · rintro rfl; rw [finNext_finPrev]

/-- ∑ over all b of `g b` restricted to two distinct points. -/
theorem sum_ite_or_eq {α : Type*} [Fintype α] [DecidableEq α] {x y : α} (hxy : x ≠ y)
    (g : α → ℕ) : ∑ b, (if b = x ∨ b = y then g b else 0) = g x + g y := by
  have : ∀ b, (if b = x ∨ b = y then g b else 0) =
      (if b = x then g b else 0) + (if b = y then g b else 0) := by
    intro b
    by_cases hx : b = x <;> by_cases hy : b = y <;> simp_all
  rw [sum_congr rfl fun b _ => this b, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp

end ACN

namespace SimpleGraph

open ACN

/-! ## Suns -/

section sun

variable {β : Type*} [Fintype β] [DecidableEq β] {m : ℕ}

/-- The sun of `B` with respect to u_1, …, u_m. -/
abbrev sun (B : SimpleGraph β) (u : Fin m → β) : SimpleGraph (β ⊕ Fin m) :=
  B.extend fun b j => b = u j ∨ b = u (finNext j)

variable {B : SimpleGraph β} [DecidableRel B.Adj] {u : Fin m → β}

/-- f(N(v_j)) = f(u_j) + f(u_{j+1}). -/
theorem sun_sumN_inr (hm : 2 ≤ m) (hu : Function.Injective u) (f : β ⊕ Fin m → ℕ) (j : Fin m) :
    (B.sun u).sumN f (.inr j) = f (.inl (u j)) + f (.inl (u (finNext j))) := by
  rw [extend_sumN_inr]
  exact sum_ite_or_eq (hu.ne (finNext_ne hm j).symm) fun b => f (.inl b)

/-- f(N(u_i)) = f_B(N(u_i)) + f(v_i) + f(v_{i-1}). -/
theorem sun_sumN_inl (hm : 2 ≤ m) (hu : Function.Injective u) (f : β ⊕ Fin m → ℕ) (i : Fin m) :
    (B.sun u).sumN f (.inl (u i)) =
      B.sumN (f ∘ .inl) (u i) + f (.inr i) + f (.inr (finPrev i)) := by
  rw [extend_sumN_inl, add_assoc]
  congr 1
  rw [← sum_ite_or_eq (finPrev_ne hm i).symm fun j => f (.inr j)]
  refine sum_congr rfl fun j _ => if_congr ?_ rfl rfl
  rw [hu.eq_iff, hu.eq_iff, finNext_eq_iff, eq_comm]

/-- The other vertices of `B` keep their sums. -/
theorem sun_sumN_hub (f : β ⊕ Fin m → ℕ) {b : β} (hb : ∀ j, b ≠ u j) :
    (B.sun u).sumN f (.inl b) = B.sumN (f ∘ .inl) b := by
  rw [extend_sumN_inl, sum_eq_zero fun j _ => ite_eq_right fun h => h.elim (hb j) (hb _)]
  simp

theorem sun_degree_inr (hm : 2 ≤ m) (hu : Function.Injective u) (j : Fin m) :
    (B.sun u).degree (.inr j) = 2 := by
  rw [← sumN_one, sun_sumN_inr hm hu]

theorem sun_degree_inl (hm : 2 ≤ m) (hu : Function.Injective u) (i : Fin m) :
    (B.sun u).degree (.inl (u i)) = B.degree (u i) + 2 := by
  rw [← sumN_one, sun_sumN_inl hm hu, ← sumN_one]
  rfl

end sun

end SimpleGraph

/-! ## The labeling of the appendix for complete suns

All quantities are natural numbers, with the paper's indices i ∈ {1, …, m}:
r = ⌈(m + 2)/3⌉ = (m + 4)/3, and 𝔭(m) = ⌈m/2⌉ + 1.  `ksQ` is the paper's permutation 𝔮. -/

namespace ACN

def ksR (m : ℕ) : ℕ := (m + 4) / 3

def ksQ (m i : ℕ) : ℕ :=
  if i = 1 then 1 else if i ≤ m / 2 + 1 then 2 * (i - 1) else 3 + 2 * (m - i)

def ksPm (m : ℕ) : ℕ := (m + 1) / 2 + 1

def ksFu (m i : ℕ) : ℕ := if m % 3 = 2 ∧ i = ksPm m then ksR m else ksQ m i / 3 + 1

def ksFv (m i : ℕ) : ℕ :=
  if i = 1 ∨ m / 2 + 2 ≤ i then ksR m + 1 - (ksQ m i + 2) / 3
  else if m % 6 = 2 ∧ i = ksPm m then 2 else ksR m + 1 - (ksQ m i + 4) / 3

/-- The predecessor of the paper's index i, modulo m. -/
def sprev (m i : ℕ) : ℕ := if i = 1 then m else i - 1

section ks

variable {m : ℕ}

theorem sprev_eq (a : ℕ) (ha : a < m) : sprev m (a + 1) = cpred m a + 1 := by
  unfold sprev cpred; split_omega

theorem ksQ_range (hm : 3 ≤ m) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) : 1 ≤ ksQ m i ∧ ksQ m i ≤ m := by
  unfold ksQ; split_omega

/-- 𝔮 is injective on {1, …, m}. -/
theorem ksQ_inj {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ m) (hj1 : 1 ≤ j) (hj2 : j ≤ m)
    (h : ksQ m i = ksQ m j) : i = j := by
  revert h
  unfold ksQ
  split_omega

theorem ksFu_range (hm : 3 ≤ m) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    1 ≤ ksFu m i ∧ ksFu m i ≤ ksR m := by
  unfold ksFu ksQ ksR ksPm; split_omega

theorem ksFv_range {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    1 ≤ ksFv m i ∧ ksFv m i ≤ ksR m := by
  unfold ksFv ksQ ksR ksPm; split_omega

theorem ksFu_last (hm : 3 ≤ m) : 2 ≤ ksFu m m := by
  unfold ksFu ksQ ksR ksPm; split_omega

set_option maxHeartbeats 4000000 in
/-- The paper's claim f(v_i) = 2r - 𝔮(i) + f(u_i) - f(v_{i-1}), checked by cases on m modulo 6
and m - i modulo 3 (the appendix's six cases).  In the case m ≡ 2 (mod 6), i = ⌊m/2⌋ + 1, the
paper takes r = m/3 + 1; in fact r = (m + 4)/3, so f(v_{i-1}) = 2 (not 1). -/
theorem ks_claim (hm : 3 ≤ m) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ m) :
    ksFv m i + ksFv m (sprev m i) + ksQ m i = 2 * ksR m + ksFu m i := by
  rcases Nat.eq_or_lt_of_le h1 with rfl | hi
  · simp only [ksFv, ksFu, ksQ, ksPm, ksR, sprev]
    mod_split m, 6 <;> split_omega
  · rw [show sprev m i = i - 1 by unfold sprev; split_omega]
    simp only [ksFv, ksFu, ksQ, ksPm, ksR]
    mod_split m, 6 <;> mod_split (m - i), 3 <;> split_omega

end ks

end ACN

namespace SimpleGraph

open ACN

/-! ## Proposition 4 -/

/-- The complete sun KS_m: the sun of the clique u_1, …, u_m. -/
abbrev completeSun (m : ℕ) : SimpleGraph (Fin m ⊕ Fin m) := (⊤ : SimpleGraph (Fin m)).sun id

/-- Proposition 4: η(KS_m) = ⌈(m + 2)/3⌉ for m ≥ 3. -/
theorem proposition_4 {m : ℕ} (hm : 3 ≤ m) : (completeSun m).eta = cdiv (m + 2) 3 := by
  have hr : cdiv (m + 2) 3 = ksR m := by simp [cdiv, ksR]
  have hinj : Function.Injective (id : Fin m → Fin m) := Function.injective_id
  apply le_antisymm
  · rw [hr]
    let f := spLab (q := m) (ksFu m) (ksFv m)
    have FU : m + 1 ≤ ∑ i : Fin m, ksFu m (i.val + 1) := by
      let a : Fin m := ⟨m - 1, by omega⟩
      have h1 := sum_erase_add univ (fun i : Fin m => ksFu m (i.val + 1)) (mem_univ a)
      have h2 := one_le_sum_erase (ksFu m) (fun i h1 h2 => (ksFu_range hm h1 h2).1) a
      have h3 : 2 ≤ ksFu m (a.val + 1) := by
        simp only [a, show m - 1 + 1 = m by omega]; exact ksFu_last hm
      omega
    have su : ∀ a : Fin m, (completeSun m).sumN f (.inl a) + ksQ m (a.val + 1) =
        ∑ i : Fin m, ksFu m (i.val + 1) + 2 * ksR m := by
      intro a
      have h1 : (completeSun m).sumN f (.inl a) = (⊤ : SimpleGraph (Fin m)).sumN (f ∘ Sum.inl) a +
          ksFv m (a.val + 1) + ksFv m (cpred m a.val + 1) :=
        sun_sumN_inl (B := ⊤) (u := id) (by omega) hinj f a
      have h2 : (⊤ : SimpleGraph (Fin m)).sumN (f ∘ Sum.inl) a + ksFu m (a.val + 1) =
          ∑ i : Fin m, ksFu m (i.val + 1) := top_sumN_add (f ∘ Sum.inl) a
      have h3 := ks_claim hm (i := a.val + 1) (by omega) a.2
      rw [sprev_eq a.val a.2] at h3
      omega
    have sv : ∀ j : Fin m, (completeSun m).sumN f (.inr j) ≤ 2 * ksR m := by
      intro j
      rw [sun_sumN_inr (B := ⊤) (by omega) hinj]
      have := ksFu_range hm (i := j.val + 1) (by omega) j.2
      have := ksFu_range hm (i := (finNext j).val + 1) (by omega) (finNext j).2
      change ksFu m (j.val + 1) + ksFu m ((finNext j).val + 1) ≤ _
      omega
    refine eta_le_of_labeling (f := f) (k := ksR m) (by unfold ksR; omega)
      (spLab_labeling (fun i h1 h2 => ksFu_range hm h1 h2) fun i h1 h2 => ksFv_range h1 h2) ?_
    have uv : ∀ a j : Fin m, (completeSun m).sumN f (.inr j) < (completeSun m).sumN f (.inl a) := by
      intro a j
      have := su a; have := sv j
      have := ksQ_range hm (i := a.val + 1) (by omega) a.2
      omega
    rintro (a | a) (b | b) h
    · simp only [extend_adj_inl_inl, top_adj] at h
      have := su a; have := su b
      have hq : ksQ m (a.val + 1) ≠ ksQ m (b.val + 1) := fun hq =>
        h (Fin.ext (by have := ksQ_inj (by omega) a.2 (by omega) b.2 hq; omega))
      omega
    · exact (uv a b).ne'
    · exact (uv b a).ne
    · exact absurd h (extend_adj_inr_inr _ _ _ _)
  · -- lower bound: Corollary 2 on the clique u_1, …, u_m, where d(u_i) = m + 1
    have hd : ∀ v ∈ spiderClique m, (completeSun m).degree v = m + 1 := by
      intro v hv
      simp only [spiderClique, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk] at hv
      obtain ⟨i, rfl⟩ := hv
      have h1 : (completeSun m).degree (.inl i) = (⊤ : SimpleGraph (Fin m)).degree i + 2 :=
        sun_degree_inl (B := ⊤) (u := id) (by omega) hinj i
      have h2 := top_sumN_add (fun _ => 1) i
      rw [sumN_one] at h2
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h2
      omega
    have := corollary_2_of_degree_eq spiderClique_isClique
      ⟨.inl ⟨0, by omega⟩, by simp [spiderClique]⟩ hd
    rwa [card_spiderClique, show m + 1 + 2 - m = 3 by omega, show m + 1 + 1 = m + 2 by omega]
      at this

end SimpleGraph

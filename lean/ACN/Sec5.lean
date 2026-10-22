/-
  Section 5: other suns.  Proposition 5: η(CS_m) = η(WS_m) = 2 for m ≥ 4.

  The cycle sun CS_m is the sun of the cycle u_1 ⋯ u_m (Mathlib's `cycleGraph m`); the wheel sun
  WS_m is the sun of the wheel W_m = C_m ∨ K_1, whose hub w is adjacent to every u_i.
-/
import ACN.Sec4Sun

set_option linter.unusedSectionVars false

open Finset

/-! ## The labeling of the appendix and its sums

Indices are 0-based here: the vertex `a : Fin m` is the paper's u_{a+1} (or v_{a+1}). -/

namespace ACN

/-- f(u_i) = 2 if i is odd, 1 otherwise (the paper's index i = a + 1). -/
def csFu (a : ℕ) : ℕ := if a % 2 = 0 then 2 else 1

/-- f(v_1) = 2 if m is odd, all other f(v_j) = 1. -/
def csFv (m a : ℕ) : ℕ := if a = 0 ∧ m % 2 = 1 then 2 else 1

/-- f(N(u_{a+1})) in CS_m. -/
def csU (m a : ℕ) : ℕ := csFu (csucc m a) + csFu (cpred m a) + csFv m a + csFv m (cpred m a)

/-- f(N(v_{a+1})) in CS_m and WS_m. -/
def csV (m a : ℕ) : ℕ := csFu a + csFu (csucc m a)

section cs

variable {m : ℕ}

/-- The values of f(N(u_{a+1})) computed in the appendix. -/
theorem csU_eq (hm : 4 ≤ m) {a : ℕ} (ha : a < m) :
    csU m a = if m % 2 = 0 then (if a % 2 = 0 then 4 else 6)
      else if a = 0 then 6 else if a = 1 then 7 else if a = m - 1 then 5
      else if a % 2 = 0 then 4 else 6 := by
  unfold csU
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · rw [csucc_of_lt (by omega), show cpred m 0 = m - 1 by simp [cpred]]
    unfold csFu csFv; split_omega
  · rw [cpred_of_pos ha0]
    rcases Nat.lt_or_ge (a + 1) m with ha1 | ha1
    · rw [csucc_of_lt ha1]; unfold csFu csFv; split_omega
    · rw [show csucc m a = 0 by simp [csucc]; omega]; unfold csFu csFv; split_omega

/-- The values of f(N(v_{a+1})). -/
theorem csV_eq (hm : 4 ≤ m) {a : ℕ} (ha : a < m) :
    csV m a = if m % 2 = 1 ∧ a = m - 1 then 4 else 3 := by
  unfold csV
  rcases Nat.lt_or_ge (a + 1) m with ha1 | ha1
  · rw [csucc_of_lt ha1]; unfold csFu; split_omega
  · rw [show csucc m a = 0 by simp [csucc]; omega]; unfold csFu; split_omega

theorem csU_range (hm : 4 ≤ m) {a : ℕ} (ha : a < m) : 4 ≤ csU m a ∧ csU m a ≤ 7 := by
  rw [csU_eq hm ha]; split_omega

theorem csU_next (hm : 4 ≤ m) {a : ℕ} (ha : a < m) : csU m a ≠ csU m (csucc m a) := by
  rw [csU_eq hm ha, csU_eq hm (csucc_lt (by omega) ha)]
  rcases Nat.lt_or_ge (a + 1) m with ha1 | ha1
  · rw [csucc_of_lt ha1]; split_omega
  · rw [show csucc m a = 0 by simp [csucc]; omega]; split_omega

theorem csV_lt (hm : 4 ≤ m) {a : ℕ} (ha : a < m) :
    csV m a < csU m a ∧ csV m a < csU m (csucc m a) := by
  rw [csV_eq hm ha, csU_eq hm ha, csU_eq hm (csucc_lt (by omega) ha)]
  rcases Nat.lt_or_ge (a + 1) m with ha1 | ha1
  · rw [csucc_of_lt ha1]; split_omega
  · rw [show csucc m a = 0 by simp [csucc]; omega]; split_omega

/-- ∑_{a < n} f(u_{a+1}) = n + ⌈n/2⌉. -/
theorem sum_csFu (n : ℕ) : ∑ a ∈ range n, csFu a = n + (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; unfold csFu; split_omega

end cs

end ACN

namespace SimpleGraph

open ACN

/-- The cycle sun CS_m. -/
abbrev cycleSun (m : ℕ) : SimpleGraph (Fin m ⊕ Fin m) := (cycleGraph m).sun id

/-- The wheel sun WS_m; its hub is `inl (inr 0)`. -/
abbrev wheelSun (m : ℕ) : SimpleGraph ((Fin m ⊕ Fin 1) ⊕ Fin m) :=
  ((cycleGraph m).joinK (Fin 1)).sun Sum.inl

/-- The labeling of CS_m. -/
def csLab (m : ℕ) : Fin m ⊕ Fin m → ℕ := Sum.elim (fun a => csFu a.val) fun a => csFv m a.val

section cycleSun

variable {m : ℕ}

theorem cycleSun_sumN_inl (hm : 4 ≤ m) (a : Fin m) :
    (cycleSun m).sumN (csLab m) (.inl a) = csU m a.val := by
  have h := sun_sumN_inl (B := cycleGraph m) (u := id) (by omega) Function.injective_id (csLab m) a
  have hc := cycleGraph_sumN (n := m) (by omega) csFu a
  change (cycleSun m).sumN (csLab m) (.inl a) =
    (cycleGraph m).sumN (fun j => csFu j.val) a + csFv m a.val + csFv m (cpred m a.val) at h
  rw [h, hc]; rfl

theorem cycleSun_sumN_inr (hm : 4 ≤ m) (a : Fin m) :
    (cycleSun m).sumN (csLab m) (.inr a) = csV m a.val :=
  sun_sumN_inr (B := cycleGraph m) (u := id) (by omega) Function.injective_id (csLab m) a

theorem cycleSun_degree_inl (hm : 4 ≤ m) (a : Fin m) : (cycleSun m).degree (.inl a) = 4 := by
  have h := sun_degree_inl (B := cycleGraph m) (u := id) (by omega) Function.injective_id a
  change (cycleSun m).degree (.inl a) = (cycleGraph m).degree a + 2 at h
  rw [h, cycleGraph_degree (by omega)]

/-- An edge between two vertices u: their sums differ. -/
theorem cs_uu (hm : 4 ≤ m) {a b : Fin m} (h : (cycleGraph m).Adj a b) :
    csU m a.val ≠ csU m b.val := by
  rcases (cycleGraph_adj_iff (by omega) a b).1 h with h' | h'
  · rw [h']; exact csU_next hm a.2
  · have : a.val = csucc m b.val := by rw [h', csucc_cpred a.2]
    rw [this]; exact (csU_next hm b.2).symm

end cycleSun

/-- Proposition 5, cycle suns: η(CS_m) = 2 for m ≥ 4. -/
theorem proposition_5_cycle {m : ℕ} (hm : 4 ≤ m) : (cycleSun m).eta = 2 := by
  refine eta_eq_two (u := .inl ⟨0, by omega⟩) (v := .inl ⟨1, by omega⟩) ?_ ?_ ?_
  · refine eta_le_of_labeling (f := csLab m) two_pos ?_ ?_
    · rintro (a | a) <;> simp only [csLab, Sum.elim_inl, Sum.elim_inr, csFu, csFv] <;> split_omega
    · rintro (a | a) (b | b) h
      · rw [cycleSun_sumN_inl hm, cycleSun_sumN_inl hm]
        exact cs_uu hm ((extend_adj_inl_inl _ _ a b).1 h)
      · rw [cycleSun_sumN_inl hm, cycleSun_sumN_inr hm]
        rcases (extend_adj_inl_inr _ _ a b).1 h with h' | h'
        · rw [show a = b from h']; exact (csV_lt hm b.2).1.ne'
        · rw [show a = finNext b from h']; exact (csV_lt hm b.2).2.ne'
      · rw [cycleSun_sumN_inr hm, cycleSun_sumN_inl hm]
        rcases (extend_adj_inr_inl _ _ a b).1 h with h' | h'
        · rw [show b = a from h']; exact (csV_lt hm a.2).1.ne
        · rw [show b = finNext a from h']; exact (csV_lt hm a.2).2.ne
      · exact absurd h (extend_adj_inr_inr _ _ _ _)
  · exact (extend_adj_inl_inl _ _ _ _).2 ((cycleGraph_adj_iff (by omega) _ _).2
      (Or.inl (by simp [csucc]; omega)))
  · rw [cycleSun_degree_inl hm, cycleSun_degree_inl hm]

/-! ## Wheel suns -/

section wheelSun

variable {m : ℕ}

/-- The hub of WS_m. -/
abbrev hub (m : ℕ) : (Fin m ⊕ Fin 1) ⊕ Fin m := .inl (.inr 0)

/-- A labeling of WS_m: f(u_{a+1}) = fu a, f(w) = c, f(v_{a+1}) = fv a. -/
def wsLab (m : ℕ) (fu fv : ℕ → ℕ) (c : ℕ) : (Fin m ⊕ Fin 1) ⊕ Fin m → ℕ :=
  Sum.elim (Sum.elim (fun a => fu a.val) fun _ => c) fun a => fv a.val

theorem wheelSun_sumN_inl (hm : 4 ≤ m) (fu fv : ℕ → ℕ) (c : ℕ) (a : Fin m) :
    (wheelSun m).sumN (wsLab m fu fv c) (.inl (.inl a)) =
      fu (csucc m a.val) + fu (cpred m a.val) + c + fv a.val + fv (cpred m a.val) := by
  have h := sun_sumN_inl (B := (cycleGraph m).joinK (Fin 1)) (u := Sum.inl) (by omega)
    Sum.inl_injective (wsLab m fu fv c) a
  have hj := joinK_sumN_inl (G := cycleGraph m) (W := Fin 1) (wsLab m fu fv c ∘ Sum.inl) a
  have hc := cycleGraph_sumN (n := m) (by omega) fu a
  change (wheelSun m).sumN (wsLab m fu fv c) (.inl (.inl a)) =
    ((cycleGraph m).joinK (Fin 1)).sumN (wsLab m fu fv c ∘ Sum.inl) (.inl a) + fv a.val +
      fv (cpred m a.val) at h
  change _ = (cycleGraph m).sumN (fun j => fu j.val) a + ∑ w : Fin 1, c at hj
  rw [h, hj, hc]
  simp only [Finset.univ_unique, sum_singleton]

theorem wheelSun_sumN_inr (hm : 4 ≤ m) (fu fv : ℕ → ℕ) (c : ℕ) (a : Fin m) :
    (wheelSun m).sumN (wsLab m fu fv c) (.inr a) = fu a.val + fu (csucc m a.val) :=
  sun_sumN_inr (B := (cycleGraph m).joinK (Fin 1)) (u := Sum.inl) (by omega) Sum.inl_injective
    (wsLab m fu fv c) a

theorem wheelSun_sumN_hub (fu fv : ℕ → ℕ) (c : ℕ) :
    (wheelSun m).sumN (wsLab m fu fv c) (hub m) = ∑ a ∈ range m, fu a := by
  have h := sun_sumN_hub (B := (cycleGraph m).joinK (Fin 1)) (u := Sum.inl) (wsLab m fu fv c)
    (b := .inr 0) fun j => Sum.inr_ne_inl
  have hj := joinK_sumN_inr (G := cycleGraph m) (W := Fin 1) (wsLab m fu fv c ∘ Sum.inl) 0
  change _ + c = ∑ a : Fin m, fu a.val + ∑ w : Fin 1, c at hj
  rw [h, ← Fin.sum_univ_eq_sum_range (fun a => fu a)]
  simp only [Finset.univ_unique, sum_singleton] at hj
  change ((cycleGraph m).joinK (Fin 1)).sumN (wsLab m fu fv c ∘ Sum.inl) (.inr 0) = _
  omega

theorem wheelSun_degree_inl (hm : 4 ≤ m) (a : Fin m) : (wheelSun m).degree (.inl (.inl a)) = 5 := by
  rw [← sumN_one]
  have h1 : (fun _ => 1 : (Fin m ⊕ Fin 1) ⊕ Fin m → ℕ) = wsLab m (fun _ => 1) (fun _ => 1) 1 := by
    funext x; rcases x with (x | x) | x <;> rfl
  rw [h1, wheelSun_sumN_inl hm]

/-- The adjacencies of WS_m between hub and cycle vertices, and on the cycle. -/
theorem wheelSun_adj_inl_inl {x y : Fin m ⊕ Fin 1} (h : (wheelSun m).Adj (.inl x) (.inl y)) :
    (∃ a b : Fin m, x = .inl a ∧ y = .inl b ∧ (cycleGraph m).Adj a b) ∨
      (∃ a : Fin m, x = .inl a ∧ y = .inr 0) ∨ (∃ a : Fin m, x = .inr 0 ∧ y = .inl a) := by
  rw [extend_adj_inl_inl] at h
  rcases x with a | w <;> rcases y with b | w'
  · exact Or.inl ⟨a, b, rfl, rfl, h⟩
  · exact Or.inr (Or.inl ⟨a, rfl, by rw [Subsingleton.elim w' 0]⟩)
  · exact Or.inr (Or.inr ⟨b, by rw [Subsingleton.elim w 0], rfl⟩)
  · exact absurd h (by simp [Subsingleton.elim w w'])

end wheelSun

/-- The special labeling of WS_5: f(u_i) = 2 for i ∈ {3, 5}, f(w) = 2, f(v_j) = 2 for j ≤ 3.
The sums are 8, 9, 8, 9, 6 on u_1, …, u_5, 2, 3, 3, 3, 3 on v_1, …, v_5, and 7 on w. -/
theorem wheelSun_five_eta_le : (wheelSun 5).eta ≤ 2 := by
  let fu : ℕ → ℕ := fun a => if a = 2 ∨ a = 4 then 2 else 1
  let fv : ℕ → ℕ := fun a => if a ≤ 2 then 2 else 1
  refine eta_le_of_labeling (f := wsLab 5 fu fv 2) two_pos ?_ ?_
  · rintro ((a | w) | a) <;> simp only [wsLab, Sum.elim_inl, Sum.elim_inr, fu, fv] <;> split_omega
  have su : ∀ a : Fin 5, (wheelSun 5).sumN (wsLab 5 fu fv 2) (.inl (.inl a)) =
      if a.val = 4 then 6 else if a.val % 2 = 0 then 8 else 9 := by
    intro a; rw [wheelSun_sumN_inl (by omega)]
    fin_cases a <;> simp [fu, fv, csucc, cpred]
  have sv : ∀ a : Fin 5, (wheelSun 5).sumN (wsLab 5 fu fv 2) (.inr a) =
      if a.val = 0 then 2 else 3 := by
    intro a; rw [wheelSun_sumN_inr (by omega)]
    fin_cases a <;> simp [fu, csucc]
  have sw : (wheelSun 5).sumN (wsLab 5 fu fv 2) (hub 5) = 7 := by
    rw [wheelSun_sumN_hub]; simp [fu, sum_range_succ]
  have w1 : ∀ w : Fin 1, (Sum.inr w : Fin 5 ⊕ Fin 1) = .inr 0 := fun w => by
    rw [Subsingleton.elim w 0]
  rintro ((a | w) | a) ((b | w') | b) h
  · rw [su, su]
    have hab := (cycleGraph_adj_iff (by omega) a b).1 (show (cycleGraph 5).Adj a b from h)
    fin_cases a <;> fin_cases b <;> simp_all [csucc, cpred]
  · rw [su, w1, sw]; fin_cases a <;> simp
  · rw [su, sv]; fin_cases a <;> fin_cases b <;> simp
  · rw [w1, sw, su]; fin_cases b <;> simp
  · exact absurd h (by rw [w1 w, w1 w']; exact (wheelSun 5).irrefl)
  · rw [w1, sw, sv]; fin_cases b <;> simp
  · rw [sv, su]; fin_cases a <;> fin_cases b <;> simp
  · rw [sv, w1, sw]; fin_cases a <;> simp
  · exact absurd h (extend_adj_inr_inr _ _ _ _)

/-- For m ≠ 5: the labeling of CS_m, plus f(w) = 1. -/
theorem wheelSun_eta_le {m : ℕ} (hm : 4 ≤ m) (h5 : m ≠ 5) : (wheelSun m).eta ≤ 2 := by
  have su : ∀ a : Fin m, (wheelSun m).sumN (wsLab m csFu (csFv m) 1) (.inl (.inl a)) =
      csU m a.val + 1 := by
    intro a; rw [wheelSun_sumN_inl hm]; unfold csU; ring
  have sv : ∀ a : Fin m, (wheelSun m).sumN (wsLab m csFu (csFv m) 1) (.inr a) = csV m a.val :=
    wheelSun_sumN_inr hm _ _ _
  have sw : (wheelSun m).sumN (wsLab m csFu (csFv m) 1) (hub m) = m + (m + 1) / 2 := by
    rw [wheelSun_sumN_hub, sum_csFu]
  have w_ne : ∀ a : Fin m, m + (m + 1) / 2 ≠ csU m a.val + 1 := by
    intro a
    have := csU_range hm a.2
    rcases Nat.eq_or_lt_of_le hm with rfl | h4
    · have : csU 4 a.val ≠ 5 := by rw [csU_eq le_rfl a.2]; split_omega
      omega
    · omega
  have w1 : ∀ w : Fin 1, (Sum.inr w : Fin m ⊕ Fin 1) = .inr 0 := fun w => by
    rw [Subsingleton.elim w 0]
  refine eta_le_of_labeling (f := wsLab m csFu (csFv m) 1) two_pos ?_ ?_
  · rintro ((a | w) | a) <;> simp only [wsLab, Sum.elim_inl, Sum.elim_inr, csFu, csFv] <;>
      split_omega
  rintro ((a | w) | a) ((b | w') | b) h
  · rw [su, su]
    have := cs_uu hm (show (cycleGraph m).Adj a b from h)
    omega
  · rw [su, w1, sw]; exact (w_ne a).symm
  · rw [su, sv]
    rcases (extend_adj_inl_inr _ _ _ b).1 h with h' | h'
    · rw [show a = b from Sum.inl_injective h']; have := (csV_lt hm b.2).1; omega
    · rw [show a = finNext b from Sum.inl_injective h']; have := (csV_lt hm b.2).2
      simp only [finNext]; omega
  · rw [w1, sw, su]; exact w_ne b
  · exact absurd h (by rw [w1 w, w1 w']; exact (wheelSun m).irrefl)
  · exact absurd ((extend_adj_inl_inr _ _ _ _).1 h) (by simp)
  · rw [sv, su]
    rcases (extend_adj_inr_inl _ _ a _).1 h with h' | h'
    · rw [show b = a from Sum.inl_injective h']; have := (csV_lt hm a.2).1; omega
    · rw [show b = finNext a from Sum.inl_injective h']; have := (csV_lt hm a.2).2
      simp only [finNext]; omega
  · exact absurd ((extend_adj_inr_inl _ _ _ _).1 h) (by simp)
  · exact absurd h (extend_adj_inr_inr _ _ _ _)

/-- Proposition 5, wheel suns: η(WS_m) = 2 for m ≥ 4. -/
theorem proposition_5_wheel {m : ℕ} (hm : 4 ≤ m) : (wheelSun m).eta = 2 := by
  refine eta_eq_two (u := .inl (.inl ⟨0, by omega⟩)) (v := .inl (.inl ⟨1, by omega⟩)) ?_ ?_ ?_
  · by_cases h5 : m = 5
    · subst h5; exact wheelSun_five_eta_le
    · exact wheelSun_eta_le hm h5
  · exact (extend_adj_inl_inl _ _ _ _).2 ((join_adj_inl_inl _ _ _).2
      ((cycleGraph_adj_iff (by omega) _ _).2 (Or.inl (by simp [csucc]; omega))))
  · rw [wheelSun_degree_inl hm, wheelSun_degree_inl hm]

end SimpleGraph

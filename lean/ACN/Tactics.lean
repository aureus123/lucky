/-
  Proof automation for the formalization.

  `split_omega` decides goals of linear arithmetic over ℕ (with `/` and `%` by constants) that
  contain `if-then-else`: the labelings of the families of graphs are defined by cases on the
  index.  It reduces every `if` whose condition `omega` decides from the hypotheses, splits the
  remaining ones, and closes each branch by `omega`.

  `omega` is not complete for several divisions by the same constant: `mod_split e, n` first
  splits on the residue of `e` modulo `n`.
-/
import Mathlib

namespace ACN

theorem ite_of_pos {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : c) : ite c a b = a :=
  ite_eq_left h

theorem ite_of_neg {α : Sort*} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : ite c a b = b :=
  ite_eq_right h

end ACN

/-- Decide a linear arithmetic goal with `if-then-else`: first every `if` whose condition `omega`
can decide (from the hypotheses) is reduced, then the remaining `if`s are split, and each branch is
closed by contradiction or `omega`. -/
macro "split_omega" : tactic =>
  `(tactic| first
    | omega
    | ((try simp (disch := omega) only [ACN.ite_of_pos, ACN.ite_of_neg]) <;>
       first
        | omega
        | (split_ifs <;>
            (try simp only [true_and, and_true, false_and, and_false, not_true_eq_false,
              not_false_eq_true] at *) <;>
            first
            | contradiction
            | omega
            | (constructor <;> intro <;> first | contradiction | omega))))

/-- `mod_split e, n` (for n = 2, 3, 6) splits the goal into the cases `e % n = 0`, …,
`e % n = n - 1`, given as hypotheses (the goal is not changed, so `split` still applies to its
`if`s); `omega` then decides the divisions by constants that it cannot decide on its own. -/
syntax "mod_split " term:max ", " num : tactic

macro_rules
  | `(tactic| mod_split $e, 2) =>
    `(tactic| rcases (by omega : $e % 2 = 0 ∨ $e % 2 = 1) with _h | _h)
  | `(tactic| mod_split $e, 3) =>
    `(tactic| rcases (by omega : $e % 3 = 0 ∨ $e % 3 = 1 ∨ $e % 3 = 2) with _h | _h | _h)
  | `(tactic| mod_split $e, 6) =>
    `(tactic| rcases (by omega : $e % 6 = 0 ∨ $e % 6 = 1 ∨ $e % 6 = 2 ∨ $e % 6 = 3 ∨ $e % 6 = 4 ∨
      $e % 6 = 5) with _h | _h | _h | _h | _h | _h)

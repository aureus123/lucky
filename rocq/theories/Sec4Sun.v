(* Section 4: suns, and complete suns (Proposition 4).

   A sun is built from a graph B on a finite type and the vertices u_1, ..., u_m of B (an
   injection u : 'I_m -> B): add the vertices v_j (inr j) and the edges u_j v_j and
   u_(j+1) v_j (indices modulo m).  The paper's index is j + 1. *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics Sec2 Sec3 Sec3Families Sec4 Sec4Spiders.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * Successor and predecessor in 'I_m *)

Lemma osucc_ne m (j : 'I_m) : 2 <= m -> osucc j != j.
Proof. by move=> hm; rewrite -(inj_eq val_inj) /= /csucc; have := ltn_ord j; split_lia. Qed.

Lemma opred_ne m (j : 'I_m) : 2 <= m -> opred j != j.
Proof. by move=> hm; rewrite -(inj_eq val_inj) /= /cpred; have := ltn_ord j; split_lia. Qed.

Lemma osucc_eq m (i j : 'I_m) : (i == osucc j) = (j == opred i).
Proof.
apply/eqP/eqP => [-> | ->]; first by rewrite opred_osucc.
by rewrite osucc_opred.
Qed.

(* the sum of g over two distinct points *)
Lemma sum_if_or (T : finType) (g : T -> nat) x y : x != y ->
  \sum_b (if (b == x) || (b == y) then g b else 0) = g x + g y.
Proof.
move=> xy; rewrite -(sum_if_eq g x) -(sum_if_eq g y) -big_split /=.
apply: eq_bigr => b _; case: (b =P x) => [-> | _]; last by case: (b == y).
by rewrite (negbTE xy) addn0.
Qed.

(** * Suns *)

Section Sun.

Variables (B : sgraph) (m : nat) (u : 'I_m -> B).
Hypotheses (hm : 2 <= m) (hu : injective u).

(* the sun of B with respect to u_1, ..., u_m *)
Definition sun := extend B (fun b (j : 'I_m) => (b == u j) || (b == u (osucc j))).

(* f(N(v_j)) = f(u_j) + f(u_(j+1)) *)
Lemma sun_sumN_inr f j : sumN sun f (inr j) = f (inl (u j)) + f (inl (u (osucc j))).
Proof.
rewrite extend_sumN_inr sum_if_or // (inj_eq hu) eq_sym.
exact: osucc_ne.
Qed.

(* f(N(u_i)) = f_B(N(u_i)) + f(v_i) + f(v_(i-1)) *)
Lemma sun_sumN_inl f i :
  sumN sun f (inl (u i)) = sumN B (fun x => f (inl x)) (u i) + f (inr i) + f (inr (opred i)).
Proof.
rewrite extend_sumN_inl -addnA; congr (_ + _).
have ne : i != opred i by rewrite eq_sym opred_ne.
rewrite -(sum_if_or (fun j => f (inr j)) ne).
apply: eq_bigr => j _; rewrite !(inj_eq hu) osucc_eq [i == j]eq_sym.
by [].
Qed.

(* the other vertices of B keep their sums *)
Lemma sun_sumN_hub f b : (forall j, b != u j) ->
  sumN sun f (inl b) = sumN B (fun x => f (inl x)) b.
Proof.
move=> hb; rewrite extend_sumN_inl big1 ?addn0 // => j _.
by rewrite (negbTE (hb j)) (negbTE (hb (osucc j))).
Qed.

Lemma sun_deg_inr j : deg sun (inr j) = 2.
Proof. by rewrite -sumN_one sun_sumN_inr. Qed.

Lemma sun_deg_inl i : deg sun (inl (u i)) = deg B (u i) + 2.
Proof. by rewrite -sumN_one sun_sumN_inl sumN_one -addnA. Qed.

End Sun.

Arguments sun B {m} u.
Arguments sun_sumN_inr B {m u} hm hu f j.
Arguments sun_sumN_inl B {m u} hm hu f i.
Arguments sun_sumN_hub B {m u} f {b}.
Arguments sun_deg_inr B {m u} hm hu j.
Arguments sun_deg_inl B {m u} hm hu i.

(** * The labeling of the appendix for complete suns

   All quantities are natural numbers, with the paper's indices i in {1, ..., m}:
   r = ceil((m + 2)/3) = (m + 4)/3, and p(m) = ceil(m/2) + 1.  ksQ is the paper's
   permutation q. *)

Definition ksR (m : nat) : nat := (m + 4) %/ 3.

Definition ksQ (m i : nat) : nat :=
  if i == 1 then 1 else if i <= m %/ 2 + 1 then 2 * (i - 1) else 3 + 2 * (m - i).

Definition ksPm (m : nat) : nat := (m + 1) %/ 2 + 1.

Definition ksFu (m i : nat) : nat :=
  if (m %% 3 == 2) && (i == ksPm m) then ksR m else ksQ m i %/ 3 + 1.

Definition ksFv (m i : nat) : nat :=
  if (i == 1) || (m %/ 2 + 2 <= i) then ksR m + 1 - (ksQ m i + 2) %/ 3
  else if (m %% 6 == 2) && (i == ksPm m) then 2 else ksR m + 1 - (ksQ m i + 4) %/ 3.

(* the predecessor of the paper's index i, modulo m *)
Definition sprev (m i : nat) : nat := if i == 1 then m else i - 1.

Section KS.

Variable m : nat.
Hypothesis hm : 3 <= m.

Lemma sprev_opred (a : 'I_m) : sprev m a.+1 = (opred a).+1.
Proof. by rewrite /sprev /= /cpred; have := ltn_ord a; split_lia. Qed.

Lemma ksQ_range i : 1 <= i <= m -> 1 <= ksQ m i <= m.
Proof. by rewrite /ksQ; split_lia. Qed.

(* q is injective on {1, ..., m} *)
Lemma ksQ_inj i j : 1 <= i <= m -> 1 <= j <= m -> ksQ m i = ksQ m j -> i = j.
Proof. by rewrite /ksQ; split_lia. Qed.

Lemma ksFu_range i : 1 <= i <= m -> 1 <= ksFu m i <= ksR m.
Proof. by rewrite /ksFu /ksQ /ksR /ksPm; split_lia. Qed.

Lemma ksFv_range i : 1 <= i <= m -> 1 <= ksFv m i <= ksR m.
Proof. by rewrite /ksFv /ksQ /ksR /ksPm; split_lia. Qed.

Lemma ksFu_last : 2 <= ksFu m m.
Proof. by rewrite /ksFu /ksQ /ksR /ksPm; split_lia. Qed.

(* The paper's claim f(v_i) = 2r - q(i) + f(u_i) - f(v_(i-1)), checked by cases.  In the
   case m = 2 (mod 6), i = floor(m/2) + 1, the paper takes r = m/3 + 1; in fact
   r = (m + 4)/3, so f(v_(i-1)) = 2 (not 1). *)
Lemma ks_claim i : 1 <= i <= m ->
  ksFv m i + ksFv m (sprev m i) + ksQ m i = 2 * ksR m + ksFu m i.
Proof. by rewrite /ksFv /ksFu /ksQ /ksPm /ksR /sprev; split_lia. Qed.

End KS.

(** * Proposition 4 *)

(* the complete sun KS_m: the sun of the clique u_1, ..., u_m *)
Definition complete_sun m := sun 'K_m id.

(* Proposition 4: eta(KS_m) = ceil((m + 2)/3) for m >= 3 *)
Theorem proposition_4 m : 3 <= m -> eta (complete_sun m) = cdiv (m + 2) 3.
Proof.
move=> hm; have hm2 : 2 <= m by lia.
have hr : cdiv (m + 2) 3 = ksR m by rewrite /cdiv /ksR; lia.
have hid : injective (@id 'I_m) by [].
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  (* lower bound: Corollary 2 on the clique u_1, ..., u_m, where d(u_i) = m + 1 *)
  have hd i : deg (complete_sun m) (inl i) = m.+1.
    rewrite (sun_deg_inl 'K_m hm2 hid i) -sumN_one.
    have := complete_sumN (fun _ => 1) i; rewrite sum_nat_const card_ord; nlia.
  have Q0 : 0 < #|uclique m| by rewrite uclique_card; lia.
  have := corollary_2_eq (@uclique_clique m _) Q0 (uclique_deg hd).
  have e1 : m.+1 + 1 = m + 2 by lia.
  have e2 : m.+1 + 2 - #|uclique m| = 3 by rewrite uclique_card; lia.
  by rewrite e1 e2.
rewrite hr.
pose f := splab m (ksFu m) (ksFv m).
have FU : m.+1 <= \sum_(i < m) ksFu m i.+1.
  apply: sum_ord_last; [lia | | exact: ksFu_last].
  by move=> i hi; have := ksFu_range hm hi; lia.
set SU := \sum_(i < m) ksFu m i.+1 in FU.
have su (a : 'I_m) : sumN (complete_sun m) f (inl a) + ksQ m a.+1 = SU + 2 * ksR m.
  have h1 := sun_sumN_inl 'K_m hm2 hid f a.
  have /= h2 := complete_sumN (fun x => f (inl x)) a.
  have h3 := ks_claim hm (i := a.+1) (ltac:(have := ltn_ord a; lia)).
  rewrite (sprev_opred hm) in h3.
  by move: h1 h2 h3; rewrite /f /complete_sun /= -/SU; nlia.
have sv (j : 'I_m) : sumN (complete_sun m) f (inr j) <= 2 * ksR m.
  rewrite /complete_sun (sun_sumN_inr 'K_m hm2 hid) /f /=.
  have := ksFu_range hm (i := j.+1) (ltac:(have := ltn_ord j; lia)).
  have := ksFu_range hm (i := (osucc j).+1) (ltac:(have := ltn_ord (osucc j); lia)).
  by nlia.
apply: (eta_le_lab (G := complete_sun m) (f := f)); first by rewrite /ksR; lia.
  apply: splab_labeling => i hi; first by have := ksFu_range hm hi; lia.
  by have := ksFv_range hm hi; lia.
have uv (a j : 'I_m) : sumN (complete_sun m) f (inr j) < sumN (complete_sun m) f (inl a).
  have := su a; have := sv j; have := ksQ_range hm (i := a.+1) (ltac:(have := ltn_ord a; lia)).
  by nlia.
move=> [a|a] [b|b] //= h.
- have hab : (a : nat) != b by move: h; rewrite /complete_rel -(inj_eq val_inj).
  have ra : 1 <= a.+1 <= m by have := ltn_ord a; lia.
  have rb : 1 <= b.+1 <= m by have := ltn_ord b; lia.
  have hq : ksQ m a.+1 != ksQ m b.+1.
    by apply/eqP => /(ksQ_inj hm ra rb) [e]; move: hab; rewrite e eqxx.
  by have := su a; have := su b; move: hq; nlia.
- by rewrite neq_ltn uv orbT.
by rewrite neq_ltn uv.
Qed.

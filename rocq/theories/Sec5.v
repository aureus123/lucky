(* Section 5: other suns.  Proposition 5: eta(CS_m) = eta(WS_m) = 2 for m >= 4.

   The cycle sun CS_m is the sun of the cycle u_1 ... u_m; the wheel sun WS_m is the sun of
   the wheel W_m = C_m v K_1, whose hub w is adjacent to every u_i.  Indices are 0-based: the
   vertex a : 'I_m is the paper's u_(a+1) (or v_(a+1)). *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics Sec2 Sec3 Sec3Families Sec4 Sec4Spiders Sec4Sun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * The labeling of the appendix and its sums *)

(* f(u_i) = 2 if i is odd, 1 otherwise (the paper's index i = a + 1) *)
Definition csFu (a : nat) : nat := if ~~ odd a then 2 else 1.

(* f(v_1) = 2 if m is odd, all other f(v_j) = 1 *)
Definition csFv (m a : nat) : nat := if (a == 0) && odd m then 2 else 1.

(* f(N(u_(a+1))) in CS_m *)
Definition csU (m a : nat) : nat :=
  csFu (csucc m a) + csFu (cpred m a) + csFv m a + csFv m (cpred m a).

(* f(N(v_(a+1))) in CS_m and WS_m *)
Definition csV (m a : nat) : nat := csFu a + csFu (csucc m a).

Section CS.

Variable m : nat.
Hypothesis hm : 4 <= m.

Lemma csU_range a : a < m -> 4 <= csU m a <= 7.
Proof. by rewrite /csU /csFu /csFv /csucc /cpred; split_lia. Qed.

Lemma csU_next a : a < m -> csU m a != csU m (csucc m a).
Proof. by rewrite /csU /csFu /csFv /csucc /cpred; split_lia. Qed.

Lemma csV_lt a : a < m -> csV m a < csU m a /\ csV m a < csU m (csucc m a).
Proof. by rewrite /csV /csU /csFu /csFv /csucc /cpred; split; split_lia. Qed.

End CS.

(* the even case m = 4 never gives the sum 5 *)
Lemma csU_four a : a < 4 -> csU 4 a != 5.
Proof. by rewrite /csU /csFu /csFv /csucc /cpred; split_lia. Qed.


(* sum_(a < n) f(u_(a+1)) = n + ceil(n/2) *)
Lemma sum_csFu n : \sum_(a < n) csFu a = n + n.+1 %/ 2.
Proof. by elim: n => [|n IH]; rewrite ?big_ord0 // big_ord_recr /= IH /csFu; split_lia. Qed.

(** * Cycle suns *)

(* the cycle sun CS_m *)
Definition cycle_sun m := sun (cycleG m) id.

(* the labeling of CS_m *)
Definition cslab m (x : ('I_m + 'I_m)%type) : nat :=
  match x with inl a => csFu a | inr a => csFv m a end.

Arguments cslab : clear implicits.

Section CycleSun.

Variable m : nat.
Hypothesis hm : 4 <= m.

Let hm2 : 2 <= m. Proof. by lia. Qed.
Let hm3 : 3 <= m. Proof. by lia. Qed.
Let hid : injective (@id 'I_m). Proof. by []. Qed.

Lemma cs_sumN_inl (a : 'I_m) : sumN (cycle_sun m) (cslab m) (inl a) = csU m a.
Proof.
rewrite /cycle_sun (sun_sumN_inl (cycleG m) hm2 hid) /=.
by rewrite (cycle_sumN hm3 csFu a).
Qed.

Lemma cs_sumN_inr (a : 'I_m) : sumN (cycle_sun m) (cslab m) (inr a) = csV m a.
Proof. by rewrite /cycle_sun (sun_sumN_inr (cycleG m) hm2 hid). Qed.

Lemma cs_deg_inl (a : 'I_m) : deg (cycle_sun m) (inl a) = 4.
Proof. by rewrite /cycle_sun (sun_deg_inl (cycleG m) hm2 hid) /= cycle_deg. Qed.

(* an edge between two vertices u: their sums differ *)
Lemma cs_uu (a b : 'I_m) : (a -- b :> cycleG m) -> csU m a != csU m b.
Proof.
rewrite cycle_adj // => /orP[/eqP -> | /eqP e]; first exact: csU_next.
have -> : (a : nat) = csucc m b by rewrite e /csucc /cpred; have := ltn_ord a; split_lia.
by rewrite eq_sym csU_next.
Qed.

(* an edge between u and v *)
Lemma cs_uv (a b : 'I_m) : (a == b) || (a == osucc b) -> csV m b < csU m a.
Proof.
case/orP => /eqP ->; first exact: (csV_lt hm (ltn_ord b)).1.
exact: (csV_lt hm (ltn_ord b)).2.
Qed.

End CycleSun.

(* Proposition 5, cycle suns: eta(CS_m) = 2 for m >= 4 *)
Theorem proposition_5_cycle m : 4 <= m -> eta (cycle_sun m) = 2.
Proof.
move=> hm; have h0 : 0 < m by lia.
have h1 : 1 < m by lia.
apply: (eta_eq_two (G := cycle_sun m) (u := inl (Ordinal h0)) (v := inl (Ordinal h1))).
- apply: (eta_le_lab (G := cycle_sun m) (f := cslab m)) => //.
    by move=> [a|a] /=; rewrite /csFu /csFv; split_lia.
  move=> [a|a] [b|b] //= h; rewrite ?cs_sumN_inl ?cs_sumN_inr //.
  + exact: cs_uu.
  + by rewrite neq_ltn cs_uv ?orbT.
  + by rewrite neq_ltn cs_uv.
- by rewrite /= /cycle_rel /csucc /=; split_lia.
by rewrite !cs_deg_inl.
Qed.

(** * Wheel suns *)

(* the wheel sun WS_m; its hub is inl (inr ord0) *)
Definition wheel_sun m := sun (joinK (cycleG m) 1) inl.

(* a labeling of WS_m: f(u_(a+1)) = fu a, f(w) = c, f(v_(a+1)) = fv a *)
Definition wslab m (fu fv : nat -> nat) (c : nat) (x : (('I_m + 'I_1) + 'I_m)%type) : nat :=
  match x with inl (inl a) => fu a | inl (inr _) => c | inr a => fv a end.

Arguments wslab : clear implicits.

Section WheelSun.

Variable m : nat.
Hypothesis hm : 4 <= m.

Let hm2 : 2 <= m. Proof. by lia. Qed.
Let hm3 : 3 <= m. Proof. by lia. Qed.
Let hinl : injective (@inl 'I_m 'I_1). Proof. by move=> x y []. Qed.

Variables (fu fv : nat -> nat) (c : nat).

Lemma ws_sumN_inl (a : 'I_m) :
  sumN (wheel_sun m) (wslab m fu fv c) (inl (inl a)) =
  fu (csucc m a) + fu (cpred m a) + c + fv a + fv (cpred m a).
Proof.
rewrite /wheel_sun (sun_sumN_inl (joinK (cycleG m) 1) hm2 hinl) /= gjoin_sumN_inl /=.
by rewrite (cycle_sumN hm3 fu a) big_ord1.
Qed.

Lemma ws_sumN_inr (a : 'I_m) :
  sumN (wheel_sun m) (wslab m fu fv c) (inr a) = fu a + fu (csucc m a).
Proof. by rewrite /wheel_sun (sun_sumN_inr (joinK (cycleG m) 1) hm2 hinl). Qed.

Lemma ws_sumN_hub :
  sumN (wheel_sun m) (wslab m fu fv c) (inl (inr ord0)) = \sum_(a < m) fu a.
Proof.
rewrite /wheel_sun (sun_sumN_hub (joinK (cycleG m) 1) (u := inl)) // gjoin_sumN_inr /=.
have := complete_sumN (fun _ : 'I_1 => c) ord0; rewrite big_ord1 => e.
by rewrite (_ : sumN _ _ _ = 0) ?addn0 //; nlia.
Qed.

(* a labeling of WS_m with labels in [2] is an additive coloring when the sums of
   adjacent vertices differ; these are the conditions *)
Lemma ws_eta_le :
  (forall a, a < m -> 0 < fu a <= 2) -> (forall a, a < m -> 0 < fv a <= 2) -> 0 < c <= 2 ->
  (forall a, a < m -> fu (csucc m a) + fu (cpred m a) + fv a + fv (cpred m a) !=
                      fu (csucc m (csucc m a)) + fu (cpred m (csucc m a)) + fv (csucc m a) +
                      fv (cpred m (csucc m a))) ->
  (forall a, a < m -> \sum_(b < m) fu b !=
                      fu (csucc m a) + fu (cpred m a) + c + fv a + fv (cpred m a)) ->
  (forall b, b < m -> fu b + fu (csucc m b) <
                      fu (csucc m b) + fu (cpred m b) + c + fv b + fv (cpred m b) /\
                      fu b + fu (csucc m b) <
                      fu (csucc m (csucc m b)) + fu (cpred m (csucc m b)) + c +
                      fv (csucc m b) + fv (cpred m (csucc m b))) ->
  eta (wheel_sun m) <= 2.
Proof.
move=> lu lv lc C1 C2 C3.
apply: (eta_le_lab (G := wheel_sun m) (f := wslab m fu fv c)) => //.
  by move=> [[a|w]|a] /=; [exact: lu | exact: lc | exact: lv].
have w0 (w : 'I_1) : w = ord0 by apply: val_inj; case: w => -[].
move=> [[a|w]|a] [[b|w']|b] //=.
- move=> h; have : (a -- b :> cycleG m) := h.
  rewrite !ws_sumN_inl (cycle_adj hm3) => /orP[/eqP e | /eqP e].
    by rewrite e; have := C1 a (ltn_ord a); nlia.
  have ea : (a : nat) = csucc m b.
    by move: e; rewrite /csucc /cpred; have := ltn_ord a; have := ltn_ord b; split_lia.
  by rewrite ea; have := C1 b (ltn_ord b); nlia.
- by move=> _; rewrite (w0 w') ws_sumN_inl ws_sumN_hub eq_sym; exact: C2.
- rewrite ws_sumN_inl ws_sumN_inr !(inj_eq hinl) => /orP[/eqP -> | /eqP ->].
    by have := (C3 b (ltn_ord b)).1; nlia.
  by have := (C3 b (ltn_ord b)).2; nlia.
- by move=> _; rewrite (w0 w) ws_sumN_inl ws_sumN_hub; exact: C2.
- by rewrite (w0 w) (w0 w') /complete_rel eqxx.
- rewrite ws_sumN_inr ws_sumN_inl !(inj_eq hinl) => /orP[/eqP -> | /eqP ->].
    by have := (C3 a (ltn_ord a)).1; nlia.
  by have := (C3 a (ltn_ord a)).2; nlia.
Qed.

End WheelSun.

(* for m <> 5: the labeling of CS_m, plus f(w) = 1 *)
Lemma wheel_sun_eta_le m : 4 <= m -> m != 5 -> eta (wheel_sun m) <= 2.
Proof.
move=> hm h5; apply: (ws_eta_le hm (fu := csFu) (fv := csFv m) (c := 1)).
- by move=> a _; rewrite /csFu; split_lia.
- by move=> a _; rewrite /csFv; split_lia.
- by [].
- by move=> a ha; have := csU_next hm ha; rewrite /csU; nlia.
- move=> a ha; rewrite sum_csFu; have := csU_range hm ha.
  case: (ltngtP m 4) => [| h | e]; first by lia.
    by rewrite /csU; nlia.
  by subst m; have := csU_four ha; rewrite /csU; nlia.
by move=> b hb; have := csV_lt hm hb; rewrite /csV /csU; nlia.
Qed.

(* the special labeling of WS_5: f(u_i) = 2 for i in {3, 5}, f(w) = 2, f(v_j) = 2 for
   j <= 3.  The sums are 8, 9, 8, 9, 6 on u_1, ..., u_5, 2, 3, 3, 3, 3 on v_1, ..., v_5,
   and 7 on w. *)
Lemma wheel_sun5_eta_le : eta (wheel_sun 5) <= 2.
Proof.
pose fu a := if (a == 2) || (a == 4) then 2 else 1.
pose fv a := if a <= 2 then 2 else 1.
apply: (ws_eta_le (m := 5) _ (fu := fu) (fv := fv) (c := 2)) => //.
- by move=> a _; rewrite /fu; split_lia.
- by move=> a _; rewrite /fv; split_lia.
- by move=> a ha; rewrite /fu /fv /csucc /cpred; split_lia.
- have s7 : \sum_(b < 5) fu b = 7 by rewrite !big_ord_recr big_ord0.
  move=> a ha; rewrite s7.
  by rewrite /fu /fv /csucc /cpred; split_lia.
by move=> b hb; rewrite /fu /fv /csucc /cpred; split; split_lia.
Qed.

(* Proposition 5, wheel suns: eta(WS_m) = 2 for m >= 4 *)
Theorem proposition_5_wheel m : 4 <= m -> eta (wheel_sun m) = 2.
Proof.
move=> hm; have h0 : 0 < m by lia.
have h1 : 1 < m by lia.
have deg5 (a : 'I_m) : deg (wheel_sun m) (inl (inl a)) = 5.
  have e : sumN (wheel_sun m) (fun _ => 1) (inl (inl a)) =
           sumN (wheel_sun m) (wslab m (fun _ => 1) (fun _ => 1) 1) (inl (inl a)).
    by apply: sumN_eq => -[[]|].
  by rewrite -sumN_one e ws_sumN_inl.
apply: (eta_eq_two (G := wheel_sun m) (u := inl (inl (Ordinal h0))) (v := inl (inl (Ordinal h1)))).
- case: (m =P 5) => [e | /eqP h5]; first by subst m; exact: wheel_sun5_eta_le.
  exact: wheel_sun_eta_le.
- by rewrite /= /cycle_rel /csucc /=; split_lia.
by rewrite !deg5.
Qed.

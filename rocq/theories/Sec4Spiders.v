(* Section 4: headless spiders (Proposition 3).

   Spiders and suns are graphs on G + B: a graph G plus a stable set B, attached by a
   relation R.  For spiders of order q the clique vertices u_i are inl i and the stable
   vertices v_i are inr i, with i : 'I_q (the paper's index is i + 1). *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics Sec2 Sec3 Sec4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * A graph with a stable set attached *)

Section Extend.

Variables (G : sgraph) (B : finType) (R : G -> B -> bool).

Definition extend_rel : rel (G + B)%type := fun x y =>
  match x, y with
  | inl a, inl b => a -- b
  | inl a, inr b => R a b
  | inr b, inl a => R a b
  | inr _, inr _ => false
  end.

Lemma extend_sym : symmetric extend_rel.
Proof. by move=> [a|a] [b|b] //=; rewrite adj_sym. Qed.

Lemma extend_irr : irreflexive extend_rel.
Proof. by move=> [a|a] //=; rewrite adj_irr. Qed.

(* G plus the stable set B, with inl a adjacent to inr b iff R a b *)
Definition extend := SGraph extend_sym extend_irr.

Lemma extend_sumN_inl f a :
  sumN extend f (inl a) =
  sumN G (fun x => f (inl x)) a + \sum_b (if R a b then f (inr b) else 0).
Proof. by rewrite sumN_mkcond big_sumType /= sumN_mkcond. Qed.

Lemma extend_sumN_inr f b :
  sumN extend f (inr b) = \sum_a (if R a b then f (inl a) else 0).
Proof. by rewrite sumN_mkcond big_sumType /= big1_eq addn0. Qed.

End Extend.

Arguments extend G {B} R.

Lemma sum_if_eq (T : finType) (g : T -> nat) i : \sum_b (if b == i then g b else 0) = g i.
Proof. by rewrite -big_mkcond big_pred1_eq. Qed.

Lemma sum_if_ne (T : finType) (g : T -> nat) i :
  \sum_b (if b != i then g b else 0) + g i = \sum_b g b.
Proof. by rewrite -big_mkcond [RHS](bigD1 i) //= addnC. Qed.

(** * Sums of labels given by the paper's indices *)

(* three values of a sum over the vertices: g(1) + g(2) + g(q) <= sum g for q >= 3 *)
Lemma sum_ord3 q (g : nat -> nat) : 3 <= q -> g 1 + g 2 + g q <= \sum_(i < q) g i.+1.
Proof.
case: q => [|[|[|q]]] // _.
rewrite big_ord_recr !big_ord_recl /= /bump /= addn0; nlia.
Qed.

(* if all the values are positive and the last one is at least 2 *)
Lemma sum_ord_last q (g : nat -> nat) : 0 < q ->
  (forall i, 1 <= i <= q -> 0 < g i) -> 2 <= g q -> q.+1 <= \sum_(i < q) g i.+1.
Proof.
case: q => // q _ h1 h2; rewrite big_ord_recr -addn2.
apply: leq_add; last exact: h2.
rewrite -[X in X <= _]card_ord -sum1_card; apply: leq_sum => i _; apply: h1.
by rewrite /=; have := ltn_ord i; nlia.
Qed.

(** * Thin and thick headless spiders *)

(* the thin headless spider of order q: u_i adjacent to v_i *)
Definition thin_spider q := extend 'K_q (fun i j : 'I_q => i == j).

(* the thick headless spider of order q: u_i adjacent to v_j for i <> j *)
Definition thick_spider q := extend 'K_q (fun i j : 'I_q => i != j).

(* a labeling given by functions of the paper's indices: f(u_i) = fu i, f(v_i) = fv i *)
Definition splab q (fu fv : nat -> nat) (x : ('I_q + 'I_q)%type) : nat :=
  match x with inl i => fu i.+1 | inr i => fv i.+1 end.

Arguments splab : clear implicits.

(* the clique u_1, ..., u_q *)
Definition uclique q : {set ('I_q + 'I_q)%type} := [set inl i | i : 'I_q].

Lemma uclique_card q : #|uclique q| = q.
Proof. by rewrite card_imset ?card_ord // => i j []. Qed.

Lemma uclique_clique q (R : 'I_q -> 'I_q -> bool) :
  @clique (extend 'K_q R) (uclique q).
Proof. by move=> _ _ /imsetP[i _ ->] /imsetP[j _ ->]; rewrite /= /complete_rel => /eqP h; apply/eqP => e; apply: h; rewrite e. Qed.

Section Spiders.

Variable q : nat.

Lemma thin_sumN_inl f (i : 'I_q) :
  sumN (thin_spider q) f (inl i) + f (inl i) = \sum_a f (inl a) + f (inr i).
Proof.
rewrite extend_sumN_inl /=.
have -> : \sum_b (if i == b then f (inr b) else 0) = f (inr i).
  by rewrite -(sum_if_eq (fun b => f (inr b)) i); apply: eq_bigr => b _; rewrite eq_sym.
by rewrite addnAC complete_sumN.
Qed.

Lemma thin_sumN_inr f (j : 'I_q) : sumN (thin_spider q) f (inr j) = f (inl j).
Proof. by rewrite extend_sumN_inr sum_if_eq. Qed.

Lemma thick_sumN_inl f (i : 'I_q) :
  sumN (thick_spider q) f (inl i) + f (inl i) + f (inr i) =
  \sum_a f (inl a) + \sum_b f (inr b).
Proof.
have e : \sum_b (if i != b then f (inr b) else 0) = \sum_b (if b != i then f (inr b) else 0).
  by apply: eq_bigr => b _; rewrite eq_sym.
have /= h1 := complete_sumN (fun x => f (inl x)) i.
have /= h2 := sum_if_ne (fun b => f (inr b)) i.
by rewrite extend_sumN_inl /= e; nlia.
Qed.

Lemma thick_sumN_inr f (j : 'I_q) :
  sumN (thick_spider q) f (inr j) + f (inl j) = \sum_a f (inl a).
Proof. by rewrite extend_sumN_inr sum_if_ne. Qed.

Lemma splab_labeling (R : 'I_q -> 'I_q -> bool) k fu fv :
  (forall i, 1 <= i <= q -> 0 < fu i <= k) -> (forall i, 1 <= i <= q -> 0 < fv i <= k) ->
  @labeling (extend 'K_q R) k (splab q fu fv).
Proof. by move=> hu hv [i|i] /=; [apply: hu | apply: hv]; have := ltn_ord i; nlia. Qed.

Lemma uclique_deg (R : 'I_q -> 'I_q -> bool) d :
  (forall i, deg (extend 'K_q R) (inl i) = d) ->
  {in uclique q, forall v, deg (extend 'K_q R) v = d}.
Proof. by move=> h _ /imsetP[i _ ->]. Qed.

End Spiders.

(* Proposition 3, thin spiders: eta = ceil((q + 1)/2) for q >= 2 *)
Theorem proposition_3_thin q : 2 <= q -> eta (thin_spider q) = cdiv (q + 1) 2.
Proof.
move=> hq; have hr : cdiv (q + 1) 2 = q.+2 %/ 2 by rewrite /cdiv; nlia.
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  (* lower bound: Corollary 2 on the clique u_1, ..., u_q, where d(u_i) = q *)
  have hd i : deg (thin_spider q) (inl i) = q.
    have := thin_sumN_inl (fun _ => 1) i; rewrite sumN_one sum_nat_const card_ord.
    by nlia.
  have Q0 : 0 < #|uclique q| by rewrite uclique_card; nlia.
  have := corollary_2_eq (@uclique_clique q _) Q0 (uclique_deg hd).
  by rewrite uclique_card (_ : q + 2 - q = 2) //; nlia.
rewrite hr; case: (ltngtP q 2) => [|hq3|q2]; first by nlia.
  (* q >= 3: the labeling of the appendix, with r = (q + 2)/2 *)
  set r := q.+2 %/ 2.
  pose fu i := if i <= r then r - i + 1 else q - i + 1.
  pose fv i := if i <= r then 1 else q.+1 %/ 2.
  pose f := splab q fu fv.
  have key i : 1 <= i <= q -> fv i + r = fu i + i by rewrite /fu /fv /r; split_lia.
  have FU : 2 * r <= \sum_(i < q) fu i.+1.
    have := sum_ord3 fu hq3; rewrite /fu /r; split_lia.
  set SU := \sum_(i < q) fu i.+1 in FU.
  have su (i : 'I_q) : sumN (thin_spider q) f (inl i) + r = SU + i.+1.
    have := thin_sumN_inl f i; have := key i.+1 (ltac:(have := ltn_ord i; nlia)).
    by rewrite /f /= -/SU; nlia.
  apply: (eta_le_lab (G := thin_spider q) (f := f)); first by rewrite /r; nlia.
    by apply: splab_labeling => i hi; rewrite /fu /fv /r; split_lia.
  have uv (i : 'I_q) : sumN (thin_spider q) f (inr i) < sumN (thin_spider q) f (inl i).
    rewrite thin_sumN_inr (_ : f (inl i) = fu i.+1) //; have := su i.
    have : fu i.+1 <= r by rewrite /fu; split_lia.
    nlia.
  move=> [i|i] [j|j] //= h.
  - have := su i; have := su j; move: h; rewrite /complete_rel -(inj_eq val_inj) /=; nlia.
  - by move: h => /eqP <-; rewrite neq_ltn uv orbT.
  - by move: h => /eqP ->; rewrite neq_ltn uv.
(* q = 2: f(u_i) = 1, f(v_1) = 1, f(v_2) = 2 *)
subst q; pose fv i := if i == 2 then 2 else 1.
apply: (eta_le_lab (G := thin_spider 2) (f := splab 2 (fun _ => 1) fv)) => //.
  by apply: splab_labeling => i; rewrite /fv; split_lia.
have S (i : 'I_2) : sumN (thin_spider 2) (splab 2 (fun _ => 1) fv) (inl i) = 1 + fv i.+1.
  have := thin_sumN_inl (splab 2 (fun _ => 1) fv) i.
  by rewrite big_ord_recr big_ord1 /=; nlia.
move=> [i|i] [j|j] //= h; rewrite ?S ?thin_sumN_inr /=.
- by move: h; rewrite /complete_rel /fv; case: i => [[|[|]]] //= ?; case: j => [[|[|]]].
- by rewrite /fv; split_lia.
by rewrite /fv; split_lia.
Qed.

(* Proposition 3, thick spiders: eta = ceil((q + 1)/2) for q >= 2 *)
Theorem proposition_3_thick q : 2 <= q -> eta (thick_spider q) = cdiv (q + 1) 2.
Proof.
move=> hq; have hr : cdiv (q + 1) 2 = q.+2 %/ 2 by rewrite /cdiv; nlia.
rewrite hr; apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  (* lower bound: f(u_i) + f(v_i) takes q distinct values in [2, 2k] *)
  apply: le_eta => k f k0 [fl fs].
  pose g (i : 'I_q) := f (inl i) + f (inr i).
  have inj : {in predT &, injective g}.
    move=> i j _ _ e; apply/eqP; apply/negPn/negP => ij.
    have := thick_sumN_inl f i; have := thick_sumN_inl f j.
    have := fs (inl i) (inl j); rewrite /= /complete_rel ij => /(_ isT).
    by move: e; rewrite /g; nlia.
  have := @card_le_interval _ predT g 2 (2 * k) inj.
  rewrite cardT size_enum_ord => h.
  have : q <= (2 * k).+1 - 2.
    by apply: h => i _; rewrite /g; have := fl (inl i); have := fl (inr i); nlia.
  by nlia.
case: (ltngtP q 2) => [|hq3|q2]; first by nlia.
  (* q >= 3: the labeling of the appendix *)
  set r := q.+2 %/ 2.
  pose fu i := if i <= r then i else r.
  pose fv i := if i <= r then 1 else i - r + 1.
  pose f := splab q fu fv.
  have key i : fu i + fv i = i + 1 by rewrite /fu /fv; split_lia.
  have FV : q.+1 <= \sum_(i < q) fv i.+1.
    by apply: sum_ord_last; rewrite /fv /r; [nlia | move=> i; split_lia | split_lia].
  set SU := \sum_(i < q) fu i.+1; set SV := \sum_(i < q) fv i.+1 in FV.
  have su (i : 'I_q) : sumN (thick_spider q) f (inl i) + i.+1 + 1 = SU + SV.
    by have := thick_sumN_inl f i; rewrite /f /= -/SU -/SV; have := key i.+1; nlia.
  have sv (j : 'I_q) : sumN (thick_spider q) f (inr j) + fu j.+1 = SU.
    by have := thick_sumN_inr f j; rewrite /f /= -/SU.
  apply: (eta_le_lab (G := thick_spider q) (f := f)); first by rewrite /r; nlia.
    by apply: splab_labeling => i hi; rewrite /fu /fv /r; split_lia.
  have uv (i j : 'I_q) : sumN (thick_spider q) f (inr j) < sumN (thick_spider q) f (inl i).
    have := su i; have := sv j; have : 0 < fu j.+1 by rewrite /fu; split_lia.
    by have := ltn_ord i; nlia.
  move=> [i|i] [j|j] //= h.
  - have := su i; have := su j; move: h; rewrite /complete_rel -(inj_eq val_inj) /=; nlia.
  - by rewrite neq_ltn uv orbT.
  - by rewrite neq_ltn uv.
(* q = 2: f(u_i) = 1, f(v_1) = 2, f(v_2) = 1 *)
subst q; pose fv i := if i == 1 then 2 else 1.
apply: (eta_le_lab (G := thick_spider 2) (f := splab 2 (fun _ => 1) fv)) => //.
  by apply: splab_labeling => i; rewrite /fv; split_lia.
have Su (i : 'I_2) :
    sumN (thick_spider 2) (splab 2 (fun _ => 1) fv) (inl i) + 1 + fv i.+1 = 5.
  have := thick_sumN_inl (splab 2 (fun _ => 1) fv) i.
  by rewrite !big_ord_recr !big_ord0 /= /fv; nlia.
have Sv (j : 'I_2) : sumN (thick_spider 2) (splab 2 (fun _ => 1) fv) (inr j) = 1.
  have := thick_sumN_inr (splab 2 (fun _ => 1) fv) j.
  by rewrite !big_ord_recr big_ord0 /=; nlia.
have fv2 (i : 'I_2) : fv i.+1 <= 2 by rewrite /fv; split_lia.
move=> [i|i] [j|j] //= h.
- have := Su i; have := Su j; move: h; rewrite /complete_rel /fv.
  by case: i => [[|[|]]] //= ?; case: j => [[|[|]]] //= ?; nlia.
- by rewrite Sv; have := Su i; have := fv2 i; nlia.
by rewrite Sv; have := Su j; have := fv2 j; nlia.
Qed.

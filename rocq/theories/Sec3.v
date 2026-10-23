(* Section 3: join with complete graphs.
   Observation 2 (true twins), Theorem 2 (eta(G v K_q) = max {eta(G), q}),
   chi(G v K_q) >= chi(G) + q, and the conjecture for G v K_q. *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics Sec2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * Observation 2: true twins *)

Section Twins.

Variable G : sgraph.

Lemma true_twins_adj u v : true_twins G u v -> u != v -> u -- v.
Proof.
move=> tt uv; have : v \in u |: N(G; u) by rewrite tt setU11.
by rewrite in_setU1 in_nbh eq_sym (negbTE uv).
Qed.

(* an additive coloring gives different labels to true twins *)
Lemma acol_true_twins k f u v : additive_coloring G k f -> true_twins G u v -> u != v ->
  f u != f v.
Proof.
move=> [_ fs] tt uv; apply/eqP => e.
have := sum_closed_nbh f u; rewrite tt sum_closed_nbh e => /addnI e'.
by move: (fs u v (true_twins_adj tt uv)); rewrite e' eqxx.
Qed.

(* Observation 2: if the vertices of T are pairwise true twins, then eta(G) >= |T| *)
Theorem observation_2 (T : {set G}) :
  {in T &, forall u v, true_twins G u v} -> #|T| <= eta G.
Proof.
move=> hT; apply: le_eta => k f _ hf.
have := @card_le_interval _ T f 1 k; rewrite subn1 /=; apply.
  move=> u v uT vT e; apply/eqP; apply/negPn/negP => uv.
  by move: (acol_true_twins hf (hT u v uT vT) uv); rewrite e eqxx.
by move=> u _; case: hf => /(_ u).
Qed.

End Twins.

(** * The join G v H

   (The library's G ∔ H, sjoin, is the disjoint union, without the edges between G and H.) *)

Section Join.

Variables (G H : sgraph).

Definition gjoin_rel : rel (G + H)%type := fun x y =>
  match x, y with
  | inl a, inl b => a -- b
  | inr a, inr b => a -- b
  | _, _ => true
  end.

Lemma gjoin_sym : symmetric gjoin_rel.
Proof. by move=> [a|a] [b|b] //=; rewrite adj_sym. Qed.

Lemma gjoin_irr : irreflexive gjoin_rel.
Proof. by move=> [a|a] /=; rewrite adj_irr. Qed.

(* the join: the disjoint union of G and H plus all edges between them *)
Definition gjoin := SGraph gjoin_sym gjoin_irr.

Lemma gjoin_sumN_inl f a :
  sumN gjoin f (inl a) = sumN G (fun x => f (inl x)) a + \sum_b f (inr b).
Proof. by rewrite sumN_mkcond big_sumType /= sumN_mkcond. Qed.

Lemma gjoin_sumN_inr f b :
  sumN gjoin f (inr b) = \sum_a f (inl a) + sumN H (fun x => f (inr x)) b.
Proof. by rewrite sumN_mkcond big_sumType /= sumN_mkcond. Qed.

End Join.

(** * The complete graph K_q of the library *)

(* f(N(a)) + f(a) = f(V) in a complete graph *)
Lemma complete_sumN n (g : 'K_n -> nat) a : sumN 'K_n g a + g a = \sum_x g x.
Proof.
rewrite /sumN [RHS](bigD1 a) //= addnC; congr (_ + _).
by apply: eq_bigl => x; rewrite /open_neigh inE /= eq_sym.
Qed.

(* G v K_q, on G + 'I_q *)
Definition joinK (G : sgraph) (q : nat) := gjoin G 'K_q.

(** * Theorem 2: eta(G v K_q) = max {eta(G), q} for q <= n - Delta - 1 *)

Section Theorem2.

Variables (G : sgraph) (q : nat).

Lemma joinK_sumN_inr f u :
  sumN (joinK G q) f (inr u) + f (inr u) = \sum_a f (inl a) + \sum_b f (inr b).
Proof. by rewrite gjoin_sumN_inr -addnA complete_sumN. Qed.

Lemma joinK_sumN_inr_eq f a b :
  sumN (joinK G q) f (inr a) + f (inr a) = sumN (joinK G q) f (inr b) + f (inr b).
Proof. by rewrite !joinK_sumN_inr. Qed.

(* f(N(v)) + f(V - N(v)) = f(V) *)
Lemma sumN_compl (g : G -> nat) v : sumN G g v + \sum_(x | x \notin N(G; v)) g x = \sum_x g x.
Proof. by rewrite [RHS](bigID (fun x => x \in N(G; v))). Qed.

(* In G v K_q every edge between V and K_q goes from the smaller to the larger sum, when f
   labels V with positive numbers and K_q with [q], and q <= n - Delta - 1. *)
Lemma joinK_sumN_lt (f : (G + 'I_q)%type -> nat) v u :
  q <= #|G| - maxdeg G - 1 -> (forall v, 0 < f (inl v)) -> (forall w, f (inr w) <= q) ->
  sumN (joinK G q) f (inl v) < sumN (joinK G q) f (inr u).
Proof.
move=> hq h1 h2.
have h3 := joinK_sumN_inr f u; rewrite gjoin_sumN_inl.
have /= h4 := sumN_compl (fun x => f (inl x)) v.
have h5 : #|G| - deg G v <= \sum_(x | x \notin N(G; v)) f (inl x).
  have e : #|G| - deg G v = \sum_(x | x \notin N(G; v)) 1.
    rewrite -(cardsC (N(G; v))) /deg addKn -sum1_card; apply: eq_bigl => x.
    by rewrite inE.
  by rewrite e; apply: leq_sum => x _; exact: h1.
set SW := \sum_(b < q) f (inr b) in h3 *.
set SV := \sum_x f (inl x) in h3 h4.
have := deg_le_maxdeg v; have := h2 u; have := ltn_ord u.
set X := sumN (joinK G q) f (inr u) in h3 *; set fu := f (inr u) in h3 *; nlia.
Qed.

(* Theorem 2 *)
Theorem theorem_2 : q <= #|G| - maxdeg G - 1 -> eta (joinK G q) = maxn (eta G) q.
Proof.
move=> hq; apply/eqP; rewrite eqn_leq; apply/andP; split.
  (* an additive coloring of the join: an optimal f on G, and 1, ..., q on K_q *)
  case: (eta_attained G) => f [fl fs].
  pose f' (x : (G + 'I_q)%type) := match x with inl v => f v | inr w => w.+1 end.
  have hV v : 0 < f' (inl v) by case/andP: (fl v).
  have hW w : f' (inr w) <= q by exact: ltn_ord.
  apply: (eta_le_lab (G := joinK G q) (f := f')); first by have := eta_pos G; lia.
    by case=> [v|w] /=; [have := fl v | have := ltn_ord w]; lia.
  case=> [a|a] [b|b] /= ab.
  - by rewrite !gjoin_sumN_inl eqn_add2r; exact: fs.
  - by rewrite neq_ltn joinK_sumN_lt.
  - by rewrite neq_ltn joinK_sumN_lt ?orbT.
  - have := joinK_sumN_inr_eq f' a b => /=.
    have ab' : (a : nat) != b by move: ab; rewrite /= /complete_rel; apply: contra => /eqP e; apply/eqP; exact: val_inj.
    by move: ab'; rewrite /reverse_coercion; lia.
rewrite geq_max; apply/andP; split.
  (* an additive coloring of the join restricts to an additive coloring of G *)
  apply: le_eta => k f k0 [fl fs]; apply: (eta_le_lab (f := fun x => f (inl x))) => //.
  by move=> a b ab; have := fs (inl a) (inl b) ab; rewrite !gjoin_sumN_inl eqn_add2r.
(* the vertices of K_q are pairwise true twins *)
have := @observation_2 (joinK G q) [set inr w | w : 'I_q].
have inj : injective (fun w : 'I_q => @inr G 'I_q w) by move=> x y [].
rewrite card_imset // card_ord.
apply=> _ _ /imsetP[a _ ->] /imsetP[b _ ->].
have N (x : 'I_q) : inr x |: N((joinK G q); (inr x)) = setT.
  apply/setP => -[y|y]; rewrite !inE //=.
  rewrite /complete_rel; case: (x =P y) => [->|ne]; first by rewrite eqxx.
  by apply/orP; right; apply/negP => /eqP e; apply: ne.
by rewrite /true_twins !N.
Qed.

(* chi(G v K_q) >= chi(G) + q (the paper uses equality) *)
Lemma chi_joinK : chi G + q <= chi (joinK G q).
Proof.
case: (chi_attained (joinK G q)) => c hc; set k := chi (joinK G q) in c hc *.
pose S := [set c (inr w) | w : 'I_q].
have cS : #|S| = q.
  rewrite card_imset ?card_ord // => a b e; apply/eqP; apply/negPn/negP => ab.
  by move: (hc (inr a) (inr b) ab); rewrite e eqxx.
have notS v : c (inl v) \in ~: S.
  rewrite inE; apply/imsetP => -[w _ e].
  by move: (hc (inl v) (inr w) isT); rewrite e eqxx.
have cC : #|~: S| = k - q by have := cardsC S; rewrite card_ord cS; lia.
case: (posnP #|G|) => [V0 | /card_gt0P[v0 _]].
  have : chi G <= #|G|.
    by apply: (chi_le (c := enum_rank)) => u v uv; rewrite (inj_eq enum_rank_inj) (adj_ne uv).
  by have := max_card S; rewrite card_ord cS; lia.
pose c' v : 'I_#|~: S| := enum_rank_in (notS v0) (c (inl v)).
have : chi G <= #|~: S|.
  apply: (chi_le (c := c')) => u v uv; apply/eqP => e.
  move/(congr1 enum_val): e; rewrite /c' !enum_rankK_in // => /eqP.
  by apply/negP; exact: (hc (inl u) (inl v) uv).
by rewrite cC; have := max_card S; rewrite card_ord cS; lia.
Qed.

(* if the conjecture holds for G, it holds for G v K_q *)
Corollary theorem_2_conjecture :
  q <= #|G| - maxdeg G - 1 -> eta G <= chi G -> eta (joinK G q) <= chi (joinK G q).
Proof. by move=> hq h; rewrite theorem_2 //; have := chi_joinK; lia. Qed.

End Theorem2.

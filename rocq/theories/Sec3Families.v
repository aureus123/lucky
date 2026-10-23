(* Section 3: fans, windmills and wheels, and Proposition 1 (odd cycles).
   Paths and cycles are graphs on 'I_N; the vertex k is the paper's v_(k+1).  Labelings of
   these graphs are given by functions on the indices. *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics Sec2 Sec3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * Sums over neighborhoods in graphs on 'I_N *)

(* f(N(i)) in a graph on 'I_N whose adjacency is a predicate on the indices *)
Lemma sumN_ord N (r : rel 'I_N) (rs : symmetric r) (ri : irreflexive r) (P : pred nat)
  (F : nat -> nat) (i : 'I_N) :
  (forall j : 'I_N, r i j = P j) ->
  sumN (SGraph rs ri) (fun j => F j) i = \sum_(k < N) (if P k then F k else 0).
Proof. by move=> h; rewrite sumN_mkcond; apply: eq_bigr => j _; rewrite -h. Qed.

Lemma sum_ord_eq1 N (F : nat -> nat) a :
  \sum_(k < N) (if k == a :> nat then F k else 0) = if a < N then F a else 0.
Proof. by elim: N => [|N IH]; rewrite ?big_ord0 ?big_ord_recr /= ?IH; split_lia. Qed.

Lemma sum_ord_or N (F : nat -> nat) a b : a != b ->
  \sum_(k < N) (if (k == a :> nat) || (k == b :> nat) then F k else 0) =
  (if a < N then F a else 0) + (if b < N then F b else 0).
Proof.
by move=> ab; elim: N => [|N IH]; rewrite ?big_ord0 ?big_ord_recr /= ?IH; split_lia.
Qed.

(* joining one vertex to a graph without universal vertices keeps eta *)
Lemma theorem_2_K1 (G : sgraph) :
  maxdeg G + 2 <= #|G| -> eta (joinK G 1) = eta G.
Proof.
move=> h; rewrite theorem_2; first by lia.
by have := eta_pos G; lia.
Qed.

(** * Paths and fans *)

Definition path_rel N : rel 'I_N := fun i j => (i.+1 == j) || (j.+1 == i).

Lemma path_sym N : symmetric (@path_rel N).
Proof. by move=> i j; rewrite /path_rel orbC. Qed.

Lemma path_irr N : irreflexive (@path_rel N).
Proof. by move=> i; rewrite /path_rel; lia. Qed.

(* the path P_N *)
Definition pathG N := SGraph (@path_sym N) (@path_irr N).

(* f(N(i)) in P_N *)
Lemma path_sumN N (F : nat -> nat) (i : 'I_N) :
  sumN (pathG N) (fun j => F j) i =
  (if 0 < i then F i.-1 else 0) + (if i.+1 < N then F i.+1 else 0).
Proof.
rewrite /pathG (@sumN_ord N _ _ _ (fun k => (i.+1 == k) || (k.+1 == i)) F i (fun j => erefl)).
have := ltn_ord i; case: (posnP i) => [i0 | ipos] hi.
  have -> : \sum_(k < N) (if (i.+1 == k) || (k.+1 == i) then F k else 0) =
            \sum_(k < N) (if k == i.+1 :> nat then F k else 0).
    by apply: eq_bigr => k _; split_lia.
  by rewrite sum_ord_eq1; split_lia.
have -> : \sum_(k < N) (if (i.+1 == k) || (k.+1 == i) then F k else 0) =
          \sum_(k < N) (if (k == i.-1 :> nat) || (k == i.+1 :> nat) then F k else 0).
  by apply: eq_bigr => k _; split_lia.
by rewrite sum_ord_or; split_lia.
Qed.

Lemma path_deg N (i : 'I_N) :
  deg (pathG N) i = (if 0 < i then 1 else 0) + (if i.+1 < N then 1 else 0).
Proof. by rewrite -sumN_one (path_sumN (fun _ => 1)). Qed.

Lemma path_maxdeg N : maxdeg (pathG N) <= 2.
Proof. by apply: maxdeg_le => i; rewrite path_deg; split_lia. Qed.

(* eta(P_N) = 2 for N >= 4 (the paper uses the bound for trees of ref. [5]).  Labeling: 2
   on the even vertices and on the last one, 1 elsewhere. *)
Lemma path_eta N : 4 <= N -> eta (pathG N) = 2.
Proof.
move=> hN.
pose F j := if (j %% 2 == 0) || (j == N.-1) then 2 else 1.
pose S a := (if 0 < a then F a.-1 else 0) + (if a.+1 < N then F a.+1 else 0).
have hS a : a.+1 < N -> S a != S a.+1 by rewrite /S /F; split_lia.
have le2 : eta (pathG N) <= 2.
  apply: (eta_le_lab (G := pathG N) (f := fun j : 'I_N => F j)) => // [j | i j].
    by rewrite /F; split_lia.
  rewrite !(path_sumN F) -/(S i) -/(S j) /= /path_rel.
  case/orP => /eqP e.
    by have := hS i; rewrite e => /(_ (ltn_ord j)).
  by have := hS j; rewrite e eq_sym => /(_ (ltn_ord i)).
have h1 : 1 < N by lia.
have h2 : 2 < N by lia.
apply: (eta_eq_two (G := pathG N) (u := Ordinal h1) (v := Ordinal h2)) => //.
by rewrite !path_deg /=; split_lia.
Qed.

(* fans: eta(F_n) = eta(P_(n+1) v K_1) = 2 for n >= 3 *)
Theorem fan n : 3 <= n -> eta (joinK (pathG n.+1) 1) = 2.
Proof.
move=> hn; have h : maxdeg (pathG n.+1) + 2 <= #|'I_n.+1|.
  by have := path_maxdeg n.+1; rewrite card_ord; lia.
by rewrite (theorem_2_K1 h) path_eta //; lia.
Qed.

(** * Windmills *)

(* m K_p: m disjoint copies of K_p; the vertex (i, j) is the j-th vertex of copy i *)
Definition copies_rel m p : rel ('I_m * 'I_p)%type :=
  fun x y => (x.1 == y.1) && (x.2 != y.2).

Lemma copies_sym m p : symmetric (@copies_rel m p).
Proof. by move=> x y; rewrite /copies_rel eq_sym [x.2 == _]eq_sym. Qed.

Lemma copies_irr m p : irreflexive (@copies_rel m p).
Proof. by move=> x; rewrite /copies_rel !eqxx. Qed.

Definition copiesK m p := SGraph (@copies_sym m p) (@copies_irr m p).

Section Copies.

Variables m p : nat.

(* the closed neighborhood of x is its copy *)
Lemma copies_adj (x y : 'I_m * 'I_p) :
  (x -- y :> copiesK m p) = (x.1 == y.1) && (x.2 != y.2).
Proof. by []. Qed.

Lemma copies_closed_nbh (x : 'I_m * 'I_p) :
  x |: N((copiesK m p); x) = [set (x.1, j) | j : 'I_p].
Proof.
case: x => x1 x2; apply/setP => -[a b]; rewrite in_setU1 /open_neigh inE copies_adj /= xpair_eqE.
have -> : ((a, b) \in [set (x1, j) | j : 'I_p]) = (a == x1).
  by apply/imsetP/eqP => [[j _ [-> _]] | ->] //; exists b.
by rewrite [x1 == a]eq_sym [x2 == b]eq_sym; case: (a == x1); case: (b == x2).
Qed.

Lemma copies_sumN f x : sumN (copiesK m p) f x + f x = \sum_j f (x.1, j).
Proof.
rewrite addnC -sum_closed_nbh copies_closed_nbh big_imset //.
by move=> i j _ _ [].
Qed.

Lemma copies_sumN_eq f x y : x.1 = y.1 ->
  sumN (copiesK m p) f x + f x = sumN (copiesK m p) f y + f y.
Proof. by move=> e; rewrite !copies_sumN e. Qed.

Lemma copies_deg x : deg (copiesK m p) x = p.-1.
Proof.
have := copies_sumN (fun _ => 1) x; rewrite sumN_one sum1_card card_ord.
by lia.
Qed.

(* eta(m K_p) = p *)
Lemma copies_eta : 0 < m -> 0 < p -> eta (copiesK m p) = p.
Proof.
move=> m0 p0; apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply: (eta_le_lab (G := copiesK m p) (f := fun x => (x.2 : nat).+1)) => // [x | x y].
    by have := ltn_ord x.2; lia.
  rewrite /= /copies_rel => /andP[/eqP e ne].
  have /= E := copies_sumN_eq (fun x => (x.2 : nat).+1) e.
  have ne' : (x.2 : nat) != y.2 by apply: contra ne => /eqP/val_inj ->.
  by move: ne' E; rewrite /=; nlia.
pose x0 : 'I_m * 'I_p := (Ordinal m0, Ordinal p0).
have := @observation_2 (copiesK m p) [set (x0.1, j) | j : 'I_p].
have inj : injective (fun j : 'I_p => (x0.1, j)) by move=> i j [].
rewrite card_imset // card_ord.
apply=> _ _ /imsetP[a _ ->] /imsetP[b _ ->].
by rewrite /true_twins !copies_closed_nbh.
Qed.

End Copies.

(* windmills: eta(W_n^m) = eta(m K_(n-1) v K_1) = n - 1 for n >= 3, m >= 2 *)
Theorem windmill n m : 3 <= n -> 2 <= m -> eta (joinK (copiesK m n.-1) 1) = n.-1.
Proof.
move=> hn hm.
have hdeg : maxdeg (copiesK m n.-1) <= n.-2.
  by apply: maxdeg_le => x; rewrite copies_deg.
have hcard : 2 * n.-1 <= m * n.-1 by rewrite leq_mul2r hm orbT.
rewrite theorem_2_K1 ?copies_eta //; try lia.
by rewrite card_prod !card_ord; lia.
Qed.

(** * Cycles and wheels *)

(* successor and predecessor modulo n *)
Definition csucc (n i : nat) : nat := if i.+1 == n then 0 else i.+1.
Definition cpred (n i : nat) : nat := if i == 0 then n.-1 else i.-1.

Lemma csucc_lt n i : i < n -> csucc n i < n.
Proof. by rewrite /csucc; split_lia. Qed.

Lemma cpred_lt n i : i < n -> cpred n i < n.
Proof. by rewrite /cpred; split_lia. Qed.

Definition cycle_rel n : rel 'I_n :=
  fun i j => (i != j :> nat) && ((j == csucc n i :> nat) || (i == csucc n j :> nat)).

Lemma cycle_sym n : symmetric (@cycle_rel n).
Proof. by move=> i j; rewrite /cycle_rel eq_sym orbC. Qed.

Lemma cycle_irr n : irreflexive (@cycle_rel n).
Proof. by move=> i; rewrite /cycle_rel eqxx. Qed.

(* the cycle C_n *)
Definition cycleG n := SGraph (@cycle_sym n) (@cycle_irr n).

Section Cycles.

Variable n : nat.
Hypothesis hn : 3 <= n.

Lemma cycle_adj (i j : 'I_n) :
  (i -- j :> cycleG n) = (j == csucc n i :> nat) || (j == cpred n i :> nat).
Proof.
rewrite (_ : (i -- j :> cycleG n) = cycle_rel i j) // /cycle_rel /csucc /cpred.
by have := ltn_ord i; have := ltn_ord j; split_lia.
Qed.

(* f(N(i)) in C_n *)
Lemma cycle_sumN (F : nat -> nat) (i : 'I_n) :
  sumN (cycleG n) (fun j => F j) i = F (csucc n i) + F (cpred n i).
Proof.
rewrite /cycleG (@sumN_ord n _ _ _ (fun k => (k == csucc n i) || (k == cpred n i)) F i (cycle_adj i)).
have ne : csucc n i != cpred n i by rewrite /csucc /cpred; have := ltn_ord i; split_lia.
rewrite (sum_ord_or _ _ ne).
by rewrite csucc_lt ?cpred_lt.
Qed.

Lemma cycle_deg i : deg (cycleG n) i = 2.
Proof. by rewrite -sumN_one (cycle_sumN (fun _ => 1)). Qed.

Lemma cycle_maxdeg : maxdeg (cycleG n) <= 2.
Proof. by apply: maxdeg_le => i; rewrite cycle_deg. Qed.

(* even cycles are regular bipartite, so Corollary 1 applies *)
Lemma cycle_eta_even : ~~ odd n -> eta (cycleG n) = 2.
Proof.
move=> ev; have h0 : 0 < n by lia.
have h1 : 1 < n by lia.
apply: (corollary_1 (G := cycleG n) (U := [set j : 'I_n | ~~ odd j]) (W := [set j : 'I_n | odd j])
                    (a := Ordinal h0) (b := Ordinal h1)).
- by move=> v; rewrite !inE negbK.
- move=> u v; rewrite cycle_adj !inE /csucc /cpred.
  by have := ltn_ord u; have := ltn_ord v; split_lia.
- by move=> u v; rewrite !cycle_deg.
by rewrite cycle_adj /csucc /=; split_lia.
Qed.

End Cycles.

(** * Successor and predecessor in 'I_n *)

Section Ord.

Variable n : nat.

(* the successor and the predecessor in 'I_n *)
Definition osucc (i : 'I_n) : 'I_n := Ordinal (csucc_lt (ltn_ord i)).
Definition opred (i : 'I_n) : 'I_n := Ordinal (cpred_lt (ltn_ord i)).

Lemma opred_osucc i : opred (osucc i) = i.
Proof. by apply: val_inj; rewrite /= /cpred /csucc; have := ltn_ord i; split_lia. Qed.

Lemma osucc_opred i : osucc (opred i) = i.
Proof. by apply: val_inj; rewrite /= /cpred /csucc; have := ltn_ord i; split_lia. Qed.

End Ord.

(** * Proposition 1: odd cycles *)

(* the labeling of the appendix for odd cycles; the vertex k is the paper's v_(k+1) *)
Definition p1F (k : nat) : nat :=
  if k == 0 then 2 else if k == 2 then 3 else if k <= 4 then 1
  else if odd k then 1 else 3.

(* the sums f(N(v_(k+1))) of that labeling *)
Definition p1S (n k : nat) : nat :=
  if k == 0 then (if n == 5 then 2 else 4) else if k == 1 then 5 else if k == 2 then 2
  else if k == 3 then 4 else if k == n.-1 then 3 else if ~~ odd k then 2
  else if k == 5 then 4 else 6.

Section Prop1.

Variable n : nat.
Hypotheses (hodd : odd n) (h5 : 5 <= n).

Lemma p1_sum k : k < n -> p1F (csucc n k) + p1F (cpred n k) = p1S n k.
Proof. by rewrite /p1F /p1S /csucc /cpred; split_lia. Qed.

Lemma p1_ne k : k < n -> p1S n k != p1S n (csucc n k).
Proof. by rewrite /p1S /csucc; split_lia. Qed.

Lemma cycle_adj_succ (i : 'I_n) : (i -- (osucc i) :> cycleG n).
Proof. by rewrite cycle_adj ?eqxx //; lia. Qed.

(* Proposition 1: eta(C_n) = 3 for odd n >= 5 *)
Theorem proposition_1 : eta (cycleG n) = 3.
Proof.
have hn : 3 <= n by lia.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply: (eta_le_lab (G := cycleG n) (f := fun j : 'I_n => p1F j)) => // [j | i j].
    by rewrite /p1F; split_lia.
  rewrite !(cycle_sumN hn p1F) !p1_sum // cycle_adj //.
  case/orP => /eqP e; first by rewrite e p1_ne.
  have -> : (i : nat) = csucc n j by rewrite e /csucc /cpred; have := ltn_ord i; split_lia.
  by rewrite eq_sym p1_ne.
(* no additive 2-coloring: two consecutive arcs point the same way, since the orientation
   cannot alternate around an odd cycle; this forces a sum 2 and a sum 4 next to f(v) = 1
   and f(v) = 2 at once *)
rewrite ltnNge; apply/negP => le2.
case: (eta_attained (cycleG n)) => f hf.
have [fl fs] := additive_coloring_mono hf le2.
pose s (i : 'I_n) := f (osucc i) + f (opred i).
have hs i : sumN (cycleG n) f i = s i.
  have ne : osucc i != opred i.
    by apply/eqP => /(congr1 val) /=; rewrite /csucc /cpred; have := ltn_ord i; split_lia.
  have N j : (i -- j :> cycleG n) = (j \in [set osucc i; opred i]).
    by rewrite cycle_adj // !inE -!(inj_eq val_inj).
  by rewrite (sumN_of_nbh _ N) big_setU1 ?big_set1 // inE.
have adj_ne i : s i != s (osucc i) by rewrite -!hs; apply: fs; exact: cycle_adj_succ.
pose b i := s i < s (osucc i).
have [k /eqP hk] : exists k, b (opred k) == b k.
  case/boolP: [exists k, b (opred k) == b k] => [/existsP // | /existsPn no]; exfalso.
  have alt (i : 'I_n) : b (osucc i) = ~~ b i.
    by move: (no (osucc i)); rewrite opred_osucc; case: (b i); case: (b (osucc i)).
  have h0 : 0 < n by lia.
  have par k (hk : k < n) : b (Ordinal hk) = b (Ordinal h0) (+) odd k.
    elim: k hk => [|k IH] hk; first by rewrite addbF; congr b; exact: val_inj.
    have hk' : k < n by lia.
    have -> : Ordinal hk = osucc (Ordinal hk') by apply: val_inj; rewrite /= /csucc; split_lia.
    by rewrite alt IH /= addbN.
  have hl : n.-1 < n by lia.
  move: (no (Ordinal h0)).
  have -> : opred (Ordinal h0) = Ordinal hl by apply: val_inj.
  have o : odd n.-1 = false by lia.
  by rewrite (par _ hl) o addbF eqxx.
have A1 := adj_ne (opred k); have A2 := adj_ne k.
rewrite /b osucc_opred in hk; rewrite osucc_opred in A1.
move: A1 A2 hk; rewrite /s osucc_opred opred_osucc.
have := fl k; have := fl (osucc k); have := fl (opred k).
have := fl (osucc (osucc k)); have := fl (opred (opred k)).
move: (f k) (f (osucc k)) (f (opred k)) (f (osucc (osucc k))) (f (opred (opred k))).
by move=> a b1 c d e; nlia.
Qed.

End Prop1.

(* wheels: eta(W_n) = eta(C_n v K_1) = 2 for even n >= 4 and 3 for odd n >= 5 *)
Theorem wheel n : 4 <= n -> eta (joinK (cycleG n) 1) = if odd n then 3 else 2.
Proof.
move=> hn; have h : maxdeg (cycleG n) + 2 <= #|'I_n|.
  by have := @cycle_maxdeg n (ltac:(lia)); rewrite card_ord; lia.
rewrite (theorem_2_K1 h).
case: ifP => o; first by apply: proposition_1 => //; lia.
by apply: cycle_eta_even; [lia | rewrite o].
Qed.

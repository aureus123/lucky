(* Section 2: regular bipartite and complete multipartite graphs.
   Observation 1, Lemma 1, Corollary 1, Lemma 2 (ref. [6], Prop. 3, proved here) and
   Theorem 1. *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * Observation 1, Lemma 1 and Corollary 1 *)

Section Obs1.

Variable G : sgraph.

(* Observation 1: eta(G) = 1 iff adjacent vertices have different degrees *)
Theorem observation_1 : eta G = 1 <-> forall u v : G, u -- v -> deg G u != deg G v.
Proof.
split=> [e1 u v uv | h].
  case: (eta_attained G) => f [fl fs]; move: fl fs; rewrite e1 => fl fs.
  have s x : sumN G f x = deg G x.
    by rewrite -sumN_one; apply: sumN_eq => w; have := fl w; lia.
  by move: (fs u v uv); rewrite !s.
apply/eqP; rewrite eqn_leq eta_pos andbT.
apply: (eta_le_lab (f := fun _ => 1)) => //; try by [].
by move=> u v uv; rewrite !sumN_one; exact: h.
Qed.

Lemma two_le_eta u v : u -- v -> deg G u = deg G v -> 2 <= eta G.
Proof.
move=> uv d; have := eta_pos G; case e: (eta G) => [|[|n]] // _.
by move: (observation_1.1 e u v uv); rewrite d eqxx.
Qed.

(* eta(G) = 2 from eta(G) <= 2 and an edge whose ends have equal degrees *)
Lemma eta_eq_two u v : eta G <= 2 -> u -- v -> deg G u = deg G v -> eta G = 2.
Proof. by move=> h uv d; apply/eqP; rewrite eqn_leq h (two_le_eta uv d). Qed.

(* Lemma 1: a bipartite graph with sides U and W (the paper's U and V), where
   d(u) < 2 d(v) for every v in W and u in N(v).  Labeling: 2 on U, 1 on W. *)
Theorem lemma_1 (U W : {set G}) :
  (forall v, (v \in W) = (v \notin U)) ->
  (forall u v : G, u -- v -> (u \in U) = (v \in W)) ->
  (forall v u, v \in W -> v -- u -> deg G u < 2 * deg G v) ->
  eta G = if [forall u, [forall v, u -- v ==> (deg G u != deg G v)]] then 1 else 2.
Proof.
move=> part bip hdeg.
pose f v := if v \in U then 2 else 1.
have sU u : u \in U -> sumN G f u = deg G u.
  move=> uU; rewrite -sumN_one; apply: eq_bigr => w; rewrite in_nbh => uw.
  by move: (bip u w uw); rewrite uU part /f => /esym/negbTE->.
have sW v : v \in W -> sumN G f v = 2 * deg G v.
  move=> vW; have e : forall w, w \in N(G; v) -> f w = 2.
    by move=> w; rewrite in_nbh adj_sym => /bip; rewrite vW /f => ->.
  by rewrite /sumN (eq_bigr _ e) sum_nat_const mulnC.
have edge u v : u \in U -> v \in W -> u -- v -> sumN G f u < sumN G f v.
  by move=> uU vW uv; rewrite sU // sW // hdeg // adj_sym.
have le2 : eta G <= 2.
  apply: (eta_le_lab (f := f)) => // [v | u v uv]; first by rewrite /f; case: (v \in U).
  case uU: (u \in U).
    by rewrite neq_ltn edge // -(bip _ _ uv).
  have vU : v \in U by apply: negbFE; rewrite -part -(bip _ _ uv) uU.
  have uW : u \in W by rewrite part uU.
  have vu : v -- u by rewrite adj_sym.
  by rewrite neq_ltn (edge v u vU uW vu) orbT.
case: ifP => [/forallP h | /forallPn[u /forallPn[v]]].
  apply/observation_1 => u v uv.
  by move: (h u) => /forallP/(_ v)/implyP; apply.
by rewrite negb_imply negbK => /andP[uv /eqP d]; exact: eta_eq_two le2 uv d.
Qed.

(* Corollary 1: a regular bipartite graph with at least one edge has eta(G) = 2 *)
Corollary corollary_1 (U W : {set G}) (a b : G) :
  (forall v, (v \in W) = (v \notin U)) ->
  (forall u v : G, u -- v -> (u \in U) = (v \in W)) ->
  (forall u v, deg G u = deg G v) -> a -- b -> eta G = 2.
Proof.
move=> part bip reg ab.
have hdeg v u : v \in W -> v -- u -> deg G u < 2 * deg G v.
  move=> _ vu; have : 0 < deg G v by apply/card_gt0P; exists u; rewrite in_nbh.
  by rewrite (reg u v); lia.
rewrite (lemma_1 part bip hdeg).
case: ifP => // /forallP/(_ a)/forallP/(_ b)/implyP/(_ ab).
by rewrite (reg a b) eqxx.
Qed.

End Obs1.

(** * The sequence s_i and the bound max ceil(s_i / |V_i|)

   For part sizes n 0, ..., n (r-1) (the paper's |V_1|, ..., |V_r|, indexed from 0),
   s_(r-1) = n_(r-1) and s_i = max {1 + s_(i+1), n_i}. *)

Fixpoint sseq_from (n : nat -> nat) (d i : nat) : nat :=
  if d is d'.+1 then maxn (sseq_from n d' i.+1).+1 (n i) else n i.

(* the sequence s_i of Lemma 2 and Theorem 1 *)
Definition sseq (r : nat) (n : nat -> nat) (i : nat) : nat := sseq_from n (r.-1 - i) i.

(* the bound max_i ceil(s_i / n_i) *)
Definition mpbound (r : nat) (n : nat -> nat) : nat := \max_(i < r) cdiv (sseq r n i) (n i).

Section Sseq.

Variables (r : nat) (n : nat -> nat).

Lemma sseq_from_le d i t : i <= t <= i + d -> n t + (t - i) <= sseq_from n d i.
Proof.
elim: d i => [|d IH] i /= h.
  have -> : t = i by lia.
  by rewrite subnn addn0.
case: (ltngtP i t) => [it | ti | <-]; last by rewrite subnn addn0 leq_maxr.
  by rewrite leq_max; have := IH i.+1 (ltac:(lia)); lia.
lia.
Qed.

Lemma sseq_from_eq d i : exists2 t, i <= t <= i + d & sseq_from n d i = n t + (t - i).
Proof.
elim: d i => [|d IH] i /=; first by exists i; rewrite ?subnn; lia.
case: (IH i.+1) => t ht ->; case: (leqP (n t + (t - i.+1)).+1 (n i)) => h.
  by exists i; lia.
by exists t; lia.
Qed.

(* closed form: s_i = max_(t >= i) (n_t + t - i) *)
Lemma sseq_le_iff i x : i < r ->
  (sseq r n i <= x) <-> (forall t, i <= t < r -> n t + (t - i) <= x).
Proof.
move=> ir; split=> [h t ht | h]; first by apply: leq_trans h; apply: sseq_from_le; lia.
by case: (sseq_from_eq (r.-1 - i) i) => t ht; rewrite /sseq => ->; apply: h; lia.
Qed.

Lemma le_sseq i t : i <= t < r -> n t + (t - i) <= sseq r n i.
Proof. by move=> h; apply: sseq_from_le; lia. Qed.

Lemma le_sseq_self i : i < r -> n i <= sseq r n i.
Proof. by move=> ir; have := @le_sseq i i; rewrite subnn addn0; apply; lia. Qed.

(* the sequence s_i is strictly decreasing *)
Lemma sseq_lt i j : i < j < r -> sseq r n j < sseq r n i.
Proof.
move=> h; case: (sseq_from_eq (r.-1 - j) j) => t ht e.
have h2 : n t + (t - i) <= sseq r n i by apply: le_sseq; lia.
by rewrite {1}/sseq e; lia.
Qed.

Hypothesis pos : forall i, i < r -> 0 < n i.

(* the bound is at most k iff n_t + (t - i) <= k n_i whenever i <= t *)
Lemma mpbound_le_iff k :
  (mpbound r n <= k) <-> (forall i t, i <= t < r -> n t + (t - i) <= k * n i).
Proof.
split=> [/bigmax_leqP h i t ht | h].
  have ir : i < r by lia.
  by move: (h (Ordinal ir) isT) => /=; rewrite cdiv_le ?pos // sseq_le_iff // => /(_ t ht).
apply/bigmax_leqP => i _; rewrite cdiv_le ?pos // sseq_le_iff //.
by move=> t ht; apply: h; lia.
Qed.

Lemma sseq_le_mpbound i : i < r -> sseq r n i <= mpbound r n * n i.
Proof.
move=> ir; rewrite -cdiv_le ?pos // /mpbound.
by rewrite (bigD1 (Ordinal ir)) //= leq_maxl.
Qed.

Lemma mpbound_pos : 0 < r -> 0 < mpbound r n.
Proof.
move=> r0; have := sseq_le_mpbound r0; have := le_sseq_self r0; have := pos r0.
by case: (mpbound r n) => //; rewrite mul0n; lia.
Qed.

(* the paper's bound s_i <= |V_i| (r - i) (indices from 0), hence eta(G) <= r *)
Lemma mpbound_le_card :
  (forall i j, i <= j < r -> n j <= n i) -> mpbound r n <= r.
Proof.
move=> anti; apply/mpbound_le_iff => i t ht.
have ir : i < r by lia.
have := anti i t ht; have := pos ir; have := leq_pmulr (r - 1) (pos ir).
have -> : r * n i = (r - 1) * n i + n i by rewrite addnC -mulSn; congr (_ * _); lia.
lia.
Qed.

End Sseq.

(* Counting the elements of a duplicate-free list that lie in an interval. *)
Lemma count_interval_le (s : seq nat) (p : pred nat) a b :
  uniq s -> (forall j, j \in s -> p j -> a <= j <= b) -> count p s <= b.+1 - a.
Proof.
move=> us h; rewrite -size_filter -(size_iota a (b.+1 - a)).
apply: uniq_leq_size; first exact: filter_uniq.
by move=> j; rewrite mem_filter mem_iota => /andP[pj /h /(_ pj)]; lia.
Qed.

(* An ordering of the parts: a permutation sg of 0, ..., r - 1, with i |-> nth 0 sg i. *)
Definition ordering (r : nat) (sg : seq nat) : Prop := perm_eq sg (iota 0 r).

Lemma ordering_size r sg : ordering r sg -> size sg = r.
Proof. by move/perm_size; rewrite size_iota. Qed.

Lemma ordering_lt r sg i : ordering r sg -> i < r -> nth 0 sg i < r.
Proof.
move=> o ir; have : nth 0 sg i \in sg by rewrite mem_nth // (ordering_size o).
by rewrite (perm_mem o) mem_iota.
Qed.

Lemma ordering_count r sg (p : pred nat) : ordering r sg ->
  count (fun j => p (nth 0 sg j)) (iota 0 r) = count p (iota 0 r).
Proof.
move=> o; rewrite -(ordering_size o) -count_map.
have -> : map (nth 0 sg) (iota 0 (size sg)) = sg by exact: mkseq_nth.
by move/permP: (o) => ->; rewrite (ordering_size o).
Qed.

Lemma iota_split m a b : a <= b -> iota m b = iota m a ++ iota (m + a) (b - a).
Proof. by move=> ab; rewrite -iotaD subnKC. Qed.

(* The ordering by decreasing size gives the least bound among all orderings of the same
   sizes.  This replaces the second half of the paper's proof of Theorem 1, whose step
   "i >= j" does not hold in general (see the README).  Take i <= t in the sorted order.  The
   parts with sizes between n_t and n_i occupy at least t - i + 1 positions of the other
   order; if a and b are the first and last of them, then b - a >= t - i, and the bound for
   the other order at (a, b) gives the bound for the sorted order at (i, t). *)
Lemma mpbound_sorted_le r (n : nat -> nat) sg :
  (forall i j, i <= j < r -> n j <= n i) -> (forall i, i < r -> 0 < n i) ->
  ordering r sg -> mpbound r n <= mpbound r (fun i => n (nth 0 sg i)).
Proof.
move=> anti pos o.
pose n' i := n (nth 0 sg i).
have pos' i : i < r -> 0 < n' i by move=> ir; exact/pos/ordering_lt.
set k := mpbound r n'.
have /(mpbound_le_iff pos') H := leqnn k.
apply/(mpbound_le_iff pos) => i t ht.
pose P x := (n t <= x) && (x <= n i).
pose Q j := (j < r) && P (n' j).
have cnt : t - i < count Q (iota 0 r).
  have -> : count Q (iota 0 r) = count (fun j => P (n (nth 0 sg j))) (iota 0 r).
    by apply: eq_in_count => j; rewrite mem_iota /Q => /andP[_ ->].
  rewrite (ordering_count (fun x => P (n x)) o).
  have e1 := iota_split 0 (ltac:(lia) : i <= r).
  have e2 := iota_split (0 + i) (ltac:(lia) : t.+1 - i <= r - i).
  rewrite e1 e2 !count_cat.
  set c := count _ (iota (0 + i) (t.+1 - i)).
  suff : c = t.+1 - i by lia.
  rewrite /c; apply/eqP; rewrite -[X in _ == X](size_iota (0 + i)) -all_count.
  by apply/allP => j; rewrite mem_iota => hj; rewrite /P !anti //; lia.
have exQ : exists j, Q j.
  have : has Q (iota 0 r) by rewrite has_count; lia.
  by case/hasP => j _ qj; exists j.
have ub j : Q j -> j <= r by case/andP; lia.
case: (ex_minnP exQ) => a /andP[ar /andP[Pa1 Pa2]] mina.
case: (ex_maxnP exQ ub) => b /andP[br /andP[Pb1 Pb2]] maxb.
have cab : count Q (iota 0 r) <= b.+1 - a.
  apply: count_interval_le; first exact: iota_uniq.
  by move=> j _ qj; rewrite (mina j qj) (maxb j qj).
have hab := H a b (ltac:(lia)).
have := leq_mul (leqnn k) Pa2.
rewrite /n' in hab Pa2 Pb1 *; lia.
Qed.

(** * Distributing a sum over a set of vertices *)

(* the labels of the elements of s, between 1 and K, with sum T *)
Fixpoint distr (G : eqType) (s : seq G) (T K : nat) : G -> nat :=
  if s is x :: s' then
    let a := minn K (T - size s') in fun v => if v == x then a else distr s' (T - a) K v
  else fun _ => 0.

Lemma distrP (G : eqType) (s : seq G) T K : uniq s -> size s <= T <= K * size s ->
  (forall v, v \in s -> 0 < distr s T K v <= K) /\ \sum_(v <- s) distr s T K v = T.
Proof.
elim: s T => [|x s IH] T /=; first by move=> _ h; split=> //; rewrite big_nil; lia.
case/andP=> xs us; rewrite mulnS => hT; set a := minn K (T - size s).
have K0 : 0 < K by move: hT; case: (posnP K) => [->|]; lia.
have Ks := leq_pmull (size s) K0.
have [IH1 IH2] := IH (T - a) us (ltac:(rewrite /a; lia)).
split=> [v | ].
  rewrite inE; case: (v =P x) => [_ _ | _ /= vs]; last exact: IH1.
  by rewrite /a; lia.
rewrite big_cons eqxx.
have -> : \sum_(v <- s) (if v == x then a else distr s (T - a) K v) =
          \sum_(v <- s) distr s (T - a) K v.
  rewrite big_seq_cond [RHS]big_seq_cond; apply: eq_bigr => v /andP[vs _].
  by case: (v =P x) => // vx; move: xs; rewrite -vx vs.
by rewrite IH2 /a; lia.
Qed.

(** * Complete multipartite graphs

   The parts are Ps 0, ..., Ps (r - 1) (the paper's V_1, ..., V_r). *)

Record complete_multipartite (G : sgraph) (r : nat) (Ps : nat -> {set G})
  : Prop := {
  cm_nonempty : forall i, i < r -> exists v, v \in Ps i;
  cm_disjoint : forall i j v, i < r -> j < r -> v \in Ps i -> v \in Ps j -> i = j;
  cm_cover : forall v, exists i, (i < r) && (v \in Ps i);
  cm_adj : forall u v : G, u -- v <->
             exists i j, [/\ i < r, j < r, i != j, u \in Ps i & v \in Ps j] }.

Arguments complete_multipartite : clear implicits.

(* an orientation is monotone for the order Ps of the parts if all arcs go forward *)
Definition monotone (G : finType) (A : rel G) (r : nat) (Ps : nat -> {set G}) : Prop :=
  forall u v, A u v -> exists i j, [/\ i < j, j < r, u \in Ps i & v \in Ps j].

Section Multipartite.

Variables (G : sgraph) (r : nat) (Ps : nat -> {set G}).
Hypothesis cm : complete_multipartite G r Ps.

(* the part of a vertex *)
Definition idx (v : G) : nat := ex_minn (cm_cover cm v).

Lemma idx_spec v : idx v < r /\ v \in Ps (idx v).
Proof. by rewrite /idx; case: ex_minnP => i /andP[]. Qed.

Lemma idx_lt v : idx v < r. Proof. by case: (idx_spec v). Qed.
Lemma mem_idx v : v \in Ps (idx v). Proof. by case: (idx_spec v). Qed.

Lemma idx_eq v i : i < r -> v \in Ps i -> idx v = i.
Proof. by move=> ir vi; exact: (cm_disjoint cm (idx_lt v) ir (mem_idx v) vi). Qed.

Lemma mem_Ps v i : i < r -> (v \in Ps i) = (idx v == i).
Proof.
move=> ir; apply/idP/eqP => [vi | <-]; [exact: idx_eq | exact: mem_idx].
Qed.

(* two vertices are adjacent iff they are in different parts *)
Lemma cm_adj_idx u v : u -- v = (idx u != idx v).
Proof.
apply/idP/idP => [/(cm_adj cm)[i [j [ir jr ij ui vj]]] | h].
  by rewrite (idx_eq ir ui) (idx_eq jr vj).
by apply/(cm_adj cm); exists (idx u), (idx v); rewrite !idx_lt !mem_idx.
Qed.

Lemma card_Ps_pos i : i < r -> 0 < #|Ps i|.
Proof. by move=> ir; case: (cm_nonempty cm ir) => v vi; apply/card_gt0P; exists v. Qed.

(* f(N(w)) = f(V) - f(V_j) for w in V_j: only the part sums matter *)
Lemma cm_sumN w f : sumN G f w + \sum_(x in Ps (idx w)) f x = \sum_x f x.
Proof.
rewrite [RHS](bigID (fun x => x \in Ps (idx w))) /= addnC; congr (_ + _).
apply: eq_bigl => x; rewrite in_nbh cm_adj_idx mem_Ps ?idx_lt //.
by rewrite eq_sym.
Qed.

Lemma cm_sumN_in w j f : j < r -> w \in Ps j ->
  sumN G f w + \sum_(x in Ps j) f x = \sum_x f x.
Proof. by move=> jr wj; rewrite -(idx_eq jr wj) cm_sumN. Qed.

(* the same graph with the parts reordered *)
Lemma cm_ordering sg : ordering r sg -> complete_multipartite G r (fun i => Ps (nth 0 sg i)).
Proof.
move=> o; have us : uniq sg by rewrite (perm_uniq o) iota_uniq.
have sz := ordering_size o.
have inj i j : i < r -> j < r -> nth 0 sg i = nth 0 sg j -> i = j.
  by move=> ir jr /eqP; rewrite nth_uniq ?sz // => /eqP.
split=> [i ir | i j v ir jr vi vj | v | u v].
- exact: (cm_nonempty cm (ordering_lt o ir)).
- by apply: inj => //; exact: (cm_disjoint cm (ordering_lt o ir) (ordering_lt o jr) vi vj).
- have : idx v \in sg by rewrite (perm_mem o) mem_iota idx_lt.
  move=> h; exists (index (idx v) sg); rewrite -sz index_mem h /=.
  by rewrite nth_index // mem_idx.
- rewrite cm_adj_idx; split=> [h | [i [j [ir jr ij ui vj]]]].
    have hu : idx u \in sg by rewrite (perm_mem o) mem_iota idx_lt.
    have hv : idx v \in sg by rewrite (perm_mem o) mem_iota idx_lt.
    exists (index (idx u) sg), (index (idx v) sg).
    rewrite -!sz !index_mem hu hv !nth_index ?mem_idx //; split=> //.
    by apply: contra h => /eqP e; rewrite -(nth_index 0 hu) -(nth_index 0 hv) e.
  rewrite (idx_eq (ordering_lt o ir) ui) (idx_eq (ordering_lt o jr) vj).
  by apply: contra ij => /eqP /(inj _ _ ir jr) ->.
Qed.

Lemma arc_forward (A : rel G) i j u w : orientation G A -> monotone A r Ps ->
  i < j -> j < r -> u \in Ps i -> w \in Ps j -> A u w.
Proof.
move=> [_ hA _] hm ij jr ui wj.
have uw : u -- w by rewrite cm_adj_idx (idx_eq _ ui) ?(idx_eq _ wj) //; lia.
case/orP: (hA u w uw) => // /hm[i' [j' [ij' jr' wi' uj']]].
have := idx_eq (ltn_trans ij' jr') wi'; have := idx_eq jr' uj'.
by rewrite (idx_eq _ ui) ?(idx_eq _ wj) //; lia.
Qed.

(* the orientation from earlier to later parts *)
Definition forward : rel G := fun u v => idx u < idx v.

Lemma forward_spec : acyclic_orientation G forward /\ monotone forward r Ps.
Proof.
split; last by move=> u v uv; exists (idx u), (idx v); rewrite idx_lt !mem_idx.
apply: (acyclic_of_rank (rk := idx)) => //.
split=> u v; rewrite /forward ?cm_adj_idx; [lia | lia | lia].
Qed.

(* one vertex from each part forms a clique, so chi(G) >= r *)
Lemma cm_le_chi : r <= chi G.
Proof.
have ex (i : 'I_r) : exists v, v \in Ps i by exact: (cm_nonempty cm (ltn_ord i)).
pose rep (i : 'I_r) := xchoose (ex i).
have rep_in (i : 'I_r) : rep i \in Ps i := xchooseP (ex i).
have rep_idx (i : 'I_r) : idx (rep i) = i := idx_eq (ltn_ord i) (rep_in i).
have inj : injective rep.
  by move=> i j e; apply: val_inj; rewrite /= -rep_idx e rep_idx.
apply: leq_trans (clique_le_chi (Q := [set rep i | i : 'I_r]) _).
  by rewrite card_imset // card_ord.
move=> _ _ /imsetP[i _ ->] /imsetP[j _ ->] ij.
by rewrite cm_adj_idx !rep_idx; apply: contra ij => /eqP/val_inj ->.
Qed.

(** * Lemma 2 (ref. [6], Prop. 3)

   In a complete multipartite graph f(N(w)) = f(V) - f(V_j) for w in V_j, so only the sums
   f(V_j) of the parts matter. *)

Let n i := #|Ps i|.

(* lower bound: the part sums of a topological additive numbering decrease strictly along a
   monotone orientation *)
Lemma lemma_2_lower (A : rel G) k f : orientation G A -> monotone A r Ps ->
  topnum G A k f -> mpbound r n <= k.
Proof.
move=> hA hm [fl fs].
pose t i := \sum_(x in Ps i) f x.
have dec i j : i < j -> j < r -> t j < t i.
  move=> ij jr; have ir : i < r by lia.
  case: (cm_nonempty cm ir) => u ui; case: (cm_nonempty cm jr) => w wj.
  have := fs u w (arc_forward hA hm ij jr ui wj).
  have := cm_sumN_in f ir ui; have := cm_sumN_in f jr wj; rewrite /t; lia.
have gap d i : i + d < r -> t (i + d) + d <= t i.
  elim: d => [|d IH] h; first by rewrite !addn0.
  by have := dec (i + d) (i + d.+1) (ltac:(lia)) h; have := IH (ltac:(lia)); lia.
have lab i : n i <= t i <= k * n i.
  apply/andP; split.
    by rewrite /n /t -sum1_card; apply: leq_sum => v _; case/andP: (fl v).
  by rewrite /n /t mulnC -sum_nat_const; apply: leq_sum => v _; case/andP: (fl v).
apply/(mpbound_le_iff card_Ps_pos) => i j hij.
have e : i + (j - i) = j by lia.
have := gap (j - i) i (ltac:(lia)); rewrite e.
by have := lab i; have := lab j; rewrite /t /n; lia.
Qed.

(* upper bound: label each part V_i with sum s_i *)
Lemma lemma_2_upper (A : rel G) : monotone A r Ps -> exists f, topnum G A (mpbound r n) f.
Proof.
move=> hm; set K := mpbound r n.
pose f v := distr (enum (Ps (idx v))) (sseq r n (idx v)) K v.
have hyp i : i < r -> size (enum (Ps i)) <= sseq r n i <= K * size (enum (Ps i)).
  move=> ir; rewrite -cardE; apply/andP; split; first exact: le_sseq_self.
  exact: (sseq_le_mpbound card_Ps_pos ir).
have fsum i : i < r -> \sum_(x in Ps i) f x = sseq r n i.
  move=> ir; rewrite -big_enum /=.
  rewrite -[RHS](distrP (enum_uniq (Ps i)) (hyp i ir)).2.
  apply: eq_big_seq => x; rewrite mem_enum => xi.
  by rewrite /f (idx_eq ir xi).
exists f; split=> [v | u w uw].
  exact: (distrP (enum_uniq _) (hyp _ (idx_lt v))).1 v (ltac:(by rewrite mem_enum mem_idx)).
case: (hm u w uw) => i [j [ij jr ui wj]].
have ir : i < r by lia.
have := cm_sumN_in f ir ui; have := cm_sumN_in f jr wj.
rewrite !fsum //; have := @sseq_lt r n i j (ltac:(lia)); lia.
Qed.

(* Lemma 2: for a monotone acyclic orientation, eta_t(D) = max ceil(s_i / |V_i|) *)
Theorem lemma_2_value (A : rel G) : 0 < r -> acyclic_orientation G A -> monotone A r Ps ->
  etaT_is G A (mpbound r n).
Proof.
move=> r0 [hA _] hm; split; first exact: mpbound_pos card_Ps_pos r0.
  exact: lemma_2_upper.
by move=> k f _ hf; exact: lemma_2_lower hA hm hf.
Qed.

End Multipartite.

(* Lemma 2: eta_t(D) < infinity iff the orientation is monotone for some ordering of the
   parts *)
Theorem lemma_2_finite_iff (G : sgraph) r Ps (A : rel G) :
  complete_multipartite G r Ps -> 0 < r -> acyclic_orientation G A ->
  etaT_finite G A <-> exists sg, ordering r sg /\ monotone A r (fun i => Ps (nth 0 sg i)).
Proof.
move=> cm r0 hA; split=> [[k [f [_ [_ fs]]]] | [sg [o hm]]].
  pose key i := \sum_(x in Ps i) f x.
  have arc u w : A u w -> key (idx cm w) < key (idx cm u).
    move=> /fs h; have := cm_sumN cm u f; have := cm_sumN cm w f; rewrite /key; lia.
  pose le := fun i j => key j <= key i.
  have tot : total le by move=> i j; rewrite /le leq_total.
  have tr : transitive le by move=> i j l; rewrite /le => h1 h2; apply: leq_trans h2 h1.
  pose sg := sort le (iota 0 r).
  have o : ordering r sg by rewrite /ordering perm_sort.
  have sz := ordering_size o.
  have srt : sorted le sg := sort_sorted tot _.
  exists sg; split=> // u w uw.
  have mem x : x < r -> x \in sg by move=> xr; rewrite (perm_mem o) mem_iota.
  set i := index (idx cm u) sg; set j := index (idx cm w) sg.
  have ir : i < r by rewrite -sz index_mem mem ?idx_lt.
  have jr : j < r by rewrite -sz index_mem mem ?idx_lt.
  exists i, j; rewrite jr !nth_index ?mem ?idx_lt ?mem_idx //; split=> //.
  rewrite ltnNge; apply/negP => ji.
  have := sorted_leq_nth tr (fun x => leqnn _) 0 srt; rewrite sz => /(_ j i jr ir ji).
  by rewrite /le !nth_index ?mem ?idx_lt //; have := arc u w uw; lia.
have := lemma_2_value (cm_ordering cm o) r0 hA hm.
by move/etaT_is_finite.
Qed.

(** * Theorem 1 *)

(* Theorem 1: for a complete r-partite graph with parts |V_1| >= ... >= |V_r|,
   eta(G) = max ceil(s_i / |V_i|) and eta(G) <= r *)
Theorem theorem_1 (G : sgraph) r Ps :
  complete_multipartite G r Ps -> 0 < r ->
  (forall i j, i <= j < r -> #|Ps j| <= #|Ps i|) ->
  eta G = mpbound r (fun i => #|Ps i|) /\ eta G <= r.
Proof.
move=> cm r0 sorted.
have pos := card_Ps_pos cm.
have upper : eta G <= mpbound r (fun i => #|Ps i|).
  have [hf hm] := forward_spec cm.
  exact: eta_le_etaT hf.1 (lemma_2_value cm r0 hf hm).
have lower : mpbound r (fun i => #|Ps i|) <= eta G.
  case: (eta_eq_min_etaT G) => _ [A [hA hk]].
  case/(lemma_2_finite_iff cm r0 hA): (etaT_is_finite hk) => sg [o hm].
  have := lemma_2_value (cm_ordering cm o) r0 hA hm.
  move/(etaT_is_unique hk) => ->.
  exact: mpbound_sorted_le sorted pos o.
have e : eta G = mpbound r (fun i => #|Ps i|) by apply/eqP; rewrite eqn_leq upper lower.
by split=> //; rewrite e; exact: mpbound_le_card.
Qed.

(* the conjecture eta(G) <= chi(G) holds for complete multipartite graphs *)
Corollary theorem_1_conjecture (G : sgraph) r Ps :
  complete_multipartite G r Ps -> 0 < r ->
  (forall i j, i <= j < r -> #|Ps j| <= #|Ps i|) -> eta G <= chi G.
Proof. by move=> cm r0 s; apply: leq_trans (theorem_1 cm r0 s).2 (cm_le_chi cm). Qed.

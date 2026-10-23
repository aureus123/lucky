(* D. Severin, On the additive chromatic number of several families of graphs,
   Inf. Process. Lett. 158 (2020) 105937.

   Section 1: graphs, additive colorings, the additive chromatic number eta, the chromatic
   number chi, acyclic orientations, topological additive numberings, eta_t, and
   eta(G) = min eta_t(D).

   Graphs are the simple graphs (sgraph) of the library coq-graph-theory of C. Doczkal and
   D. Pous: a finite type of vertices with a symmetric irreflexive edge relation.  The
   adjacency x -- y is also written G x y.  N(G; v) is N(v), deg G v is d(v), maxdeg G is
   Delta, sumN G f v is f(N(v)), and chi G is the library's chromatic number. *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * Ceiling division *)

(* cdiv a b = ceil(a/b) *)
Definition cdiv (a b : nat) : nat := (a + b - 1) %/ b.

Lemma cdiv_le a b k : 0 < b -> (cdiv a b <= k) = (a <= k * b).
Proof. by move=> b0; rewrite /cdiv -ltnS ltn_divLR // mulSn; lia. Qed.

(* cdiv a b is the least k with a <= k b, i.e. the ceiling of a/b *)
Lemma cdiv_spec a b : 0 < b ->
  a <= cdiv a b * b /\ forall k, a <= k * b -> cdiv a b <= k.
Proof. by move=> b0; split=> [|k]; rewrite -cdiv_le. Qed.

Lemma cdiv_mono a a' b b' : a <= a' -> 0 < b' -> b' <= b -> cdiv a b <= cdiv a' b'.
Proof.
move=> aa b0 bb; have b1 : 0 < b by exact: leq_trans b0 bb.
rewrite cdiv_le //; apply: (leq_trans aa); apply: (leq_trans _ (leq_mul (leqnn _) bb)).
by rewrite -cdiv_le.
Qed.

(** * Counting values in an interval *)

(* an injective map from A into [lo, hi] *)
Lemma card_le_interval (T : finType) (A : {pred T}) (g : T -> nat) lo hi :
  {in A &, injective g} -> {in A, forall x, lo <= g x <= hi} -> #|A| <= hi.+1 - lo.
Proof.
move=> inj rng; rewrite cardE -(size_map g) -(size_iota lo (hi.+1 - lo)).
apply: uniq_leq_size.
  by rewrite map_inj_in_uniq ?enum_uniq // => x y; rewrite !mem_enum; exact: inj.
move=> y /mapP[x]; rewrite mem_enum => xA ->; rewrite mem_iota; have := rng x xA; lia.
Qed.

(** * Graphs *)

(* The library keeps x -- y folded under simpl (edge_rel is simpl never).  Here simpl
   reduces it in a concrete graph (a join, a spider, a sun, ...) to its edge relation. *)
Arguments digraph_of G /.
Arguments edge_rel : simpl nomatch.

Section Graph.

Variable G : sgraph.

Lemma adj_sym (u v : G) : u -- v = v -- u.
Proof. exact: sg_sym. Qed.

Lemma adj_irr (v : G) : v -- v = false.
Proof. exact: sg_irrefl. Qed.

Definition deg (v : G) : nat := #|N(G; v)|.
Definition maxdeg : nat := \max_(v : G) deg v.

(* f(N(v)) *)
Definition sumN (f : G -> nat) (v : G) : nat := \sum_(w in N(G; v)) f w.

Lemma in_nbh (v w : G) : (w \in N(G; v)) = v -- w.
Proof. exact: in_opn. Qed.

Lemma adj_ne (u v : G) : u -- v -> u != v.
Proof. by apply: contraTneq => ->; rewrite adj_irr. Qed.

Lemma deg_le_maxdeg v : deg v <= maxdeg.
Proof. exact: leq_bigmax. Qed.

Lemma maxdeg_le d : (forall v, deg v <= d) -> maxdeg <= d.
Proof. by move=> h; apply/bigmax_leqP => v _. Qed.

Lemma sumN_mkcond f (v : G) : sumN f v = \sum_w (if v -- w then f w else 0).
Proof. by rewrite /sumN big_mkcond; apply: eq_bigr => w _; rewrite inE. Qed.

Lemma sumN_eq f g v : (forall w, f w = g w) -> sumN f v = sumN g v.
Proof. by move=> h; apply: eq_bigr => w _. Qed.

Lemma sumN_one v : sumN (fun _ => 1) v = deg v.
Proof. exact: sum1_card. Qed.

(* f(N(v)) from an explicit neighborhood *)
Lemma sumN_of_nbh (S : {set G}) f v : (forall w, v -- w = (w \in S)) ->
  sumN f v = \sum_(w in S) f w.
Proof. by move=> h; apply: eq_bigl => w; rewrite inE h. Qed.

(* f(N[v]) = f(v) + f(N(v)) *)
Lemma sum_closed_nbh f v : \sum_(w in v |: N(G; v)) f w = f v + sumN f v.
Proof. by rewrite big_setU1 // inE adj_irr. Qed.

(** * Labelings and additive colorings *)

(* f : V -> [k] *)
Definition labeling (k : nat) (f : G -> nat) : Prop := forall v, 0 < f v <= k.

Definition additive_coloring (k : nat) (f : G -> nat) : Prop :=
  labeling k f /\ forall u v : G, u -- v -> sumN f u != sumN f v.

Lemma labeling_mono k k' f : labeling k f -> k <= k' -> labeling k' f.
Proof. by move=> h kk v; have := h v; lia. Qed.

Lemma additive_coloring_mono k k' f :
  additive_coloring k f -> k <= k' -> additive_coloring k' f.
Proof. by case=> h1 h2 kk; split=> //; exact: labeling_mono kk. Qed.

(* The existence of a labeling f : V -> [k] with a property P of f is decidable. *)
Lemma labelingP k (P : (G -> nat) -> bool) :
  (forall f g, (forall v, f v = g v) -> P f = P g) ->
  reflect (exists f, labeling k f /\ P f)
          [exists g : {ffun G -> 'I_k.+1}, [forall v, 0 < g v] && P (fun x => g x)].
Proof.
move=> Pext; apply: (iffP existsP) => [[g /andP[/forallP g0 Pg]] | [f [fl Pf]]].
  by exists (fun x => nat_of_ord (g x)); split=> // v; rewrite g0 -ltnS ltn_ord.
have fK v : (inord (f v) : 'I_k.+1) = f v :> nat by rewrite inordK // ltnS; case/andP: (fl v).
exists [ffun v => inord (f v)]; apply/andP; split.
  by apply/forallP => v; rewrite ffunE fK; case/andP: (fl v).
by rewrite (Pext _ f) // => v; rewrite ffunE fK.
Qed.

Definition acol_test (f : G -> nat) : bool :=
  [forall u, [forall v, u -- v ==> (sumN f u != sumN f v)]].

Lemma acol_test_ext f g : (forall v, f v = g v) -> acol_test f = acol_test g.
Proof.
move=> h; apply: eq_forallb => u; apply: eq_forallb => v.
by rewrite (sumN_eq _ h) (sumN_eq v h).
Qed.

Lemma acol_testP f : reflect (forall u v : G, u -- v -> sumN f u != sumN f v) (acol_test f).
Proof.
apply: (iffP forallP) => [h u v uv | h u]; first by move: (h u) => /forallP/(_ v)/implyP; apply.
by apply/forallP => v; apply/implyP; exact: h.
Qed.

Definition has_acol (k : nat) : bool :=
  [exists g : {ffun G -> 'I_k.+1}, [forall v, 0 < g v] && acol_test (fun x => g x)].

Lemma has_acolP k : reflect (exists f, additive_coloring k f) (has_acol k).
Proof.
apply: (iffP (labelingP k acol_test_ext)) => [[f [fl /acol_testP fs]] | [f [fl fs]]].
  by exists f.
by exists f; split=> //; apply/acol_testP.
Qed.

End Graph.

Arguments deg : clear implicits.
Arguments sumN : clear implicits.
Arguments additive_coloring : clear implicits.

Arguments adj_ne {G u v}.

(** * Every graph has an additive coloring: distinct powers of two *)

(* A set of indices is determined by the sum of the corresponding powers of two. *)
Lemma sum_pow2_inj n (S T : {set 'I_n}) :
  \sum_(i in S) 2 ^ i = \sum_(i in T) 2 ^ i -> S = T.
Proof.
elim: n S T => [|n IH] S T E; first by apply/setP => -[].
have dec (X : {set 'I_n.+1}) : \sum_(i in X) 2 ^ i =
    (ord0 \in X) + 2 * \sum_(j in [set j : 'I_n | lift ord0 j \in X]) 2 ^ j.
  rewrite big_mkcond big_ord_recl /= big_distrr [in RHS]big_mkcond /= expn0.
  congr (_ + _); apply: eq_bigr => j _; by rewrite inE /bump /= add1n expnS.
move: E; rewrite !dec => E.
have E0 : (ord0 \in S) = (ord0 \in T) by move: E; case: (ord0 \in S); case: (ord0 \in T) => /=; lia.
have /IH E1 : \sum_(j in [set j : 'I_n | lift ord0 j \in S]) 2 ^ j =
              \sum_(j in [set j : 'I_n | lift ord0 j \in T]) 2 ^ j by move: E; rewrite E0; lia.
apply/setP => i; case: (unliftP ord0 i) => [j -> | ->] //.
by move/setP: E1 => /(_ j); rewrite !inE.
Qed.

Section Eta.

Variable G : sgraph.

Lemma exists_acol : exists k, (0 < k) && has_acol G k.
Proof.
exists (2 ^ #|G|); rewrite expn_gt0 /=; apply/has_acolP.
exists (fun v => 2 ^ enum_rank v); split.
  by move=> v; rewrite expn_gt0 /= leq_pexp2l // ltnW.
move=> u v uv; apply/negP => /eqP E.
have : enum_rank @: N(G; u) = enum_rank @: N(G; v).
  by apply: sum_pow2_inj; rewrite !big_imset //= => x y _ _; exact: enum_rank_inj.
move/imset_inj => /(_ (@enum_rank_inj _)) Nuv.
by have := in_nbh u v; rewrite Nuv in_nbh adj_irr uv.
Qed.

(* eta(G): the least positive k such that G has an additive k-coloring *)
Definition eta : nat := ex_minn exists_acol.

Lemma eta_spec : 0 < eta /\ exists f, additive_coloring G eta f.
Proof. by rewrite /eta; case: ex_minnP => k /andP[k0 /has_acolP fk] _. Qed.

Lemma eta_pos : 0 < eta.
Proof. by case: eta_spec. Qed.

Lemma eta_attained : exists f, additive_coloring G eta f.
Proof. by case: eta_spec. Qed.

Lemma eta_le k f : 0 < k -> additive_coloring G k f -> eta <= k.
Proof.
move=> k0 fk; rewrite /eta; case: ex_minnP => m _ min; apply: min.
by rewrite k0; apply/has_acolP; exists f.
Qed.

Lemma le_eta m : (forall k f, 0 < k -> additive_coloring G k f -> m <= k) -> m <= eta.
Proof. by move=> h; case: eta_attained => f hf; exact: h eta_pos hf. Qed.

(* an upper bound eta(G) <= k from an explicit labeling *)
Lemma eta_le_lab k f : 0 < k -> labeling k f ->
  (forall u v : G, u -- v -> sumN G f u != sumN G f v) -> eta <= k.
Proof. by move=> k0 fl fs; apply: (eta_le k0 (f := f)). Qed.

End Eta.

(** * The chromatic number

   chi G is the chromatic number of coq-graph-theory: the least number of stable sets that
   partition the vertices.  It is also the least k such that G has a proper k-coloring
   (chi_attained and chi_le). *)

Definition chi (G : sgraph) : nat := χ([set: G]).

Section Chi.

Variable G : sgraph.

Definition proper (k : nat) (c : G -> 'I_k) : Prop := forall u v : G, u -- v -> c u != c v.

(* a proper k-coloring gives a partition into at most k stable sets *)
Lemma chi_le k (c : G -> 'I_k) : proper c -> chi G <= k.
Proof.
move=> hc; set P := preim_partition c [set: G].
have colP : coloring P [set: G].
  apply/andP; split; first exact: preim_partitionP.
  apply/forall_inP => B /imsetP[x _ ->]; apply/stableP => u v.
  rewrite !inE /= => /eqP eu /eqP ev; apply/negP => uv.
  by move: (hc u v uv); rewrite -eu -ev eqxx.
apply: leq_trans (color_bound colP) _.
have -> : P = (fun i => [set y in [set: G] | i == c y]) @: (c @: [set: G]).
  by rewrite -imset_comp.
by apply: leq_trans (leq_imset_card _ _) _; apply: leq_trans (max_card _) _; rewrite card_ord.
Qed.

(* an optimal partition into stable sets gives a proper chi(G)-coloring *)
Lemma chi_attained : exists c : G -> 'I_(chi G), proper c.
Proof.
rewrite /chi; case: chiP => P /andP[pP /forall_inP stP] _.
have inP x : pblock P x \in P by rewrite pblock_mem // (cover_partition pP) inE.
have lt x : index (pblock P x) (enum P) < #|P| by rewrite cardE index_mem mem_enum.
exists (fun x => Ordinal (lt x)) => u v uv; apply/negP => /eqP [e].
have hu : pblock P u \in enum P by rewrite mem_enum.
have hv : pblock P v \in enum P by rewrite mem_enum.
have e' : pblock P u = pblock P v by rewrite -(nth_index set0 hu) e (nth_index set0 hv).
have vB : v \in pblock P u by rewrite e' mem_pblock (cover_partition pP) inE.
have uB : u \in pblock P u by rewrite mem_pblock (cover_partition pP) inE.
by move/stableP: (stP _ (inP u)) => /(_ u v uB vB); rewrite uv.
Qed.

(* the clique bound *)
Lemma clique_le_chi (Q : {set G}) : clique Q -> #|Q| <= chi G.
Proof. by move=> cl; rewrite -(chi_clique cl); apply: sub_chi; exact: subsetT. Qed.

End Chi.

(** * Acyclic orientations and topological additive numberings

   An orientation of G is a relation A that contains, for every edge, exactly one of its two
   directions.  The paper's digraph D representing it has the same vertices, so N_D(v) = N(v).
   It is acyclic if no arc u -> v can be closed by a path from v back to u. *)

Section Orientations.

Variable G : sgraph.

Definition orientation (A : rel G) : Prop :=
  [/\ forall u v, A u v -> u -- v, forall u v : G, u -- v -> A u v || A v u
    & forall u v, A u v -> ~~ A v u].

Definition acyclic_orientation (A : rel G) : Prop :=
  orientation A /\ forall u v, A u v -> ~~ connect A v u.

(* a topological additive k-numbering of D *)
Definition topnum (A : rel G) (k : nat) (f : G -> nat) : Prop :=
  labeling k f /\ forall u v, A u v -> sumN G f u < sumN G f v.

(* eta_t(D) < infinity *)
Definition etaT_finite (A : rel G) : Prop := exists k f, 0 < k /\ topnum A k f.

(* eta_t(D) = k *)
Definition etaT_is (A : rel G) (k : nat) : Prop :=
  [/\ 0 < k, exists f, topnum A k f & forall k' f, 0 < k' -> topnum A k' f -> k <= k'].

Lemma etaT_is_unique (A : rel G) k k' : etaT_is A k -> etaT_is A k' -> k = k'.
Proof.
case=> k0 [f hf] m1 [k0' [f' hf'] m2].
by apply/eqP; rewrite eqn_leq (m1 _ _ k0' hf') (m2 _ _ k0 hf).
Qed.

Definition top_test (A : rel G) (f : G -> nat) : bool :=
  [forall u, [forall v, A u v ==> (sumN G f u < sumN G f v)]].

Lemma top_testP (A : rel G) f : reflect (forall u v, A u v -> sumN G f u < sumN G f v) (top_test A f).
Proof.
apply: (iffP forallP) => [h u v uv | h u]; first by move: (h u) => /forallP/(_ v)/implyP; apply.
by apply/forallP => v; apply/implyP; exact: h.
Qed.

Lemma top_test_ext (A : rel G) f g : (forall v, f v = g v) -> top_test A f = top_test A g.
Proof.
move=> h; apply: eq_forallb => u; apply: eq_forallb => v.
by rewrite (sumN_eq _ h) (sumN_eq v h).
Qed.

Lemma has_topP (A : rel G) k : reflect (exists f, topnum A k f)
  [exists g : {ffun G -> 'I_k.+1}, [forall v, 0 < g v] && top_test A (fun x => g x)].
Proof.
apply: (iffP (labelingP k (top_test_ext A))) => [[f [fl /top_testP fs]] | [f [fl fs]]].
  by exists f.
by exists f; split=> //; apply/top_testP.
Qed.

(* if eta_t(D) is finite, it is attained *)
Lemma etaT_finite_is (A : rel G) : etaT_finite A -> exists k, etaT_is A k.
Proof.
move=> h.
have ex : exists k, (0 < k) && [exists g : {ffun G -> 'I_k.+1},
                                  [forall v, 0 < g v] && top_test A (fun x => g x)].
  by case: h => k [f [k0 hf]]; exists k; rewrite k0; apply/has_topP; exists f.
case: (ex_minnP ex) => k /andP[k0 /has_topP fk] min.
exists k; split=> // k' f k0' hf; apply: min; rewrite k0'; apply/has_topP; by exists f.
Qed.

Lemma etaT_is_finite (A : rel G) k : etaT_is A k -> etaT_finite A.
Proof. by case=> k0 [f hf] _; exists k, f. Qed.

Lemma topnum_additive (A : rel G) k f : orientation A -> topnum A k f -> additive_coloring G k f.
Proof.
case=> _ hA _ [fl fs]; split=> // u v uv; case/orP: (hA u v uv) => /fs h.
  by rewrite neq_ltn h.
by rewrite neq_ltn h orbT.
Qed.

Lemma eta_le_etaT (A : rel G) k : orientation A -> etaT_is A k -> eta G <= k.
Proof. by move=> hA [k0 [f hf] _]; exact: eta_le k0 (topnum_additive hA hf). Qed.

(* a relation with a strictly increasing rank has no cycles *)
Lemma connect_rank (A : rel G) (rk : G -> nat) :
  (forall u v, A u v -> rk u < rk v) -> forall x y, connect A x y -> rk x <= rk y.
Proof.
move=> h x y /connectP[p]; elim: p x => [|z p IH] x /=; first by move=> _ ->.
by case/andP=> xz pz yl; apply: leq_trans (ltnW (h _ _ xz)) (IH _ pz yl).
Qed.

Lemma acyclic_of_rank (A : rel G) (rk : G -> nat) :
  orientation A -> (forall u v, A u v -> rk u < rk v) -> acyclic_orientation A.
Proof.
move=> hA h; split=> // u v uv; apply/negP => /(connect_rank h) vu.
by have := h _ _ uv; lia.
Qed.

(* the orientation induced by the sums: every edge goes from the smaller to the larger sum *)
Definition induced_orientation (f : G -> nat) : rel G := fun u v => u -- v && (sumN G f u < sumN G f v).

Lemma induced_acyclic k f : additive_coloring G k f -> acyclic_orientation (induced_orientation f).
Proof.
case=> _ fs; apply: (acyclic_of_rank (rk := sumN G f)); last by move=> u v /andP[].
split=> [u v /andP[] // | u v uv | u v /andP[_ h]].
  rewrite /induced_orientation uv (adj_sym v u) uv /=.
  by move: (fs u v uv); rewrite neq_ltn.
by rewrite /induced_orientation negb_and -leqNgt ltnW ?orbT.
Qed.

Lemma induced_topnum k f : additive_coloring G k f -> topnum (induced_orientation f) k f.
Proof. by case=> fl _; split=> // u v /andP[]. Qed.

(* eta(G) = min { eta_t(D) : D represents an acyclic orientation of G } *)
Theorem eta_eq_min_etaT :
  (forall A k, acyclic_orientation A -> etaT_is A k -> eta G <= k) /\
  exists A, acyclic_orientation A /\ etaT_is A (eta G).
Proof.
split=> [A k [hA _] hk | ]; first exact: eta_le_etaT hA hk.
case: (eta_attained G) => f hf.
have hA := induced_acyclic hf.
exists (induced_orientation f); split=> //; split; [exact: eta_pos | by exists f; exact: induced_topnum |].
by move=> k' g k0 hg; exact: eta_le k0 (topnum_additive hA.1 hg).
Qed.

End Orientations.

Arguments orientation : clear implicits.
Arguments acyclic_orientation : clear implicits.
Arguments topnum : clear implicits.
Arguments etaT_finite : clear implicits.
Arguments etaT_is : clear implicits.
Arguments induced_orientation : clear implicits.

(** * True twins *)

Definition true_twins (G : sgraph) (u v : G) : Prop :=
  u |: N(G; u) = v |: N(G; v).

Arguments true_twins : clear implicits.

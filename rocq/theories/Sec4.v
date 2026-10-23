(* Section 4: split graphs.
   Theorem 3, the conjecture for split graphs, Proposition 2 (complete splits), Lemma 3
   (ref. [6], Prop. 1, proved here) and Corollary 2. *)

From mathcomp Require Import all_boot zify.
From GraphTheory Require Import preliminaries digraph sgraph dom coloring.
From ACN Require Import Tactics Basics Sec2 Sec3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope implicit_scope.

(** * Sums and cliques *)

Lemma sum_subset_le (T : finType) (A B : {set T}) (f : T -> nat) :
  A \subset B -> \sum_(x in A) f x <= \sum_(x in B) f x.
Proof.
move=> AB; rewrite [X in _ <= X](big_setID A) /= (setIidPr AB).
exact: leq_addr.
Qed.

Section Cliques.

Variable G : sgraph.

Lemma clique_nbh (Q : {set G}) q : clique Q -> q \in Q -> N(G; q) :&: Q = Q :\ q.
Proof.
move=> cl qQ; apply/setP => x; rewrite !inE ?in_nbh andbC.
case xQ: (x \in Q); rewrite ?andbF //=.
case: (x =P q) => [-> | /eqP xq]; first by rewrite adj_irr.
by rewrite cl // eq_sym.
Qed.

(* |Q| <= d(q) + 1 for q in a clique Q *)
Lemma clique_card_le_deg (Q : {set G}) q : clique Q -> q \in Q -> #|Q| <= deg G q + 1.
Proof.
move=> cl qQ; rewrite (cardsD1 q Q) qQ -(clique_nbh cl qQ) addnC leq_add2r.
by apply: subset_leq_card; exact: subsetIl.
Qed.

(* f(N(q)) = f(Q) - f(q) + f(N(q) - Q) for q in a clique Q *)
Lemma clique_sumN (Q : {set G}) q f : clique Q -> q \in Q ->
  sumN G f q + f q = \sum_(x in Q) f x + \sum_(x in N(G; q) :\: Q) f x.
Proof.
move=> cl qQ; rewrite /sumN (big_setID Q) /= (clique_nbh cl qQ) (big_setD1 q qQ) /=.
by rewrite addnC addnA.
Qed.

Lemma clique_deg (Q : {set G}) q : clique Q -> q \in Q ->
  deg G q + 1 = #|Q| + #|N(G; q) :\: Q|.
Proof. by move=> cl qQ; have := clique_sumN (fun _ => 1) cl qQ; rewrite sumN_one !sum1_card. Qed.

End Cliques.

(** * Theorem 3: an upper bound for split graphs *)

(* a split graph with clique Q and stable set S; Q is maximal, i.e. no vertex of S is
   adjacent to all of Q *)
Record split_graph (G : sgraph) (Q S : {set G}) : Prop := {
  sp_part : forall v, (v \in S) = (v \notin Q);
  sp_clique : clique Q;
  sp_stable : {in S &, forall a b, ~~ a -- b};
  sp_max : forall v, v \in S -> exists2 u, u \in Q & ~~ u -- v }.

Arguments split_graph : clear implicits.

Section Split.

Variables (G : sgraph) (Q S : {set G}).
Hypothesis sp : split_graph G Q S.

Lemma sp_nbh_S v : v \in S -> N(G; v) \subset Q.
Proof.
move=> vS; apply/subsetP => w; rewrite in_nbh => vw.
apply/negPn/negP => wQ; have wS : w \in S by rewrite (sp_part sp).
by move: (sp_stable sp vS wS); rewrite vw.
Qed.

Lemma sp_nbhD u : N(G; u) :\: Q = N(G; u) :&: S.
Proof. by apply/setP => x; rewrite !inE (sp_part sp) andbC. Qed.

(* d(u) + 1 = |Q| + r(u) for u in Q, where r(u) = |N(u) n S| *)
Lemma sp_deg_Q u : u \in Q -> deg G u + 1 = #|Q| + #|N(G; u) :&: S|.
Proof. by move=> uQ; rewrite -sp_nbhD; exact: clique_deg (sp_clique sp) uQ. Qed.

(* f(N(u)) + f(u) = f(Q) + c r(u) for u in Q, when f = c on S *)
Lemma sp_sumN_Q u f c : u \in Q -> (forall w, w \in S -> f w = c) ->
  sumN G f u + f u = \sum_(x in Q) f x + c * #|N(G; u) :&: S|.
Proof.
move=> uQ hc; rewrite (clique_sumN f (sp_clique sp) uQ) sp_nbhD; congr (_ + _).
have e : forall w, w \in N(G; u) :&: S -> f w = c by move=> w /setIP[_ /hc].
by rewrite (eq_bigr _ e) sum_nat_const mulnC.
Qed.

(* Theorem 3: if T is a subset of Q and the degrees in T are pairwise distinct, then
   eta(G) <= |Q| - |T| + 1.  Labeling: 1, ..., q - t on Q - T, and q - t + 1 on T u S.
   (The paper assumes T <> {}; the proof does not need it.) *)
Theorem theorem_3 (T : {set G}) : T \subset Q ->
  {in T &, forall x y, deg G x = deg G y -> x = y} -> eta G <= #|Q| - #|T| + 1.
Proof.
move=> TQ hdeg; set c := #|Q| - #|T| + 1.
set R := Q :\: T.
have cR : #|R| = #|Q| - #|T| by rewrite cardsDS.
pose f x := if x \in R then (index x (enum R)).+1 else c.
have fR x : x \in R -> f x < c.
  move=> xR; rewrite /f xR /c; have := index_mem x (enum R).
  by rewrite mem_enum xR -cardE cR; lia.
have flab x : 0 < f x <= c.
  by case xR : (x \in R); [have := fR x xR; rewrite /f xR; lia | rewrite /f xR; lia].
have fS w : w \in S -> f w = c.
  move=> wS; have wQ : (w \in Q) = false by apply/negbTE; rewrite -(sp_part sp).
  by rewrite /f !inE wQ andbF.
have sQ u : u \in Q -> sumN G f u + f u = \sum_(x in Q) f x + c * #|N(G; u) :&: S|.
  by move=> uQ; exact: sp_sumN_Q uQ fS.
have sS v : v \in S -> sumN G f v < \sum_(x in Q) f x.
  move=> vS; case: (sp_max sp vS) => u0 u0Q nadj.
  have sub : N(G; v) \subset Q :\ u0.
    apply/subsetP => w wN; rewrite !inE (subsetP (sp_nbh_S vS)) // andbT.
    by apply: contraNneq nadj => e; rewrite -e adj_sym -in_nbh.
  have := sum_subset_le f sub; rewrite [X in _ <= _ -> _ < X](big_setD1 u0) //=.
  by have := flab u0; rewrite /sumN; nlia.
(* an edge between Q and S goes from S to Q *)
have QS u v : u \in Q -> v \in S -> u -- v -> sumN G f v < sumN G f u.
  move=> uQ vS uv; have r1 : 0 < #|N(G; u) :&: S|.
    by apply/card_gt0P; exists v; rewrite inE ?in_nbh uv.
  have := leq_pmulr c r1; have := sQ u uQ; have := sS v vS; have := flab u; lia.
apply: (eta_le_lab (f := f)) => //; first by lia.
move=> x y xy; case xQ: (x \in Q); case yQ: (y \in Q).
- set rx := #|N(G; x) :&: S|; set ry := #|N(G; y) :&: S|.
  have h1 := sQ x xQ; have h2 := sQ y yQ.
  case: (ltngtP rx ry) => [lt | gt | eq].
  + have : c * rx + c <= c * ry by rewrite addnC -mulnS leq_mul2l lt orbT.
    by have := flab x; have := flab y; rewrite -/rx -/ry in h1 h2; lia.
  + have : c * ry + c <= c * rx by rewrite addnC -mulnS leq_mul2l gt orbT.
    by have := flab x; have := flab y; rewrite -/rx -/ry in h1 h2; lia.
  (* equal sums and equal r: equal labels, so both are in T and have equal degrees *)
  apply/negP => /eqP es.
  have fxy : f x = f y by move: h1 h2; rewrite -/rx -/ry eq es; lia.
  have xT : x \in T /\ y \in T.
    case xR : (x \in R); case yR : (y \in R).
    - move: fxy; rewrite /f xR yR => -[] e.
      have hx : x \in enum R by rewrite mem_enum.
      have hy : y \in enum R by rewrite mem_enum.
      have exy : x = y by rewrite -(nth_index x hx) e (nth_index x hy).
      by move: xy; rewrite exy adj_irr.
    - by move: fxy (fR x xR); rewrite /f xR yR => ->; rewrite ltnn.
    - by move: fxy (fR y yR); rewrite /f xR yR => <-; rewrite ltnn.
    by move: xR yR; rewrite !inE xQ yQ !andbT => /negbFE xT /negbFE yT.
  have dxy : deg G x = deg G y.
    by have := sp_deg_Q xQ; have := sp_deg_Q yQ; rewrite -/rx -/ry eq; lia.
  by move: xy; rewrite (hdeg x y xT.1 xT.2 dxy) adj_irr.
- have yS : y \in S by rewrite (sp_part sp) yQ.
  by rewrite neq_ltn (QS x y) ?orbT // xQ.
- have xS : x \in S by rewrite (sp_part sp) xQ.
  by rewrite neq_ltn (QS y x) // adj_sym.
have xS : x \in S by rewrite (sp_part sp) xQ.
have yS : y \in S by rewrite (sp_part sp) yQ.
by move: (sp_stable sp xS yS); rewrite xy.
Qed.

(* with |T| = 1: eta(G) <= |Q| <= chi(G), so the conjecture holds for split graphs *)
Corollary theorem_3_conjecture : 0 < #|G| -> eta G <= #|Q| /\ eta G <= chi G.
Proof.
move=> /card_gt0P[v _].
have [u uQ] : exists u, u \in Q.
  case vQ : (v \in Q); first by exists v.
  have vS : v \in S by rewrite (sp_part sp) vQ.
  by have [u uQ _] := sp_max sp vS; exists u.
have h : eta G <= #|Q| - #|[set u]| + 1.
  apply: theorem_3; first by rewrite sub1set.
  by move=> x y /set1P -> /set1P ->.
have Q0 : 0 < #|Q| by apply/card_gt0P; exists u.
rewrite cards1 in h; split; first by lia.
by apply: leq_trans (clique_le_chi (sp_clique sp)); lia.
Qed.

End Split.

Section SplitAny.

Variables (G : sgraph) (Q S : {set G}).

(* moving to Q a vertex of S adjacent to all of Q keeps a split partition *)
Lemma split_add v :
  (forall x, (x \in S) = (x \notin Q)) -> clique Q -> {in S &, forall a b, ~~ a -- b} ->
  v \in S -> {in Q, forall u, u -- v} -> split_graph G (v |: Q) (S :\ v).
Proof.
move=> part cl st vS hv; split.
- move=> x; rewrite !inE part; by case: (x =P v) => [-> | _]; rewrite ?vS ?part.
- move=> x y; rewrite !inE => /orP[/eqP -> | xQ] /orP[/eqP -> | yQ]; rewrite ?eqxx //.
  + by move=> _; rewrite adj_sym hv.
  + by move=> _; rewrite hv.
  + exact: cl.
- by move=> a b /setD1P[_ aS] /setD1P[_ bS]; exact: st.
move=> w /setD1P[wv wS]; exists v; first exact: setU11.
exact: st.
Qed.

(* the conjecture holds for every split graph: a split partition can be made maximal by
   moving one vertex from S to Q *)
Theorem split_graph_conjecture :
  0 < #|G| -> (forall x, (x \in S) = (x \notin Q)) -> clique Q ->
  {in S &, forall a b, ~~ a -- b} -> eta G <= chi G.
Proof.
move=> V0 part cl st.
case: (boolP [forall v, (v \in S) ==> [exists u, (u \in Q) && ~~ u -- v]]) => [/forallP h | ].
  have sp : split_graph G Q S.
    split=> // v vS; move: (h v); rewrite vS => /existsP[u /andP[uQ nuv]].
    by exists u.
  exact: (theorem_3_conjecture sp V0).2.
move=> /forallPn[v]; rewrite negb_imply => /andP[vS /existsPn hv].
have hv' : {in Q, forall u, u -- v} by move=> u uQ; move: (hv u); rewrite uQ negbK.
exact: (theorem_3_conjecture (split_add part cl st vS hv') V0).2.
Qed.

End SplitAny.

(** * Proposition 2: complete splits *)

(* Proposition 2: a complete split graph (a clique Q with |Q| >= 1, a stable set S with
   |S| >= 2, and all edges between them) has eta(G) = |Q| *)
Theorem proposition_2 (G : sgraph) (Q S : {set G}) :
  (forall x, (x \in S) = (x \notin Q)) -> clique Q -> {in S &, forall a b, ~~ a -- b} ->
  {in Q & S, forall u v : G, u -- v} -> 0 < #|Q| -> 2 <= #|S| -> eta G = #|Q|.
Proof.
move=> part cl st full /card_gt0P[u uQ] S2.
have [v vS] : exists v, v \in S by apply/card_gt0P; lia.
have vQ : v \notin Q by rewrite -part.
have Nv : N(G; v) = Q.
  apply/setP => x; rewrite in_nbh; case xQ : (x \in Q); first by rewrite adj_sym full.
  by apply/negbTE/st => //; rewrite part xQ.
have Nu : N(G; u) = (Q :\ u) :|: S.
  apply/setP => x; rewrite in_nbh !inE part.
  case xQ : (x \in Q) => /=.
    by case: (x =P u) => [-> | /eqP xu]; rewrite ?adj_irr // cl // eq_sym.
  have xS : x \in S by rewrite part xQ.
  by rewrite (full u x uQ xS) andbF.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  have sp := split_add part cl st vS (fun w wQ => full w v wQ vS).
  have du : deg G u = #|Q| - 1 + #|S|.
    rewrite /deg Nu cardsU (cardsD1 u Q) uQ.
    have -> : (Q :\ u) :&: S = set0.
      by apply/setP => x; rewrite !inE part; case: (x \in Q); rewrite ?andbF.
    by rewrite cards0; lia.
  have dv : deg G v = #|Q| by rewrite /deg Nv.
  have uv : u != v by apply: contraNneq vQ => <-.
  have hT : [set u; v] \subset v |: Q.
    by apply/subsetP => x; rewrite !inE => /orP[/eqP -> | /eqP ->]; rewrite ?uQ ?eqxx ?orbT.
  have hd : {in [set u; v] &, forall x y, deg G x = deg G y -> x = y}.
    move=> x y; rewrite !inE => /orP[/eqP -> | /eqP ->] /orP[/eqP -> | /eqP ->] // e;
      by exfalso; move: e; rewrite du dv; lia.
  have Q1 : 0 < #|Q| by apply/card_gt0P; exists u.
  by have := theorem_3 sp hT hd; rewrite cards2 uv cardsU1 vQ /=; nlia.
  (* the vertices of Q are pairwise true twins: N[w] = V for w in Q *)
have N w : w \in Q -> w |: N(G; w) = setT.
  move=> wQ; apply/setP => x; rewrite !inE ?in_nbh.
  case: (x =P w) => //= /eqP xw; case xQ : (x \in Q); first by rewrite cl // eq_sym.
  by rewrite full // part xQ.
by apply: observation_2 => a b aQ bQ; rewrite /true_twins !N.
Qed.

(** * Lemma 3 (ref. [6], Prop. 1) and Corollary 2

   For a clique Q of an acyclic orientation, q_F and q_L are the source and the sink of Q,
   i.e. the first and last vertices of Q in a topological order. *)

Section Lemma3.

Variable G : sgraph.

(* Lemma 3, for a topological additive k-numbering f.  The proof of [6]: for q in Q let
   Y_q = f(N(q) - Q) - f(q) (shifted by k to stay in nat).  Then f(N(q)) = f(Q) + Y_q, so
   the Y_q are |Q| distinct integers between Y_qF >= |N(q_F) - Q| - k and
   Y_qL <= k |N(q_L) - Q| - 1. *)
Lemma lemma_3_topnum (A : rel G) (Q : {set G}) qF qL k f :
  orientation G A -> clique Q -> qF \in Q -> qL \in Q ->
  (forall q, q \in Q -> q != qF -> A qF q) -> (forall q, q \in Q -> q != qL -> A q qL) ->
  0 < k -> topnum G A k f -> cdiv (deg G qF + 1) (deg G qL + 2 - #|Q|) <= k.
Proof.
move=> [hA1 hA2 _] cl qFQ qLQ src snk k0 [fl fs].
pose Y q := \sum_(x in N(G; q) :\: Q) f x + k - f q.
have SY q : q \in Q -> sumN G f q + k = \sum_(x in Q) f x + Y q.
  by move=> qQ; have := clique_sumN f cl qQ; have := fl q; rewrite /Y; lia.
have Ylt u v : u \in Q -> v \in Q -> A u v -> Y u < Y v.
  by move=> uQ vQ /fs; have := SY u uQ; have := SY v vQ; lia.
have inj : {in Q &, injective Y}.
  move=> u v uQ vQ e; apply/eqP; apply/negPn/negP => uv.
  case/orP: (hA2 u v (cl u v uQ vQ uv)) => h;
    [have := Ylt _ _ uQ vQ h | have := Ylt _ _ vQ uQ h]; lia.
have rng : {in Q, forall q, Y qF <= Y q <= Y qL}.
  move=> q qQ; apply/andP; split.
    by case: (q =P qF) => [-> // | /eqP h]; exact/ltnW/Ylt/src.
  by case: (q =P qL) => [-> // | /eqP h]; exact/ltnW/Ylt/snk.
have hspread := card_le_interval inj rng.
set a := #|N(G; qF) :\: Q|; set c := #|N(G; qL) :\: Q|.
have hYF : a <= Y qF.
  have : a <= \sum_(x in N(G; qF) :\: Q) f x.
    by rewrite /a -sum1_card; apply: leq_sum => x _; case/andP: (fl x).
  by have := fl qF; rewrite /Y; lia.
have hYL : Y qL < k * c + k.
  have : \sum_(x in N(G; qL) :\: Q) f x <= k * c.
    by rewrite /c mulnC -sum_nat_const; apply: leq_sum => x _; case/andP: (fl x).
  by have := fl qL; rewrite /Y; lia.
have h1 := clique_deg cl qFQ; have h2 := clique_deg cl qLQ.
rewrite -/a in h1; rewrite -/c in h2.
have -> : deg G qL + 2 - #|Q| = c.+1 by lia.
have hs : #|Q| <= (Y qL).+1 - Y qF := hspread.
by have := rng qF qFQ; rewrite cdiv_le // mulnS; lia.
Qed.

(* Lemma 3: eta_t(D) >= ceil((d(q_F) + 1) / (d(q_L) - |Q| + 2)) *)
Theorem lemma_3 (A : rel G) (Q : {set G}) qF qL k :
  acyclic_orientation G A -> clique Q -> qF \in Q -> qL \in Q ->
  (forall q, q \in Q -> q != qF -> A qF q) -> (forall q, q \in Q -> q != qL -> A q qL) ->
  etaT_is G A k -> cdiv (deg G qF + 1) (deg G qL + 2 - #|Q|) <= k.
Proof.
move=> [hA _] cl qFQ qLQ src snk [k0 [f hf] _].
exact: lemma_3_topnum hA cl qFQ qLQ src snk k0 hf.
Qed.

(* Corollary 2: if d1 and d2 bound the degrees of a clique Q from below and above (the paper
   takes the smallest and the largest degree), then
   eta(G) >= ceil((d1 + 1) / (d2 - |Q| + 2)) *)
Theorem corollary_2 (Q : {set G}) d1 d2 :
  clique Q -> 0 < #|Q| -> {in Q, forall v, d1 <= deg G v <= d2} ->
  cdiv (d1 + 1) (d2 + 2 - #|Q|) <= eta G.
Proof.
move=> cl /card_gt0P[q0 q0Q] hd.
case: (eta_attained G) => f hf.
have hne u v : u \in Q -> v \in Q -> u != v -> sumN G f u != sumN G f v.
  by move=> uQ vQ uv; apply: hf.2; exact: cl.
case: (@arg_minnP _ q0 (fun x => x \in Q) (sumN G f) q0Q) => qF qFQ minF.
case: (@arg_maxnP _ q0 (fun x => x \in Q) (sumN G f) q0Q) => qL qLQ maxL.
have src q : q \in Q -> q != qF -> induced_orientation G f qF q.
  move=> qQ qqF; rewrite /induced_orientation cl // 1?eq_sym //= ltn_neqAle minF // andbT.
  by rewrite hne // eq_sym.
have snk q : q \in Q -> q != qL -> induced_orientation G f q qL.
  move=> qQ qqL; rewrite /induced_orientation cl //= ltn_neqAle; apply/andP; split.
    exact: hne.
  exact: maxL.
have h3 := lemma_3_topnum (induced_acyclic hf).1 cl qFQ qLQ src snk (eta_pos G)
  (induced_topnum hf).
apply: leq_trans h3; apply: cdiv_mono.
- by have := hd qF qFQ; lia.
- by have := clique_card_le_deg cl qLQ; lia.
by have := hd qL qLQ; lia.
Qed.

(* Corollary 2 when all the vertices of the clique have the same degree d *)
Corollary corollary_2_eq (Q : {set G}) d :
  clique Q -> 0 < #|Q| -> {in Q, forall v, deg G v = d} ->
  cdiv (d + 1) (d + 2 - #|Q|) <= eta G.
Proof.
move=> cl Q0 hd; apply: corollary_2 => // v vQ.
by rewrite hd // leqnn.
Qed.

End Lemma3.

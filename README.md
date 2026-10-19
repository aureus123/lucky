# Additive chromatic number of several families of graphs

This repository accompanies D. Severín, *On the additive chromatic number of several families of
graphs*, Inf. Process. Lett. 158 (2020) 105937, doi:10.1016/j.ipl.2020.105937
([arXiv:1602.07675](https://arxiv.org/abs/1602.07675)).

It contains:

- the paper's results;
- remarks on hypotheses that the paper leaves implicit, and small slips found while preparing the
  formalization;
- machine-checked formalizations of Sections 1–5 in Isabelle/HOL and in Mizar.

| File or folder | Content |
|---|---|
| `severin-additive-chromatic-number.pdf` | arXiv version (v3, 12 Feb 2020): the paper plus the appendix with the proofs of the propositions (ref. [7]); download it from [arXiv](https://arxiv.org/abs/1602.07675) |
| [`references/`](references/README.md) | summaries of the papers cited by the paper |
| [`others/`](others/README.md) | summaries of further papers on additive colorings and their techniques (Combinatorial Nullstellensatz, discharging, list and closed variants) |
| [`isabelle/`](isabelle/README.md) | the formalization in Isabelle/HOL |
| [`mizar/`](mizar/README.md) | the formalization in Mizar |

The PDF file is not part of the repository (see [License](#license)).

---

## 1. Results of the paper

Numbering follows the IPL version. Each kind of statement (Observation, Lemma, Corollary, Theorem,
Proposition) has its own counter.

### Notation

- $`G = (V,E)`$ is a finite, undirected, simple graph. $`N(v)`$ is the open neighborhood,
  $`N[v] = N(v) \cup \{v\}`$, $`d(v) = |N(v)|`$, and $`\Delta`$ is the maximum degree.
- $`[k] = \{1, \dots, k\}`$. For $`f : V \to [k]`$ and $`S \subseteq V`$, $`f(S) = \sum_{u \in S} f(u)`$.
- $`f`$ is an **additive $`k`$-coloring** if $`f(N(u)) \ne f(N(v))`$ for every edge $`uv`$. The
  **additive chromatic number** $`\eta(G)`$ is the least such $`k`$. This is the Additive Coloring
  Problem (ACP), also called lucky labeling.
- **Additive Coloring Conjecture** (ref. [5]): $`\eta(G) \le \chi(G)`$ for every graph $`G`$.
- $`u, v`$ are **true twins** if $`N[u] = N[v]`$.
- For a DAG $`D = (V,A)`$, $`N_D(v)`$ is the set of vertices joined to $`v`$ by an arc in either
  direction, and $`G(D)`$ is the underlying graph.
  - $`D`$ **represents an acyclic orientation** of $`G`$ if $`G(D) \cong G`$.
  - $`f`$ is a **topological additive $`k`$-numbering** if $`f(N(u)) < f(N(v))`$ for every arc
    $`(u,v)`$. $`\eta_t(D)`$ is the least such $`k`$, or $`+\infty`$ if there is none (ref. [6]).
  - Then $`\eta(G) = \min\{\eta_t(D) : D`$ represents an acyclic orientation of $`G\}`$.
- $`G_1 \lor G_2`$ is the **join**: the disjoint union plus all edges between $`V(G_1)`$ and $`V(G_2)`$.
- A **split graph** $`G = (Q \cup S, E)`$ has a clique $`Q = \{u_1, \dots, u_q\}`$ and a stable set
  $`S = \{v_1, \dots, v_s\}`$. $`Q`$ is assumed maximal unless said otherwise.
- **Families.**
  - Fan: $`F_n = P_{n+1} \lor K_1`$ ($`n \ge 3`$).
  - Windmill: $`W_n^m = mK_{n-1} \lor K_1`$ ($`n \ge 3`$, $`m \ge 2`$).
  - Wheel: $`W_n = C_n \lor K_1`$ ($`n \ge 4`$).
  - Complete split: a clique $`Q'`$ with $`|Q'| \ge 1`$, a stable set $`S'`$ with $`|S'| \ge 2`$, and all
    edges between them.
  - Thin headless spider of order $`q \ge 2`$: a split graph with $`|Q| = |S| = q`$ and edges $`u_i v_i`$
    between $`Q`$ and $`S`$.
  - Thick headless spider of order $`q \ge 2`$: the same with edges $`u_i v_j`$ for $`i \ne j`$. It is
    the complement of the thin one.
  - Sun: from $`G`$ and $`U = \{u_1, \dots, u_m\} \subseteq V(G)`$, add $`v_1, \dots, v_m`$ and the edges
    $`u_i v_{i-1}`$, $`u_i v_i`$ (indices mod $`m`$).
  - Complete sun $`KS_m`$: $`G = K_m`$. Cycle sun $`CS_m`$: $`G = C_m`$. Wheel sun $`WS_m`$:
    $`G = W_m`$ (with hub $`w`$).

### Main results

- **§2 (regular bipartite and complete multipartite graphs).**
  - Observation 1: $`\eta(G) = 1`$ iff $`d(u) \ne d(v)`$ for every edge $`uv`$.
  - Lemma 1: let $`G = (U \cup V, E)`$ be bipartite with $`d(u) < 2d(v)`$ for all $`v \in V`$ and
    $`u \in N(v)`$. Then $`\eta(G) = 1`$ if adjacent degrees always differ, and $`\eta(G) = 2`$
    otherwise. Labeling: 2 on $`U`$, 1 on $`V`$.
  - Corollary 1: regular bipartite graphs have $`\eta(G) = 2`$.
  - Lemma 2 (ref. [6], Prop. 3; also proved in the formalization): a complete $`r`$-partite digraph $`D`$ has
    $`\eta_t(D) < \infty`$ iff it is monotone. In that case
    $`\eta_t(D) = \max_i \lceil s_i/|V_i| \rceil`$, with $`s_r = |V_r|`$ and
    $`s_i = \max\{1 + s_{i+1}, |V_i|\}`$.
  - **Theorem 1:** let $`G`$ be complete $`r`$-partite with parts $`|V_1| \ge \dots \ge |V_r|`$. Then
    $`\eta(G) = \max_i \lceil s_i/|V_i| \rceil`$ (the same $`s_i`$), and $`\eta(G) \le r`$. Hence the
    conjecture holds for complete multipartite graphs.
    - The orientation from larger to smaller parts is optimal among all monotone orientations: an
      exchange argument shows $`s'_i \ge s_i`$.
    - The bound $`s_i \le |V_i|(r - i + 1)`$ is proved by induction.
- **§3 (join with complete graphs).**
  - Observation 2: if the vertices of $`T`$ are pairwise true twins, then $`\eta(G) \ge |T|`$.
  - **Theorem 2:** if $`G`$ has $`n`$ vertices and maximum degree $`\Delta`$, then
    $`\eta(G \lor K_q) = \max\{\eta(G), q\}`$ for all $`q \le n - \Delta - 1`$. Labeling: keep an optimal
    $`f`$ on $`G`$ and label $`u_i`$ with $`i`$.
    - The bound on $`q`$ is needed. For $`G^*`$ of Figure 1 (the octahedron $`K_{2,2,2}`$, so
      $`n - \Delta = 2`$), $`\eta(G^*) = 2`$ but $`\eta(G^* \lor K_2) = 3`$.
    - If the conjecture holds for $`G`$, it holds for $`G \lor K_q`$, since
      $`\chi(G \lor K_q) = \chi(G) + q`$.
  - **Consequences** (without universal vertices, $`\eta(G \lor K_1) = \eta(G)`$):
    - fans: $`\eta(F_n) = 2`$, since $`\eta(P_{n+1}) = 2`$;
    - windmills: $`\eta(W_n^m) = n - 1`$;
    - wheels: $`\eta(W_n) = 2`$ for even $`n`$ (Corollary 1), and $`\eta(W_n) = 3`$ for odd $`n`$, by
      Proposition 1: $`\eta(C_n) = 3`$ for odd $`n \ge 5`$.
- **§4 (split graphs).**
  - **Theorem 3:** let $`G = (Q \cup S, E)`$ be split with $`Q`$ maximal, and let $`T \subseteq Q`$ be
    nonempty with pairwise distinct degrees. Then $`\eta(G) \le |Q| - |T| + 1`$.
    - Labeling: $`1, \dots, q-t`$ on $`Q \setminus T`$, and $`q - t + 1`$ on $`T \cup S`$.
    - With $`|T| = 1`$, $`\eta(G) \le |Q| \le \chi(G)`$: **the conjecture holds for split graphs.**
  - Proposition 2: complete splits have $`\eta(G) = |Q'|`$.
  - Lemma 3 (ref. [6], Prop. 1; also proved in the formalization): let the vertices of a DAG be ordered topologically, let
    $`Q`$ be a clique of $`G(D)`$, and let $`q_F, q_L`$ be its first and last vertices. Then
    $`\eta_t(D) \ge \lceil (d(q_F) + 1)/(d(q_L) - |Q| + 2) \rceil`$.
  - Corollary 2: if $`d_1, d_2`$ are the smallest and largest degrees of a clique $`Q`$, then
    $`\eta(G) \ge \lceil (d_1 + 1)/(d_2 - |Q| + 2) \rceil`$.
  - Proposition 3: thin and thick headless spiders of order $`q`$ have
    $`\eta(G) = \lceil (q+1)/2 \rceil`$.
  - Proposition 4: $`\eta(KS_m) = \lceil (m+2)/3 \rceil`$ for $`m \ge 3`$.
- **§5 (other suns).** Proposition 5: $`\eta(CS_m) = \eta(WS_m) = 2`$ for $`m \ge 4`$.
- **§6 (a tool).** An integer programming model, solved with CPLEX, checks the conjecture on all
  connected graphs with up to 10 vertices (about 12 million graphs).

### Appendix (arXiv version, ref. [7])

- **A. Proofs of Propositions 1–5.**
  - Explicit labelings for the upper bounds.
  - Lower bounds:
    - Prop 1: a parity argument on a directed path of 3 vertices with sums in $`\{2,3,4\}`$;
    - Props 3 and 4: Corollary 2;
    - Prop 3, thick spiders: a pigeonhole argument.
  - Proposition 4 uses a permutation $`\mathfrak p`$ of $`[m]`$ and its inverse $`\mathfrak q`$, and a case
    analysis of $`f(v_i) = 2r - \mathfrak q(i) + f(u_i) - f(v_{i-1})`$ modulo 3 and 6.
- **B. The ACP solver.**
  - **Formulation $`\mathscr F`$.** Integer variables $`k`$ and $`f(v)`$; binary $`z(u,v)`$ that
    orients each edge; big-M constraints
    $`f(N(u)) - f(N(v)) + M_{uv} z(u,v) \le M_{uv} - 1`$ with
    $`M_{uv} = 1 + |N(u) \setminus N(v)| \cdot UB - |N(v) \setminus N(u)|`$.
  - **$`\mathscr F_1`$** adds the valid inequalities $`z(v,w) + z(w,u) \le 1`$ for nonadjacent $`u, v`$ and
    $`w \in N(u) \subseteq N(v)`$.
  - **$`\mathscr F_2`$** breaks symmetries between false twins and true twins.
  - Experiments on random graphs with 20–30 vertices, and on all connected graphs with up to 10
    vertices.
  - **Closed additive colorings.** $`f(N[u]) \ne f(N[v])`$ on edges, for graphs without true twins, gives
    $`\eta[G]`$.
    - $`\eta[G] \le \chi(G)`$ holds up to 10 vertices.
    - It fails in general: subdividing each edge of $`K_n`$ ($`n \ge 4`$) twice gives
      $`\chi = 3`$ and $`\eta[G] \ge n`$. The smallest instance has 16 vertices, with $`\eta[G] = 4`$.
- **C. Figures** of the families and of optimal additive colorings.

---

## 2. Remarks on the paper

Found while preparing and writing the formalization. None affects a result.

- **Proof of Theorem 1, optimality.** The step "Due to the ordering in the cardinality of sets of
  $`V(D)`$, $`i \ge j`$" is false.
  - For part sizes $`(3, 1)`$ and $`D'`$ ordered as $`(1, 3)`$, we get $`i = 1`$ and $`j = 2`$.
  - The inequality $`s'_j \ge s_i`$ that the step is used for also fails, e.g. for sizes
    $`(5,5,5,5,4,4)`$ against $`(4,4,5,5,5,5)`$.
  - An exhaustive check over all multisets of at most 6 sizes $`\le 5`$ found 4592
    counterexamples to $`i \ge j`$ and 1001 to $`s'_j \ge s_i`$, but none to the theorem. The
    first claim, $`s'_i \ge s_i`$, holds in every case.
  - A correct argument: write $`s_i = \max_{t \ge i}(n_t + t - i)`$. Then
    $`\max_i \lceil s_i/n_i\rceil \le k`$ iff $`n_t + (t - i) \le k\,n_i`$ for all $`i \le t`$.
    For $`i \le t`$ in the decreasing order, the parts with sizes in $`[n_t, n_i]`$ occupy at
    least $`t - i + 1`$ positions of any other order. If $`a \le b`$ are the first and last of
    them, the condition at $`(a, b)`$ gives the condition at $`(i, t)`$. This argument is in the
    formalization (`mp_bound_sorted_le`).
- **Proof of Proposition 4, case 4** ($`m \equiv 2 \pmod 6`$, $`i = \lfloor m/2\rfloor + 1`$).
  - The paper writes $`r = m/3 + 1`$ (not an integer here) and $`f(v_{i-1}) = 1`$.
  - In fact $`r = (m+4)/3`$, so $`f(v_{i-1}) = r + 1 - \lceil m/3 \rceil = 2`$, and
    $`f(v_i) = 2 = 3r - m - f(v_{i-1})`$.
  - The claimed recurrence still holds; it was checked for all $`m < 400`$ and proved in Isabelle and in Mizar.

- **Brute-force check.** The exact formulas were checked against $`\eta`$ computed by brute force:
  - $`C_5, C_7, C_9`$;
  - thin and thick spiders with $`q \le 6`$;
  - $`KS_m`$ with $`m \le 7`$;
  - $`CS_m`$ and $`WS_m`$ with $`m \le 8`$;
  - 13 complete multipartite graphs.

  All of them agree.
- **The explicit labelings were checked too**, as additive colorings with the claimed number of labels:
  - Prop 1 for odd $`n \le 59`$;
  - Prop 3 for $`q \le 60`$;
  - Prop 4 for $`m \le 120`$ (including that $`\mathfrak p`$ and $`\mathfrak q`$ are inverse
    permutations);
  - Prop 5 for $`m \le 60`$;
  - Theorem 3 on 3000 random split graphs.
- **Corollary 1 needs at least one edge.** A 0-regular bipartite graph has $`\eta = 1`$.
- **Intro: "non-3-colorable planar graphs with girth at least 13".** By Grötzsch's theorem every
  triangle-free planar graph is 3-colorable, so this class is empty. The case covered by ref. [3]'s bound
  $`\eta \le 4`$ is vacuous. The girth-26 case (non-bipartite, $`\eta \le 3 \le \chi`$) is not.
- **Proof of Theorem 3, last case.** "Suppose that $`(q-t+1)(r_j - r_k) = \alpha`$" should read
  $`(q-t+1)(r_k - r_j) = \alpha`$. The contradiction is the same.
- **Proof of Proposition 2.** "we obtain $`\eta(G) = |Q| - 1`$" should read $`\eta(G) \le |Q| - 1`$.
  Equality comes from the true-twin bound. Theorem 3 applies because $`d(u) = |Q'| - 1 + |S'|`$ and
  $`d(v) = |Q'|`$ differ, which uses $`|S'| \ge 2`$.
- **Implicit facts used by §3.**
  - $`\eta(P_{n+1}) = 2`$: the upper bound comes from trees (ref. [5]). The LaTeX source has a
    commented-out citation to Orlow, see [`others/`](others/README.md).
  - $`\eta(mK_{n-1}) = n - 1`$, through $`\eta(K_n) = n`$ and $`\eta`$ of a disjoint union being the
    maximum.
  - The hypothesis $`q = 1 \le n - \Delta - 1`$, i.e. no universal vertex, holds for $`P_{n+1}`$
    ($`n \ge 3`$), $`mK_{n-1}`$ ($`m \ge 2`$) and $`C_n`$ ($`n \ge 4`$).
- **$`\eta(G) = \min \eta_t(D)`$** is stated as "clearly". It holds because an additive coloring orients
  every edge from the smaller to the larger sum, and this orientation is acyclic.
- **The intro bound $`\eta(G) \le \Delta^2 - \Delta + 1`$** (ref. [2]) needs $`\Delta \ge 2`$.

---

## 3. The formalizations

Sections 1–5, with the proofs of Propositions 1–5 from the appendix, are formalized twice:
in **Isabelle/HOL** (Isabelle2025-2) and in **Mizar** (8.1.15, MML 5.94.1493).

### Isabelle/HOL

See [`isabelle/README.md`](isabelle/README.md).

- **Libraries.** It builds on two AFP entries: the graph library *Undirected Graph Theory*
  (C. Edmonds) and *Girth Chromatic* (L. Noschinski). The chromatic number is proved equal to
  Noschinski's `chromatic_number`.
- **Status.** Everything is proved, with no `sorry`. The session checks in about 50 s.
- **No assumptions.** The two lemmas cited from ref. [6] (Lemmas 2 and 3) are proved as well, so
  every result is unconditional. This includes η(G) = min η_t(D) and η(P_N) = 2, which the paper
  takes as known.
- **Requirements and installation.** [Isabelle2025-2](https://isabelle.in.tum.de) and the AFP
  entries *Undirected Graph Theory*, *Girth Chromatic* and the seven entries their ROOT files refer
  to (listed in `isabelle/afp/ROOTS`), from the [AFP](https://www.isa-afp.org/download/) release for
  Isabelle2025-2. Run `AFP=/path/to/afp/thys isabelle/build.sh` (or copy the entries into
  `isabelle/afp/`); `isabelle/jedit.sh` opens the IDE. Details are in
  [`isabelle/README.md`](isabelle/README.md).
- **Main theorems.**
  - `theorem_1`, `theorem_2`, `theorem_3`, `proposition_1` … `proposition_5_wheel`;
  - `fan`, `windmill`, `wheel`;
  - the conjecture for complete multipartite graphs, joins and split graphs:
    `theorem_1_conjecture`, `theorem_2_conjecture`, `split_graph_conjecture`.

### Mizar

See [`mizar/README.md`](mizar/README.md).

- **Libraries.** Graphs are finite irreflexive symmetric `RelStr`s, and χ(G) is `chromatic#` of
  the MML article MYCIELSK. Sums of labels are the bag sums of NAT_5.
- **Status.** A single article, `mizar/text/acn.miz` (about 11000 lines, 200 theorems), with no
  unproved steps. It verifies in about 55 s.
- **No assumptions.** As in Isabelle, Lemmas 2 and 3 of ref. [6], η(G) = min η_t(D),
  η(P_N) = 2, χ(G ∨ K_q) ≥ χ(G) + q and the existence of additive colorings are proved. Each
  family of graphs comes with an existence theorem.
- **Requirements and installation.** The [Mizar system](https://mizar.uwb.edu.pl/system/) 8.1.15
  with MML 5.94.1493, Python 3. Set `MIZFILES` and the `PATH` (a local copy can go in
  `mizar/system/`, which git ignores) and run `mizar/miz.sh acn`.
- **Main theorems.**
  - `Theorem1`, `Theorem2`, `Theorem3`, `Proposition1` … `Proposition5Wheel`;
  - `Lemma2Value`, `Lemma2Finite`, `Lemma3`, `Corollary2`, `EtaMinEtaT`;
  - `Fan`, `Windmill`, `Wheel`;
  - the conjecture for complete multipartite graphs, joins and split graphs:
    `Theorem1Conjecture`, `Theorem2Conjecture`, `SplitConjecture`.

---

## License

MIT (see [LICENSE](LICENSE)). The papers summarized in `references/` and `others/`, and the paper
itself, are copyrighted by their publishers and are not included.

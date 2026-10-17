# Other references (related to additive colorings, not cited in the paper's bibliography)

These are related papers on additive colorings (lucky labelings), their list and closed-neighborhood
variants, and the two main techniques of the area: the Combinatorial Nullstellensatz and discharging.
Papers cited by the paper are summarized in [`references/README.md`](../references/README.md).

| Key | Reference | DOI / notes | File |
|---|---|---|---|
| AD13 | A. Ahadi, A. Dehghan, *The inapproximability for the (0,1)-additive number*, arXiv:1306.0182 (2013) | published in Discrete Math. Theor. Comput. Sci. 17(3) (2016), doi:10.46298/dmtcs.2145. The file is the arXiv version | `ahadi-dehghan-2013.pdf` |
| Alo99 | N. Alon, *Combinatorial Nullstellensatz*, Combin. Probab. Comput. 8 (1999) 7–29 | doi:10.1017/S0963548398003411. Used by [2], [3], [4], [5] | `alon-1999.pdf` |
| AHP16 | M. Axenovich, J. Harant, J. Przybyło, R. Soták, M. Voigt, J. Weidelich, *A note on adjacent vertex distinguishing colorings of graphs*, Discrete Appl. Math. 205 (2016) 1–7 | doi:10.1016/j.dam.2015.12.005. Mentioned (not in the bibliography) in the paper's Appendix B | `axenovich-etal-2016.pdf` |
| BDJ15 | A. Brandt, J. Diemunsch, S. Jahanbekam, *Lucky choice number of planar graphs with given girth*, preprint (January 2015) | earlier version of ref. [4], see [references](../references/README.md) | `brandt-diemunsch-jahanbekam-2015.pdf` |
| CW17 | D. W. Cranston, D. B. West, *An introduction to the discharging method via graph coloring*, Discrete Math. 340 (2017) 766–793 | doi:10.1016/j.disc.2016.11.022. The technique of [4] | `cranston-west-2017.pdf` |
| Orl09 | N. Orlow, *Advances in lucky labelling graphs, Fibsum graphs, and 3-regular graph decompositions*, REGS 2009 report (University of Illinois), August 17, 2009 | unpublished. Cited in a commented-out `\cite{ORLOW}` of the LaTeX source, next to $`\eta(P_{n+1}) = 2`$ | `orlow-2009.pdf` |
| Sea12a | B. Seamone, *On weight choosability and additive choosability numbers of graphs*, arXiv:1210.6944 (2012) | | `seamone-2012a.pdf` |
| Sea12b | B. Seamone, *The 1-2-3 Conjecture and related problems: a survey*, arXiv:1211.5122 (2012) | | `seamone-2012b.pdf` |

## Results per paper

Statements only (proofs not checked). Notation as in [`references/README.md`](../references/README.md).

### Ahadi, Dehghan 2013 — *The inapproximability for the (0,1)-additive number* (arXiv:1306.0182; DMTCS 17(3), 2016)
- **Thm 1.** For every $`k`$ there is a graph with $`\eta(G) \le k \le \eta_\ell(G)/2`$. This disproves
  Seamone's Additive List Coloring Conjecture $`\eta = \eta_\ell`$ (Sea12a, Sea12b): the gap
  $`\eta_\ell - \eta`$ is unbounded.
- **Thm 2.**
  - (i) $`\eta(G) \ge \lceil \omega / (n - \omega + 1) \rceil`$ for every graph, where $`\omega`$ is the
    clique number.
  - (ii) If $`G`$ is regular and $`\omega > (n+4)/3`$, then $`\eta(G) \ge 3`$.
- A **(0,1)-additive labeling** uses labels in $`\{0,1\}`$. A graph may have none.
- **Thm 3.** Deciding whether a planar triangle-free graph has a (0,1)-additive labeling is NP-complete.
- **Thm 4.** Let $`\eta_1(G)`$ be the minimum number of 1's in a (0,1)-additive labeling. If
  P $`\ne`$ NP, then $`\eta_1`$ has no polynomial $`n^{1-\varepsilon}`$-approximation on planar graphs.
- **Thm 5.** Deciding whether a perfect graph has a (0,1)-additive labeling is NP-complete.

Thm 2(i) is the bound that ref. [6] (Prop. 1) improves. The paper's Corollary 2 is the undirected
version of the latter.

### Alon 1999 — *Combinatorial Nullstellensatz* (Combin. Probab. Comput. 8)
- **Thm 1.1.** If $`f`$ vanishes on all common zeros of $`g_i = \prod_{s \in S_i} (x_i - s)`$, then
  $`f = \sum h_i g_i`$ with $`\deg h_i \le \deg f - \deg g_i`$.
- **Thm 1.2 (the Nullstellensatz used in the area).** Suppose $`\deg f = \sum t_i`$ and the coefficient
  of $`\prod x_i^{t_i}`$ in $`f`$ is nonzero. Then for any sets $`S_i`$ with $`|S_i| > t_i`$ there is
  $`s \in \prod S_i`$ with $`f(s) \ne 0`$.
- **Applications** (one section each):
  - restricted sums (Cauchy–Davenport, Erdős–Heilbronn, Dias da Silva–Hamidoune);
  - set addition in vector spaces over prime fields;
  - graphs, subgraphs and cubes (regular subgraphs, covering the cube by hyperplanes);
  - graph coloring, through the graph polynomial: choosability of graphs with an orientation with
    few Eulerian subgraphs (Alon–Tarsi);
  - the permanent lemma.

In the additive coloring papers it is applied to $`\prod_{uv \in E} (S(u) - S(v))`$, where
$`S(v) = \sum_{w \in N(v)} x_w`$ (refs. [2], [3], [4], [5]).

### Axenovich, Harant, Przybyło, Soták, Voigt, Weidelich 2016 — *A note on adjacent vertex distinguishing colorings of graphs* (DAM 205)
Closed neighborhoods: $`S[u] = \sum_{w \in N[u]} f(w)`$. A labeling is *closed distinguishing* if
$`S[u] \ne S[v]`$ for adjacent $`u, v`$ with $`N[u] \ne N[v]`$. $`\mathrm{dis}[G]`$ is the least $`k`$,
and $`\mathrm{dis}_\ell[G]`$ its list version. $`\mathrm{dis}(G)`$ is the open version, $`= \eta(G)`$.
- **Thm 1 (Norin, see ref. [3]).** $`\mathrm{dis}(G) \le n_1 \cdots n_r`$ for pairwise coprime
  $`n_i \ge \mathrm{col}(G)`$, where $`r = \chi(G)`$.
- **Thm 2.** If $`\Delta(G) = \Delta \ge 2`$:
  - $`\mathrm{dis}[G] \le \mathrm{dis}_\ell[G] \le \Delta^2 - \Delta + 1`$;
  - for every $`\Delta`$ there is $`G`$ with $`\mathrm{dis}[G] \ge (1 - o(1))\Delta^2`$;
  - for infinitely many $`\Delta`$ the bound is attained.
- **Thm 3.** With coloring number $`k`$, $`\mathrm{dis}_\ell(G) \le (k-1)\Delta + 1 \le \Delta^2 + 1`$.
- **Cor 4.** For planar $`G`$, $`\mathrm{dis}_\ell(G) \le 5\Delta + 1`$, which beats 468 (ref. [3]) when
  $`\Delta \le 93`$.
- **Thm 5.** For bipartite graphs that are not stars, bounds on $`\mathrm{dis}[G]`$ in terms of
  $`\Delta_A, \Delta_B`$ and the least degrees $`\ge 2`$. So $`\mathrm{dis}[G]`$ can be arbitrarily large even
  for bipartite graphs: the closed analogue of the conjecture fails.
- **Thm 6.** For a tree $`T \ne K_2`$, $`\mathrm{dis}_\ell[T] \le 3`$ and $`\mathrm{dis}[T] \le 2`$, with
  a variant for lists of size 2.
- **Cor 7.** If the edges are covered by $`k`$ induced strong forests, then
  $`\mathrm{dis}[G] \le p_1 \cdots p_k`$ (pairwise coprime $`p_i \ge 4`$).

In Appendix B the paper defines $`\eta[G]`$ (for graphs without true twins) and gives counterexamples
to $`\eta[G] \le \chi(G)`$. It mentions this paper as an independent source of the same bound
$`\Delta^2 - \Delta + 1`$ and of another family of counterexamples.

### Brandt, Diemunsch, Jahanbekam 2015 — *Lucky choice number of planar graphs with given girth* (preprint)
The preprint of ref. [4], with $`\eta_\ell`$ in place of $`\mathrm{ch}_\Sigma`$.
- **Main results.**
  - Thm 4.1: $`\eta_\ell(G) \le 19`$ for planar graphs of girth $`\ge 5`$;
  - Thm 4.2: $`\le 9`$ for girth $`\ge 6`$;
  - Thm 4.3: $`\le 8`$ for girth $`\ge 7`$;
  - Thm 1.6: $`\eta(G) \le 3`$ for girth $`\ge 26`$.
- **Reducible configurations.** Lemmas 3.1–3.4, the same as in the published version.
- **Cor 4.6.** $`\eta_\ell(C_{2n+1}) = 3`$ for $`n \ge 13`$.
- **Differences with the published version.**
  - Different authors: Diemunsch in place of White.
  - Different title.
  - The published version adds Thm 1.4 (girth $`\ge 10 \Rightarrow \chi_\Sigma \le 4`$).
  - The published version uses the notation $`\chi_\Sigma`$, $`\mathrm{ch}_\Sigma`$.

### Cranston, West 2017 — *An introduction to the discharging method via graph coloring* (Discrete Math. 340)
A how-to guide to discharging, with graph coloring examples. Sections:
1. introduction;
2. structure and coloring of sparse graphs (maximum average degree, reducible configurations);
3. discharging on plane graphs (face charges, Euler's formula, girth);
4. list coloring, including squares of planar graphs and $`\chi_\ell(G^2)`$ for large girth;
5. edge-coloring and list edge-coloring.

New proofs and open problems are spread through the sections.

It is background for ref. [4], whose proofs are discharging arguments with reducible configurations.

### Orlow 2009 — *Advances in lucky labelling graphs, Fibsum graphs, and 3-regular graph decompositions* (REGS report)
A four-page summary from the 2009 Research Experiences for Graduate Students program (D. B. West).
- **Lucky labelings of trees.** A constructive proof (an algorithm) that trees have lucky labelings with
  labels $`\{1, 2\}`$.
  - Start with all weights 2 and root the tree at a leaf.
  - Do a depth-first search. At a vertex of degree $`\ge 2`$ whose sum and whose parent's sum are both
    even and equal, change the weight of its left child to 1.
  - The proof uses three invariants: each sum changes at most once, no two weight-1 vertices are
    adjacent, and no vertex has two weight-1 neighbors.
  - A variant (Fox) drops "and equal".
- **Fibsum graphs.** Vertices $`1..n`$ with $`u \sim v`$ iff $`u + v`$ is a Fibonacci number. A spanning
  path exists for $`n = F_k`$ (with Kinnersly).
- **3-regular graphs.** Work in progress on decomposing a 3-regular graph into a spanning tree, cycles and
  a matching.

The paper uses $`\eta(P_{n+1}) = 2`$ for fans, where the LaTeX source has `%(see \cite{ORLOW})`. The
labeling also follows from $`\eta(T) \le 2`$ for trees (ref. [5]).

### Seamone 2012a — *On weight choosability and additive choosability numbers of graphs* (arXiv:1210.6944)
Mainly about list versions of the 1-2-3 Conjecture (edge weightings) and the 1-2 Conjecture (total
weightings), via the permanent method of Bartnicki–Grytczuk–Niwczyk.
- **Thm 3.1.**
  - $`\mathrm{ch}^e_\Sigma(G) \le 2\Delta + 1`$ for nice graphs;
  - $`\mathrm{ch}^t_\Sigma(G) \le \lceil 3\Delta/2 \rceil + 1`$ for every graph;
  - $`\mathrm{ch}^e_\Pi(G) \le 4\Delta + 2`$ (Thm 3.9).
- **Corollaries 3.10–3.12.** Bounds for $`(k,l)`$-weight choosability.
- **§5, additive colourings** ($`\chi^v_\Sigma = \eta`$, $`\mathrm{ch}^v_\Sigma = \eta_\ell`$):
  - **Additive List Colouring Conjecture.** $`\mathrm{ch}^v_\Sigma(G) = \chi^v_\Sigma(G)`$ (disproved by
    AD13).
  - **Prop 5.1.** $`\mathrm{ch}^v_\Sigma(K_n) = n`$.
  - **Thm 5.3.** If $`G`$ is $`d`$-degenerate, then $`\mathrm{ch}^v_\Sigma(G) \le d\Delta + 1`$. Hence
    $`\Delta(\chi - 1) + 1`$ for chordal graphs, $`2\Delta + 1`$ for $`K_4`$-minor-free graphs, and
    $`5\Delta + 1`$ for planar graphs.
  - **Thm 5.4.** For complete multipartite $`K_{t_1, \dots, t_k}`$ with $`t = \min t_i`$,
    $`\mathrm{ch}^v_\Sigma(G) \le \lceil (k-1)/t \rceil + 1`$. So the conjecture holds, even for lists,
    for complete multipartite graphs.

Thm 5.4 is a list-version upper bound for the graphs of the paper's Theorem 1. The paper gives the exact
value of $`\eta`$ there.

### Seamone 2012b — *The 1-2-3 Conjecture and related problems: a survey* (arXiv:1211.5122)
A survey of colourings by sums, products, multisets and sets of edge, vertex and total weightings.
- **§4, vertex weightings.**
  - The Additive Colouring Conjecture.
  - NP-completeness (ref. [1]).
  - Prop 4.5: $`\chi^v_m(G) \le \chi(G)`$ for multisets; Prop 4.6 for sets.
  - Every graph has an additive colouring from some set of $`\chi(G)`$ integers. More precisely, the
    smallest such set of reals has size exactly $`\chi^v_m(G)`$.
  - $`\chi^v_\Sigma(K_n) = n`$, and the planar bounds of ref. [3].
- **§5, list versions.**
  - Additive List Colouring Conjecture.
  - Thm 5.9: ref. [2]'s bound $`\Delta^2 - \Delta + 1`$.
  - Thm 5.10: $`d\Delta + 1`$ for $`d`$-degenerate graphs (as in Sea12a).
- **Other sections.** The 1-2-3 and 1-2 Conjectures, with the best known bounds in 2012 (e.g.
  Kalkowski–Karoński–Pfender: edge weights $`\{1, \dots, 5\}`$ suffice), and open problems.

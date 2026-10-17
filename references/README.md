# References of Severín, *On the additive chromatic number of several families of graphs* (IPL 158, 2020, arXiv:1602.07675)

The numbers are those of the paper's bibliography.

| # | Reference | DOI | File |
|---|---|---|---|
| 1 | A. Ahadi, A. Dehghan, M. Kazemi, E. Mollaahmadi, *Computation of lucky number of planar graphs is NP-hard*, Inf. Process. Lett. 112 (2012) 109–112 | doi:10.1016/j.ipl.2011.11.002 | `01-ahadi-etal-2012.pdf` |
| 2 | S. Akbari, M. Ghanbari, R. Manaviyat, S. Zare, *On the lucky choice number of graphs*, Graphs Comb. 29 (2013) 157–163 | doi:10.1007/s00373-011-1112-4 | `02-akbari-etal-2013.pdf` |
| 3 | T. Bartnicki, B. Bosek, S. Czerwiński, J. Grytczuk, G. Matecki, W. Żelazny, *Additive colorings of planar graphs*, Graphs Comb. 30 (2014) 1087–1098 | doi:10.1007/s00373-013-1331-y | `03-bartnicki-etal-2014.pdf` |
| 4 | A. Brandt, S. Jahanbekam, J. White, *Additive list coloring of planar graphs with given girth*, Discuss. Math. Graph Theory 40 (2020) 855–873 (cited "in press") | doi:10.7151/dmgt.2156 | `04-brandt-jahanbekam-white-2020.pdf` |
| 5 | S. Czerwiński, J. Grytczuk, W. Żelazny, *Lucky labelings of graphs*, Inf. Process. Lett. 109 (2009) 1078–1081 | doi:10.1016/j.ipl.2009.05.011 | `05-czerwinski-grytczuk-zelazny-2009.pdf` |
| 6 | J. Marenco, M. Mydlarz, D. Severín, *Topological additive numbering of directed acyclic graphs*, Inf. Process. Lett. 115 (2015) 199–202 | doi:10.1016/j.ipl.2014.09.011 | `06-marenco-mydlarz-severin-2015.pdf` |
| 7 | D. Severín, *Appendix and source code of ACP solver for the paper On the additive chromatic number of several families of graphs*, Mendeley Data, v1 (2020) | doi:10.17632/9zwm2nxvbs.1 | (no file: the appendix is also part of the arXiv version, [`../severin-additive-chromatic-number.pdf`](../severin-additive-chromatic-number.pdf)) |

File names follow `NN-author-year.pdf`, where `author` lists the authors' surnames (`etal` for four or
more authors) and `year` is the year of publication.

The [4] file is the published DMGT version (open access). An earlier preprint of the same work, by
Brandt, Diemunsch and Jahanbekam with the title *Lucky choice number of planar graphs with given
girth* (2015), is in [`others/`](../others/README.md).

## Results per reference

Statements only (proofs not checked). Notation used below, unless a paper says otherwise:
- $`G = (V,E)`$ is a finite simple graph, $`N(v)`$ is the open neighborhood, $`d(v) = |N(v)|`$ the
  degree, and $`\Delta`$ the maximum degree;
- for a labeling $`f : V \to \mathbb{N}`$, $`S(v) = f(N(v)) = \sum_{w \in N(v)} f(w)`$;
- $`f`$ is **lucky** (or **additive**) if $`S(u) \ne S(v)`$ for every edge $`uv`$;
- $`\eta(G)`$ is the **lucky number** (or **additive chromatic number**): the least $`k`$ such that
  $`G`$ has a lucky labeling with labels in $`[k] = \{1,\dots,k\}`$. [4] writes it $`\chi_\Sigma(G)`$;
- $`\eta_\ell(G)`$ (also $`\mathrm{ch}_\Sigma(G)`$) is the **lucky choice number**: the least $`k`$ such
  that every assignment of lists of size $`k`$ to the vertices admits a lucky labeling from the lists.
  Clearly $`\eta(G) \le \eta_\ell(G)`$.

### [1] Ahadi, Dehghan, Kazemi, Mollaahmadi 2012 — *Computation of lucky number of planar graphs is NP-hard* (IPL 112)
- **Remark.** $`\eta(G) = 1`$ iff no two adjacent vertices have the same degree. So deciding
  $`\eta(G) = 1`$ is polynomial.
- **Thm 1.** Deciding whether $`\eta(G) = 2`$ is NP-complete, even for planar 3-colorable graphs.
  - The reduction is from Planar 3-SAT (type 2), with gadgets $`B(x_j)`$ per variable and $`A(c_j)`$ per
    clause.
  - Lemma 1: in a lucky 2-labeling, $`\ell(x_j) + \ell(\lnot x_j) \ge 3`$.
  - Lemma 2: for each clause $`c_j = a \lor b \lor c`$, $`\ell(a) + \ell(b) + \ell(c) < 6`$. The proof
    uses that the lucky number of an odd cycle is 3.
- **Cor 1.** For every $`k > 2`$, deciding $`\eta(G) = 2`$ is NP-complete for graphs with $`\chi(G) = k`$.
- **Thm 2.** For every $`k \ge 2`$, deciding $`\eta(G) = k`$ is NP-complete (reduction from
  3-colorability).
  - A key fact (Fact 1): vertices whose neighborhoods agree except for each other (true twins) get
    distinct labels, so $`k`$ such vertices force $`\eta \ge k`$.

This is the source of "ACP is NP-hard" in the paper's introduction.

### [2] Akbari, Ghanbari, Manaviyat, Zare 2013 — *On the lucky choice number of graphs* (Graphs Comb. 29)
Proved with Alon's Combinatorial Nullstellensatz, applied to
$`\prod_{v_i \sim v_j,\, i<j} (a(v_i) - a(v_j))`$ with $`a(v) = \sum_{w \sim v} x_w`$.
- **Lemma 1.** $`\eta_\ell(G) \le \Delta^2 + 1`$.
- **Thm 2.** If $`G`$ is $`k`$-regular with $`k \ge 2`$, then $`\eta_\ell(G) \le k^2 - k + 1`$.
- **Thm 3.** If $`\Delta \ge 2`$, then $`\eta_\ell(G) \le \Delta^2 - \Delta + 1`$ (induction on $`|V|`$,
  regular case by Thm 2).
- **Thm 4.** If adjacent vertices always have at least $`\lambda`$ common neighbors, then
  $`\eta_\ell(G) \le \Delta(\Delta - \lambda) + 1`$.
- **Cor 1.** For a strongly regular graph $`\mathrm{srg}(n,k,\lambda,\mu)`$, $`\eta_\ell \le k(k-\lambda) + 1`$.
- **Thm 5.** A bipartite graph with an orientation of maximum out-degree $`k`$ is *proper* lucky
  $`(2k+1)`$-choosable: the lucky labeling can be chosen to be a proper coloring as well.
- **Cor 2.** Every forest is proper lucky 3-choosable, and 3 is best possible.

The paper uses Thm 3 ($`\eta(G) \le \Delta^2 - \Delta + 1`$) in the introduction and as the upper bound
$`UB`$ of its integer programming model (Appendix B).

### [3] Bartnicki, Bosek, Czerwiński, Grytczuk, Matecki, Żelazny 2014 — *Additive colorings of planar graphs* (Graphs Comb. 30)
- **Thm 1 (S. Norin).** If $`\chi(G) = r`$, the coloring number is $`\mathrm{col}(G) = k`$, and
  $`n_1, \dots, n_r \ge k`$ are pairwise coprime, then $`\eta(G) \le n_1 \cdots n_r`$. For planar graphs
  this gives $`\eta(G) \le 5544`$ ($`7 \cdot 8 \cdot 9 \cdot 11`$).
- **Lemma 1.** A hypergraph $`H`$ with $`\mathrm{col}(H) = k`$ has $`f : V(H) \to \mathbb{Z}_k`$ with nonzero
  sum on every hyperedge.
- **Lemma 2.** If $`G`$ is bipartite planar with classes $`X, Y`$ and $`H`$ is the hypergraph on $`X`$ whose
  incidence graph is $`G`$, then $`\mathrm{col}(H) \le 12`$.
- **Thm 3** (via the Combinatorial Nullstellensatz). Let $`G`$ be bipartite with an orientation of
  in-degree at most $`k`$, and give each vertex a list of $`k+1`$ reals. Then, for every
  $`q : V \to \mathbb{R}`$, there is a labeling from the lists with $`S(u) + q(u) \ne S(v) + q(v)`$ on every
  edge.
- **Cor 1.** Trees have additive colorings from lists of size 2, and bipartite planar graphs from lists
  of size 3.
- **Thm 4.** Planar graphs with $`\chi(G) \le 3`$ satisfy $`\eta(G) \le 36`$.
- **Thm 5.** Planar graphs satisfy $`\eta(G) \le 468`$.
- **Thm 6.** Planar graphs of girth at least 13 satisfy $`\eta(G) \le 4`$. The proof partitions $`V`$
  into a 2-independent set $`I`$ (labels 1) and a forest $`F`$ (labels $`\{2, 4\}`$).
- **Thm 7.** For every $`r \ge 2`$ there is $`G_r`$ with $`\chi(G_r) = r`$ that has no additive coloring
  over any abelian group of order $`r`$, but has one over $`\mathbb{Z}_{r+1}`$.
- **Thm 8.** For a fixed abelian group $`A`$, deciding whether $`G`$ has an additive coloring over $`A`$ is
  NP-complete if $`|A| \ge 3`$, and polynomial for $`A = \mathbb{Z}_2`$.

The paper cites Thms 4, 5 and 6 in its introduction.

### [4] Brandt, Jahanbekam, White 2020 — *Additive list coloring of planar graphs with given girth* (DMGT 40)
Notation $`\chi_\Sigma`$ (additive coloring number) and $`\mathrm{ch}_\Sigma`$ (its list version).
- **Thm 1.4.** Planar graphs of girth at least 10 satisfy $`\chi_\Sigma(G) \le 4`$. This follows from
  $`I,F`$-partitions of graphs with $`\mathrm{mad}(G) < 5/2`$ (Brandt et al.), improving Thm 6 of [3].
- **Thm 1.7 (main).** Let $`G`$ be planar with girth $`g`$:
  1. if $`g \ge 5`$, then $`\mathrm{ch}_\Sigma(G) \le 19`$ (Thm 3.4);
  2. if $`g \ge 6`$, then $`\mathrm{ch}_\Sigma(G) \le 9`$ (Thm 3.6);
  3. if $`g \ge 7`$, then $`\mathrm{ch}_\Sigma(G) \le 8`$ (Thm 3.7);
  4. if $`g \ge 26`$, then $`\mathrm{ch}_\Sigma(G) \le 3`$ (Thm 3.10).
- The bound 3 for girth at least 26 is best possible for non-bipartite planar graphs, which affirms the
  conjecture for this class.
- **Method.** Discharging, with reducible configurations (Lemmas 3.1, 3.2, 3.5, 3.8) proved by the
  Combinatorial Nullstellensatz and sumset bounds: $`|A_1 \oplus \dots \oplus A_r| \ge 1 + \sum (|A_i| - 1)`$
  (Prop. 1), and $`|A \ominus B| \ge |A| + |B| - 1`$ (Cor. 2).
- The ingredients are $`\mathrm{mad}(G) < 2g/(g-2)`$ for planar graphs of girth $`g`$, and an independent
  set of size $`\ge (n+1)/3`$ in planar triangle-free graphs.

The paper cites item 4 ($`\eta(G) \le 3`$ for girth at least 26).

### [5] Czerwiński, Grytczuk, Żelazny 2009 — *Lucky labelings of graphs* (IPL 109)
Introduces lucky labelings ($`S(v) = 0`$ for isolated vertices).
- **Conjecture 1 (Additive Coloring Conjecture).** $`\eta(G) \le \chi(G)`$ for every graph $`G`$.
- **Remark.** $`\eta(K_n) = n`$, so there is no absolute bound.
- **Prop 1.** Every tree has a lucky labeling modulo $`n`$ for every $`n \ge 3`$.
- **Thm 1.** If $`E(G)`$ decomposes into $`r`$ induced forests, then $`G`$ has a lucky labeling modulo
  $`N = p_1 \cdots p_r`$ (distinct odd primes), so $`\eta(G) \le N`$.
- **Cor 1.** With $`a(G)`$ the acyclic chromatic number, $`\eta(G) \le`$ the product of
  $`\binom{a(G)}{2}`$ distinct odd primes. For planar graphs ($`a \le 5`$) this gives
  $`\eta(G) \le 3 \cdot 5 \cdots 31 = 100\,280\,245\,065`$.
- **Lemma 1 and Prop 2.** Some bipartite graphs, including the unit interval bigraphs, have lucky
  labelings modulo every $`n \ge 3`$.
- **Conjecture 2.** For every $`k`$ there is $`r(k)`$ such that every $`k`$-colorable graph has a proper
  $`r`$-coloring in which any two color classes span a graph of that class.
- **Thm 3** (Combinatorial Nullstellensatz). A bipartite graph with an orientation of maximum out-degree
  $`k`$ has a lucky labeling from any lists of $`k+1`$ complex numbers. Hence $`\eta(T) \le 2`$ for trees,
  and (**Cor 2**) $`\eta(G) \le 3`$ for bipartite planar graphs.
- **Final comments.**
  - Every graph has a lucky labeling from any $`\chi(G)`$ reals that are independent over $`\mathbb{Q}`$.
  - $`\eta(G) > k`$ iff the modified graph polynomial lies in the ideal $`I_{k,n}`$.

The paper takes the conjecture, $`\eta(K_n) = n`$, $`\eta(T) \le 2`$ for trees, and $`\eta \le 3`$ for
planar bipartite graphs from here.

### [6] Marenco, Mydlarz, Severín 2015 — *Topological additive numbering of directed acyclic graphs* (IPL 115)
For a DAG $`D`$, a labeling $`f`$ is a **topological additive numbering** if $`S(u) < S(v)`$ for every
arc $`(u,v)`$. $`\eta_t(D)`$ is the least largest label, when such an $`f`$ exists ($`D \in \mathcal{D}`$).
- **Obs 1.** If $`N(u) \subseteq N(v)`$ and there is a directed path from $`v`$ to $`u`$, then
  $`D \notin \mathcal{D}`$. The condition is not necessary.
- **Basic fact.** $`\eta_t(D) \ge \eta(G(D))`$.
- **Prop 1 (clique bound).** Let $`D \in \mathcal{D}`$ have its vertices ordered topologically, let $`Q`$
  be a clique, and let $`q_F, q_L`$ be its smallest and largest vertices. Then
  $`\eta_t(D) \ge \lceil (d(q_F) + 1)/(d(q_L) - |Q| + 2) \rceil`$. The proof is a pigeonhole argument
  on $`Y_q = f(N(q) \setminus Q) - f(q)`$.
- **Prop 2.** Deciding $`D \in \mathcal{D}`$ is polynomial: it is the feasibility of the LP relaxation of
  an integer program.
- **Monotone digraphs.** An $`r`$-partite digraph is *monotone* if its parts $`V_1, \dots, V_r`$ can be
  ordered so that every arc goes from $`V_i`$ to $`V_j`$ with $`i < j`$. A complete $`r`$-partite digraph
  is in $`\mathcal{D}`$ iff it is monotone.
- **Prop 3.** If $`D`$ is complete monotone $`r`$-partite, then
  $`\eta_t(D) = \max_i \lceil s_i / |V_i| \rceil`$, where $`s_r = |V_r|`$ and
  $`s_i = \max\{1 + s_{i+1}, |V_i|\}`$. Key fact: $`f`$ works iff $`f(V_i) > f(V_{i+1})`$ for all $`i`$.
- **Prop 4.** If $`D`$ is monotone bipartite, then
  $`\eta_t(D) = \max\{\lfloor d(u)/d(v) \rfloor + 1 : v \in V_2,\ u \in N(v)\}`$.
- **Thm 1.** Deciding $`\eta_t(D) = 2`$ is NP-complete even when $`G(D)`$ is planar bipartite (reduction
  from Planar 3-SAT (type 2), following [1]).

The paper uses Prop 3 (its Lemma 2) for complete multipartite graphs, and Prop 1 (its Lemma 3) for the
lower bound of Corollary 2.

### [7] Severín 2020 — Appendix and source code (Mendeley Data)
The proofs of the paper's Propositions 1–5, the integer programming formulation of the solver, the
experiments, and the closed additive colorings. This is the appendix of the arXiv version, summarized in
the main [README](../README.md).

### Thread through the references (relevant to Severín's paper)
- [5] defines the problem and the conjecture.
- [1] (NP-hardness, $`\eta = 1`$ iff adjacent degrees differ) and [6] (the oriented version
  $`\eta_t`$) give the complexity side. [6] is the main tool of the paper: Lemma 2 (complete multipartite)
  and Lemma 3 (clique lower bound) come from it.
- [2], [3], [4] are the upper-bound line:
  - in terms of $`\Delta`$: $`\Delta^2 - \Delta + 1`$ [2];
  - planar graphs: 468, 36 when 3-colorable, and 4 with girth $`\ge 13`$ [3];
  - planar graphs with girth $`\ge 26`$: 3 [4].
  All three use Alon's Combinatorial Nullstellensatz (see [`others/`](../others/README.md)).

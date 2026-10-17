# Isabelle/HOL formalization

Formalization of Sections 1–5 of D. Severín, *On the additive chromatic number of several families
of graphs* (Inf. Process. Lett. 158, 2020), including the proofs of Propositions 1–5 from the
appendix of the arXiv version. See the main [README](../README.md) for the statements.

## Requirements

- **Isabelle2025-2**: <https://isabelle.in.tum.de>.
- **The AFP entries** *Undirected Graph Theory* (C. Edmonds) and *Girth Chromatic* (L. Noschinski),
  from the Archive of Formal Proofs release that matches Isabelle2025-2
  (<https://www.isa-afp.org/download/>).
  - Their ROOT files refer to seven more entries, which must also be present: Card_Partitions,
    Design_Theory, Discrete_Summation, Graph_Theory, List-Index, Nested_Multisets_Ordinals and
    Ordinal. They are listed in `afp/ROOTS`.
  - Only two theories are actually loaded: `Undirected_Graph_Basics` and `Ugraphs`, the latter
    through the `sessions` clause of `ACN/ROOT`. No AFP heap is built.

## Installation and build

1. Install Isabelle, so that the `isabelle` executable is on the `PATH`. Otherwise set
   `ISABELLE=/path/to/isabelle` when calling the scripts.
   - On macOS, unpack `Isabelle2025-2_macos.tar.gz` into `~/Applications`; the executable is
     `~/Applications/Isabelle2025-2.app/bin/isabelle`.
   - On Linux, unpack `Isabelle2025-2_linux.tar.gz`; the executable is
     `Isabelle2025-2/bin/isabelle`.
2. Download and unpack the AFP release that matches Isabelle2025-2: `afp-current.tar.gz` from
   <https://www.isa-afp.org/download/> while Isabelle2025-2 is the current release, otherwise the
   corresponding archive at <https://sourceforge.net/projects/afp/files/>. Its `etc/version` file
   must say `AFP_VERSION=2025-2`. Then do one of the following:
   - point the scripts at its `thys` directory: `export AFP=/path/to/afp/thys`;
   - or copy (or symlink) the nine entries listed in `afp/ROOTS` into `isabelle/afp/`, which is the
     scripts' default location:

     ```sh
     for e in $(cat afp/ROOTS); do cp -R /path/to/afp/thys/$e afp/; done
     ```
3. Check the session:

   ```sh
   ./build.sh                          # batch check; prints progress, errors and slow commands
   ```

   The first run builds `HOL-Library` (about 5 min). After that, `ACN` takes about 50 s.
4. To browse the theories in Isabelle/jEdit, with `HOL-Library` as the logic:

   ```sh
   ./jedit.sh                          # opens ACN/ACN_Sec2.thy
   ./jedit.sh ACN/ACN_Sec4_Sun.thy     # or any theory files
   ```

## Files (`ACN/`)

| Theory | Contents |
|---|---|
| `ACN_Basics` | §1: `sumN f v` = f(N(v)), `labeling`, `additive_coloring`, `eta` (η); existence of additive colorings (powers of 2); orientations, `top_add_numbering`, `eta_t` (η_t); **`eta_min_eta_t`**: η(G) = min η_t(D) over acyclic orientations; cliques; the chromatic number `chi` and `clique_le_chi`; `cdiv` (ceiling division) |
| `ACN_Chromatic` | `chi` agrees with `chromatic_number` of *Girth Chromatic* on graphs with natural vertices (`chi_eq_chromatic_number`) |
| `ACN_Sec2` | §2: `observation_1`, `lemma_1`, `corollary_1`; the sequence `sseq` (s_i) and `mp_bound` (max ⌈s_i/\|V_i\|⌉); `complete_multipartite`, `monotone`; locale `MMS15_lemma2` (Lemma 2, assumed); **`theorem_1`** and `theorem_1_conjecture` |
| `ACN_Sec3` | §3: `observation_2` (true twins); the join `join_edges` and locale `join_complete`; **`theorem_2`**; χ(G ∨ K_q) ≥ χ(G) + q (`J_chi_ge`) and `theorem_2_conjecture` |
| `ACN_Sec3_Families` | paths (η(P_N) = 2 for N ≥ 4), `fan`; disjoint copies of K_p, `windmill`; circuits (η = 2 when even), **`proposition_1`** (odd circuits), `wheel` |
| `ACN_Sec4` | §4: locale `split_graph`, **`theorem_3`**, `theorem_3_conjecture`, `split_graph_conjecture` (any split graph); locale `complete_split`, **`proposition_2`**; locale `MMS15_lemma3` (Lemma 3, assumed), **`corollary_2`** |
| `ACN_Sec4_Spiders` | thin and thick headless spiders: **`proposition_3_thin`**, **`proposition_3_thick`** |
| `ACN_Suns` | the sun construction: locale `sun_graph`, its neighborhoods and sums |
| `ACN_Sec4_Sun` | the labeling of the appendix for complete suns (`ks_q` = the permutation 𝔮, `ks_fu`, `ks_fv`), the recurrence `ks_claim`, **`proposition_4`** |
| `ACN_Sec5` | §5: cycle suns and wheel suns, **`proposition_5_cycle`**, **`proposition_5_wheel`** |

**Representation:**
- A graph is an instance of the locale `fin_sgraph V E` of *Undirected Graph Theory*: edges are
  2-element sets, and `vert_adj`, `neighborhood` and `degree` come from that library.
- Families of graphs use concrete vertex types: `nat` (paths, circuits, `{0..<n}`), `nat × nat`
  (copies of K_p), and `nat + nat` (spiders and suns: u_i = `Inl i`, v_i = `Inr i`, the hub of a
  wheel sun is `Inl 0`).
- A labeling of a sun or spider is `case_sum fu fv`, with fu i = f(u_i) and fv i = f(v_i).

## Status

Everything is proved: there is no `sorry`, and the session builds without `quick_and_dirty`.

**What is assumed.** The two results of Marenco, Mydlarz and Severín (ref. [6]) that the paper
cites are assumed, not proved, as locale assumptions about a given graph (as in the UPRF
formalization for J. Robinson's theorem). No axiom is added.
- `MMS15_lemma2` (Lemma 2 = [6], Prop. 3): for a complete multipartite graph, an acyclic
  orientation has η_t < ∞ iff it is monotone for some ordering of the parts, and in that case
  η_t = max ⌈s_i/|V_i|⌉. It is used by Theorem 1.
- `MMS15_lemma3` (Lemma 3 = [6], Prop. 1): the clique bound
  η_t(D) ≥ ⌈(d(q_F) + 1)/(d(q_L) − |Q| + 2)⌉. It is used by Corollary 2, hence by the lower bounds of
  Propositions 3 (thin spiders) and 4.
  - In the formalization, q_F and q_L are the source and the sink of Q in the orientation. These
    are the smallest and largest vertices of Q in any topological order.

Every other result is proved, including facts that the paper takes from the literature or uses
without proof:
- η(K_n) = n, through windmills;
- η(P_N) = 2, with an explicit labeling, instead of the tree bound of ref. [5];
- η(G) = min η_t(D);
- χ(G ∨ K_q) ≥ χ(G) + q;
- the existence of an additive coloring of every graph.

The thick spiders and Propositions 1, 2 and 5 do not depend on any assumption.

**Deviations from the paper:**
- **Theorem 1.** The lower bound uses a different argument. In the paper's proof, the step
  "Due to the ordering … i ≥ j" is false: for part sizes (3, 1) ordered as (1, 3), i = 1 and j = 2.
  The weaker inequality s'_j ≥ s_i that it is used for also fails, e.g. for (5,5,5,5,4,4) against
  (4,4,5,5,5,5). The theorem is true; the formal proof is in `mp_bound_sorted_le`:
  - With s_i = max_{t ≥ i} (n_t + t − i), the bound is ≤ k iff n_t + (t − i) ≤ k·n_i for all
    i ≤ t (`sseq_le_iff`, `mp_bound_le_iff`).
  - For i ≤ t in the sorted order, the parts with sizes between n_t and n_i occupy at least
    t − i + 1 positions of any other order. If a and b are the first and last of them, the
    condition at (a, b) in that order gives the condition at (i, t) in the sorted one.
- **Theorem 1, η(G) ≤ r.** Proved from the closed form instead of the paper's induction.
  `sseq_le_mult` is the paper's s_i ≤ |V_i|(r − i + 1).
- **Theorem 3.** The case "j ∈ [q−t], j < k" is done with |f(u_j) − f(u_k)| < q − t + 1 in the
  integers, so the edges inside the clique need no ordering. When f(u_j) = f(u_k), both vertices
  are in T and their degrees decide.
- **Proposition 2.** Theorem 3 is applied to the maximal clique Q' ∪ {v}.
- **Proposition 4.** The recurrence f(v_i) = 2r − 𝔮(i) + f(u_i) − f(v_{i−1}) is proved by the
  appendix's six cases, each reduced to identities in one variable (`ident_mid`, `ident_last`,
  `S1`–`S4`).
  - In the case m ≡ 2 (mod 6), i = ⌊m/2⌋ + 1, the paper writes r = m/3 + 1 and f(v_{i−1}) = 1.
    In fact r = (m + 4)/3 and f(v_{i−1}) = 2, so f(v_i) = 2 = 3r − m − f(v_{i−1}).
- **Proposition 1 (lower bound).** The "oriented path of 3 consecutive vertices" is obtained by
  parity: if the orientation alternated along the circuit, n would be even.
- **Families.** All families are concrete graphs, so each proposition is a statement about a
  specific graph; the paper states them up to isomorphism. Thin spiders of order 2 get the
  paper's labeling directly. Thick spiders of order 2 get an explicit labeling, since the paper's
  isomorphism argument is not formalized.

**Out of scope:** §6 and Appendix B (the integer programming tool, the experiments, and the
closed additive colorings).

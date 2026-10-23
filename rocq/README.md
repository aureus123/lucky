# Rocq + MathComp/ssreflect formalization

Formalization of Sections 1–5 of D. Severín, *On the additive chromatic number of several families
of graphs* (Inf. Process. Lett. 158, 2020), including the proofs of Propositions 1–5 from the
appendix of the arXiv version. See the main [README](../README.md) for the statements.

## Requirements

- **Rocq 9.3** (the Rocq Prover): <https://rocq-prover.org>.
- **MathComp 2.6** (`rocq-mathcomp-ssreflect`).
- **mczify** (`coq-mathcomp-zify`), so that `lia` works on ssreflect's natural numbers.
- **coq-graph-theory** (C. Doczkal, D. Pous, <https://github.com/coq-community/graph-theory>),
  which needs **MathComp finmap 2.2** (`rocq-mathcomp-finmap`). Its last release (0.9.7)
  requires Coq < 9.2 and MathComp < 2.6, so for Rocq 9.3 it is pinned to its development
  version; the formalization was checked with commit `322e352` (6 May 2026). Only `sgraph`,
  `coloring` and the files they load are used.

## Installation and build

With opam (<https://opam.ocaml.org>):

```sh
opam switch create lucky ocaml-base-compiler.5.3.0     # optional: a dedicated switch
eval $(opam env --switch=lucky)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-prover rocq-mathcomp-ssreflect coq-mathcomp-zify rocq-mathcomp-finmap
opam pin add coq-graph-theory "git+https://github.com/coq-community/graph-theory.git#322e352"
```

(The pin also installs small compatibility packages: `coq`, `coq-core` and `coq-mathcomp-*`.)

Then build (about 2 min):

```sh
./build.sh
```

## Files (`theories/`)

| File | Lines | Contents |
|---|---|---|
| `Tactics.v` | 93 | the Ltac2 tactics `split_lia` and `nlia` (see below) |
| `Basics.v` | 420 | §1: `cdiv` (ceiling division, `cdiv_spec`); `deg`, `maxdeg` (Δ), `sumN` (f(N(v))) on the library's graphs; `labeling`, `additive_coloring`, `eta` (η); existence of additive colorings (powers of 2); `chi` (the library's χ) and its characterization by proper colorings (`chi_le`, `chi_attained`), `clique_le_chi`; orientations, `topnum`, `etaT_is` and `etaT_finite` (η_t); **`eta_eq_min_etaT`**: η(G) = min η_t(D) over acyclic orientations; `true_twins` |
| `Sec2.v` | 535 | §2: `observation_1`, `lemma_1`, `corollary_1`; the sequence `sseq` (s_i) and `mpbound` (max ⌈s_i/\|V_i\|⌉); `complete_multipartite`, `monotone`, orderings of the parts; **`lemma_2_value`**, **`lemma_2_finite_iff`** (Lemma 2); **`theorem_1`** and `theorem_1_conjecture` |
| `Sec3.v` | 196 | §3: `observation_2` (true twins); the join `gjoin` and `joinK` (G ∨ K_q, with the library's `'K_q`); **`theorem_2`**; χ(G ∨ K_q) ≥ χ(G) + q (`chi_joinK`) and `theorem_2_conjecture` |
| `Sec3Families.v` | 361 | paths (`path_eta`: η(P_N) = 2 for N ≥ 4), **`fan`**; m K_p (`copiesK`, `copies_eta`), **`windmill`**; cycles (`cycle_eta_even`), **`proposition_1`** (odd cycles), **`wheel`** |
| `Sec4.v` | 360 | §4: `split_graph`, **`theorem_3`**, `theorem_3_conjecture`, `split_graph_conjecture` (any split graph); **`proposition_2`** (complete splits); **`lemma_3`**, **`corollary_2`** |
| `Sec4Spiders.v` | 252 | `extend` (a graph plus a stable set attached by a relation); thin and thick headless spiders: **`proposition_3_thin`**, **`proposition_3_thick`** |
| `Sec4Sun.v` | 200 | suns (`sun`, their neighborhoods and sums); the labeling of the appendix for complete suns (`ksQ` = the permutation 𝔮, `ksFu`, `ksFv`), the recurrence `ks_claim`, **`proposition_4`** |
| `Sec5.v` | 251 | §5: cycle suns and wheel suns, **`proposition_5_cycle`**, **`proposition_5_wheel`** |

Most of the build time is `Sec5.v` (about 55 s) and `Sec3Families.v` (about 20 s), where
`split_lia` checks the closed forms of the sums by cases.

**Representation:**
- Graphs are the simple graphs of coq-graph-theory: a record `sgraph` with a finite type of
  vertices and a symmetric irreflexive edge relation `x -- y`. From the library come N(v)
  (`N(G; v)`), cliques (`clique`), the complete graph `'K_q` and the chromatic number χ
  (`χ(A)`, the least number of stable sets partitioning A; `chi G` is `χ([set: G])`). The
  degree d(v), Δ, the sums f(N(v)), the join G ∨ H (`gjoin`; the library's `G ∔ H` is the
  disjoint union) and all the families of graphs are defined here.
- `chi_le` and `chi_attained` show that χ(G) is also the least k such that G has a proper
  k-coloring `G -> 'I_k`; the proofs use this form.
- η(G) is the least witness (`ex_minn`) of a decidable predicate: the existence of an additive
  k-coloring is a finite search over finite functions `{ffun G -> 'I_k.+1}` (`has_acolP`).
- Orientations are boolean relations `A : rel V`; acyclic means that no arc `A u v` can be
  closed by a path from `v` back to `u` (`connect` of MathComp's `fingraph`). η_t(D), which
  may be ∞, is given by two predicates: `etaT_is G A k` (η_t(D) = k) and `etaT_finite G A`
  (η_t(D) < ∞). So η(G) = min η_t(D) reads: η(G) ≤ η_t(D) for every acyclic orientation D,
  and η_t(D) = η(G) for some acyclic orientation D.
- The parts of a complete multipartite graph are `Ps 0, …, Ps (r - 1)`, indexed by `nat`, and an
  ordering of the parts is a permutation `sg` of `iota 0 r` (`ordering`).
- Paths and cycles are graphs on `'I_N`; the vertex k is the paper's v_{k+1}. The complete graph
  K_q is the library's `'K_q`, also on `'I_q`.
- Spiders and suns live on sum types: u_i = `inl i`, v_i = `inr i`, with `i : 'I_m` the
  paper's index minus one. The wheel sun is the sun of `joinK (cycleG m) 1`, whose hub is
  `inl (inr ord0)`.
- The labelings of the families are functions of the paper's indices (`splab fu fv`,
  `wslab fu fv c`), so the arithmetic is done in `nat`.

## Proof automation (`Tactics.v`, Ltac2)

Rocq's `lia`, with mczify, is stronger than Lean's `omega` on this development. It decides
linear arithmetic over ssreflect's `nat` including divisions and remainders by constants
(`%/`, `%%`) and the boolean tests `==`, `<=`, `<`, `&&`, `||`, `~~` and `odd`. For example,
⌊(2k + 5)/3⌋ + ⌊(2k + 7)/3⌋ + ⌊(2k + 3)/3⌋ = 2k + 4 is one call, while Lean's `omega` needs a
split on k mod 3. So the Lean tactic `mod_split` has no counterpart here.

What `lia` does not handle is `if-then-else`, and the labelings of the families are defined by
cases on the index. Two Ltac2 tactics, callable from ssreflect scripts, fill the gaps.

- **`split_lia`** decides goals of linear arithmetic that contain `if`s, in the goal or in the
  hypotheses. It repeatedly picks an `if`, takes the first atomic test of its condition (a
  condition `b1 || b2` is split on `b1` first), and then:
  1. reduces it if `lia` decides it from the hypotheses, or splits on it otherwise;
  2. rewrites it in the goal and in every hypothesis, and simplifies the boolean connectives;
  3. if it is an equation `x == y` that holds, substitutes it, so that `F x` and `F y` become the
     same term (`lia` cannot see that they are equal).

  Every branch is closed by `lia`. It is used about 60 times: labeling ranges, the sums of the
  explicit labelings, the closed forms of the sums in cycles and suns, and the indexed sums
  over `'I_N`. The appendix's claim for complete suns,
  f(v_i) + f(v_{i-1}) + 𝔮(i) = 2r + f(u_i), is one call (`ks_claim`, about 3 s), without the
  residue splits of the Lean proof or the six cases of the Isabelle and Mizar proofs.
- **`nlia`** is `lia` after normalizing the goal and the hypotheses. MathComp's finite types are
  canonical structures. Two occurrences of the same sum or vertex can be elaborated at
  different but convertible instances, for example with a `reverse_coercion` wrapper or an
  unreduced `Finite.sort` projection. `lia` then treats them as different atoms. `nlia`
  unfolds the wrappers and simplifies before calling `lia`. It is used about 50 times, mostly
  on sum types (spiders and suns).

## Status

Everything is proved, with no `Admitted`. The main theorems are **closed under the global
context** (checked with `Print Assumptions`): they use no axioms at all, not even functional
extensionality. η is defined constructively, as the least witness of a decidable predicate,
and the parts of coq-graph-theory that are used are axiom-free as well.

**Nothing is assumed.** As in the Isabelle, Mizar and Lean formalizations, the two results of
Marenco, Mydlarz and Severín (ref. [6]) that the paper cites are proved, following [6]:
- **Lemma 2** = [6], Prop. 3 (`lemma_2_value`, `lemma_2_finite_iff`);
- **Lemma 3** = [6], Prop. 1 (`lemma_3`, and `lemma_3_topnum` for any topological additive
  numbering).

So every result is unconditional, including facts that the paper takes from the literature or
uses without proof: η(G) = min η_t(D), η(P_N) = 2, η(K_n) = n (through windmills),
χ(G ∨ K_q) ≥ χ(G) + q, and the existence of an additive coloring of every graph.

**Deviations from the paper** (the same as in the other formalizations; see the main README):
- **Theorem 1.** The lower bound uses a different argument (`mpbound_sorted_le`), because the
  paper's step "i ≥ j" is false.
- **Theorem 1, η(G) ≤ r.** It is proved from the closed form of s_i (`mpbound_le_card`).
- **Theorem 3.** The hypothesis T ≠ ∅ is not needed, so it is dropped.
- **Proposition 2.** Theorem 3 is applied to the maximal clique Q' ∪ {v}.
- **Corollary 2.** It is stated for any bounds d₁ ≤ d(v) ≤ d₂ on the degrees of the clique.
  The paper's d₁ and d₂ (the smallest and the largest degree) are a special case, and since
  ⌈(d₁ + 1)/(d₂ − |Q| + 2)⌉ is monotone in d₁ and antitone in d₂, the two forms are equivalent.
- **Proposition 4.** In the case m ≡ 2 (mod 6), i = ⌊m/2⌋ + 1, the paper writes r = m/3 + 1 and
  f(v_{i−1}) = 1. In fact r = (m + 4)/3 and f(v_{i−1}) = 2. `ks_claim` checks the claimed
  recurrence in all cases.
- **Proposition 1 (lower bound).** The "oriented path of 3 consecutive vertices" is obtained by
  parity: if the orientation alternated along the cycle, n would be even.
- **Families.** All families are concrete graphs, so each proposition is a statement about a
  specific graph; the paper states them up to isomorphism.

**Out of scope:** §6 and Appendix B (the integer programming tool, the experiments, and the
closed additive colorings).

## Notes

- **Pitfalls:**
  - A conditional `rewrite` puts its side conditions *before* the rewritten goal, so
    `rewrite lemma; last by tac` applies `tac` to the main goal. Proving the side condition
    first with `have` is more robust.
  - `rewrite ?mulnC` (and any `?` with a commutativity lemma) loops forever.
  - `split_lia` uses every hypothesis in the context. A lemma proved with it inside a `Section`
    therefore depends on all the section's hypotheses, even those it does not need. The
    successor and predecessor on `'I_n` (`osucc`, `opred`) live in a section of their own for
    this reason.
  - coq-graph-theory declares `edge_rel` (that is, `x -- y`) as `simpl never`, so that the
    notation survives simplification. `Basics.v` sets it back to `simpl nomatch` (and lets
    `digraph_of` unfold), so that `/=` computes the adjacency of the concrete graphs (joins,
    spiders, suns). This setting is exported to the files that import `Basics`.
  - When the vertex type of a concrete graph is a sum or an ordinal type, the graph cannot be
    inferred from the vertices: write `x -- y :> G` (in `implicit_scope`) and name the graph
    in lemmas, e.g. `eta_le_lab (G := cycle_sun m)`.

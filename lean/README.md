# Lean 4 + Mathlib formalization

Formalization of Sections 1–5 of D. Severín, *On the additive chromatic number of several families
of graphs* (Inf. Process. Lett. 158, 2020), including the proofs of Propositions 1–5 from the
appendix of the arXiv version. See the main [README](../README.md) for the statements.

## Requirements

- **elan**, the Lean toolchain manager: <https://github.com/leanprover/elan>. It installs the
  Lean version pinned in `lean-toolchain` (Lean 4.35.0).
- **Mathlib v4.35.0**. It is fetched automatically by `lake`, as pinned in `lakefile.toml` and
  `lake-manifest.json`.
- About 6 GB of disk space for the prebuilt Mathlib cache.

## Installation and build

```sh
lake exe cache get     # download the prebuilt Mathlib (once)
./build.sh             # build the library; prints only errors and warnings
```

The library builds in about 3 min from clean, after loading Mathlib. Most of it is the
arithmetic of Proposition 4 (`ks_claim`, about 70 s).

## Files (`ACN/`)

| File | Lines | Contents |
|---|---|---|
| `Tactics.lean` | 53 | the tactics `split_omega` and `mod_split` (see below) |
| `Basics.lean` | 237 | §1: `cdiv` (ceiling division, `cdiv_eq_ceil`); `sumN f v` = f(N(v)), `Labeling`, `AdditiveColoring`, `eta` (η); existence of additive colorings (powers of 2); orientations, `TopAddNumbering`, `etaT` (η_t); **`eta_eq_iInf_etaT`**: η(G) = min η_t(D) over acyclic orientations; `TrueTwins` |
| `Sec2.lean` | 547 | §2: `observation_1`, `lemma_1`, `corollary_1`; the sequence `sseq` (s_i) and `mpBound` (max ⌈s_i/\|V_i\|⌉); `IsCompleteMultipartiteWith`, `IsMonotone`; **`lemma_2_value`**, **`lemma_2_finite_iff`** (Lemma 2); **`theorem_1`** and `theorem_1_conjecture` |
| `Sec3.lean` | 201 | §3: `observation_2` (true twins); the join `join` and `joinK` (G ∨ K_q); **`theorem_2`**; χ(G ∨ K_q) ≥ χ(G) + q (`chromaticNumber_joinK`) and `theorem_2_conjecture` |
| `Sec3Families.lean` | 395 | paths (`pathGraph_eta`: η(P_N) = 2 for N ≥ 4), **`fan`**; m K_p (`copiesK`, `copiesK_eta`), **`windmill`**; cycles (`cycleGraph_eta_even`), **`proposition_1`** (odd cycles), **`wheel`** |
| `Sec4.lean` | 418 | §4: `IsSplitWith`, **`theorem_3`**, `theorem_3_conjecture`, `split_graph_conjecture` (any split graph); **`proposition_2`** (complete splits); **`lemma_3`**, **`corollary_2`** |
| `Sec4Spiders.lean` | 320 | `extend` (a graph plus a stable set attached by a relation); thin and thick headless spiders: **`proposition_3_thin`**, **`proposition_3_thick`** |
| `Sec4Sun.lean` | 246 | suns (`sun`, their neighborhoods and sums); the labeling of the appendix for complete suns (`ksQ` = the permutation 𝔮, `ksFu`, `ksFv`), the recurrence `ks_claim`, **`proposition_4`** |
| `Sec5.lean` | 295 | §5: cycle suns and wheel suns, **`proposition_5_cycle`**, **`proposition_5_wheel`** |

**Representation:**
- A graph is a Mathlib `SimpleGraph V` on a finite type `V` with decidable adjacency; every
  element of `V` is a vertex. N(v) is `G.neighborFinset v`, d(v) is `G.degree v`, Δ is
  `G.maxDegree` and χ(G) is Mathlib's `G.chromaticNumber`.
- Orientations are relations `A : V → V → Prop`; acyclic means that the transitive closure is
  irreflexive.
- Paths and cycles are Mathlib's `pathGraph n` and `cycleGraph n` on `Fin n`; the vertex k is the
  paper's v_{k+1}. The complete graph K_q is `⊤`.
- Spiders and suns live on sum types: u_i = `inl i`, v_i = `inr i`, with `i : Fin m` the paper's
  index minus one. The wheel sun is the sun of `(cycleGraph m).joinK (Fin 1)`, whose hub is
  `inl (inr 0)`.
- The labelings of the families are functions of the paper's indices (`spLab fu fv`, `wsLab`),
  so the arithmetic is done in ℕ.

## Proof automation (`Tactics.lean`)

Most of the work in the families of graphs is arithmetic over ℕ with labelings defined by
cases on the index, with divisions and remainders by constants. Two tactics handle it.

- **`split_omega`** decides goals of linear arithmetic that contain `if-then-else`:
  1. it reduces every `if` whose condition `omega` decides from the hypotheses
     (`simp (disch := omega) only [ite_of_pos, ite_of_neg]`);
  2. it splits the remaining `if`s with `split_ifs`;
  3. it closes each branch by contradiction or `omega` (a goal `P ↔ Q` is split into its two
     implications).

  It is used about 70 times: labeling ranges, sums of the explicit labelings, and the closed
  forms of the sums in cycles and suns.
- **`mod_split e, n`** (n = 2, 3, 6) splits on the residue of `e` modulo `n`, as hypotheses
  `e % n = c`. `omega` is not complete for several divisions by the same constant: for example
  ⌊(2k + 5)/3⌋ + ⌊(2k + 7)/3⌋ + ⌊(2k + 3)/3⌋ = 2k + 4 needs a split on k mod 3. With it, the
  appendix's claim for complete suns,
  f(v_i) + f(v_{i-1}) + 𝔮(i) = 2r + f(u_i), is one line:
  `mod_split m, 6 <;> mod_split (m - i), 3 <;> split_omega`. The Isabelle and Mizar proofs
  need the six cases of the appendix and a dozen arithmetic identities.

Two general lemmas play the role of the Isabelle method `neighborhood_eq`:
- `sumN_fin` computes f(N(i)) in a graph on `Fin N` from a description of the adjacency on
  the indices;
- `extend_sumN_inl` and `extend_sumN_inr` compute it in a graph with a stable set attached.

## Status

Everything is proved, with no `sorry`. The main theorems depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

**Nothing is assumed.** As in the Isabelle and Mizar formalizations, the two results of
Marenco, Mydlarz and Severín (ref. [6]) that the paper cites are proved, following [6]:
- **Lemma 2** = [6], Prop. 3 (`lemma_2_value`, `lemma_2_finite_iff`);
- **Lemma 3** = [6], Prop. 1 (`lemma_3`).

So every result is unconditional, including facts that the paper takes from the literature or
uses without proof: η(G) = min η_t(D), η(P_N) = 2, η(K_n) = n (through windmills),
χ(G ∨ K_q) ≥ χ(G) + q, and the existence of an additive coloring of every graph.

**Deviations from the paper** (the same as in Isabelle; see the main README):
- **Theorem 1.** The lower bound uses a different argument (`mpBound_sorted_le`), because the
  paper's step "i ≥ j" is false.
- **Theorem 1, η(G) ≤ r.** It is proved from the closed form of s_i (`mpBound_le_card`).
- **Theorem 3.** The hypothesis T ≠ ∅ is not needed, so it is dropped.
- **Proposition 2.** Theorem 3 is applied to the maximal clique Q' ∪ {v}.
- **Proposition 4.** In the case m ≡ 2 (mod 6), i = ⌊m/2⌋ + 1, the paper writes r = m/3 + 1 and
  f(v_{i−1}) = 1. In fact r = (m + 4)/3 and f(v_{i−1}) = 2. `ks_claim` checks the claimed
  recurrence in all cases.
- **Proposition 1 (lower bound).** The "oriented path of 3 consecutive vertices" is obtained by
  parity: if the orientation alternated along the cycle, n would be even.
- **Families.** All families are concrete graphs, so each proposition is a statement about a
  specific graph; the paper states them up to isomorphism. Fans and wheels use Mathlib's
  `pathGraph` and `cycleGraph`; m K_p is `copiesK m p` on `Fin m × Fin p`.

**Out of scope:** §6 and Appendix B (the integer programming tool, the experiments, and the
closed additive colorings).

## Metadata

`formalization.yaml` describes this formalization in the
[formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) standard (v0.4),
as used by the [Palomar Registry](https://palomar-registry.org): sources, scope, automation,
review status, and the correspondence between the paper's results and the Lean declarations.

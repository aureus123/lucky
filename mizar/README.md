# Mizar formalization

Formalization of Sections 1–5 of D. Severín, *On the additive chromatic number of several families
of graphs* (Inf. Process. Lett. 158, 2020), including the proofs of Propositions 1–5 from the
appendix of the arXiv version. See the main [README](../README.md) for the statements.

## Requirements

- **The Mizar system 8.1.15 with MML 5.94.1493**: <https://mizar.uwb.edu.pl/system/>.
  Prebuilt packages exist for Linux, macOS and Windows.
- A POSIX shell and Python 3. They are used by `miz.sh` to print the errors with their
  explanations.

## Installation and verification

1. Download the package for your platform and run its `install.sh`. It asks for a directory
   for the binaries and one for the shared files (MML, vocabularies, `mizar.msg`).
   - The folder `system/` (with `bin/` and `share/`) is the conventional place for a local copy;
     it is ignored by git.
2. Put the binaries on the `PATH` and set `MIZFILES` to the shared directory, for example:

   ```sh
   export MIZFILES=$PWD/system/share
   export PATH=$PWD/system/bin:$PATH
   ```

3. Verify the article (about 55 s):

   ```sh
   ./miz.sh acn
   ```

   `miz.sh` runs the accommodator and the verifier on `text/acn.miz`, and prints `OK` or the
   list of errors with their messages. The vocabulary `dict/acn.voc` is found automatically,
   because `miz.sh` works from this directory.

`./mmlthm.sh ARTICLE REGEX` is a small helper used during development. It searches an MML
abstract and shows the theorem labels.

## Layout

| Path | Content |
|---|---|
| `text/acn.miz` | the article. It is a single file because Mizar can cite the theorems of another article only by number. |
| `dict/acn.voc` | vocabulary (the new symbols) |
| `miz.sh`, `mmlthm.sh` | scripts described above |
| `acn.pdf` | the statements of the article, typeset in the style of a [Formalized Mathematics](https://mizar.uwb.edu.pl/fm/) paper |
| `fm/` | the generator of `acn.pdf`: `build.sh` runs `miz2tex.py` (theorems and definitions of `acn.miz` translated to English and LaTeX) and `bib.py` (the bibliography, from the `fm.bib` of the Mizar distribution), then pdfLaTeX |

## Representation

- **Graphs.** A graph is a `Graph`: a non-empty, finite, irreflexive and symmetric `RelStr`
  (the attributes of NECKLACE). `u,v are_adjacent` means `[u,v] in the InternalRel of G`.
  - `Nb v` is N(v), `deg v` is d(v) = |N(v)|, and `maxdeg G` is Δ.
  - The paper's graphs have at least one vertex, so the graph without vertices is excluded.
- **Labelings.** A labeling is a `Function of the carrier of G, NAT`.
  - f(S) = Σ_{u∈S} f(u) is `Sum(f|S)` (the sum of a bag, NAT_5); f(N(v)) is `SumN(f,v)`.
  - `f is k-labeling` means 1 ≤ f(v) ≤ k for every vertex; `f is additive` means
    f(N(u)) ≠ f(N(v)) on every edge.
- **η and χ.** `eta G` is the least k with a `k-labeling additive` function. χ(G) is
  `chromatic# G` of MYCIELSK (the least number of classes of a partition into stable sets), and
  cliques are the `Clique`s of DILWORTH.
- **Orientations.** An orientation is a `Relation` A with `A is_orientation_of G`. `A is acyclic`
  means that every closed `RedSequence` (REWRITE1) of A is trivial. `eta_t(G,A)` is an `ExtReal`,
  the infimum of the k with a topological additive k-numbering, so it is `+infty` when there is
  none.
- **Families.** Each family is a predicate on graphs, with an existence theorem:
  - `G is_path_of N`, `G is_cycle_of N` (vertices 1..N);
  - `G is_copies_of m,p` (m K_p, vertices [i,j]);
  - `H is_join_of G,U` (G ∨ K_U);
  - `G is_thin_spider_of q`, `G is_thick_spider_of q` (u_i = [0,i], v_i = [1,i]);
  - `G is_sun_of m,B,R` (the sun of a base graph on u_i = [0,i], i ∈ B, with edges given by R;
    v_j = [1,j]). The bases are `KRel m` (K_m), `CycRel m` (C_m) and `WRel m` (W_m, hub u_0).
  - Complete multipartite graphs and split graphs are described by hypotheses on G
    (`P is_cm_of G` for the parts P = ⟨V_1, …, V_r⟩, `G is_split_by Q,S`).
- **Numbers.** `cdiv(a,b)` is ⌈a/b⌉ (`CdivCeil`: `cdiv(a,b) = [/ a / b \]`). `csucc(N,i)` and
  `cpred(N,i)` are the successor and the predecessor modulo N on 1..N.

## Contents of `acn.miz` (10926 lines, 200 theorems, 35 definitions, 4 schemes)

| Paper | Mizar |
|---|---|
| §1: N(v), d(v), f(N(v)), additive colorings, η | `Nb`, `deg`, `SumN`, `k-labeling`, `additive`, `eta`; `ExAdditive` (powers of two), `EtaLe`, `EtaAtt`, `EtaPos` |
| §1: orientations, η_t, η(G) = min η_t(D) | `is_orientation_of`, `acyclic`, `is_topological_for`, `eta_t`; `InducedOrientation`, **`EtaMinEtaT`** |
| cliques and χ(G) ≥ ω(G) | `CliqueAdj`, `CliqueI`, `CliqueLeChi` |
| Observation 1, Lemma 1, Corollary 1 | `Observation1`, `Lemma1`, `Corollary1` |
| s_i and max ⌈s_i/\|V_i\|⌉; the recurrence s_i = max{1 + s_{i+1}, n_i} | `sseq`, `cmBound`; `SseqLast`, `SseqRec`, `BoundLe`, `SseqDec` |
| complete multipartite graphs, monotone orientations | `is_cm_of`, `Sizes`, `PSum`, `is_monotone_for`; `CmNb`, `CmSumP`, `ForwardOrientation` |
| Lemma 2 (ref. [6], Prop. 3) | **`Lemma2Value`**, **`Lemma2Finite`** (with `Lemma2Lower`, `Lemma2Upper`) |
| Theorem 1, and the conjecture for complete multipartite graphs | **`Theorem1`**, `CmChi`, `Theorem1Conjecture` |
| Observation 2 | `are_true_twins`, `Observation2` |
| the join G ∨ K_q, Theorem 2, χ(G ∨ K_q) ≥ χ(G) + q | `is_join_of`, `JoinExists`, **`Theorem2`**, `JoinChi`, `Theorem2Conjecture`, `JoinK1` |
| paths, fans | `is_path_of`, `PathEta`, `Fan` |
| m K_p, windmills | `is_copies_of`, `CopiesEta`, `Windmill` |
| cycles, Proposition 1, wheels | `is_cycle_of`, `CycleEven`, `OddCycleLower`, **`Proposition1`**, `Wheel` |
| split graphs, Theorem 3, the conjecture for split graphs | `is_split_by`, **`Theorem3`**, `Theorem3Conjecture`, `SplitConjecture` |
| Proposition 2 (complete splits) | **`Proposition2`** |
| Lemma 3 (ref. [6], Prop. 1), Corollary 2 | **`Lemma3`**, **`Corollary2`** |
| Proposition 3 (thin and thick headless spiders) | `is_thin_spider_of`, `is_thick_spider_of`, **`Proposition3Thin`**, **`Proposition3Thick`** |
| suns | `is_sun_of`, `SunExists`, `SunsExist`, `SunNbU`, `SunNbV`, `SunSums` |
| Proposition 4 (complete suns), the labeling of the appendix | `ksq` (the permutation 𝔮), `ksu`, `ksv`, `ksa`; `KsClaim`, `KsRanges`, `KsqInj`, **`Proposition4`** |
| Proposition 5 (cycle and wheel suns) | **`Proposition5Cycle`**, **`Proposition5Wheel`** |

## Remarks on the proofs

The proofs follow the [Isabelle formalization](../isabelle/README.md), with these differences:

- **Theorem 1, lower bound.** It is proved directly from an additive coloring, without
  permutations of the parts: the part sums f(V_j) are distinct, and for i ≤ t in the sorted
  order the parts with sizes between n_t and n_i have at least t − i + 1 distinct sums.
- **Lemma 2, "η_t(D) < ∞ iff D is monotone".** The monotone order of the parts is built by
  ranking the parts by their sums (`Lemma2Finite`); the reordered parts are again a partition
  `is_cm_of G`.
- **Proposition 4.** The claim f(v_i) + f(v_{i−1}) + 𝔮(i) = 2r + f(u_i) is stated additively
  (`KsClaim`) with f(v_i) = r + 1 − a(i). Its six cases reduce to
  ⌊x/3⌋ + ⌊(x+2)/3⌋ + ⌊(x+4)/3⌋ = x + 1 (`Hermite3`) and to four identities that depend on
  m mod 6 (`KsS`). The case m ≡ 2 (mod 6), i = ⌊m/2⌋ + 1 uses f(v_{i−1}) = 2, as noted in the
  main README.
- **u–v edges of the complete sun.** f(N(u_i)) = f(U) + 2r − 𝔮(i) ≥ 2r + 1 because f(u_m) = 2,
  while f(N(v_j)) ≤ 2r.

## Mizar pitfalls met

- `div` binds more loosely than `+`: write `(x div 3) + (y div 3)`, never `x div 3 + y div 3`.
- Mizar has no `moreover`/`ultimately`: use labels.
- `Sum(f|J)` has mode `Real` (an object). To use it as a `Nat` (for example, as the k of
  `k-labeling`), reconsider it `as Element of NAT by ORDINAL1:def 12`.
- For functions, `g*f` is g ∘ f by a FUNCT_1 synonym, but RELSET_1 redefines `*` for relations
  between sets with the relational order. To reorder a FinSequence, build it with
  `FINSEQ_2:sch 1` instead of composing.
- Citing a hypothesis that is a large defined predicate (such as `H is_join_of G,U`) together
  with other facts can make the checker very slow; extract the needed conjunct first.
- `by T1, T2` cannot instantiate the same universal fact twice in one step; split the step.
- Numerals block instantiation: state `3 = 3 * 1 + 0` before using `Div3`.
- The vocabulary symbol of a parameterized attribute such as `k-labeling` is `V-labeling`.

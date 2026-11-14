# Upstreaming to Mathlib

This file maps the contents of lc-analysis against Mathlib, so that Mathlib maintainers and
reviewers can see what might belong in Mathlib, what it depends on, and where it overlaps with
existing Mathlib code. Nothing has been proposed to Mathlib yet; the first candidate is prepared
(see [below](#prepared-a-locallyconvexspace-instance-on-quotients)). Inclusion is decided by the
Mathlib community, piece by piece, after discussion.

Checked against Mathlib `v4.36.0-rc2` (commit `9d581dfff2e4`), on 2026-11-12. The overlap search
was by name and topic in the Mathlib sources; it may have missed results stated under other names.

## How pieces would be proposed

The rules are those of the Mathlib contribution guide,
<https://leanprover-community.github.io/contribute/index.html>.

* **Scope first.** Additions to theories Mathlib already has (class E below) can go straight to a
  PR. New theories (classes N and F) are first raised in the `#mathlib` channel of the Lean Zulip,
  to ask whether they fit in Mathlib at all.
* **Small PRs.** Each file listed here would be split into PRs of a few hundred lines, and adapted
  to Mathlib's naming: Mathlib declarations live at the root or in the namespace of the main
  object, not in `LocallyConvex.Analysis`.
* **AI disclosure.** The proofs in this repository were written by an AI assistant (see
  [How this library was written](README.md#how-this-library-was-written)). Every PR says so in
  its description, names the tool and how it was used, and carries the `LLM-generated` label. The
  author of each PR must understand all of its content and justify every design decision to
  reviewers himself.
* **Tracking.** When a piece is proposed, its row gets the Zulip thread or PR number. When it is
  merged, the file here is changed to use the Mathlib version, and the row says so.

## Prepared: a `LocallyConvexSpace` instance on quotients

The first candidate is ready but not yet proposed. It is a single instance, added to Mathlib's
`Mathlib/Topology/Algebra/Module/LocallyConvex.lean` (22 lines, on Mathlib master of
2026-11-12):

```lean
instance Submodule.Quotient.locallyConvexSpace (S : Submodule 𝕜 E) :
    LocallyConvexSpace 𝕜 (E ⧸ S)
```

for a ring `𝕜` with a partial order and a topological additive group `E` which is a locally
convex `𝕜`-module. The submodule need not be closed.

**Why it is worth adding, although the proof is three lines of existing lemmas.**

* *An instance is found automatically.* Today every user who needs `E ⧸ S` to be locally convex
  must prove it by hand at each use, also when `E ⧸ S` appears inside another construction. With
  the instance, Lean finds it.
* *It completes the basic constructions.* The same Mathlib file has the instances for
  subspaces, `Prod.locallyConvexSpace` and `Pi.locallyConvexSpace`, each a one-line consequence
  of existing lemmas. Quotients are the missing basic construction.
* *It has a use.* In this library, `Spaces/DirectLimitQuotient.lean` presents locally convex
  direct limits (LF-spaces) as quotients of direct sums, and has to supply this fact by hand
  through `locallyConvexSpace_quotient`, stated over `ℝ` only.
* *No diamonds.* `LocallyConvexSpace` is a `Prop`, so another path to the same instance (for
  example through a normed quotient) cannot conflict with this one.

**The cost: one import.** The file now imports `Mathlib.Topology.Algebra.Module.Basic`, where the
topology on `E ⧸ S` is declared. This adds 10 modules to what the file loads, and keeps
`assert_not_exists NormedSpace` true. Nine of the ten come from the quotient topology on groups,
through `GroupTheory/GroupAction/Quotient.lean` (orbit counting, periodic points, permutations of
lists). Of that file, the topology on quotient groups uses only the action of `G` on `G ⧸ N` and
its transitivity, about 76 lines; splitting them off into a light file, which would be a
separate pull request on the group theory files, brings the cost down to 3 modules. Downstream,
six of the seven Mathlib files that import `LocallyConvex` directly already load
`Module.Basic`.

**After it is merged,** `locallyConvexSpace_quotient` is removed from this library and
`Spaces/DirectLimitQuotient.lean` uses the Mathlib instance.

## Classes

| Class | Meaning |
|---|---|
| **E** | Extends a theory Mathlib already has: lemmas or generalizations of existing declarations. |
| **N** | A new theory, independent of the Michal–Bastiani calculus. Needs a scope discussion on Zulip. |
| **F** | Built on the Michal–Bastiani calculus (`Calculus/MichalBastiani.lean`). Can only be proposed after that framework is accepted; see [The central design question](#the-central-design-question). |
| **X** | A counterexample. Candidate for Mathlib's `Counterexamples/` project, which collects results that fail outside the usual hypotheses. |

Status column: `–` not proposed; otherwise a Zulip thread, a PR, or "merged".

## The central design question

Mathlib's differential calculus (`HasFDerivAt`, `ContDiff`, `AnalyticAt`) is built on normed
spaces. Mathlib's directional derivative `HasLineDerivAt` already allows a domain `E` with no
topology, but its target `F` is normed. The Michal–Bastiani calculus of this library needs
locally convex targets as well, with `C^k` defined through continuity of the differentials on
`U × E` (`ContDiffMBOn`).

Three ways to bring it in would have to be weighed with the Mathlib community:

1. **Generalize `HasLineDerivAt`** to topological vector space targets, and define `ContDiffMBOn`
   on top of it. This touches existing Mathlib code.
2. **Add a parallel theory**, as this library does now, with bridges to the normed theory.
   Already proved bridges: `smoothMBOn_iff_contDiffOn` (Michal–Bastiani and Fréchet smoothness
   agree on normed spaces) and `complexAnalyticOn_iff_differentiableOn` (complex analyticity and
   complex differentiability agree on Banach spaces).
3. **Keep it outside Mathlib**, and upstream only the parts of classes E and N.

Everything in class F waits on this choice. Classes E, N and X do not.

## Overlaps with Mathlib

These should be resolved before any PR. In each case the options are to reuse the Mathlib
declaration, to prove a bridge to it, or to explain why it does not suffice.

| Here | In Mathlib | Relation |
|---|---|---|
| `HasDirDerivAt`, `dMB` (`Calculus/MichalBastiani.lean`) | `HasLineDerivAt`, `lineDeriv` (`Analysis/Calculus/LineDeriv/Basic.lean`) | Same notion. Ours allows a locally convex target; Mathlib's needs a normed target. No bridge lemma yet. |
| `ComplexAnalyticOn`, `RealAnalyticOn` (`Analytic/`) | `AnalyticAt`, `AnalyticOnNhd` (power series on normed spaces) | Ours work on locally convex spaces. On Banach spaces they should agree with Mathlib's. Proved for the complex case through differentiability; no direct bridge for the real case. |
| `OpenPartialHomeomorph.realAnalyticOn_symm` (`Analytic/RealInverse.lean`) | `OpenPartialHomeomorph.analyticAt_symm` (`Analysis/Calculus/FDeriv/Analytic.lean`) | Same theorem on Banach spaces, for the two notions of analyticity. Superseded by Mathlib's once the real bridge exists. |
| `LCDirectLimit` (`Spaces/DirectLimit.lean`) | the LF topology of `TestFunction` (`Analysis/Distribution/TestFunction.lean`), defined there as the finest locally convex topology for the inclusions | Ours is the general construction; Mathlib's is the special case of test functions. A general version could serve both. |
| `FiniteTop` (`Topology/FiniteTopology.lean`) | `moduleTopology` (`Topology/Algebra/Module/ModuleTopology.lean`) | Related topologies on a vector space; the comparison is not formalized. |
| `SeqComplete` (`Calculus/Integral/Existence.lean`) | the namespace `SequentiallyComplete` (`Topology/UniformSpace/Cauchy.lean`), a construction, not a class | No overlap in content, but a name clash. Mathlib has no sequential completeness class. |
| `exists_boundedBelow_of_isEmbedding` (`Calculus/BoundedBelow.lean`) | `ContinuousLinearMap.antilipschitz_of_isEmbedding` (`Analysis/Normed/Operator/NormedSpace.lean`) | Same fact; ours would be replaced by Mathlib's. |
| `isOpen_isUnit` (`Counterexamples/Units.lean`) | `Units.isOpen` | Ours restates Mathlib's; only the counterexample is new. |
| `DiffForm.d₁`, `DiffForm.d₂` (`Counterexamples/WeakDarboux.lean`) | `extDeriv` (`Analysis/Calculus/DifferentialForm/Basic.lean`) | Local exterior derivatives for the counterexample; would be rewritten with `extDeriv`. |
| `exists_posPart_negPart` (`Krein/SpectralParts.lean`) | continuous functional calculus, `CFC.posPart` | Ours is built on Mathlib's; the real case goes through a complexification Mathlib does not have. |

Already used from Mathlib, with no duplication: `LocallyConvexSpace`, `QuasiCompleteSpace`,
`StrongDual`, `CompactlyGeneratedSpace`, `IsPicardLindelof`, `circleAverage` and Jensen's formula.

## Dependencies

Only the following files depend on Mathlib alone, with no Michal–Bastiani calculus anywhere in
their imports:

* `Topology/` (all five files) and `Spaces/DirectLimit.lean`;
* `Krein/` (all six files);
* `Analytic/Polynomial.lean`;
* `Counterexamples/Units.lean`, `Counterexamples/WeakDarboux.lean`,
  `Counterexamples/BognarKrein.lean`.

Some files of class N depend on the calculus only for a few results, and would be split before
proposing them:

* `Spaces/DirectSum.lean`: the topology of the direct sum is independent; the last section
  (`contDiffMBOn_map`, `smoothMBOn_map`, `realAnalyticOn_map`, `complexAnalyticOn_map`) is class F.
* `Spaces/Silva.lean`: only `ContDiffMBOn` along the steps uses the calculus.
* `Spaces/DirectCompleteness.lean`: it imports `Calculus/Integral/Existence.lean` only for the
  classes `SeqComplete` and `MackeyComplete`, which would move to a file of their own.

## Inventory

Proposed Mathlib locations are tentative.

### `Topology/`

| File | Contents | Proposed location | Class | Status |
|---|---|---|---|---|
| `DirectLimit` | Direct limit topology of an ascending sequence of subsets; strict, compactifying and compactly regular sequences; `k_ω`-spaces | `Topology/DirectLimit.lean` | N | – |
| `DirectLimitAlgebra` | Direct limits of topological groups and vector spaces | `Topology/Algebra/Group/DirectLimit.lean` | N | – |
| `FiniteTopology` | The finite topology on a vector space | `Topology/Algebra/Module/FiniteTopology.lean` | N (see `moduleTopology`) | – |
| `KOmega` | `k_ω`-spaces: invariance, σ-compact locally compact spaces, characterization by direct limits | `Topology/Compactness/KOmega.lean` | N | – |
| `KOmegaLimits` | Direct limits and finite products of (locally) `k_ω`-spaces | `Topology/Compactness/KOmega.lean` | N | – |

### `Spaces/`

| File | Contents | Proposed location | Class | Status |
|---|---|---|---|---|
| `DirectLimit` | Locally convex direct limits, universal property, strict limits, completeness | `Analysis/LocallyConvex/DirectLimit.lean` | N (see `TestFunction`) | – |
| `DirectSum` | Locally convex direct sums, universal property; direct sums of `C^k` and analytic maps | `Analysis/LocallyConvex/DirectSum.lean` | N, last section F | – |
| `DirectLimitQuotient` | Direct limits as quotients of direct sums; the quotient of a locally convex space is locally convex | `Analysis/LocallyConvex/DirectLimit.lean`; the quotient instance in `Topology/Algebra/Module/LocallyConvex.lean` | N (`locallyConvexSpace_quotient`: E) | quotient instance prepared, not proposed |
| `DirectCompleteness` | Sequential, Mackey and quasi-completeness of direct sums and strict limits | `Analysis/LocallyConvex/DirectLimit.lean` | N | – |
| `Silva` | Silva spaces (DFS) | `Analysis/LocallyConvex/Silva.lean` | N, one result F | – |
| `SilvaDuality` | Reflexivity of Silva spaces; Silva spaces are `k_ω` | `Analysis/LocallyConvex/Silva.lean` | N | – |
| `InverseAlgebra` | Continuous inverse algebras; inversion is smooth and analytic | — | F | – |

### `Krein/`

| File | Contents | Proposed location | Class | Status |
|---|---|---|---|---|
| `HilbertComplexification` | Complexification of a real inner product space | `Analysis/InnerProductSpace/Complexification.lean` | N | – |
| `SpectralParts` | Positive and negative parts of self-adjoint operators, spectral projections | `Analysis/InnerProductSpace/` | E | – |
| `OrthoComplemented` | Ortho-complemented subspaces of a Krein space, Gram operators | `Analysis/InnerProductSpace/Krein/` | N | – |
| `Majorant` | Krein spaces, fundamental decompositions, majorant topology | `Analysis/InnerProductSpace/Krein/` | N | – |
| `IntrinsicDimension` | Ranks of positivity and negativity | `Analysis/InnerProductSpace/Krein/` | N | – |
| `Perturbation` | The index is locally constant in continuous families | `Analysis/InnerProductSpace/Krein/` | N | – |

### `Analytic/`

| File | Contents | Proposed location | Class | Status |
|---|---|---|---|---|
| `Polynomial` | Symmetric multilinear maps, symmetrization, polarization formula, continuous homogeneous polynomials | `LinearAlgebra/Multilinear/Symmetric.lean`, `Topology/Algebra/Module/Multilinear/` | E | – |
| `OneVariable` | Power series and complex derivatives of one variable with locally convex values | — | F | – |
| `Complex`, `Real`, `Operations`, `Identity` | Complex and real analytic maps on locally convex spaces | — | F | – |
| `ComplexMB`, `ComplexC1`, `BanachHolomorphic` | Complex Michal–Bastiani calculus; bridges to Mathlib's holomorphy | — | F | – |
| `HartogsLemma` | Hartogs' lemma for vector-valued holomorphic families | `Analysis/Complex/` | F; possibly E (see below) | – |
| `Hartogs`, `SeparateAnalyticity`, `Zorn` | Hartogs' theorem on separate analyticity, Zorn's theorem | `Analysis/Complex/Hartogs.lean` for `ℂ²` | F; possibly E for `ℂ²` (see below) | – |

Hartogs' theorem on `ℂ²` (`continuousOn_of_separately`) and Hartogs' lemma (`hartogs_lemma`) are
not in Mathlib. The statement of `hartogs_lemma` already uses Mathlib's `AnalyticOnNhd`; the one of
`continuousOn_of_separately` uses this library's `CAnalyticOn`, which agrees with `AnalyticOnNhd`
for Banach-valued maps. Both files import `Analytic/OneVariable.lean`, and through it the
calculus. Whether that import can be removed has not been checked; if it can, both are class E.
| `HomogeneousSeries`, `RealSeries` | Series of homogeneous polynomials (Bochnak–Siciak) | — | F | – |
| `WeakHolomorphic` | Weakly holomorphic maps into Mackey complete spaces | — | F | – |
| `OperatorValued` | Analytic operator-valued maps | — | F | – |
| `RealInverse` | Real analytic inverse function theorem | — | F (see Mathlib's `analyticAt_symm`) | – |

### `Calculus/`

| File | Contents | Proposed location | Class | Status |
|---|---|---|---|---|
| `MichalBastiani` | Directional derivatives, `C^k` maps, chain rule | see [The central design question](#the-central-design-question) | F (core) | – |
| `Higher`, `Rules` | Higher differentials, product rule, Taylor's formula | — | F | – |
| `Operations` | Sums, products, multiples, differences, products of maps, closed subspaces, locality of the differential, comparison with Fréchet derivatives | — | F | – |
| `MBFrechet` | Michal–Bastiani `C^{k+1}` implies Fréchet `C^k` on normed spaces | — | F (bridge) | – |
| `Integral/Basic`, `Integral/Existence`, `Integral/FundamentalTheorem` | Weak integrals, existence, fundamental theorem | — | F; `SeqComplete`, `MackeyComplete`: N | – |
| `MackeyLipschitz` | Mackey completeness through Lipschitz curves | — | F | – |
| `BoundedBelow`, `BoundedBelowLC`, `OperatorValued` | Maps with bounded below derivative reflect smoothness | — | F (`exists_boundedBelow_of_isEmbedding` is in Mathlib) | – |
| `CklMaps`, `CklSchwarz`, `ExponentialLaw`, `SmoothExponentialLaw` | `C^{k,ℓ}` maps and the exponential law | — | F | – |
| `DenseInterior/` (7 files) | `C^k` maps on locally convex sets with dense interior | — | F | – |

### `MappingSpace/`, `ODE/`, `Frobenius/`, `Complex/`

All files in these folders are class F. Some state theorems about Banach spaces whose statements
fit Mathlib's normed calculus, but their proofs go through this library:

* `ODE/Flow.lean`: smooth dependence of local flows on initial data, on Banach spaces. Mathlib has
  existence and uniqueness (`IsPicardLindelof`), but not smooth dependence.
* `ODE/Quadratic.lean`: uniform local existence for quadratic sprays.
* `Frobenius/Basic.lean`, `Frobenius/Chart.lean`: the Frobenius theorem on Banach spaces.
* `Complex/NormedComplexification.lean`: a complex norm on the complexification of a real normed
  space. Mathlib has no complexification of normed spaces.

These would be candidates of class E if they were rewritten with Mathlib's Fréchet calculus.

### `Counterexamples/`

| File | Contents | Depends on the calculus | Status |
|---|---|---|---|
| `Units` | The units of `C(ℝ, ℝ)` are not open | no | – |
| `WeakDarboux` | Darboux's theorem fails for weak symplectic forms (Marsden) | no (normed calculus) | – |
| `BognarKrein` | A closed positive definite subspace of a Krein space that is not a Krein space | no (`Krein/`) | – |
| `BoundedBelowStability` | Lower bounds of operator families: stable in normed spaces, not in Fréchet spaces | yes | – |
| `ReflectSmoothness` | Invertible derivatives do not reflect smoothness in Fréchet spaces | yes | – |
| `InverseFunction` | The inverse function theorem fails on `ℝ^ℕ` | yes | – |
| `ODEUniqueness`, `ODEExistence` | Uniqueness and existence fail for linear ODEs in Fréchet spaces | yes | – |
| `FrobeniusFails` | The Frobenius theorem fails in Fréchet spaces | yes | – |
| `HomogeneousSeries` | Series of homogeneous polynomials: the Baire and completeness hypotheses are needed | yes | – |
| `LocalBoundedness` | Complex analytic maps need not be locally bounded | yes | – |

## Suggested order

1. **Class E, now.** Each item extends an existing Mathlib file and needs no prior Zulip
   discussion:
   * `Analytic/Polynomial.lean` (symmetrization and polarization);
   * `locallyConvexSpace_quotient` (Mathlib has no `LocallyConvexSpace` instance on quotients;
     prepared, see [above](#prepared-a-locallyconvexspace-instance-on-quotients));
   * the real case of `Krein/SpectralParts.lean`.
2. **Class X without the calculus:** `Units`, `WeakDarboux` (after rewriting with `extDeriv`),
   `BognarKrein` (after `Krein/`).
3. **Class N, after a scope discussion on Zulip:** `Topology/` (direct limits and `k_ω`-spaces),
   locally convex direct limits and sums (related to `TestFunction`), Silva spaces, Krein spaces.
4. **Class F**, only if the design discussion on the Michal–Bastiani calculus concludes that it
   belongs in Mathlib.

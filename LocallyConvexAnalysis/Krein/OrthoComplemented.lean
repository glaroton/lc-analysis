/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import LocallyConvexAnalysis.Krein.HilbertComplexification
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import LocallyConvexAnalysis.Krein.SpectralParts

/-!
# Ortho-complemented subspaces of a Krein space

References: J. Bognár, *Indefinite Inner Product Spaces*, Springer (1974): §I.9, p. 18
(ortho-complemented subspaces, Lemma I.9.2) and Corollary I.9.5 (p. 19); Example I.9.7
(pp. 19–20); §I.11, p. 24 (fundamental decompositions); Corollary III.2.5 (p. 60); §III.8, p. 71
(intrinsic norm, intrinsically complete subspaces); Theorem IV.5.2 (p. 89); §V.1, p. 100 (Krein
spaces, Corollary V.1.2) and Theorem V.1.3 (p. 101); **Theorem V.3.1** (p. 103); Example V.3.3 and
**Theorem V.3.4** (p. 104); **Theorem V.3.5** (pp. 104–105).
T. Ya. Azizov and I. S. Iokhvidov, *Linear Operators in Spaces with an Indefinite Metric*, Wiley
(1989), Ch. 1 §7: Definition 7.8, Propositions 7.9 and 7.10 (p. 44), Lemma 7.11 (p. 45),
Theorem 7.16 (p. 46).

## Setting

Bognár's definitions are algebraic. An *inner product space* is a vector space with a Hermitian
form `[·, ·]`; it is a **Krein space** (§V.1) if it admits a fundamental decomposition
`L = L₊ ⊕ L₋` (a `[·, ·]`-orthogonal direct sum, `[·, ·]` positive definite on `L₊` and negative
definite on `L₋`, §I.11) whose components are **intrinsically complete**: complete for the norms
`√[x, x]` on `L₊` and `√(-[x, x])` on `L₋` (§III.8). No topology enters this definition
(`AlgFundamentalDecomposition`, `KreinDecomposition`, `IsKreinSpace`, `IntrinsicallyComplete`,
for a sesquilinear form on any module).

## Main results

* `IsOrthoComplemented.isClosed`, `IsOrthoComplemented.eq_zero`: an ortho-complemented subspace
  is closed and nondegenerate ([Bog74, Corollaries III.2.5 and I.9.5]; [AI89, 1.7.9 and 1.7.10]).
  No completeness is used.
* `isOrthoComplemented_iff_bijective_gram`: for a subspace with an orthogonal projection `P_L`,
  `L` is ortho-complemented iff the **Gram operator** `G_L = P_L J|_L` (`gram`, characterized by
  `⟪G_L x, y⟫ = [x, y]` on `L`) is bijective (condition (3.1) in Bognár's proof of Theorem V.3.4;
  [AI89, Lemma 1.7.11 and Theorem 1.7.16], a ⇔ b).
* `isOrthoComplemented_iff_exists_projector`: `L` is ortho-complemented iff there is a
  **continuous `J`-orthogonal projector** onto `L`, i.e. `Q` with `[Q w, t] = [w, t]` for
  `t ∈ L`; such a projector is unique (`IsOrthoComplemented.eq_of_projector`).
* `isOrthoComplemented_of_kreinDecomposition` (**Theorem V.3.4, "if"**): a closed subspace which
  is a Krein space with the restricted form is ortho-complemented; so it has a continuous
  `J`-orthogonal projector (`exists_projector_of_kreinDecomposition`).
* `IsOrthoComplemented.isKreinSpace` (**Theorem V.3.4, "only if"**) and
  `isOrthoComplemented_iff_isClosed_and_isKreinSpace`: **a subspace of a Krein space is
  ortho-complemented if and only if it is closed and a Krein space**, over `ℝ` and `ℂ`. The whole
  space is a Krein space (`isKreinSpace_top`).
* `exists_spectral_projection`, `exists_posPart_negPart`, `exists_sign_decomposition` (spectral
  projections and positive and negative parts of self-adjoint operators) are in
  `LocallyConvexAnalysis.Krein.SpectralParts`.
* `exists_fundamentalDecomposition_of_isClosed` (**Theorem V.3.1**): every closed subspace `L` of
  a Krein space has a fundamental decomposition `L = L⁰ ∔ L₊ ∔ L₋` (§I.11, `L⁰` the isotropic
  part) whose three components and the sums of any two of them are closed; for nondegenerate `L`,
  `exists_algFundamentalDecomposition_of_isClosed`.
* `isOrthoComplemented_iff_uniformlyPositive_of_posDef`,
  `isOrthoComplemented_iff_intrinsicallyComplete_of_posDef`: a positive definite subspace is
  ortho-complemented iff it is closed and uniformly positive, iff it is closed and intrinsically
  complete (`IntrinsicallyComplete.exists_lower_bound`, open mapping theorem). Hence
  `not_isOrthoComplemented_of_posDef`: a closed positive definite subspace which is not uniformly
  positive is nondegenerate and decomposable but not a Krein space; **[Bog74, Example V.3.3]** is
  such a subspace (`LocallyConvexAnalysis/Counterexamples/BognarKrein.lean`).
* `isOrthoComplemented_iff_isClosed_nondegenerate` (**Theorem V.3.5**, as stated by Bognár): `L`
  is ortho-complemented iff it is closed, nondegenerate, and every fundamental decomposition
  `L = L₊ ⊕ L₋` extends to one `H = H₊ ⊕ H₋` of the whole space with `L₊ ⊆ H₊`, `L₋ ⊆ H₋`;
  `isOrthoComplemented_iff_algFundamentalDecomposition` is the variant with "has a fundamental
  decomposition" in place of "nondegenerate". On the way: every fundamental decomposition of the
  whole Krein space has uniformly definite components (`exists_pos_bound_of_top`,
  `exists_neg_bound_of_top`), and an orthogonal sum of ortho-complemented subspaces is
  ortho-complemented (`IsOrthoComplemented.sup`, Lemma I.9.2).
* The application to fields of `β`-orthogonal projectors on submanifolds of a Krein space (their
  tangent spaces are ortho-complemented Krein spaces, with continuous projectors) is in
  lc-manifolds (`LocallyConvexManifolds/Metric/KreinProjector.lean`).

## Where completeness is used

* Closedness and nondegeneracy of ortho-complemented subspaces, and the equivalence with the
  surjectivity of the Gram operator, use no completeness (only the orthogonal projection onto
  `L`, which exists when `L` is complete).
* "If": the completeness of `H` (closed graph theorem for the inclusion of the intrinsic Hilbert
  space `(L₊, √[x, x])` into `H`), the closedness of `L` (the limit of a sequence of `L₊` lies in
  `L`, where `[·, ·]` is nondegenerate), and the intrinsic completeness of `L₊`, `L₋` (Riesz
  representation in them).
* "Only if": the completeness of `H` and the closedness of `L` (bounded inverse of `G_L`, and
  the continuous functional calculus in the C⋆-algebra of the complexification of `L`); the
  components `L₊`, `L₋` are the spectral subspaces of `G_L` for `(0, ∞)` and `(-∞, 0)`, closed,
  with `±[x, x] ≥ c ‖x‖²`, hence intrinsically complete.
* Positive definite subspaces and Theorem V.3.5: the completeness of `H` (through Theorem V.3.4 and
  the open mapping theorem).
* Theorem V.3.1: the completeness of `H` and the closedness of `L` (the continuous functional
  calculus for the Gram operator `G_L` in the C⋆-algebra of the complexification of `L`, and
  orthogonal projections onto closed subspaces of `L`).

## Departures from the sources

Bognár proves Theorem V.3.4 through his Theorem V.1.3 (a space is Krein iff its form has a
Hilbert majorant with completely invertible Gram operator) and the theory of majorant topologies
of Chapter IV. Here "if" is proved directly: the closed graph theorem shows that the intrinsic
norms dominate the norm of `H`, and Riesz's theorem in `L₊` and `L₋` produces the
`J`-orthogonal projection; this is the route c ⇒ d ⇒ a of [AI89, Theorem 1.7.16],
with the closed graph theorem in place of their Theorem 1.5.7 (p. 32; uniform definiteness of
the components). "Only if" uses the spectral projections of the Gram operator, as in
Azizov–Iokhvidov (b ⇒ c, via their Corollary 1.6.12, p. 39). We do not claim this argument is new.

Bognár works over `ℂ`; everything here holds over `ℝ` and `ℂ`. Mathlib's continuous functional
calculus is available for complex C⋆-algebras only, so for real spaces the spectral projection of
`G_L` is obtained from that of its complexification `G_ℂ`, which commutes with the conjugation
(`exists_spectral_projection`).

Theorem V.3.1: Bognár deduces it from Corollary V.1.2 and Theorem IV.5.2, whose proof uses the
spectral function `E(λ)` of the Gram operator `G` of a Hilbert majorant: the components are
`E(-0) H`, `(E(0) - E(-0)) H` and `(I - E(0)) H`. Since `0` may lie in the spectrum of `G`, these
spectral projections are not continuous functions of `G`. We use instead the positive and negative
parts `G^±` (continuous functions of `G`) and take `ker G`, `(ker G⁺)^⊥` and `(ker G⁻)^⊥`: the
relation `G⁻ G⁺ = 0` gives `(ker G⁺)^⊥ ⊆ ker G⁻`, and positivity of `G⁺` gives definiteness
(`exists_sign_decomposition`). The subspaces coincide with Bognár's, but this is not used.

Theorem V.3.5: Bognár's "if" ortho-complements `L₊` inside the Hilbert space `(H₊, [·, ·])`;
here `L₊` is shown to be closed and uniformly positive, hence ortho-complemented in `H`. For a
closed nondegenerate `L` a fundamental decomposition exists by Theorem V.3.1, so the theorem is
stated exactly as Bognár does (`isOrthoComplemented_iff_isClosed_nondegenerate`). We do not claim
these arguments are new.

## References

* [T. Ya. Azizov, I. S. Iokhvidov, *Linear Operators in Spaces with an Indefinite Metric*][AI89]
* [J. Bognár, *Indefinite Inner Product Spaces*][Bog74]
-/

@[expose] public section

open Filter RCLike
open scoped Topology InnerProductSpace ComplexConjugate

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Krein spaces without topology -/

section Algebraic

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- A subspace `S` is **intrinsically complete** for the sesquilinear form `B` if it is complete
for the "intrinsic norm" `√(re B(x, x))`: every sequence of `S` that is Cauchy for it converges
in it to a point of `S`. Only meaningful when `B` is positive definite on `S`. -/
def IntrinsicallyComplete (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (S : Submodule 𝕜 E) : Prop :=
  ∀ u : ℕ → E, (∀ n, u n ∈ S) →
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, re (B (u m - u n) (u m - u n)) < ε) →
    ∃ x ∈ S, Tendsto (fun n ↦ re (B (u n - x) (u n - x))) atTop (𝓝 0)

/-- A **fundamental decomposition** of the subspace `L` for the sesquilinear form `B`
([Bog74, §I.11]): `L = L₊ ⊕ L₋`, a `B`-orthogonal direct sum with `B` positive definite on `L₊` and
negative definite on `L₋`. Purely algebraic: unlike `FundamentalDecomposition`
(in lc-manifolds, `LocallyConvexManifolds.Metric.Bilinear`), no continuous projector is required. -/
structure AlgFundamentalDecomposition (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (L : Submodule 𝕜 E) where
  /-- The positive component `L₊`. -/
  pos : Submodule 𝕜 E
  /-- The negative component `L₋`. -/
  neg : Submodule 𝕜 E
  sup_eq : pos ⊔ neg = L
  disjoint : Disjoint pos neg
  orth : ∀ x ∈ pos, ∀ y ∈ neg, B x y = 0
  pos_def : ∀ x ∈ pos, x ≠ 0 → 0 < re (B x x)
  neg_def : ∀ x ∈ neg, x ≠ 0 → re (B x x) < 0

/-- A **Krein decomposition** of the subspace `L` for the sesquilinear form `B`: a fundamental
decomposition `L = L₊ ⊕ L₋` whose components are intrinsically complete (`L₊` for `B`, `L₋` for
`-B`). No topology is involved. -/
structure KreinDecomposition (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (L : Submodule 𝕜 E)
    extends AlgFundamentalDecomposition B L where
  pos_complete : IntrinsicallyComplete B pos
  neg_complete : IntrinsicallyComplete (-B) neg

/-- `L`, with the restriction of `B`, **is a Krein space** ([Bog74, §V.1]). -/
def IsKreinSpace (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (L : Submodule 𝕜 E) : Prop :=
  Nonempty (KreinDecomposition B L)

namespace AlgFundamentalDecomposition

variable {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} {L : Submodule 𝕜 E} (K : AlgFundamentalDecomposition B L)

theorem pos_le : K.pos ≤ L := le_sup_left.trans K.sup_eq.le

theorem neg_le : K.neg ≤ L := le_sup_right.trans K.sup_eq.le

include K in
/-- A subspace with a fundamental decomposition is **nondegenerate**: no nonzero vector of `L`
is `B`-orthogonal to `L`. -/
theorem eq_zero_of_forall (hB : ∀ x y, conj (B y x) = B x y) {v : E} (hv : v ∈ L)
    (hperp : ∀ z ∈ L, B v z = 0) : v = 0 := by
  rw [← K.sup_eq, Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  have hab : B a b = 0 := K.orth a ha b hb
  have hba : B b a = 0 := by rw [← hB, K.orth a ha b hb, map_zero]
  have h1 : B a a = 0 := by
    have := hperp a (K.pos_le ha)
    rwa [map_add, LinearMap.add_apply, hba, add_zero] at this
  have h2 : B b b = 0 := by
    have := hperp b (K.neg_le hb)
    rwa [map_add, LinearMap.add_apply, hab, zero_add] at this
  have ha0 : a = 0 := by
    by_contra h
    have := K.pos_def a ha h
    rw [h1, map_zero] at this
    exact lt_irrefl _ this
  have hb0 : b = 0 := by
    by_contra h
    have := K.neg_def b hb h
    rw [h2, map_zero] at this
    exact lt_irrefl _ this
  rw [ha0, hb0, add_zero]

end AlgFundamentalDecomposition

/-- The sum of two mutually `B`-orthogonal positive definite subspaces is positive definite. -/
theorem posDef_sup {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} {S T : Submodule 𝕜 E}
    (hS : ∀ x ∈ S, x ≠ 0 → 0 < re (B x x)) (hT : ∀ x ∈ T, x ≠ 0 → 0 < re (B x x))
    (hST : ∀ x ∈ S, ∀ y ∈ T, B x y = 0) (hTS : ∀ x ∈ T, ∀ y ∈ S, B x y = 0) :
    ∀ x ∈ S ⊔ T, x ≠ 0 → 0 < re (B x x) := by
  intro x hx hx0
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  have e : re (B (a + b) (a + b)) = re (B a a) + re (B b b) := by
    simp only [map_add, LinearMap.add_apply, hST a ha b hb, hTS b hb a ha, add_zero, zero_add]
  have h1 : 0 ≤ re (B a a) := by
    by_cases h : a = 0
    · simp [h]
    · exact (hS a ha h).le
  have h2 : 0 ≤ re (B b b) := by
    by_cases h : b = 0
    · simp [h]
    · exact (hT b hb h).le
  rw [e]
  by_cases h : a = 0
  · subst h
    simp only [zero_add] at hx0 ⊢
    have := hT b hb hx0
    simpa using this
  · linarith [hS a ha h]

end Algebraic

/-! ### The intrinsic Hilbert space of a definite subspace -/

section Intrinsic

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- The subspace `S` with the inner product `B` (Hermitian, positive definite on `S`). A type
synonym of `S`. -/
@[nolint unusedArguments]
def IntrinsicSpace (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (S : Submodule 𝕜 E)
    (_hB : ∀ x y, conj (B y x) = B x y) (_hpos : ∀ x ∈ S, x ≠ 0 → 0 < re (B x x)) : Type _ :=
  S

namespace IntrinsicSpace

variable {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} {S : Submodule 𝕜 E} {hB : ∀ x y, conj (B y x) = B x y}
  {hpos : ∀ x ∈ S, x ≠ 0 → 0 < re (B x x)}

instance : AddCommGroup (IntrinsicSpace B S hB hpos) := inferInstanceAs (AddCommGroup S)

instance : Module 𝕜 (IntrinsicSpace B S hB hpos) := inferInstanceAs (Module 𝕜 S)

/-- The underlying vector of `E`. -/
def val (x : IntrinsicSpace B S hB hpos) : E := ((show S from x) : E)

theorem val_mem (x : IntrinsicSpace B S hB hpos) : x.val ∈ S := (show S from x).2

/-- The vector of `S` seen in the intrinsic space. -/
def mk (x : E) (hx : x ∈ S) : IntrinsicSpace B S hB hpos := (⟨x, hx⟩ : S)

@[simp] theorem val_mk (x : E) (hx : x ∈ S) : (mk x hx : IntrinsicSpace B S hB hpos).val = x :=
  rfl

@[simp] theorem val_zero : (0 : IntrinsicSpace B S hB hpos).val = 0 := rfl

@[simp] theorem val_add (x y : IntrinsicSpace B S hB hpos) : (x + y).val = x.val + y.val := rfl

@[simp] theorem val_sub (x y : IntrinsicSpace B S hB hpos) : (x - y).val = x.val - y.val := rfl

@[simp] theorem val_smul (c : 𝕜) (x : IntrinsicSpace B S hB hpos) : (c • x).val = c • x.val :=
  rfl

theorem val_injective : Function.Injective (val : IntrinsicSpace B S hB hpos → E) :=
  fun _ _ h ↦ Subtype.ext h

/-- The inner product `B` on `S`. -/
@[instance_reducible]
def core : InnerProductSpace.Core 𝕜 (IntrinsicSpace B S hB hpos) where
  inner x y := B x.val y.val
  conj_inner_symm x y := hB _ _
  re_inner_nonneg x := by
    by_cases hx : x.val = 0
    · simp [hx]
    · exact (hpos _ x.val_mem hx).le
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := by
    by_contra h
    have h' : x.val ≠ 0 := fun h0 ↦ h (val_injective (by simpa using h0))
    have := hpos _ x.val_mem h'
    have hx' : B x.val x.val = 0 := hx
    rw [hx', map_zero] at this
    exact lt_irrefl _ this

instance : NormedAddCommGroup (IntrinsicSpace B S hB hpos) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 _ _ _ _ core

instance : InnerProductSpace 𝕜 (IntrinsicSpace B S hB hpos) :=
  InnerProductSpace.ofCore (core (B := B) (S := S) (hB := hB) (hpos := hpos)).toCore

theorem inner_eq (x y : IntrinsicSpace B S hB hpos) : ⟪x, y⟫_𝕜 = B x.val y.val := rfl

theorem norm_eq (x : IntrinsicSpace B S hB hpos) : ‖x‖ = √(re (B x.val x.val)) := rfl

/-- An intrinsically complete subspace is a Hilbert space for its intrinsic norm. -/
theorem completeSpace (hc : IntrinsicallyComplete B S) :
    CompleteSpace (IntrinsicSpace B S hB hpos) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨x, hxS, hx⟩ := hc (fun n ↦ (u n).val) (fun n ↦ (u n).val_mem) fun ε hε ↦ by
    obtain ⟨N, hN⟩ := hu (√ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h := hN m hm n hn
    rw [dist_eq_norm, norm_eq, val_sub] at h
    exact (Real.sqrt_lt_sqrt_iff_of_pos hε).1 h |>.trans_le' le_rfl
  refine ⟨mk x hxS, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp hx
  simpa [Function.comp_def, norm_eq] using this

end IntrinsicSpace

end Intrinsic

/-! ### Fundamental symmetries -/

/-- A **fundamental symmetry** of a Hilbert space `H`: a continuous self-adjoint involution `J`.
It defines the indefinite inner product `[x, y] = ⟪J x, y⟫` (`FundamentalSymmetry.form`), and
`(H, [·, ·])` is a Krein space whose strong topology is the topology of `H`; every Krein space
arises in this way ([Bog74, Corollary V.1.2]). -/
structure FundamentalSymmetry (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] where
  /-- The operator `J`. -/
  op : H →L[𝕜] H
  inner_op : ∀ x y, ⟪op x, y⟫_𝕜 = ⟪x, op y⟫_𝕜
  op_op : ∀ x, op (op x) = x

namespace FundamentalSymmetry

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (J : FundamentalSymmetry 𝕜 H)

/-- The indefinite inner product `[x, y] = ⟪J x, y⟫`. -/
def form : H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜).comp J.op.toLinearMap

@[simp] theorem form_apply (x y : H) : J.form x y = ⟪J.op x, y⟫_𝕜 := rfl

/-- `[·, ·]` is Hermitian. -/
theorem conj_form (x y : H) : conj (J.form y x) = J.form x y := by
  simp only [form_apply, J.inner_op y, inner_conj_symm]

theorem form_comm (x y : H) : ⟪J.op x, y⟫_𝕜 = conj ⟪J.op y, x⟫_𝕜 := by
  rw [J.inner_op y, inner_conj_symm]

/-- `[·, ·]` is nondegenerate on `H`. -/
theorem eq_zero_of_forall {v : H} (hv : ∀ h, ⟪J.op v, h⟫_𝕜 = 0) : v = 0 := by
  have : J.op v = 0 := inner_self_eq_zero.1 (hv _)
  rw [← J.op_op v, this, map_zero]

theorem norm_form_le (x : H) : ‖J.form x x‖ ≤ ‖J.op‖ * ‖x‖ ^ 2 := by
  rw [form_apply, sq, ← mul_assoc]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (J.op.le_opNorm x)
    (norm_nonneg _))

/-- The `J`-orthogonal companion `L^[⊥] = {y | [x, y] = 0 for all x ∈ L}`. -/
def orth (L : Submodule 𝕜 H) : Submodule 𝕜 H where
  carrier := {y | ∀ x ∈ L, ⟪J.op x, y⟫_𝕜 = 0}
  add_mem' {a b} ha hb x hx := by rw [inner_add_right, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := inner_zero_right _
  smul_mem' c a ha x hx := by rw [inner_smul_right, ha x hx, mul_zero]

theorem mem_orth {L : Submodule 𝕜 H} {y : H} : y ∈ J.orth L ↔ ∀ x ∈ L, ⟪J.op x, y⟫_𝕜 = 0 :=
  Iff.rfl

theorem inner_op_eq_zero_of_mem_orth {L : Submodule 𝕜 H} {x y : H} (hx : x ∈ L)
    (hy : y ∈ J.orth L) : ⟪J.op y, x⟫_𝕜 = 0 := by
  rw [J.form_comm, hy x hx, map_zero]

theorem isClosed_orth (L : Submodule 𝕜 H) : IsClosed (J.orth L : Set H) := by
  have : (J.orth L : Set H) = ⋂ x ∈ L, {y | ⟪J.op x, y⟫_𝕜 = 0} := by
    ext y; simp [mem_orth]
  rw [this]
  exact isClosed_biInter fun x _ ↦ isClosed_eq (continuous_const.inner continuous_id)
    continuous_const

/-- `L` is **ortho-complemented** ([Bog74, §I.9]): `L + L^[⊥] = H`, i.e. every vector has a
`J`-orthogonal projection onto `L`. In the terminology of Azizov and Iokhvidov, `L` is
*projectively complete*. -/
def IsOrthoComplemented (L : Submodule 𝕜 H) : Prop := L ⊔ J.orth L = ⊤

variable {J} {L : Submodule 𝕜 H}

/-- An ortho-complemented subspace is nondegenerate ([Bog74, Corollary I.9.5]). -/
theorem IsOrthoComplemented.eq_zero (hL : J.IsOrthoComplemented L) {v : H} (hv : v ∈ L)
    (hv' : v ∈ J.orth L) : v = 0 := by
  refine J.eq_zero_of_forall fun h ↦ ?_
  have hh : h ∈ L ⊔ J.orth L := hL ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
  rw [inner_add_right, J.inner_op_eq_zero_of_mem_orth ha hv', hb v hv, add_zero]

/-- `L^[⊥][⊥] = L` for an ortho-complemented subspace. -/
theorem IsOrthoComplemented.orth_orth (hL : J.IsOrthoComplemented L) : J.orth (J.orth L) = L := by
  refine le_antisymm (fun z hz ↦ ?_) fun x hx b hb ↦ J.inner_op_eq_zero_of_mem_orth hx hb
  have hz' : z ∈ L ⊔ J.orth L := hL ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hz'
  suffices y = 0 by rw [this, add_zero]; exact hx
  refine J.eq_zero_of_forall fun h ↦ ?_
  have hh : h ∈ L ⊔ J.orth L := hL ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
  have h1 : ⟪J.op y, b⟫_𝕜 = 0 := by
    have hxy : ⟪J.op (x + y), b⟫_𝕜 = 0 := J.inner_op_eq_zero_of_mem_orth hb hz
    rwa [map_add, inner_add_left, hb x hx, zero_add] at hxy
  rw [inner_add_right, J.inner_op_eq_zero_of_mem_orth ha hy, h1, add_zero]

/-- An ortho-complemented subspace is closed ([Bog74, Corollary III.2.5]; Azizov–Iokhvidov,
1.7.9). No completeness is needed. -/
theorem IsOrthoComplemented.isClosed (hL : J.IsOrthoComplemented L) : IsClosed (L : Set H) :=
  hL.orth_orth ▸ J.isClosed_orth _

/-- A continuous projector onto `L` along a subspace of `L^[⊥]` makes `L` ortho-complemented. -/
theorem isOrthoComplemented_of_projector (Q : H → H) (hQ : ∀ w, Q w ∈ L)
    (horth : ∀ w, ∀ t ∈ L, ⟪J.op (Q w), t⟫_𝕜 = ⟪J.op w, t⟫_𝕜) : J.IsOrthoComplemented L := by
  refine eq_top_iff.2 fun w _ ↦ Submodule.mem_sup.2 ⟨Q w, hQ w, w - Q w, fun t ht ↦ ?_, by abel⟩
  rw [J.form_comm, map_sub, inner_sub_left, horth w t ht, sub_self, map_zero]

variable (J) in
/-- The fundamental symmetry `-J`, whose form is `-[·, ·]` (the anti-space of `H`). -/
protected def neg : FundamentalSymmetry 𝕜 H where
  op := -J.op
  inner_op x y := by simp [J.inner_op]
  op_op x := by simp [J.op_op]

@[simp] theorem neg_op : J.neg.op = -J.op := rfl

theorem orth_neg (L : Submodule 𝕜 H) : J.neg.orth L = J.orth L := by
  ext y
  simp [mem_orth, inner_neg_left]

@[simp] theorem isOrthoComplemented_neg :
    J.neg.IsOrthoComplemented L ↔ J.IsOrthoComplemented L := by
  simp [IsOrthoComplemented, orth_neg]

/-- **The orthogonal sum of ortho-complemented subspaces is ortho-complemented** (one direction
of [Bog74, Lemma I.9.2, p. 18]). No completeness is used. -/
theorem IsOrthoComplemented.sup {S T : Submodule 𝕜 H} (hS : J.IsOrthoComplemented S)
    (hT : J.IsOrthoComplemented T) (hST : ∀ x ∈ S, ∀ y ∈ T, ⟪J.op x, y⟫_𝕜 = 0) :
    J.IsOrthoComplemented (S ⊔ T) := by
  refine eq_top_iff.2 fun h _ ↦ ?_
  have hh : h ∈ S ⊔ J.orth S := hS ▸ Submodule.mem_top
  obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 hh
  have hy' : y ∈ T ⊔ J.orth T := hT ▸ Submodule.mem_top
  obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 hy'
  refine Submodule.mem_sup.2 ⟨a + b, Submodule.add_mem_sup ha hb, z, fun w hw ↦ ?_, by abel⟩
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hw
  have h1 := hy s hs
  rw [inner_add_right, hST s hs b hb, zero_add] at h1
  rw [map_add, inner_add_left, h1, hz t ht, add_zero]

section AlgFundamentalDecomposition

variable (K : AlgFundamentalDecomposition J.form L)

/-- The positive component of a fundamental decomposition of `L` is `L ∩ L₋^[⊥]`; in particular
it is closed if `L` is (Bognár invokes his Corollary III.2.6 for this in the proof of
Theorem V.3.5). -/
theorem _root_.LocallyConvex.Analysis.AlgFundamentalDecomposition.pos_eq_inf :
    K.pos = L ⊓ J.orth K.neg := by
  refine le_antisymm (le_inf K.pos_le fun y hy x hx ↦ ?_) fun x ⟨hxL, hx⟩ ↦ ?_
  · rw [J.form_comm, show ⟪J.op y, x⟫_𝕜 = J.form y x from rfl, K.orth y hy x hx, map_zero]
  · rw [← K.sup_eq] at hxL
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hxL
    suffices b = 0 by rw [this, add_zero]; exact ha
    refine K.eq_zero_of_forall J.conj_form (K.neg_le hb) fun z hz ↦ ?_
    rw [← K.sup_eq] at hz
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 hz
    have h1 : ⟪J.op b', a + b⟫_𝕜 = 0 := hx b' hb'
    have h2 : ⟪J.op b', a⟫_𝕜 = 0 := by
      rw [J.form_comm, show ⟪J.op a, b'⟫_𝕜 = J.form a b' from rfl, K.orth a ha b' hb', map_zero]
    rw [inner_add_right, h2, zero_add] at h1
    rw [form_apply, inner_add_right, J.form_comm b a', show ⟪J.op a', b⟫_𝕜 = J.form a' b from rfl,
      K.orth a' ha' b hb, map_zero, zero_add, J.form_comm, h1, map_zero]

/-- The negative component of a fundamental decomposition of `L` is `L ∩ L₊^[⊥]`. -/
theorem _root_.LocallyConvex.Analysis.AlgFundamentalDecomposition.neg_eq_inf :
    K.neg = L ⊓ J.orth K.pos := by
  refine le_antisymm (le_inf K.neg_le fun y hy x hx ↦ K.orth x hx y hy) fun x ⟨hxL, hx⟩ ↦ ?_
  rw [← K.sup_eq] at hxL
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hxL
  suffices a = 0 by rw [this, zero_add]; exact hb
  refine K.eq_zero_of_forall J.conj_form (K.pos_le ha) fun z hz ↦ ?_
  rw [← K.sup_eq] at hz
  obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 hz
  have h1 : ⟪J.op a', a + b⟫_𝕜 = 0 := hx a' ha'
  have h2 : ⟪J.op a', b⟫_𝕜 = 0 := K.orth a' ha' b hb
  rw [inner_add_right, h2, add_zero] at h1
  rw [form_apply, inner_add_right, show ⟪J.op a, b'⟫_𝕜 = J.form a b' from rfl,
    K.orth a ha b' hb', add_zero, J.form_comm, h1, map_zero]

/-- The components of a fundamental decomposition of a closed subspace are closed. -/
theorem _root_.LocallyConvex.Analysis.AlgFundamentalDecomposition.isClosed_pos
    (hL : IsClosed (L : Set H)) : IsClosed (K.pos : Set H) := by
  rw [K.pos_eq_inf, Submodule.coe_inf]
  exact hL.inter (J.isClosed_orth _)

theorem _root_.LocallyConvex.Analysis.AlgFundamentalDecomposition.isClosed_neg
    (hL : IsClosed (L : Set H)) : IsClosed (K.neg : Set H) := by
  rw [K.neg_eq_inf, Submodule.coe_inf]
  exact hL.inter (J.isClosed_orth _)

end AlgFundamentalDecomposition

/-! ### The Gram operator -/

section Gram

variable (J L) in
/-- The **Gram operator** of the closed subspace `L`: `G_L = P_L J|_L`, where `P_L` is the
orthogonal projection onto `L`. It represents the restriction of `[·, ·]` to `L` in the inner
product of `H`: `⟪G_L x, y⟫ = [x, y]` (`inner_gram`). -/
def gram [L.HasOrthogonalProjection] : L →L[𝕜] L :=
  L.orthogonalProjectionOnto ∘L J.op ∘L L.subtypeL

variable [L.HasOrthogonalProjection]

theorem inner_gram (x y : L) : ⟪J.gram L x, y⟫_𝕜 = ⟪J.op x, (y : H)⟫_𝕜 := by
  simp [gram]

theorem gram_eq_iff (x : L) (h : H) : J.gram L x = L.orthogonalProjectionOnto (J.op h) ↔
    (x : H) - h ∈ J.orth L := by
  have key : J.gram L x = L.orthogonalProjectionOnto (J.op h) ↔
      ∀ t : L, ⟪(t : H), J.op x⟫_𝕜 = ⟪(t : H), J.op h⟫_𝕜 := by
    constructor
    · intro hx t
      have := congrArg (fun z : L ↦ ⟪t, z⟫_𝕜) hx
      simpa only [gram, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using this
    · intro ht
      refine ext_inner_left 𝕜 fun t ↦ ?_
      simpa only [gram, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using ht t
  rw [key]
  constructor
  · intro ht t htL
    rw [J.inner_op, map_sub, inner_sub_right, ht ⟨t, htL⟩, sub_self]
  · intro hx t
    have := hx t t.2
    rwa [J.inner_op, map_sub, inner_sub_right, sub_eq_zero] at this

/-- **Ortho-complemented subspaces and the Gram operator** ([Bog74, proof of Theorem V.3.4];
[AI89, Lemma 1.7.11]): `L` is ortho-complemented iff `G_L` is surjective. Only the
orthogonal projection onto `L` is used. -/
theorem isOrthoComplemented_iff_surjective_gram :
    J.IsOrthoComplemented L ↔ Function.Surjective (J.gram L) := by
  constructor
  · intro hL ℓ
    have hh : J.op ℓ ∈ L ⊔ J.orth L := hL ▸ Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hh
    refine ⟨⟨x, hx⟩, ?_⟩
    have := (gram_eq_iff (J := J) ⟨x, hx⟩ (J.op ℓ)).2 (by
      rw [← hxy]; simpa using (J.orth L).neg_mem hy)
    rw [this, J.op_op]
    exact L.orthogonalProjectionOnto_mem_subspace_eq_self ℓ
  · intro hG
    refine eq_top_iff.2 fun h _ ↦ ?_
    obtain ⟨x, hx⟩ := hG (L.orthogonalProjectionOnto (J.op h))
    have := (gram_eq_iff x h).1 hx
    exact Submodule.mem_sup.2 ⟨x, x.2, h - x, by simpa using (J.orth L).neg_mem this, by abel⟩

/-- For an ortho-complemented `L` the Gram operator is injective. -/
theorem IsOrthoComplemented.injective_gram (hL : J.IsOrthoComplemented L) :
    Function.Injective (J.gram L) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have h0 : J.gram L x = L.orthogonalProjectionOnto (J.op 0) := by simpa using hx
  have := (gram_eq_iff x 0).1 h0
  rw [sub_zero] at this
  exact Subtype.ext (hL.eq_zero x.2 this)

/-- `L` is ortho-complemented iff its Gram operator is bijective ([Bog74, (3.1)] in the proof of
Theorem V.3.4; [AI89, Theorem 1.7.16], a ⇔ b). -/
theorem isOrthoComplemented_iff_bijective_gram :
    J.IsOrthoComplemented L ↔ Function.Bijective (J.gram L) :=
  ⟨fun hL ↦ ⟨hL.injective_gram, isOrthoComplemented_iff_surjective_gram.1 hL⟩,
    fun h ↦ isOrthoComplemented_iff_surjective_gram.2 h.2⟩

end Gram

/-- **Ortho-complemented subspaces and `J`-orthogonal projectors.** In a Hilbert space `H`, `L`
is ortho-complemented iff there is a continuous projector `Q` onto `L` which is `J`-orthogonal:
`[Q w, t] = [w, t]` for `t ∈ L`, i.e. `ker Q ⊆ L^[⊥]`. The continuity of `Q` comes from the
closed graph theorem (through the bounded inverse of the Gram operator), and uses the
completeness of `H`. -/
theorem isOrthoComplemented_iff_exists_projector [CompleteSpace H] :
    J.IsOrthoComplemented L ↔ ∃ Q : H →L[𝕜] H, (∀ w, Q w ∈ L) ∧ (∀ t ∈ L, Q t = t) ∧
      ∀ w, ∀ t ∈ L, ⟪J.op (Q w), t⟫_𝕜 = ⟪J.op w, t⟫_𝕜 := by
  refine ⟨fun hL ↦ ?_, fun ⟨Q, hQ, _, horth⟩ ↦ isOrthoComplemented_of_projector Q hQ horth⟩
  have : CompleteSpace L := hL.isClosed.completeSpace_coe
  have hb := isOrthoComplemented_iff_bijective_gram.1 hL
  let e := ContinuousLinearEquiv.ofBijective (J.gram L) (LinearMap.ker_eq_bot.2 hb.1)
    (LinearMap.range_eq_top.2 hb.2)
  refine ⟨L.subtypeL ∘L (e.symm : L →L[𝕜] L) ∘L L.orthogonalProjectionOnto ∘L J.op,
    fun w ↦ by simp, fun t ht ↦ ?_, fun w t ht ↦ ?_⟩
  · have h1 : L.orthogonalProjectionOnto (J.op t) = e ⟨t, ht⟩ := rfl
    simp [h1]
  · have hx : J.gram L (e.symm (L.orthogonalProjectionOnto (J.op w))) =
        L.orthogonalProjectionOnto (J.op w) := e.apply_symm_apply _
    have := J.inner_op_eq_zero_of_mem_orth ht ((gram_eq_iff _ w).1 hx)
    rw [map_sub, inner_sub_left, sub_eq_zero] at this
    simpa using this

/-! ### Krein subspaces are ortho-complemented -/

/-- The key step: `J`-orthogonal projections onto one component `S` of a Krein decomposition of
a closed subspace `L` (`B' = σ [·, ·]` positive definite and intrinsically complete on `S`).
By the closed graph theorem the inclusion of the intrinsic Hilbert space of `S` into `H` is
continuous, so `x ↦ [h, x]` is intrinsically continuous on `S` and is represented by a vector
of `S` (Riesz). -/
theorem exists_proj_of_component [CompleteSpace H] (hL : IsClosed (L : Set H))
    (hnd : ∀ v ∈ L, (∀ z ∈ L, ⟪J.op v, z⟫_𝕜 = 0) → v = 0)
    {S : Submodule 𝕜 H} (hSL : S ≤ L) (B' : H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜) (σ : 𝕜) (hσ : σ ≠ 0)
    (hB' : ∀ x y, B' x y = σ * ⟪J.op x, y⟫_𝕜) (hherm : ∀ x y, conj (B' y x) = B' x y)
    (hpos : ∀ x ∈ S, x ≠ 0 → 0 < re (B' x x)) (hc : IntrinsicallyComplete B' S)
    (hcomp : ∀ z ∈ L, ∃ a ∈ S, ∀ x ∈ S, ⟪J.op x, z⟫_𝕜 = ⟪J.op x, a⟫_𝕜) (h : H) :
    ∃ w ∈ S, ∀ x ∈ S, ⟪J.op w, x⟫_𝕜 = ⟪J.op h, x⟫_𝕜 := by
  have := IntrinsicSpace.completeSpace (hB := hherm) (hpos := hpos) hc
  let ι : IntrinsicSpace B' S hherm hpos →ₗ[𝕜] H :=
    { toFun := IntrinsicSpace.val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hι : Continuous ι := by
    refine ι.continuous_of_seq_closed_graph fun u x y hux huy ↦ ?_
    have hyL : y ∈ L :=
      hL.mem_of_tendsto huy (Eventually.of_forall fun n ↦ hSL (u n).val_mem)
    have hyx : y - x.val = 0 := by
      refine hnd _ (L.sub_mem hyL (hSL x.val_mem)) fun z hz ↦ ?_
      obtain ⟨a, ha, hza⟩ := hcomp z hz
      have h1 : Tendsto (fun n ↦ ⟪J.op (u n).val, z⟫_𝕜) atTop (𝓝 ⟪J.op y, z⟫_𝕜) :=
        ((J.op.continuous.inner continuous_const).tendsto y).comp huy
      have h2 : Tendsto (fun n ↦ ⟪u n, IntrinsicSpace.mk a ha⟫_𝕜) atTop
          (𝓝 ⟪x, IntrinsicSpace.mk (B := B') (hB := hherm) (hpos := hpos) a ha⟫_𝕜) :=
        ((continuous_id.inner continuous_const).tendsto x).comp hux
      have e : ∀ v : IntrinsicSpace B' S hherm hpos,
          ⟪v, IntrinsicSpace.mk a ha⟫_𝕜 = σ * ⟪J.op v.val, z⟫_𝕜 := fun v ↦ by
        rw [IntrinsicSpace.inner_eq, hB', IntrinsicSpace.val_mk, hza _ v.val_mem]
      simp_rw [e] at h2
      have h3 := h2.const_mul σ⁻¹
      simp only [← mul_assoc, inv_mul_cancel₀ hσ, one_mul] at h3
      rw [map_sub, inner_sub_left, tendsto_nhds_unique h1 h3, sub_self]
    exact sub_eq_zero.1 hyx
  let φ : StrongDual 𝕜 (IntrinsicSpace B' S hherm hpos) :=
    σ • (innerSL 𝕜 (J.op h)).comp ⟨ι, hι⟩
  refine ⟨((InnerProductSpace.toDual 𝕜 _).symm φ).val, IntrinsicSpace.val_mem _,
    fun x hx ↦ ?_⟩
  have := InnerProductSpace.toDual_symm_apply (x := IntrinsicSpace.mk x hx) (y := φ)
  rw [IntrinsicSpace.inner_eq, hB'] at this
  simp only [φ, ι, FunLike.coe_smul, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.coe_mk', Function.comp_apply,
    Pi.smul_apply, innerSL_apply_apply, IntrinsicSpace.val_mk, smul_eq_mul] at this
  exact mul_left_cancel₀ hσ this

/-- **A closed Krein subspace is ortho-complemented** ([Bog74, Theorem V.3.4], "if";
[AI89, Theorem 1.7.16], c ⇒ d ⇒ a). If `L` is closed and, with the restriction of
`[·, ·]`, a Krein space, then `L + L^[⊥] = H`. Uses the completeness of `H` (closed graph
theorem) and of the components `L₊`, `L₋` (Riesz); valid over `ℝ` and `ℂ`. -/
theorem isOrthoComplemented_of_kreinDecomposition [CompleteSpace H] (hL : IsClosed (L : Set H))
    (K : KreinDecomposition J.form L) : J.IsOrthoComplemented L := by
  have hnd : ∀ v ∈ L, (∀ z ∈ L, ⟪J.op v, z⟫_𝕜 = 0) → v = 0 :=
    fun v hv hz ↦ K.eq_zero_of_forall J.conj_form hv fun z hzL ↦ by simpa using hz z hzL
  have hpn : ∀ x ∈ K.pos, ∀ y ∈ K.neg, ⟪J.op x, y⟫_𝕜 = 0 := fun x hx y hy ↦ by
    simpa using K.orth x hx y hy
  have hnp : ∀ x ∈ K.neg, ∀ y ∈ K.pos, ⟪J.op x, y⟫_𝕜 = 0 := fun x hx y hy ↦ by
    rw [J.form_comm, hpn y hy x hx, map_zero]
  have hdec : ∀ z ∈ L, ∃ a ∈ K.pos, ∃ b ∈ K.neg, a + b = z := fun z hz ↦
    Submodule.mem_sup.1 (by rw [K.sup_eq]; exact hz)
  have hP := fun h : H ↦ J.exists_proj_of_component hL hnd K.pos_le J.form 1
    one_ne_zero (fun x y ↦ by simp) J.conj_form K.pos_def K.pos_complete (fun z hz ↦ by
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec z hz
      exact ⟨a, ha, fun x hx ↦ by rw [inner_add_right, hpn x hx b hb, add_zero]⟩) h
  have hN := fun h : H ↦ J.exists_proj_of_component hL hnd K.neg_le (-J.form) (-1)
    (neg_ne_zero.2 one_ne_zero) (fun x y ↦ by simp)
    (fun x y ↦ by simp only [LinearMap.neg_apply, map_neg, J.conj_form])
    (fun x hx hx0 ↦ by simpa using K.neg_def x hx hx0) K.neg_complete (fun z hz ↦ by
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec z hz
      exact ⟨b, hb, fun x hx ↦ by rw [inner_add_right, hnp x hx a ha, zero_add]⟩) h
  refine eq_top_iff.2 fun h _ ↦ ?_
  obtain ⟨wp, hwp, hp⟩ := hP h
  obtain ⟨wn, hwn, hn⟩ := hN h
  refine Submodule.mem_sup.2 ⟨wp + wn, L.add_mem (K.pos_le hwp) (K.neg_le hwn), h - (wp + wn),
    fun t ht ↦ ?_, by abel⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := hdec t ht
  rw [J.form_comm, map_sub, map_add, inner_sub_left, inner_add_left, inner_add_right,
    inner_add_right, inner_add_right, hp a ha, hn b hb, hpn wp hwp b hb, hnp wn hwn a ha]
  simp


/-- A `J`-orthogonal projector onto a nondegenerate subspace is unique: if `Q` and `Q'` are
projectors onto `L` with `[Q w, t] = [Q' w, t] = [w, t]` for `t ∈ L`, and `L` is
ortho-complemented, then `Q = Q'`. -/
theorem IsOrthoComplemented.eq_of_projector (hL : J.IsOrthoComplemented L) {Q Q' : H → H}
    (hQ : ∀ w, Q w ∈ L) (hQ' : ∀ w, Q' w ∈ L)
    (horth : ∀ w, ∀ t ∈ L, ⟪J.op (Q w), t⟫_𝕜 = ⟪J.op w, t⟫_𝕜)
    (horth' : ∀ w, ∀ t ∈ L, ⟪J.op (Q' w), t⟫_𝕜 = ⟪J.op w, t⟫_𝕜) : Q = Q' := by
  funext w
  refine sub_eq_zero.1 (hL.eq_zero (L.sub_mem (hQ w) (hQ' w)) fun t ht ↦ ?_)
  rw [J.form_comm, map_sub, inner_sub_left, horth w t ht, horth' w t ht, sub_self, map_zero]

/-- **Closed Krein subspaces have continuous `J`-orthogonal projectors** (any scalar field): if
`L` is closed and a Krein space for `[·, ·]`, there is a continuous projector `Q` onto `L` with
`[Q w, t] = [w, t]` for all `t ∈ L`. -/
theorem exists_projector_of_kreinDecomposition [CompleteSpace H] (hL : IsClosed (L : Set H))
    (K : KreinDecomposition J.form L) : ∃ Q : H →L[𝕜] H, (∀ w, Q w ∈ L) ∧ (∀ t ∈ L, Q t = t) ∧
      ∀ w, ∀ t ∈ L, ⟪J.op (Q w), t⟫_𝕜 = ⟪J.op w, t⟫_𝕜 :=
  isOrthoComplemented_iff_exists_projector.1 (isOrthoComplemented_of_kreinDecomposition hL K)

end FundamentalSymmetry

/-! ### Intrinsic completeness from norm bounds -/

/-- A closed subspace on which `re B(x, x)` is comparable to `‖x‖²` is intrinsically complete. -/
theorem intrinsicallyComplete_of_bounds {𝕜 : Type*} [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {B : H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜} {S : Submodule 𝕜 H} (hS : IsClosed (S : Set H)) {c C : ℝ}
    (hc : 0 < c) (hlow : ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ re (B x x))
    (hup : ∀ x, re (B x x) ≤ C * ‖x‖ ^ 2) : IntrinsicallyComplete B S := by
  intro u hu hcau
  have hC : CauchySeq u := by
    refine Metric.cauchySeq_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := hcau (c * ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have h1 := (hlow _ (S.sub_mem (hu m) (hu n))).trans_lt (hN m hm n hn)
    rw [dist_eq_norm]
    have h2 : ‖u m - u n‖ ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left h1 hc.le
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h2
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨x, hS.mem_of_tendsto hx (Eventually.of_forall hu), ?_⟩
  have h0 : Tendsto (fun n ↦ C * ‖u n - x‖ ^ 2) atTop (𝓝 0) := by
    simpa using ((tendsto_iff_norm_sub_tendsto_zero.1 hx).pow 2).const_mul C
  refine squeeze_zero' (Eventually.of_forall fun n ↦ ?_) (Eventually.of_forall fun n ↦ hup _) h0
  exact (mul_nonneg hc.le (sq_nonneg _)).trans
    (hlow _ (S.sub_mem (hu n) (hS.mem_of_tendsto hx (Eventually.of_forall hu))))

/-- **Intrinsic completeness forces a lower bound** (converse of
`intrinsicallyComplete_of_bounds`): if `S` is a closed subspace of the Hilbert space `H`, `B` is
Hermitian, positive definite on `S` and bounded above (`re B(x, x) ≤ C ‖x‖²`), and `S` is
intrinsically complete, then `re B(x, x) ≥ c ‖x‖²` on `S` for some `c > 0`. The identity of `S`
onto its intrinsic Hilbert space is continuous and bijective between complete spaces, so its
inverse is bounded (open mapping theorem). Uses the completeness of `H`. -/
theorem IntrinsicallyComplete.exists_lower_bound {𝕜 : Type*} [RCLike 𝕜] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {B : H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜} {S : Submodule 𝕜 H} (hS : IsClosed (S : Set H))
    (hB : ∀ x y, conj (B y x) = B x y) (hpos : ∀ x ∈ S, x ≠ 0 → 0 < re (B x x)) {C : ℝ}
    (hup : ∀ x, re (B x x) ≤ C * ‖x‖ ^ 2) (hc : IntrinsicallyComplete B S) :
    ∃ c > 0, ∀ x ∈ S, c * ‖x‖ ^ 2 ≤ re (B x x) := by
  have : CompleteSpace S := hS.completeSpace_coe
  have := IntrinsicSpace.completeSpace (hB := hB) (hpos := hpos) hc
  have hnn : ∀ x ∈ S, 0 ≤ re (B x x) := fun x hx ↦ by
    by_cases h : x = 0
    · simp [h]
    · exact (hpos x hx h).le
  let ι : S →ₗ[𝕜] IntrinsicSpace B S hB hpos :=
    { toFun := fun x ↦ IntrinsicSpace.mk x x.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hnorm : ∀ x : S, ‖ι x‖ = √(re (B x x)) := fun x ↦ IntrinsicSpace.norm_eq _
  have hbd : ∀ x : S, ‖ι x‖ ≤ √C * ‖x‖ := fun x ↦ by
    rw [hnorm, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul' _ (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hup x)
  let ιc : S →L[𝕜] IntrinsicSpace B S hB hpos := ι.mkContinuous √C hbd
  have hbij : Function.Bijective ιc :=
    ⟨fun x y h ↦ Subtype.ext (congrArg IntrinsicSpace.val h),
      fun z ↦ ⟨⟨z.val, z.val_mem⟩, rfl⟩⟩
  let e := ContinuousLinearEquiv.ofBijective ιc (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)
  set K := ‖(e.symm : IntrinsicSpace B S hB hpos →L[𝕜] S)‖
  refine ⟨1 / (K ^ 2 + 1), by positivity, fun x hx ↦ ?_⟩
  have h1 : ‖(⟨x, hx⟩ : S)‖ ≤ K * ‖ι ⟨x, hx⟩‖ := by
    have h' : e.symm (ι ⟨x, hx⟩) = ⟨x, hx⟩ := e.symm_apply_apply ⟨x, hx⟩
    have := (e.symm : IntrinsicSpace B S hB hpos →L[𝕜] S).le_opNorm (ι ⟨x, hx⟩)
    rwa [ContinuousLinearEquiv.coe_coe, h'] at this
  have h2 : ‖ι ⟨x, hx⟩‖ ^ 2 = re (B x x) := by
    rw [hnorm, Real.sq_sqrt (hnn x hx)]
  have h3 : ‖x‖ ^ 2 ≤ K ^ 2 * re (B x x) := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, h2] at this
    exact this
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [hnn x hx]

namespace FundamentalSymmetry



/-! ### Ortho-complemented subspaces are Krein spaces -/

section Krein

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] {J : FundamentalSymmetry 𝕜 H} {L : Submodule 𝕜 H}

/-- **An ortho-complemented subspace is a Krein space** ([Bog74, Theorem V.3.4], "only if";
[AI89, Theorem 1.7.16], a ⇒ b ⇒ c), for real and complex Hilbert spaces. The Gram
operator `G_L` is bijective and self-adjoint; its spectral projections onto the positive and
negative half-lines (`exists_spectral_projection`; over `ℝ` through the complexification) give
a fundamental decomposition `L = L₊ ⊕ L₋` on which `±[x, x] ≥ c ‖x‖²`, `c > 0` the distance from
`0` to the spectrum. -/
theorem IsOrthoComplemented.isKreinSpace (hL : J.IsOrthoComplemented L) :
    IsKreinSpace J.form L := by
  have hcl := hL.isClosed
  have : CompleteSpace L := hcl.completeSpace_coe
  set G := J.gram L with hGdef
  have hGx : ∀ x y : L, ⟪G x, y⟫_𝕜 = ⟪J.op x, (y : H)⟫_𝕜 := inner_gram
  have hGsa : ∀ x y : L, ⟪G x, y⟫_𝕜 = ⟪x, G y⟫_𝕜 := fun x y ↦ by
    rw [hGx, ← inner_conj_symm x, hGx, ← J.form_comm]
  have hb := isOrthoComplemented_iff_bijective_gram.1 hL
  obtain ⟨P, c, hc, hPP, hPsa, hGP, hpos_bd, hneg_bd, -⟩ := exists_spectral_projection hGsa hb
  replace hpos_bd : ∀ x : L, P x = x → c * ‖x‖ ^ 2 ≤ re ⟪J.op x, (x : H)⟫_𝕜 :=
    fun x hx ↦ by simpa [hGx] using hpos_bd x hx
  replace hneg_bd : ∀ x : L, P x = 0 → c * ‖x‖ ^ 2 ≤ -re ⟪J.op x, (x : H)⟫_𝕜 :=
    fun x hx ↦ by simpa [hGx] using hneg_bd x hx
  -- the components
  let Kp : Submodule 𝕜 L := LinearMap.ker (((1 : L →L[𝕜] L) - P : L →L[𝕜] L) : L →ₗ[𝕜] L)
  let Kn : Submodule 𝕜 L := LinearMap.ker (P : L →ₗ[𝕜] L)
  have hKp : ∀ x, x ∈ Kp ↔ P x = x := fun x ↦ by
    simp only [Kp, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self]
    exact sub_eq_zero.trans eq_comm
  have hKn : ∀ x, x ∈ Kn ↔ P x = 0 := fun x ↦ Iff.rfl
  have hclosed : ∀ K : Submodule 𝕜 L, IsClosed (K : Set L) →
      IsClosed (K.map L.subtype : Set H) := fun K hK ↦ by
    rw [Submodule.map_coe]
    exact hcl.isClosedMap_subtype_val _ hK
  have hup : ∀ v : H, ‖J.form v v‖ ≤ ‖J.op‖ * ‖v‖ ^ 2 := J.norm_form_le
  refine ⟨{
    pos := Kp.map L.subtype
    neg := Kn.map L.subtype
    sup_eq := ?_
    disjoint := ?_
    orth := ?_
    pos_def := ?_
    neg_def := ?_
    pos_complete := ?_
    neg_complete := ?_ }⟩
  · refine le_antisymm (sup_le (Submodule.map_subtype_le _ _) (Submodule.map_subtype_le _ _))
      fun h hh ↦ Submodule.mem_sup.2 ⟨P ⟨h, hh⟩, ⟨P ⟨h, hh⟩, (hKp _).2 (hPP _), rfl⟩,
        (⟨h, hh⟩ - P ⟨h, hh⟩ : L), ⟨(⟨h, hh⟩ - P ⟨h, hh⟩ : L),
          (hKn _).2 (by rw [map_sub, hPP, sub_self]), rfl⟩, ?_⟩
    simp
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxy' : y = x := Subtype.ext hxy
    subst hxy'
    rw [(hKp _).1 hx |>.symm, (hKn _).1 hy]
    rfl
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [Submodule.subtype_apply, form_apply]
    rw [← hGx, ← (hKp _).1 hx, hGP, hPsa, (hKn _).1 hy, inner_zero_right]
  · rintro _ ⟨x, hx, rfl⟩ hx0
    have hx0' : x ≠ 0 := fun h ↦ hx0 (by simp [h])
    have := hpos_bd x ((hKp _).1 hx)
    have : 0 < c * ‖x‖ ^ 2 := by positivity
    simp only [Submodule.subtype_apply, form_apply]
    linarith
  · rintro _ ⟨x, hx, rfl⟩ hx0
    have hx0' : x ≠ 0 := fun h ↦ hx0 (by simp [h])
    have := hneg_bd x ((hKn _).1 hx)
    have : 0 < c * ‖x‖ ^ 2 := by positivity
    simp only [Submodule.subtype_apply, form_apply]
    linarith
  · refine intrinsicallyComplete_of_bounds (hclosed _ (ContinuousLinearMap.isClosed_ker _)) hc
      ?_ fun v ↦ (re_le_norm _).trans (hup v)
    rintro _ ⟨x, hx, rfl⟩
    simpa using hpos_bd x ((hKp _).1 hx)
  · refine intrinsicallyComplete_of_bounds (C := ‖J.op‖)
      (hclosed _ (ContinuousLinearMap.isClosed_ker _)) hc ?_ fun v ↦ ?_
    · rintro _ ⟨x, hx, rfl⟩
      simpa using hneg_bd x ((hKn _).1 hx)
    · have := hup v
      simp only [LinearMap.neg_apply, map_neg] at this ⊢
      exact (neg_le_abs _).trans ((abs_re_le_norm _).trans this)

/-- **[Bog74, Theorem V.3.4].** A subspace `L` of the Krein space `(H, [·, ·])` (`H` a real or
complex Hilbert space, `[x, y] = ⟪J x, y⟫`) is ortho-complemented, `L + L^[⊥] = H`, if and only if
`L` is closed and, with the restriction of `[·, ·]`, a Krein space. -/
theorem isOrthoComplemented_iff_isClosed_and_isKreinSpace :
    J.IsOrthoComplemented L ↔ IsClosed (L : Set H) ∧ IsKreinSpace J.form L :=
  ⟨fun hL ↦ ⟨hL.isClosed, hL.isKreinSpace⟩,
    fun ⟨hcl, ⟨K⟩⟩ ↦ isOrthoComplemented_of_kreinDecomposition hcl K⟩

/-- The whole space is a Krein space for `[·, ·]` ([Bog74, Corollary V.1.2]). -/
theorem isKreinSpace_top : IsKreinSpace J.form (⊤ : Submodule 𝕜 H) :=
  IsOrthoComplemented.isKreinSpace (J := J) (top_sup_eq _)

/-! ### Positive definite subspaces ([Bog74, Example V.3.3]) -/

/-- The Krein decomposition `L = L ⊕ 0` of a positive definite, intrinsically complete
subspace. -/
def kreinDecompositionOfPosDef (hpos : ∀ x ∈ L, x ≠ 0 → 0 < re ⟪J.op x, x⟫_𝕜)
    (hc : IntrinsicallyComplete J.form L) : KreinDecomposition J.form L where
  pos := L
  neg := ⊥
  sup_eq := sup_bot_eq L
  disjoint := disjoint_bot_right
  orth x _ y hy := by rw [(Submodule.mem_bot 𝕜).1 hy, map_zero]
  pos_def x hx h0 := hpos x hx h0
  neg_def x hx h0 := absurd ((Submodule.mem_bot 𝕜).1 hx) h0
  pos_complete := hc
  neg_complete u hu _ := by
    have h0 : ∀ n, u n = 0 := fun n ↦ (Submodule.mem_bot 𝕜).1 (hu n)
    exact ⟨0, Submodule.zero_mem _, by simp [h0]⟩

omit [CompleteSpace H] in
/-- In a Krein decomposition of a positive definite subspace, `L₊ = L`. -/
theorem _root_.LocallyConvex.Analysis.KreinDecomposition.pos_eq_of_posDef
    (hpos : ∀ x ∈ L, x ≠ 0 → 0 < re ⟪J.op x, x⟫_𝕜)
    (K : KreinDecomposition J.form L) : K.pos = L := by
  have hneg : K.neg = ⊥ := (Submodule.eq_bot_iff _).2 fun x hx ↦ by
    by_contra h0
    have h1 := K.neg_def x hx h0
    have h2 := hpos x (K.neg_le hx) h0
    rw [form_apply] at h1
    linarith
  calc K.pos = K.pos ⊔ K.neg := by rw [hneg, sup_bot_eq]
    _ = L := K.sup_eq

/-- **Positive definite subspaces and intrinsic completeness** (from [Bog74, Theorem V.3.4]): a
positive definite subspace `L` of the Krein space `H` is ortho-complemented if and only if it is
closed and intrinsically complete. [Bog74, Example V.3.3] is a closed positive definite subspace
which is not intrinsically complete. Uses the completeness of `H`; over `ℝ` and `ℂ`. -/
theorem isOrthoComplemented_iff_intrinsicallyComplete_of_posDef
    (hpos : ∀ x ∈ L, x ≠ 0 → 0 < re ⟪J.op x, x⟫_𝕜) :
    J.IsOrthoComplemented L ↔ IsClosed (L : Set H) ∧ IntrinsicallyComplete J.form L := by
  refine ⟨fun hL ↦ ⟨hL.isClosed, ?_⟩, fun ⟨hcl, hc⟩ ↦
    isOrthoComplemented_of_kreinDecomposition hcl (kreinDecompositionOfPosDef hpos hc)⟩
  obtain ⟨K⟩ := hL.isKreinSpace
  rw [← K.pos_eq_of_posDef hpos]
  exact K.pos_complete

/-- **Positive definite subspaces** (from [Bog74, Theorem V.3.4]): a positive definite subspace
`L` of the Krein space `H` is ortho-complemented if and only if it is closed and **uniformly
positive**, `[x, x] ≥ c ‖x‖²` on `L` for some `c > 0`. Uses the completeness of `H` (open mapping
theorem in `exists_lower_bound`); over `ℝ` and `ℂ`. -/
theorem isOrthoComplemented_iff_uniformlyPositive_of_posDef
    (hpos : ∀ x ∈ L, x ≠ 0 → 0 < re ⟪J.op x, x⟫_𝕜) :
    J.IsOrthoComplemented L ↔
      IsClosed (L : Set H) ∧ ∃ c > 0, ∀ x ∈ L, c * ‖x‖ ^ 2 ≤ re ⟪J.op x, x⟫_𝕜 := by
  rw [isOrthoComplemented_iff_intrinsicallyComplete_of_posDef hpos]
  have hup : ∀ x, re (J.form x x) ≤ ‖J.op‖ * ‖x‖ ^ 2 :=
    fun x ↦ (re_le_norm _).trans (J.norm_form_le x)
  refine ⟨fun ⟨hcl, hc⟩ ↦ ⟨hcl, ?_⟩, fun ⟨hcl, c, hc, hlow⟩ ↦
    ⟨hcl, intrinsicallyComplete_of_bounds hcl hc hlow hup⟩⟩
  exact hc.exists_lower_bound hcl J.conj_form hpos hup

/-- A closed, positive definite subspace which is not uniformly positive is neither
intrinsically complete, nor a Krein space, nor ortho-complemented, although it is nondegenerate
and decomposable (`L = L ⊕ 0`). [Bog74, Example V.3.3], is of this kind
(`LocallyConvex.Analysis.Counterexamples.BognarKrein`). -/
theorem not_isOrthoComplemented_of_posDef (hcl : IsClosed (L : Set H))
    (hpos : ∀ x ∈ L, x ≠ 0 → 0 < re ⟪J.op x, x⟫_𝕜)
    (hnot : ∀ c > 0, ∃ x ∈ L, re ⟪J.op x, x⟫_𝕜 < c * ‖x‖ ^ 2) :
    ¬ IntrinsicallyComplete J.form L ∧ ¬ IsKreinSpace J.form L ∧ ¬ J.IsOrthoComplemented L := by
  have hno : ¬ J.IsOrthoComplemented L := fun hL ↦ by
    obtain ⟨-, c, hc, hlow⟩ := (isOrthoComplemented_iff_uniformlyPositive_of_posDef hpos).1 hL
    obtain ⟨x, hx, hlt⟩ := hnot c hc
    exact (hlow x hx).not_gt hlt
  refine ⟨fun hc ↦ hno ((isOrthoComplemented_iff_intrinsicallyComplete_of_posDef hpos).2
    ⟨hcl, hc⟩), fun ⟨K⟩ ↦ hno (isOrthoComplemented_of_kreinDecomposition hcl K), hno⟩

/-! ### Fundamental decompositions of an ortho-complemented subspace ([Bog74, Theorem V.3.5]) -/

/-- In a Krein space, the positive component of **every** fundamental decomposition
`H = H₊ ⊕ H₋` of the whole space is uniformly positive: `H₊` is ortho-complemented (`H₋` is a
complement inside `H₊^[⊥]`), hence closed and, being positive definite, uniformly positive. -/
theorem exists_pos_bound_of_top (K : AlgFundamentalDecomposition J.form ⊤) :
    ∃ c > 0, ∀ x ∈ K.pos, c * ‖x‖ ^ 2 ≤ re ⟪J.op x, x⟫_𝕜 := by
  have hortho : J.IsOrthoComplemented K.pos := by
    refine eq_top_iff.2 fun h _ ↦ ?_
    have hh : h ∈ K.pos ⊔ K.neg := by rw [K.sup_eq]; exact Submodule.mem_top
    have hle : K.neg ≤ J.orth K.pos := fun y hy x hx ↦ K.orth x hx y hy
    exact sup_le_sup_left hle _ hh
  exact ((isOrthoComplemented_iff_uniformlyPositive_of_posDef
    (fun x hx h0 ↦ K.pos_def x hx h0)).1 hortho).2

/-- In a Krein space, the negative component of every fundamental decomposition of the whole
space is uniformly negative. -/
theorem exists_neg_bound_of_top (K : AlgFundamentalDecomposition J.form ⊤) :
    ∃ c > 0, ∀ x ∈ K.neg, c * ‖x‖ ^ 2 ≤ -re ⟪J.op x, x⟫_𝕜 := by
  have hortho : J.neg.IsOrthoComplemented K.neg := by
    rw [isOrthoComplemented_neg]
    refine eq_top_iff.2 fun h _ ↦ ?_
    have hh : h ∈ K.neg ⊔ K.pos := by rw [sup_comm, K.sup_eq]; exact Submodule.mem_top
    have hle : K.pos ≤ J.orth K.neg := fun y hy x hx ↦ by
      rw [J.form_comm, show ⟪J.op y, x⟫_𝕜 = J.form y x from rfl, K.orth y hy x hx, map_zero]
    exact sup_le_sup_left hle _ hh
  obtain ⟨-, c, hc, hlow⟩ := (isOrthoComplemented_iff_uniformlyPositive_of_posDef (J := J.neg)
    (fun x hx h0 ↦ by simpa using K.neg_def x hx h0)).1 hortho
  exact ⟨c, hc, fun x hx ↦ by simpa using hlow x hx⟩

/-- **[Bog74, Theorem V.3.5], "only if"**: if `L` is ortho-complemented, every fundamental
decomposition `L = L₊ ⊕ L₋` extends to a fundamental decomposition `H = H₊ ⊕ H₋` with
`L₊ ⊆ H₊` and `L₋ ⊆ H₋`. As in Bognár, `H₊ = L₊ + M₊` and `H₋ = L₋ + M₋` for a fundamental
decomposition `L^[⊥] = M₊ ⊕ M₋`; here `M₊`, `M₋` come from Theorem V.3.4 applied to the
ortho-complemented `L^[⊥]` (Bognár uses his Corollary V.4.2, Theorem IV.5.2 and Lemma I.14.1).
Uses the
completeness of `H`. -/
theorem IsOrthoComplemented.exists_algFundamentalDecomposition_top
    (hL : J.IsOrthoComplemented L) (K : AlgFundamentalDecomposition J.form L) :
    ∃ K' : AlgFundamentalDecomposition J.form ⊤, K.pos ≤ K'.pos ∧ K.neg ≤ K'.neg := by
  have hL' : J.IsOrthoComplemented (J.orth L) := by
    refine eq_top_iff.2 fun h _ ↦ ?_
    have hh : h ∈ J.orth L ⊔ L := by rw [sup_comm]; exact hL ▸ Submodule.mem_top
    have hle : L ≤ J.orth (J.orth L) := fun x hx y hy ↦ J.inner_op_eq_zero_of_mem_orth hx hy
    exact sup_le_sup_left hle _ hh
  obtain ⟨M⟩ := hL'.isKreinSpace
  have hLM : ∀ x ∈ L, ∀ y ∈ J.orth L, J.form x y = 0 := fun x hx y hy ↦ hy x hx
  have hML : ∀ x ∈ J.orth L, ∀ y ∈ L, J.form x y = 0 :=
    fun x hx y hy ↦ J.inner_op_eq_zero_of_mem_orth hy hx
  have hpos : ∀ x ∈ K.pos ⊔ M.pos, x ≠ 0 → 0 < re (J.form x x) :=
    posDef_sup K.pos_def M.pos_def (fun x hx y hy ↦ hLM x (K.pos_le hx) y (M.pos_le hy))
      (fun x hx y hy ↦ hML x (M.pos_le hx) y (K.pos_le hy))
  have hneg' : ∀ x ∈ K.neg ⊔ M.neg, x ≠ 0 → 0 < re ((-J.form) x x) :=
    posDef_sup (fun x hx h0 ↦ by simpa using K.neg_def x hx h0)
      (fun x hx h0 ↦ by simpa using M.neg_def x hx h0)
      (fun x hx y hy ↦ by simp [hLM x (K.neg_le hx) y (M.neg_le hy)])
      (fun x hx y hy ↦ by simp [hML x (M.neg_le hx) y (K.neg_le hy)])
  have hneg : ∀ x ∈ K.neg ⊔ M.neg, x ≠ 0 → re (J.form x x) < 0 := fun x hx h0 ↦ by
    simpa using hneg' x hx h0
  refine ⟨{
    pos := K.pos ⊔ M.pos
    neg := K.neg ⊔ M.neg
    sup_eq := ?_
    disjoint := ?_
    orth := ?_
    pos_def := hpos
    neg_def := hneg }, le_sup_left, le_sup_left⟩
  · rw [sup_sup_sup_comm, K.sup_eq, M.sup_eq]
    exact hL
  · rw [Submodule.disjoint_def]
    intro x h1 h2
    by_contra h0
    linarith [hpos x h1 h0, hneg x h2 h0]
  · intro x hx y hy
    obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨b, hb, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
    simp only [map_add, LinearMap.add_apply, K.orth a ha b hb, M.orth m hm n hn,
      hLM a (K.pos_le ha) n (M.neg_le hn), hML m (M.pos_le hm) b (K.neg_le hb), add_zero]

/-- **[Bog74, Theorem V.3.5], "if"**: if `L` is closed and some fundamental decomposition
`L = L₊ ⊕ L₋` satisfies `L₊ ⊆ H₊`, `L₋ ⊆ H₋` for a fundamental decomposition `H = H₊ ⊕ H₋`,
then `L` is ortho-complemented. `L₊ = L ∩ L₋^[⊥]` is closed and, inside the uniformly positive
`H₊`, uniformly positive, hence ortho-complemented; likewise `L₋`; and the orthogonal sum of
ortho-complemented subspaces is ortho-complemented (Lemma I.9.2). Bognár instead
ortho-complements `L₊` inside the Hilbert space `(H₊, [·, ·])`. Uses the completeness of `H`. -/
theorem isOrthoComplemented_of_algFundamentalDecomposition (hL : IsClosed (L : Set H))
    (K : AlgFundamentalDecomposition J.form L) (K' : AlgFundamentalDecomposition J.form ⊤)
    (hpos : K.pos ≤ K'.pos) (hneg : K.neg ≤ K'.neg) : J.IsOrthoComplemented L := by
  obtain ⟨c, hc, hbd⟩ := exists_pos_bound_of_top K'
  obtain ⟨c', hc', hbd'⟩ := exists_neg_bound_of_top K'
  have h1 : J.IsOrthoComplemented K.pos :=
    (isOrthoComplemented_iff_uniformlyPositive_of_posDef (fun x hx h0 ↦ K.pos_def x hx h0)).2
      ⟨K.isClosed_pos hL, c, hc, fun x hx ↦ hbd x (hpos hx)⟩
  have h2 : J.IsOrthoComplemented K.neg := by
    rw [← isOrthoComplemented_neg]
    exact (isOrthoComplemented_iff_uniformlyPositive_of_posDef (J := J.neg)
      (fun x hx h0 ↦ by simpa using K.neg_def x hx h0)).2
      ⟨K.isClosed_neg hL, c', hc', fun x hx ↦ by simpa using hbd' x (hneg hx)⟩
  rw [← K.sup_eq]
  exact h1.sup h2 fun x hx y hy ↦ K.orth x hx y hy

/-- **[Bog74, Theorem V.3.5].** A subspace `L` of the Krein space `(H, [·, ·])` is
ortho-complemented if and only if it is closed, admits a fundamental decomposition, and every
fundamental decomposition `L = L₊ ⊕ L₋` extends to one of `H`: `L₊ ⊆ H₊`, `L₋ ⊆ H₋`.

Bognár states the conditions as: `L` closed, nondegenerate, and the extension property for every
fundamental decomposition of `L` (`isOrthoComplemented_iff_isClosed_nondegenerate`).
Nondegeneracy follows from the existence of a fundamental decomposition
(`AlgFundamentalDecomposition.eq_zero_of_forall`); conversely the existence is automatic for
closed nondegenerate subspaces by Theorem V.3.1 (`exists_algFundamentalDecomposition_of_isClosed`).
Uses the completeness of `H`; over `ℝ` and `ℂ`. -/
theorem isOrthoComplemented_iff_algFundamentalDecomposition :
    J.IsOrthoComplemented L ↔ IsClosed (L : Set H) ∧
      Nonempty (AlgFundamentalDecomposition J.form L) ∧
      ∀ K : AlgFundamentalDecomposition J.form L,
        ∃ K' : AlgFundamentalDecomposition J.form ⊤, K.pos ≤ K'.pos ∧ K.neg ≤ K'.neg := by
  refine ⟨fun hL ↦ ⟨hL.isClosed, ?_, hL.exists_algFundamentalDecomposition_top⟩,
    fun ⟨hcl, ⟨K⟩, h⟩ ↦ ?_⟩
  · obtain ⟨K⟩ := hL.isKreinSpace
    exact ⟨K.toAlgFundamentalDecomposition⟩
  · obtain ⟨K', h1, h2⟩ := h K
    exact isOrthoComplemented_of_algFundamentalDecomposition hcl K K' h1 h2

/-- **[Bog74, Theorem V.3.1]**: a closed subspace `L` of a Krein space admits a fundamental
decomposition `L = L⁰ ∔ L₊ ∔ L₋` (§I.11, (11.1): a `[·, ·]`-orthogonal direct sum of a neutral,
a positive definite and a negative definite subspace; `L⁰` is then the isotropic part
`L ∩ L^[⊥]`) whose three components, as well as the direct sum of any two of them, are closed.
Over `ℝ` and `ℂ`.

Bognár derives it from his Theorem IV.5.2, whose proof takes the spectral subspaces of the Gram
operator `G_L` (`⟪G_L x, y⟫ = [x, y]` on `L`) for `{0}`, `(0, ∞)` and `(-∞, 0)` via its spectral
function. Here the same subspaces are `ker G_L`, `(ker G_L⁺)^⊥` and `(ker G_L⁻)^⊥`, where
`G_L^±` are the positive and negative parts of `G_L` from the continuous functional calculus
(`exists_sign_decomposition`); no spectral measure is needed. -/
theorem exists_fundamentalDecomposition_of_isClosed (hcl : IsClosed (L : Set H)) :
    ∃ L₀ Lp Lm : Submodule 𝕜 H,
      (∀ v, v ∈ L₀ ↔ v ∈ L ∧ ∀ z ∈ L, J.form v z = 0) ∧
      IsClosed (L₀ : Set H) ∧ IsClosed (Lp : Set H) ∧ IsClosed (Lm : Set H) ∧
      IsClosed ((L₀ ⊔ Lp : Submodule 𝕜 H) : Set H) ∧
      IsClosed ((L₀ ⊔ Lm : Submodule 𝕜 H) : Set H) ∧
      IsClosed ((Lp ⊔ Lm : Submodule 𝕜 H) : Set H) ∧
      L₀ ⊔ Lp ⊔ Lm = L ∧ Disjoint Lp Lm ∧ Disjoint L₀ (Lp ⊔ Lm) ∧
      (∀ x ∈ Lp, x ≠ 0 → 0 < re (J.form x x)) ∧ (∀ x ∈ Lm, x ≠ 0 → re (J.form x x) < 0) ∧
      ∀ x ∈ Lp, ∀ y ∈ Lm, J.form x y = 0 := by
  have : CompleteSpace L := hcl.completeSpace_coe
  set G := J.gram L with hGdef
  have hGx : ∀ x y : L, ⟪G x, y⟫_𝕜 = ⟪J.op x, (y : H)⟫_𝕜 := inner_gram
  have hGsa : ∀ x y : L, ⟪G x, y⟫_𝕜 = ⟪x, G y⟫_𝕜 := fun x y ↦ by
    rw [hGx, ← inner_conj_symm x, hGx, ← J.form_comm]
  obtain ⟨N₀, Np, Nm, h0, hc0, hcp, hcm, hc0p, hc0m, hcpm, htop, hdpm, hd0, hpos, hneg, horth⟩ :=
    exists_sign_decomposition hGsa
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have hclosed : ∀ N : Submodule 𝕜 L, IsClosed (N : Set L) →
      IsClosed ((N.map L.subtype : Submodule 𝕜 H) : Set H) := fun N hN ↦ by
    rw [Submodule.map_coe]
    exact hemb.isClosedMap _ hN
  have hinj : Function.Injective L.subtype := Subtype.val_injective
  have hdisj : ∀ N N' : Submodule 𝕜 L, Disjoint N N' →
      Disjoint (N.map L.subtype) (N'.map L.subtype) := fun N N' h ↦ by
    rw [disjoint_iff, ← Submodule.map_inf _ hinj, disjoint_iff.1 h, Submodule.map_bot]
  have hform : ∀ x y : L, J.form x y = ⟪G x, y⟫_𝕜 := fun x y ↦ by rw [hGx]; rfl
  refine ⟨N₀.map L.subtype, Np.map L.subtype, Nm.map L.subtype, fun v ↦ ⟨?_, ?_⟩,
    hclosed _ hc0, hclosed _ hcp, hclosed _ hcm, ?_, ?_, ?_, ?_, hdisj _ _ hdpm, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun z hz ↦ ?_⟩
    rw [Submodule.subtype_apply, show z = ((⟨z, hz⟩ : L) : H) from rfl, hform, (h0 x).1 hx,
      inner_zero_left]
  · rintro ⟨hv, hvz⟩
    refine ⟨⟨v, hv⟩, (h0 _).2 ?_, rfl⟩
    rw [← inner_self_eq_zero (𝕜 := 𝕜), ← hform]
    exact hvz _ (G ⟨v, hv⟩).2
  · rw [← Submodule.map_sup]; exact hclosed _ hc0p
  · rw [← Submodule.map_sup]; exact hclosed _ hc0m
  · rw [← Submodule.map_sup]; exact hclosed _ hcpm
  · rw [← Submodule.map_sup, ← Submodule.map_sup, htop, Submodule.map_subtype_top]
  · rw [← Submodule.map_sup]; exact hdisj _ _ hd0
  · rintro _ ⟨x, hx, rfl⟩ hx0
    rw [Submodule.subtype_apply, hform, Submodule.coe_inner]
    exact hpos x hx fun h ↦ hx0 (by rw [h]; rfl)
  · rintro _ ⟨x, hx, rfl⟩ hx0
    rw [Submodule.subtype_apply, hform, Submodule.coe_inner]
    exact hneg x hx fun h ↦ hx0 (by rw [h]; rfl)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply, hform, horth x hx y hy]

/-- **[Bog74, Theorem V.3.1], nondegenerate case**: a closed nondegenerate subspace of a Krein
space has a fundamental decomposition `L = L₊ ⊕ L₋` with closed components. -/
theorem exists_algFundamentalDecomposition_of_isClosed (hcl : IsClosed (L : Set H))
    (hnd : ∀ v ∈ L, (∀ z ∈ L, J.form v z = 0) → v = 0) :
    ∃ K : AlgFundamentalDecomposition J.form L,
      IsClosed (K.pos : Set H) ∧ IsClosed (K.neg : Set H) := by
  obtain ⟨L₀, Lp, Lm, h0, -, hcp, hcm, -, -, -, hsum, hdpm, -, hpos, hneg, horth⟩ :=
    exists_fundamentalDecomposition_of_isClosed (J := J) hcl
  have hL₀ : L₀ = ⊥ := (Submodule.eq_bot_iff _).2 fun v hv ↦
    hnd v ((h0 v).1 hv).1 ((h0 v).1 hv).2
  rw [hL₀, bot_sup_eq] at hsum
  exact ⟨⟨Lp, Lm, hsum, hdpm, horth, hpos, hneg⟩, hcp, hcm⟩

/-- **[Bog74, Theorem V.3.5]**, as stated there: a subspace `L` of the Krein space `(H, [·, ·])`
is ortho-complemented if and only if it is closed, nondegenerate, and every fundamental
decomposition `L = L₊ ⊕ L₋` extends to one of `H`: `L₊ ⊆ H₊`, `L₋ ⊆ H₋`. "If" takes a
fundamental decomposition of `L` from Theorem V.3.1
(`exists_algFundamentalDecomposition_of_isClosed`) and applies
`isOrthoComplemented_of_algFundamentalDecomposition`. Uses the completeness of `H`; over `ℝ`
and `ℂ`. -/
theorem isOrthoComplemented_iff_isClosed_nondegenerate :
    J.IsOrthoComplemented L ↔ IsClosed (L : Set H) ∧
      (∀ v ∈ L, (∀ z ∈ L, J.form v z = 0) → v = 0) ∧
      ∀ K : AlgFundamentalDecomposition J.form L,
        ∃ K' : AlgFundamentalDecomposition J.form ⊤, K.pos ≤ K'.pos ∧ K.neg ≤ K'.neg := by
  refine ⟨fun hL ↦ ⟨hL.isClosed, fun v hv h ↦ hL.eq_zero hv
    (J.mem_orth.2 fun x hx ↦ by rw [J.form_comm, ← J.form_apply, h x hx, map_zero]),
    hL.exists_algFundamentalDecomposition_top⟩, fun ⟨hcl, hnd, h⟩ ↦ ?_⟩
  obtain ⟨K, -, -⟩ := exists_algFundamentalDecomposition_of_isClosed hcl hnd
  obtain ⟨K', h1, h2⟩ := h K
  exact isOrthoComplemented_of_algFundamentalDecomposition hcl K K' h1 h2

end Krein

end FundamentalSymmetry

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Symmetric multilinear maps, polarization and continuous homogeneous polynomials

This file develops the algebra of homogeneous polynomials between topological vector spaces, as a
foundation for real and complex analytic maps between locally convex spaces in the sense of
Bochnak–Siciak (*Polynomials and multilinear mappings in topological vector-spaces*, Studia Math.
39 (1971) 59–76, and *Analytic functions in topological vector-spaces*, Studia Math. 39 (1971)
77–112) and Glöckner (*Infinite-dimensional Lie groups without completeness restrictions*,
Banach Center Publ. 55 (2002)).

## Main definitions

* `MultilinearMap.diag A x = A (x, …, x)`: the restriction of a multilinear map to the diagonal.
  The homogeneous polynomials of degree `k` are exactly these maps for `ι = Fin k`.
* `MultilinearMap.IsSymm A`: `A` is invariant under permutations of its arguments.
* `MultilinearMap.symmetrize A = (1 / k!) ∑_σ A ∘ σ`, and its continuous counterpart
  `ContinuousMultilinearMap.symmetrize`.
* `LocallyConvex.Analysis.IsContHomPoly 𝕜 k p`: `p : E → F` is the diagonal of a *continuous*
  `k`-linear map.

## Main results

* `MultilinearMap.polarization`: the Mazur–Orlicz polarization formula in the `±1` form
  ([BS71a, Theorem A, p. 60]): for a symmetric `k`-linear `A`,
  `∑_{ε ∈ {±1}^k} ε₁ ⋯ ε_k • A.diag (ε₁ x₁ + ⋯ + ε_k x_k) = 2^k k! • A (x₁, …, x_k)`.
  It holds over any commutative ring; dividing by `2^k k!` (`MultilinearMap.eq_polarization`)
  needs characteristic zero.
* `MultilinearMap.eq_of_diag_eq`: a symmetric multilinear map is determined by its diagonal;
  `MultilinearMap.diag_eq_diag_iff`: two multilinear maps have the same diagonal iff they have
  the same symmetrization.
* `MultilinearMap.continuous_of_isSymm_of_continuous_diag` and
  `LocallyConvex.Analysis.isContHomPoly_iff_continuous`: an algebraic homogeneous polynomial is
  continuous iff its symmetric multilinear map is (the remark after Theorem A in
  [BS71a, p. 61]).
  Hence the continuous homogeneous polynomials are exactly the continuous maps that are
  algebraic homogeneous polynomials.
* Closure properties of `IsContHomPoly`; degree `0` gives the constants
  (`isContHomPoly_zero_iff`) and degree `1` the continuous linear maps
  (`isContHomPoly_one_iff`).
* `LocallyConvex.Analysis.homogeneous_components_eq_zero`: if `∑_{n ≤ N} p_n (t x) = 0` for
  `N + 1` values of `t`, with each `p_n` homogeneous of degree `n`, then every `p_n x` vanishes
  (uniqueness of finite homogeneous expansions, by a Vandermonde argument).

## Assumptions

No completeness is assumed anywhere in this file. Bochnak–Siciak work with a sequentially
complete locally convex target throughout their analytic theory (part II, p. 78), and Glöckner
removes this restriction; the algebra developed here needs neither completeness nor local
convexity, nor the Hausdorff property. The topological statements only use that addition is
continuous on the source and the target (`IsTopologicalAddGroup`) and that multiplication by
each fixed scalar is continuous on the target (`ContinuousConstSMul 𝕜 F`); no topology on the
field `𝕜` is required. The field `𝕜` is arbitrary of characteristic zero, which covers `ℝ` and
`ℂ`; the polarization identity itself holds over any commutative ring.

## Implementation notes

* Signs are encoded as `ε : ι → ℤˣ`, acting on any additive group through `ℤ`; the sum over
  `ι → ℤˣ` is a sum over the `2^k` sign vectors.
* The declarations about (continuous) multilinear maps live in the namespaces
  `MultilinearMap` and `ContinuousMultilinearMap`, so that dot notation (`A.diag`,
  `A.symmetrize`) is available; the theory of homogeneous polynomials lives in
  `LocallyConvex.Analysis`.
* Multilinear maps are indexed by an arbitrary finite type `ι`; homogeneous polynomials use
  `Fin k`, so that the degree is a natural number.

## References

* [J. Bochnak, J. Siciak, *Polynomials and multilinear mappings in topological
  vector-spaces*][BS71a]
-/

@[expose] public section

open Function Finset
open scoped Nat BigOperators

noncomputable section

namespace MultilinearMap

section Ring

variable {R : Type*} [CommRing R] {ι : Type*} {M N : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The *diagonal* of a multilinear map, `x ↦ A (x, …, x)`. For `ι = Fin k` this is the
homogeneous polynomial of degree `k` associated with `A`. -/
def diag (A : MultilinearMap R (fun _ : ι ↦ M) N) (x : M) : N :=
  A fun _ ↦ x

/-- Unfolding lemma for `MultilinearMap.diag`. -/
@[simp] theorem diag_apply (A : MultilinearMap R (fun _ : ι ↦ M) N) (x : M) :
    A.diag x = A fun _ ↦ x := rfl

/-- The diagonal of a multilinear map is homogeneous of degree `card ι`. -/
theorem diag_smul [Fintype ι] (A : MultilinearMap R (fun _ : ι ↦ M) N) (c : R) (x : M) :
    A.diag (c • x) = c ^ Fintype.card ι • A.diag x := by
  simp [diag, A.map_smul_univ (fun _ ↦ c) (fun _ ↦ x)]

/-- A multilinear map is *symmetric* if it is invariant under every permutation of its
arguments. -/
def IsSymm (A : MultilinearMap R (fun _ : ι ↦ M) N) : Prop :=
  ∀ (σ : Equiv.Perm ι) (v : ι → M), A (v ∘ σ) = A v

/-- Symmetry, stated through `MultilinearMap.domDomCongr`. -/
theorem isSymm_iff_domDomCongr (A : MultilinearMap R (fun _ : ι ↦ M) N) :
    A.IsSymm ↔ ∀ σ : Equiv.Perm ι, A.domDomCongr σ = A := by
  refine ⟨fun h σ ↦ ext fun v ↦ h σ v, fun h σ v ↦ ?_⟩
  exact DFunLike.congr_fun (h σ) v

/-- Sum of the `n`-th powers of the two signs `±1`. -/
private theorem sum_units_pow (n : ℕ) : ∑ u : ℤˣ, ((u ^ n : ℤˣ) : ℤ) = 1 + (-1) ^ n := by
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} by decide]
  simp

/-- The sign sum in the polarization formula: for `r : ι → ι`,
`∑_ε (∏_j ε_j) (∏_i ε_{r i})` equals `2 ^ card ι` when `r` is surjective (hence a permutation),
and vanishes otherwise, since then some sign `ε_j` occurs only once. -/
private theorem sum_signs [Fintype ι] [DecidableEq ι] (r : ι → ι) :
    ∑ ε : ι → ℤˣ, (((∏ j, ε j) * ∏ i, ε (r i) : ℤˣ) : ℤ) =
      if Surjective r then 2 ^ Fintype.card ι else 0 := by
  have key : ∀ ε : ι → ℤˣ, (((∏ j, ε j) * ∏ i, ε (r i) : ℤˣ) : ℤ) =
      ∏ j, ((ε j ^ (#{i | r i = j} + 1) : ℤˣ) : ℤ) := by
    intro ε
    rw [← Finset.prod_fiberwise' univ r ε, ← prod_mul_distrib, Units.coe_prod]
    refine prod_congr rfl fun j _ ↦ ?_
    rw [prod_const, pow_succ, mul_comm]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun j (u : ℤˣ) ↦ ((u ^ (#{i | r i = j} + 1) : ℤˣ) : ℤ))]
  simp_rw [sum_units_pow]
  split_ifs with hr
  · have hb : Bijective r := ⟨Finite.injective_iff_surjective.mpr hr, hr⟩
    have hc : ∀ j, #{i | r i = j} = 1 := by
      intro j
      rw [card_eq_one]
      obtain ⟨i, hi, hu⟩ := hb.existsUnique j
      exact ⟨i, by ext i'; simpa using ⟨fun h ↦ hu i' h, fun h ↦ h ▸ hi⟩⟩
    simp [hc, Finset.card_univ]
  · obtain ⟨j, hj⟩ := not_forall.mp hr
    refine prod_eq_zero (mem_univ j) ?_
    have : #{i | r i = j} = 0 := by
      rw [card_eq_zero, filter_eq_empty_iff]
      exact fun i _ h ↦ hj ⟨i, h⟩
    simp [this]

/-- Expansion of the diagonal on a signed sum, by multilinearity: the sum runs over all maps
`r : ι → ι`, not only permutations. -/
theorem diag_sum_units_smul [Fintype ι] [DecidableEq ι] (A : MultilinearMap R (fun _ : ι ↦ M) N)
    (ε : ι → ℤˣ) (x : ι → M) :
    A.diag (∑ j, ε j • x j) = ∑ r : ι → ι, (∏ i, ε (r i)) • A (x ∘ r) := by
  rw [diag, A.map_sum (fun _ j ↦ ε j • x j)]
  refine sum_congr rfl fun r _ ↦ ?_
  have h : ∀ (u : ℤˣ) (y : M), u • y = ((u : ℤ) : R) • y := fun u y ↦ by
    rw [Units.smul_def, Int.cast_smul_eq_zsmul]
  simp_rw [h, A.map_smul_univ, Units.smul_def, Units.coe_prod, ← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

/-- **Polarization formula** (Mazur–Orlicz; [BS71a, Theorem A, p. 60]), `±1` form.
For a symmetric multilinear map `A` and `x : ι → M`, with `k = card ι`,
`∑_{ε ∈ {±1}^ι} (∏_j ε_j) • A.diag (∑_j ε_j • x_j) = (2^k k!) • A x`.
It holds over any commutative ring; no topology is involved. -/
theorem polarization [Fintype ι] [DecidableEq ι] {A : MultilinearMap R (fun _ : ι ↦ M) N}
    (hA : A.IsSymm) (x : ι → M) :
    ∑ ε : ι → ℤˣ, (∏ j, ε j) • A.diag (∑ j, ε j • x j) =
      (2 ^ Fintype.card ι * (Fintype.card ι)!) • A x := by
  simp_rw [diag_sum_units_smul, smul_sum, smul_smul]
  rw [sum_comm]
  simp_rw [Units.smul_def, ← sum_smul, sum_signs]
  rw [← Fintype.sum_of_injective (fun σ : Equiv.Perm ι ↦ (σ : ι → ι)) DFunLike.coe_injective
    (fun _ ↦ (2 ^ Fintype.card ι : ℤ) • A x)
    (fun r ↦ (if Surjective r then (2 : ℤ) ^ Fintype.card ι else 0) • A (x ∘ r))]
  · rw [sum_const, card_univ, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul,
      ← Nat.cast_smul_eq_nsmul ℤ]
    push_cast
    ring_nf
  · intro r hr
    have hs : ¬ Surjective r := fun hs ↦
      hr ⟨Equiv.ofBijective r ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, rfl⟩
    simp [hs]
  · intro σ
    simp [σ.surjective, hA σ x]

end Ring

section Field

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : Type*}
  [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]

/-- The *symmetrization* `(1 / k!) ∑_σ A ∘ σ` of a multilinear map, `k = card ι`. -/
def symmetrize (A : MultilinearMap 𝕜 (fun _ : ι ↦ M) N) : MultilinearMap 𝕜 (fun _ : ι ↦ M) N :=
  ((Fintype.card ι)! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm ι, A.domDomCongr σ

/-- Value of the symmetrization: the average of `A` over all permutations of the arguments. -/
theorem symmetrize_apply (A : MultilinearMap 𝕜 (fun _ : ι ↦ M) N) (v : ι → M) :
    A.symmetrize v = ((Fintype.card ι)! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm ι, A (v ∘ σ) := by
  simp only [symmetrize, smul_apply, sum_apply, domDomCongr_apply]
  rfl

/-- The symmetrization of a multilinear map is symmetric. -/
theorem symmetrize_isSymm (A : MultilinearMap 𝕜 (fun _ : ι ↦ M) N) : A.symmetrize.IsSymm := by
  intro τ v
  rw [symmetrize_apply, symmetrize_apply,
    ← Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm ι ↦ A (v ∘ σ))]
  rfl

variable [CharZero 𝕜]

private theorem natCast_factorial_ne_zero (n : ℕ) : ((n)! : 𝕜) ≠ 0 :=
  Nat.cast_ne_zero.mpr n.factorial_ne_zero

/-- Symmetrization does not change the diagonal (characteristic zero). -/
@[simp] theorem diag_symmetrize (A : MultilinearMap 𝕜 (fun _ : ι ↦ M) N) :
    A.symmetrize.diag = A.diag := by
  ext x
  have h : ∀ σ : Equiv.Perm ι, ((fun _ : ι ↦ x) ∘ σ) = fun _ ↦ x := fun _ ↦ rfl
  rw [diag_apply, diag_apply, symmetrize_apply]
  simp only [h, sum_const, card_univ, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul 𝕜]
  rw [inv_smul_smul₀ (natCast_factorial_ne_zero _)]

/-- Symmetrization fixes symmetric multilinear maps (characteristic zero). -/
theorem symmetrize_eq_self {A : MultilinearMap 𝕜 (fun _ : ι ↦ M) N} (hA : A.IsSymm) :
    A.symmetrize = A := by
  ext v
  simp only [symmetrize_apply, hA _ v, sum_const, card_univ, Fintype.card_perm,
    ← Nat.cast_smul_eq_nsmul 𝕜]
  rw [inv_smul_smul₀ (natCast_factorial_ne_zero _)]

/-- The polarization formula solved for `A x` (characteristic zero): a symmetric multilinear
map is an explicit finite linear combination of values of its diagonal. -/
theorem eq_polarization {A : MultilinearMap 𝕜 (fun _ : ι ↦ M) N} (hA : A.IsSymm) (x : ι → M) :
    A x = ((2 ^ Fintype.card ι * (Fintype.card ι)! : ℕ) : 𝕜)⁻¹ •
      ∑ ε : ι → ℤˣ, (∏ j, ε j) • A.diag (∑ j, ε j • x j) := by
  rw [polarization hA, ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀]
  exact Nat.cast_ne_zero.mpr (by positivity)

omit [Fintype ι] [DecidableEq ι] in
/-- A symmetric multilinear map is determined by its diagonal (characteristic zero). -/
theorem eq_of_diag_eq [Finite ι] {A B : MultilinearMap 𝕜 (fun _ : ι ↦ M) N} (hA : A.IsSymm)
    (hB : B.IsSymm) (h : A.diag = B.diag) : A = B := by
  cases nonempty_fintype ι
  classical
  ext x
  rw [eq_polarization hA, eq_polarization hB, h]

/-- Two multilinear maps define the same homogeneous polynomial iff their symmetrizations
agree. -/
theorem diag_eq_diag_iff {A B : MultilinearMap 𝕜 (fun _ : ι ↦ M) N} :
    A.diag = B.diag ↔ A.symmetrize = B.symmetrize := by
  refine ⟨fun h ↦ eq_of_diag_eq A.symmetrize_isSymm B.symmetrize_isSymm ?_, fun h ↦ ?_⟩
  · rw [diag_symmetrize, diag_symmetrize, h]
  · rw [← diag_symmetrize A, h, diag_symmetrize]

end Field

end MultilinearMap

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The *diagonal* `x ↦ A (x, …, x)` of a continuous multilinear map. -/
def diag (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (x : E) : F :=
  A fun _ ↦ x

/-- Unfolding lemma for `ContinuousMultilinearMap.diag`. -/
@[simp] theorem diag_apply (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (x : E) :
    A.diag x = A fun _ ↦ x := rfl

/-- The diagonal of a continuous multilinear map is that of the underlying multilinear map. -/
@[simp] theorem toMultilinearMap_diag (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    A.toMultilinearMap.diag = A.diag := rfl

/-- The diagonal of a continuous multilinear map is continuous. -/
theorem continuous_diag (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    Continuous A.diag :=
  A.cont.comp (continuous_pi fun _ ↦ continuous_id)

/-- The diagonal of a continuous multilinear map is homogeneous of degree `card ι`. -/
theorem diag_smul [Fintype ι] (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (c : 𝕜)
    (x : E) : A.diag (c • x) = c ^ Fintype.card ι • A.diag x :=
  A.toMultilinearMap.diag_smul c x

variable [Fintype ι] [DecidableEq ι] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]

/-- The symmetrization of a continuous multilinear map; it is continuous because the target
is a topological additive group with continuous multiplication by each fixed scalar. -/
def symmetrize (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F :=
  ((Fintype.card ι)! : 𝕜)⁻¹ • ∑ σ : Equiv.Perm ι, A.domDomCongr σ

/-- The continuous symmetrization has the algebraic symmetrization as underlying map. -/
@[simp] theorem toMultilinearMap_symmetrize (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    A.symmetrize.toMultilinearMap = A.toMultilinearMap.symmetrize := by
  ext v
  simp only [symmetrize, MultilinearMap.symmetrize_apply, coe_coe, smul_apply, sum_apply,
    domDomCongr_apply]
  rfl

/-- The symmetrization of a continuous multilinear map is symmetric. -/
theorem symmetrize_isSymm (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    A.symmetrize.toMultilinearMap.IsSymm := by
  rw [toMultilinearMap_symmetrize]
  exact A.toMultilinearMap.symmetrize_isSymm

variable [CharZero 𝕜]

/-- Symmetrization does not change the diagonal (characteristic zero). -/
@[simp] theorem diag_symmetrize (A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    A.symmetrize.diag = A.diag := by
  rw [← toMultilinearMap_diag, toMultilinearMap_symmetrize, MultilinearMap.diag_symmetrize,
    toMultilinearMap_diag]

/-- Symmetrization fixes symmetric continuous multilinear maps (characteristic zero). -/
theorem symmetrize_eq_self {A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F}
    (hA : A.toMultilinearMap.IsSymm) : A.symmetrize = A :=
  toMultilinearMap_injective <| by rw [toMultilinearMap_symmetrize, A.1.symmetrize_eq_self hA]

omit [Fintype ι] [DecidableEq ι] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F] in
/-- A symmetric continuous multilinear map is determined by its diagonal. -/
theorem eq_of_diag_eq [Finite ι] {A B : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F}
    (hA : A.toMultilinearMap.IsSymm) (hB : B.toMultilinearMap.IsSymm) (h : A.diag = B.diag) :
    A = B :=
  toMultilinearMap_injective <| MultilinearMap.eq_of_diag_eq hA hB h

end ContinuousMultilinearMap

namespace MultilinearMap

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {ι : Type*} [Finite ι] {E F : Type*}
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]

/-- **Continuity criterion** (Bochnak–Siciak I, remark after Theorem A, p. 61). A symmetric
multilinear map, a priori without any continuity, is jointly continuous as soon as its diagonal
is continuous: by polarization, `A x` is a fixed linear combination of the values
`A.diag (∑_j ε_j x_j)`, which depend continuously on `x`. No completeness, local convexity or
Hausdorff assumption is needed. -/
theorem continuous_of_isSymm_of_continuous_diag {A : MultilinearMap 𝕜 (fun _ : ι ↦ E) F}
    (hA : A.IsSymm) (hp : Continuous A.diag) : Continuous A := by
  cases nonempty_fintype ι
  classical
  have h : ⇑A = fun x ↦ ((2 ^ Fintype.card ι * (Fintype.card ι)! : ℕ) : 𝕜)⁻¹ •
      ∑ ε : ι → ℤˣ, (∏ j, ε j) • A.diag (∑ j, ε j • x j) := funext (eq_polarization hA)
  rw [h]
  refine (continuous_finsetSum _ fun ε _ ↦ ?_).const_smul _
  refine (hp.comp (continuous_finsetSum _ fun j _ ↦ ?_)).const_smul _
  exact (continuous_apply j).const_smul (ε j)

end MultilinearMap

namespace LocallyConvex.Analysis

section ContHomPoly

variable {𝕜 : Type*} [Field 𝕜] {k : ℕ} {D E F G : Type*}
  [AddCommGroup D] [Module 𝕜 D] [TopologicalSpace D]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
  {p q : E → F}

variable (𝕜) in
/-- `p : E → F` is a *continuous homogeneous polynomial of degree `k`* if it is the diagonal of
a continuous `k`-linear map; the map may be taken symmetric (`IsContHomPoly.exists_symm`).
No completeness of `E` or `F` is assumed. -/
def IsContHomPoly (k : ℕ) (p : E → F) : Prop :=
  ∃ A : ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ E) F, ∀ x, p x = A fun _ ↦ x

namespace IsContHomPoly

/-- A continuous homogeneous polynomial is continuous. -/
theorem continuous (hp : IsContHomPoly 𝕜 k p) : Continuous p := by
  obtain ⟨A, hA⟩ := hp
  rw [show p = A.diag from funext hA]
  exact A.continuous_diag

/-- A homogeneous polynomial of degree `k` is homogeneous of degree `k`. -/
theorem map_smul (hp : IsContHomPoly 𝕜 k p) (c : 𝕜) (x : E) : p (c • x) = c ^ k • p x := by
  obtain ⟨A, hA⟩ := hp
  rw [hA, hA]
  simpa using A.diag_smul c x

/-- The continuous multilinear map defining a homogeneous polynomial can be chosen
symmetric. -/
theorem exists_symm [CharZero 𝕜] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
    (hp : IsContHomPoly 𝕜 k p) :
    ∃ A : ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ E) F,
      A.toMultilinearMap.IsSymm ∧ ∀ x, p x = A fun _ ↦ x := by
  obtain ⟨A, hA⟩ := hp
  refine ⟨A.symmetrize, A.symmetrize_isSymm, fun x ↦ ?_⟩
  rw [← ContinuousMultilinearMap.diag_apply, A.diag_symmetrize, hA, A.diag_apply]

/-- The zero map is a continuous homogeneous polynomial of every degree. -/
theorem zero : IsContHomPoly 𝕜 k (0 : E → F) := ⟨0, fun _ ↦ rfl⟩

/-- Continuous homogeneous polynomials of degree `k` are closed under addition. -/
theorem add [ContinuousAdd F] (hp : IsContHomPoly 𝕜 k p) (hq : IsContHomPoly 𝕜 k q) :
    IsContHomPoly 𝕜 k (p + q) := by
  obtain ⟨A, hA⟩ := hp
  obtain ⟨B, hB⟩ := hq
  exact ⟨A + B, fun x ↦ by simp [hA, hB]⟩

/-- Continuous homogeneous polynomials of degree `k` are closed under negation. -/
theorem neg [IsTopologicalAddGroup F] (hp : IsContHomPoly 𝕜 k p) : IsContHomPoly 𝕜 k (-p) := by
  obtain ⟨A, hA⟩ := hp
  exact ⟨-A, fun x ↦ by simp [hA]⟩

/-- Continuous homogeneous polynomials of degree `k` are closed under subtraction. -/
theorem sub [IsTopologicalAddGroup F] (hp : IsContHomPoly 𝕜 k p) (hq : IsContHomPoly 𝕜 k q) :
    IsContHomPoly 𝕜 k (p - q) := by
  rw [sub_eq_add_neg]
  exact hp.add hq.neg

/-- Continuous homogeneous polynomials of degree `k` are closed under scalar multiples. -/
theorem const_smul [ContinuousConstSMul 𝕜 F] (hp : IsContHomPoly 𝕜 k p) (c : 𝕜) :
    IsContHomPoly 𝕜 k (c • p) := by
  obtain ⟨A, hA⟩ := hp
  exact ⟨c • A, fun x ↦ by simp [hA]⟩

/-- Composition on the left with a continuous linear map. -/
theorem clm_comp (L : F →L[𝕜] G) (hp : IsContHomPoly 𝕜 k p) : IsContHomPoly 𝕜 k (L ∘ p) := by
  obtain ⟨A, hA⟩ := hp
  exact ⟨L.compContinuousMultilinearMap A, fun x ↦ by simp [hA]⟩

/-- Composition on the right with a continuous linear map. -/
theorem comp_clm (hp : IsContHomPoly 𝕜 k p) (T : D →L[𝕜] E) : IsContHomPoly 𝕜 k (p ∘ T) := by
  obtain ⟨A, hA⟩ := hp
  exact ⟨A.compContinuousLinearMap fun _ ↦ T, fun x ↦ by simp [hA]⟩

end IsContHomPoly

/-- The continuous homogeneous polynomials of degree `0` are the constant maps. -/
theorem isContHomPoly_zero_iff : IsContHomPoly 𝕜 0 p ↔ ∃ c : F, p = fun _ ↦ c := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A 0, funext fun x ↦ by rw [hA]; congr; exact Subsingleton.elim _ _⟩
  · rintro ⟨c, rfl⟩
    exact ⟨ContinuousMultilinearMap.constOfIsEmpty 𝕜 (fun _ : Fin 0 ↦ E) c, fun _ ↦ rfl⟩

/-- The continuous homogeneous polynomials of degree `1` are the continuous linear maps. -/
theorem isContHomPoly_one_iff : IsContHomPoly 𝕜 1 p ↔ ∃ L : E →L[𝕜] F, ⇑L = p := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨(ContinuousMultilinearMap.ofSubsingleton 𝕜 E F (0 : Fin 1)).symm A,
      funext fun x ↦ by simp [hA]⟩
  · rintro ⟨L, rfl⟩
    exact ⟨ContinuousMultilinearMap.ofSubsingleton 𝕜 E F (0 : Fin 1) L, fun x ↦ by simp⟩

/-- A continuous linear map is a continuous homogeneous polynomial of degree `1`. -/
theorem isContHomPoly_continuousLinearMap (L : E →L[𝕜] F) : IsContHomPoly 𝕜 1 L :=
  isContHomPoly_one_iff.mpr ⟨L, rfl⟩

variable [CharZero 𝕜] [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]

/-- **Bochnak–Siciak continuity criterion** (part I, remark after Theorem A, p. 61). If the
diagonal of an algebraic `k`-linear map `A` (symmetric or not) is continuous, then it is a
continuous homogeneous polynomial: the symmetrization of `A` has the same diagonal and is
continuous by polarization. -/
theorem isContHomPoly_diag_of_continuous {A : MultilinearMap 𝕜 (fun _ : Fin k ↦ E) F}
    (hp : Continuous A.diag) : IsContHomPoly 𝕜 k A.diag := by
  have hc : Continuous A.symmetrize := A.symmetrize.continuous_of_isSymm_of_continuous_diag
    A.symmetrize_isSymm (by rwa [MultilinearMap.diag_symmetrize])
  exact ⟨⟨A.symmetrize, hc⟩, fun x ↦ by
    rw [← MultilinearMap.diag_symmetrize]; rfl⟩

/-- The continuous homogeneous polynomials of degree `k` are exactly the continuous maps that
are algebraic homogeneous polynomials of degree `k`. -/
theorem isContHomPoly_iff_continuous :
    IsContHomPoly 𝕜 k p ↔
      Continuous p ∧ ∃ A : MultilinearMap 𝕜 (fun _ : Fin k ↦ E) F, p = A.diag := by
  refine ⟨fun hp ↦ ⟨hp.continuous, ?_⟩, ?_⟩
  · obtain ⟨A, hA⟩ := hp
    exact ⟨A.toMultilinearMap, funext hA⟩
  · rintro ⟨hc, A, rfl⟩
    exact isContHomPoly_diag_of_continuous hc

end ContHomPoly

section Uniqueness

variable {𝕜 : Type*} [Field 𝕜] {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- A vector-valued polynomial `t ↦ ∑_{n ≤ N} t^n • v_n` vanishing at more than `N` points has
all its coefficients equal to zero (Vandermonde). Purely algebraic: the target is any vector
space, and the scalar case is applied through linear functionals. -/
theorem eq_zero_of_sum_pow_smul_eq_zero {N : ℕ} {v : ℕ → F} (S : Finset 𝕜) (hS : N < #S)
    (h : ∀ t ∈ S, ∑ n ∈ range (N + 1), t ^ n • v n = 0) {n : ℕ} (hn : n ≤ N) : v n = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff 𝕜]
  intro ℓ
  let P : Polynomial 𝕜 := ∑ m ∈ range (N + 1), Polynomial.C (ℓ (v m)) * Polynomial.X ^ m
  have hP : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P S (fun t ht ↦ ?_) ?_
    · have := congrArg ℓ (h t ht)
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
      rw [← this]
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
    · refine lt_of_le_of_lt ?_ hS
      exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm ↦
        (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (mem_range.mp hm))
  have := congrArg (fun Q ↦ Polynomial.coeff Q n) hP
  simpa [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Nat.lt_succ_iff.mpr hn]
    using this

/-- **Uniqueness of finite homogeneous expansions.** If `p_n` is homogeneous of degree `n` for
`n ≤ N` and `∑_{n ≤ N} p_n (t • x) = 0` for all `t` in a set of more than `N` scalars, then
`p_n x = 0` for each `n ≤ N`. Only algebraic homogeneity is used. -/
theorem homogeneous_components_eq_zero {N : ℕ} {p : ℕ → E → F}
    (hp : ∀ n (t : 𝕜) x, p n (t • x) = t ^ n • p n x) {x : E} (S : Finset 𝕜) (hS : N < #S)
    (h : ∀ t ∈ S, ∑ n ∈ range (N + 1), p n (t • x) = 0) {n : ℕ} (hn : n ≤ N) : p n x = 0 :=
  eq_zero_of_sum_pow_smul_eq_zero (v := fun m ↦ p m x) S hS
    (fun t ht ↦ by simpa only [hp] using h t ht) hn

/-- Uniqueness of finite homogeneous expansions when the expansion vanishes on the whole
line `t ↦ t • x`, over an infinite field (for instance any field of characteristic zero). -/
theorem homogeneous_components_eq_zero' [Infinite 𝕜] {N : ℕ} {p : ℕ → E → F}
    (hp : ∀ n (t : 𝕜) x, p n (t • x) = t ^ n • p n x) {x : E}
    (h : ∀ t : 𝕜, ∑ n ∈ range (N + 1), p n (t • x) = 0) {n : ℕ} (hn : n ≤ N) : p n x = 0 := by
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq 𝕜 (N + 1)
  exact homogeneous_components_eq_zero hp S (by omega) (fun t _ ↦ h t) hn

end Uniqueness

end LocallyConvex.Analysis

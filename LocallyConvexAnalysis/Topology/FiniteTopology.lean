/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Topology.DirectLimitAlgebra
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# The finite topology

Reference: [GN26, Examples A.7.14] and A.7.16 (pp. 890–891).

Let `E` be a real vector space. Each finite-dimensional subspace `F` carries its unique vector
topology, the module topology (`moduleTopology ℝ F`). The **finite topology** on `E`
(`FiniteTop E`) is the direct limit topology of the finite-dimensional subspaces.

## Main definitions

* `FinSub E`: the finite-dimensional subspaces of `E`, each with its module topology.
* `FiniteTop E`: `E` with the finite topology, the direct limit topology of the `FinSub E`
  ([GN26, Example A.7.16]).
* `seqSub b n`: for a countable basis `b : Module.Basis ℕ ℝ E`, the span `Fₙ` of
  `b 0, …, b (n - 1)`.

## Main results

* `FiniteTop.continuous_linearMap`: every linear map from `FiniteTop E` to a topological vector
  space is continuous; `FiniteTop.topology_le`: the finite topology is finer than every vector
  topology on `E` (Example A.7.16).
* For `E` with a countable basis `b : Module.Basis ℕ ℝ E`:
  `FiniteTop.topology_eq_seq`: the finite topology is the direct limit topology of the
  sequence `F₀ ⊆ F₁ ⊆ ⋯`; `FiniteTop.isTopologicalAddGroup`, `FiniteTop.continuousSMul`,
  `FiniteTop.locallyConvexSpace`, `FiniteTop.t2Space`: it is a Hausdorff locally convex vector
  topology, hence the finest vector topology and the finest locally convex topology on `E`
  (Example A.7.16). For `E = ℝ^(ℕ)` (`ℕ →₀ ℝ`, with the standard basis) this is Example A.7.14.
* `FiniteTop.continuousLinearEquivOfLinearEquiv`: linear isomorphisms between spaces of countable
  dimension are isomorphisms of topological vector spaces for the finite topologies; in
  particular `FiniteTop.continuousLinearEquivFinsupp`: `E ≅ ℝ^(ℕ)` (Example A.7.16).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

open TopDirectLimit

universe u

variable (E : Type u) [AddCommGroup E] [Module ℝ E]

/-- The finite-dimensional subspaces of `E`. -/
abbrev FinSub : Type u := {F : Submodule ℝ E // FiniteDimensional ℝ F}

variable {E}

/-- The module topology of a finite-dimensional subspace. -/
@[instance_reducible]
instance FinSub.topologicalSpace (F : FinSub E) : TopologicalSpace F.1 := moduleTopology ℝ F.1

instance FinSub.isModuleTopology (F : FinSub E) : IsModuleTopology ℝ F.1 := ⟨rfl⟩

instance FinSub.continuousAdd (F : FinSub E) : ContinuousAdd F.1 :=
  IsModuleTopology.toContinuousAdd ℝ _

/-- The module topology of a finite-dimensional subspace, on the set `F`. -/
@[instance_reducible]
instance FinSub.topologicalSpaceSet (F : FinSub E) : TopologicalSpace ((F.1 : Set E)) :=
  FinSub.topologicalSpace F

variable (E) in
/-- `E` with the **finite topology**: the direct limit topology of its finite-dimensional
subspaces ([GN26, Example A.7.16]). -/
abbrev FiniteTop : Type u := TopDirectLimit fun F : FinSub E ↦ ((F.1 : Set E))

namespace FiniteTop

/-- The identity of `E`, into the finite topology. -/
def toFiniteTop : E ≃ₗ[ℝ] FiniteTop E := LinearEquiv.refl ℝ E

/-- **Linear maps on the finite topology are continuous** ([GN26, Example A.7.16]): their
restrictions to the finite-dimensional subspaces are. -/
theorem continuous_linearMap {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [ContinuousAdd G] [ContinuousSMul ℝ G] (f : FiniteTop E →ₗ[ℝ] G) : Continuous f :=
  continuous_iff.2 fun F ↦ IsModuleTopology.continuous_of_linearMap
    (f.comp ((F.1.subtype : F.1 →ₗ[ℝ] E)))

/-- **The finite topology is finer than every vector topology**
([GN26, Example A.7.16]). -/
theorem topology_le {τ : TopologicalSpace E} (hadd : @ContinuousAdd E τ _)
    (hsmul : @ContinuousSMul ℝ E _ _ τ) :
    TopDirectLimit.topology (fun F : FinSub E ↦ ((F.1 : Set E))) ≤ τ :=
  TopDirectLimit.topology_le fun F ↦
    @IsModuleTopology.continuous_of_linearMap ℝ _ _ F.1 _ _ _ _ E _ _ τ hadd hsmul F.1.subtype

end FiniteTop

/-! ### Finite-dimensional spaces with the module topology -/

section FiniteDimensional

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace F]
  [IsModuleTopology ℝ F]

/-- A finite-dimensional space with the module topology is homeomorphic to `ℝᵈ`. -/
def homeomorphFinBasis : F ≃ₜ (Fin (Module.finrank ℝ F) → ℝ) :=
  have : ContinuousAdd F := IsModuleTopology.toContinuousAdd ℝ F
  { toEquiv := (Module.finBasis ℝ F).equivFun.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (Module.finBasis ℝ F).equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (Module.finBasis ℝ F).equivFun.symm.toLinearMap }

theorem t2Space_of_isModuleTopology : T2Space F :=
  (homeomorphFinBasis (F := F)).isEmbedding.t2Space

theorem locallyCompactSpace_of_isModuleTopology : LocallyCompactSpace F :=
  (homeomorphFinBasis (F := F)).isClosedEmbedding.locallyCompactSpace

theorem locallyConvexSpace_of_isModuleTopology : LocallyConvexSpace ℝ F := by
  have h := LocallyConvexSpace.induced (𝕜 := ℝ) (t := inferInstance)
    (Module.finBasis ℝ F).equivFun.toLinearMap
  convert h
  exact (homeomorphFinBasis (F := F)).isInducing.eq_induced

end FiniteDimensional

/-! ### Countable dimension -/

section Countable

variable (b : Module.Basis ℕ ℝ E)

/-- The span `Fₙ` of `b 0, …, b (n - 1)`. -/
def seqSub (n : ℕ) : Submodule ℝ E := Submodule.span ℝ (b '' Iio n)

instance (n : ℕ) : FiniteDimensional ℝ (seqSub b n) :=
  FiniteDimensional.span_of_finite ℝ ((finite_Iio n).image b)

/-- `Fₙ`, as a finite-dimensional subspace. -/
def seqFin (n : ℕ) : FinSub E := ⟨seqSub b n, inferInstance⟩

/-- The module topology of `Fₙ`. -/
@[instance_reducible]
instance seqSub.topologicalSpace (n : ℕ) : TopologicalSpace (seqSub b n) :=
  FinSub.topologicalSpace (seqFin b n)

instance (n : ℕ) : IsModuleTopology ℝ (seqSub b n) := ⟨rfl⟩

instance (n : ℕ) : IsTopologicalAddGroup (seqSub b n) :=
  IsModuleTopology.isTopologicalAddGroup ℝ _

instance (n : ℕ) : T2Space (seqSub b n) := t2Space_of_isModuleTopology

instance (n : ℕ) : LocallyCompactSpace (seqSub b n) := locallyCompactSpace_of_isModuleTopology

instance (n : ℕ) : LocallyConvexSpace ℝ (seqSub b n) := locallyConvexSpace_of_isModuleTopology

attribute [local instance] submoduleTop

instance (n : ℕ) : T2Space ((seqSub b n : Set E)) :=
  inferInstanceAs (T2Space (seqSub b n))

instance (n : ℕ) : LocallyCompactSpace ((seqSub b n : Set E)) :=
  inferInstanceAs (LocallyCompactSpace (seqSub b n))

/-- Every vector lies in some `Fₙ`. -/
theorem exists_mem_seqSub (x : E) : ∃ n, x ∈ seqSub b n := by
  refine ⟨(b.repr x).support.sup id + 1, Submodule.span_mono (image_mono fun i hi ↦ ?_)
    (b.mem_span_repr_support x)⟩
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)

/-- The spans `F₀ ⊆ F₁ ⊆ ⋯` form a direct sequence. -/
theorem isDirectSeq_seqSub : IsDirectSeq fun n ↦ (seqSub b n : Set E) where
  mono _ _ h := Submodule.span_mono (image_mono (Iio_subset_Iio h))
  exists_mem := exists_mem_seqSub b
  continuous_inclusion n := IsModuleTopology.continuous_of_linearMap
    (Submodule.inclusion (p := seqSub b n) (p' := seqSub b (n + 1))
      (Submodule.span_mono (image_mono (Iio_subset_Iio (Nat.le_succ n)))))

/-- The spans `Fₙ` are cofinal among the finite-dimensional subspaces. -/
theorem exists_le_seqFin (F : FinSub E) : ∃ n, F ≤ seqFin b n := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional F.1).2 F.2
  refine ⟨s.sup fun x ↦ (b.repr x).support.sup id + 1, ?_⟩
  change F.1 ≤ seqSub b _
  rw [← hs, Submodule.span_le]
  intro x hx
  refine Submodule.span_mono (image_mono fun i hi ↦ ?_) (b.mem_span_repr_support x)
  exact (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)).trans_le
    (Finset.le_sup (f := fun x ↦ (b.repr x).support.sup id + 1) hx)

namespace FiniteTop

include b

/-- **The finite topology is the direct limit topology of `F₀ ⊆ F₁ ⊆ ⋯`**
([GN26, Example A.7.16], with Remark A.7.15(b)). -/
theorem topology_eq_seq :
    TopDirectLimit.topology (fun F : FinSub E ↦ ((F.1 : Set E))) =
      TopDirectLimit.topology fun n ↦ (seqSub b n : Set E) :=
  TopDirectLimit.topology_eq_comp (S := fun F : FinSub E ↦ ((F.1 : Set E))) (fun _ _ h ↦ h)
    (fun h ↦
    IsModuleTopology.continuous_of_linearMap (Submodule.inclusion h)) (seqFin b)
    (exists_le_seqFin b)

theorem isCompactifying_seqSub : (isDirectSeq_seqSub b).IsCompactifying :=
  (isDirectSeq_seqSub b).isCompactifying_of_locallyCompactSpace

/-- **The finite topology of a space of countable dimension is a vector topology**
([GN26, Examples A.7.14] and A.7.16): additions are continuous. -/
theorem isTopologicalAddGroup : IsTopologicalAddGroup (FiniteTop E) := by
  have h := (isCompactifying_seqSub b).isTopologicalAddGroup_submodule
  change @IsTopologicalAddGroup E (TopDirectLimit.topology fun F : FinSub E ↦ ((F.1 : Set E))) _
  rw [topology_eq_seq b]
  exact h

/-- Scalar multiplication is continuous for the finite topology of a space of countable
dimension ([GN26, Examples A.7.14] and A.7.16). -/
theorem continuousSMul : ContinuousSMul ℝ (FiniteTop E) := by
  have h := (isCompactifying_seqSub b).continuousSMul
  change @ContinuousSMul ℝ E _ _ (TopDirectLimit.topology fun F : FinSub E ↦ ((F.1 : Set E)))
  rw [topology_eq_seq b]
  exact h

/-- **The finite topology of a space of countable dimension is locally convex**
([GN26, Examples A.7.14] and A.7.16). -/
theorem locallyConvexSpace : LocallyConvexSpace ℝ (FiniteTop E) := by
  have h := (isCompactifying_seqSub b).locallyConvexSpace
  change @LocallyConvexSpace ℝ E _ _ _ _ (TopDirectLimit.topology fun F : FinSub E ↦
    ((F.1 : Set E)))
  rw [topology_eq_seq b]
  exact h

/-- The finite topology of a space of countable dimension is Hausdorff. -/
theorem t2Space : T2Space (FiniteTop E) := by
  have h := (isCompactifying_seqSub b).t2Space
  change @T2Space E (TopDirectLimit.topology fun F : FinSub E ↦ ((F.1 : Set E)))
  rw [topology_eq_seq b]
  exact h

/-- **Linear isomorphisms between spaces of countable dimension are isomorphisms of topological
vector spaces for the finite topologies** ([GN26, Example A.7.16]). -/
def continuousLinearEquivOfLinearEquiv {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    (b' : Module.Basis ℕ ℝ E') (f : E ≃ₗ[ℝ] E') : FiniteTop E ≃L[ℝ] FiniteTop E' :=
  have := isTopologicalAddGroup b
  have := continuousSMul b
  have := isTopologicalAddGroup b'
  have := continuousSMul b'
  { toLinearEquiv := f
    continuous_toFun := continuous_linearMap (E := E) (G := FiniteTop E') f.toLinearMap
    continuous_invFun := continuous_linearMap (E := E') (G := FiniteTop E) f.symm.toLinearMap }

/-- **A space of countable dimension with the finite topology is isomorphic to `ℝ^(ℕ)`**
([GN26, Example A.7.16]). -/
def continuousLinearEquivFinsupp : FiniteTop E ≃L[ℝ] FiniteTop (ℕ →₀ ℝ) :=
  continuousLinearEquivOfLinearEquiv b (Finsupp.basisSingleOne) b.repr

end FiniteTop

end Countable

end LocallyConvex.Analysis

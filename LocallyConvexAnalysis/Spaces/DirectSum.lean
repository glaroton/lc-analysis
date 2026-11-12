/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Real

/-!
# Locally convex direct sums

Reference: [GN26, Appendix B.13] (pp. 941–944) and Section 2.8 (pp. 234–235).

For a family `(E j)_{j ∈ J}` of topological vector spaces, `LCDirectSum E` is the space
`⊕_j E j` of finitely supported families, with the **box topology**: a basis of
`0`-neighbourhoods is given by the boxes `⊕_j V j = {x | ∀ j, x j ∈ V j}`, with `V j` a
`0`-neighbourhood in `E j` (`LCDirectSum.nhds_zero_hasBasis`, [GN26, Remark B.13.1(a)]).

## Main results

* The box topology is a vector topology over any nontrivially normed field, locally convex and
  Hausdorff when the summands are; the coordinates and the inclusions of the summands are
  continuous (Remark B.13.1(b), (c)).
* `LCDirectSum.continuous_of_continuous_single`: **the universal property** for countable `J`
  (Lemma B.13.2(a)).
* `LCDirectSum.prodEquiv`: `⊕_j (E j × F j) ≅ (⊕_j E j) × (⊕_j F j)` (Lemma B.13.2(c)).
* `LCDirectSum.contDiffMBOn_map`, `LCDirectSum.smoothMBOn_map`, `LCDirectSum.realAnalyticOn_map`:
  **direct sums of `C^k`, smooth, real analytic maps** `⊕_j f j`, with `f j 0 = 0` for all but
  finitely many `j`, are `C^k`, smooth, real analytic (Proposition 2.8.1);
  `LCDirectSum.complexAnalyticOn_map` is the complex analytic case.

## Implementation notes

* **The definition.** Glöckner–Neeb define the topology, for countable `J`, by the seminorms
  `x ↦ sup_j p_j(x_j)` with `p_j` continuous on `E j` (B.24), and observe that the boxes form a
  basis of `0`-neighbourhoods (Remark B.13.1(a)). We take the boxes as the definition: this needs
  no seminorms, works over `ℝ` and `ℂ` at once, and for countable `J` gives the same locally convex
  topology, since it is locally convex and has the universal property of Lemma B.13.2(a) (which
  characterizes the locally convex direct sum as the finest locally convex topology making the
  inclusions continuous). For uncountable `J` the locally convex direct sum topology can be
  strictly finer than the box topology; the results that need countability say so.
* `⊕_j f j` is `LCDirectSum.map f S hS`, where `hS : ∀ j ∉ S, f j 0 = 0` for a finite set `S`;
  the maps `f j` are total, and statements about the open sets `U j ⊆ E j` are made on the box
  `⊕_j U j`, which is open (`LCDirectSum.isOpen_box`).
* The real analytic case needs `0 ∈ U j` for `j ∉ S`, as in Glöckner–Neeb: there `⊕_j U j` is
  only defined under this assumption.

* `LCDirectSum.isEmbedding_mapCLM_subtype`, `LCDirectSum.exists_finset_of_isVonNBounded`, and the
  `CompleteSpace` instance: subspaces, bounded sets and completeness (Lemma B.13.2(d), (e), (f));
  the quasi-complete, sequentially complete and Mackey complete cases of (f) are in
  `Spaces/DirectCompleteness.lean`.

* `LCDirectSum.sigmaEquiv`: associativity, `⊕_{(i, j)} E i j ≅ ⊕_i ⊕_j E i j`
  (Lemma B.13.2(b)), for any index sets.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology Pointwise

noncomputable section

namespace LocallyConvex.Analysis

variable {J : Type*}

/-- The direct sum `⊕_j E j` of a family of spaces, to be endowed with the box topology. -/
def LCDirectSum (E : J → Type*) [∀ j, Zero (E j)] : Type _ := Π₀ j, E j

namespace LCDirectSum

variable {E : J → Type*}

section Algebra

variable [∀ j, AddCommGroup (E j)]

instance : AddCommGroup (LCDirectSum E) := inferInstanceAs (AddCommGroup (Π₀ j, E j))

instance : DFunLike (LCDirectSum E) J E := inferInstanceAs (DFunLike (Π₀ j, E j) J E)

instance {R : Type*} [Semiring R] [∀ j, Module R (E j)] : Module R (LCDirectSum E) :=
  inferInstanceAs (Module R (Π₀ j, E j))

instance {R S : Type*} [Semiring R] [Semiring S] [SMul R S] [∀ j, Module R (E j)]
    [∀ j, Module S (E j)] [∀ j, IsScalarTower R S (E j)] : IsScalarTower R S (LCDirectSum E) :=
  inferInstanceAs (IsScalarTower R S (Π₀ j, E j))

@[ext] theorem ext {x y : LCDirectSum E} (h : ∀ j, x j = y j) : x = y := DFinsupp.ext h

@[simp] theorem zero_apply (j : J) : (0 : LCDirectSum E) j = 0 := rfl
@[simp] theorem add_apply (x y : LCDirectSum E) (j : J) : (x + y) j = x j + y j := rfl
@[simp] theorem neg_apply (x : LCDirectSum E) (j : J) : (-x) j = -x j := rfl
@[simp] theorem sub_apply (x y : LCDirectSum E) (j : J) : (x - y) j = x j - y j :=
  DFinsupp.sub_apply x y j
@[simp] theorem smul_apply {R : Type*} [Semiring R] [∀ j, Module R (E j)] (c : R)
    (x : LCDirectSum E) (j : J) : (c • x) j = c • x j := rfl

/-- Every element vanishes outside a finite set. -/
theorem exists_finset (x : LCDirectSum E) : ∃ s : Finset J, ∀ j ∉ s, x j = 0 := by
  classical
  exact ⟨DFinsupp.support x, fun j hj ↦ DFinsupp.notMem_support_iff.1 hj⟩

/-- The box `⊕_j V j = {x | ∀ j, x j ∈ V j}`. -/
def box (V : ∀ j, Set (E j)) : Set (LCDirectSum E) := {x | ∀ j, x j ∈ V j}

@[simp] theorem mem_box {V : ∀ j, Set (E j)} {x : LCDirectSum E} : x ∈ box V ↔ ∀ j, x j ∈ V j :=
  Iff.rfl

end Algebra

section Topology

variable [∀ j, AddCommGroup (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, IsTopologicalAddGroup (E j)]

variable (E) in
set_option warn.classDefReducibility false in
/-- The filter basis of boxes `⊕_j V j` of `0`-neighbourhoods. -/
def addGroupFilterBasis : AddGroupFilterBasis (LCDirectSum E) where
  sets := {S | ∃ V : ∀ j, Set (E j), (∀ j, V j ∈ 𝓝 0) ∧ S = box V}
  nonempty := ⟨box fun _ ↦ univ, fun _ ↦ univ, fun _ ↦ univ_mem, rfl⟩
  inter_sets := by
    rintro _ _ ⟨V, hV, rfl⟩ ⟨W, hW, rfl⟩
    exact ⟨box fun j ↦ V j ∩ W j, ⟨_, fun j ↦ inter_mem (hV j) (hW j), rfl⟩,
      fun x hx ↦ ⟨fun j ↦ (hx j).1, fun j ↦ (hx j).2⟩⟩
  zero' := by
    rintro _ ⟨V, hV, rfl⟩ j
    exact mem_of_mem_nhds (hV j)
  add' := by
    rintro _ ⟨V, hV, rfl⟩
    choose W hW hWV using fun j ↦ exists_nhds_zero_half (hV j)
    refine ⟨box W, ⟨W, hW, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩ j
    exact hWV j _ (hx j) _ (hy j)
  neg' := by
    rintro _ ⟨V, hV, rfl⟩
    refine ⟨box fun j ↦ -V j, ⟨_, fun j ↦ neg_mem_nhds_zero _ (hV j), rfl⟩, fun x hx j ↦ ?_⟩
    have h := hx j
    rw [Set.mem_neg] at h
    exact h
  conj' := by
    rintro x₀ _ ⟨V, hV, rfl⟩
    refine ⟨box V, ⟨V, hV, rfl⟩, fun x hx ↦ ?_⟩
    simpa [add_comm x₀ x, add_assoc] using hx

theorem mem_addGroupFilterBasis {S : Set (LCDirectSum E)} :
    S ∈ addGroupFilterBasis E ↔ ∃ V : ∀ j, Set (E j), (∀ j, V j ∈ 𝓝 0) ∧ S = box V :=
  Iff.rfl

/-- The box topology. -/
instance : TopologicalSpace (LCDirectSum E) := (addGroupFilterBasis E).topology

instance : IsTopologicalAddGroup (LCDirectSum E) := (addGroupFilterBasis E).isTopologicalAddGroup

/-- **The boxes of `0`-neighbourhoods form a basis of `0`-neighbourhoods**
([GN26, Remark B.13.1(a)]). -/
theorem nhds_zero_hasBasis :
    (𝓝 (0 : LCDirectSum E)).HasBasis (fun V : ∀ j, Set (E j) ↦ ∀ j, V j ∈ 𝓝 0) box := by
  have h := (addGroupFilterBasis E).nhds_zero_hasBasis
  refine ⟨fun s ↦ ?_⟩
  rw [h.mem_iff]
  constructor
  · rintro ⟨_, hmem, hs⟩
    obtain ⟨V, hV, rfl⟩ := mem_addGroupFilterBasis.1 hmem
    exact ⟨V, hV, hs⟩
  · rintro ⟨V, hV, hs⟩
    exact ⟨_, mem_addGroupFilterBasis.2 ⟨V, hV, rfl⟩, hs⟩

/-- **The boxes of neighbourhoods form a basis of neighbourhoods**
([GN26, Remark B.13.1(a)]). -/
theorem nhds_hasBasis (x : LCDirectSum E) :
    (𝓝 x).HasBasis (fun V : ∀ j, Set (E j) ↦ ∀ j, V j ∈ 𝓝 (x j)) box := by
  refine ⟨fun s ↦ ?_⟩
  rw [← map_add_left_nhds_zero x, mem_map, nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨V, hV, hs⟩
    refine ⟨fun j ↦ (x j + ·) '' V j, fun j ↦ ?_, fun y hy ↦ ?_⟩
    · rw [← map_add_left_nhds_zero (x j)]
      exact image_mem_map (hV j)
    · have hy' : y - x ∈ box V := fun j ↦ by
        obtain ⟨v, hv, he⟩ := hy j
        rw [sub_apply, ← he, add_sub_cancel_left]
        exact hv
      have := hs hy'
      simpa using this
  · rintro ⟨V, hV, hs⟩
    refine ⟨fun j ↦ (x j + ·) ⁻¹' V j, fun j ↦ ?_, fun y hy ↦ hs fun j ↦ hy j⟩
    have h := hV j
    rw [← map_add_left_nhds_zero (x j)] at h
    exact h

theorem box_mem_nhds {x : LCDirectSum E} {V : ∀ j, Set (E j)} (hV : ∀ j, V j ∈ 𝓝 (x j)) :
    box V ∈ 𝓝 x :=
  (nhds_hasBasis x).mem_of_mem hV

/-- **Boxes of open sets are open** ([GN26, Remark B.13.1(a)]). -/
theorem isOpen_box {U : ∀ j, Set (E j)} (hU : ∀ j, IsOpen (U j)) : IsOpen (box U) :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ box_mem_nhds fun j ↦ (hU j).mem_nhds (hx j)

/-- The coordinate projections are continuous; equivalently, the inclusion into the product is
continuous ([GN26, Remark B.13.1(b)]). -/
theorem continuous_apply (j : J) : Continuous fun x : LCDirectSum E ↦ x j := by
  classical
  refine continuous_iff_continuousAt.2 fun x s hs ↦ ?_
  rw [mem_map]
  refine mem_of_superset (box_mem_nhds (V := Function.update (fun _ ↦ univ) j s) fun i ↦ ?_)
    fun y hy ↦ ?_
  · rcases eq_or_ne i j with rfl | hij
    · simpa using hs
    · simp [Function.update_of_ne hij]
  · have := hy j
    simpa using this

theorem continuous_toFun : Continuous fun x : LCDirectSum E ↦ (x : ∀ j, E j) :=
  continuous_pi continuous_apply

instance [∀ j, T2Space (E j)] : T2Space (LCDirectSum E) :=
  T2Space.of_injective_continuous (fun _ _ h ↦ ext fun j ↦ congrFun h j) continuous_toFun

/-- Scalar multiplication is continuous, over any nontrivially normed field. -/
instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] [∀ j, Module 𝕜 (E j)]
    [∀ j, ContinuousSMul 𝕜 (E j)] : ContinuousSMul 𝕜 (LCDirectSum E) := by
  refine ContinuousSMul.of_nhds_zero ?_ ?_ ?_
  · -- uniformly in the coordinates, through balanced cores
    rw [nhds_zero_hasBasis.tendsto_right_iff]
    intro V hV
    have hB : ∀ j, balancedCore 𝕜 (V j) ∈ 𝓝 (0 : E j) := fun j ↦ balancedCore_mem_nhds_zero (hV j)
    filter_upwards [prod_mem_prod (Metric.closedBall_mem_nhds (0 : 𝕜) one_pos)
      (box_mem_nhds (x := 0) hB)] with p hp j
    refine balancedCore_subset (𝕜 := 𝕜) (V j) ?_
    exact (balancedCore.balanced (𝕜 := 𝕜) (V j)) p.1 (by simpa using hp.1) ⟨p.2 j, hp.2 j, rfl⟩
  · intro m
    obtain ⟨s, hs⟩ := exists_finset m
    rw [nhds_zero_hasBasis.tendsto_right_iff]
    intro V hV
    have hj : ∀ j ∈ s, ∀ᶠ a : 𝕜 in 𝓝 0, a • m j ∈ V j := fun j _ ↦ by
      have h := (tendsto_id (x := 𝓝 (0 : 𝕜))).smul_const (m j)
      rw [zero_smul] at h
      exact h (hV j)
    filter_upwards [(s.eventually_all).2 hj] with a ha j
    by_cases hjs : j ∈ s
    · exact ha j hjs
    · simp only [smul_apply, hs j hjs, smul_zero]
      exact mem_of_mem_nhds (hV j)
  · intro a
    rw [nhds_zero_hasBasis.tendsto_right_iff]
    intro V hV
    filter_upwards [box_mem_nhds (x := (0 : LCDirectSum E)) (V := fun j ↦ (a • ·) ⁻¹' V j)
      fun j ↦ (continuous_const_smul a).continuousAt.preimage_mem_nhds (by simpa using hV j)]
      with x hx j
    exact hx j

/-- The box topology is locally convex. -/
instance [∀ j, Module ℝ (E j)] [∀ j, LocallyConvexSpace ℝ (E j)] :
    LocallyConvexSpace ℝ (LCDirectSum E) := by
  refine LocallyConvexSpace.ofBasisZero ℝ _ (fun V : ∀ j, Set (E j) ↦ box V)
    (fun V ↦ ∀ j, V j ∈ 𝓝 0 ∧ Convex ℝ (V j)) ⟨fun s ↦ ?_⟩ fun V hV ↦ ?_
  · rw [nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨V, hV, hs⟩
      choose W hW hWV using fun j ↦ (LocallyConvexSpace.convex_basis_zero ℝ (E j)).mem_iff.1
        (hV j)
      exact ⟨W, fun j ↦ (hW j).1 |> fun h ↦ ⟨h, (hW j).2⟩,
        fun x hx ↦ hs fun j ↦ hWV j (hx j)⟩
    · rintro ⟨V, hV, hs⟩
      exact ⟨V, fun j ↦ (hV j).1, hs⟩
  · intro x hx y hy a b ha hb hab j
    exact (hV j).2 (hx j) (hy j) ha hb hab

end Topology

section Maps

variable {F : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, AddCommGroup (F j)]

open Classical in
/-- **The direct sum of maps** `⊕_j f j : (x j)_j ↦ (f j (x j))_j`, for maps with `f j 0 = 0`
outside a finite set `S`. -/
def map (f : ∀ j, E j → F j) (S : Finset J) (_hS : ∀ j ∉ S, f j 0 = 0) (x : LCDirectSum E) :
    LCDirectSum F :=
  (DFinsupp.mapRange (fun j v ↦ f j v - f j 0) (fun _ ↦ sub_self _) x : Π₀ j, F j) +
    ∑ j ∈ S, DFinsupp.single j (f j 0)

@[simp] theorem map_apply (f : ∀ j, E j → F j) (S : Finset J) (hS : ∀ j ∉ S, f j 0 = 0)
    (x : LCDirectSum E) (j : J) : map f S hS x j = f j (x j) := by
  classical
  change (DFinsupp.mapRange (fun j v ↦ f j v - f j 0) (fun _ ↦ sub_self _) x +
    ∑ j ∈ S, DFinsupp.single j (f j 0) : Π₀ j, F j) j = _
  erw [DFinsupp.add_apply, DFinsupp.mapRange_apply, DFinsupp.finsetSum_apply]
  by_cases hj : j ∈ S
  · rw [Finset.sum_eq_single j (fun b _ hb ↦ by simp [DFinsupp.single_apply, hb])
      (fun h ↦ absurd hj h)]
    simp only [DFinsupp.single_eq_same, sub_add_cancel]
    rfl
  · rw [Finset.sum_eq_zero fun b hb ↦ by
      simp [DFinsupp.single_apply, show b ≠ j from fun h ↦ hj (h ▸ hb)], hS j hj]
    simp only [sub_zero, add_zero]
    rfl

theorem map_mem_box {f : ∀ j, E j → F j} {S : Finset J} {hS : ∀ j ∉ S, f j 0 = 0}
    {U : ∀ j, Set (E j)} {V : ∀ j, Set (F j)} (h : ∀ j, MapsTo (f j) (U j) (V j)) :
    MapsTo (map f S hS) (box U) (box V) := fun x hx j ↦ by
  rw [map_apply]
  exact h j (hx j)

variable [∀ j, TopologicalSpace (E j)] [∀ j, IsTopologicalAddGroup (E j)]
  [∀ j, TopologicalSpace (F j)] [∀ j, IsTopologicalAddGroup (F j)]

theorem continuousAt_map {f : ∀ j, E j → F j} {S : Finset J} {hS : ∀ j ∉ S, f j 0 = 0}
    {x : LCDirectSum E} (hf : ∀ j, ContinuousAt (f j) (x j)) : ContinuousAt (map f S hS) x := by
  rw [ContinuousAt, (nhds_hasBasis _).tendsto_right_iff]
  intro W hW
  filter_upwards [box_mem_nhds (x := x) (V := fun j ↦ f j ⁻¹' W j)
    fun j ↦ hf j (by simpa using hW j)] with y hy j
  simpa using hy j

/-- **Direct sums of continuous maps are continuous** ([GN26, Proposition 2.8.1],
`k = 0`). -/
theorem continuousOn_map {f : ∀ j, E j → F j} {S : Finset J} {hS : ∀ j ∉ S, f j 0 = 0}
    {U : ∀ j, Set (E j)} (hU : ∀ j, IsOpen (U j)) (hf : ∀ j, ContinuousOn (f j) (U j)) :
    ContinuousOn (map f S hS) (box U) := fun _ hx ↦
  (continuousAt_map fun j ↦ (hf j).continuousAt ((hU j).mem_nhds (hx j))).continuousWithinAt

theorem continuous_map {f : ∀ j, E j → F j} {S : Finset J} {hS : ∀ j ∉ S, f j 0 = 0}
    (hf : ∀ j, Continuous (f j)) : Continuous (map f S hS) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_map fun j ↦ (hf j).continuousAt

variable {𝕜 : Type*} [Semiring 𝕜] [∀ j, Module 𝕜 (E j)] [∀ j, Module 𝕜 (F j)]

/-- The direct sum `⊕_j L j` of continuous linear maps. -/
def mapCLM (L : ∀ j, E j →L[𝕜] F j) : LCDirectSum E →L[𝕜] LCDirectSum F where
  toFun := map (fun j ↦ L j) ∅ fun j _ ↦ map_zero (L j)
  map_add' x y := ext fun j ↦ by simp
  map_smul' c x := ext fun j ↦ by simp
  cont := continuous_map fun j ↦ (L j).continuous

@[simp] theorem mapCLM_apply (L : ∀ j, E j →L[𝕜] F j) (x : LCDirectSum E) (j : J) :
    mapCLM L x j = L j (x j) :=
  map_apply (fun j ↦ ⇑(L j)) ∅ (fun j _ ↦ map_zero (L j)) x j

/-- **`⊕_j (E j × F j) ≅ (⊕_j E j) × (⊕_j F j)`** as topological vector spaces
([GN26, Lemma B.13.2(c)]). -/
def prodEquiv : LCDirectSum (fun j ↦ E j × F j) ≃L[𝕜] LCDirectSum E × LCDirectSum F where
  toFun x := (mapCLM (fun j ↦ ContinuousLinearMap.fst 𝕜 (E j) (F j)) x,
    mapCLM (fun j ↦ ContinuousLinearMap.snd 𝕜 (E j) (F j)) x)
  invFun p := mapCLM (fun j ↦ ContinuousLinearMap.inl 𝕜 (E j) (F j)) p.1 +
    mapCLM (fun j ↦ ContinuousLinearMap.inr 𝕜 (E j) (F j)) p.2
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := ext fun j ↦ by simp
  right_inv p := by ext <;> simp
  continuous_toFun := (mapCLM _).continuous.prodMk (mapCLM _).continuous
  continuous_invFun := ((mapCLM _).continuous.comp continuous_fst).add
    ((mapCLM _).continuous.comp continuous_snd)

@[simp] theorem prodEquiv_symm_apply (p : LCDirectSum E × LCDirectSum F) (j : J) :
    (prodEquiv (𝕜 := 𝕜)).symm p j = (p.1 j, p.2 j) := by
  change (mapCLM (fun j ↦ ContinuousLinearMap.inl 𝕜 (E j) (F j)) p.1 +
    mapCLM (fun j ↦ ContinuousLinearMap.inr 𝕜 (E j) (F j)) p.2 : LCDirectSum _) j = _
  simp

section Sigma

variable {ι : Type*} {κ : ι → Type*} {E : ∀ i, κ i → Type*} [∀ i j, AddCommGroup (E i j)]
  [∀ i j, TopologicalSpace (E i j)] [∀ i j, IsTopologicalAddGroup (E i j)]
  {𝕜 : Type*} [Semiring 𝕜] [∀ i j, Module 𝕜 (E i j)]

open Classical in
/-- **Associativity of direct sums** ([GN26, Lemma B.13.2(b)]):
`⊕_{(i, j)} E i j ≅ ⊕_i ⊕_j E i j` as topological vector spaces, for any index sets (for the box
topology, no countability is needed): the boxes correspond to boxes of boxes. -/
def sigmaEquiv : LCDirectSum (fun p : Σ i, κ i ↦ E p.1 p.2) ≃L[𝕜]
    LCDirectSum fun i ↦ LCDirectSum (E i) where
  __ := DFinsupp.sigmaCurryLEquiv (R := 𝕜) (M := E)
  continuous_toFun := by
    let φ : LCDirectSum (fun p : Σ i, κ i ↦ E p.1 p.2) →+ LCDirectSum fun i ↦ LCDirectSum (E i) :=
      (DFinsupp.sigmaCurryLEquiv (R := 𝕜) (M := E)).toLinearMap.toAddMonoidHom
    refine continuous_of_continuousAt_zero φ ?_
    rw [ContinuousAt, map_zero]
    refine ((nhds_zero_hasBasis).tendsto_iff (nhds_zero_hasBasis)).2 fun W hW ↦ ?_
    choose V hV hVW using fun i ↦ (nhds_zero_hasBasis (E := E i)).mem_iff.1 (hW i)
    exact ⟨fun p ↦ V p.1 p.2, fun p ↦ hV p.1 p.2, fun x hx i ↦ hVW i fun j ↦ hx ⟨i, j⟩⟩
  continuous_invFun := by
    let ψ : (LCDirectSum fun i ↦ LCDirectSum (E i)) →+ LCDirectSum (fun p : Σ i, κ i ↦ E p.1 p.2) :=
      (DFinsupp.sigmaCurryLEquiv (R := 𝕜) (M := E)).symm.toLinearMap.toAddMonoidHom
    refine continuous_of_continuousAt_zero ψ ?_
    rw [ContinuousAt, map_zero]
    refine ((nhds_zero_hasBasis).tendsto_iff (nhds_zero_hasBasis)).2 fun V hV ↦ ?_
    exact ⟨fun i ↦ box fun j ↦ V ⟨i, j⟩, fun i ↦ box_mem_nhds fun j ↦ hV ⟨i, j⟩,
      fun y hy p ↦ hy p.1 p.2⟩

@[simp] theorem sigmaEquiv_apply (x : LCDirectSum fun p : Σ i, κ i ↦ E p.1 p.2) (i : ι)
    (j : κ i) : sigmaEquiv (𝕜 := 𝕜) x i j = x ⟨i, j⟩ := by
  rfl

end Sigma

end Maps

/-! ### Differential calculus ([GN26, Section 2.8]) -/

section Calculus

theorem _root_.LocallyConvex.Analysis.dMB_zero_dir {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (x : X) : dMB f (x, 0) = 0 := by
  have h : HasDirDerivAt f x 0 0 := by
    simp only [HasDirDerivAt, smul_zero, add_zero, sub_self]
    exact tendsto_const_nhds
  exact h.dMB_eq

universe u

variable {F : J → Type*} [∀ j, AddCommGroup (F j)] [∀ j, Module ℝ (F j)]
  [∀ j, TopologicalSpace (F j)] [∀ j, IsTopologicalAddGroup (F j)] [∀ j, ContinuousSMul ℝ (F j)]
  [∀ j, T2Space (F j)]

section Dir

variable [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, IsTopologicalAddGroup (E j)] [∀ j, ContinuousSMul ℝ (E j)]

omit [∀ (j : J), IsTopologicalAddGroup (F j)] [∀ (j : J), ContinuousSMul ℝ (F j)]
  [∀ (j : J), IsTopologicalAddGroup (E j)] [∀ (j : J), ContinuousSMul ℝ (E j)] in
omit [(j : J) → TopologicalSpace (E j)] in
theorem dMB_map_zero (f : ∀ j, E j → F j) (S : Finset J) :
    ∀ j ∉ S, dMB (f j) (0 : E j × E j) = 0 := fun j _ ↦ dMB_zero_dir (f j) 0

omit [∀ (j : J), ContinuousSMul ℝ (F j)] [∀ (j : J), ContinuousSMul ℝ (E j)] in
/-- **The directional derivatives of a direct sum of maps** ([GN26, (2.131)]):
`d(⊕ f j)(x, h) = (d(f j)(x j, h j))_j`. -/
theorem hasDirDerivAt_map {f : ∀ j, E j → F j} {S : Finset J} (hS : ∀ j ∉ S, f j 0 = 0)
    {x h : LCDirectSum E} (hd : ∀ j, HasDirDerivAt (f j) (x j) (h j) (dMB (f j) (x j, h j))) :
    HasDirDerivAt (map f S hS) x h
      (map (fun j ↦ dMB (f j)) S (dMB_map_zero f S) ((prodEquiv (𝕜 := ℝ)).symm (x, h))) := by
  classical
  obtain ⟨s₁, hs₁⟩ := exists_finset x
  obtain ⟨s₂, hs₂⟩ := exists_finset h
  set M := S ∪ s₁ ∪ s₂
  rw [HasDirDerivAt, (nhds_hasBasis _).tendsto_right_iff]
  intro W hW
  have hfin : ∀ j ∈ M, ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      t⁻¹ • (f j (x j + t • h j) - f j (x j)) ∈ W j := fun j _ ↦ hd j (by simpa using hW j)
  filter_upwards [(M.eventually_all).2 hfin] with t ht j
  simp only [smul_apply, sub_apply, map_apply, add_apply]
  by_cases hj : j ∈ M
  · exact ht j hj
  · have hjS : j ∉ S := fun h' ↦ hj (by simp [M, h'])
    have hx0 : x j = 0 := hs₁ j fun h' ↦ hj (by simp [M, h'])
    have hh0 : h j = 0 := hs₂ j fun h' ↦ hj (by simp [M, h'])
    have hW0 := mem_of_mem_nhds (hW j)
    simp only [map_apply, prodEquiv_symm_apply, hx0, hh0] at hW0
    rw [hx0, hh0, smul_zero, add_zero, sub_self, smul_zero]
    rwa [dMB_zero_dir] at hW0

end Dir

omit [∀ (j : J), ContinuousSMul ℝ (F j)] in
/-- **Direct sums of `C^k` maps are `C^k`** ([GN26, Proposition 2.8.1]): if
`f j : U j → F j` is `C^k` on the open set `U j ⊆ E j` for each `j`, and `f j 0 = 0` for all but
finitely many `j`, then `⊕_j f j` is `C^k` on the open set `⊕_j U j`. -/
theorem contDiffMBOn_map : ∀ (k : ℕ) {E : J → Type u} [∀ j, AddCommGroup (E j)]
    [∀ j, Module ℝ (E j)] [∀ j, TopologicalSpace (E j)] [∀ j, IsTopologicalAddGroup (E j)]
    [∀ j, ContinuousSMul ℝ (E j)] [∀ j, LocallyConvexSpace ℝ (E j)] [∀ j, T2Space (E j)]
    {f : ∀ j, E j → F j} {S : Finset J} (hS : ∀ j ∉ S, f j 0 = 0) {U : ∀ j, Set (E j)},
    (∀ j, IsOpen (U j)) → (∀ j, ContDiffMBOn k (f j) (U j)) →
      ContDiffMBOn k (map f S hS) (box U) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ _ _ _ f S hS U hU hf
    exact continuousOn_map hU hf
  | succ k ih =>
    intro E _ _ _ _ _ _ _ f S hS U hU hf
    set Φ := (prodEquiv (𝕜 := ℝ) (E := E) (F := E)).symm
    have hderiv : ∀ x ∈ box U, ∀ h, HasDirDerivAt (map f S hS) x h
        (map (fun j ↦ dMB (f j)) S (dMB_map_zero f S) (Φ (x, h))) := fun x hx h ↦
      hasDirDerivAt_map hS fun j ↦ (hf j).hasDirDerivAt (hx j) (h j)
    refine ⟨continuousOn_map hU fun j ↦ (hf j).continuousOn, fun x hx h ↦ ?_, ?_⟩
    · rw [(hderiv x hx h).dMB_eq]
      exact hderiv x hx h
    · have hU' : ∀ j, IsOpen (U j ×ˢ (univ : Set (E j))) := fun j ↦ (hU j).prod isOpen_univ
      have hIH := ih (E := fun j ↦ E j × E j) (f := fun j ↦ dMB (f j)) (dMB_map_zero f S) hU'
        fun j ↦ (hf j).2.2
      have hc := ContDiffMBOn.comp_clm Φ.toContinuousLinearMap (isOpen_box hU') hIH
      have hset : Φ.toContinuousLinearMap ⁻¹' box (fun j ↦ U j ×ˢ univ) =
          box U ×ˢ univ := by
        ext p
        simp [Φ, mem_box]
      rw [hset] at hc
      exact hc.congr_of_isOpen ((isOpen_box hU).prod isOpen_univ)
        fun p hp ↦ ((hderiv p.1 hp.1 p.2).dMB_eq).symm

omit [∀ (j : J), ContinuousSMul ℝ (F j)] in
/-- **Direct sums of smooth maps are smooth** ([GN26, Proposition 2.8.1], `k = ∞`). -/
theorem smoothMBOn_map {E : J → Type u} [∀ j, AddCommGroup (E j)]
    [∀ j, Module ℝ (E j)] [∀ j, TopologicalSpace (E j)] [∀ j, IsTopologicalAddGroup (E j)]
    [∀ j, ContinuousSMul ℝ (E j)] [∀ j, LocallyConvexSpace ℝ (E j)] [∀ j, T2Space (E j)]
    {f : ∀ j, E j → F j} {S : Finset J} (hS : ∀ j ∉ S, f j 0 = 0) {U : ∀ j, Set (E j)}
    (hU : ∀ j, IsOpen (U j)) (hf : ∀ j, SmoothMBOn (f j) (U j)) :
    SmoothMBOn (map f S hS) (box U) := fun k ↦ contDiffMBOn_map k hS hU fun j ↦ hf j k

end Calculus

/-! ### Real analytic maps -/

section Analytic

open Complexification

universe v

variable {E : J → Type u} [∀ j, AddCommGroup (E j)] [∀ j, Module ℝ (E j)]
  [∀ j, TopologicalSpace (E j)] [∀ j, IsTopologicalAddGroup (E j)] [∀ j, ContinuousSMul ℝ (E j)]
  [∀ j, LocallyConvexSpace ℝ (E j)] [∀ j, T2Space (E j)]
  {G : J → Type v} [∀ j, AddCommGroup (G j)] [∀ j, Module ℝ (G j)]
  [∀ j, TopologicalSpace (G j)] [∀ j, IsTopologicalAddGroup (G j)] [∀ j, ContinuousSMul ℝ (G j)]
  [∀ j, LocallyConvexSpace ℝ (G j)] [∀ j, T2Space (G j)]

variable (E) in
/-- `(⊕_j E j)_ℂ → ⊕_j (E j)_ℂ`, `p ↦ (Re p j + i Im p j)_j` (cf.
[GN26, Lemma B.13.2(c)]). -/
def complexifyOut : Complexification (LCDirectSum E) →L[ℂ]
    LCDirectSum fun j ↦ Complexification (E j) where
  toFun p := mapCLM (fun j ↦ mkCLM (ContinuousLinearMap.id ℝ (E j)) 0) (re p) +
    mapCLM (fun j ↦ mkCLM 0 (ContinuousLinearMap.id ℝ (E j))) (im p)
  map_add' p q := by
    simp only [re_add, im_add, map_add]
    abel
  map_smul' c p := by
    ext j <;> simp [mkCLM] <;> abel
  cont := ((mapCLM _).continuous.comp continuous_re).add ((mapCLM _).continuous.comp continuous_im)

omit [∀ (j : J), ContinuousSMul ℝ (E j)] [∀ (j : J), LocallyConvexSpace ℝ (E j)]
  [∀ (j : J), T2Space (E j)] in
@[simp] theorem complexifyOut_apply (p : Complexification (LCDirectSum E)) (j : J) :
    complexifyOut E p j = mk (re p j) (im p j) := by
  change (mapCLM (fun j ↦ mkCLM (ContinuousLinearMap.id ℝ (E j)) 0) (re p) +
    mapCLM (fun j ↦ mkCLM 0 (ContinuousLinearMap.id ℝ (E j))) (im p) :
      LCDirectSum fun j ↦ Complexification (E j)) j = _
  ext <;> simp [mkCLM]

variable (G) in
/-- `⊕_j (G j)_ℂ → (⊕_j G j)_ℂ`, `q ↦ (Re q j)_j + i (Im q j)_j`. -/
def complexifyIn : (LCDirectSum fun j ↦ Complexification (G j)) →L[ℂ]
    Complexification (LCDirectSum G) where
  toFun q := mk (mapCLM (fun j ↦ (reCLM : Complexification (G j) →L[ℝ] G j)) q)
    (mapCLM (fun j ↦ (imCLM : Complexification (G j) →L[ℝ] G j)) q)
  map_add' p q := by ext <;> simp
  map_smul' c q := by ext <;> simp
  cont := continuous_mk (mapCLM _).continuous (mapCLM _).continuous

omit [∀ (j : J), ContinuousSMul ℝ (G j)] [∀ (j : J), LocallyConvexSpace ℝ (G j)]
  [∀ (j : J), T2Space (G j)] in
@[simp] theorem re_complexifyIn (q : LCDirectSum fun j ↦ Complexification (G j)) (j : J) :
    re (complexifyIn G q) j = re (q j) := by
  simp [complexifyIn]

omit [∀ (j : J), ContinuousSMul ℝ (G j)] [∀ (j : J), LocallyConvexSpace ℝ (G j)]
  [∀ (j : J), T2Space (G j)] in
@[simp] theorem im_complexifyIn (q : LCDirectSum fun j ↦ Complexification (G j)) (j : J) :
    im (complexifyIn G q) j = im (q j) := by
  simp [complexifyIn]

/-- **Direct sums of holomorphic maps are complex analytic** ([GN26, proof of Proposition 2.8.1]).
-/
theorem complexAnalyticOn_map {g : ∀ j, Complexification (E j) → Complexification (G j)}
    {S : Finset J} (hS : ∀ j ∉ S, g j 0 = 0) {V : ∀ j, Set (Complexification (E j))}
    (hV : ∀ j, IsOpen (V j)) (hg : ∀ j, ComplexAnalyticOn (g j) (V j)) :
    ComplexAnalyticOn (map g S hS) (box V) := by
  have hhol := fun j ↦ (complexAnalyticOn_iff_holomorphicOn (hV j)).1 (hg j)
  refine (complexAnalyticOn_iff_holomorphicOn (isOpen_box hV)).2
    ⟨smoothMBOn_map hS hV fun j ↦ (hhol j).1, fun x hx c h ↦ ?_⟩
  have hd : ∀ h, HasDirDerivAt (map g S hS) x h
      (map (fun j ↦ dMB (g j)) S (dMB_map_zero g S) ((prodEquiv (𝕜 := ℝ)).symm (x, h))) :=
    fun h ↦ hasDirDerivAt_map hS fun j ↦ ((hhol j).1 1).hasDirDerivAt (hx j) (h j)
  rw [(hd _).dMB_eq, (hd _).dMB_eq]
  refine ext fun j ↦ ?_
  simp only [map_apply, prodEquiv_symm_apply, smul_apply]
  rw [(hhol j).2 _ (hx j) c (h j)]

/-- **Direct sums of real analytic maps are real analytic**
([GN26, Proposition 2.8.1]): if `f j` is real analytic on the open set `U j` for each `j`, with
`0 ∈ U j` and `f j 0 = 0` for all but finitely many `j`, then `⊕_j f j` is real analytic on
`⊕_j U j`. -/
theorem realAnalyticOn_map {f : ∀ j, E j → G j} {S : Finset J} (hS : ∀ j ∉ S, f j 0 = 0)
    {U : ∀ j, Set (E j)} (h0 : ∀ j ∉ S, (0 : E j) ∈ U j)
    (hf : ∀ j, RealAnalyticOn (f j) (U j)) : RealAnalyticOn (map f S hS) (box U) := by
  choose V hV g hg hext using hf
  have hg0 : ∀ j ∉ S, g j 0 = 0 := fun j hj ↦ by
    have h := (hext j 0 (h0 j hj)).2
    rw [map_zero, hS j hj, map_zero] at h
    exact h
  have hG := complexAnalyticOn_map hg0 hV hg
  set W := complexifyOut E ⁻¹' box V
  have hW : IsOpen W := (isOpen_box hV).preimage (complexifyOut E).continuous
  refine ⟨W, hW, complexifyIn G ∘ map g S hg0 ∘ complexifyOut E,
    ((complexifyIn G).complexAnalyticOn isOpen_univ).comp
      (hG.comp ((complexifyOut E).complexAnalyticOn hW) hW (isOpen_box hV) fun _ hz ↦ hz) hW
      isOpen_univ (mapsTo_univ _ _), fun x hx ↦ ⟨fun j ↦ ?_, ?_⟩⟩
  · change complexifyOut E (ofReal x) j ∈ V j
    rw [complexifyOut_apply]
    exact (hext j (x j) (hx j)).1
  · have hj : ∀ j, map g S hg0 (complexifyOut E (ofReal x)) j = ofReal (f j (x j)) := fun j ↦ by
      rw [map_apply, complexifyOut_apply]
      exact (hext j (x j) (hx j)).2
    ext j
    · simp [hj]
    · simp [hj]

end Analytic

/-! ### Inclusions and the universal property -/

section Universal

variable [∀ j, AddCommGroup (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, IsTopologicalAddGroup (E j)] [DecidableEq J]

/-- The inclusion `E j → ⊕_i E i` of a summand. -/
def single (j : J) : E j →+ LCDirectSum E := DFinsupp.singleAddHom E j

omit [∀ (j : J), IsTopologicalAddGroup (E j)] [(j : J) → TopologicalSpace (E j)] in
@[simp] theorem single_apply_same (j : J) (v : E j) : single j v j = v :=
  DFinsupp.single_eq_same

omit [∀ (j : J), IsTopologicalAddGroup (E j)] [(j : J) → TopologicalSpace (E j)] in
theorem single_apply_of_ne {i j : J} (h : i ≠ j) (v : E j) : single j v i = 0 :=
  DFinsupp.single_eq_of_ne h

/-- The inclusions of the summands are continuous ([GN26, Remark B.13.1(c)]). -/
theorem continuous_single (j : J) : Continuous (single (E := E) j) := by
  refine continuous_iff_continuousAt.2 fun v ↦ ?_
  rw [ContinuousAt, (nhds_hasBasis _).tendsto_right_iff]
  intro W hW
  have hWj : W j ∈ 𝓝 v := by simpa using hW j
  filter_upwards [hWj] with w hw i
  rcases eq_or_ne i j with rfl | hij
  · simpa using hw
  · have h0 := mem_of_mem_nhds (hW i)
    rw [single_apply_of_ne hij] at h0 ⊢
    exact h0

/-- **The universal property of the locally convex direct sum**
([GN26, Lemma B.13.2(a)]): for countable `J`, an additive map `α` from `⊕_j E j` to a topological
group is continuous as soon as its restrictions to the summands are. -/
theorem continuous_of_continuous_single [Countable J] {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] (α : LCDirectSum E →+ F)
    (hα : ∀ j, Continuous fun v : E j ↦ α (single j v)) : Continuous α := by
  classical
  refine continuous_of_continuousAt_zero α ?_
  rw [ContinuousAt, map_zero]
  intro Q₀ hQ₀
  -- a sequence of `0`-neighbourhoods with `Q (k + 1) + Q (k + 1) ⊆ Q k`
  choose half hhalf hhalf' using fun s : {s : Set F // s ∈ 𝓝 0} ↦ exists_nhds_zero_half s.2
  let Q : ℕ → {s : Set F // s ∈ 𝓝 0} :=
    fun k ↦ Nat.rec ⟨Q₀, hQ₀⟩ (fun _ q ↦ ⟨half q, hhalf q⟩) k
  have hQadd : ∀ k, ∀ v ∈ (Q (k + 1)).1, ∀ w ∈ (Q (k + 1)).1, v + w ∈ (Q k).1 :=
    fun k ↦ hhalf' (Q k)
  have hQ0 : ∀ k, (0 : F) ∈ (Q k).1 := fun k ↦ mem_of_mem_nhds (Q k).2
  have hQanti : Antitone fun k ↦ (Q k).1 := antitone_nat_of_succ_le fun k v hv ↦ by
    simpa using hQadd k v hv 0 (hQ0 (k + 1))
  -- an injective enumeration of `J`
  obtain ⟨n, hn⟩ := Countable.exists_injective_nat J
  -- sums over finite sets with distinct indices
  have hsum : ∀ (s : Finset J) (y : J → F), (∀ j ∈ s, y j ∈ (Q (n j + 1)).1) →
      ∀ N, (∀ j ∈ s, N ≤ n j) → ∑ j ∈ s, y j ∈ (Q N).1 := by
    intro s y hy
    induction s using Finset.induction_on_max_value (fun j ↦ -(n j : ℤ)) with
    | empty => intro N _; simpa using hQ0 N
    | insert a s has hmin ih =>
      intro N hN
      rw [Finset.sum_insert has]
      have ha : N ≤ n a := hN a (Finset.mem_insert_self a s)
      refine hQadd N _ (hQanti (show N + 1 ≤ n a + 1 by omega)
        (hy a (Finset.mem_insert_self a s))) _ (ih
        (fun j hj ↦ hy j (Finset.mem_insert_of_mem hj)) (N + 1) fun j hj ↦ ?_)
      have h1 : n a ≤ n j := by have := hmin j hj; omega
      have h2 : n a ≠ n j := fun h ↦ has (hn h ▸ hj)
      omega
  -- the box of preimages
  refine mem_map.2 (mem_of_superset (box_mem_nhds (x := 0)
    (V := fun j ↦ (fun v : E j ↦ α (single j v)) ⁻¹' (Q (n j + 1)).1) fun j ↦ ?_) fun x hx ↦ ?_)
  · exact (hα j).continuousAt.preimage_mem_nhds (by simpa using (Q (n j + 1)).2)
  · have hx' : α x = ∑ j ∈ DFinsupp.support x, α (single j (x j)) := by
      have hxs : x = ∑ j ∈ DFinsupp.support x, single j (x j) :=
        (DFinsupp.sum_single (f := (x : Π₀ j, E j))).symm
      conv_lhs => rw [hxs]
      rw [map_sum]
    rw [mem_preimage, hx']
    exact hsum _ _ (fun j _ ↦ hx j) 0 fun _ _ ↦ Nat.zero_le _

end Universal

/-! ### Subspaces, bounded sets and completeness ([GN26, Lemma B.13.2]) -/

section Subspaces

variable [∀ j, AddCommGroup (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, IsTopologicalAddGroup (E j)] {R : Type*} [Ring R] [∀ j, Module R (E j)]
  [∀ j, ContinuousConstSMul R (E j)]

omit [∀ (j : J), ContinuousConstSMul R (E j)] in
/-- **Subspaces** ([GN26, Lemma B.13.2(d)]): for subspaces `F j ⊆ E j`, the topology
induced by `⊕_j E j` on `⊕_j F j` is the box topology: the inclusion is an embedding. -/
theorem isEmbedding_mapCLM_subtype (F : ∀ j, Submodule R (E j)) :
    Topology.IsEmbedding (mapCLM (fun j ↦ (F j).subtypeL) :
      LCDirectSum (fun j ↦ F j) → LCDirectSum E) := by
  refine ⟨Topology.isInducing_iff_nhds.2 fun x ↦ ?_, fun x y h ↦ ext fun j ↦ Subtype.ext ?_⟩
  · refine (nhds_hasBasis x).ext ((nhds_hasBasis _).comap _) (fun W hW ↦ ?_) fun V hV ↦ ?_
    · choose V hV hVW using fun j ↦ (mem_nhds_subtype _ _ _).1 (hW j)
      exact ⟨V, fun j ↦ by simpa using hV j, fun y hy j ↦ hVW j (by simpa using hy j)⟩
    · exact ⟨fun j ↦ (↑) ⁻¹' V j,
        fun j ↦ (continuous_subtype_val.tendsto _) (by simpa using hV j),
        fun y hy j ↦ by simpa using hy j⟩
  · have := congrArg (fun z ↦ z j) h
    simpa using this

end Subspaces

section Bounded

variable [∀ j, AddCommGroup (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, IsTopologicalAddGroup (E j)] [∀ j, Module ℝ (E j)] [∀ j, ContinuousSMul ℝ (E j)]
  [∀ j, T1Space (E j)]

/-- **Bounded sets lie in finite partial sums** ([GN26, Lemma B.13.2(e)]): a bounded subset
of `⊕_j E j` vanishes outside a finite set of indices. -/
theorem exists_finset_of_isVonNBounded {B : Set (LCDirectSum E)}
    (hB : Bornology.IsVonNBounded ℝ B) : ∃ s : Finset J, ∀ x ∈ B, ∀ j ∉ s, x j = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  -- an injective sequence of indices `k n` and points `y n ∈ B` with `y n (k n) ≠ 0`
  choose x hxB j hj hx0 using hcon
  let s : ℕ → Finset J := fun n ↦ Nat.rec ∅ (fun _ t ↦ insert (j t) t) n
  let k : ℕ → J := fun n ↦ j (s n)
  have hks : ∀ m n, m < n → k m ∈ s n := by
    intro m n hmn
    induction n with
    | zero => omega
    | succ n ih =>
      change k m ∈ insert (j (s n)) (s n)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
      · exact Finset.mem_insert_of_mem (ih h)
      · subst h; exact Finset.mem_insert_self _ _
  have hinj : Function.Injective k := by
    intro m n hmn
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h' := hks m n h
      rw [hmn] at h'
      exact hj (s n) h'
    · have h' := hks n m h
      rw [← hmn] at h'
      exact hj (s m) h'
  set y : ℕ → LCDirectSum E := fun n ↦ x (s n)
  have hyB : ∀ n, y n ∈ B := fun n ↦ hxB (s n)
  have hyk : ∀ n, y n (k n) ≠ 0 := fun n ↦ hx0 (s n)
  have hinv : ∀ n, Function.invFun k (k n) = n := fun n ↦ Function.leftInverse_invFun hinj n
  -- the box `W`
  let W : ∀ i, Set (E i) := fun i ↦
    if i ∈ Set.range k then
      {v | (((Function.invFun k i : ℕ) : ℝ) + 1) • v ≠ y (Function.invFun k i) i}
    else univ
  have hW : ∀ i, W i ∈ 𝓝 (0 : E i) := fun i ↦ by
    by_cases hi : i ∈ Set.range k
    · obtain ⟨n, rfl⟩ := hi
      simp only [W, Set.mem_range_self, ↓reduceIte, hinv]
      refine ((continuous_const_smul _).isOpen_preimage _ isOpen_ne).mem_nhds ?_
      simpa using (hyk n).symm
    · simp only [W, hi, ↓reduceIte]
      exact univ_mem
  obtain ⟨r, -, hr⟩ := (hB (box_mem_nhds (x := 0) hW)).exists_pos
  obtain ⟨n, hn⟩ := exists_nat_ge r
  have hsub := hr (((n : ℝ) + 1)) (by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith)
  obtain ⟨w, hw, hwy⟩ := hsub (hyB n)
  have h1 := hw (k n)
  simp only [W, Set.mem_range_self, ↓reduceIte, hinv, Set.mem_ofPred_eq] at h1
  apply h1
  rw [← hwy]
  rfl

end Bounded

section Complete

variable [∀ j, AddCommGroup (E j)] [∀ j, UniformSpace (E j)] [∀ j, IsUniformAddGroup (E j)]

/-- The uniform structure of the topological group `⊕_j E j`. -/
instance : UniformSpace (LCDirectSum E) := IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (LCDirectSum E) := isUniformAddGroup_of_addCommGroup

/-- The evaluation at `j`, as an additive map. -/
def evalAddHom (j : J) : LCDirectSum E →+ E j where
  toFun x := x j
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Completeness** ([GN26, Lemma B.13.2(f)]): a direct sum of complete Hausdorff spaces is
complete. -/
instance [∀ j, CompleteSpace (E j)] [∀ j, T1Space (E j)] : CompleteSpace (LCDirectSum E) := by
  classical
  refine ⟨fun {f} hf ↦ ?_⟩
  have : f.NeBot := hf.1
  have hcont : ∀ j, Tendsto (fun x : LCDirectSum E ↦ x j) f
      (𝓝 (CompleteSpace.complete (hf.map (uniformContinuous_addMonoidHom_of_continuous
        (f := evalAddHom (E := E) j) (continuous_apply j)))).choose) := fun j ↦
    (CompleteSpace.complete (hf.map (uniformContinuous_addMonoidHom_of_continuous
      (f := evalAddHom (E := E) j) (continuous_apply j)))).choose_spec
  set z : ∀ j, E j := fun j ↦ (CompleteSpace.complete (hf.map
    (uniformContinuous_addMonoidHom_of_continuous (f := evalAddHom (E := E) j)
      (continuous_apply j)))).choose
  -- the Cauchy property, read on closed boxes
  have key : ∀ V : ∀ j, Set (E j), (∀ j, V j ∈ 𝓝 0) → (∀ j, IsClosed (V j)) →
      ∃ A ∈ f, ∀ a ∈ A, ∀ j, a j - z j ∈ V j := by
    intro V hV hVc
    have hent : {p : LCDirectSum E × LCDirectSum E | p.2 + -p.1 ∈ box fun j ↦ -V j} ∈
        uniformity (LCDirectSum E) := by
      rw [uniformity_eq_comap_nhds_zero']
      exact preimage_mem_comap (box_mem_nhds (x := 0) fun j ↦ by
        simpa using neg_mem_nhds_zero _ (hV j))
    obtain ⟨A, hA, hAA⟩ := mem_prod_same_iff.1 (hf.2 hent)
    refine ⟨A, hA, fun a ha j ↦ ?_⟩
    have ht : Tendsto (fun b : LCDirectSum E ↦ a j - b j) f (𝓝 (a j - z j)) :=
      tendsto_const_nhds.sub (hcont j)
    refine (hVc j).mem_of_tendsto ht (eventually_of_mem hA fun b hb ↦ ?_)
    have h := hAA (mk_mem_prod ha hb) j
    simp only [add_apply, neg_apply, Set.mem_neg] at h
    simpa [sub_eq_add_neg, add_comm] using h
  -- `z` has finite support
  have hfin : Set.Finite {j | z j ≠ 0} := by
    by_contra hinf
    have hV : ∀ j, ∃ V : Set (E j), V ∈ 𝓝 0 ∧ IsClosed V ∧ (z j ≠ 0 → -z j ∉ V) := fun j ↦ by
      by_cases hj : z j = 0
      · exact ⟨univ, univ_mem, isClosed_univ, fun h ↦ absurd hj h⟩
      · have h0 : (0 : E j) ≠ -z j := by simpa [eq_comm] using hj
        obtain ⟨V, ⟨hV, hVc⟩, hsub⟩ := (closed_nhds_basis (0 : E j)).mem_iff.1
          (isOpen_ne.mem_nhds h0)
        exact ⟨V, hV, hVc, fun _ h ↦ hsub h rfl⟩
    choose V hV hVc hVz using hV
    obtain ⟨A, hA, hAz⟩ := key V hV hVc
    obtain ⟨a, ha⟩ := hf.1.nonempty_of_mem hA
    obtain ⟨s, hs⟩ := exists_finset a
    refine hinf (s.finite_toSet.subset fun j hj ↦ ?_)
    by_contra hjs
    have h := hAz a ha j
    rw [hs j hjs, zero_sub] at h
    exact hVz j hj h
  -- the limit
  let x : LCDirectSum E := DFinsupp.mk hfin.toFinset fun j ↦ z j
  have hx : ∀ j, x j = z j := fun j ↦ by
    change (DFinsupp.mk hfin.toFinset fun j ↦ z j : ∀ j, E j) j = z j
    rw [DFinsupp.mk_apply]
    split_ifs with hj
    · rfl
    · exact (by simpa using hj : z j = 0).symm
  refine ⟨x, fun U hU ↦ ?_⟩
  obtain ⟨W, hW, hWU⟩ := (nhds_hasBasis x).mem_iff.1 hU
  have hW' : ∀ j, (x j + ·) ⁻¹' W j ∈ 𝓝 (0 : E j) := fun j ↦ by
    have := hW j
    rw [← map_add_left_nhds_zero] at this
    exact this
  choose V hV hVW using fun j ↦ (closed_nhds_basis (0 : E j)).mem_iff.1 (hW' j)
  obtain ⟨A, hA, hAz⟩ := key V (fun j ↦ (hV j).1) fun j ↦ (hV j).2
  refine mem_of_superset hA fun a ha ↦ hWU fun j ↦ ?_
  have h := hVW j (hAz a ha j)
  simp only [Set.mem_preimage, hx, add_sub_cancel] at h
  exact h

end Complete

end LCDirectSum

end LocallyConvex.Analysis

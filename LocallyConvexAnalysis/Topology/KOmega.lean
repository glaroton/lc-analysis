/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Topology.DirectLimit

/-!
# `k_ω`-spaces

Reference: [GN26, Example A.7.17, Definition A.7.18 and Remark A.7.19] (p. 891).

`k_ω`-spaces (`IsKOmegaSpace`) and locally `k_ω`-spaces (`IsLocallyKOmegaSpace`) are defined in
`Topology/DirectLimit.lean`. Here we prove their basic properties, for Hausdorff spaces, and that
`k`-spaces are the direct limits of their compact subsets.

## Main definitions

* `homeomorphTopDirectLimitUniv`: the direct limit of the constant sequence `Y ⊆ Y ⊆ ⋯` is
  homeomorphic to `Y`.

## Main results

* `IsKOmegaSpace.of_homeomorph`, `IsLocallyKOmegaSpace.of_homeomorph`: `k_ω`-spaces and locally
  `k_ω`-spaces are invariant under homeomorphisms.
* `IsKOmegaSpace.isLocallyKOmegaSpace`, `isKOmegaSpace_of_sigmaCompactSpace`,
  `isLocallyKOmegaSpace_of_locallyCompactSpace`: `k_ω`-spaces are locally `k_ω`, σ-compact locally
  compact spaces are `k_ω`, and locally compact spaces are locally `k_ω` (Remark A.7.19(a)).
* `topology_eq_of_absorbing`: in a Hausdorff `k_ω`-space, any sequence of compact sets absorbing
  the compact sets has the topology of the space as its direct limit topology (compare
  Remark A.7.19(b)).
* `isKOmegaSpace_iff_exists_topology_eq`: a space is `k_ω` iff it is the direct limit of an
  ascending sequence of compact subspaces (Remark A.7.19(b)).
* `IsLocallyKOmegaSpace.compactlyGeneratedSpace`: locally `k_ω`-spaces are `k`-spaces
  (Remark A.7.19(c)).
* `compactlyGeneratedSpace_iff_topology_eq`: a Hausdorff space is a `k`-space iff it is the direct
  limit of its compact subsets (Example A.7.17).

## Implementation notes

* GN's `k`-spaces are Hausdorff (Example A.7.17); `IsKOmegaSpace` does not include the Hausdorff
  property, which is assumed where needed.
* Locally compact spaces are locally `k_ω` because, as Hausdorff steps of the constant sequence
  `Y ⊆ Y ⊆ ⋯`, they form a compactifying sequence (Remark A.7.2(c)), whose direct limit is `Y` and
  is locally `k_ω` by Proposition A.7.20.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u

open TopDirectLimit

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]

/-- `k_ω`-spaces are invariant under homeomorphisms. -/
theorem IsKOmegaSpace.of_homeomorph (e : Y ≃ₜ Z) (h : IsKOmegaSpace Y) : IsKOmegaSpace Z := by
  have := h.1
  obtain ⟨K, hKc, hK⟩ := h.2
  refine ⟨compactlyGeneratedSpace_of_coinduced e.continuous e.coinduced_eq.symm,
    fun n ↦ e '' K n, fun n ↦ (hKc n).image e.continuous, fun L hL ↦ ?_⟩
  obtain ⟨n, hn⟩ := hK _ (hL.image e.symm.continuous)
  refine ⟨n, fun z hz ↦ ⟨e.symm z, hn ⟨z, hz, rfl⟩, e.apply_symm_apply z⟩⟩

/-- Locally `k_ω`-spaces are invariant under homeomorphisms. -/
theorem IsLocallyKOmegaSpace.of_homeomorph (e : Y ≃ₜ Z) (h : IsLocallyKOmegaSpace Y) :
    IsLocallyKOmegaSpace Z := by
  have := h.1
  refine ⟨e.symm.isEmbedding.t2Space, fun z ↦ ?_⟩
  obtain ⟨V, hV, hzV, hVk⟩ := h.2 (e.symm z)
  exact ⟨e '' V, e.isOpenMap V hV, ⟨e.symm z, hzV, e.apply_symm_apply z⟩,
    hVk.of_homeomorph (e.image V)⟩

variable [T2Space Y]

/-- **`k_ω`-spaces are locally `k_ω`** ([GN26, Remark A.7.19(a)]). -/
theorem IsKOmegaSpace.isLocallyKOmegaSpace (h : IsKOmegaSpace Y) : IsLocallyKOmegaSpace Y :=
  ⟨inferInstance, fun y ↦ ⟨univ, isOpen_univ, mem_univ y,
    h.of_homeomorph (Homeomorph.Set.univ Y).symm⟩⟩

/-- **σ-compact locally compact spaces are `k_ω`** ([GN26, Remark A.7.19(a)]): a compact
exhaustion absorbs every compact set. -/
theorem isKOmegaSpace_of_sigmaCompactSpace [LocallyCompactSpace Y] [SigmaCompactSpace Y] :
    IsKOmegaSpace Y :=
  ⟨inferInstance, CompactExhaustion.choice Y, fun n ↦ (CompactExhaustion.choice Y).isCompact n,
    fun _ hL ↦ (CompactExhaustion.choice Y).exists_superset_of_isCompact hL⟩

/-- The direct limit of the constant sequence `Y ⊆ Y ⊆ ⋯` is `Y`. -/
def homeomorphTopDirectLimitUniv : TopDirectLimit (fun _ : ℕ ↦ (univ : Set Y)) ≃ₜ Y where
  toEquiv := Equiv.refl _
  continuous_toFun := continuous_iff.2 fun _ ↦ continuous_subtype_val
  continuous_invFun := continuous_def.2 fun _ hM ↦
    (Homeomorph.Set.univ Y).isOpen_preimage.1 (isOpen_iff.1 hM 0)

/-- **Locally compact spaces are locally `k_ω`** ([GN26, Remark A.7.19(a)]). -/
theorem isLocallyKOmegaSpace_of_locallyCompactSpace [LocallyCompactSpace Y] :
    IsLocallyKOmegaSpace Y := by
  have hS : IsDirectSeq fun _ : ℕ ↦ (univ : Set Y) :=
    ⟨fun _ _ _ ↦ subset_rfl, fun y ↦ ⟨0, mem_univ y⟩, fun _ ↦ continuous_inclusion _⟩
  have : ∀ _ : ℕ, LocallyCompactSpace (univ : Set Y) := fun _ ↦
    isClosed_univ.locallyCompactSpace
  exact hS.isCompactifying_of_locallyCompactSpace.isLocallyKOmegaSpace.of_homeomorph
    homeomorphTopDirectLimitUniv

/-- In a Hausdorff `k_ω`-space, **any sequence of compact sets absorbing the compact sets is a
`k_ω`-sequence**: the topology is the direct limit topology of the sequence (compare
[GN26, Remark A.7.19(b)]). -/
theorem topology_eq_of_absorbing (hY : IsKOmegaSpace Y) {K : ℕ → Set Y}
    (hKc : ∀ n, IsCompact (K n)) (hK : ∀ L, IsCompact L → ∃ n, L ⊆ K n) :
    TopDirectLimit.topology K = ‹TopologicalSpace Y› := by
  have := hY.1
  refine TopologicalSpace.ext_iff_isClosed.2 fun F ↦ ?_
  refine (@isClosed_iff Y ℕ K _ F).trans ⟨fun hF ↦ CompactlyGeneratedSpace.isClosed
    fun L hL ↦ ?_, fun hF n ↦ hF.preimage continuous_subtype_val⟩
  obtain ⟨n, hn⟩ := hK L hL
  have : CompactSpace (K n) := isCompact_iff_compactSpace.1 (hKc n)
  have hFn : IsClosed (F ∩ K n) := by
    have hc : IsCompact ((Subtype.val : K n → Y) ⁻¹' F) := (hF n).isCompact
    have := (hc.image continuous_subtype_val).isClosed
    rwa [image_preimage_eq_inter_range, Subtype.range_coe] at this
  have : F ∩ L = (F ∩ K n) ∩ L := by rw [inter_assoc, inter_eq_right.2 hn]
  rw [this]
  exact hFn.inter hL.isClosed

/-- **`k_ω`-spaces are the direct limits of ascending sequences of compact spaces**
([GN26, Remark A.7.19(b)]), for Hausdorff spaces. A compact subset of the direct limit lies
in a step (Lemma A.7.6(e)), and a set whose traces on the steps are closed is closed in a
`k`-space. -/
theorem isKOmegaSpace_iff_exists_topology_eq :
    IsKOmegaSpace Y ↔ ∃ K : ℕ → Set Y, Monotone K ∧ (∀ n, IsCompact (K n)) ∧
      (∀ y, ∃ n, y ∈ K n) ∧ TopDirectLimit.topology K = ‹TopologicalSpace Y› := by
  constructor
  · rintro ⟨hCG, K, hKc, hK⟩
    set K' : ℕ → Set Y := fun n ↦ ⋃ m ∈ Iic n, K m
    have hK'c : ∀ n, IsCompact (K' n) := fun n ↦ (finite_Iic n).isCompact_biUnion fun m _ ↦ hKc m
    have hKK' : ∀ n, K n ⊆ K' n := fun n ↦ subset_biUnion_of_mem (u := K) (mem_Iic.2 le_rfl)
    refine ⟨K', fun m n hmn ↦ biUnion_subset_biUnion_left (Iic_subset_Iic.2 hmn), hK'c,
      fun y ↦ ?_, ?_⟩
    · obtain ⟨n, hn⟩ := hK _ isCompact_singleton
      exact ⟨n, hKK' n (hn rfl)⟩
    exact topology_eq_of_absorbing ⟨hCG, K, hKc, hK⟩ hK'c fun L hL ↦
      let ⟨n, hn⟩ := hK L hL; ⟨n, hn.trans (hKK' n)⟩
  · rintro ⟨K, hKmono, hKc, hcover, h⟩
    refine ⟨compactlyGeneratedSpace_of_isClosed_of_t2 fun F hF ↦ ?_, K, hKc, fun L hL ↦ ?_⟩
    · have : IsClosed[TopDirectLimit.topology K] F := (@isClosed_iff Y ℕ K _ F).2 fun n ↦ by
        have := (hF (K n) (hKc n)).preimage (continuous_subtype_val (p := (· ∈ K n)))
        rwa [preimage_inter, Subtype.coe_preimage_self, inter_univ] at this
      rwa [h] at this
    · have hS : IsDirectSeq K := ⟨hKmono, hcover, fun _ ↦ continuous_inclusion _⟩
      have hL' : @IsCompact Y (TopDirectLimit.topology K) L := by rw [h]; exact hL
      exact hS.exists_subset_of_isCompact hL'

/-- **`k`-spaces are the direct limits of their compact subsets**
([GN26, Example A.7.17]), for Hausdorff spaces: a set is closed in the direct limit of the compact
subsets iff it meets every compact set in a closed set. -/
theorem compactlyGeneratedSpace_iff_topology_eq :
    CompactlyGeneratedSpace Y ↔
      TopDirectLimit.topology (fun K : {K : Set Y // IsCompact K} ↦ (K : Set Y)) =
        ‹TopologicalSpace Y› := by
  -- traces on compact sets
  have htr : ∀ (K : {K : Set Y // IsCompact K}) (F : Set Y),
      IsClosed ((Subtype.val : ↥(K : Set Y) → Y) ⁻¹' F) ↔ IsClosed (F ∩ K) := fun K F ↦ by
    constructor
    · intro hF
      have : CompactSpace ↥(K : Set Y) := isCompact_iff_compactSpace.1 K.2
      have := (hF.isCompact.image continuous_subtype_val).isClosed
      rwa [image_preimage_eq_inter_range, Subtype.range_coe] at this
    · intro hF
      have := hF.preimage (continuous_subtype_val (p := (· ∈ (K : Set Y))))
      rwa [preimage_inter, Subtype.coe_preimage_self, inter_univ] at this
  constructor
  · intro hCG
    refine TopologicalSpace.ext_iff_isClosed.2 fun F ↦ ?_
    refine (@isClosed_iff Y _ (fun K : {K : Set Y // IsCompact K} ↦ (K : Set Y)) _ F).trans
      ⟨fun hF ↦ CompactlyGeneratedSpace.isClosed fun L hL ↦ (htr ⟨L, hL⟩ F).1 (hF ⟨L, hL⟩),
        fun hF K ↦ (htr K F).2 (hF.inter K.2.isClosed)⟩
  · intro h
    refine compactlyGeneratedSpace_of_isClosed_of_t2 fun F hF ↦ ?_
    have : IsClosed[TopDirectLimit.topology (fun K : {K : Set Y // IsCompact K} ↦ (K : Set Y))] F :=
      (@isClosed_iff Y _ (fun K : {K : Set Y // IsCompact K} ↦ (K : Set Y)) _ F).2 fun K ↦
        (htr K F).2 (hF _ K.2)
    rwa [h] at this

omit [T2Space Y] in
/-- **Locally `k_ω`-spaces are `k`-spaces** ([GN26, Remark A.7.19(c)]): closedness is
checked on the open `k_ω` neighbourhoods. -/
theorem IsLocallyKOmegaSpace.compactlyGeneratedSpace (h : IsLocallyKOmegaSpace Y) :
    CompactlyGeneratedSpace Y := by
  have := h.1
  refine compactlyGeneratedSpace_of_isClosed_of_t2 fun F hF ↦ ?_
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V, hV, hxV, hVk⟩ := h.2 x
  have := hVk.1
  -- the trace of `F` on `V` is closed in `V`
  have hFV : IsClosed ((↑) ⁻¹' F : Set V) := CompactlyGeneratedSpace.isClosed fun L hL ↦ by
    have hL' := hL.image continuous_subtype_val
    have : ((↑) ⁻¹' F : Set V) ∩ L = (↑) ⁻¹' (F ∩ (↑) '' L) := by
      rw [preimage_inter, Subtype.val_injective.preimage_image]
    rw [this]
    exact (hF _ hL').preimage continuous_subtype_val
  refine ⟨(↑) '' ((↑) ⁻¹' F : Set V)ᶜ, ?_, hV.isOpenMap_subtype_val _ hFV.isOpen_compl,
    ⟨⟨x, hxV⟩, show (⟨x, hxV⟩ : V) ∈ ((↑) ⁻¹' F : Set V)ᶜ from hx, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hy

end LocallyConvex.Analysis

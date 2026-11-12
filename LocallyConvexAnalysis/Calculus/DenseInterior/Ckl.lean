/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.CklMaps
public import LocallyConvexAnalysis.Calculus.DenseInterior.Rules

/-!
# `C^{k,ℓ}` maps on products of sets with dense interior

Reference: [GN26, §1.7], pp. 94–95 and 108. This file extends
`LocallyConvexAnalysis.Calculus.CklMaps` (open `U`, `V`) to locally convex subsets `U ⊆ E₁`,
`V ⊆ E₂` with dense interior, as in Definition 1.7.17.

## Main definitions

* `ContDiffLC₂ k ℓ f U V`: `f` is `C^{k,ℓ}` on `U × V`: it is continuous on `U × V`, it is
  `C^{k,ℓ}` on `U⁰ × V⁰`, and the mixed differentials `d^(i,j) (f|U⁰×V⁰)`, `i ≤ k`, `j ≤ ℓ`,
  extend to continuous maps on `U × V × E₁^i × E₂^j`.
* `iteratedDLC₂ i j f U V`: the continuous extension of `d^(i,j) (f|U⁰×V⁰)`
  (`ContDiffLC₂.continuousOn_iteratedDLC₂`, `iteratedDLC₂_eqOn_of_continuousOn`).

## Main results

* `contDiffLC₂_iff`: `ContDiffLC₂` is [GN26, Definition 1.7.17], literally.
* `contDiffLC₂_iff_contDiffMBOn₂`: on open sets it agrees with `ContDiffMBOn₂`.
* `iteratedDMB₂_extension_unique`: the extensions `d^(i,j) f` are unique.
* `hasDirDerivAt_of_continuousOn_prod`: a parametrized family of maps with continuous directional
  derivatives keeps them at accumulation points of the parameters (the role of
  [GN26, Lemma 1.4.18]).
* `ContDiffLC₂.contDiffLC_right`: the partial maps `f(x, ·)` are `C^ℓ` on `V` for every `x ∈ U`,
  also on the boundary, with `d^(j) (f(x, ·)) = d^(0,j) f(x, ·)` ([GN26, Lemma 1.7.18]).
* `ContDiffLC₂.contDiffLC_left`: the maps `x ↦ d^(0,j) f(x, y, w)` are `C^k` on `U` for every
  `y ∈ V` ([GN26, Remark 1.7.19(b)]).
* `ContDiffLC.contDiffLC₂`: `C^{k+ℓ}` maps on `U × V` are `C^{k,ℓ}`
  ([GN26, Proposition 1.7.33(a)]).

## Implementation notes

As in `LocallyConvexAnalysis.Calculus.CklMaps`, only finite `k`, `ℓ` are treated. The proofs of
Lemma 1.7.18 and Remark 1.7.19(b) pass to the limit from `U⁰` (resp. `V⁰`) with
`hasDirDerivAt_of_continuousOn_prod`, which rests on the mean value inclusion
(`hasDirDerivAt_of_tendsto`), and conclude with the sufficiency in Lemma 1.4.5
(`contDiffLC_of_extends`).

## See also

* Products and the chain rules (Propositions 1.7.20, 1.7.26 and 1.7.28) are in
  `LocallyConvexAnalysis.Calculus.DenseInterior.CklRules`; the spaces `C^k(V, F)`,
  `C^{k,ℓ}(U × V, F)` and the exponential law (Theorem 1.7.30), in
  `LocallyConvexAnalysis.Calculus.DenseInterior.ExpLaw`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

section Limit

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Limits of parametrized differentiable maps** (compare [GN26, Lemma 1.4.18]). Let
`x₀ ∈ S` lie in the closure of `A ⊆ S`, and let `g, D : X → E → F` be continuous on `S × V` with
`V` open. If `g x` has directional derivative `D x z` in the direction `y` at every `z ∈ V` for
every `x ∈ A`, then so does `g x₀`. -/
theorem hasDirDerivAt_of_continuousOn_prod {X : Type*} [TopologicalSpace X] {S A : Set X}
    {x₀ : X} (hx₀ : x₀ ∈ S) (hA : A ⊆ S) (hcl : x₀ ∈ closure A) {g D : X → E → F}
    {V : Set E} (hV : IsOpen V) {y : E} (hd : ∀ x ∈ A, ∀ z ∈ V, HasDirDerivAt (g x) z y (D x z))
    (hg : ContinuousOn (uncurry g) (S ×ˢ V)) (hD : ContinuousOn (uncurry D) (S ×ˢ V)) {z : E}
    (hz : z ∈ V) : HasDirDerivAt (g x₀) z y (D x₀ z) := by
  have : (𝓝[A] x₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hin : ∀ z ∈ V, Tendsto (fun x ↦ (x, z)) (𝓝[A] x₀) (𝓝[S ×ˢ V] (x₀, z)) := by
    intro z hz
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.prodMk continuous_const).tendsto x₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx using ⟨hA hx, hz⟩
  have hsl : ∀ x ∈ S, ContinuousOn (D x) V := fun x hx ↦
    hD.comp (continuous_const.prodMk continuous_id).continuousOn fun z hz ↦ ⟨hx, hz⟩
  refine hasDirDerivAt_of_tendsto (l := 𝓝[A] x₀) hV
    (eventually_nhdsWithin_of_forall hd)
    (eventually_nhdsWithin_of_forall fun x hx ↦ hsl x (hA hx))
    (fun z hz ↦ (hg (x₀, z) ⟨hx₀, hz⟩).tendsto.comp (hin z hz)) ?_ (hsl x₀ hx₀) hz
  intro K hKV hK O hO hKO
  have key : ∀ z ∈ K, ∀ᶠ q : X × E in 𝓝 (x₀, z), q.1 ∈ S → q.2 ∈ V → D q.1 q.2 ∈ O := by
    intro z hz
    have h := (hD (x₀, z) ⟨hx₀, hKV hz⟩).preimage_mem_nhdsWithin (hO.mem_nhds (hKO hz))
    rw [mem_nhdsWithin_iff_eventually] at h
    filter_upwards [h] with q hq h1 h2 using hq ⟨h1, h2⟩
  filter_upwards [nhdsWithin_le_nhds (hK.eventually_forall_of_forall_eventually
    (P := fun a b ↦ a ∈ S → b ∈ V → D a b ∈ O) key),
    self_mem_nhdsWithin] with x hx hxA z hz
  exact hx z hz (hA hxA) (hKV hz)

end Limit

section Definition

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F]

/-- **`C^{k,ℓ}` maps on sets with dense interior** ([GN26, Definition 1.7.17, p. 94]):
`f` is continuous on `U × V`, it is `C^{k,ℓ}` on `U⁰ × V⁰` (so the iterated directional
derivatives `d^(i,j) f` exist there, `contDiffMBOn₂_iff`), and each `d^(i,j) (f|U⁰×V⁰)`, `i ≤ k`,
`j ≤ ℓ`, extends to a continuous map on `U × V × E₁^i × E₂^j`. The extension is unique
(`iteratedDMB₂_extension_unique`). For `U`, `V` meant to be locally convex subsets with dense
interior. -/
def ContDiffLC₂ (k ℓ : ℕ) (f : E₁ × E₂ → F) (U : Set E₁) (V : Set E₂) : Prop :=
  ContinuousOn f (U ×ˢ V) ∧ ContDiffMBOn₂ k ℓ f (interior U) (interior V) ∧
    ∀ i ≤ k, ∀ j ≤ ℓ, ∃ D : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) → F,
      ContinuousOn D ((U ×ˢ V) ×ˢ univ) ∧
        EqOn D (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ)

open scoped Classical in
/-- The mixed differential `d^(i,j) f : U × V × E₁^i × E₂^j → F` on sets with dense interior:
`iteratedDMB₂ i j f` over `U⁰ × V⁰`, and its limit from there at the other points (junk value where
the limit does not exist). For `C^{k,ℓ}` maps it is the continuous extension of
`d^(i,j) (f|U⁰×V⁰)` (`ContDiffLC₂.continuousOn_iteratedDLC₂`). -/
def iteratedDLC₂ (i j : ℕ) (f : E₁ × E₂ → F) (U : Set E₁) (V : Set E₂)
    (p : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂)) : F :=
  if p.1 ∈ interior U ×ˢ interior V then iteratedDMB₂ i j f p
  else limUnder (𝓝[(interior U ×ˢ interior V) ×ˢ univ] p) (iteratedDMB₂ i j f)

omit [ContinuousSMul ℝ F] in
theorem iteratedDLC₂_eqOn_interior (i j : ℕ) (f : E₁ × E₂ → F) (U : Set E₁) (V : Set E₂) :
    EqOn (iteratedDLC₂ i j f U V) (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ) :=
  fun p hp ↦ by simp [iteratedDLC₂, hp.1]

end Definition

section Results

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

/-- **[GN26, Definition 1.7.17]**, literally: `f` is continuous, the iterated directional
derivatives defining `d^(i,j) f` exist on `U⁰ × V⁰`, and they extend continuously to
`U × V × E₁^i × E₂^j`. -/
theorem contDiffLC₂_iff :
    ContDiffLC₂ k ℓ f U V ↔ ContinuousOn f (U ×ˢ V) ∧
      (∀ j < ℓ, ∀ x ∈ interior U, ∀ y ∈ interior V, ∀ w : Fin (j + 1) → E₂,
        HasDirDerivAt (fun y' ↦ iteratedDMB₂ 0 j f ((x, y'), Fin.elim0, Fin.init w)) y
          (w (Fin.last j)) (iteratedDMB₂ 0 (j + 1) f ((x, y), Fin.elim0, w))) ∧
      (∀ i < k, ∀ j ≤ ℓ, ∀ x ∈ interior U, ∀ y ∈ interior V, ∀ (v : Fin (i + 1) → E₁)
        (w : Fin j → E₂), HasDirDerivAt (fun x' ↦ iteratedDMB₂ i j f ((x', y), Fin.init v, w)) x
          (v (Fin.last i)) (iteratedDMB₂ (i + 1) j f ((x, y), v, w))) ∧
      ∀ i ≤ k, ∀ j ≤ ℓ, ∃ D : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) → F,
        ContinuousOn D ((U ×ˢ V) ×ˢ univ) ∧
          EqOn D (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ) := by
  rw [ContDiffLC₂, contDiffMBOn₂_iff isOpen_interior isOpen_interior]
  constructor
  · rintro ⟨hc, ⟨h1, h2, -⟩, hD⟩
    exact ⟨hc, h1, h2, hD⟩
  · rintro ⟨hc, h1, h2, hD⟩
    refine ⟨hc, ⟨h1, h2, fun i hi j hj ↦ ?_⟩, hD⟩
    obtain ⟨D, hDc, hDe⟩ := hD i hi j hj
    refine (hDc.mono (prod_mono (prod_mono interior_subset interior_subset) le_rfl)).congr
      fun p hp ↦ (hDe hp).symm

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- On open sets, `ContDiffLC₂` is `ContDiffMBOn₂`. -/
theorem contDiffLC₂_iff_contDiffMBOn₂ (hU : IsOpen U) (hV : IsOpen V) :
    ContDiffLC₂ k ℓ f U V ↔ ContDiffMBOn₂ k ℓ f U V := by
  rw [ContDiffLC₂, hU.interior_eq, hV.interior_eq]
  refine ⟨fun h ↦ h.2.1, fun h ↦ ⟨?_, h, fun i hi j hj ↦ ⟨_, h.continuousOn i hi j hj,
    fun _ _ ↦ rfl⟩⟩⟩
  exact (h.continuousOn 0 (Nat.zero_le _) 0 (Nat.zero_le _)).comp
    (f := fun p : E₁ × E₂ ↦ (p, ((Fin.elim0 : Fin 0 → E₁), (Fin.elim0 : Fin 0 → E₂))))
    (by fun_prop) fun p hp ↦ ⟨hp, mem_univ _⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- The continuous extensions of `d^(i,j) (f|U⁰×V⁰)` to `U × V × E₁^i × E₂^j` are unique. -/
theorem iteratedDMB₂_extension_unique (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    {i j : ℕ} {D₁ D₂ : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) → F}
    (h₁ : ContinuousOn D₁ ((U ×ˢ V) ×ˢ univ)) (h₂ : ContinuousOn D₂ ((U ×ˢ V) ×ˢ univ))
    (e₁ : EqOn D₁ (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ))
    (e₂ : EqOn D₂ (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ)) :
    EqOn D₁ D₂ ((U ×ˢ V) ×ˢ univ) := by
  refine EqOn.of_subset_closure (fun p hp ↦ (e₁ hp).trans (e₂ hp).symm) h₁ h₂
    (prod_mono (prod_mono interior_subset interior_subset) le_rfl) ?_
  rw [closure_prod_eq, closure_prod_eq, closure_univ]
  exact prod_mono (prod_mono hU hV) le_rfl

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Every continuous extension of `d^(i,j) (f|U⁰×V⁰)` is `iteratedDLC₂ i j f U V`. -/
theorem iteratedDLC₂_eqOn_of_continuousOn (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    {i j : ℕ} {D : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) → F}
    (hD : ContinuousOn D ((U ×ˢ V) ×ˢ univ))
    (heq : EqOn D (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ)) :
    EqOn (iteratedDLC₂ i j f U V) D ((U ×ˢ V) ×ˢ univ) := by
  intro p hp
  by_cases hp1 : p.1 ∈ interior U ×ˢ interior V
  · rw [iteratedDLC₂_eqOn_interior i j f U V ⟨hp1, mem_univ _⟩, heq ⟨hp1, mem_univ _⟩]
  · simp only [iteratedDLC₂, hp1, ite_false]
    have hsub : (interior U ×ˢ interior V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂))) ⊆
        (U ×ˢ V) ×ˢ univ := prod_mono (prod_mono interior_subset interior_subset) le_rfl
    have hcl : p ∈ closure ((interior U ×ˢ interior V) ×ˢ
        (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) := by
      rw [closure_prod_eq, closure_prod_eq, closure_univ]
      exact ⟨⟨hU hp.1.1, hV hp.1.2⟩, mem_univ _⟩
    have : (𝓝[(interior U ×ˢ interior V) ×ˢ univ] p).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hT : Tendsto D (𝓝[(interior U ×ˢ interior V) ×ˢ univ] p) (𝓝 (D p)) :=
      (hD p hp).mono_left (nhdsWithin_mono _ hsub)
    exact (hT.congr' (eventually_nhdsWithin_of_forall heq)).limUnder_eq

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- The mixed differentials `d^(i,j) f = iteratedDLC₂ i j f U V` of a `C^{k,ℓ}` map are continuous
on `U × V × E₁^i × E₂^j`. -/
theorem ContDiffLC₂.continuousOn_iteratedDLC₂ (hf : ContDiffLC₂ k ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ) :
    ContinuousOn (iteratedDLC₂ i j f U V) ((U ×ˢ V) ×ˢ univ) := by
  obtain ⟨D, hDc, hDe⟩ := hf.2.2 i hi j hj
  exact hDc.congr (iteratedDLC₂_eqOn_of_continuousOn hU hV hDc hDe)

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- A criterion for `C^{k,ℓ}`: continuity, `C^{k,ℓ}` on `U⁰ × V⁰`, and continuity of the
`iteratedDLC₂ i j f U V`. -/
theorem ContDiffLC₂.of_continuousOn_iteratedDLC₂ (hc : ContinuousOn f (U ×ˢ V))
    (hf : ContDiffMBOn₂ k ℓ f (interior U) (interior V))
    (hD : ∀ i ≤ k, ∀ j ≤ ℓ, ContinuousOn (iteratedDLC₂ i j f U V) ((U ×ˢ V) ×ˢ univ)) :
    ContDiffLC₂ k ℓ f U V :=
  ⟨hc, hf, fun i hi j hj ↦ ⟨_, hD i hi j hj, iteratedDLC₂_eqOn_interior i j f U V⟩⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `C^{0,0}` maps are the continuous maps. -/
theorem contDiffLC₂_zero_zero_iff : ContDiffLC₂ 0 0 f U V ↔ ContinuousOn f (U ×ˢ V) := by
  refine ⟨fun h ↦ h.1, fun hc ↦ ⟨hc, ?_, fun i hi j hj ↦ ?_⟩⟩
  · have hc' := hc.mono (prod_mono interior_subset interior_subset)
    refine ⟨fun x hx ↦ ?_, fun j hj y hy w ↦ ?_, fun i hi j hj ↦ ?_⟩
    · exact hc'.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy ↦ ⟨hx, hy⟩
    · obtain rfl : j = 0 := by omega
      exact hc'.comp (continuous_id.prodMk continuous_const).continuousOn fun x hx ↦ ⟨hx, hy⟩
    · obtain rfl : i = 0 := by omega
      obtain rfl : j = 0 := by omega
      exact hc'.comp continuous_fst.continuousOn fun p hp ↦ hp.1
  · obtain rfl : i = 0 := by omega
    obtain rfl : j = 0 := by omega
    exact ⟨fun p ↦ f p.1, hc.comp continuous_fst.continuousOn fun p hp ↦ hp.1, fun _ _ ↦ rfl⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- **[GN26, Lemma 1.7.18]** (p. 94). If `f` is `C^{k,ℓ}` on `U × V`, then for every
`x ∈ U` (also on the boundary) the partial map `f(x, ·)` is `C^ℓ` on `V`, and its differentials
are `d^(j) (f(x, ·))(y, w) = d^(0,j) f(x, y, w)` on `V × E₂^j` for any continuous extension
`d^(0,j) f` (1.85). -/
theorem ContDiffLC₂.contDiffLC_right (hf : ContDiffLC₂ k ℓ f U V) (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) {x : E₁} (hx : x ∈ U) :
    ContDiffLC ℓ (fun y ↦ f (x, y)) V ∧ ∀ j ≤ ℓ, ∀ D : (E₁ × E₂) × (Fin 0 → E₁) × (Fin j → E₂) → F,
      ContinuousOn D ((U ×ˢ V) ×ˢ univ) →
      EqOn D (iteratedDMB₂ 0 j f) ((interior U ×ˢ interior V) ×ˢ univ) →
      EqOn (iteratedDLC j (fun y ↦ f (x, y)) V) (fun p ↦ D ((x, p.1), Fin.elim0, p.2))
        (V ×ˢ univ) := by
  obtain ⟨hc, hf₀, hD⟩ := hf
  choose G hGc hGe using fun j (hj : j ≤ ℓ) ↦ hD 0 (Nat.zero_le k) j hj
  have hxcl : x ∈ closure (interior U) := hU hx
  have hGe' : ∀ j (hj : j ≤ ℓ), ∀ x' ∈ interior U, ∀ y ∈ interior V, ∀ w : Fin j → E₂,
      iteratedDMB j (fun y ↦ f (x', y)) (y, w) = G j hj ((x', y), Fin.elim0, w) :=
    fun j hj x' hx' y hy w ↦ (hGe j hj (show ((x', y), (Fin.elim0 : Fin 0 → E₁), w) ∈ _ from
      ⟨⟨hx', hy⟩, mem_univ _⟩)).symm
  -- the derivatives of `y ↦ G j (x, y, w)`
  have hderiv : ∀ j (hj : j < ℓ), ∀ y ∈ interior V, ∀ w : Fin (j + 1) → E₂,
      HasDirDerivAt (fun z ↦ G j hj.le ((x, z), Fin.elim0, Fin.init w)) y (w (Fin.last j))
        (G (j + 1) hj ((x, y), Fin.elim0, w)) := by
    intro j hj y hy w
    refine hasDirDerivAt_of_continuousOn_prod (S := U) (A := interior U) hx interior_subset hxcl
      (g := fun x' z ↦ G j hj.le ((x', z), Fin.elim0, Fin.init w))
      (D := fun x' z ↦ G (j + 1) hj ((x', z), Fin.elim0, w)) isOpen_interior ?_ ?_ ?_ hy
    · intro x' hx' z hz
      have h := (hf₀.contDiffMBOn_right x' hx').hasContIterDerivOn.1 j hj z hz w
      have hev : (fun z' ↦ iteratedDMB j (fun y ↦ f (x', y)) (z', Fin.init w)) =ᶠ[𝓝 z]
          fun z' ↦ G j hj.le ((x', z'), Fin.elim0, Fin.init w) :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hz) fun z' hz' ↦
          hGe' j hj.le x' hx' z' hz' _
      rw [hGe' (j + 1) hj x' hx' z hz w] at h
      exact h.congr_of_eventuallyEq hev
    · exact (hGc j hj.le).comp (by fun_prop) fun q hq ↦ ⟨⟨hq.1, interior_subset hq.2⟩, mem_univ _⟩
    · exact (hGc (j + 1) hj).comp (by fun_prop)
        fun q hq ↦ ⟨⟨hq.1, interior_subset hq.2⟩, mem_univ _⟩
  -- `G 0` is `f`
  have hG0 : ∀ p ∈ U ×ˢ V, ∀ w : Fin 0 → E₂, G 0 (Nat.zero_le ℓ) (p, Fin.elim0, w) = f p := by
    intro p hp w
    have := iteratedDMB₂_extension_unique hU hV (hGc 0 (Nat.zero_le ℓ))
      (D₂ := fun q ↦ f q.1) (hc.comp continuous_fst.continuousOn fun q hq ↦ hq.1)
      (hGe 0 (Nat.zero_le ℓ)) (fun q _ ↦ rfl) (show (p, (Fin.elim0, w)) ∈ _ from ⟨hp, mem_univ _⟩)
    exact this
  -- the differentials of `f(x, ·)` on `V⁰` are the `G j`
  have hid : ∀ j (hj : j ≤ ℓ), ∀ y ∈ interior V, ∀ w : Fin j → E₂,
      iteratedDMB j (fun y ↦ f (x, y)) (y, w) = G j hj ((x, y), Fin.elim0, w) := by
    intro j
    induction j with
    | zero => intro _ y hy w; exact (hG0 (x, y) ⟨hx, interior_subset hy⟩ w).symm
    | succ j ih =>
      intro hj y hy w
      rw [iteratedDMB_succ]
      have hev : (fun z ↦ iteratedDMB j (fun y ↦ f (x, y)) (z, Fin.init w)) =ᶠ[𝓝 y]
          fun z ↦ G j (by omega) ((x, z), Fin.elim0, Fin.init w) :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hy) fun z hz ↦ ih (by omega) z hz _
      rw [dMB_congr_of_eventuallyEq hev]
      exact (hderiv j hj y hy w).dMB_eq
  have hcV : ContinuousOn (fun y ↦ f (x, y)) V :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy ↦ ⟨hx, hy⟩
  have hGc' : ∀ j (hj : j ≤ ℓ), ContinuousOn (fun p : E₂ × (Fin j → E₂) ↦
      G j hj ((x, p.1), Fin.elim0, p.2)) (V ×ˢ univ) := fun j hj ↦
    (hGc j hj).comp (by fun_prop) fun p hp ↦ ⟨⟨hx, hp.1⟩, mem_univ _⟩
  have hcd : ContDiffMBOn ℓ (fun y ↦ f (x, y)) (interior V) := by
    refine HasContIterDerivOn.contDiffMBOn isOpen_interior ⟨fun j hj y hy w ↦ ?_, fun j hj ↦ ?_⟩
    · rw [hid (j + 1) hj y hy w]
      have hev : (fun z ↦ iteratedDMB j (fun y ↦ f (x, y)) (z, Fin.init w)) =ᶠ[𝓝 y]
          fun z ↦ G j hj.le ((x, z), Fin.elim0, Fin.init w) :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hy) fun z hz ↦ hid j hj.le z hz _
      exact (hderiv j hj y hy w).congr_of_eventuallyEq hev.symm
    · exact ((hGc' j hj).mono (prod_mono interior_subset le_rfl)).congr fun p hp ↦
        hid j hj p.1 hp.1 p.2
  have hLC : ContDiffLC ℓ (fun y ↦ f (x, y)) V :=
    contDiffLC_of_extends hV hcV hcd fun j hj ↦
      ⟨_, hGc' j hj, fun p hp ↦ (hid j hj p.1 hp.1 p.2).symm⟩
  refine ⟨hLC, fun j hj D hDc hDe ↦ ?_⟩
  have hDG := iteratedDMB₂_extension_unique hU hV hDc (hGc j hj) hDe (hGe j hj)
  refine iteratedDLC_unique hV (hLC.continuousOn_iteratedDLC hj)
    (hDc.comp (by fun_prop) fun p hp ↦ ⟨⟨hx, hp.1⟩, mem_univ _⟩)
    (fun p hp ↦ iteratedDLC_eq_iteratedDMB hp.1) fun p hp ↦ ?_
  rw [hid j hj p.1 hp.1 p.2]
  exact hDG ⟨⟨hx, interior_subset hp.1⟩, mem_univ _⟩

omit [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **[GN26, Remark 1.7.19(b)]** (p. 95). If `f` is `C^{k,ℓ}` on `U × V`, `j ≤ ℓ`,
`y ∈ V` (also on the boundary) and `w ∈ E₂^j`, then `x ↦ d^(0,j) f(x, y, w)` is `C^k` on `U`. -/
theorem ContDiffLC₂.contDiffLC_left (hf : ContDiffLC₂ k ℓ f U V) (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) {j : ℕ} (hj : j ≤ ℓ) {y : E₂} (hy : y ∈ V) (w : Fin j → E₂)
    {D : (E₁ × E₂) × (Fin 0 → E₁) × (Fin j → E₂) → F} (hDc : ContinuousOn D ((U ×ˢ V) ×ˢ univ))
    (hDe : EqOn D (iteratedDMB₂ 0 j f) ((interior U ×ˢ interior V) ×ˢ univ)) :
    ContDiffLC k (fun x ↦ D ((x, y), Fin.elim0, w)) U ∧ ∀ i ≤ k,
      ∀ D' : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) → F, ContinuousOn D' ((U ×ˢ V) ×ˢ univ) →
      EqOn D' (iteratedDMB₂ i j f) ((interior U ×ˢ interior V) ×ˢ univ) →
      EqOn (iteratedDLC i (fun x ↦ D ((x, y), Fin.elim0, w)) U) (fun p ↦ D' ((p.1, y), p.2, w))
        (U ×ˢ univ) := by
  obtain ⟨hc, hf₀, hD⟩ := hf
  choose H hHc hHe using fun i (hi : i ≤ k) ↦ hD i hi j hj
  have hycl : y ∈ closure (interior V) := hV hy
  have hHe' : ∀ i (hi : i ≤ k), ∀ x ∈ interior U, ∀ y' ∈ interior V, ∀ v : Fin i → E₁,
      iteratedDMB₂ i j f ((x, y'), v, w) = H i hi ((x, y'), v, w) :=
    fun i hi x hx y' hy' v ↦ (hHe i hi (show ((x, y'), v, w) ∈ _ from
      ⟨⟨hx, hy'⟩, mem_univ _⟩)).symm
  -- the derivatives of `x ↦ H i (x, y, v, w)`
  have hderiv : ∀ i (hi : i < k), ∀ x ∈ interior U, ∀ v : Fin (i + 1) → E₁,
      HasDirDerivAt (fun x' ↦ H i hi.le ((x', y), Fin.init v, w)) x (v (Fin.last i))
        (H (i + 1) hi ((x, y), v, w)) := by
    intro i hi x hx v
    refine hasDirDerivAt_of_continuousOn_prod (S := V) (A := interior V) hy interior_subset hycl
      (g := fun y' x' ↦ H i hi.le ((x', y'), Fin.init v, w))
      (D := fun y' x' ↦ H (i + 1) hi ((x', y'), v, w)) isOpen_interior ?_ ?_ ?_ hx
    · intro y' hy' x' hx'
      have h := hf₀.hasDirDerivAt_left hi hj hx' hy' v w
      have hev : (fun x'' ↦ iteratedDMB₂ i j f ((x'', y'), Fin.init v, w)) =ᶠ[𝓝 x']
          fun x'' ↦ H i hi.le ((x'', y'), Fin.init v, w) :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hx') fun x'' hx'' ↦
          hHe' i hi.le x'' hx'' y' hy' _
      rw [hHe' (i + 1) hi x' hx' y' hy' v] at h
      exact h.congr_of_eventuallyEq hev
    · exact (hHc i hi.le).comp (by fun_prop) fun q hq ↦ ⟨⟨interior_subset hq.2, hq.1⟩, mem_univ _⟩
    · exact (hHc (i + 1) hi).comp (by fun_prop)
        fun q hq ↦ ⟨⟨interior_subset hq.2, hq.1⟩, mem_univ _⟩
  -- the differentials of `x ↦ H 0 (x, y, w)` on `U⁰`
  have hid : ∀ i (hi : i ≤ k), ∀ x ∈ interior U, ∀ v : Fin i → E₁,
      iteratedDMB i (fun x' ↦ H 0 (Nat.zero_le k) ((x', y), Fin.elim0, w)) (x, v) =
        H i hi ((x, y), v, w) := by
    intro i
    induction i with
    | zero => intro _ x _ v; rw [Subsingleton.elim v Fin.elim0]; rfl
    | succ i ih =>
      intro hi x hx v
      rw [iteratedDMB_succ]
      have hev : (fun z ↦ iteratedDMB i (fun x' ↦ H 0 (Nat.zero_le k) ((x', y), Fin.elim0, w))
          (z, Fin.init v)) =ᶠ[𝓝 x] fun z ↦ H i (by omega) ((z, y), Fin.init v, w) :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hx) fun z hz ↦ ih (by omega) z hz _
      rw [dMB_congr_of_eventuallyEq hev]
      exact (hderiv i hi x hx v).dMB_eq
  have hHc' : ∀ i (hi : i ≤ k), ContinuousOn (fun p : E₁ × (Fin i → E₁) ↦
      H i hi ((p.1, y), p.2, w)) (U ×ˢ univ) := fun i hi ↦
    (hHc i hi).comp (by fun_prop) fun p hp ↦ ⟨⟨hp.1, hy⟩, mem_univ _⟩
  have hcd : ContDiffMBOn k (fun x' ↦ H 0 (Nat.zero_le k) ((x', y), Fin.elim0, w))
      (interior U) := by
    refine HasContIterDerivOn.contDiffMBOn isOpen_interior ⟨fun i hi x hx v ↦ ?_, fun i hi ↦ ?_⟩
    · rw [hid (i + 1) hi x hx v]
      have hev : (fun z ↦ iteratedDMB i (fun x' ↦ H 0 (Nat.zero_le k) ((x', y), Fin.elim0, w))
          (z, Fin.init v)) =ᶠ[𝓝 x] fun z ↦ H i hi.le ((z, y), Fin.init v, w) :=
        Filter.eventually_of_mem (isOpen_interior.mem_nhds hx) fun z hz ↦ hid i hi.le z hz _
      exact (hderiv i hi x hx v).congr_of_eventuallyEq hev.symm
    · exact ((hHc' i hi).mono (prod_mono interior_subset le_rfl)).congr fun p hp ↦
        hid i hi p.1 hp.1 p.2
  have hLC := contDiffLC_of_extends hU ((hHc' 0 (Nat.zero_le k)).comp
    (f := fun x : E₁ ↦ (x, (Fin.elim0 : Fin 0 → E₁))) (by fun_prop)
    fun x hx ↦ ⟨hx, mem_univ _⟩) hcd fun i hi ↦
      ⟨_, hHc' i hi, fun p hp ↦ (hid i hi p.1 hp.1 p.2).symm⟩
  have hDH := iteratedDMB₂_extension_unique hU hV (hHc 0 (Nat.zero_le k)) hDc
    (hHe 0 (Nat.zero_le k)) hDe
  have hLC' := hLC.congr fun x hx ↦ hDH ⟨⟨hx, hy⟩, mem_univ _⟩
  refine ⟨hLC', fun i hi D' hD'c hD'e ↦ ?_⟩
  have hD'H := iteratedDMB₂_extension_unique hU hV hD'c (hHc i hi) hD'e (hHe i hi)
  refine iteratedDLC_unique hU (hLC'.continuousOn_iteratedDLC hi)
    (hD'c.comp (f := fun p : E₁ × (Fin i → E₁) ↦ ((p.1, y), p.2, w)) (by fun_prop)
      fun p hp ↦ ⟨⟨hp.1, hy⟩, mem_univ _⟩)
    (fun p hp ↦ iteratedDLC_eq_iteratedDMB hp.1) fun p hp ↦ ?_
  have hev : (fun x ↦ D ((x, y), Fin.elim0, w)) =ᶠ[𝓝 p.1]
      fun x' ↦ H 0 (Nat.zero_le k) ((x', y), Fin.elim0, w) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds hp.1) fun x hx ↦
      (hDH ⟨⟨interior_subset hx, hy⟩, mem_univ _⟩).symm
  change D' ((p.1, y), p.2, w) = iteratedDMB i (fun x ↦ D ((x, y), Fin.elim0, w)) (p.1, p.2)
  rw [iteratedDMB_congr_of_eventuallyEq i hev, hid i hi p.1 hp.1 p.2]
  exact hD'H ⟨⟨interior_subset hp.1, hy⟩, mem_univ _⟩

/-- **[GN26, Proposition 1.7.33(a)]** (p. 108), for sets with dense interior: every map
that is `C^{k+ℓ}` on `U × V` is `C^{k,ℓ}`, the extensions of the mixed differentials being given
by (1.107),
`d^(i,j) f(x, y, v, w) = d^(j+i) f((x, y), (0, w₁), …, (0, wⱼ), (v₁, 0), …, (vᵢ, 0))`. -/
theorem ContDiffLC.contDiffLC₂ (hf : ContDiffLC (k + ℓ) f (U ×ˢ V)) :
    ContDiffLC₂ k ℓ f U V := by
  have hint : interior (U ×ˢ V) = interior U ×ˢ interior V := interior_prod_eq U V
  refine ⟨hf.continuousOn, ?_, fun i hi j hj ↦ ⟨fun p ↦ iteratedDLC (j + i) f (U ×ˢ V)
    (p.1, Fin.append (fun s ↦ ((0 : E₁), p.2.2 s)) fun s ↦ (p.2.1 s, (0 : E₂))), ?_, ?_⟩⟩
  · have h := hf.contDiffMBOn_interior
    rw [hint] at h
    exact ContDiffMBOn.contDiffMBOn₂ isOpen_interior isOpen_interior h
  · exact (hf.continuousOn_iteratedDLC (show j + i ≤ k + ℓ by omega)).comp
      (continuous_append_directions i j).continuousOn fun p hp ↦ ⟨hp.1, mem_univ _⟩
  · intro p hp
    rw [iteratedDMB₂_eq_iteratedDMB]
    exact iteratedDLC_eq_iteratedDMB (by rw [hint]; exact hp.1)

end Results

end LocallyConvex.Analysis

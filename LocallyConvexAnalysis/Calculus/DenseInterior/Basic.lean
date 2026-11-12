/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.Rules

/-!
# `C^k` maps on locally convex subsets with dense interior

Reference: [GN26, §1.4] "Differential calculus on non-open domains", pp. 51–62.

Cubes `[0, 1]ⁿ`, half-spaces and open subsets of them are not open, but the Michal–Bastiani
calculus extends to them ([GN26, §1.4]). A subset `U` of a locally convex space `E` is
*locally convex* if every point of `U` has a convex neighborhood in `U`
([GN26, Definition 1.4.1, p. 51]), and it has *dense interior* if `U ⊆ closure (interior U)`
([GN26, p. 52]). A map `f : U → F` on such a set is `C^1` if it is continuous, `f` is `C^1` on the
interior `U⁰` and `d(f|U⁰) : U⁰ × E → F` extends to a continuous map `df : U × E → F`; it is
`C^{k+1}` if moreover `df` is `C^k` on `U × E` ([GN26, Definition 1.4.4, p. 52]). This is the domain
of the charts of manifolds with rough boundary ([GN26, Definition 3.5.1, p. 278]).

## Main definitions

* `IsLocallyConvexSubset U`: every `x ∈ U` has a convex neighborhood in `U`
  ([GN26, Definition 1.4.1]).
* `HasDenseInterior U`: `U ⊆ closure (interior U)`.
* `dLC f U : E × E → F`: the differential of `f` on `U`. It is `dMB f` over the interior of `U`
  and the limit of `dMB f` from the interior elsewhere, so it depends only on `f` on `U⁰`
  (`dLC_congr`).
* `ContDiffLC k f U`: `f` is `C^k` on `U` in the sense of [GN26, Definition 1.4.4]. The
  definition is recursive, like `ContDiffMBOn`: `ContDiffLC (k + 1) f U` means that `f` is
  continuous on `U`, has all directional derivatives on `U⁰`, and `dLC f U` is `C^k` on `U ×ˢ univ`.

## Main results

* `contDiffLC_iff_contDiffMBOn`: on open sets, `ContDiffLC` is `ContDiffMBOn`.
* `dLC_eqOn_of_continuousOn`: uniqueness of the continuous extension of `d(f|U⁰)` (Glöckner–Neeb
  1.4.4).
* `ContDiffLC.of_hasDirDerivAt`: `f` is `C^{k+1}` as soon as `d(f|U⁰)` has some `C^k` extension
  to `U × E`, and then `dLC f U` is that extension. All the rules below are proved from it.
* `ContDiffLC.exists_clm`: `df(x)` is continuous linear for every `x ∈ U` ([GN26, Lemma 1.4.7]).
* `ContDiffLC.integral_dLC`: mean value theorem `f(x + h) - f(x) = ∫₀¹ df(x + th, h) dt`,
  in weak form, along any segment contained in `U` ([GN26, Proposition 1.4.8]).
* `ContDiffLC.tendsto_quotient`: difference quotients extend continuously to `t = 0`
  ([GN26, Lemma 1.4.9]).
* `ContDiffLC.comp`, `ContDiffLC.dLC_comp`: chain rule ([GN26, Proposition 1.4.10]).
* `ContDiffLC.prodMk`, `ContDiffLC.prodMap`, `ContinuousLinearMap.contDiffLC`,
  `ContDiffLC.clm_comp`, `ContDiffLC.add`, `ContDiffLC.bilin`, `ContDiffMBOn.contDiffLC`:
  pairs, products, linear maps, sums, the product rule, restrictions of maps on open sets.
* `ContDiffLC.mono`, `ContDiffLC.of_local`: restriction to smaller subsets with dense interior;
  `C^k` is a local property. With `IsLocallyConvexSubset.inter_isOpen` and
  `HasDenseInterior.inter_isOpen` this is what the transition maps of manifolds with rough
  boundary need ([GN26, Remark 3.5.2, p. 279]).

## Hypotheses

No completeness is assumed anywhere: integrals are weak (scalar) integrals. The chain rule
needs the target domain `V` to be locally convex with dense interior, but only density of the
interior of the source `U`. Local convexity of `U` is used only in the mean value theorem along
segments and in the extension of difference quotients.

## Departures from Glöckner–Neeb

Glöckner–Neeb prove the mean value theorem (Proposition 1.4.8) first on convex sets, with a strong
integral in a completion of `F`, and then on general locally convex sets by splitting a segment
into finitely many pieces that lie in convex neighborhoods. Here the convex case is proved with
weak integrals, by shrinking the segment towards an interior point and passing to the limit in a
parameter-dependent integral; the convex case gives the extension of difference quotients
(Lemma 1.4.9), and the general mean value theorem then follows from the fundamental theorem of
calculus on `[0, 1]` for `t ↦ φ (f (x + t h))`, whose right derivative is given by Lemma 1.4.9.
We do not claim this argument is new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v u₁ u₂

/-! ### Locally convex subsets with dense interior -/

section Geometry

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- [GN26, Definition 1.4.1]: `U ⊆ E` is *locally convex* if every point of `U` has a
convex neighborhood in `U` (for the topology induced on `U`). -/
def IsLocallyConvexSubset (U : Set E) : Prop :=
  ∀ x ∈ U, ∃ V ∈ 𝓝[U] x, V ⊆ U ∧ Convex ℝ V

/-- `U` has *dense interior* ([GN26, p. 52]): the interior of `U` is dense in `U`. -/
def HasDenseInterior (U : Set E) : Prop :=
  U ⊆ closure (interior U)

theorem _root_.Convex.isLocallyConvexSubset {U : Set E} (hU : Convex ℝ U) :
    IsLocallyConvexSubset U :=
  fun _ _ ↦ ⟨U, self_mem_nhdsWithin, subset_rfl, hU⟩

theorem _root_.IsOpen.isLocallyConvexSubset [LocallyConvexSpace ℝ E] {U : Set E} (hU : IsOpen U) :
    IsLocallyConvexSubset U := by
  intro x hx
  obtain ⟨C, ⟨hC, hCc⟩, hCU⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x).mem_iff.mp (hU.mem_nhds hx)
  exact ⟨C, mem_nhdsWithin_of_mem_nhds hC, hCU, hCc⟩

theorem isLocallyConvexSubset_univ : IsLocallyConvexSubset (univ : Set E) :=
  convex_univ.isLocallyConvexSubset

/-- [GN26, Remark 1.4.2]: finite intersections of locally convex subsets are locally
convex. -/
theorem IsLocallyConvexSubset.inter {U V : Set E} (hU : IsLocallyConvexSubset U)
    (hV : IsLocallyConvexSubset V) : IsLocallyConvexSubset (U ∩ V) := by
  intro x hx
  obtain ⟨A, hA, hAU, hAc⟩ := hU x hx.1
  obtain ⟨B, hB, hBV, hBc⟩ := hV x hx.2
  exact ⟨A ∩ B, inter_mem (nhdsWithin_mono _ inter_subset_left hA)
    (nhdsWithin_mono _ inter_subset_right hB), inter_subset_inter hAU hBV, hAc.inter hBc⟩

/-- Relatively open subsets of locally convex subsets are locally convex. -/
theorem IsLocallyConvexSubset.inter_isOpen [LocallyConvexSpace ℝ E] {U W : Set E}
    (hU : IsLocallyConvexSubset U) (hW : IsOpen W) : IsLocallyConvexSubset (U ∩ W) :=
  hU.inter hW.isLocallyConvexSubset

theorem IsLocallyConvexSubset.prod {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    [TopologicalSpace E'] {U : Set E} {V : Set E'} (hU : IsLocallyConvexSubset U)
    (hV : IsLocallyConvexSubset V) : IsLocallyConvexSubset (U ×ˢ V) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨A, hA, hAU, hAc⟩ := hU x hx
  obtain ⟨B, hB, hBV, hBc⟩ := hV y hy
  refine ⟨A ×ˢ B, ?_, prod_mono hAU hBV, hAc.prod hBc⟩
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hA hB

/-- [GN26, Remark 1.4.3]: every neighborhood of `x ∈ U` contains an open convex
neighborhood `W` of `x` in `E` such that `U ∩ W` is convex. -/
theorem IsLocallyConvexSubset.exists_isOpen_convex [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {U : Set E} (hU : IsLocallyConvexSubset U) {x : E} (hx : x ∈ U)
    {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ Convex ℝ W ∧ Convex ℝ (U ∩ W) := by
  obtain ⟨V, hV, hVU, hVc⟩ := hU x hx
  obtain ⟨O, hO, hOV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV
  obtain ⟨C, ⟨hC, hCc⟩, hCN⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x).mem_iff.mp (inter_mem hN hO)
  refine ⟨interior C, isOpen_interior, mem_interior_iff_mem_nhds.mpr hC,
    interior_subset.trans (hCN.trans inter_subset_left), hCc.interior, ?_⟩
  have hUW : U ∩ interior C = V ∩ interior C := by
    refine subset_antisymm (fun z hz ↦ ⟨hOV ⟨?_, hz.1⟩, hz.2⟩)
      (inter_subset_inter_left _ hVU)
    exact (hCN (interior_subset hz.2)).2
  rw [hUW]
  exact hVc.inter hCc.interior

omit [AddCommGroup E] [Module ℝ E] in
theorem _root_.IsOpen.hasDenseInterior {U : Set E} (hU : IsOpen U) : HasDenseInterior U := by
  rw [HasDenseInterior, hU.interior_eq]
  exact subset_closure

omit [AddCommGroup E] [Module ℝ E] in
theorem hasDenseInterior_univ : HasDenseInterior (univ : Set E) :=
  isOpen_univ.hasDenseInterior

/-- A convex set with nonempty interior has dense interior ([GN26, Lemma B.1.3(c), p. 897]). -/
theorem _root_.Convex.hasDenseInterior [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {U : Set E}
    (hU : Convex ℝ U) (hne : (interior U).Nonempty) : HasDenseInterior U := by
  rw [HasDenseInterior, hU.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

omit [AddCommGroup E] [Module ℝ E] in
theorem HasDenseInterior.prod {E' : Type*} [TopologicalSpace E'] {U : Set E} {V : Set E'}
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) : HasDenseInterior (U ×ˢ V) := by
  rw [HasDenseInterior, interior_prod_eq, closure_prod_eq]
  exact prod_mono hU hV

omit [AddCommGroup E] [Module ℝ E] in
theorem HasDenseInterior.prod_univ {E' : Type*} [TopologicalSpace E'] {U : Set E}
    (hU : HasDenseInterior U) : HasDenseInterior (U ×ˢ (univ : Set E')) :=
  hU.prod isOpen_univ.hasDenseInterior

omit [AddCommGroup E] [Module ℝ E] in
/-- Relatively open subsets of sets with dense interior have dense interior. -/
theorem HasDenseInterior.inter_isOpen {U W : Set E} (hU : HasDenseInterior U) (hW : IsOpen W) :
    HasDenseInterior (U ∩ W) := by
  intro x hx
  rw [interior_inter, hW.interior_eq, inter_comm]
  exact hW.inter_closure ⟨hx.2, hU hx.1⟩

/-- In a locally convex subset with dense interior, every point has open convex neighborhoods
`W` such that `U ∩ W` is convex with nonempty interior. -/
theorem IsLocallyConvexSubset.exists_isOpen_convex_interior [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {U : Set E} (hU : IsLocallyConvexSubset U)
    (hd : HasDenseInterior U) {x : E} (hx : x ∈ U) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ N ∧ Convex ℝ (U ∩ W) ∧ (interior (U ∩ W)).Nonempty := by
  obtain ⟨W, hW, hxW, hWN, -, hc⟩ := hU.exists_isOpen_convex hx hN
  refine ⟨W, hW, hxW, hWN, hc, ?_⟩
  obtain ⟨z, hz⟩ := mem_closure_iff.mp (hd hx) W hW hxW
  exact ⟨z, by rw [interior_inter, hW.interior_eq]; exact ⟨hz.2, hz.1⟩⟩

end Geometry

/-! ### The differential on a set with dense interior -/

section Definition

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

open scoped Classical in
/-- The differential of `f` on `U`: `dMB f` over the interior of `U`, and the limit of `dMB f`
from `interior U ×ˢ univ` at the other points (junk value where the limit does not exist). For
`C^1` maps on sets with dense interior this is the unique continuous extension of `d(f|U⁰)` to
`U × E` (`dLC_eqOn_of_continuousOn`). -/
def dLC (f : E → F) (U : Set E) (p : E × E) : F :=
  if p.1 ∈ interior U then dMB f p else limUnder (𝓝[interior U ×ˢ univ] p) (dMB f)

/-- [GN26, Definition 1.4.4]: `C^k` maps on a set `U` (meant to be a locally convex
subset with dense interior), `k ∈ ℕ`. `f` is `C^{k+1}` on `U` if it is continuous on `U`, has
all directional derivatives at the interior points of `U`, and its differential `dLC f U`
(the extension of `d(f|U⁰)`) is `C^k` on `U ×ˢ univ`; in particular `dLC f U` is continuous on
`U ×ˢ univ`. -/
def ContDiffLC : ℕ → ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
    (E → F) → Set E → Prop
  | 0, _, _, _, _, f, U => ContinuousOn f U
  | k + 1, _, _, _, _, f, U =>
      ContinuousOn f U ∧ (∀ x ∈ interior U, ∀ h, HasDirDerivAt f x h (dMB f (x, h))) ∧
        ContDiffLC k (dLC f U) (U ×ˢ univ)

/-- Smooth maps on `U`. -/
def SmoothLC (f : E → F) (U : Set E) : Prop := ∀ k, ContDiffLC k f U

theorem ContDiffLC.continuousOn {k : ℕ} {f : E → F} {U : Set E} (hf : ContDiffLC k f U) :
    ContinuousOn f U := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

theorem ContDiffLC.hasDirDerivAt {k : ℕ} {f : E → F} {U : Set E} (hf : ContDiffLC (k + 1) f U)
    {x : E} (hx : x ∈ interior U) (h : E) : HasDirDerivAt f x h (dMB f (x, h)) :=
  hf.2.1 x hx h

theorem ContDiffLC.contDiffLC_dLC {k : ℕ} {f : E → F} {U : Set E}
    (hf : ContDiffLC (k + 1) f U) : ContDiffLC k (dLC f U) (U ×ˢ univ) :=
  hf.2.2

theorem ContDiffLC.continuousOn_dLC {k : ℕ} {f : E → F} {U : Set E}
    (hf : ContDiffLC (k + 1) f U) : ContinuousOn (dLC f U) (U ×ˢ univ) :=
  hf.2.2.continuousOn

theorem ContDiffLC.of_succ : ∀ {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {f : E → F} {U : Set E}, ContDiffLC (k + 1) f U → ContDiffLC k f U
  | 0, _, _, _, _, _, _, hf => hf.1
  | _ + 1, _, _, _, _, _, _, hf => ⟨hf.1, hf.2.1, ContDiffLC.of_succ hf.2.2⟩

theorem ContDiffLC.of_le {k l : ℕ} {f : E → F} {U : Set E} (hf : ContDiffLC k f U)
    (hlk : l ≤ k) : ContDiffLC l f U := by
  induction hlk with
  | refl => exact hf
  | step _ ih => exact ih hf.of_succ

theorem SmoothLC.contDiffLC {f : E → F} {U : Set E} (hf : SmoothLC f U) (k : ℕ) :
    ContDiffLC k f U :=
  hf k

theorem dLC_of_mem_interior (f : E → F) {U : Set E} {p : E × E} (hp : p.1 ∈ interior U) :
    dLC f U p = dMB f p := by
  simp [dLC, hp]

theorem dLC_eqOn_interior (f : E → F) (U : Set E) :
    EqOn (dLC f U) (dMB f) (interior U ×ˢ univ) :=
  fun _ hp ↦ dLC_of_mem_interior f hp.1

theorem dLC_of_isOpen (f : E → F) {U : Set E} (hU : IsOpen U) :
    EqOn (dLC f U) (dMB f) (U ×ˢ univ) := by
  simpa [hU.interior_eq] using dLC_eqOn_interior f U

section Uniqueness

variable [T2Space F]

/-- Uniqueness of the extension ([GN26, Definition 1.4.4]): on a set with dense
interior, every continuous map on `U × E` that agrees with `dMB f` on `U⁰ × E` is `dLC f U`. -/
theorem dLC_eqOn_of_continuousOn {f : E → F} {U : Set E} (hd : HasDenseInterior U)
    {D : E × E → F} (hD : ContinuousOn D (U ×ˢ univ))
    (heq : EqOn D (dMB f) (interior U ×ˢ univ)) : EqOn (dLC f U) D (U ×ˢ univ) := by
  intro p hp
  by_cases hp1 : p.1 ∈ interior U
  · rw [dLC_of_mem_interior f hp1, heq ⟨hp1, mem_univ _⟩]
  · simp only [dLC, hp1, ite_false]
    have hsub : interior U ×ˢ (univ : Set E) ⊆ U ×ˢ univ := prod_mono interior_subset subset_rfl
    have hcl : p ∈ closure (interior U ×ˢ (univ : Set E)) := by
      rw [closure_prod_eq, closure_univ]
      exact ⟨hd hp.1, mem_univ _⟩
    have : (𝓝[interior U ×ˢ univ] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hT : Tendsto D (𝓝[interior U ×ˢ univ] p) (𝓝 (D p)) :=
      (hD p hp).mono_left (nhdsWithin_mono _ hsub)
    exact (hT.congr' (eventually_nhdsWithin_of_forall heq)).limUnder_eq

end Uniqueness

end Definition

/-! ### Basic rules -/

section Rules

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The differential `dLC f U` only depends on `f` on the interior of `U`
([GN26, p. 52]: the extension of `d(f|U⁰)` is determined by `f|U⁰`). -/
theorem dLC_congr {f₁ f₂ : E → F} {U : Set E} (h : EqOn f₁ f₂ (interior U)) :
    dLC f₁ U = dLC f₂ U := by
  have hd : ∀ q : E × E, q.1 ∈ interior U → dMB f₁ q = dMB f₂ q := fun q hq ↦
    dMB_congr_of_eventuallyEq (h.eventuallyEq_of_mem (isOpen_interior.mem_nhds hq)) q.2
  funext p
  by_cases hp : p.1 ∈ interior U
  · rw [dLC_of_mem_interior f₁ hp, dLC_of_mem_interior f₂ hp]
    exact hd p hp
  · simp only [dLC, hp, ite_false, limUnder]
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hd q hq.1

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- `C^k` only depends on the values on `U`. -/
theorem ContDiffLC.congr {k : ℕ} {f₁ f₂ : E → F} {U : Set E} (hf : ContDiffLC k f₁ U)
    (h : EqOn f₁ f₂ U) : ContDiffLC k f₂ U := by
  cases k with
  | zero => exact ContinuousOn.congr hf h.symm
  | succ k =>
    refine ⟨ContinuousOn.congr hf.1 h.symm, fun x hx v ↦ ?_, ?_⟩
    · have hev : f₁ =ᶠ[𝓝 x] f₂ :=
        (h.mono interior_subset).eventuallyEq_of_mem (isOpen_interior.mem_nhds hx)
      rw [← dMB_congr_of_eventuallyEq hev v]
      exact (hf.2.1 x hx v).congr_of_eventuallyEq hev
    · rw [← dLC_congr (h.mono interior_subset)]
      exact hf.2.2

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The basic criterion: if the directional derivatives of `f` on `U⁰` are given by a map `D`
that is `C^k` on `U × E`, then `f` is `C^{k+1}` on `U` and `dLC f U = D` on `U × E`. All the
rules for `ContDiffLC` are proved from it. -/
theorem ContDiffLC.of_hasDirDerivAt {k : ℕ} {f : E → F} {U : Set E} {D : E × E → F}
    (hd : HasDenseInterior U) (hf : ContinuousOn f U)
    (hD : ∀ x ∈ interior U, ∀ h, HasDirDerivAt f x h (D (x, h)))
    (hDk : ContDiffLC k D (U ×ˢ univ)) :
    ContDiffLC (k + 1) f U ∧ EqOn (dLC f U) D (U ×ˢ univ) := by
  have heqD : EqOn D (dMB f) (interior U ×ˢ univ) := fun p hp ↦ ((hD p.1 hp.1 p.2).dMB_eq).symm
  have hE := dLC_eqOn_of_continuousOn hd hDk.continuousOn heqD
  refine ⟨⟨hf, fun x hx h ↦ ?_, hDk.congr fun p hp ↦ (hE hp).symm⟩, hE⟩
  rw [(hD x hx h).dMB_eq]
  exact hD x hx h

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- On open sets, `ContDiffLC` is `ContDiffMBOn`. -/
theorem contDiffLC_iff_contDiffMBOn : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U : Set E₁},
    IsOpen U → (ContDiffLC k f U ↔ ContDiffMBOn k f U) := by
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ f U hU; exact Iff.rfl
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U hU
    have hdeq := dLC_of_isOpen f hU
    have hUE := hU.prod (isOpen_univ (X := E₁))
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx h ↦ h2 x (by rwa [hU.interior_eq]) h, ?_⟩
      exact ContDiffMBOn.congr_of_isOpen hUE hdeq ((ih hUE).mp h3)
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, fun x hx h ↦ h2 x (by rwa [hU.interior_eq] at hx) h, ?_⟩
      exact (ih hUE).mpr (ContDiffMBOn.congr_of_isOpen hUE hdeq.symm h3)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- A map that is `C^k` on an open set `O` is `C^k` on every subset of `O` with dense
interior. -/
theorem ContDiffMBOn.contDiffLC : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {O U : Set E₁},
    IsOpen O → ContDiffMBOn k f O → U ⊆ O → HasDenseInterior U → ContDiffLC k f U := by
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ f O U _ hf hUO _; exact ContinuousOn.mono hf hUO
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f O U hO hf hUO hd
    exact (ContDiffLC.of_hasDirDerivAt hd (hf.continuousOn.mono hUO)
      (fun x hx h ↦ hf.2.1 x (hUO (interior_subset hx)) h)
      (ih (hO.prod isOpen_univ) hf.2.2 (prod_mono hUO subset_rfl) hd.prod_univ)).1

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- For a map that is `C^1` on an open set `O ⊇ U`, `dLC f U` is `dMB f` on `U × E`. -/
theorem ContDiffMBOn.dLC_eq {f : E → F} {O U : Set E} (hf : ContDiffMBOn 1 f O)
    (hUO : U ⊆ O) (hd : HasDenseInterior U) : EqOn (dLC f U) (dMB f) (U ×ˢ univ) :=
  dLC_eqOn_of_continuousOn hd ((hf.2.2 : ContinuousOn (dMB f) (O ×ˢ univ)).mono
    (prod_mono hUO subset_rfl)) fun _ _ ↦ rfl

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- A `C^k` map on `U` is `C^k` on the interior of `U`. -/
theorem ContDiffLC.contDiffMBOn_interior : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁]
    [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U : Set E₁},
    ContDiffLC k f U → ContDiffMBOn k f (interior U) := by
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ f U hf; exact ContinuousOn.mono hf interior_subset
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U hf
    refine ⟨hf.1.mono interior_subset, hf.2.1, ?_⟩
    have h := ih hf.2.2
    rw [interior_prod_eq, interior_univ] at h
    exact ContDiffMBOn.congr_of_isOpen (isOpen_interior.prod isOpen_univ)
      (dLC_eqOn_interior f U) h

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Restriction to a smaller subset with dense interior. -/
theorem ContDiffLC.mono : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U V : Set E₁},
    ContDiffLC k f U → V ⊆ U → HasDenseInterior V → ContDiffLC k f V := by
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ f U V hf hVU _; exact ContinuousOn.mono hf hVU
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U V hf hVU hV
    refine (ContDiffLC.of_hasDirDerivAt hV (hf.1.mono hVU) (fun x hx h ↦ ?_)
      (ih hf.2.2 (prod_mono hVU subset_rfl) hV.prod_univ)).1
    have hxU : (x, h).1 ∈ interior U := interior_mono hVU hx
    rw [dLC_of_mem_interior f hxU]
    exact hf.2.1 x hxU h

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- On a smaller subset with dense interior, the differential is the restriction. -/
theorem ContDiffLC.dLC_mono {f : E → F} {U V : Set E} (hf : ContDiffLC 1 f U) (hVU : V ⊆ U)
    (hV : HasDenseInterior V) : EqOn (dLC f V) (dLC f U) (V ×ˢ univ) :=
  dLC_eqOn_of_continuousOn hV (hf.continuousOn_dLC.mono (prod_mono hVU subset_rfl))
    fun _ hp ↦ dLC_of_mem_interior f (interior_mono hVU hp.1)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The differential is local: on `W × E`, `W` open, `dLC f (U ∩ W)` is `dLC f U`. -/
theorem dLC_inter_isOpen (f : E → F) (U : Set E) {W : Set E} (hW : IsOpen W) {p : E × E}
    (hp : p.1 ∈ W) : dLC f (U ∩ W) p = dLC f U p := by
  have hi : interior (U ∩ W) = interior U ∩ W := by rw [interior_inter, hW.interior_eq]
  by_cases h : p.1 ∈ interior U
  · rw [dLC_of_mem_interior f h, dLC_of_mem_interior f (by rw [hi]; exact ⟨h, hp⟩)]
  · have h' : p.1 ∉ interior (U ∩ W) := by rw [hi]; exact fun h' ↦ h h'.1
    simp only [dLC, h, h', ite_false]
    rw [hi, show (interior U ∩ W) ×ˢ (univ : Set E) = (interior U ×ˢ univ) ∩ (W ×ˢ univ) by
      rw [prod_inter_prod, inter_univ], nhdsWithin_inter_of_mem'
      (mem_nhdsWithin_of_mem_nhds ((hW.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩))]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Being `C^k` is a local property. -/
theorem ContDiffLC.of_local : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {U : Set E₁},
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ContDiffLC k f (U ∩ W)) → ContDiffLC k f U := by
  have hcont : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
      {f : E₁ → F} {U : Set E₁},
      (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ContDiffLC k f (U ∩ W)) → ContinuousOn f U := by
    intro k E₁ _ _ _ f U hloc x hx
    obtain ⟨W, hW, hxW, hf⟩ := hloc x hx
    exact (continuousWithinAt_inter (hW.mem_nhds hxW)).mp (hf.continuousOn x ⟨hx, hxW⟩)
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ f U hloc; exact hcont hloc
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f U hloc
    refine ⟨hcont hloc, fun x hx h ↦ ?_, ih fun p hp ↦ ?_⟩
    · obtain ⟨W, hW, hxW, hf⟩ := hloc x (interior_subset hx)
      exact hf.2.1 x (by rw [interior_inter, hW.interior_eq]; exact ⟨hx, hxW⟩) h
    · obtain ⟨W, hW, hxW, hf⟩ := hloc p.1 hp.1
      refine ⟨W ×ˢ univ, hW.prod isOpen_univ, ⟨hxW, mem_univ _⟩, ?_⟩
      rw [prod_inter_prod, inter_univ]
      exact hf.2.2.congr fun q hq ↦ dLC_inter_isOpen f U hW hq.1.2

end Rules

/-! ### Linearity of the differential, mean value theorem, difference quotients -/

section Calculus

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem ContDiffLC.continuousOn_dLC_left {f : E → F} {U : Set E} (hf : ContDiffLC 1 f U)
    (v : E) : ContinuousOn (fun y ↦ dLC f U (y, v)) U :=
  hf.continuousOn_dLC.comp (continuousOn_id.prodMk continuousOn_const) fun _ hy ↦ ⟨hy, mem_univ _⟩

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Homogeneity of `df(x)` for `x ∈ U` ([GN26, Lemma 1.4.7]). -/
theorem ContDiffLC.dLC_smul {f : E → F} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC 1 f U) {x : E} (hx : x ∈ U) (c : ℝ) (h : E) :
    dLC f U (x, c • h) = c • dLC f U (x, h) := by
  refine EqOn.of_subset_closure (s := interior U) (fun y hy ↦ ?_) (hf.continuousOn_dLC_left _)
    ((hf.continuousOn_dLC_left h).const_smul c) interior_subset hd hx
  simp only [Pi.smul_apply]
  rw [dLC_of_mem_interior f (p := (y, c • h)) hy, dLC_of_mem_interior f (p := (y, h)) hy]
  exact hf.contDiffMBOn_interior.dMB_smul hy c h

/-- Additivity of `df(x)` for `x ∈ U` ([GN26, Lemma 1.4.7]). -/
theorem ContDiffLC.dLC_add {f : E → F} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC 1 f U) {x : E} (hx : x ∈ U) (h k : E) :
    dLC f U (x, h + k) = dLC f U (x, h) + dLC f U (x, k) := by
  refine EqOn.of_subset_closure (s := interior U) (fun y hy ↦ ?_) (hf.continuousOn_dLC_left _)
    ((hf.continuousOn_dLC_left h).add (hf.continuousOn_dLC_left k)) interior_subset hd hx
  simp only [Pi.add_apply]
  rw [dLC_of_mem_interior f (p := (y, h + k)) hy, dLC_of_mem_interior f (p := (y, h)) hy,
    dLC_of_mem_interior f (p := (y, k)) hy]
  exact hf.contDiffMBOn_interior.dMB_add isOpen_interior hy h k

/-- [GN26, Lemma 1.4.7] (`k = 1`): for every `x ∈ U` (also on the boundary),
`df(x) = dLC f U (x, ·)` is a continuous linear map. -/
theorem ContDiffLC.exists_clm {f : E → F} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC 1 f U) {x : E} (hx : x ∈ U) :
    ∃ L : E →L[ℝ] F, ∀ h, L h = dLC f U (x, h) :=
  ⟨{ toFun := fun h ↦ dLC f U (x, h)
     map_add' := hf.dLC_add hd hx
     map_smul' := hf.dLC_smul hd hx
     cont := hf.continuousOn_dLC.comp_continuous (by fun_prop) fun h ↦ ⟨hx, mem_univ h⟩ },
    fun _ ↦ rfl⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Mean value theorem on a convex set `C ⊆ U` with an interior point (weak form; the convex
case of [GN26, Proposition 1.4.8]). The segment from `x` to `y` is shrunk towards the
interior point `z`; on the shrunk segments, which lie in the interior, this is
`ContDiffMBOn.integral_dMB`, and both sides are continuous in the shrinking parameter. -/
theorem ContDiffLC.integral_dLC_of_convex {f : E → F} {U C : Set E} (hf : ContDiffLC 1 f U)
    (hCU : C ⊆ U) (hC : Convex ℝ C) {z : E} (hz : z ∈ interior C) {x y : E} (hx : x ∈ C)
    (hy : y ∈ C) (φ : F →L[ℝ] ℝ) :
    φ (f y) - φ (f x) = ∫ s in (0 : ℝ)..1, φ (dLC f U (x + s • (y - x), y - x)) := by
  obtain ⟨P, hP⟩ : ∃ P : ℝ → E, P = fun r ↦ z + r • (x - z) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → E, Q = fun r ↦ z + r • (y - z) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ → ℝ, c = fun r ↦ max 0 (min 1 r) := ⟨_, rfl⟩
  have hPc : Continuous P := hP ▸ by fun_prop
  have hQc : Continuous Q := hQ ▸ by fun_prop
  have hcc : Continuous c := hc ▸ by fun_prop
  have hcI : ∀ r, c r ∈ Icc (0 : ℝ) 1 := fun r ↦ by
    subst hc; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hcr : ∀ r ∈ Icc (0 : ℝ) 1, c r = r := fun r hr ↦ by
    subst hc; simp [min_eq_right hr.2, max_eq_right hr.1]
  have hPC : ∀ r ∈ Icc (0 : ℝ) 1, P r ∈ C := fun r hr ↦ by
    subst hP; exact hC.add_smul_sub_mem (interior_subset hz) hx hr
  have hQC : ∀ r ∈ Icc (0 : ℝ) 1, Q r ∈ C := fun r hr ↦ by
    subst hQ; exact hC.add_smul_sub_mem (interior_subset hz) hy hr
  have hRC : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, P r + s • (Q r - P r) ∈ C :=
    fun r hr s hs ↦ hC.add_smul_sub_mem (hPC r hr) (hQC r hr) hs
  have hint : ∀ {w : E}, w ∈ C → ∀ r ∈ Ico (0 : ℝ) 1, z + r • (w - z) ∈ interior C := by
    intro w hw r hr
    have : z + r • (w - z) = (1 - r) • z + r • w := by module
    rw [this]
    exact hC.combo_interior_self_mem_interior hz hw (by linarith [hr.2]) hr.1 (by ring)
  have hRi : ∀ r ∈ Ico (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, P r + s • (Q r - P r) ∈ interior C :=
    fun r hr s hs ↦ hC.interior.add_smul_sub_mem (hP ▸ hint hx r hr) (hQ ▸ hint hy r hr) hs
  -- The parameter-dependent integrand, made globally continuous by clamping to `[0, 1]`.
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ → ℝ, H = fun r s ↦
      φ (dLC f U (P (c r) + c s • (Q (c r) - P (c r)), Q (c r) - P (c r))) := ⟨_, rfl⟩
  have hHc : Continuous (uncurry H) := by
    have hm : Continuous fun q : ℝ × ℝ ↦
        (P (c q.1) + c q.2 • (Q (c q.1) - P (c q.1)), Q (c q.1) - P (c q.1)) := by fun_prop
    have := φ.continuous.comp (hf.continuousOn_dLC.comp_continuous hm
      fun q ↦ ⟨hCU (hRC _ (hcI _) _ (hcI _)), mem_univ _⟩)
    subst hH
    exact this
  have hB : Continuous fun r ↦ ∫ s in (0 : ℝ)..1, H r s :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hHc 0 1
  have hHeq : ∀ r ∈ Icc (0 : ℝ) 1, ∫ s in (0 : ℝ)..1, H r s =
      ∫ s in (0 : ℝ)..1, φ (dLC f U (P r + s • (Q r - P r), Q r - P r)) := by
    intro r hr
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le zero_le_one] at hs
    simp only [hH, hcr r hr, hcr s hs]
  have hA : ContinuousOn (fun r ↦ φ (f (Q r)) - φ (f (P r))) (Icc 0 1) :=
    (φ.continuous.comp_continuousOn (hf.continuousOn.comp hQc.continuousOn
      fun r hr ↦ hCU (hQC r hr))).sub
    (φ.continuous.comp_continuousOn (hf.continuousOn.comp hPc.continuousOn
      fun r hr ↦ hCU (hPC r hr)))
  have hEq : EqOn (fun r ↦ φ (f (Q r)) - φ (f (P r))) (fun r ↦ ∫ s in (0 : ℝ)..1, H r s)
      (Ico 0 1) := by
    intro r hr
    simp only
    rw [hHeq r (Ico_subset_Icc_self hr)]
    have key := hf.contDiffMBOn_interior.integral_dMB (x := P r) (h := Q r - P r)
      (fun s hs ↦ interior_mono hCU (hRi r hr s hs)) φ
    rw [add_sub_cancel] at key
    rw [key]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le zero_le_one] at hs
    rw [dLC_of_mem_interior f (p := (P r + s • (Q r - P r), Q r - P r))
      (interior_mono hCU (hRi r hr s hs))]
  have h1 := EqOn.of_subset_closure hEq hA hB.continuousOn Ico_subset_Icc_self
    (by rw [closure_Ico zero_ne_one]) (right_mem_Icc.mpr zero_le_one)
  simp only at h1
  rw [hHeq 1 (right_mem_Icc.mpr zero_le_one)] at h1
  have hP1 : P 1 = x := by subst hP; simp
  have hQ1 : Q 1 = y := by subst hQ; simp
  rwa [hP1, hQ1] at h1

/-- Mean value inclusion on a convex set `C ⊆ U` with an interior point: the difference
quotient lies in the closed convex hull of the derivatives along the segment. -/
theorem ContDiffLC.quotient_mem_closure_convexHull_of_convex {g : E → F} {U C : Set E}
    (hd : HasDenseInterior U) (hg : ContDiffLC 1 g U) (hCU : C ⊆ U) (hC : Convex ℝ C) {z : E}
    (hz : z ∈ interior C) {y v : E} {t : ℝ} (ht : t ≠ 0) (hy : y ∈ C) (hyt : y + t • v ∈ C) :
    t⁻¹ • (g (y + t • v) - g y) ∈
      closure (convexHull ℝ ((fun s : ℝ ↦ dLC g U (y + s • (t • v), v)) '' Icc 0 1)) := by
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, y + s • (t • v) ∈ C := fun s hs ↦ by
    simpa using hC.add_smul_sub_mem hy hyt hs
  by_contra hnot
  obtain ⟨φ, u, hlt, hgt⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _).closure isClosed_closure hnot
  have hcont : ContinuousOn (fun s : ℝ ↦ φ (dLC g U (y + s • (t • v), v))) (Icc 0 1) :=
    φ.continuous.comp_continuousOn (hg.continuousOn_dLC.comp (by fun_prop)
      fun s hs ↦ ⟨hCU (hseg s hs), mem_univ _⟩)
  have hle : ∫ s in (0 : ℝ)..1, φ (dLC g U (y + s • (t • v), v)) ≤ u := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) zero_le_one
      (hcont.intervalIntegrable_of_Icc zero_le_one)
      (continuousOn_const.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one)
      (fun s hs ↦ (hlt _ (subset_closure (subset_convexHull ℝ _ ⟨s, hs, rfl⟩))).le)
    simpa using this
  have hftc := hg.integral_dLC_of_convex hCU hC hz hy hyt φ
  simp only [add_sub_cancel_left] at hftc
  have hsmul : ∫ s in (0 : ℝ)..1, φ (dLC g U (y + s • (t • v), t • v)) =
      t * ∫ s in (0 : ℝ)..1, φ (dLC g U (y + s • (t • v), v)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le zero_le_one] at hs
    simp only [hg.dLC_smul hd (hCU (hseg s hs)), map_smul, smul_eq_mul]
  have hq : φ (t⁻¹ • (g (y + t • v) - g y)) =
      ∫ s in (0 : ℝ)..1, φ (dLC g U (y + s • (t • v), v)) := by
    rw [map_smul, map_sub, smul_eq_mul, hftc, hsmul, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
  linarith

/-- [GN26, Lemma 1.4.9]: on a locally convex subset with dense interior, the difference
quotient `t⁻¹ • (g (y + t • v) - g y)` of a `C^1` map tends to `dg(y, v)` as
`(y', v', t) → (y, v, 0)` with `t ≠ 0` and `y', y' + t • v' ∈ U`. -/
theorem ContDiffLC.tendsto_quotient {g : E → F} {U : Set E} (hU : IsLocallyConvexSubset U)
    (hd : HasDenseInterior U) (hg : ContDiffLC 1 g U) {y v : E} (hy : y ∈ U) :
    Tendsto (fun p : E × E × ℝ ↦ p.2.2⁻¹ • (g (p.1 + p.2.2 • p.2.1) - g p.1))
      (𝓝[{p | p.1 ∈ U ∧ p.1 + p.2.2 • p.2.1 ∈ U ∧ p.2.2 ≠ 0}] (y, v, 0))
      (𝓝 (dLC g U (y, v))) := by
  refine Filter.tendsto_def.mpr fun N hN ↦ ?_
  obtain ⟨K, hK, hKc, hKconv, hKN⟩ := exists_closed_convex_nhds_subset hN
  have hcw : ContinuousWithinAt (dLC g U) (U ×ˢ univ) (y, v) :=
    hg.continuousOn_dLC (y, v) ⟨hy, mem_univ _⟩
  obtain ⟨O, hO, hOK⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hcw.preimage_mem_nhdsWithin hK)
  obtain ⟨W, hW, hyW, -, hWc, z, hz⟩ := hU.exists_isOpen_convex_interior hd hy univ_mem
  have hev : ∀ᶠ q : E × E in 𝓝 (y, v), q.1 ∈ W ∧ q ∈ O :=
    (continuous_fst.continuousAt.eventually_mem (hW.mem_nhds hyW)).and hO
  have htube : ∀ᶠ p : E × E × ℝ in 𝓝 (y, v, 0), ∀ s ∈ Icc (0 : ℝ) 1,
      p.1 + s • (p.2.2 • p.2.1) ∈ W ∧ (p.1 + s • (p.2.2 • p.2.1), p.2.1) ∈ O := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦ ?_
    have hΨ : Continuous fun w : (E × E × ℝ) × ℝ ↦
        (w.1.1 + w.2 • (w.1.2.2 • w.1.2.1), w.1.2.1) := by
      fun_prop
    have : Tendsto (fun w : (E × E × ℝ) × ℝ ↦ (w.1.1 + w.2 • (w.1.2.2 • w.1.2.1), w.1.2.1))
        (𝓝 ((y, v, 0), s)) (𝓝 (y, v)) := by
      simpa using hΨ.tendsto ((y, v, (0 : ℝ)), s)
    exact this.eventually hev
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [htube] with p hp hpS
  obtain ⟨hp1, hp2, hp0⟩ := hpS
  have hW0 : p.1 ∈ U ∩ W := ⟨hp1, by simpa using (hp 0 ⟨le_rfl, zero_le_one⟩).1⟩
  have hW1 : p.1 + p.2.2 • p.2.1 ∈ U ∩ W := ⟨hp2, by simpa using (hp 1 ⟨zero_le_one, le_rfl⟩).1⟩
  have hmem := hg.quotient_mem_closure_convexHull_of_convex hd inter_subset_left hWc hz hp0 hW0 hW1
  refine hKN (closure_minimal (convexHull_min ?_ hKconv) hKc hmem)
  rintro _ ⟨s, hs, rfl⟩
  have hsC : p.1 + s • (p.2.2 • p.2.1) ∈ U ∩ W := by
    simpa using hWc.add_smul_sub_mem hW0 hW1 hs
  exact hOK ⟨(hp s hs).2, hsC.1, mem_univ _⟩

/-- [GN26, Proposition 1.4.8]: the mean value theorem
`φ (f (x + h)) - φ (f x) = ∫₀¹ φ (df(x + t h, h)) dt` along every segment contained in a locally
convex subset `U` with dense interior, for continuous linear functionals `φ` (weak form: no
completeness of `F` is needed). -/
theorem ContDiffLC.integral_dLC {f : E → F} {U : Set E} (hU : IsLocallyConvexSubset U)
    (hd : HasDenseInterior U) (hf : ContDiffLC 1 f U) {x h : E}
    (hxh : ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) (φ : F →L[ℝ] ℝ) :
    φ (f (x + h)) - φ (f x) = ∫ t in (0 : ℝ)..1, φ (dLC f U (x + t • h, h)) := by
  have hline : Continuous fun t : ℝ ↦ x + t • h := by fun_prop
  have hcont : ContinuousOn (fun t : ℝ ↦ φ (f (x + t • h))) (Icc 0 1) :=
    φ.continuous.comp_continuousOn (hf.continuousOn.comp hline.continuousOn hxh)
  have hd' : ContinuousOn (fun t : ℝ ↦ φ (dLC f U (x + t • h, h))) (Icc 0 1) :=
    φ.continuous.comp_continuousOn (hf.continuousOn_dLC.comp (by fun_prop)
      fun t ht ↦ ⟨hxh t ht, mem_univ _⟩)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ ↦ φ (f (x + t • h)))
      (φ (dLC f U (x + t • h, h))) (Ioi t) t := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self (by simp)]
    have hq := hf.tendsto_quotient hU hd (hxh t htI) (v := h)
    have hpt : ∀ r : ℝ, x + t • h + (r - t) • h = x + r • h := fun r ↦ by
      rw [sub_smul]; abel
    have hmap : Tendsto (fun r : ℝ ↦ (x + t • h, h, r - t)) (𝓝[Ioi t] t)
        (𝓝[{p : E × E × ℝ | p.1 ∈ U ∧ p.1 + p.2.2 • p.2.1 ∈ U ∧ p.2.2 ≠ 0}]
          (x + t • h, h, 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Continuous fun r : ℝ ↦ (x + t • h, h, r - t) := by fun_prop
        simpa using (this.tendsto t).mono_left nhdsWithin_le_nhds
      · have hlt : ∀ᶠ r in 𝓝[Ioi t] t, r < 1 := nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
        filter_upwards [self_mem_nhdsWithin, hlt] with r (hr : t < r) hr1
        refine ⟨hxh t htI, ?_, sub_ne_zero.mpr (ne_of_gt hr)⟩
        rw [hpt]
        exact hxh r ⟨ht.1.le.trans hr.le, hr1.le⟩
    refine ((φ.continuous.tendsto _).comp (hq.comp hmap)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : t < r)
    simp only [comp_apply, slope_def_field, map_smul, map_sub, smul_eq_mul, hpt]
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hcont hderiv
    (hd'.intervalIntegrable_of_Icc zero_le_one)
  simpa using this.symm

/-! ### The chain rule -/

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- [GN26, Proposition 1.4.10] for `k = 1`, with the formula
`d(g ∘ f)(x, h) = dg(f x, df(x, h))` on all of `U × E`. -/
theorem ContDiffLC.comp_one {f : E → F} {g : F → G} {U : Set E} {V : Set F}
    (hd : HasDenseInterior U) (hV : IsLocallyConvexSubset V) (hVd : HasDenseInterior V)
    (hg : ContDiffLC 1 g V) (hf : ContDiffLC 1 f U) (hUV : MapsTo f U V) :
    ContDiffLC 1 (g ∘ f) U ∧
      EqOn (dLC (g ∘ f) U) (fun p ↦ dLC g V (f p.1, dLC f U p)) (U ×ˢ univ) := by
  have hD : ∀ x ∈ interior U, ∀ h,
      HasDirDerivAt (g ∘ f) x h (dLC g V (f (x, h).1, dLC f U (x, h))) := by
    intro x hx h
    have hfx := hf.2.1 x hx h
    rw [dLC_of_mem_interior f (p := (x, h)) hx]
    have hq := hg.tendsto_quotient hV hVd (hUV (interior_subset hx)) (v := dMB f (x, h))
    have hin : ∀ᶠ t in 𝓝[≠] (0 : ℝ), x + t • h ∈ U := by
      have hc : Continuous fun t : ℝ ↦ x + t • h := by fun_prop
      have : Tendsto (fun t : ℝ ↦ x + t • h) (𝓝 0) (𝓝 x) := by simpa using hc.tendsto 0
      exact nhdsWithin_le_nhds
        ((this.eventually (mem_interior_iff_mem_nhds.mp hx)).mono fun _ ht ↦ ht)
    have hΔ : Tendsto (fun t : ℝ ↦ (f x, t⁻¹ • (f (x + t • h) - f x), t)) (𝓝[≠] 0)
        (𝓝[{p : F × F × ℝ | p.1 ∈ V ∧ p.1 + p.2.2 • p.2.1 ∈ V ∧ p.2.2 ≠ 0}]
          (f x, dMB f (x, h), 0)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact tendsto_const_nhds.prodMk_nhds
          (hfx.prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
      · filter_upwards [hin, self_mem_nhdsWithin] with t ht (ht0 : t ≠ 0)
        refine ⟨hUV (interior_subset hx), ?_, ht0⟩
        simp only [smul_smul, mul_inv_cancel₀ ht0, one_smul, add_sub_cancel]
        exact hUV ht
    refine (hq.comp hΔ).congr' (eventually_nhdsWithin_of_forall fun t ht ↦ ?_)
    have ht : t ≠ 0 := ht
    simp [smul_smul, mul_inv_cancel₀ ht]
  have hcD : ContDiffLC 0 (fun p : E × E ↦ dLC g V (f p.1, dLC f U p)) (U ×ˢ univ) :=
    hg.continuousOn_dLC.comp ((hf.continuousOn.comp continuousOn_fst
      fun (p : E × E) (hp : p ∈ U ×ˢ univ) ↦ hp.1).prodMk
      hf.continuousOn_dLC) fun _ hp ↦ ⟨hUV hp.1, mem_univ _⟩
  exact ContDiffLC.of_hasDirDerivAt hd (hg.continuousOn.comp hf.continuousOn hUV) hD hcD

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Chain rule: the formula `d(g ∘ f)(x, h) = dg(f x, df(x, h))`, for every `x ∈ U`
([GN26, Proposition 1.4.10]). -/
theorem ContDiffLC.dLC_comp {f : E → F} {g : F → G} {U : Set E} {V : Set F}
    (hd : HasDenseInterior U) (hV : IsLocallyConvexSubset V) (hVd : HasDenseInterior V)
    (hg : ContDiffLC 1 g V) (hf : ContDiffLC 1 f U) (hUV : MapsTo f U V) {x : E} (hx : x ∈ U)
    (h : E) : dLC (g ∘ f) U (x, h) = dLC g V (f x, dLC f U (x, h)) :=
  (hg.comp_one hd hV hVd hf hUV).2 ⟨hx, mem_univ h⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Precomposition with a continuous linear open map (for instance a projection
`E × E' → E`) preserves `C^k`. -/
theorem ContDiffLC.comp_clm_of_isOpenMap : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁]
    [Module ℝ E₁] [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂]
    [TopologicalSpace E₂] [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
    [LocallyConvexSpace ℝ E₂] [T2Space E₂] (L : E₁ →L[ℝ] E₂) {f : E₂ → F} {U : Set E₂},
    IsOpenMap L → HasDenseInterior U → ContDiffLC k f U → ContDiffLC k (f ∘ L) (L ⁻¹' U) := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ E₂ _ _ _ _ _ _ _ L f U _ _ hf
    exact ContinuousOn.comp hf L.continuous.continuousOn fun _ hx ↦ hx
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ E₂ _ _ _ _ _ _ _ L f U hL hd hf
    have hint : interior (L ⁻¹' U) = L ⁻¹' interior U :=
      (hL.preimage_interior_eq_interior_preimage L.continuous U).symm
    have hdL : HasDenseInterior (L ⁻¹' U) := by
      intro x hx
      rw [hint, ← hL.preimage_closure_eq_closure_preimage L.continuous]
      exact hd hx
    have hLL : IsOpenMap (L.prodMap L) := by
      rw [ContinuousLinearMap.coe_prodMap']
      exact hL.prodMap hL
    have h2 := ih (L.prodMap L) hLL hd.prod_univ hf.2.2
    have hpre : (L.prodMap L) ⁻¹' (U ×ˢ univ) = (L ⁻¹' U) ×ˢ univ := by ext p; simp
    rw [hpre] at h2
    refine (ContDiffLC.of_hasDirDerivAt hdL (hf.1.comp L.continuous.continuousOn fun _ hx ↦ hx)
      (fun x hx h ↦ ?_) h2).1
    rw [hint] at hx
    have := hf.2.1 (L x) hx (L h)
    simp only [comp_apply, ContinuousLinearMap.coe_prodMap', Prod.map,
      dLC_of_mem_interior f (p := (L x, L h)) hx]
    exact this.congr fun t ↦ by simp

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
/-- [GN26, Lemma 1.4.6]: pairs of `C^k` maps are `C^k`. -/
theorem ContDiffLC.prodMk : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {f : E₁ → F} {g : E₁ → G} {U : Set E₁},
    HasDenseInterior U → ContDiffLC k f U → ContDiffLC k g U →
      ContDiffLC k (fun x ↦ (f x, g x)) U := by
  intro k
  induction k with
  | zero => intro E₁ _ _ _ _ _ _ _ f g U _ hf hg; exact ContinuousOn.prodMk hf hg
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ f g U hd hf hg
    refine (ContDiffLC.of_hasDirDerivAt (D := fun p ↦ (dLC f U p, dLC g U p)) hd
      (hf.1.prodMk hg.1) (fun x hx h ↦ ?_) (ih hd.prod_univ hf.2.2 hg.2.2)).1
    simp only [dLC_of_mem_interior f (p := (x, h)) hx, dLC_of_mem_interior g (p := (x, h)) hx]
    exact (hf.2.1 x hx h).prodMk (hg.2.1 x hx h)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
/-- [GN26, (1.45)]: the differential of a pair is the pair of differentials. -/
theorem ContDiffLC.dLC_prodMk {f : E → F} {g : E → G} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC 1 f U) (hg : ContDiffLC 1 g U) :
    EqOn (dLC (fun x ↦ (f x, g x)) U) (fun p ↦ (dLC f U p, dLC g U p)) (U ×ˢ univ) := by
  refine dLC_eqOn_of_continuousOn hd (hf.continuousOn_dLC.prodMk hg.continuousOn_dLC)
    fun p hp ↦ ?_
  simp only [dLC_of_mem_interior f hp.1, dLC_of_mem_interior g hp.1]
  exact (((hf.2.1 p.1 hp.1 p.2).prodMk (hg.2.1 p.1 hp.1 p.2)).dMB_eq).symm

/-- [GN26, Proposition 1.4.10]: chain rule for `C^k` maps between locally convex subsets
with dense interior. Only the target domain `V` needs to be locally convex. -/
theorem ContDiffLC.comp : ∀ {k : ℕ} {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]
    [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
    [LocallyConvexSpace ℝ E₁] [T2Space E₁] {F₁ : Type v} [AddCommGroup F₁] [Module ℝ F₁]
    [TopologicalSpace F₁] [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁]
    [LocallyConvexSpace ℝ F₁] [T2Space F₁] {f : E₁ → F₁} {g : F₁ → G} {U : Set E₁}
    {V : Set F₁}, HasDenseInterior U → IsLocallyConvexSubset V → HasDenseInterior V →
      ContDiffLC k g V → ContDiffLC k f U → MapsTo f U V → ContDiffLC k (g ∘ f) U := by
  intro k
  induction k with
  | zero =>
    intro E₁ _ _ _ _ _ _ _ F₁ _ _ _ _ _ _ _ f g U V _ _ _ hg hf hUV
    exact ContinuousOn.comp hg hf hUV
  | succ k ih =>
    intro E₁ _ _ _ _ _ _ _ F₁ _ _ _ _ _ _ _ f g U V hd hV hVd hg hf hUV
    obtain ⟨h1, heq⟩ := ContDiffLC.comp_one hd hV hVd (hg.of_le (by omega)) (hf.of_le (by omega))
      hUV
    refine ⟨h1.1, h1.2.1, ?_⟩
    have hfst : ContDiffLC k (f ∘ ContinuousLinearMap.fst ℝ E₁ E₁) (U ×ˢ univ) := by
      have := ContDiffLC.comp_clm_of_isOpenMap (ContinuousLinearMap.fst ℝ E₁ E₁)
        (by rw [ContinuousLinearMap.coe_fst']; exact isOpenMap_fst) hd hf.of_succ
      have hpre : (ContinuousLinearMap.fst ℝ E₁ E₁) ⁻¹' U = U ×ˢ univ := by ext; simp
      rwa [hpre] at this
    have hP := ContDiffLC.prodMk hd.prod_univ hfst hf.2.2
    have hc := ih hd.prod_univ (hV.prod isLocallyConvexSubset_univ) hVd.prod_univ hg.2.2 hP
      fun p hp ↦ ⟨hUV hp.1, mem_univ _⟩
    refine hc.congr fun p hp ↦ ?_
    simp only [comp_apply, ContinuousLinearMap.coe_fst']
    exact (heq hp).symm

/-- Composition on the left with a map that is `C^k` on an open set. -/
theorem ContDiffMBOn.comp_contDiffLC {k : ℕ} {f : E → F} {g : F → G} {U : Set E} {W : Set F}
    (hW : IsOpen W) (hg : ContDiffMBOn k g W) (hd : HasDenseInterior U) (hf : ContDiffLC k f U)
    (hUW : MapsTo f U W) : ContDiffLC k (g ∘ f) U :=
  ContDiffLC.comp hd hW.isLocallyConvexSubset hW.hasDenseInterior
    ((contDiffLC_iff_contDiffMBOn hW).mpr hg) hf hUW

/-- Smooth maps compose. -/
theorem SmoothLC.comp {f : E → F} {g : F → G} {U : Set E} {V : Set F} (hd : HasDenseInterior U)
    (hV : IsLocallyConvexSubset V) (hVd : HasDenseInterior V) (hg : SmoothLC g V)
    (hf : SmoothLC f U) (hUV : MapsTo f U V) : SmoothLC (g ∘ f) U :=
  fun k ↦ ContDiffLC.comp hd hV hVd (hg k) (hf k) hUV

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
theorem smoothLC_iff_smoothMBOn {f : E → F} {U : Set E} (hU : IsOpen U) :
    SmoothLC f U ↔ SmoothMBOn f U :=
  forall_congr' fun _ ↦ contDiffLC_iff_contDiffMBOn hU

/-! ### Linear maps, sums, products -/

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Continuous linear maps are `C^k` on every subset with dense interior. -/
theorem _root_.ContinuousLinearMap.contDiffLC (L : E →L[ℝ] F) (k : ℕ) {U : Set E}
    (hd : HasDenseInterior U) : ContDiffLC k L U :=
  ContDiffMBOn.contDiffLC isOpen_univ (L.contDiffMBOn k univ) (subset_univ U) hd

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
theorem contDiffLC_const (k : ℕ) (c : F) {U : Set E} (hd : HasDenseInterior U) :
    ContDiffLC k (fun _ : E ↦ c) U :=
  ContDiffMBOn.contDiffLC isOpen_univ (contDiffMBOn_const k c univ) (subset_univ U) hd

theorem contDiffLC_id (k : ℕ) {U : Set E} (hd : HasDenseInterior U) :
    ContDiffLC k (id : E → E) U :=
  (ContinuousLinearMap.id ℝ E).contDiffLC k hd

/-- Postcomposition with a continuous linear map preserves `C^k`. -/
theorem ContDiffLC.clm_comp {k : ℕ} {f : E → F} {U : Set E} (L : F →L[ℝ] G)
    (hd : HasDenseInterior U) (hf : ContDiffLC k f U) : ContDiffLC k (L ∘ f) U :=
  (L.contDiffMBOn k univ).comp_contDiffLC isOpen_univ hd hf (mapsTo_univ _ _)

/-- [GN26, Lemma 1.4.6] (converse direction): the components of a `C^k` map into a
product are `C^k`. -/
theorem ContDiffLC.fst {k : ℕ} {f : E → F × G} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC k f U) : ContDiffLC k (fun x ↦ (f x).1) U :=
  hf.clm_comp (ContinuousLinearMap.fst ℝ F G) hd

theorem ContDiffLC.snd {k : ℕ} {f : E → F × G} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC k f U) : ContDiffLC k (fun x ↦ (f x).2) U :=
  hf.clm_comp (ContinuousLinearMap.snd ℝ F G) hd

theorem ContDiffLC.add {k : ℕ} {f g : E → F} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC k f U) (hg : ContDiffLC k g U) : ContDiffLC k (fun x ↦ f x + g x) U :=
  (hf.prodMk hd hg).clm_comp (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F) hd

theorem ContDiffLC.sub {k : ℕ} {f g : E → F} {U : Set E} (hd : HasDenseInterior U)
    (hf : ContDiffLC k f U) (hg : ContDiffLC k g U) : ContDiffLC k (fun x ↦ f x - g x) U :=
  (hf.prodMk hd hg).clm_comp (ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F) hd

theorem ContDiffLC.const_smul {k : ℕ} {f : E → F} {U : Set E} (hd : HasDenseInterior U)
    (c : ℝ) (hf : ContDiffLC k f U) : ContDiffLC k (fun x ↦ c • f x) U :=
  hf.clm_comp (c • ContinuousLinearMap.id ℝ F) hd

/-- Product rule ([GN26, Remark 1.4.15] together with Proposition 1.3.5): for a
continuous bilinear map `β`, `x ↦ β (f x) (g x)` is `C^k` if `f` and `g` are. -/
theorem ContDiffLC.bilin {A : Type u₁} {B : Type u₂} [AddCommGroup A] [Module ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
    [T2Space A]
    [AddCommGroup B] [Module ℝ B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [ContinuousSMul ℝ B] [LocallyConvexSpace ℝ B] [T2Space B] (β : A →ₗ[ℝ] B →ₗ[ℝ] F)
    (hβ : Continuous fun p : A × B ↦ β p.1 p.2) {k : ℕ} {f : E → A} {g : E → B} {U : Set E}
    (hd : HasDenseInterior U) (hf : ContDiffLC k f U) (hg : ContDiffLC k g U) :
    ContDiffLC k (fun x ↦ β (f x) (g x)) U :=
  (contDiffMBOn_bilin β hβ k).comp_contDiffLC isOpen_univ hd (hf.prodMk hd hg) (mapsTo_univ _ _)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] in
/-- Products of `C^k` maps on products of subsets with dense interior. -/
theorem ContDiffLC.prodMap {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
    {k : ℕ} {f : E → F} {g : E₂ → G} {U : Set E} {V : Set E₂} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLC k f U) (hg : ContDiffLC k g V) :
    ContDiffLC k (Prod.map f g) (U ×ˢ V) := by
  have h1 := ContDiffLC.comp_clm_of_isOpenMap (ContinuousLinearMap.fst ℝ E E₂)
    (by rw [ContinuousLinearMap.coe_fst']; exact isOpenMap_fst) hU hf
  have h2 := ContDiffLC.comp_clm_of_isOpenMap (ContinuousLinearMap.snd ℝ E E₂)
    (by rw [ContinuousLinearMap.coe_snd']; exact isOpenMap_snd) hV hg
  have hp1 : (ContinuousLinearMap.fst ℝ E E₂) ⁻¹' U = U ×ˢ univ := by ext; simp
  have hp2 : (ContinuousLinearMap.snd ℝ E E₂) ⁻¹' V = univ ×ˢ V := by ext; simp
  rw [hp1] at h1
  rw [hp2] at h2
  have hUV := hU.prod hV
  refine (ContDiffLC.prodMk hUV (h1.mono (prod_mono subset_rfl (subset_univ V)) hUV)
    (h2.mono (prod_mono (subset_univ U) subset_rfl) hUV)).congr fun _ _ ↦ rfl

end Calculus

end LocallyConvex.Analysis

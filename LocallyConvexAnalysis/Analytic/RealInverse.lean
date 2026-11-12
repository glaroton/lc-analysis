/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Complex.Nijenhuis
public import LocallyConvexAnalysis.Analytic.BanachHolomorphic

/-!
# The real analytic inverse function theorem on Banach spaces

We show that the inverse of a real analytic diffeomorphism between open subsets of real Banach
spaces is real analytic (in the sense of Milnor, `RealAnalyticOn`), and deduce the inverse
function theorem for real analytic maps.

## Main results

* `RealAnalyticOn.exists_holomorphic_extension_normed`: a real analytic map between Banach spaces
  has a holomorphic extension between the normed complexifications.
* `OpenPartialHomeomorph.realAnalyticOn_symm`: if a partial homeomorphism `φ` between open subsets
  of real Banach spaces is real analytic (in the sense of Milnor, `RealAnalyticOn`) and its
  derivative is invertible at every point, then `φ⁻¹` is real analytic.
* `RealAnalyticOn.exists_openPartialHomeomorph`: the inverse function theorem for real analytic
  maps, with real analytic local inverse.

## Implementation notes

Complexify. A complex analytic extension `g : Ω → F_ℂ` of `φ`, on an open set `Ω` of the normed
complexification `E_ℂ`, has at `x₀ + i0` the derivative `Dφ(x₀)_ℂ`, which is invertible. The
holomorphic inverse function theorem (Mathlib's, over `ℂ`) gives a holomorphic local inverse `ψ`
of `g`, and `ψ(y + i0) = φ⁻¹(y) + i0` for real `y` near `φ(x₀)`, since `g(φ⁻¹(y) + i0) = y + i0`.
So `ψ` is a complex analytic extension of `φ⁻¹` near `φ(x₀)` (`realAnalyticOn_symm_local`), and
real analyticity is a local property (`RealAnalyticOn.of_local`, [GN26, Lemma 2.2.3]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

open Complexification NormedComplexification

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem NormedComplexification.re_ofRealCLM_add_I_smul (a b : E) :
    re (toCx (ofRealCLM a + Complex.I • ofRealCLM b)) = a := by
  change re (ofReal a + Complex.I • ofReal b) = a
  simp

theorem NormedComplexification.im_ofRealCLM_add_I_smul (a b : E) :
    im (toCx (ofRealCLM a + Complex.I • ofRealCLM b)) = b := by
  change im (ofReal a + Complex.I • ofReal b) = b
  simp

end Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A real analytic map between Banach spaces has a holomorphic extension between the normed
complexifications. -/
theorem RealAnalyticOn.exists_holomorphic_extension_normed {f : E → F} {U : Set E}
    (hf : RealAnalyticOn f U) :
    ∃ Ω : Set (NormedComplexification E), IsOpen Ω ∧
      ∃ g : NormedComplexification E → NormedComplexification F, DifferentiableOn ℂ g Ω ∧
        ∀ x ∈ U, ofRealCLM x ∈ Ω ∧ g (ofRealCLM x) = ofRealCLM (f x) := by
  obtain ⟨V, hV, h, hh, hext⟩ := hf
  have hΩ : IsOpen (ofNormed ⁻¹' V : Set (NormedComplexification E)) :=
    hV.preimage ofNormed.continuous
  refine ⟨ofNormed ⁻¹' V, hΩ, toNormed ∘ h ∘ ofNormed, ?_, fun x hx ↦ ⟨(hext x hx).1, ?_⟩⟩
  · exact ((toNormed.complexAnalyticOn isOpen_univ).comp
      (hh.comp (ofNormed.complexAnalyticOn hΩ) hΩ hV fun _ hz ↦ hz) hΩ isOpen_univ
      (mapsTo_univ _ _)).differentiableOn hΩ
  · change toNormed (h (ofReal x)) = _
    rw [(hext x hx).2]
    rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- A complex linear map `E_ℂ → F_ℂ` extending a real isomorphism `E ≅ F` is bijective. -/
theorem bijective_of_extends {L : NormedComplexification E →L[ℂ] NormedComplexification F}
    {e : E ≃L[ℝ] F} (hL : ∀ a, L (ofRealCLM a) = ofRealCLM (e a)) : Bijective L := by
  have hLp : ∀ a b, L (ofRealCLM a + Complex.I • ofRealCLM b) =
      ofRealCLM (e a) + Complex.I • ofRealCLM (e b) := fun a b ↦ by
    rw [map_add, map_smul, hL, hL]
  refine ⟨(injective_iff_map_eq_zero L).2 fun p hp ↦ ?_, fun q ↦ ?_⟩
  · rw [eq_ofRealCLM_add_I_smul p, hLp] at hp
    have h1 : e (re (toCx p)) = 0 := by
      have := congrArg (fun q ↦ re (toCx q)) hp
      simpa using this
    have h2 : e (im (toCx p)) = 0 := by
      have := congrArg (fun q ↦ im (toCx q)) hp
      simpa using this
    rw [eq_ofRealCLM_add_I_smul p, e.map_eq_zero_iff.1 h1, e.map_eq_zero_iff.1 h2, map_zero,
      smul_zero, add_zero]
  · refine ⟨ofRealCLM (e.symm (re (toCx q))) + Complex.I • ofRealCLM (e.symm (im (toCx q))), ?_⟩
    rw [hLp, e.apply_symm_apply, e.apply_symm_apply]
    exact (eq_ofRealCLM_add_I_smul q).symm

/-- **Local real analytic inverse.** -/
theorem realAnalyticOn_symm_local (φ : OpenPartialHomeomorph E F) (hφ : RealAnalyticOn φ φ.source)
    {x₀ : E} (hx₀ : x₀ ∈ φ.source) {e : E ≃L[ℝ] F} (he : HasFDerivAt φ (e : E →L[ℝ] F) x₀) :
    ∃ W : Set F, IsOpen W ∧ φ x₀ ∈ W ∧ RealAnalyticOn φ.symm (φ.target ∩ W) := by
  obtain ⟨Ω, hΩ, g, hg, hext⟩ := hφ.exists_holomorphic_extension_normed
  set z₀ : NormedComplexification E := ofRealCLM x₀
  have hz₀ : z₀ ∈ Ω := (hext x₀ hx₀).1
  have hgd : HasFDerivAt g (fderiv ℂ g z₀) z₀ :=
    ((hg z₀ hz₀).differentiableAt (hΩ.mem_nhds hz₀)).hasFDerivAt
  set L := fderiv ℂ g z₀
  -- `L = Dφ(x₀)_ℂ` is invertible
  have hL : ∀ a, L (ofRealCLM a) = ofRealCLM (e a) := by
    have h1 : HasFDerivAt (fun x ↦ g (ofRealCLM x)) ((L.restrictScalars ℝ).comp ofRealCLM) x₀ :=
      (hgd.restrictScalars ℝ).comp x₀ ofRealCLM.hasFDerivAt
    have h2 : HasFDerivAt (fun x ↦ ofRealCLM (φ x)) (ofRealCLM.comp (e : E →L[ℝ] F)) x₀ :=
      ofRealCLM.hasFDerivAt.comp x₀ he
    have h3 : (fun x ↦ ofRealCLM (φ x)) =ᶠ[𝓝 x₀] fun x ↦ g (ofRealCLM x) :=
      eventually_of_mem (φ.open_source.mem_nhds hx₀) fun x hx ↦ (hext x hx).2.symm
    have h := (h1.congr_of_eventuallyEq h3).unique h2
    exact fun a ↦ congrArg (fun T : E →L[ℝ] NormedComplexification F ↦ T a) h
  have hbij := bijective_of_extends hL
  set Le := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)
  have hder : HasFDerivAt g (Le : NormedComplexification E →L[ℂ] NormedComplexification F) z₀ :=
    hgd
  -- the holomorphic inverse function theorem
  have hgC : ContDiffOn ℂ 1 g Ω := by exact_mod_cast hg.contDiffOn_one_complex hΩ
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  set H := (hgC.contDiffAt (hΩ.mem_nhds hz₀)).toOpenPartialHomeomorph g hder hn
  set S := Ω ∩ fderiv ℂ g ⁻¹' range ((↑) : (NormedComplexification E ≃L[ℂ]
    NormedComplexification F) → NormedComplexification E →L[ℂ] NormedComplexification F)
  have hS : IsOpen S := (hgC.continuousOn_fderiv_of_isOpen hΩ le_rfl).isOpen_inter_preimage
    hΩ ContinuousLinearEquiv.isOpen
  have hz₀S : z₀ ∈ S := ⟨hz₀, Le, hder.fderiv.symm⟩
  set ψ := H.restrOpen S hS
  have hsrc : ψ.source ⊆ S := fun z hz ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source] at hz; exact hz.2
  have hz₀ψ : z₀ ∈ ψ.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hder hn, hz₀S⟩
  have hψs : DifferentiableOn ℂ ψ.symm ψ.target := by
    intro y hy
    obtain ⟨hpΩ, e', he'⟩ := hsrc (ψ.map_target hy)
    have hd : HasFDerivAt ψ (e' : NormedComplexification E →L[ℂ] NormedComplexification F)
        (ψ.symm y) := by
      rw [he']
      exact ((hg _ hpΩ).differentiableAt (hΩ.mem_nhds hpΩ)).hasFDerivAt
    exact ((ψ.contDiffAt_symm hy hd (hgC.contDiffAt (hΩ.mem_nhds hpΩ))).differentiableAt
      (by simp)).differentiableWithinAt
  -- at real points, `ψ` inverts `φ`
  set W : Set F := ofRealCLM ⁻¹' ψ.target ∩
    (φ.target ∩ φ.symm ⁻¹' (ofRealCLM ⁻¹' ψ.source))
  have hW : IsOpen W := (ψ.open_target.preimage ofRealCLM.continuous).inter
    (φ.continuousOn_symm.isOpen_inter_preimage φ.open_target
      (ψ.open_source.preimage ofRealCLM.continuous))
  have hgψ : ∀ z, ψ z = g z := fun _ ↦ rfl
  have hy₀W : φ x₀ ∈ W := by
    refine ⟨?_, φ.map_source hx₀, ?_⟩
    · have h := ψ.map_source hz₀ψ
      rw [hgψ, (hext x₀ hx₀).2] at h
      exact h
    · change ofRealCLM (φ.symm (φ x₀)) ∈ ψ.source
      rw [φ.left_inv hx₀]
      exact hz₀ψ
  have hreal : ∀ y ∈ φ.target ∩ W, ψ.symm (ofRealCLM y) = ofRealCLM (φ.symm y) := by
    intro y hy
    have hs : ofRealCLM (φ.symm y) ∈ ψ.source := hy.2.2.2
    have h : ψ (ofRealCLM (φ.symm y)) = ofRealCLM y := by
      rw [hgψ, (hext _ (φ.map_target hy.1)).2, φ.right_inv hy.1]
    rw [← h, ψ.left_inv hs]
  -- the complex analytic extension of `φ⁻¹`
  set V : Set (Complexification F) := toNormed ⁻¹' ψ.target
  have hV : IsOpen V := ψ.open_target.preimage toNormed.continuous
  refine ⟨W, hW, hy₀W, V, hV, ofNormed ∘ ψ.symm ∘ toNormed, ?_, fun y hy ↦ ⟨hy.2.1, ?_⟩⟩
  · exact (ofNormed.complexAnalyticOn isOpen_univ).comp
      ((hψs.complexAnalyticOn ψ.open_target).comp (toNormed.complexAnalyticOn hV) hV
        ψ.open_target fun _ hz ↦ hz) hV isOpen_univ (mapsTo_univ _ _)
  · change ofNormed (ψ.symm (ofRealCLM y)) = _
    rw [hreal y hy]
    rfl

/-- **Inverses of real analytic diffeomorphisms are real analytic.** If a partial homeomorphism
`φ` between open subsets of real Banach spaces is real analytic (in the sense of Milnor) with
invertible derivative at every point of its source, then `φ⁻¹` is real analytic. -/
theorem _root_.OpenPartialHomeomorph.realAnalyticOn_symm (φ : OpenPartialHomeomorph E F)
    (hφ : RealAnalyticOn φ φ.source)
    (hd : ∀ x ∈ φ.source, ∃ e : E ≃L[ℝ] F, HasFDerivAt φ (e : E →L[ℝ] F) x) :
    RealAnalyticOn φ.symm φ.target :=
  RealAnalyticOn.of_local φ.open_target fun y hy ↦ by
    obtain ⟨e, he⟩ := hd _ (φ.map_target hy)
    obtain ⟨W, hW, hyW, h⟩ := realAnalyticOn_symm_local φ hφ (φ.map_target hy) he
    rw [φ.right_inv hy] at hyW
    exact ⟨W, hW, hyW, h⟩

/-- **The real analytic inverse function theorem** on Banach spaces: a map real analytic (in the
sense of Milnor) near `x₀`, with invertible derivative at `x₀`, is a real analytic
diffeomorphism between neighbourhoods of `x₀` and `f(x₀)`. -/
theorem RealAnalyticOn.exists_openPartialHomeomorph {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : RealAnalyticOn f U) {x₀ : E} (hx₀ : x₀ ∈ U) {e : E ≃L[ℝ] F}
    (he : HasFDerivAt f (e : E →L[ℝ] F) x₀) :
    ∃ φ : OpenPartialHomeomorph E F, x₀ ∈ φ.source ∧ φ.source ⊆ U ∧ EqOn φ f φ.source ∧
      RealAnalyticOn φ φ.source ∧ RealAnalyticOn φ.symm φ.target := by
  have hfC : ContDiffOn ℝ ∞ f U := (smoothMBOn_iff_contDiffOn hU).1 (hf.smoothMBOn hU)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set H := (hfC.contDiffAt (hU.mem_nhds hx₀)).toOpenPartialHomeomorph f he hn
  set S := U ∩ fderiv ℝ f ⁻¹' range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hS : IsOpen S := (hfC.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
    hU ContinuousLinearEquiv.isOpen
  have hx₀S : x₀ ∈ S := ⟨hx₀, e, he.fderiv.symm⟩
  set φ := H.restrOpen S hS
  have hsrc : φ.source ⊆ S := fun x hx ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx; exact hx.2
  have hφa : RealAnalyticOn φ φ.source := (hf.mono fun x hx ↦ (hsrc hx).1).congr fun _ _ ↦ rfl
  refine ⟨φ, ?_, fun x hx ↦ (hsrc hx).1, fun _ _ ↦ rfl, hφa, φ.realAnalyticOn_symm hφa ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ he hn, hx₀S⟩
  · intro x hx
    obtain ⟨hxU, e', he'⟩ := hsrc hx
    refine ⟨e', ?_⟩
    rw [he']
    exact ((hfC.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).hasFDerivAt

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Complex
public import LocallyConvexAnalysis.Analytic.WeakHolomorphic
public import LocallyConvexAnalysis.Calculus.MBFrechet
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
# Holomorphic maps between complex normed spaces

On complex normed spaces, complex analytic maps in the sense of Glöckner–Neeb
(`ComplexAnalyticOn`) are exactly Mathlib's complex differentiable maps
(`complexAnalyticOn_iff_differentiableOn`). This lets the Banach space tools of Mathlib (the
inverse function theorem, the contraction principle, Bochner integrals) be used for complex
analytic maps.

## Main results

* `complexAnalyticOn_iff_differentiableOn`: on an open subset of a complex normed space, with
  complete target, a map is complex analytic in the sense of Glöckner–Neeb if and only if it is
  complex differentiable.
* `DifferentiableOn.gateauxAnalyticOn`, `DifferentiableOn.complexAnalyticOn`: a complex
  differentiable map is continuous and complex analytic along every complex line (Mathlib's
  one-variable theory, through `CAnalyticOn.of_weak`), hence complex analytic
  (`complexAnalyticOn_iff_gateauxAnalyticOn`).
* `ComplexAnalyticOn.differentiableOn`: a complex analytic map is real Fréchet smooth
  (`smoothMBOn_iff_contDiffOn`), and its real derivative is complex linear.
* `DifferentiableOn.contDiffOn_one_complex`: complex differentiable maps are `C¹` over `ℂ`.
* `TendstoLocallyUniformlyOn.differentiableOn_complex`: **locally uniform limits of holomorphic
  maps on open subsets of complex normed spaces are holomorphic.** Mathlib has this for open
  subsets of `ℂ`; along complex lines it gives Gâteaux analyticity, and the limit is continuous.

## Implementation notes

The passage from complex differentiability to complex analyticity uses the completeness of the
target (through `CAnalyticOn.of_weak`, which needs Mackey completeness); the converse does not.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {U : Set E}

/-- A complex differentiable map is complex analytic along every complex line. -/
theorem _root_.DifferentiableOn.gateauxAnalyticOn [CompleteSpace F] (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : GateauxAnalyticOn f U := by
  intro x _ y
  have hg : Differentiable ℂ fun z : ℂ ↦ x + z • y := by fun_prop
  have hV : IsOpen {z : ℂ | x + z • y ∈ U} := hU.preimage hg.continuous
  have hline : DifferentiableOn ℂ (fun z : ℂ ↦ f (x + z • y)) {z : ℂ | x + z • y ∈ U} :=
    hf.comp hg.differentiableOn fun _ hz ↦ hz
  exact CAnalyticOn.of_weak hV hline.continuousOn fun ℓ ↦
    ℓ.differentiable.comp_differentiableOn hline

/-- **Complex differentiable maps are complex analytic** (Glöckner–Neeb). -/
theorem _root_.DifferentiableOn.complexAnalyticOn [CompleteSpace F] (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ComplexAnalyticOn f U :=
  (complexAnalyticOn_iff_gateauxAnalyticOn hU).2 ⟨hf.continuousOn, hf.gateauxAnalyticOn hU⟩

/-- **Complex analytic maps are complex differentiable**: they are real Fréchet smooth, with
complex linear derivatives. -/
theorem ComplexAnalyticOn.differentiableOn (hf : ComplexAnalyticOn f U) (hU : IsOpen U) :
    DifferentiableOn ℂ f U := by
  have hhol := (complexAnalyticOn_iff_holomorphicOn hU).1 hf
  have hC : ContDiffOn ℝ ∞ f U := (smoothMBOn_iff_contDiffOn hU).1 hhol.1
  intro x hx
  have hdx : DifferentiableAt ℝ f x :=
    (hC.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hL : ∀ v, fderiv ℝ f x v = Analysis.dMB f (x, v) := fun v ↦
    ((hdx.hasFDerivAt.hasDirDerivAt v).dMB_eq).symm
  let L : E →L[ℂ] F :=
    { toFun := fderiv ℝ f x
      map_add' := (fderiv ℝ f x).map_add
      map_smul' := fun c v ↦ by
        simp only [RingHom.id_apply, hL]
        exact hhol.2 x hx c v
      cont := (fderiv ℝ f x).continuous }
  exact (hasFDerivAt_of_restrictScalars ℝ hdx.hasFDerivAt (f' := L) rfl).differentiableAt
    |>.differentiableWithinAt

/-- On complex normed spaces, complex analyticity in the sense of Glöckner–Neeb is complex
differentiability (for complete `F`). -/
theorem complexAnalyticOn_iff_differentiableOn [CompleteSpace F] (hU : IsOpen U) :
    ComplexAnalyticOn f U ↔ DifferentiableOn ℂ f U :=
  ⟨fun h ↦ h.differentiableOn hU, fun h ↦ h.complexAnalyticOn hU⟩

/-- **Complex differentiable maps are `C¹` over `ℂ`** on open subsets of complex normed spaces
(for complete `F`). Their real derivatives are continuous, since complex differentiable maps are
complex analytic, hence real smooth; and restriction of scalars `L_ℂ(E, F) → L_ℝ(E, F)` is an
isometry. (Mathlib proves the analogue for maps on open subsets of `ℂ` with Cauchy's formula.) -/
theorem _root_.DifferentiableOn.contDiffOn_one_complex [CompleteSpace F] (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ 1 f U := by
  have hC : ContDiffOn ℝ ∞ f U := (smoothMBOn_iff_contDiffOn hU).1
    ((complexAnalyticOn_iff_holomorphicOn hU).1 (hf.complexAnalyticOn hU)).1
  have hR : ContinuousOn (fderiv ℝ f) U := hC.continuousOn_fderiv_of_isOpen hU (by simp)
  have hcont : ContinuousOn (fderiv ℂ f) U := by
    rw [(ContinuousLinearMap.restrictScalarsIsometry ℂ E F ℝ ℂ).isometry.isEmbedding.isInducing
      |>.continuousOn_iff]
    refine hR.congr fun x hx ↦ ?_
    exact ((hf.differentiableAt (hU.mem_nhds hx)).fderiv_restrictScalars ℝ).symm
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hf, by simp, contDiffOn_zero.2 hcont⟩

/-- **Locally uniform limits of holomorphic maps are holomorphic**, on open subsets of complex
normed spaces. -/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn_complex [CompleteSpace F] {ι : Type w}
    {φ : Filter ι}
    [φ.NeBot] {G : ι → E → F} (hG : TendstoLocallyUniformlyOn G f φ U)
    (hGd : ∀ᶠ n in φ, DifferentiableOn ℂ (G n) U) (hU : IsOpen U) : DifferentiableOn ℂ f U := by
  have hc : ContinuousOn f U := hG.continuousOn (hGd.mono fun _ h ↦ h.continuousOn).frequently
  refine ComplexAnalyticOn.differentiableOn ?_ hU
  refine (complexAnalyticOn_iff_gateauxAnalyticOn hU).2 ⟨hc, fun x _ y ↦ ?_⟩
  set g : ℂ → E := fun z ↦ x + z • y
  have hg : Differentiable ℂ g := by fun_prop
  have hV : IsOpen {z : ℂ | x + z • y ∈ U} := hU.preimage hg.continuous
  have hmaps : MapsTo g {z : ℂ | x + z • y ∈ U} U := fun _ hz ↦ hz
  have hline : ContinuousOn (fun z ↦ f (g z)) {z : ℂ | x + z • y ∈ U} :=
    hc.comp hg.continuous.continuousOn hmaps
  refine CAnalyticOn.of_weak hV hline fun ℓ ↦ ?_
  have hl : TendstoLocallyUniformlyOn (fun n z ↦ ℓ (G n (g z))) (fun z ↦ ℓ (f (g z))) φ
      {z : ℂ | x + z • y ∈ U} :=
    ℓ.uniformContinuous.comp_tendstoLocallyUniformlyOn
      (hG.comp g hmaps hg.continuous.continuousOn)
  exact hl.differentiableOn (hGd.mono fun _ h ↦
    ℓ.differentiable.comp_differentiableOn (h.comp hg.differentiableOn hmaps)) hV

end LocallyConvex.Analysis

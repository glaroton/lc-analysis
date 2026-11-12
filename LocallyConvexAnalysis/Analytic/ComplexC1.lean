/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.BanachHolomorphic
public import LocallyConvexAnalysis.Analytic.WeakHolomorphic
public import LocallyConvexAnalysis.Analytic.Real

/-!
# Complex `C^1` maps into Banach spaces are complex analytic

Reference: [GN26, Theorem 2.1.12], (f) ⇒ (d), p. 134.

We show that a map from a complex locally convex space to a complex Banach space which is real
`C^1` in the sense of Michal–Bastiani, with complex linear differentials, is complex analytic.
On the way we show that `C^1` maps on finite-dimensional normed spaces are Fréchet
differentiable.

## Main definitions

* `dMBCLM hV hg hx`: the differential `h ↦ dg(x, h)` of a `C^1` map `g` on an open subset of a
  finite-dimensional normed space, as a continuous linear map.

## Main results

* `ContDiffMBOn.hasFDerivAt_of_finiteDimensional`: on a finite-dimensional normed space, a map
  which is `C^1` in the sense of Michal–Bastiani is Fréchet differentiable, with derivative
  `h ↦ df(x, h)`.
* `complexAnalyticOn_of_contDiffMBOn_one`: a map from a complex locally convex space to a complex
  Banach space which is real `C^1` (Michal–Bastiani) with complex linear differentials is complex
  analytic ([GN26, Theorem 2.1.12], (f) ⇒ (d)).

## Implementation notes

For the first statement, Glöckner's lemma on difference quotients (`ContDiffMBOn.tendsto_quotient`)
and the compactness of the unit sphere give `t⁻¹ (g(x + t u) - g(x)) → dg(x, u)` uniformly in
`‖u‖ = 1`, which is Fréchet differentiability. For the second, the restrictions of `f` to complex
lines `z ↦ f(x + z y)` are then complex differentiable, hence complex analytic
(`CAnalyticOn.of_weak`), so `f` is Gâteaux analytic and continuous, hence complex analytic
(`complexAnalyticOn_iff_gateauxAnalyticOn`, [GN26, Theorem 2.1.12] (c) ⇔ (d)).
Glöckner–Neeb prove (f) ⇒ (d) for Mackey complete targets; here the target is a Banach space.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

section FiniteDimensional

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The differential `h ↦ dg(x, h)` of a `C^1` map, as a continuous linear map on a
finite-dimensional space. -/
def dMBCLM {g : X → F} {V : Set X} (hV : IsOpen V) (hg : ContDiffMBOn 1 g V) {x : X}
    (hx : x ∈ V) : X →L[ℝ] F :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h ↦ dMB g (x, h)
      map_add' := hg.dMB_add hV hx
      map_smul' := hg.dMB_smul hx }

@[simp]
theorem dMBCLM_apply {g : X → F} {V : Set X} (hV : IsOpen V) (hg : ContDiffMBOn 1 g V) {x : X}
    (hx : x ∈ V) (h : X) : dMBCLM hV hg hx h = dMB g (x, h) :=
  rfl

/-- **`C^1` maps on finite-dimensional spaces are Fréchet differentiable.** -/
theorem ContDiffMBOn.hasFDerivAt_of_finiteDimensional {g : X → F} {V : Set X} (hV : IsOpen V)
    (hg : ContDiffMBOn 1 g V) {x : X} (hx : x ∈ V) :
    HasFDerivAt g (dMBCLM hV hg hx) x := by
  set L := dMBCLM hV hg hx
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  -- uniform convergence of the quotients on the unit sphere
  have key : ∀ u₀ ∈ sphere (0 : X) 1, ∀ᶠ r : ℝ × X in 𝓝 (0, u₀),
      r.1 ≠ 0 → ‖r.1⁻¹ • (g (x + r.1 • r.2) - g x) - L r.2‖ ≤ ε := by
    intro u₀ _
    have hq := hg.tendsto_quotient hV hx (v := u₀)
    have hc : Tendsto (fun r : ℝ × X ↦ (x, r.2, r.1))
        (𝓝[{r : ℝ × X | r.1 ≠ 0}] (0, u₀)) (𝓝[{p : X × X × ℝ | p.2.2 ≠ 0}] (x, u₀, 0)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_const.prodMk (continuous_snd.prodMk
        continuous_fst)).tendsto _).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun r hr ↦ hr⟩
    have h1 := (hq.comp hc).eventually (ball_mem_nhds (dMB g (x, u₀)) (half_pos hε))
    have h2 : ∀ᶠ r : ℝ × X in 𝓝 (0, u₀), ‖L r.2 - L u₀‖ < ε / 2 := by
      have := ((L.continuous.comp continuous_snd).tendsto ((0 : ℝ), u₀)).eventually
        (ball_mem_nhds (L u₀) (half_pos hε))
      filter_upwards [this] with r hr
      simpa [dist_eq_norm] using hr
    rw [eventually_nhdsWithin_iff] at h1
    filter_upwards [h1, h2] with r hr1 hr2 hr0
    have h1' := hr1 hr0
    simp only [comp_apply, dist_eq_norm] at h1'
    have hL : L u₀ = dMB g (x, u₀) := rfl
    calc ‖r.1⁻¹ • (g (x + r.1 • r.2) - g x) - L r.2‖
        = ‖(r.1⁻¹ • (g (x + r.1 • r.2) - g x) - dMB g (x, u₀)) - (L r.2 - L u₀)‖ := by
          rw [hL]; congr 1; abel
      _ ≤ ‖r.1⁻¹ • (g (x + r.1 • r.2) - g x) - dMB g (x, u₀)‖ + ‖L r.2 - L u₀‖ :=
          norm_sub_le _ _
      _ ≤ ε := by linarith
  have hunif := (isCompact_sphere (0 : X) 1).eventually_forall_of_forall_eventually
    (P := fun (t : ℝ) (u : X) ↦ t ≠ 0 → ‖t⁻¹ • (g (x + t • u) - g x) - L u‖ ≤ ε) key
  -- conclusion for `h = ‖h‖ u`
  have hnorm : Tendsto (fun h : X ↦ ‖h‖) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_norm.tendsto (0 : X))
  filter_upwards [hnorm.eventually hunif] with h hh
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  have hn : ‖h‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hu : ‖h‖⁻¹ • h ∈ sphere (0 : X) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hb := hh (‖h‖⁻¹ • h) hu hn
  have hxh : x + ‖h‖ • ‖h‖⁻¹ • h = x + h := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  rw [hxh] at hb
  have hLh : L h = ‖h‖ • L (‖h‖⁻¹ • h) := by
    rw [map_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
  calc ‖g (x + h) - g x - L h‖
      = ‖‖h‖ • (‖h‖⁻¹ • (g (x + h) - g x) - L (‖h‖⁻¹ • h))‖ := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ hn, one_smul, ← hLh]
    _ = ‖h‖ * ‖‖h‖⁻¹ • (g (x + h) - g x) - L (‖h‖⁻¹ • h)‖ := by
        rw [norm_smul, norm_norm]
    _ ≤ ‖h‖ * ε := by gcongr
    _ = ε * ‖h‖ := mul_comm _ _

end FiniteDimensional

section Complex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **[GN26, Theorem 2.1.12], (f) ⇒ (d)**, for Banach targets: a real `C^1` map with
complex linear differentials is complex analytic. -/
theorem complexAnalyticOn_of_contDiffMBOn_one {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn 1 f U)
    (hI : ∀ x ∈ U, ∀ h, dMB f (x, Complex.I • h) = Complex.I • dMB f (x, h)) :
    ComplexAnalyticOn f U := by
  refine (complexAnalyticOn_iff_gateauxAnalyticOn hU).2 ⟨hf.continuousOn, fun x _ y ↦ ?_⟩
  set V : Set ℂ := {z | x + z • y ∈ U}
  have hcont : Continuous fun z : ℂ ↦ x + z • y := by fun_prop
  have hV : IsOpen V := hU.preimage hcont
  set ℓ : ℂ → F := fun z ↦ f (x + z • y)
  -- the line map is `C^1`
  have hd : ∀ z ∈ V, ∀ w : ℂ, HasDirDerivAt ℓ z w (dMB f (x + z • y, w • y)) := by
    intro z hz w
    refine (hf.hasDirDerivAt hz (w • y)).congr fun t ↦ ?_
    simp only [ℓ, add_smul, smul_assoc, add_assoc]
  have hd2 : ContinuousOn (dMB f) (U ×ˢ univ) := hf.2.2
  have hdc : ContinuousOn (fun p : ℂ × ℂ ↦ dMB f (x + p.1 • y, p.2 • y)) (V ×ˢ univ) :=
    hd2.comp (by fun_prop) fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have hℓ : ContDiffMBOn 1 ℓ V := by
    refine ⟨hf.continuousOn.comp hcont.continuousOn fun z hz ↦ hz, fun z hz w ↦ ?_, ?_⟩
    · rw [(hd z hz w).dMB_eq]; exact hd z hz w
    · exact hdc.congr fun p hp ↦ (hd p.1 hp.1 p.2).dMB_eq
  -- it is complex differentiable
  have hdiff : DifferentiableOn ℂ ℓ V := by
    intro z hz
    have hF := hℓ.hasFDerivAt_of_finiteDimensional hV hz
    have hlin : ∀ (c : ℂ) (w : ℂ), dMBCLM hV hℓ hz (c • w) = c • dMBCLM hV hℓ hz w := by
      refine map_smul_of_map_I_smul (T := dMBCLM hV hℓ hz) (fun v w ↦ map_add _ v w)
        (fun r w ↦ ?_) (fun w ↦ ?_)
      · exact map_smul _ r w
      · simp only [dMBCLM_apply, (hd z hz _).dMB_eq, smul_assoc, hI _ hz]
    let L : ℂ →L[ℂ] F := (1 : ℂ →L[ℂ] ℂ).smulRight (dMBCLM hV hℓ hz 1)
    refine (hasFDerivAt_of_restrictScalars ℝ hF (f' := L) ?_).differentiableAt
      |>.differentiableWithinAt
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply, L]
    rw [← hlin]
    change dMBCLM hV hℓ hz (w * 1) = dMBCLM hV hℓ hz w
    rw [mul_one]
  exact CAnalyticOn.of_weak hV hdiff.continuousOn fun φ ↦
    φ.differentiable.comp_differentiableOn hdiff

end Complex

end LocallyConvex.Analysis

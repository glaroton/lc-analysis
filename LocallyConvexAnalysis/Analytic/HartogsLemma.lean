/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.OneVariable
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # A Hartogs lemma for vector-valued holomorphic families

Hartogs' lemma on subharmonic functions, in the form needed for series of homogeneous
polynomials ([BS71b, §4]). Bochnak and Siciak use Siciak's polynomial lemma, whose proof rests
on potential theory (Siciak's extremal function, Fekete points, regularity for the Dirichlet
problem). Here the same uniformity is obtained from Jensen's formula in Mathlib.

## Main results

* `log_norm_le_circleAverage`: Jensen's inequality `log ‖h c‖ ≤ ⨍_{|z - c| = R} log ‖h‖`.
* `exists_clm_eq_seminorm`: Hahn–Banach, a continuous seminorm is attained by a dominated
  continuous functional.
* `posLog_le_circleAverage`: for a weakly holomorphic `g : ℂ → F` and a continuous seminorm `q`,
  `log⁺ q(g)` satisfies the sub-mean value inequality on circles.
* `ofReal_le_lintegral_ball`: the sub-mean value inequality on circles implies it on discs
  (integration in polar coordinates).
* `hartogs_lemma`: if `q (gₙ) ≤ e^{nB}` on a closed disc and `(q (gₙ z))ₙ` is bounded at each
  point, then `q (gₙ) ≤ e^{nε}` eventually, uniformly on the disc of half the radius.

No completeness of `F` is assumed.

## References

* [J. Bochnak, J. Siciak, *Analytic functions in topological vector-spaces*][BS71b]
-/

@[expose] public section

open Set Filter Function Metric MeasureTheory Real
open scoped Topology ENNReal

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Sub-mean value inequalities -/

section SubMean

/-- **Jensen's inequality** on a circle: for `h` holomorphic near the closed disc with
`h c ≠ 0`, `log ‖h c‖` is at most the circle average of `log ‖h‖`. This is Jensen's formula
(`AnalyticOnNhd.circleAverage_log_norm`) with its nonnegative zero-counting term dropped. -/
theorem log_norm_le_circleAverage {h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hh : AnalyticOnNhd ℂ h (closedBall c R)) (hc : h c ≠ 0) :
    Real.log ‖h c‖ ≤ circleAverage (fun z ↦ Real.log ‖h z‖) c R := by
  have hh' : AnalyticOnNhd ℂ h (closedBall c |R|) := by rwa [abs_of_pos hR]
  rw [hh'.circleAverage_log_norm hR.ne' hc]
  have : 0 ≤ ∑ᶠ u, (MeromorphicOn.divisor h (closedBall c |R|) u : ℝ) *
      Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_nonneg fun u ↦ ?_
    by_cases hu : u ∈ closedBall c |R|
    · refine mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh' u) ?_
      rw [abs_of_pos hR, mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at hu
      rcases eq_or_lt_of_le (norm_nonneg (c - u)) with h0 | h0
      · rw [← h0]; simp
      · exact Real.log_nonneg (by rw [← div_eq_mul_inv, le_div_iff₀ h0, one_mul]; exact hu)
    · simp [hu]
  linarith

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]

/-- **Hahn–Banach**: a continuous seminorm is attained by a continuous functional which it
dominates. -/
theorem exists_clm_eq_seminorm {q : Seminorm ℂ F} (hq : Continuous q) (v : F) :
    ∃ ℓ : F →L[ℂ] ℂ, ℓ v = ((q v : ℝ) : ℂ) ∧ ∀ w, ‖ℓ w‖ ≤ q w := by
  let f : F →ₗ.[ℂ] ℂ := LinearPMap.mkSpanSingleton' v ((q v : ℝ) : ℂ) (by
    intro c hc
    rcases smul_eq_zero.1 hc with rfl | rfl
    · simp
    · simp)
  obtain ⟨g, hg, hgq⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm f.domain f.toFun hq (by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have : f ⟨c • v, hx⟩ = c • ((q v : ℝ) : ℂ) := LinearPMap.mkSpanSingleton'_apply _ _ _ _ _
      change ‖f ⟨c • v, hx⟩‖ ≤ q (c • v)
      rw [this, map_smul_eq_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg q v)])
  refine ⟨g, ?_, hgq⟩
  rw [hg ⟨v, Submodule.mem_span_singleton_self v⟩]
  exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/-- **Sub-mean value inequality** for `log⁺ q (g ·)`, where `g` is weakly holomorphic: for a
continuous seminorm `q`, the positive part of the logarithm of `q ∘ g` is subharmonic. -/
theorem posLog_le_circleAverage {g : ℂ → F} (hg : Continuous g)
    (hℓ : ∀ ℓ : F →L[ℂ] ℂ, AnalyticOnNhd ℂ (ℓ ∘ g) (closedBall c R)) (hR : 0 < R)
    {q : Seminorm ℂ F} (hq : Continuous q) :
    posLog (q (g c)) ≤ circleAverage (fun z ↦ posLog (q (g z))) c R := by
  by_cases h1 : q (g c) ≤ 1
  · rw [(posLog_eq_zero_iff _).2 (by rwa [abs_of_nonneg (apply_nonneg q _)])]
    exact circleAverage_nonneg_of_nonneg fun _ _ ↦ posLog_nonneg
  rw [not_le] at h1
  obtain ⟨ℓ, hℓv, hℓq⟩ := exists_clm_eq_seminorm hq (g c)
  have hnorm : ‖(ℓ ∘ g) c‖ = q (g c) := by
    simp [hℓv, Complex.norm_real, abs_of_nonneg (apply_nonneg q _)]
  have hne : (ℓ ∘ g) c ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm]; linarith
  calc posLog (q (g c)) = Real.log ‖(ℓ ∘ g) c‖ := by
        rw [hnorm, posLog_eq_log (by rw [abs_of_nonneg (apply_nonneg q _)]; exact h1.le)]
    _ ≤ circleAverage (fun z ↦ Real.log ‖(ℓ ∘ g) z‖) c R :=
        log_norm_le_circleAverage hR (hℓ ℓ) hne
    _ ≤ circleAverage (fun z ↦ posLog (q (g z))) c R := by
        apply circleAverage_mono
        · have hm : MeromorphicOn (ℓ ∘ g) (sphere c |R|) := by
            rw [abs_of_pos hR]
            exact ((hℓ ℓ).mono sphere_subset_closedBall).meromorphicOn
          exact hm.circleIntegrable_log_norm
        · exact (continuous_posLog.comp (hq.comp hg)).continuousOn.circleIntegrable'
        · intro z _
          calc Real.log ‖(ℓ ∘ g) z‖ ≤ posLog ‖(ℓ ∘ g) z‖ := le_max_right _ _
            _ ≤ posLog (q (g z)) := posLog_le_posLog (by linarith [norm_nonneg ((ℓ ∘ g) z)])
                (hℓq _)

end SubMean

/-! ### From circles to discs -/

section Disc

/-- The integral of `u` over the circle of radius `r` about `z`, in the angular range
`(-π, π)` of polar coordinates, is `2π` times the circle average. -/
theorem integral_Ioo_circleMap (u : ℂ → ℝ) (z : ℂ) (r : ℝ) :
    ∫ θ in Ioo (-π) π, u (z + circleMap 0 r θ) = 2 * π * circleAverage u z r := by
  have h1 : (fun θ ↦ u (z + circleMap 0 r θ)) = fun θ ↦ u (circleMap z r θ) := by
    funext θ; simp [circleMap]
  rw [h1, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
    circleAverage_eq_integral_add (-π),
    intervalIntegral.integral_comp_add_right (fun θ ↦ u (circleMap z r θ)), smul_eq_mul,
    zero_add, show 2 * π + -π = π by ring, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **Disc averages from circle averages.** If a continuous `u ≥ 0` satisfies the sub-mean value
inequality on all circles of radius `< s` about `z`, then `π s² u(z) ≤ ∫_{B(z,s)} u`. The proof
integrates in polar coordinates. -/
theorem ofReal_le_lintegral_ball {u : ℂ → ℝ} (hu : Continuous u) (hu0 : ∀ w, 0 ≤ u w) {z : ℂ}
    {s : ℝ} (hs : 0 < s) (hsub : ∀ t ∈ Ioo 0 s, u z ≤ circleAverage u z t) :
    ENNReal.ofReal (π * s ^ 2 * u z) ≤ ∫⁻ w in ball z s, ENNReal.ofReal (u w) := by
  set f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) s).indicator fun w ↦ ENNReal.ofReal (u (z + w))
  have hf : Measurable f :=
    (ENNReal.measurable_ofReal.comp (hu.comp (continuous_const.add continuous_id)).measurable
      ).indicator measurableSet_ball
  have e1 : ∫⁻ w in ball z s, ENNReal.ofReal (u w) = ∫⁻ w, f w := by
    rw [← lintegral_indicator measurableSet_ball,
      ← lintegral_add_left_eq_self (μ := (volume : Measure ℂ)) _ z]
    congr 1
    ext w
    simp only [f, indicator, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hpm : Measurable fun p : ℝ × ℝ ↦ Complex.polarCoord.symm p := by
    have : Continuous fun p : ℝ × ℝ ↦ (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
      fun_prop
    simpa only [Complex.polarCoord_symm_apply] using this.measurable
  have hmeas : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p) :=
    measurable_fst.ennreal_ofReal.smul (hf.comp hpm)
  rw [e1, ← Complex.lintegral_comp_polarCoord_symm, polarCoord_target,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ hmeas.aemeasurable]
  -- restrict the radial integral to `(0, s)`
  have hmono : ∫⁻ r in Ioo 0 s, ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (r, θ).1 • f (Complex.polarCoord.symm (r, θ)) ≤
      ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (r, θ).1 • f (Complex.polarCoord.symm (r, θ)) :=
    lintegral_mono_set Ioo_subset_Ioi_self
  refine le_trans ?_ hmono
  -- the inner integral on `(0, s)`
  have hinner : ∀ r ∈ Ioo 0 s, ENNReal.ofReal (r * (2 * π * u z)) ≤ ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (r, θ).1 • f (Complex.polarCoord.symm (r, θ)) := by
    intro r hr
    have hpt : ∀ θ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := fun θ ↦ by
      rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
      push_cast
      ring
    have hin : ∀ θ, f (Complex.polarCoord.symm (r, θ)) =
        ENNReal.ofReal (u (z + circleMap 0 r θ)) := fun θ ↦ by
      rw [hpt]
      simp only [f, indicator, mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_pos hr.1, hr.2, ite_true]
    simp only [hin, smul_eq_mul]
    have hcm : Continuous fun θ ↦ u (z + circleMap 0 r θ) :=
      hu.comp (continuous_const.add (continuous_circleMap 0 r))
    rw [lintegral_const_mul (ENNReal.ofReal r)
      (f := fun θ ↦ ENNReal.ofReal (u (z + circleMap 0 r θ))) hcm.measurable.ennreal_ofReal,
      ← ofReal_integral_eq_lintegral_ofReal, ← ENNReal.ofReal_mul hr.1.le,
      integral_Ioo_circleMap u]
    · gcongr
      · exact hr.1.le
      · exact hsub r hr
    · exact hcm.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    · exact Eventually.of_forall fun θ ↦ hu0 _
  calc ENNReal.ofReal (π * s ^ 2 * u z)
      = ∫⁻ r in Ioo 0 s, ENNReal.ofReal (r * (2 * π * u z)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le]
          simp only [intervalIntegral.integral_mul_const, integral_id]
          ring
        · exact (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          exact mul_nonneg hr.1.le (by have := hu0 z; positivity)
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hinner

end Disc

/-! ### Hartogs' lemma -/

section Hartogs

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]

/-- **Hartogs' lemma** for families of weakly entire maps `gₙ : ℂ → F` (after Hartogs; compare
[BS71b, Polynomial Lemma and Proposition 4.1]). Assume that, for a continuous
seminorm `q`, `q (gₙ z) ≤ e^{n B}` on a closed disc and that `(q (gₙ z))ₙ` is bounded at every
point of the disc. Then for every `ε > 0`, eventually `q (gₙ z) ≤ e^{n ε}` uniformly on the
concentric disc of half the radius.

The functions `vₙ = n⁻¹ log⁺ q(gₙ)` are subharmonic (`posLog_le_circleAverage`), uniformly
bounded, and tend to `0` pointwise; the sub-mean value inequality on discs
(`ofReal_le_lintegral_ball`) and dominated convergence on a fixed disc give the uniformity. -/
theorem hartogs_lemma {g : ℕ → ℂ → F} (hc : ∀ n, Continuous (g n))
    (hℓ : ∀ n, ∀ ℓ : F →L[ℂ] ℂ, AnalyticOnNhd ℂ (ℓ ∘ g n) univ) {q : Seminorm ℂ F}
    (hq : Continuous q) {z₀ : ℂ} {R B : ℝ} (hR : 0 < R)
    (hB : ∀ n ≥ 1, ∀ z ∈ closedBall z₀ R, q (g n z) ≤ Real.exp (n * B))
    (hpt : ∀ z ∈ closedBall z₀ R, ∃ C, ∀ n, q (g n z) ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ z ∈ closedBall z₀ (R / 2), q (g n z) ≤ Real.exp (n * ε) := by
  set B' := max B 0
  set v : ℕ → ℂ → ℝ := fun n z ↦ (n : ℝ)⁻¹ * posLog (q (g n z))
  have hv0 : ∀ n z, 0 ≤ v n z := fun n z ↦ mul_nonneg (by positivity) posLog_nonneg
  have hvc : ∀ n, Continuous (v n) := fun n ↦
    continuous_const.mul (continuous_posLog.comp (hq.comp (hc n)))
  have hvB : ∀ n ≥ 1, ∀ z ∈ closedBall z₀ R, v n z ≤ B' := by
    intro n hn z hz
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : posLog (q (g n z)) ≤ n * B' := by
      calc posLog (q (g n z)) ≤ posLog (Real.exp (n * B)) :=
            posLog_le_posLog (by linarith [apply_nonneg q (g n z)]) (hB n hn z hz)
        _ = max 0 (n * B) := by rw [posLog_apply, Real.log_exp]
        _ ≤ n * B' := max_le (by positivity) (by gcongr; exact le_max_left _ _)
    simp only [v]
    rw [inv_mul_le_iff₀ hn']
    exact h1
  have hvlim : ∀ z ∈ closedBall z₀ R, Tendsto (fun n ↦ v n z) atTop (𝓝 0) := by
    intro z hz
    obtain ⟨C, hC⟩ := hpt z hz
    have hup : ∀ n, v n z ≤ (n : ℝ)⁻¹ * posLog C := fun n ↦ by
      simp only [v]
      exact mul_le_mul_of_nonneg_left
        (posLog_le_posLog (by linarith [apply_nonneg q (g n z)]) (hC n)) (by positivity)
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * posLog C) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.mul_const (posLog C)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (hv0 · z) hup
  -- dominated convergence on the disc `B(z₀, R)`
  set L : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ w in ball z₀ R, ENNReal.ofReal (v n w)
  have hL : Tendsto L atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (ball z₀ R))
      (F := fun n w ↦ ENNReal.ofReal (v (n + 1) w)) (f := fun _ ↦ 0)
      (fun _ ↦ ENNReal.ofReal B')
      (fun n ↦ (hvc (n + 1)).measurable.ennreal_ofReal)
      (fun n ↦ by
        filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
        exact ENNReal.ofReal_le_ofReal (hvB (n + 1) (by omega) w (ball_subset_closedBall hw)))
      (by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
      (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
        have := (hvlim w (ball_subset_closedBall hw)).comp (tendsto_add_atTop_nat 1)
        have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp this
        rw [ENNReal.ofReal_zero] at h2
        exact h2)
    simp only [lintegral_zero] at this
    exact (tendsto_add_atTop_iff_nat 1).1 this
  set s := R / 2
  have hs : 0 < s := by positivity
  have hpos : (0 : ℝ) < π * s ^ 2 * ε := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hL.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hpos)))
  refine ⟨max N 1, fun n hn z hz ↦ ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  -- sub-mean value inequality for `v n` about `z`
  have hsub : ∀ t ∈ Ioo 0 s, v n z ≤ circleAverage (v n) z t := by
    intro t ht
    have h := posLog_le_circleAverage (c := z) (R := t) (hc n)
      (fun ℓ ↦ (hℓ n ℓ).mono (subset_univ _)) ht.1 hq
    have e : circleAverage (v n) z t =
        (n : ℝ)⁻¹ * circleAverage (fun w ↦ posLog (q (g n w))) z t := by
      simp only [v]
      rw [← smul_eq_mul, ← circleAverage_fun_smul]
      rfl
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have hdisc := ofReal_le_lintegral_ball (hvc n) (hv0 n) hs hsub
  have hball : ball z s ⊆ ball z₀ R := by
    intro w hw
    rw [mem_ball] at hw ⊢
    rw [mem_closedBall] at hz
    calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
      _ < s + s := by linarith
      _ = R := by simp only [s]; ring
  have hlt : ENNReal.ofReal (π * s ^ 2 * v n z) < ENNReal.ofReal (π * s ^ 2 * ε) :=
    hdisc.trans_lt ((lintegral_mono_set hball).trans_lt (hN n (le_of_max_le_left hn)))
  rw [ENNReal.ofReal_lt_ofReal_iff hpos] at hlt
  have hvε : v n z < ε := by
    have : π * s ^ 2 * v n z < π * s ^ 2 * ε := hlt
    exact lt_of_mul_lt_mul_left this (by positivity)
  have hlog : posLog (q (g n z)) ≤ n * ε := by
    have : (n : ℝ)⁻¹ * posLog (q (g n z)) < ε := hvε
    rw [inv_mul_lt_iff₀ hn'] at this
    exact this.le
  calc q (g n z) ≤ max 1 (q (g n z)) := le_max_right _ _
    _ = Real.exp (posLog (q (g n z))) := by
        rw [posLog_eq_log_max_one (apply_nonneg q _), Real.exp_log (by positivity)]
    _ ≤ Real.exp (n * ε) := Real.exp_le_exp.2 hlog

end Hartogs

end LocallyConvex.Analysis

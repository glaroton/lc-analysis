/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.HartogsLemma
public import LocallyConvexAnalysis.Analytic.Complex
public import LocallyConvexAnalysis.Analytic.WeakHolomorphic
public import Mathlib.Topology.TietzeExtension

/-! # Hartogs' theorem on separately holomorphic maps

Hartogs' theorem (1906): a function of two complex variables which is holomorphic in each
variable separately is continuous, with no continuity assumption. We prove it for maps with
values in a complex locally convex space `F`, without any completeness of `F`, following Mujica,
*Complex Analysis in Banach Spaces*, North-Holland Math. Studies 120 (1986), §36 (Lemma 36.2,
Lemma 36.3 and Theorem 36.1 for `n = 2`), one continuous seminorm at a time.

## Main results

* `hartogs_lemma_real`: Hartogs' lemma for nonnegative functions with the sub-mean value
  property on a disc (a local form of `hartogs_lemma`).
* `posLog_le_circleAverage_of_dominated`: sub-mean value inequality for `log⁺ q (g)` when only
  the functionals dominated by `q` are known to give holomorphic functions.
* `seminorm_sub_le_of_dominated`: such maps are `q`-Lipschitz.
* `differentiableOn_iteratedDeriv_of_bound`: Osgood's lemma for the Taylor coefficients.
* `exists_ball_seminorm_bound`: [Muj86, Lemma 36.2] (Baire) for one seminorm.
* `hartogs_continuousAt`, `continuousOn_of_separately`: **Hartogs' theorem**, continuity of
  separately complex analytic maps on open subsets of `ℂ²`.
* `differentiableAt_line_of_separately`: Osgood's lemma along complex lines, scalar case.
* `complexAnalyticOn_of_separately`: **Hartogs' theorem**, joint complex analyticity, for a
  Mackey complete target.
* `not_complexAnalyticOn_sepG`, `not_mackeyComplete_sepSpan`: without completeness, joint
  analyticity fails. In the span `sepSpan ⊆ ℂ^{ℕ × ℕ}` of the matrices `α(n) σᵐ`, `ζⁿ β(m)`,
  `G(ζ, σ) = (ζⁿ σᵐ)` is separately analytic, but `e₂₀ + e₁₁ + e₀₂ ∉ sepSpan`
  (`diagCoeff₂_notMem`: the test `∑ q_s p_r x(s, r)` with `P = X ∏ (X - σᵢ)`,
  `Q = X ∏ (X - ζⱼ)` kills the span and not this vector).

## Implementation notes

* Continuity in `F` is continuity for each continuous seminorm `q`, so the whole argument is
  run for a fixed `q`: the point `b` given by Baire's theorem, and the Taylor coefficients
  `Aₖ(σ)` of `g(·, σ)` at `b`, depend on `q`. The coefficients are only known to be weakly
  holomorphic and `q`-Lipschitz, which is all that Jensen's inequality and Hartogs' lemma need.
* Joint complex analyticity needs the Taylor coefficients of `g` along oblique complex lines in
  `F`. They are limits of elements of `F` with geometric error bounds independent of the
  seminorm (`exists_coeff_of_weak`), so Mackey completeness of `F` suffices, and some
  completeness is necessary (`not_complexAnalyticOn_sepG`). Continuity needs no completeness.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [J. Mujica, *Complex Analysis in Banach Spaces*][Muj86]
-/

@[expose] public section

open Set Filter Function Metric MeasureTheory Real
open scoped Topology ENNReal

noncomputable section

namespace LocallyConvex.Analysis

/-! ### A local Hartogs lemma for real functions -/

/-- **Hartogs' lemma, abstract local form.** Let `vₙ ≥ 0` be continuous on a closed disc
`B̄(z₀, R)`, bounded there by `B` for `n ≥ 1`, tending to `0` pointwise, and satisfying the
sub-mean value inequality on the circles of radius `< R/2` about the points of `B̄(z₀, R/2)`.
Then `vₙ ≤ ε` on `B̄(z₀, R/2)` for large `n`. The functions are extended continuously to `ℂ`
(Tietze) and the proof of `hartogs_lemma` applies. -/
theorem hartogs_lemma_real {v : ℕ → ℂ → ℝ} {z₀ : ℂ} {R B : ℝ} (hR : 0 < R)
    (hc : ∀ n, ContinuousOn (v n) (closedBall z₀ R))
    (hv0 : ∀ n, ∀ z ∈ closedBall z₀ R, 0 ≤ v n z)
    (hB : ∀ n ≥ 1, ∀ z ∈ closedBall z₀ R, v n z ≤ B)
    (hlim : ∀ z ∈ closedBall z₀ R, Tendsto (fun n ↦ v n z) atTop (𝓝 0))
    (hsub : ∀ n, ∀ z ∈ closedBall z₀ (R / 2), ∀ t ∈ Ioo 0 (R / 2),
      v n z ≤ circleAverage (v n) z t) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ z ∈ closedBall z₀ (R / 2), v n z ≤ ε := by
  -- continuous nonnegative extensions
  have hext : ∀ n, ∃ w : ℂ → ℝ, Continuous w ∧ (∀ z, 0 ≤ w z) ∧
      EqOn w (v n) (closedBall z₀ R) := by
    intro n
    let f : C(closedBall z₀ R, ℝ) := ⟨(closedBall z₀ R).domRestrict (v n), (hc n).domRestrict⟩
    obtain ⟨w, hw0, hwf⟩ := ContinuousMap.exists_restrict_eq_forall_mem_of_closed f
      (t := Ici 0) (fun x ↦ hv0 n x.1 x.2) ⟨0, mem_Ici.2 le_rfl⟩ isClosed_closedBall
    refine ⟨w, w.continuous, hw0, fun z hz ↦ ?_⟩
    have := congrArg (fun F : C(closedBall z₀ R, ℝ) ↦ F ⟨z, hz⟩) hwf
    simpa [f] using this
  choose w hwc hw0 hwv using hext
  set B' := max B 0
  have hwB : ∀ n ≥ 1, ∀ z ∈ closedBall z₀ R, w n z ≤ B' := fun n hn z hz ↦ by
    rw [hwv n hz]; exact (hB n hn z hz).trans (le_max_left _ _)
  -- dominated convergence on the disc `B(z₀, R)`
  set L : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ x in ball z₀ R, ENNReal.ofReal (w n x)
  have hL : Tendsto L atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (ball z₀ R))
      (F := fun n x ↦ ENNReal.ofReal (w (n + 1) x)) (f := fun _ ↦ 0)
      (fun _ ↦ ENNReal.ofReal B')
      (fun n ↦ (hwc (n + 1)).measurable.ennreal_ofReal)
      (fun n ↦ by
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        exact ENNReal.ofReal_le_ofReal (hwB (n + 1) (by omega) x (ball_subset_closedBall hx)))
      (by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
      (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
        have h1 : Tendsto (fun n ↦ w (n + 1) x) atTop (𝓝 0) := by
          refine ((hlim x (ball_subset_closedBall hx)).comp (tendsto_add_atTop_nat 1)).congr
            fun n ↦ ?_
          simp [hwv (n + 1) (ball_subset_closedBall hx)]
        have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
        rw [ENNReal.ofReal_zero] at h2
        exact h2)
    simp only [lintegral_zero] at this
    exact (tendsto_add_atTop_iff_nat 1).1 this
  set s := R / 2
  have hs : 0 < s := by positivity
  have hpos : (0 : ℝ) < π * s ^ 2 * ε := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hL.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hpos)))
  refine ⟨N, fun n hn z hz ↦ ?_⟩
  have hzR : z ∈ closedBall z₀ R :=
    closedBall_subset_closedBall (half_le_self hR.le) hz
  have hball : ball z s ⊆ ball z₀ R := by
    intro x hx
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hz
    calc dist x z₀ ≤ dist x z + dist z z₀ := dist_triangle _ _ _
      _ < s + s := by linarith
      _ = R := by simp only [s]; ring
  have hsubw : ∀ t ∈ Ioo 0 s, w n z ≤ circleAverage (w n) z t := by
    intro t ht
    have heq : circleAverage (w n) z t = circleAverage (v n) z t := by
      refine circleAverage_congr_sphere fun x hx ↦ hwv n ?_
      rw [abs_of_pos ht.1] at hx
      exact ball_subset_closedBall (hball (sphere_subset_closedBall.trans
        (closedBall_subset_ball ht.2) hx))
    rw [heq, hwv n hzR]
    exact hsub n z hz t ht
  have hdisc := ofReal_le_lintegral_ball (hwc n) (hw0 n) hs hsubw
  have hlt : ENNReal.ofReal (π * s ^ 2 * w n z) < ENNReal.ofReal (π * s ^ 2 * ε) :=
    hdisc.trans_lt ((lintegral_mono_set hball).trans_lt (hN n hn))
  rw [ENNReal.ofReal_lt_ofReal_iff hpos] at hlt
  rw [← hwv n hzR]
  exact (lt_of_mul_lt_mul_left hlt (by positivity)).le

/-! ### Seminorms of weakly holomorphic maps -/

section Weak

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [PolynormableSpace ℂ F]

/-- **Sub-mean value inequality for `log⁺ q (g)`, local form**: it suffices that `ℓ ∘ g` be
holomorphic near the closed disc for the functionals `ℓ` dominated by `q`, and that `q ∘ g` be
continuous on the circle. No continuity of `g` itself is required. -/
theorem posLog_le_circleAverage_of_dominated {g : ℂ → F} {q : Seminorm ℂ F} (hq : Continuous q)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hℓ : ∀ ℓ : F →L[ℂ] ℂ, (∀ w, ‖ℓ w‖ ≤ q w) → AnalyticOnNhd ℂ (ℓ ∘ g) (closedBall c R))
    (hqg : ContinuousOn (fun z ↦ q (g z)) (sphere c R)) :
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
        log_norm_le_circleAverage hR (hℓ ℓ hℓq) hne
    _ ≤ circleAverage (fun z ↦ posLog (q (g z))) c R := by
        apply circleAverage_mono
        · have hm : MeromorphicOn (ℓ ∘ g) (sphere c |R|) := by
            rw [abs_of_pos hR]
            exact ((hℓ ℓ hℓq).mono sphere_subset_closedBall).meromorphicOn
          exact hm.circleIntegrable_log_norm
        · refine ContinuousOn.circleIntegrable' ?_
          rw [abs_of_pos hR]
          exact continuous_posLog.comp_continuousOn hqg
        · intro z _
          calc Real.log ‖(ℓ ∘ g) z‖ ≤ posLog ‖(ℓ ∘ g) z‖ := le_max_right _ _
            _ ≤ posLog (q (g z)) := posLog_le_posLog (by linarith [norm_nonneg ((ℓ ∘ g) z)])
                (hℓq _)

/-- **Weakly bounded holomorphic maps are seminorm-Lipschitz.** If, for every functional `ℓ`
dominated by `q`, `ℓ ∘ g` is holomorphic on `B(c, 3r)`, and `q ∘ g ≤ M` there, then
`q (g z - g w) ≤ (M / r) |z - w|` on `B̄(c, r)`. -/
theorem seminorm_sub_le_of_dominated {g : ℂ → F} {q : Seminorm ℂ F} (hq : Continuous q)
    {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hℓ : ∀ ℓ : F →L[ℂ] ℂ, (∀ w, ‖ℓ w‖ ≤ q w) → DifferentiableOn ℂ (ℓ ∘ g) (ball c (3 * r)))
    (hM : ∀ z ∈ ball c (3 * r), q (g z) ≤ M) {z w : ℂ} (hz : z ∈ closedBall c r)
    (hw : w ∈ closedBall c r) : q (g z - g w) ≤ M / r * ‖z - w‖ := by
  refine seminorm_le_of_forall_clm hq fun ℓ hℓq ↦ ?_
  have hd := hℓ ℓ hℓq
  have hsub : ∀ x ∈ closedBall c r, closedBall x r ⊆ ball c (3 * r) := by
    intro x hx y hy
    rw [mem_closedBall] at hx hy
    rw [mem_ball]
    calc dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
      _ < 3 * r := by linarith
  have hderiv : ∀ x ∈ closedBall c r, ‖deriv (ℓ ∘ g) x‖ ≤ M / r := by
    intro x hx
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
      ((hd.mono ((closure_ball_subset_closedBall).trans (hsub x hx))).diffContOnCl)
      fun y hy ↦ ?_
    exact (hℓq _).trans (hM y (hsub x hx (sphere_subset_closedBall hy)))
  have hdiff : ∀ x ∈ closedBall c r, DifferentiableAt ℂ (ℓ ∘ g) x := fun x hx ↦
    hd.differentiableAt (isOpen_ball.mem_nhds (hsub x hx (mem_closedBall_self hr.le)))
  have := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx ↦ (hdiff x hx)) hderiv hw hz
  simpa [map_sub, norm_sub_rev] using this

end Weak

/-! ### Holomorphy of the Taylor coefficients (scalar) -/

/-- **The Taylor coefficients in one variable are holomorphic in the other** (Osgood's lemma,
`OsgoodHyp.differentiableOn_coeff`, rescaled): if `h (ζ, σ)` is holomorphic in `ζ` on
`B̄(b, r)` for `σ ∈ B̄(c, S)`, holomorphic in `σ` on `B(c, S)` for `ζ ∈ B̄(b, r)`, and bounded on
`|ζ - b| = r`, `σ ∈ B̄(c, S)`, then `σ ↦ ∂ζᵏ h (b, σ)` is holomorphic on `B(c, S)`. -/
theorem differentiableOn_iteratedDeriv_of_bound {h : ℂ → ℂ → ℂ} {b c : ℂ} {r S m : ℝ}
    (hr : 0 < r) (hS : 0 < S)
    (h₁ : ∀ σ ∈ closedBall c S, DifferentiableOn ℂ (fun ζ ↦ h ζ σ) (closedBall b r))
    (h₂ : ∀ ζ ∈ closedBall b r, DifferentiableOn ℂ (h ζ) (ball c S))
    (hm : ∀ ζ ∈ sphere b r, ∀ σ ∈ closedBall c S, ‖h ζ σ‖ ≤ m) (k : ℕ) :
    DifferentiableOn ℂ (fun σ ↦ iteratedDeriv k (fun ζ ↦ h ζ σ) b) (ball c S) := by
  set lam : ℂ := ((S / r : ℝ) : ℂ)
  have hlam : ‖lam‖ = S / r := by simp [lam, abs_of_pos hS, abs_of_pos hr]
  have hlam0 : lam ≠ 0 := by rw [← norm_ne_zero_iff, hlam]; positivity
  set G : ℂ → ℂ → ℂ := fun u w ↦ h (b + w) (c + lam * u)
  have hmapσ : ∀ u : ℂ, ‖u‖ ≤ r → c + lam * u ∈ closedBall c S := fun u hu ↦ by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, hlam]
    calc S / r * ‖u‖ ≤ S / r * r := by gcongr
      _ = S := by field_simp
  have hmapσ' : ∀ u : ℂ, ‖u‖ < r → c + lam * u ∈ ball c S := fun u hu ↦ by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hlam]
    calc S / r * ‖u‖ < S / r * r := by gcongr
      _ = S := by field_simp
  have hO : OsgoodHyp G r m := by
    refine ⟨hr, fun u hu ↦ ?_, fun w hw ↦ ?_, fun u hu w hw ↦ ?_⟩
    · rw [mem_closedBall_zero_iff] at hu
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball 0 hr.ne']
      refine (h₁ _ (hmapσ u hu)).comp (differentiableOn_const _ |>.add differentiableOn_id)
        fun w hw ↦ ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      simpa using hw
    · rw [mem_ball_zero_iff] at hw
      have hζ : b + w ∈ closedBall b r := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hw.le
      exact (h₂ _ hζ).comp ((differentiableOn_const _).add
        ((differentiableOn_const _).mul differentiableOn_id)) fun u hu ↦
          hmapσ' u (by simpa using hu)
    · rw [mem_closedBall_zero_iff] at hu
      refine hm _ ?_ _ (hmapσ u hu)
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left]
      simpa using hw
  have hd := hO.differentiableOn_coeff k
  have e : ∀ σ, iteratedDeriv k (fun ζ ↦ h ζ σ) b =
      k.factorial * osgoodCoeff G k (lam⁻¹ * (σ - c)) := by
    intro σ
    have hσ : c + lam * (lam⁻¹ * (σ - c)) = σ := by field_simp; ring
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    rw [osgoodCoeff, mul_div_cancel₀ _ hfac]
    simp only [G, hσ]
    rw [iteratedDeriv_comp_const_add k (fun ζ ↦ h ζ σ) b]
    simp
  have hcomp : DifferentiableOn ℂ (fun σ ↦ osgoodCoeff G k (lam⁻¹ * (σ - c))) (ball c S) := by
    refine hd.comp ((differentiableOn_const _).mul (differentiableOn_id.sub
      (differentiableOn_const _))) fun σ hσ ↦ ?_
    rw [mem_ball_zero_iff, norm_mul, norm_inv, hlam]
    rw [mem_ball, dist_eq_norm] at hσ
    calc (S / r)⁻¹ * ‖σ - c‖ < (S / r)⁻¹ * S := by gcongr
      _ = r := by field_simp
  simp only [e]
  exact hcomp.const_mul _

/-! ### Seminorm continuity of sums and Baire's theorem -/

section Continuity

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [PolynormableSpace ℂ F]

omit [PolynormableSpace ℂ F] in
/-- **Continuity of a sum for one seminorm.** If `G = ∑ uₖ` near `x`, each `uₖ` is
`q`-continuous at `x`, and `q (uₖ) ≤ θᵏ` near `x` for large `k` (`θ < 1`), then `G` is
`q`-continuous at `x`. -/
theorem tendsto_seminorm_sub_of_hasSum {X : Type*} [TopologicalSpace X] {q : Seminorm ℂ F}
    (hq : Continuous q) {u : ℕ → X → F} {G : X → F} {x : X} {V : Set X} (hV : V ∈ 𝓝 x)
    (hxV : x ∈ V) (hsum : ∀ y ∈ V, HasSum (fun k ↦ u k y) (G y))
    (hcont : ∀ k, Tendsto (fun y ↦ q (u k y - u k x)) (𝓝 x) (𝓝 0))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {N : ℕ}
    (htail : ∀ k ≥ N, ∀ y ∈ V, q (u k y) ≤ θ ^ k) :
    Tendsto (fun y ↦ q (G y - G x)) (𝓝 x) (𝓝 0) := by
  have h1θ : 0 < 1 - θ := by linarith
  -- tail bound
  have hT : ∀ K ≥ N, ∀ y ∈ V, q (G y - ∑ k ∈ Finset.range K, u k y) ≤ θ ^ K / (1 - θ) := by
    intro K hK y hy
    set M : ℕ → ℝ := fun n ↦ if n < K then q (u n y) else θ ^ n
    have hMK : ∀ n, M (n + K) = θ ^ K * θ ^ n := fun n ↦ by
      simp [M, pow_add, mul_comm]
    have hMs : Summable M := by
      rw [← summable_nat_add_iff K]
      simp only [hMK]
      exact (summable_geometric_of_lt_one hθ0 hθ1).mul_left _
    have hle : ∀ n, q (u n y) ≤ M n := fun n ↦ by
      simp only [M]
      split_ifs with hn
      · exact le_rfl
      · exact htail n (hK.trans (not_lt.1 hn)) y hy
    calc q (G y - ∑ k ∈ Finset.range K, u k y) ≤ ∑' n, M (n + K) :=
          seminorm_sub_sum_le_of_hasSum hq (hsum y hy) hMs hle K
      _ = θ ^ K / (1 - θ) := by
          simp only [hMK]
          rw [tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1, div_eq_mul_inv]
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun y ↦
    ha.trans_le (apply_nonneg q _), fun ε hε ↦ ?_⟩
  have hgeom : Tendsto (fun K : ℕ ↦ 2 * (θ ^ K / (1 - θ))) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).div_const (1 - θ)).const_mul 2
  obtain ⟨K, hK1, hK2⟩ := ((hgeom.eventually (gt_mem_nhds (half_pos hε))).and
    (eventually_ge_atTop N)).exists
  have hfin : Tendsto (fun y ↦ ∑ k ∈ Finset.range K, q (u k y - u k x)) (𝓝 x) (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.range K) fun k _ ↦ hcont k
  filter_upwards [hV, hfin.eventually (gt_mem_nhds (half_pos hε))] with y hy hfy
  have hsplit : G y - G x = (G y - ∑ k ∈ Finset.range K, u k y) +
      ∑ k ∈ Finset.range K, (u k y - u k x) - (G x - ∑ k ∈ Finset.range K, u k x) := by
    rw [Finset.sum_sub_distrib]; abel
  calc q (G y - G x) ≤ q (G y - ∑ k ∈ Finset.range K, u k y) +
        q (∑ k ∈ Finset.range K, (u k y - u k x)) + q (G x - ∑ k ∈ Finset.range K, u k x) := by
        rw [hsplit]
        exact (map_sub_le_add q _ _).trans (by gcongr; exact map_add_le_add q _ _)
    _ ≤ θ ^ K / (1 - θ) + ∑ k ∈ Finset.range K, q (u k y - u k x) + θ ^ K / (1 - θ) := by
        gcongr
        · exact hT K hK2 y hy
        · exact Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
        · exact hT K hK2 x hxV
    _ < ε := by linarith

omit [IsTopologicalAddGroup F] [PolynormableSpace ℂ F] in
/-- **Baire's theorem for separately continuous maps** ([Muj86, Lemma 36.2], one seminorm): if
`g (ζ, σ)` is continuous in `ζ ∈ B(a, R)` and in `σ ∈ B̄(c, S)` separately, then `q ∘ g` is
bounded on `B(b, ρ) × B̄(c, S)` for some ball `B(b, ρ) ⊆ B(a, R)`. -/
theorem exists_ball_seminorm_bound {g : ℂ → ℂ → F} {a c : ℂ} {R S : ℝ} (hR : 0 < R)
    (h₁ : ∀ σ ∈ closedBall c S, ContinuousOn (fun ζ ↦ g ζ σ) (ball a R))
    (h₂ : ∀ ζ ∈ ball a R, ContinuousOn (g ζ) (closedBall c S)) {q : Seminorm ℂ F}
    (hq : Continuous q) :
    ∃ b ρ m, 0 < ρ ∧ ball b ρ ⊆ ball a R ∧
      ∀ ζ ∈ ball b ρ, ∀ σ ∈ closedBall c S, q (g ζ σ) ≤ m := by
  set X := ball a R
  have hX : IsOpen X := isOpen_ball
  have : BaireSpace X := hX.baireSpace
  have : Nonempty X := ⟨⟨a, mem_ball_self hR⟩⟩
  set A : ℕ → Set X := fun m ↦ {ζ | ∀ σ ∈ closedBall c S, q (g ζ σ) ≤ m}
  have hA : ∀ m, IsClosed (A m) := by
    intro m
    have : A m = ⋂ σ ∈ closedBall c S, (fun ζ : X ↦ q (g ζ σ)) ⁻¹' Iic (m : ℝ) := by
      ext; simp [A]
    rw [this]
    refine isClosed_biInter fun σ hσ ↦ isClosed_Iic.preimage ?_
    exact hq.comp ((h₁ σ hσ).comp_continuous continuous_subtype_val fun ζ ↦ ζ.2)
  have hcov : ⋃ m, A m = univ := by
    refine eq_univ_of_forall fun ζ ↦ mem_iUnion.2 ?_
    obtain ⟨C, hC⟩ := (isCompact_closedBall c S).exists_bound_of_continuousOn
      (hq.comp_continuousOn (h₂ ζ ζ.2))
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨m, fun σ hσ ↦ (le_abs_self _).trans ((hC σ hσ).trans hm)⟩
  obtain ⟨m, ζ₀, hζ₀⟩ := nonempty_interior_of_iUnion_of_closed hA hcov
  have hO : IsOpen ((↑) '' interior (A m) : Set ℂ) := hX.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ (mem_image_of_mem _ hζ₀)
  refine ⟨ζ₀, ρ, m, hρ, fun ζ hζ ↦ ?_, fun ζ hζ σ hσ ↦ ?_⟩
  · obtain ⟨ζ', -, rfl⟩ := hball hζ
    exact ζ'.2
  · obtain ⟨ζ', hζ', rfl⟩ := hball hζ
    exact interior_subset hζ' σ hσ

end Continuity

/-! ### Hartogs' theorem in two variables -/

section Main

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
/-- Complex analyticity in one variable passes to open subsets. -/
theorem CAnalyticOn.mono_of_isOpen {f : ℂ → F} {U V : Set ℂ} (hf : CAnalyticOn f U)
    (hV : IsOpen V) (hVU : V ⊆ U) : CAnalyticOn f V := by
  intro x hx
  obtain ⟨r, hr, -, a, ha⟩ := hf x (hVU hx)
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.1 hV x hx
  refine ⟨min r s, lt_min hr hs, (ball_subset_ball (min_le_right _ _)).trans hsV, a,
    fun z hz ↦ ha z (hz.trans_le (min_le_left _ _))⟩

/-- **Hartogs' theorem, local form** ([Muj86, Theorem 36.1] for `n = 2`, with Lemmas 36.2 and
36.3). Let `g (ζ, σ)` be holomorphic in each variable separately on the bidisc of radius `4R`
about `(a, c)`, with values in a complex locally convex space. Then `g` is continuous at
`(a, c)`.

No continuity of `g` is assumed. For each continuous seminorm `q`: Baire's theorem gives a
small disc `B(b, ρ)` with `q ∘ g` bounded on `B(b, ρ) × B̄(c, 3R)`; the Taylor coefficients
`Aₖ(σ)` of `g(·, σ)` at `b` are then weakly holomorphic in `σ` (Osgood's lemma) and
`q`-Lipschitz; Hartogs' lemma for `k⁻¹ log⁺ ((2R)ᵏ q (Aₖ))` gives
`q (Aₖ(σ)) ≤ (2/(3R))ᵏ` for large `k`, uniformly near `c`, so the Taylor series in `ζ` converges
`q`-uniformly near `(a, c)`. -/
theorem hartogs_continuousAt {g : ℂ → ℂ → F} {a c : ℂ} {R : ℝ} (hR : 0 < R)
    (h₁ : ∀ σ ∈ ball c (4 * R), CAnalyticOn (fun ζ ↦ g ζ σ) (ball a (4 * R)))
    (h₂ : ∀ ζ ∈ ball a (4 * R), CAnalyticOn (g ζ) (ball c (4 * R))) :
    ContinuousAt (uncurry g) (a, c) := by
  rw [ContinuousAt, tendsto_nhds_iff_seminorm]
  intro q hq ε hε
  suffices H : Tendsto (fun y : ℂ × ℂ ↦ q (uncurry g y - uncurry g (a, c))) (𝓝 (a, c)) (𝓝 0) from
    H.eventually (gt_mem_nhds hε)
  -- Step 1: Baire
  have hc3 : closedBall c (3 * R) ⊆ ball c (4 * R) := closedBall_subset_ball (by linarith)
  obtain ⟨b, ρ, m, hρ, hbρ, hm⟩ := exists_ball_seminorm_bound (g := g) (a := a) (c := c)
    (R := R) (S := 3 * R) hR
    (fun σ hσ ↦ (h₁ σ (hc3 hσ)).continuousOn.mono (ball_subset_ball (by linarith)))
    (fun ζ hζ ↦ (h₂ ζ (ball_subset_ball (by linarith) hζ)).continuousOn.mono hc3) hq
  have hb : dist b a < R := hbρ (mem_ball_self hρ)
  obtain ⟨r₀, hr₀_def⟩ : ∃ r, r = min ρ R / 2 := ⟨_, rfl⟩
  have hr₀ : 0 < r₀ := by rw [hr₀_def]; exact half_pos (lt_min hρ hR)
  have hr₀ρ : r₀ < ρ := by
    have := min_le_left ρ R; rw [hr₀_def]; linarith
  have hr₀R : r₀ < 5 * R / 2 := by
    have := min_le_right ρ R; rw [hr₀_def]; linarith
  -- the Taylor coefficients in `ζ` at `b`
  set A : ℕ → ℂ → F := fun k σ ↦ (k.factorial : ℂ)⁻¹ • cDeriv^[k] (fun ζ ↦ g ζ σ) b
  have hsub : closedBall b (5 * R / 2) ⊆ ball a (4 * R) := by
    intro ζ hζ
    rw [mem_closedBall] at hζ
    rw [mem_ball]
    calc dist ζ a ≤ dist ζ b + dist b a := dist_triangle _ _ _
      _ < 4 * R := by linarith
  have hP : ∀ σ ∈ ball c (4 * R),
      HasPowerSeriesOnDisc (fun ζ ↦ g ζ σ) (fun k ↦ A k σ) b (5 * R / 2) := fun σ hσ ↦
    (h₁ σ hσ).hasPowerSeriesOnDisc (by positivity) hsub
  have hAm : ∀ σ ∈ closedBall c (3 * R), ∀ k, q (A k σ) ≤ m / r₀ ^ k := by
    intro σ hσ k
    refine (hP σ (hc3 hσ)).seminorm_coeff_le hr₀ hr₀R hq (fun ζ hζ ↦ hm ζ ?_ σ hσ) k
    exact sphere_subset_closedBall.trans (closedBall_subset_ball hr₀ρ) hζ
  have hApt : ∀ σ ∈ closedBall c (3 * R), ∃ C, ∀ k, (2 * R) ^ k * q (A k σ) ≤ C := by
    intro σ hσ
    obtain ⟨M, hM⟩ := exists_seminorm_bound_sphere
      ((h₁ σ (hc3 hσ)).continuousOn.mono (sphere_subset_closedBall.trans
        ((closedBall_subset_closedBall (by linarith)).trans hsub))) hq (x := b) (R := 2 * R)
    refine ⟨M, fun k ↦ ?_⟩
    have h := (hP σ (hc3 hσ)).seminorm_coeff_le (by positivity) (by linarith) hq hM k
    have hpos : (0 : ℝ) < (2 * R) ^ k := by positivity
    rw [le_div_iff₀ hpos] at h
    linarith
  -- weak holomorphy of the coefficients
  have hAd : ∀ ℓ : F →L[ℂ] ℂ, (∀ w, ‖ℓ w‖ ≤ q w) → ∀ k,
      DifferentiableOn ℂ (fun σ ↦ ℓ (A k σ)) (ball c (3 * R)) := by
    intro ℓ hℓq k
    have hd := differentiableOn_iteratedDeriv_of_bound (h := fun ζ σ ↦ ℓ (g ζ σ)) (b := b)
      (c := c) (r := r₀) (S := 3 * R) (m := m) hr₀ (by positivity)
      (fun σ hσ ↦ ((h₁ σ (hc3 hσ)).differentiableOn_clm ℓ).mono
        ((closedBall_subset_closedBall hr₀R.le).trans hsub))
      (fun ζ hζ ↦ ((h₂ ζ (hsub (closedBall_subset_closedBall hr₀R.le hζ))).differentiableOn_clm
        ℓ).mono (ball_subset_ball (by linarith)))
      (fun ζ hζ σ hσ ↦ (hℓq _).trans (hm ζ
        (sphere_subset_closedBall.trans (closedBall_subset_ball hr₀ρ) hζ) σ hσ)) k
    refine (hd.div_const (k.factorial : ℂ)).congr fun σ hσ ↦ ?_
    have hσ4 : σ ∈ ball c (4 * R) := ball_subset_ball (by linarith) hσ
    exact (hP σ hσ4).clm_apply (by positivity) ℓ k
  -- Lipschitz bounds
  have hAlip : ∀ k, ∀ σ ∈ closedBall c R, ∀ σ' ∈ closedBall c R,
      q (A k σ - A k σ') ≤ m / r₀ ^ k / R * ‖σ - σ'‖ := fun k σ hσ σ' hσ' ↦
    seminorm_sub_le_of_dominated hq hR (fun ℓ hℓ ↦ hAd ℓ hℓ k)
      (fun z hz ↦ hAm z (ball_subset_closedBall hz) k) hσ hσ'
  have hqA : ∀ k, ContinuousOn (fun σ ↦ q (A k σ)) (closedBall c R) := fun k ↦
    (LipschitzOnWith.of_dist_le' (K := m / r₀ ^ k / R) fun σ hσ σ' hσ' ↦ by
      rw [Real.dist_eq, dist_eq_norm]
      exact (abs_sub_map_le_sub q _ _).trans (hAlip k σ hσ σ' hσ')).continuousOn
  -- Hartogs' lemma for `vₖ = k⁻¹ log⁺ ((2R)ᵏ q (Aₖ))`
  set v : ℕ → ℂ → ℝ := fun k σ ↦ (k : ℝ)⁻¹ * posLog ((2 * R) ^ k * q (A k σ))
  have hcR : closedBall c R ⊆ closedBall c (3 * R) := closedBall_subset_closedBall (by linarith)
  set Bd : ℝ := posLog m + posLog (2 * R / r₀)
  have hv := hartogs_lemma_real (v := v) (z₀ := c) (R := R) (B := Bd) hR
    (fun k ↦ continuousOn_const.mul (continuous_posLog.comp_continuousOn
      (continuousOn_const.mul (hqA k))))
    (fun k z _ ↦ mul_nonneg (by positivity) posLog_nonneg)
    (fun k hk σ hσ ↦ by
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hle : (2 * R) ^ k * q (A k σ) ≤ m * (2 * R / r₀) ^ k := by
        calc (2 * R) ^ k * q (A k σ) ≤ (2 * R) ^ k * (m / r₀ ^ k) := by
              gcongr; exact hAm σ (hcR hσ) k
          _ = m * (2 * R / r₀) ^ k := by rw [div_pow]; ring
      have h0 : 0 ≤ (2 * R) ^ k * q (A k σ) := by positivity
      have hlog : posLog ((2 * R) ^ k * q (A k σ)) ≤ posLog m + k * posLog (2 * R / r₀) := by
        calc _ ≤ posLog (m * (2 * R / r₀) ^ k) := posLog_le_posLog (by linarith) hle
          _ ≤ posLog m + posLog ((2 * R / r₀) ^ k) := posLog_mul
          _ = posLog m + k * posLog (2 * R / r₀) := by rw [posLog_pow]
      have h1 : (k : ℝ)⁻¹ * posLog m ≤ posLog m :=
        mul_le_of_le_one_left posLog_nonneg (inv_le_one_of_one_le₀ hk')
      calc v k σ ≤ (k : ℝ)⁻¹ * (posLog m + k * posLog (2 * R / r₀)) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = (k : ℝ)⁻¹ * posLog m + posLog (2 * R / r₀) := by field_simp
        _ ≤ Bd := by simp only [Bd]; linarith)
    (fun σ hσ ↦ by
      obtain ⟨C, hC⟩ := hApt σ (hcR hσ)
      have hup : ∀ k, v k σ ≤ (k : ℝ)⁻¹ * posLog C := fun k ↦ by
        refine mul_le_mul_of_nonneg_left (posLog_le_posLog ?_ (hC k)) (by positivity)
        have : 0 ≤ (2 * R) ^ k * q (A k σ) := by positivity
        linarith
      have hlow : ∀ k, 0 ≤ v k σ := fun k ↦ mul_nonneg (by positivity) posLog_nonneg
      have h0 : Tendsto (fun k : ℕ ↦ (k : ℝ)⁻¹ * posLog C) atTop (𝓝 0) := by
        simpa using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.mul_const
          (posLog C)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hlow hup)
    (fun k z hz t ht ↦ by
      set g' : ℂ → F := fun σ ↦ ((2 * R : ℂ) ^ k) • A k σ
      have hqg' : ∀ σ, q (g' σ) = (2 * R) ^ k * q (A k σ) := fun σ ↦ by
        simp only [g', map_smul_eq_mul, norm_pow, norm_mul, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
      have hball : closedBall z t ⊆ ball c R := by
        intro x hx
        rw [mem_closedBall] at hx
        rw [mem_closedBall] at hz
        rw [mem_ball]
        calc dist x c ≤ dist x z + dist z c := dist_triangle _ _ _
          _ < R := by linarith [ht.2]
      have hJ := posLog_le_circleAverage_of_dominated (g := g') hq ht.1
        (fun ℓ hℓ ↦ by
          have hd : DifferentiableOn ℂ (ℓ ∘ g') (ball c (3 * R)) := by
            have := (hAd ℓ hℓ k).const_mul ((2 * R : ℂ) ^ k)
            refine this.congr fun σ _ ↦ ?_
            simp [g', map_smul]
          exact (hd.analyticOnNhd isOpen_ball).mono
            (hball.trans (ball_subset_ball (by linarith))))
        (by
          simp only [hqg']
          exact (continuousOn_const.mul (hqA k)).mono
            (sphere_subset_closedBall.trans (hball.trans ball_subset_closedBall)))
      simp only [hqg'] at hJ
      have e : circleAverage (v k) z t =
          (k : ℝ)⁻¹ * circleAverage (fun σ ↦ posLog ((2 * R) ^ k * q (A k σ))) z t := by
        simp only [v, Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_const_mul]
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hJ (by positivity))
    (ε := Real.log (4 / 3)) (Real.log_pos (by norm_num))
  obtain ⟨N, hN⟩ := hv
  have hAgeom : ∀ k ≥ max N 1, ∀ σ ∈ closedBall c (R / 2),
      q (A k σ) ≤ (2 / (3 * R)) ^ k := by
    intro k hk σ hσ
    have hk1 : (0 : ℝ) < k := by exact_mod_cast (le_of_max_le_right hk)
    have h := hN k (le_of_max_le_left hk) σ hσ
    have hlog : posLog ((2 * R) ^ k * q (A k σ)) ≤ k * Real.log (4 / 3) := by
      have : (k : ℝ)⁻¹ * posLog ((2 * R) ^ k * q (A k σ)) ≤ Real.log (4 / 3) := h
      rwa [inv_mul_le_iff₀ hk1] at this
    have hx0 : 0 ≤ (2 * R) ^ k * q (A k σ) := by positivity
    have hle : (2 * R) ^ k * q (A k σ) ≤ (4 / 3 : ℝ) ^ k := by
      calc (2 * R) ^ k * q (A k σ) ≤ max 1 ((2 * R) ^ k * q (A k σ)) := le_max_right _ _
        _ = Real.exp (posLog ((2 * R) ^ k * q (A k σ))) := by
            rw [posLog_eq_log_max_one hx0, Real.exp_log (by positivity)]
        _ ≤ Real.exp (k * Real.log (4 / 3)) := Real.exp_le_exp.2 hlog
        _ = (4 / 3 : ℝ) ^ k := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hpos : (0 : ℝ) < (2 * R) ^ k := by positivity
    calc q (A k σ) = (2 * R) ^ k * q (A k σ) / (2 * R) ^ k := by field_simp
      _ ≤ (4 / 3 : ℝ) ^ k / (2 * R) ^ k := by gcongr
      _ = (2 / (3 * R)) ^ k := by rw [← div_pow]; congr 1; field_simp; ring
  -- the Taylor series in `ζ` converges `q`-uniformly near `(a, c)`
  set V : Set (ℂ × ℂ) := ball a (R / 4) ×ˢ ball c (R / 2)
  have hV : V ∈ 𝓝 (a, c) := prod_mem_nhds (ball_mem_nhds a (by positivity))
    (ball_mem_nhds c (by positivity))
  have hxV : (a, c) ∈ V := ⟨mem_ball_self (by positivity), mem_ball_self (by positivity)⟩
  have hζb : ∀ y ∈ V, ‖y.1 - b‖ < 5 * R / 4 := by
    intro y hy
    have h1 : dist y.1 a < R / 4 := hy.1
    rw [← dist_eq_norm]
    calc dist y.1 b ≤ dist y.1 a + dist a b := dist_triangle _ _ _
      _ < 5 * R / 4 := by rw [dist_comm a b]; linarith
  have hσ4 : ∀ y ∈ V, y.2 ∈ ball c (4 * R) := fun y hy ↦
    ball_subset_ball (by linarith) hy.2
  refine tendsto_seminorm_sub_of_hasSum (u := fun k y ↦ (y.1 - b) ^ k • A k y.2) hq hV hxV
    (fun y hy ↦ ?_) (fun k ↦ ?_) (θ := 5 / 6) (by norm_num) (by norm_num) (N := max N 1)
    (fun k hk y hy ↦ ?_)
  · have h := hP y.2 (hσ4 y hy) (y.1 - b) (by linarith [hζb y hy])
    simpa [add_sub_cancel, uncurry] using h
  · -- each term is `q`-continuous
    set L := m / r₀ ^ k / R
    have hbound : ∀ᶠ y in 𝓝 (a, c), q ((y.1 - b) ^ k • A k y.2 - (a - b) ^ k • A k c) ≤
        ‖(y.1 - b) ^ k - (a - b) ^ k‖ * (m / r₀ ^ k) + ‖(a - b) ^ k‖ * (L * ‖y.2 - c‖) := by
      filter_upwards [prod_mem_nhds univ_mem (ball_mem_nhds c hR)] with y hy
      have hyc : y.2 ∈ closedBall c R := ball_subset_closedBall hy.2
      have e : (y.1 - b) ^ k • A k y.2 - (a - b) ^ k • A k c =
          ((y.1 - b) ^ k - (a - b) ^ k) • A k y.2 + (a - b) ^ k • (A k y.2 - A k c) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      refine (map_add_le_add q _ _).trans (add_le_add ?_ ?_)
      · rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hAm _ (hcR hyc) k) (norm_nonneg _)
      · rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (hAlip k _ hyc c (mem_closedBall_self hR.le)) (norm_nonneg _)
    have hlim : Tendsto (fun y : ℂ × ℂ ↦ ‖(y.1 - b) ^ k - (a - b) ^ k‖ * (m / r₀ ^ k) +
        ‖(a - b) ^ k‖ * (L * ‖y.2 - c‖)) (𝓝 (a, c)) (𝓝 0) := by
      have h1 : Tendsto (fun y : ℂ × ℂ ↦ ‖(y.1 - b) ^ k - (a - b) ^ k‖) (𝓝 (a, c)) (𝓝 0) := by
        have : Continuous fun y : ℂ × ℂ ↦ ‖(y.1 - b) ^ k - (a - b) ^ k‖ := by fun_prop
        simpa using this.tendsto (a, c)
      have h2 : Tendsto (fun y : ℂ × ℂ ↦ ‖y.2 - c‖) (𝓝 (a, c)) (𝓝 0) := by
        have : Continuous fun y : ℂ × ℂ ↦ ‖y.2 - c‖ := by fun_prop
        simpa using this.tendsto (a, c)
      simpa using (h1.mul_const _).add ((h2.const_mul L).const_mul _)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun y ↦ apply_nonneg q _) hbound
  · -- geometric tail
    have hyσ : y.2 ∈ closedBall c (R / 2) := ball_subset_closedBall hy.2
    rw [map_smul_eq_mul, norm_pow]
    calc ‖y.1 - b‖ ^ k * q (A k y.2) ≤ (5 * R / 4) ^ k * (2 / (3 * R)) ^ k := by
          gcongr
          · exact (hζb y hy).le
          · exact hAgeom k hk _ hyσ
      _ = (5 / 6 : ℝ) ^ k := by rw [← mul_pow]; congr 1; field_simp; ring

/-- **Hartogs' theorem on separate holomorphy, continuity** (Hartogs 1906; [Muj86, Theorem 36.1]
for `n = 2`). A map `g : U → F` on an open set `U ⊆ ℂ²`, with values in a complex locally
convex space, which is complex analytic in each variable separately, is continuous. No
completeness of `F` and no continuity of `g` are assumed. -/
theorem continuousOn_of_separately {g : ℂ → ℂ → F} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h₁ : ∀ σ, CAnalyticOn (fun ζ ↦ g ζ σ) {ζ | (ζ, σ) ∈ U})
    (h₂ : ∀ ζ, CAnalyticOn (g ζ) {σ | (ζ, σ) ∈ U}) : ContinuousOn (uncurry g) U := by
  rintro ⟨a, c⟩ hac
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU _ hac
  set R := r / 4
  have hR : 0 < R := by positivity
  have hbox : ∀ ζ ∈ ball a (4 * R), ∀ σ ∈ ball c (4 * R), (ζ, σ) ∈ U := by
    intro ζ hζ σ hσ
    refine hrU ?_
    rw [← ball_prod_same]
    have h4 : 4 * R = r := by simp only [R]; ring
    rw [h4] at hζ hσ
    exact ⟨hζ, hσ⟩
  refine (hartogs_continuousAt hR (fun σ hσ ↦ ?_) (fun ζ hζ ↦ ?_)).continuousWithinAt
  · exact (h₁ σ).mono_of_isOpen isOpen_ball fun ζ hζ ↦ hbox ζ hζ σ hσ
  · exact (h₂ ζ).mono_of_isOpen isOpen_ball fun σ hσ ↦ hbox ζ hζ σ hσ

end Main

/-! ### Scalar functions: holomorphy along complex lines (Osgood) -/

/-- A continuous, separately holomorphic scalar function on a closed bidisc about `p` is
holomorphic along the complex lines through `p` with slope `|λ| ≤ 1` in the first variable. -/
theorem differentiableAt_line_of_le {h : ℂ → ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hc : ContinuousOn (uncurry h) U)
    (h₁ : ∀ σ, DifferentiableOn ℂ (fun ζ ↦ h ζ σ) {ζ | (ζ, σ) ∈ U})
    (h₂ : ∀ ζ, DifferentiableOn ℂ (h ζ) {σ | (ζ, σ) ∈ U}) {p : ℂ × ℂ} (hp : p ∈ U)
    {y : ℂ × ℂ} (hy : ‖y.2‖ ≤ ‖y.1‖) :
    DifferentiableAt ℂ (fun t : ℂ ↦ h (p.1 + t * y.1) (p.2 + t * y.2)) 0 := by
  by_cases hy1 : y.1 = 0
  · have hy2 : y.2 = 0 := by rw [hy1, norm_zero] at hy; exact norm_le_zero_iff.1 hy
    simp only [hy1, hy2, mul_zero, add_zero]
    exact differentiableAt_const _
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
  set r := ε / 2
  have hr : 0 < r := half_pos hε
  have hbox : ∀ ζ ∈ closedBall p.1 r, ∀ σ ∈ closedBall p.2 r, (ζ, σ) ∈ U := by
    intro ζ hζ σ hσ
    refine hεU ?_
    rw [← ball_prod_same]
    exact ⟨closedBall_subset_ball (half_lt_self hε) hζ,
      closedBall_subset_ball (half_lt_self hε) hσ⟩
  have hy1n : 0 < ‖y.1‖ := norm_pos_iff.2 hy1
  set R := r / ‖y.1‖
  have hR : 0 < R := div_pos hr hy1n
  have hmap : ∀ w : ℂ, ‖w‖ ≤ R → ∀ z : ℂ, dist (z + y.1 * w) z ≤ r := by
    intro w hw z
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul]
    calc ‖y.1‖ * ‖w‖ ≤ ‖y.1‖ * R := by gcongr
      _ = r := by simp only [R]; field_simp
  set G : ℂ → ℂ → ℂ := fun ζ σ ↦ h (p.1 + y.1 * ζ) (p.2 + y.1 * σ)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p.1 r |>.prod (isCompact_closedBall p.2 r)
    ).exists_bound_of_continuousOn (hc.mono fun z hz ↦ hbox z.1 hz.1 z.2 hz.2)
  have hO : OsgoodHyp G R M := by
    refine ⟨hR, fun ζ hζ ↦ ?_, fun σ hσ ↦ ?_, fun ζ hζ σ hσ ↦ ?_⟩
    · refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball 0 hR.ne']
      refine (h₂ _).comp ((differentiableOn_const _).add
        ((differentiableOn_const _).mul differentiableOn_id)) fun σ hσ ↦ ?_
      exact hbox _ (hmap ζ (by simpa using hζ) p.1) _ (hmap σ (by simpa using hσ) p.2)
    · refine (h₁ _).comp ((differentiableOn_const _).add
        ((differentiableOn_const _).mul differentiableOn_id)) fun ζ hζ ↦ ?_
      exact hbox _ (hmap ζ (by simpa using (mem_ball_zero_iff.1 hζ).le) p.1) _
        (hmap σ (by simpa using (mem_ball_zero_iff.1 hσ).le) p.2)
    · exact hM (_, _) ⟨hmap ζ (by simpa using hζ) p.1,
        hmap σ (by simpa using (mem_sphere_zero_iff_norm.1 hσ).le) p.2⟩
  set lam := y.2 / y.1
  have hlam : ‖lam‖ ≤ 1 := by
    rw [norm_div, div_le_one hy1n]; exact hy
  have hser : ∀ t : ℂ, ‖t‖ < R / 2 → HasSum (fun m ↦ t ^ m •
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal m, osgoodCoeff₂ G q.1 q.2 * lam ^ q.1)
      (h (p.1 + (0 + t) * y.1) (p.2 + (0 + t) * y.2)) := by
    intro t ht
    have := hO.hasSum_line hlam ht
    have e : G t (lam * t) = h (p.1 + (0 + t) * y.1) (p.2 + (0 + t) * y.2) := by
      simp only [G, lam, zero_add]
      congr 2 <;> field_simp
    rw [← e]
    simpa only [smul_eq_mul] using this
  have hd := differentiableOn_of_hasSum (g := fun t : ℂ ↦ h (p.1 + t * y.1) (p.2 + t * y.2))
    (x := 0) (half_pos hR) hser
  exact hd.differentiableAt (ball_mem_nhds 0 (half_pos hR))

/-- **Scalar Osgood lemma along lines**: a continuous, separately holomorphic function on an
open set `U ⊆ ℂ²` is holomorphic along every complex line. -/
theorem differentiableAt_line_of_separately {h : ℂ → ℂ → ℂ} {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (hc : ContinuousOn (uncurry h) U)
    (h₁ : ∀ σ, DifferentiableOn ℂ (fun ζ ↦ h ζ σ) {ζ | (ζ, σ) ∈ U})
    (h₂ : ∀ ζ, DifferentiableOn ℂ (h ζ) {σ | (ζ, σ) ∈ U}) {p : ℂ × ℂ} (hp : p ∈ U)
    (y : ℂ × ℂ) : DifferentiableAt ℂ (fun t : ℂ ↦ h (p.1 + t * y.1) (p.2 + t * y.2)) 0 := by
  rcases le_total ‖y.2‖ ‖y.1‖ with hy | hy
  · exact differentiableAt_line_of_le hU hc h₁ h₂ hp hy
  · have := differentiableAt_line_of_le (h := fun ζ σ ↦ h σ ζ) (U := Prod.swap ⁻¹' U)
      (hU.preimage continuous_swap) (hc.comp continuous_swap.continuousOn fun z hz ↦ hz)
      (fun σ ↦ h₂ σ) (fun ζ ↦ h₁ ζ) (p := p.swap) (by simpa using hp) (y := y.swap)
      (by simpa using hy)
    simpa using this

/-! ### Joint complex analyticity -/

section Joint

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] polynormableSpace_complex

/-- **Hartogs' theorem** ([Muj86, Theorem 36.1] for `n = 2`), for a **Mackey complete** complex
locally convex space `F`: a map on an open subset of `ℂ²` which is complex analytic in each
variable separately is complex analytic. It is continuous (`continuousOn_of_separately`, no
completeness); along each complex line it is weakly holomorphic (Osgood's lemma for the
functions `ℓ ∘ g`, `differentiableAt_line_of_separately`), hence complex analytic there by
`CAnalyticOn.of_weak`, which is where Mackey completeness enters; [GN26, Theorem 2.1.12]
(`complexAnalyticOn_iff_gateauxAnalyticOn`) concludes. -/
theorem complexAnalyticOn_of_separately [MackeyComplete F] {g : ℂ → ℂ → F}
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (h₁ : ∀ σ, CAnalyticOn (fun ζ ↦ g ζ σ) {ζ | (ζ, σ) ∈ U})
    (h₂ : ∀ ζ, CAnalyticOn (g ζ) {σ | (ζ, σ) ∈ U}) : ComplexAnalyticOn (uncurry g) U := by
  have hc := continuousOn_of_separately hU h₁ h₂
  refine (complexAnalyticOn_iff_gateauxAnalyticOn hU).2 ⟨hc, fun x _ y ↦ ?_⟩
  have hline : Continuous fun z : ℂ ↦ x + z • y := continuous_const.add
    (continuous_id.smul continuous_const)
  have hV : IsOpen {z : ℂ | x + z • y ∈ U} := hU.preimage hline
  refine CAnalyticOn.of_weak hV (hc.comp hline.continuousOn fun z hz ↦ hz) fun ℓ z₀ hz₀ ↦ ?_
  refine DifferentiableAt.differentiableWithinAt ?_
  set p : ℂ × ℂ := x + z₀ • y
  have hd := differentiableAt_line_of_separately (h := fun ζ σ ↦ ℓ (g ζ σ)) hU
    (ℓ.continuous.comp_continuousOn hc) (fun σ ↦ (h₁ σ).differentiableOn_clm ℓ)
    (fun ζ ↦ (h₂ ζ).differentiableOn_clm ℓ) (p := p) hz₀ y
  have he : (ℓ ∘ fun z : ℂ ↦ uncurry g (x + z • y)) =
      (fun t : ℂ ↦ ℓ (g (p.1 + t * y.1) (p.2 + t * y.2))) ∘ fun z ↦ z - z₀ := by
    funext z
    simp only [Function.comp, uncurry, p, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    congr 2 <;> ring
  rw [he]
  refine DifferentiableAt.comp z₀ ?_ (differentiableAt_id.sub_const z₀)
  simpa using hd

end Joint

/-! ### A counterexample without completeness -/

section Counterexample

/-- The matrices `α(n) σᵐ` and `ζⁿ β(m)`, rank one with a geometric factor. -/
def geomRankOne : Set (ℕ × ℕ → ℂ) :=
  {x | ∃ σ ζ : ℂ, (∃ α : ℕ → ℂ, x = fun p ↦ α p.1 * σ ^ p.2) ∨
    (∃ β : ℕ → ℂ, x = fun p ↦ ζ ^ p.1 * β p.2)}

/-- Their linear span in `ℂ^{ℕ × ℕ}` (product topology), a non-closed subspace. -/
def sepSpan : Submodule ℂ (ℕ × ℕ → ℂ) := Submodule.span ℂ geomRankOne

instance : LocallyConvexSpace ℝ sepSpan :=
  LocallyConvexSpace.induced (sepSpan.subtype.restrictScalars ℝ)

/-- The bilinear test `T(P, Q)(x) = ∑_{s, r < D} q_s p_r x(s, r)`. -/
def testSum (P Q : Polynomial ℂ) (D : ℕ) (x : ℕ × ℕ → ℂ) : ℂ :=
  ∑ s ∈ Finset.range D, ∑ r ∈ Finset.range D, Q.coeff s * P.coeff r * x (s, r)

theorem testSum_eq_zero_of_mem {P Q : Polynomial ℂ} {D : ℕ} (hP : P.natDegree < D)
    (hQ : Q.natDegree < D) {x : ℕ × ℕ → ℂ} {σ ζ : ℂ}
    (hx : (∃ α : ℕ → ℂ, x = fun p ↦ α p.1 * σ ^ p.2) ∨
      (∃ β : ℕ → ℂ, x = fun p ↦ ζ ^ p.1 * β p.2))
    (hσ : P.eval σ = 0) (hζ : Q.eval ζ = 0) : testSum P Q D x = 0 := by
  rcases hx with ⟨α, rfl⟩ | ⟨β, rfl⟩
  · have h : ∀ s, ∑ r ∈ Finset.range D, Q.coeff s * P.coeff r * (α s * σ ^ r) =
        Q.coeff s * α s * P.eval σ := fun s ↦ by
      rw [Polynomial.eval_eq_sum_range' hP, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by ring
    simp only [testSum, h, hσ, mul_zero, Finset.sum_const_zero]
  · have h : ∑ s ∈ Finset.range D, ∑ r ∈ Finset.range D, Q.coeff s * P.coeff r * (ζ ^ s * β r) =
        Q.eval ζ * ∑ r ∈ Finset.range D, P.coeff r * β r := by
      rw [Polynomial.eval_eq_sum_range' hQ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by ring
    simp only [testSum, h, hζ, zero_mul]

/-- `X ∏ᵢ (X - cᵢ)` over the nonzero `cᵢ`: it vanishes at every `cᵢ`, has no constant term,
and a nonzero coefficient of `X`. -/
def annPoly {k : ℕ} (c : Fin k → ℂ) : Polynomial ℂ :=
  Polynomial.X * ∏ i, (if c i = 0 then 1 else Polynomial.X - Polynomial.C (c i))

theorem annPoly_eval {k : ℕ} (c : Fin k → ℂ) (i : Fin k) : (annPoly c).eval (c i) = 0 := by
  rw [annPoly, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod]
  by_cases hi : c i = 0
  · rw [hi, zero_mul]
  · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    simp [hi]

theorem annPoly_coeff_zero {k : ℕ} (c : Fin k → ℂ) : (annPoly c).coeff 0 = 0 := by
  simp [annPoly]

theorem annPoly_coeff_one {k : ℕ} (c : Fin k → ℂ) : (annPoly c).coeff 1 ≠ 0 := by
  rw [annPoly, Polynomial.coeff_X_mul, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_
  by_cases hi : c i = 0 <;> simp [hi]

/-- The second Taylor coefficient of `t ↦ G(t, t)`, `e₂₀ + e₁₁ + e₀₂`. -/
def diagCoeff₂ : ℕ × ℕ → ℂ := fun p ↦ if p.1 + p.2 = 2 then 1 else 0

/-- **The mixed coefficient is not in the span.** -/
theorem diagCoeff₂_notMem : diagCoeff₂ ∉ sepSpan := by
  intro h
  obtain ⟨k, f, g, hfg⟩ := Submodule.mem_span_set'.1 h
  choose σ ζ hσζ using fun i ↦ (g i).2
  set P := annPoly σ
  set Q := annPoly ζ
  set D := max P.natDegree Q.natDegree + 3
  have hP : P.natDegree < D := by omega
  have hQ : Q.natDegree < D := by omega
  have hlin : testSum P Q D diagCoeff₂ =
      ∑ i, f i * testSum P Q D (g i) := by
    rw [← hfg]
    simp only [testSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Finset.sum_comm (s := Finset.univ)]
    exact Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
  have h0 : testSum P Q D diagCoeff₂ = 0 := by
    rw [hlin]
    exact Finset.sum_eq_zero fun i _ ↦ by
      rw [testSum_eq_zero_of_mem hP hQ (hσζ i) (annPoly_eval σ i) (annPoly_eval ζ i), mul_zero]
  have h1 : testSum P Q D diagCoeff₂ = Q.coeff 1 * P.coeff 1 := by
    have hD : 2 < D := by omega
    simp only [testSum, diagCoeff₂]
    rw [Finset.sum_eq_single 1, Finset.sum_eq_single 1]
    · simp
    · intro r _ hr
      have : ¬ (1 + r = 2) := by omega
      simp [this]
    · intro hr; exact absurd (Finset.mem_range.2 (by omega)) hr
    · intro s _ hs
      refine Finset.sum_eq_zero fun r _ ↦ ?_
      by_cases h2 : s + r = 2
      · rcases (show s = 0 ∨ s = 2 by omega) with rfl | rfl
        · simp [Q, annPoly_coeff_zero]
        · have : r = 0 := by omega
          subst this; simp [P, annPoly_coeff_zero]
      · simp [h2]
    · intro hs; exact absurd (Finset.mem_range.2 (by omega)) hs
  exact mul_ne_zero (annPoly_coeff_one ζ) (annPoly_coeff_one σ) (h1 ▸ h0)

/-- `G(ζ, σ) = (ζⁿ σᵐ)_{n, m}`, as a map into `sepSpan`. -/
def sepG (ζ σ : ℂ) : sepSpan :=
  ⟨fun p ↦ ζ ^ p.1 * σ ^ p.2, Submodule.subset_span ⟨σ, 0, Or.inl ⟨fun n ↦ ζ ^ n, rfl⟩⟩⟩

theorem sepSpan_hasSum_iff {f : ℕ → sepSpan} {a : sepSpan} :
    HasSum f a ↔ ∀ p, HasSum (fun k ↦ (f k : ℕ × ℕ → ℂ) p) ((a : ℕ × ℕ → ℂ) p) := by
  have hi : Topology.IsInducing (sepSpan.subtype) := Topology.IsInducing.subtypeVal
  rw [← hi.hasSum_iff f a]
  exact Pi.hasSum

/-- `(z + x)ⁿ = ∑_{k ≤ n} zᵏ C(n, k) xⁿ⁻ᵏ`, as an unconditional sum over `k ∈ ℕ`. -/
theorem hasSum_binomial (x z : ℂ) (n : ℕ) :
    HasSum (fun k ↦ z ^ k * ((n.choose k : ℂ) * x ^ (n - k))) ((x + z) ^ n) := by
  have h : HasSum (fun k ↦ z ^ k * ((n.choose k : ℂ) * x ^ (n - k)))
      (∑ k ∈ Finset.range (n + 1), z ^ k * ((n.choose k : ℂ) * x ^ (n - k))) :=
    hasSum_sum_of_ne_finset_zero fun k hk ↦ by
      rw [Finset.mem_range, not_lt] at hk
      simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]
  convert h using 1
  rw [add_comm, add_pow]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- `G` is complex analytic in `ζ`. -/
theorem cAnalyticOn_sepG_fst (σ : ℂ) : CAnalyticOn (fun ζ ↦ sepG ζ σ) univ := by
  intro x _
  refine ⟨1, one_pos, subset_univ _, fun k ↦ ⟨fun p ↦ (p.1.choose k : ℂ) * x ^ (p.1 - k) *
    σ ^ p.2, Submodule.subset_span ⟨σ, 0, Or.inl ⟨fun n ↦ (n.choose k : ℂ) * x ^ (n - k),
      rfl⟩⟩⟩, fun z _ ↦ ?_⟩
  refine sepSpan_hasSum_iff.2 fun p ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, sepG]
  have := (hasSum_binomial x z p.1).mul_right (σ ^ p.2)
  convert this using 1
  funext k; ring

/-- `G` is complex analytic in `σ`. -/
theorem cAnalyticOn_sepG_snd (ζ : ℂ) : CAnalyticOn (sepG ζ) univ := by
  intro x _
  refine ⟨1, one_pos, subset_univ _, fun k ↦ ⟨fun p ↦ ζ ^ p.1 * ((p.2.choose k : ℂ) *
    x ^ (p.2 - k)), Submodule.subset_span ⟨0, ζ, Or.inr ⟨fun m ↦ (m.choose k : ℂ) * x ^ (m - k),
      rfl⟩⟩⟩, fun z _ ↦ ?_⟩
  refine sepSpan_hasSum_iff.2 fun p ↦ ?_
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, sepG]
  have := (hasSum_binomial x z p.2).mul_left (ζ ^ p.1)
  convert this using 1
  funext k; ring

attribute [local instance] polynormableSpace_complex in
/-- **Separate analyticity does not imply joint analyticity without completeness.** The map
`G(ζ, σ) = (ζⁿ σᵐ)` into `sepSpan ⊆ ℂ^{ℕ × ℕ}` is complex analytic in each variable on `ℂ²`
(and continuous, `continuousOn_of_separately`), but not complex analytic: the second Taylor
coefficient of `t ↦ G(t, t)` would be `e₂₀ + e₁₁ + e₀₂ ∉ sepSpan` (`diagCoeff₂_notMem`). -/
theorem not_complexAnalyticOn_sepG : ¬ ComplexAnalyticOn (uncurry sepG) univ := by
  intro h
  have hg := ((complexAnalyticOn_iff_gateauxAnalyticOn isOpen_univ).1 h).2 0 (mem_univ _) (1, 1)
  obtain ⟨r, hr, -, a, ha⟩ := hg 0 (by simp)
  have hcoord : ∀ p : ℕ × ℕ, ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun k ↦ z ^ k • (a k : ℕ × ℕ → ℂ) p) (z ^ (p.1 + p.2)) := by
    intro p z hz
    have := sepSpan_hasSum_iff.1 (ha z hz) p
    simpa [sepG, uncurry, pow_add] using this
  have hδ : ∀ p : ℕ × ℕ, ∀ z : ℂ, ‖z‖ < r →
      HasSum (fun k ↦ z ^ k • (if k = p.1 + p.2 then (1 : ℂ) else 0)) (z ^ (p.1 + p.2)) := by
    intro p z _
    have := hasSum_ite_eq (p.1 + p.2) (z ^ (p.1 + p.2))
    convert this using 1
    funext k; split_ifs with hk <;> simp [hk]
  have heq : (a 2 : ℕ × ℕ → ℂ) = diagCoeff₂ := by
    funext p
    have h1 := coeff_eq_iteratedDeriv_of_hasSum (g := fun z : ℂ ↦ z ^ (p.1 + p.2)) (x := 0)
      (c := fun k ↦ (a k : ℕ × ℕ → ℂ) p) hr (fun z hz ↦ by simpa using hcoord p z hz) 2
    have h2 := coeff_eq_iteratedDeriv_of_hasSum (g := fun z : ℂ ↦ z ^ (p.1 + p.2)) (x := 0)
      (c := fun k ↦ if k = p.1 + p.2 then (1 : ℂ) else 0) hr
      (fun z hz ↦ by simpa using hδ p z hz) 2
    rw [h1, ← h2, diagCoeff₂]
    simp only [eq_comm]
  exact diagCoeff₂_notMem (heq ▸ (a 2).2)

/-- **`sepSpan` is not Mackey complete**: otherwise `G` would be complex analytic
(`complexAnalyticOn_of_separately`). -/
theorem not_mackeyComplete_sepSpan : ¬ MackeyComplete sepSpan := by
  intro hM
  refine not_complexAnalyticOn_sepG (complexAnalyticOn_of_separately isOpen_univ
    (fun σ ↦ ?_) (fun ζ ↦ ?_))
  · simpa using cAnalyticOn_sepG_fst σ
  · simpa using cAnalyticOn_sepG_snd ζ

end Counterexample

end LocallyConvex.Analysis

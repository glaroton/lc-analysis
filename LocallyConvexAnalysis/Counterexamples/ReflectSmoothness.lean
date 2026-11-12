/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Counterexamples.BoundedBelowStability
public import LocallyConvexAnalysis.Calculus.BoundedBelowLC
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Pointwise invertible derivatives do not reflect smoothness in Fréchet spaces

Let `j : E → F` be a smooth map between locally convex spaces. We prove
(`ContDiffMBOn.of_comp_of_equiEmbedding`, in `LocallyConvexAnalysis/Calculus/BoundedBelowLC.lean`)
that `j` reflects smoothness of continuous maps (if `γ` is continuous and `j ∘ γ` is `C^k`, then `γ`
is `C^k`) provided that the derivatives of `j` are topological embeddings *uniformly near each
point*, which is the hypothesis (H) `EquiEmbeddingNear`. In normed spaces (H) follows from a
lower bound for `dj` at each single point. The companion file `BoundedBelowStability.lean` shows
that in the Fréchet space `s` of rapidly decreasing sequences a pointwise lower bound does not
propagate to a neighborhood. Here we show that the uniformity cannot be removed from the theorem
itself: **pointwise embeddings, even pointwise automorphisms, do not suffice.** This answers the
question left open in the module docstring of `Calculus/BoundedBelowLC.lean`.

**The example** (`RapidDecay.not_reflect_smoothness`). The space `s` is complete
(`RapidDecay.completeSpace`), so the example does not exploit incompleteness.

* Let `φ` be the flat bump of `BoundedBelowStability.lean` (`φ = 1` on `|u - 1| ≤ 1/4`,
  `φ = 0` on `|u - 1| ≥ 1/2`) and `ψ(u) = (1 - (u - 1)²) φ(u)` (`RapidDecay.Reflect.psi`). Then
  `ψ` is smooth with bounded derivatives, `ψ ≤ 1`, `ψ(0) = 0`, and `ψ(u) = 1 - (u - 1)²` for
  `|u - 1| ≤ 1/4`.
* Let `εₙ = e^{-(n+1)}`, `aₙ(t) = 1 - (1 - εₙ) ψ((n + 1) t)` and `L(t) x = (aₙ(t) xₙ)ₙ`. Then
  `aₙ ≥ εₙ > 0`, `aₙ(0) = 1`, the `j`-th derivative of `aₙ` is bounded by `C_j (n + 1)^j`
  uniformly in `t`, and every `L(t)` is a continuous linear automorphism of `s`.
* `j(t, x) = (t, L(t) x)` is a smooth bijection of `ℝ × s` (`RapidDecay.Reflect.smoothMBOn_j`,
  `RapidDecay.Reflect.bijective_j`), and its derivative
  `dj(t, x)(τ, w) = (τ, L(t) w + τ L'(t) x)` is a continuous linear automorphism at every point,
  with inverse `(τ, z) ↦ (τ, L(t)⁻¹ (z - τ L'(t) x))` (`RapidDecay.Reflect.dj`,
  `RapidDecay.Reflect.dMB_j`).
* Let `cₙ = e^{-5(n+1)/4}`, `xₙ(t) = cₙ / aₙ(t)` and `γ(t) = (t, x(t))`. Since
  `|xₙ(t)| ≤ cₙ / εₙ = e^{-(n+1)/4}`, uniformly in `t`, `x(t) ∈ s` and `γ` is continuous
  (`RapidDecay.continuous_of_coord`). Moreover `j(γ(t)) = (t, c)` is affine, hence smooth.
* `γ` is not `C¹` near `0` (`RapidDecay.Reflect.not_contDiffMBOn_γ`). Let
  `tₙ = (1 + √εₙ)/(n + 1)`, so that `(n + 1) tₙ - 1 = √εₙ ≤ 1/4` for `n ≥ 3`. Then
  `aₙ(tₙ) = εₙ (2 - εₙ) ≤ 2 εₙ` and `aₙ'(tₙ) = 2 (n + 1) (1 - εₙ) √εₙ`, so
  `|xₙ'(tₙ)| = cₙ |aₙ'(tₙ)| / aₙ(tₙ)² ≥ (n + 1)/4` (`RapidDecay.Reflect.le_abs_xd`; the true
  size is of order `(n + 1) e^{(n+1)/4}`). If `γ` were `C¹` near `0`, then `t ↦ dγ(t)(1)` would be
  continuous at `0`, so `p₀` of its second component would be bounded near `0`; but its `n`-th
  coordinate is `xₙ'(t)` (evaluation of a coordinate is continuous and linear), which is
  unbounded along `tₙ → 0`.

The quadratic profile of `ψ` is essential: with the flat bump, `|aₙ'| / aₙ` is only
polynomially large in `n` where `aₙ` is small, and the estimate above breaks down.

**Consequences.**

* At every point `dj(p)` satisfies the pointwise version of (H)
  (`RapidDecay.Reflect.equiEmbeddingOn_singleton`), but by the theorem of
  `Calculus/BoundedBelowLC.lean` (H) fails at some point
  (`RapidDecay.Reflect.not_forall_equiEmbeddingNear`).
* The family of inverses is not continuous: `(p, v) ↦ dj(p)⁻¹ v` is not continuous
  (`RapidDecay.Reflect.not_continuous_dj_symm`); along `γ`, `dj(γ(t))⁻¹ (1, 0)` has coordinates
  `xₙ'(t)`.
* The inverse `j⁻¹(t, y) = (t, L(t)⁻¹ y)` is not `C¹` on any neighborhood of `(0, c)`
  (`RapidDecay.Reflect.not_contDiffMBOn_jInv`): `j` is a smooth bijection with invertible
  derivative everywhere which is not a `C¹` diffeomorphism.

**Source.** We found no source for this counterexample; we do not claim it is new. It belongs to
the family of examples in R. S. Hamilton, *The inverse function theorem of Nash and Moser*, Bull.
Amer. Math. Soc. 7 (1982), Part I: Counterexample 5.3.3 (p. 103) and §5.5, "Counterexamples in
Fréchet spaces" (p. 121 ff.). In Counterexample 5.5.3 (p. 125) the map `P(f) = e^f` has an
invertible derivative at every point, with a smooth family of inverses, but is not locally
invertible. Here `j` is a smooth bijection with invertible derivative everywhere whose inverse is
not `C¹`, and the family of inverses `dj(p)⁻¹` is not continuous.

## Main definitions

* `RapidDecay.Reflect.psi`: the profile `ψ(u) = (1 - (u - 1)²) φ(u)`.
* `RapidDecay.Reflect.L t`: the continuous linear automorphism `x ↦ (aₙ(t) xₙ)ₙ` of `s`.
* `RapidDecay.Reflect.j`, `RapidDecay.Reflect.jInv`: the smooth bijection
  `j(t, x) = (t, L(t) x)` of `ℝ × s` and its inverse.
* `RapidDecay.Reflect.dj p`: the derivative of `j` at `p`, a continuous linear automorphism.
* `RapidDecay.Reflect.γ`: the continuous curve `γ(t) = (t, x(t))`, `xₙ(t) = cₙ / aₙ(t)`.

## Main results

* `RapidDecay.not_reflect_smoothness`: there are a smooth bijection `j` of `ℝ × s` whose
  derivative at every point is a continuous linear automorphism and a continuous curve `γ` such
  that `j ∘ γ` is smooth but `γ` is not `C¹` on any neighborhood of `0`; moreover the pointwise
  version of (H) holds everywhere, (H) fails at some point, and `(p, v) ↦ dj(p)⁻¹ v` is not
  continuous.
* `RapidDecay.Reflect.smoothMBOn_j`, `RapidDecay.Reflect.bijective_j`,
  `RapidDecay.Reflect.dMB_j`: `j` is a smooth bijection with `dj(p)` invertible at every point.
* `RapidDecay.Reflect.smoothMBOn_j_comp_γ`, `RapidDecay.Reflect.not_contDiffMBOn_γ`: `j ∘ γ` is
  smooth, but `γ` is not `C¹` on any open set containing `0`.
* `RapidDecay.Reflect.equiEmbeddingOn_singleton`,
  `RapidDecay.Reflect.not_forall_equiEmbeddingNear`: `j` satisfies the pointwise version of (H)
  at every point, but not (H) itself.
* `RapidDecay.Reflect.not_continuous_dj_symm`: `(p, v) ↦ dj(p)⁻¹ v` is not continuous.
* `RapidDecay.Reflect.not_contDiffMBOn_jInv`: `j⁻¹` is not `C¹` on any open set containing
  `(0, c)`.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal lp


noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

namespace RapidDecay

/-! ### Auxiliary facts on `s` -/

/-- `(n + 1)^k e^{-r(n+1)} ≤ k! / r^k`, from `y^k / k! ≤ e^y`. -/
theorem wt_mul_exp_le {r : ℝ} (hr : 0 < r) (k n : ℕ) :
    wt k n * Real.exp (-(r * ((n : ℝ) + 1))) ≤ k.factorial / r ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := r * ((n : ℝ) + 1)) (by positivity) k
  rw [div_le_iff₀ (by positivity)] at h
  rw [le_div_iff₀ (by positivity), wt, Real.exp_neg]
  have he := Real.exp_pos (r * ((n : ℝ) + 1))
  calc ((n : ℝ) + 1) ^ k * (Real.exp (r * ((n : ℝ) + 1)))⁻¹ * r ^ k
      = (r * ((n : ℝ) + 1)) ^ k * (Real.exp (r * ((n : ℝ) + 1)))⁻¹ := by rw [mul_pow]; ring
    _ ≤ (Real.exp (r * ((n : ℝ) + 1)) * k.factorial) * (Real.exp (r * ((n : ℝ) + 1)))⁻¹ := by
        gcongr
    _ = k.factorial := by field_simp

/-- The coordinates `x ↦ x n` are continuous on `s`. -/
theorem continuous_coord (n : ℕ) : Continuous fun y : RapidDecay ↦ y n := by
  have h : Continuous (weights : RapidDecay → ℕ → ℓ^∞(ℕ, ℝ)) :=
    isUniformInducing_weights.uniformContinuous.continuous
  refine ((continuous_lp_apply n).comp ((_root_.continuous_apply 0).comp h)).congr fun y ↦ ?_
  simp [weights, wt]

/-- A curve in `s` is continuous if its coordinates are continuous and it is dominated by a fixed
rapidly decreasing sequence: the tail is uniformly small, and finitely many coordinates are
handled by continuity. -/
theorem continuous_of_coord {f : ℝ → RapidDecay} (hc : ∀ n, Continuous fun t ↦ f t n)
    {d : ℕ → ℝ} (hd : ∀ k, ∃ C, ∀ n, wt k n * d n ≤ C) (hfd : ∀ t n, |f t n| ≤ d n) :
    Continuous f := by
  refine continuous_iff_continuousAt.mpr fun t₀ ↦
    (withSeminorms.tendsto_nhds _ _).mpr fun k ε hε ↦ ?_
  obtain ⟨D, hD⟩ := hd (k + 1)
  have hD0 : 0 ≤ D :=
    (mul_nonneg (wt_pos _ _).le ((abs_nonneg _).trans (hfd t₀ 0))).trans (hD 0)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * D / ε)
  -- the tail
  have htail : ∀ t, ∀ n, N ≤ n → wt k n * |f t n - f t₀ n| ≤ ε / 2 := by
    intro t n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hA : wt k n * |f t n - f t₀ n| * ((n : ℝ) + 1) ≤ 2 * D := by
      have h1 : |f t n - f t₀ n| ≤ 2 * d n := by
        have := abs_sub (f t n) (f t₀ n)
        linarith [hfd t n, hfd t₀ n]
      calc wt k n * |f t n - f t₀ n| * ((n : ℝ) + 1)
          = wt (k + 1) n * |f t n - f t₀ n| := by rw [wt, wt, pow_succ]; ring
        _ ≤ wt (k + 1) n * (2 * d n) := by gcongr
        _ = 2 * (wt (k + 1) n * d n) := by ring
        _ ≤ 2 * D := by gcongr; exact hD n
    by_contra! hlt
    have h4 : 4 * D < ε * (N : ℝ) := by rw [div_lt_iff₀ hε] at hN; linarith
    have : ε / 2 * ((n : ℝ) + 1) < wt k n * |f t n - f t₀ n| * ((n : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hlt (by positivity)
    nlinarith
  -- the first `N` coordinates
  have hhead : ∀ᶠ t in 𝓝 t₀, ∀ n ∈ Finset.range N, wt k n * |f t n - f t₀ n| < ε / 2 := by
    rw [eventually_all_finset]
    intro n _
    have : Tendsto (fun t ↦ wt k n * |f t n - f t₀ n|) (𝓝 t₀)
        (𝓝 (wt k n * |f t₀ n - f t₀ n|)) :=
      (((hc n).tendsto t₀).sub_const _).abs.const_mul _
    rw [sub_self, abs_zero, mul_zero] at this
    exact this.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hhead] with t ht
  refine (seminorm_le (half_pos hε).le fun n ↦ ?_).trans_lt (half_lt_self hε)
  rw [sub_apply]
  rcases lt_or_ge n N with h | h
  · exact (ht n (Finset.mem_range.mpr h)).le
  · exact htail t n h

/-! ### The quadratic bump -/

namespace Reflect

/-- The bump with quadratic profile `ψ(u) = (1 - (u - 1)²) φ(u)`, where `φ = bump` is flat
equal to `1` on `|u - 1| ≤ 1/4` and vanishes for `|u - 1| ≥ 1/2`. -/
def psi (u : ℝ) : ℝ := (1 - (u - 1) ^ 2) * bump u

/-- `ψ` is smooth. -/
theorem contDiff_psi : ContDiff ℝ (⊤ : ℕ∞) psi := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun u : ℝ ↦ 1 - (u - 1) ^ 2 :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).pow 2)
  exact h1.mul bump.contDiff

/-- `ψ` has compact support. -/
theorem hasCompactSupport_psi : HasCompactSupport psi :=
  bump.hasCompactSupport.mul_left (f := fun u : ℝ ↦ 1 - (u - 1) ^ 2)

/-- `ψ ≤ 1`. -/
theorem psi_le_one (u : ℝ) : psi u ≤ 1 :=
  (mul_le_of_le_one_left (bump_nonneg u) (by nlinarith [sq_nonneg (u - 1)])).trans
    (bump_le_one u)

/-- `ψ(u) = 0` for `|u - 1| ≥ 1/2`. -/
theorem psi_eq_zero {u : ℝ} (hu : 1 / 2 ≤ |u - 1|) : psi u = 0 := by
  rw [psi, bump_eq_zero hu, mul_zero]

/-- `ψ(0) = 0`. -/
theorem psi_zero : psi 0 = 0 := psi_eq_zero (by norm_num)

/-- `ψ(u) = 1 - (u - 1)²` for `|u - 1| ≤ 1/4`. -/
theorem psi_of_near {u : ℝ} (hu : |u - 1| ≤ 1 / 4) : psi u = 1 - (u - 1) ^ 2 := by
  rw [psi, bump.one_of_mem_closedBall (by simpa [bump, Real.dist_eq] using hu), mul_one]

/-- `ψ'(u) = -2 (u - 1)` for `|u - 1| < 1/4`. -/
theorem hasDerivAt_psi_of_near {u : ℝ} (hu : |u - 1| < 1 / 4) :
    HasDerivAt psi (-(2 * (u - 1))) u := by
  have hev : (bump : ℝ → ℝ) =ᶠ[𝓝 u] fun _ ↦ 1 := by
    have ho : IsOpen {v : ℝ | |v - 1| < 1 / 4} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [ho.mem_nhds hu] with v hv
    exact bump.one_of_mem_closedBall (by simpa [bump, Real.dist_eq] using le_of_lt hv)
  have hb : HasDerivAt (bump : ℝ → ℝ) 0 u := (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq hev
  have h1 : HasDerivAt (fun v : ℝ ↦ 1 - (v - 1) ^ 2) (-(2 * (u - 1))) u := by
    convert (((hasDerivAt_id u).sub_const 1).pow 2).const_sub 1 using 1 <;> simp
  have hb1 : bump u = 1 := hev.eq_of_nhds
  exact (h1.mul hb).congr_deriv (by rw [hb1]; ring)

/-- The derivatives of `ψ`. -/
theorem hasDerivAt_iteratedDeriv_psi (j : ℕ) (u : ℝ) :
    HasDerivAt (iteratedDeriv j psi) (iteratedDeriv (j + 1) psi u) u := by
  rw [iteratedDeriv_succ]
  exact (contDiff_psi.differentiable_iteratedDeriv j
    (by exact_mod_cast WithTop.coe_lt_top j) u).hasDerivAt

/-- Each derivative of `ψ` is bounded. -/
theorem exists_bound_iteratedDeriv_psi (j : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ u, |iteratedDeriv j psi u| ≤ B := by
  have hc : Continuous (iteratedFDeriv ℝ j psi) :=
    contDiff_psi.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (hasCompactSupport_psi.iteratedFDeriv j)
  refine ⟨max B 0, le_max_right _ _, fun u ↦ ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hB u).trans (le_max_left _ _)

/-! ### The multipliers and the operators `L(t)` -/

/-- The multipliers `aₙ(t) = 1 - (1 - e^{-(n+1)}) ψ((n + 1) t)`. -/
def a (n : ℕ) (t : ℝ) : ℝ := 1 - cf n * psi (((n : ℝ) + 1) * t)

/-- `aₙ` and its derivatives: `Da j n t = ∂ᵗʲ aₙ(t)`. -/
def Da (j n : ℕ) (t : ℝ) : ℝ :=
  (if j = 0 then 1 else 0) - cf n * (wt j n * iteratedDeriv j psi (((n : ℝ) + 1) * t))

/-- `Da 0 = a`. -/
theorem Da_zero : Da 0 = a := by
  funext n t
  simp [Da, a, wt]

/-- The derivatives of `aₙ` are bounded by `C_j (n + 1)^j`, uniformly in `t`. -/
theorem admissible_Da : Admissible Da where
  hasDerivAt j n t := by
    have h1 : HasDerivAt (fun t ↦ iteratedDeriv j psi (((n : ℝ) + 1) * t))
        (iteratedDeriv (j + 1) psi (((n : ℝ) + 1) * t) * (((n : ℝ) + 1) * 1)) t :=
      (hasDerivAt_iteratedDeriv_psi j _).comp t ((hasDerivAt_id t).const_mul _)
    have h2 := (h1.const_mul (cf n * wt j n)).const_sub (if j = 0 then (1 : ℝ) else 0)
    convert h2 using 1
    · funext s
      simp only [Da]
      ring
    · simp only [Da, wt, pow_succ, Nat.add_one_ne_zero, ↓reduceIte]
      ring
  bound j := by
    obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_psi j
    refine ⟨1 + B, by positivity, j, fun n t ↦ ?_⟩
    have h1 : |(if j = 0 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have h2 : |cf n * (wt j n * iteratedDeriv j psi (((n : ℝ) + 1) * t))| ≤ wt j n * B := by
      rw [abs_mul, abs_mul, abs_of_nonneg (cf_nonneg n), abs_of_pos (wt_pos j n)]
      calc cf n * (wt j n * |iteratedDeriv j psi (((n : ℝ) + 1) * t)|) ≤ 1 * (wt j n * B) := by
            gcongr
            · exact cf_le_one n
            · exact hB _
        _ = wt j n * B := one_mul _
    calc |Da j n t| ≤ 1 + wt j n * B := (abs_sub _ _).trans (add_le_add h1 h2)
      _ ≤ wt j n + wt j n * B := by gcongr; exact one_le_wt j n
      _ = (1 + B) * wt j n := by ring

/-- `aₙ` has derivative `Da 1 n t`. -/
theorem hasDerivAt_a (n : ℕ) (t : ℝ) : HasDerivAt (a n) (Da 1 n t) t := by
  simpa [Da_zero] using admissible_Da.hasDerivAt 0 n t

/-- `aₙ` is continuous. -/
theorem continuous_a (n : ℕ) : Continuous (a n) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_a n t).continuousAt

/-- For fixed `t`, `(aₙ(t))ₙ` is a bounded multiplier. -/
theorem polyBdd_a (t : ℝ) : PolyBdd fun n ↦ a n t := by
  simpa [Da_zero] using admissible_Da.polyBdd 0 t

/-- `aₙ(t) ≥ e^{-(n+1)}`. -/
theorem exp_neg_le_a (n : ℕ) (t : ℝ) : Real.exp (-((n : ℝ) + 1)) ≤ a n t := by
  have := mul_le_mul_of_nonneg_left (psi_le_one (((n : ℝ) + 1) * t)) (cf_nonneg n)
  rw [a, cf] at *
  linarith

/-- `aₙ(t) > 0`. -/
theorem a_pos (n : ℕ) (t : ℝ) : 0 < a n t := (Real.exp_pos _).trans_le (exp_neg_le_a n t)

/-- `aₙ(0) = 1`. -/
theorem a_zero (n : ℕ) : a n 0 = 1 := by simp [a, psi_zero]

/-- For fixed `t`, `(1 / aₙ(t))ₙ` is bounded by `e^{3/(2|t|)}`. -/
theorem polyBdd_inv_a (t : ℝ) : PolyBdd fun n ↦ (a n t)⁻¹ := by
  refine ⟨Real.exp (3 / (2 * |t|)), (Real.exp_pos _).le, 0, fun n ↦ ?_⟩
  rw [wt, pow_zero, mul_one, abs_inv, abs_of_pos (a_pos n t)]
  by_cases h : psi (((n : ℝ) + 1) * t) = 0
  · rw [a, h, mul_zero, sub_zero, inv_one]
    exact Real.one_le_exp (by positivity)
  · have hd : |((n : ℝ) + 1) * t - 1| < 1 / 2 := by
      by_contra! h'
      exact h (psi_eq_zero h')
    rw [abs_lt] at hd
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht : 0 < t := by
      by_contra! ht
      nlinarith
    rw [abs_of_pos ht]
    calc (a n t)⁻¹ ≤ (Real.exp (-((n : ℝ) + 1)))⁻¹ :=
          inv_anti₀ (Real.exp_pos _) (exp_neg_le_a n t)
      _ = Real.exp ((n : ℝ) + 1) := by rw [Real.exp_neg, inv_inv]
      _ ≤ Real.exp (3 / (2 * t)) := by
          gcongr
          rw [le_div_iff₀ (by positivity)]
          nlinarith

/-- **The operators `L t x = (aₙ(t) xₙ)ₙ`**, continuous linear automorphisms of `s`. -/
def L (t : ℝ) : RapidDecay ≃L[ℝ] RapidDecay :=
  ContinuousLinearEquiv.equivOfInverse (mulCLM _ (polyBdd_a t)) (mulCLM _ (polyBdd_inv_a t))
    (fun x ↦ ext fun n ↦ by
      simp only [mulCLM_apply]
      rw [← mul_assoc, inv_mul_cancel₀ (a_pos n t).ne', one_mul])
    (fun x ↦ ext fun n ↦ by
      simp only [mulCLM_apply]
      rw [← mul_assoc, mul_inv_cancel₀ (a_pos n t).ne', one_mul])

/-- The terms of `L t x`. -/
@[simp] theorem L_apply (t : ℝ) (x : RapidDecay) (n : ℕ) : L t x n = a n t * x n :=
  mulCLM_apply (polyBdd_a t) x n

/-- The terms of `(L t)⁻¹ x`. -/
@[simp] theorem L_symm_apply (t : ℝ) (x : RapidDecay) (n : ℕ) :
    (L t).symm x n = (a n t)⁻¹ * x n :=
  mulCLM_apply (polyBdd_inv_a t) x n

/-- `L 0` is the identity. -/
theorem L_zero : L 0 = ContinuousLinearEquiv.refl ℝ RapidDecay :=
  ContinuousLinearEquiv.ext (funext fun x ↦ ext fun n ↦ by simp [a_zero])

/-! ### The map `j` and its derivative -/

/-- **The map `j(t, x) = (t, L t x)`** on `ℝ × s`. -/
def j (p : ℝ × RapidDecay) : ℝ × RapidDecay := (p.1, L p.1 p.2)

/-- `j` in terms of the multiplier family `fam`. -/
theorem j_eq : j = fun p ↦ (p.1, fam (Da 0) p) := by
  funext p
  refine Prod.ext rfl (ext fun n ↦ ?_)
  change L p.1 p.2 n = fam (Da 0) p n
  rw [L_apply, fam_apply admissible_Da, Da_zero]

/-- **`j` is smooth** in the sense of Michal–Bastiani on `ℝ × s`. -/
theorem smoothMBOn_j : SmoothMBOn j univ := by
  intro k
  rw [j_eq]
  exact ContDiffMBOn.prodMk isOpen_univ
    ((ContinuousLinearMap.fst ℝ ℝ RapidDecay).contDiffMBOn k univ)
    (contDiffMBOn_fam k admissible_Da)

/-- The inverse of `j`, `(t, y) ↦ (t, L(t)⁻¹ y)`. -/
def jInv (p : ℝ × RapidDecay) : ℝ × RapidDecay := (p.1, (L p.1).symm p.2)

/-- **`j` is bijective**, with inverse `jInv`. -/
theorem bijective_j : Function.Bijective j :=
  Function.bijective_iff_has_inverse.mpr ⟨jInv, fun p ↦ by simp [j, jInv],
    fun p ↦ by simp [j, jInv]⟩

/-- The vector `L'(t) x = (aₙ'(t) xₙ)ₙ`, for `p = (t, x)`. -/
def dL (p : ℝ × RapidDecay) : RapidDecay := fam (Da 1) p

/-- The terms of `L'(t) x`. -/
theorem dL_apply (p : ℝ × RapidDecay) (n : ℕ) : dL p n = Da 1 n p.1 * p.2 n :=
  fam_apply admissible_Da 1 p n

/-- **The derivative of `j` at `p = (t, x)`**, `(τ, w) ↦ (τ, L(t) w + τ L'(t) x)`, as a
continuous linear automorphism of `ℝ × s`, with inverse
`(τ, z) ↦ (τ, L(t)⁻¹ (z - τ L'(t) x))`. -/
def dj (p : ℝ × RapidDecay) : (ℝ × RapidDecay) ≃L[ℝ] (ℝ × RapidDecay) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ ℝ RapidDecay).prod
      ((L p.1 : RapidDecay →L[ℝ] RapidDecay).comp (ContinuousLinearMap.snd ℝ ℝ RapidDecay) +
        (ContinuousLinearMap.fst ℝ ℝ RapidDecay).smulRight (dL p)))
    ((ContinuousLinearMap.fst ℝ ℝ RapidDecay).prod
      (((L p.1).symm : RapidDecay →L[ℝ] RapidDecay).comp
        (ContinuousLinearMap.snd ℝ ℝ RapidDecay -
          (ContinuousLinearMap.fst ℝ ℝ RapidDecay).smulRight (dL p))))
    (fun v ↦ Prod.ext rfl (by simp))
    (fun v ↦ Prod.ext rfl (by simp))

/-- `dj(t, x)(τ, w) = (τ, L(t) w + τ L'(t) x)`. -/
theorem dj_apply (p v : ℝ × RapidDecay) : dj p v = (v.1, L p.1 v.2 + v.1 • dL p) := rfl

/-- `dj(t, x)⁻¹(τ, z) = (τ, L(t)⁻¹ (z - τ L'(t) x))`. -/
theorem dj_symm_apply (p v : ℝ × RapidDecay) :
    (dj p).symm v = (v.1, (L p.1).symm (v.2 - v.1 • dL p)) := rfl

/-- The directional derivatives of `j`. -/
theorem hasDirDerivAt_j (p v : ℝ × RapidDecay) : HasDirDerivAt j p v (dj p v) := by
  have h : HasDirDerivAt (fun p : ℝ × RapidDecay ↦ (p.1, fam (Da 0) p)) p v
      (v.1, v.1 • fam (Da 1) p + fam (Da 0) (p.1, v.2)) :=
    ((ContinuousLinearMap.fst ℝ ℝ RapidDecay).hasDirDerivAt p v).prodMk
      (hasDirDerivAt_fam admissible_Da p v)
  rw [j_eq]
  convert h using 1
  refine Prod.ext rfl (ext fun n ↦ ?_)
  simp only [dj_apply, add_apply, smul_apply, L_apply, dL_apply, fam_apply admissible_Da]
  rw [Da_zero]
  ring

/-- **The derivative of `j` is invertible everywhere**: `dj(p) = dMB j (p, ·)` is a continuous
linear automorphism of `ℝ × s`. -/
theorem dMB_j (p v : ℝ × RapidDecay) : dMB j (p, v) = dj p v :=
  (hasDirDerivAt_j p v).dMB_eq

/-- **Pointwise embeddings.** At every point `p` the derivative `dj(p)` is a topological
embedding, in the form of the hypothesis (H) of `Calculus/BoundedBelowLC.lean` (`EquiEmbeddingOn`)
restricted to the single point `p`: for every continuous seminorm `r` there are a continuous
seminorm `q` and
`C ≥ 0` with `r w ≤ C q (dj(p) w)`. -/
theorem equiEmbeddingOn_singleton (p : ℝ × RapidDecay) : EquiEmbeddingOn j {p} := by
  intro r hr
  refine ⟨r.comp ((dj p).symm : (ℝ × RapidDecay) →L[ℝ] (ℝ × RapidDecay)).toLinearMap,
    hr.comp (dj p).symm.continuous, 1, zero_le_one, fun w z hz ↦ ?_⟩
  rw [image_singleton, convexHull_singleton, closure_singleton, mem_singleton_iff, dMB_j] at hz
  subst hz
  simp

/-! ### The curve `γ` -/

/-- The sequence `cₙ = e^{-5(n+1)/4}`. -/
def c (n : ℕ) : ℝ := Real.exp (-(5 / 4 * ((n : ℝ) + 1)))

/-- The terms `xₙ(t) = cₙ / aₙ(t)`. -/
def xs (t : ℝ) (n : ℕ) : ℝ := c n / a n t

/-- `|xₙ(t)| ≤ cₙ / e^{-(n+1)} = e^{-(n+1)/4}`. -/
theorem abs_xs_le (t : ℝ) (n : ℕ) : |xs t n| ≤ Real.exp (-(1 / 4 * ((n : ℝ) + 1))) := by
  have hc : 0 < c n := Real.exp_pos _
  rw [xs, abs_of_pos (div_pos hc (a_pos n t))]
  calc c n / a n t ≤ c n / Real.exp (-((n : ℝ) + 1)) :=
        div_le_div_of_nonneg_left hc.le (Real.exp_pos _) (exp_neg_le_a n t)
    _ = Real.exp (-(1 / 4 * ((n : ℝ) + 1))) := by
        rw [c, ← Real.exp_sub]
        ring_nf

/-- `(xₙ(t))ₙ` is rapidly decreasing, uniformly in `t`. -/
theorem xs_bound (t : ℝ) (k : ℕ) : ∀ n, wt k n * |xs t n| ≤ k.factorial / (1 / 4 : ℝ) ^ k :=
  fun n ↦ (mul_le_mul_of_nonneg_left (abs_xs_le t n) (wt_pos k n).le).trans
    (wt_mul_exp_le (by norm_num) k n)

/-- **The curve `x(t) = (cₙ / aₙ(t))ₙ`** in `s`. -/
def x (t : ℝ) : RapidDecay := mk (xs t) fun k ↦ ⟨_, xs_bound t k⟩

/-- The terms of `x(t)`. -/
@[simp] theorem x_apply (t : ℝ) (n : ℕ) : x t n = c n / a n t := rfl

/-- **The curve `γ(t) = (t, x(t))`** in `ℝ × s`. -/
def γ (t : ℝ) : ℝ × RapidDecay := (t, x t)

/-- `x` is continuous. -/
theorem continuous_x : Continuous x :=
  continuous_of_coord (fun n ↦ continuous_const.div (continuous_a n) fun t ↦ (a_pos n t).ne')
    (fun k ↦ ⟨_, wt_mul_exp_le (by norm_num : (0 : ℝ) < 1 / 4) k⟩) abs_xs_le

/-- **`γ` is continuous.** -/
theorem continuous_γ : Continuous γ := continuous_id.prodMk continuous_x

/-- The constant sequence `c = (cₙ)ₙ`, as an element of `s`. -/
def cvec : RapidDecay := mk c fun k ↦ ⟨k.factorial / (5 / 4 : ℝ) ^ k, fun n ↦ by
  rw [c, abs_of_pos (Real.exp_pos _)]
  exact wt_mul_exp_le (by norm_num : (0 : ℝ) < 5 / 4) k n⟩

/-- `j(γ(t)) = (t, c)`. -/
theorem j_comp_γ : j ∘ γ = fun t ↦ (t, cvec) := by
  funext t
  refine Prod.ext rfl (ext fun n ↦ ?_)
  simp only [Function.comp_apply, j, γ, L_apply, x_apply, cvec, mk_apply]
  field_simp [(a_pos n t).ne']

/-- **`j ∘ γ` is smooth**: it is the affine map `t ↦ (t, c)`. -/
theorem smoothMBOn_j_comp_γ : SmoothMBOn (j ∘ γ) univ := by
  intro k
  rw [j_comp_γ]
  exact ContDiffMBOn.prodMk isOpen_univ (smoothMBOn_id univ k) (contDiffMBOn_const k cvec univ)

/-! ### `γ` is not `C¹` -/

/-- The derivative `xₙ'(t) = -cₙ aₙ'(t) / aₙ(t)²`. -/
def xd (n : ℕ) (t : ℝ) : ℝ := -(c n * Da 1 n t) / a n t ^ 2

/-- `xₙ` has derivative `xd n t`. -/
theorem hasDerivAt_xs (n : ℕ) (t : ℝ) : HasDerivAt (fun s ↦ xs s n) (xd n t) t := by
  have := ((hasDerivAt_a n t).inv (a_pos n t).ne').const_mul (c n)
  convert this using 1
  · funext s
    simp [xs, div_eq_mul_inv]
  · simp only [xd]
    ring

/-- The number `rₙ = e^{-(n+1)/4}`; then `cₙ = rₙ⁵` and `e^{-(n+1)} = rₙ⁴`. -/
def r (n : ℕ) : ℝ := Real.exp (-(1 / 4 * ((n : ℝ) + 1)))

/-- `rₙ > 0`. -/
theorem r_pos (n : ℕ) : 0 < r n := Real.exp_pos _

/-- `rₙ⁴ = e^{-(n+1)}`. -/
theorem r_pow_four (n : ℕ) : r n ^ 4 = Real.exp (-((n : ℝ) + 1)) := by
  rw [r, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `cₙ = rₙ⁵`. -/
theorem c_eq (n : ℕ) : c n = r n ^ 5 := by
  rw [c, r, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `rₙ < 1/2` for `n ≥ 3`. -/
theorem r_lt_half {n : ℕ} (hn : 3 ≤ n) : r n < 1 / 2 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : r n ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : 2 < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
  rw [Real.exp_neg] at h1
  refine h1.trans_lt ?_
  rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith

/-- The points `tₙ = (1 + rₙ²)/(n + 1)`, where `(n + 1) tₙ - 1 = √εₙ` with `εₙ = e^{-(n+1)}`. -/
def tn (n : ℕ) : ℝ := (1 + r n ^ 2) / ((n : ℝ) + 1)

/-- **The derivatives blow up**: `|xₙ'(tₙ)| ≥ (n + 1)/4` for `n ≥ 3`. Here
`aₙ(tₙ) = rₙ⁴ (2 - rₙ⁴)` and `aₙ'(tₙ) = 2 (n + 1) (1 - rₙ⁴) rₙ²`, so that
`|xₙ'(tₙ)| = 2 (n + 1) (1 - rₙ⁴) / (rₙ (2 - rₙ⁴)²)`. -/
theorem le_abs_xd {n : ℕ} (hn : 3 ≤ n) : ((n : ℝ) + 1) / 4 ≤ |xd n (tn n)| := by
  have hr := r_pos n
  have hr2 := r_lt_half hn
  set R := r n with hR
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hu : ((n : ℝ) + 1) * tn n = 1 + R ^ 2 := by
    rw [tn, ← hR]; field_simp
  have hnear : |((n : ℝ) + 1) * tn n - 1| < 1 / 4 := by
    rw [hu, add_sub_cancel_left, abs_of_pos (by positivity)]
    nlinarith
  have hcf : cf n = 1 - R ^ 4 := by rw [cf, hR, r_pow_four]
  have ha : a n (tn n) = R ^ 4 * (2 - R ^ 4) := by
    rw [a, psi_of_near hnear.le, hu, hcf]
    ring
  have hDa : Da 1 n (tn n) = 2 * ((n : ℝ) + 1) * (1 - R ^ 4) * R ^ 2 := by
    rw [Da, iteratedDeriv_one, (hasDerivAt_psi_of_near hnear).deriv, hu, hcf]
    simp [wt]
    ring
  have hR4 : R ^ 4 < 1 / 16 := by
    calc R ^ 4 < (1 / 2) ^ 4 := by gcongr
      _ = 1 / 16 := by norm_num
  have hxd : xd n (tn n) = -(2 * ((n : ℝ) + 1) * (1 - R ^ 4)) / (R * (2 - R ^ 4) ^ 2) := by
    have h2 : (0 : ℝ) < 2 - R ^ 4 := by linarith
    rw [xd, hDa, ha, c_eq]
    field_simp
    ring
  have hR4' : 0 < R ^ 4 := pow_pos hr 4
  have hD : 0 < R * (2 - R ^ 4) ^ 2 := by
    have : (0 : ℝ) < 2 - R ^ 4 := by linarith
    positivity
  have hD2 : R * (2 - R ^ 4) ^ 2 ≤ 2 := by
    have h1 : (2 - R ^ 4) ^ 2 ≤ 4 := by nlinarith
    nlinarith
  rw [hxd, neg_div, abs_neg, abs_of_pos (div_pos (by nlinarith) hD), le_div_iff₀ hD]
  nlinarith

/-- `0 < tₙ ≤ 2 / (n + 1)` for `n ≥ 3`. -/
theorem tn_pos_le {n : ℕ} (hn : 3 ≤ n) : 0 < tn n ∧ tn n ≤ 2 / ((n : ℝ) + 1) := by
  have hr2 := r_lt_half hn
  have hr := r_pos n
  refine ⟨by unfold tn; positivity, ?_⟩
  unfold tn
  gcongr
  nlinarith

/-- **The key estimate.** If the `n`-th coordinate of the second component of `f t` is `xₙ'(t)`
for all `t` near `0`, then `f` is not continuous at `0`: `p₀` of the second component is at least
`|xₙ'(tₙ)| ≥ (n + 1)/4` at `tₙ → 0`. -/
theorem not_continuousAt_of_coord {f : ℝ → ℝ × RapidDecay} {U : Set ℝ} (hU : U ∈ 𝓝 0)
    (hf : ∀ t ∈ U, ∀ n, (f t).2 n = xd n t) : ¬ ContinuousAt f 0 := by
  intro hc
  have h1 : ContinuousAt (fun t ↦ seminorm 0 (f t).2) 0 :=
    (withSeminorms.continuous_seminorm 0).continuousAt.comp (continuous_snd.continuousAt.comp hc)
  set M := seminorm 0 (f 0).2 + 1
  have h2 : ∀ᶠ t in 𝓝 0, seminorm 0 (f t).2 < M ∧ t ∈ U :=
    (h1.eventually (gt_mem_nhds (lt_add_one _))).and hU
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h2
  obtain ⟨N, hN⟩ := exists_nat_gt (max (4 * M) (2 / δ))
  have hN1 : 4 * M < N := (le_max_left _ _).trans_lt hN
  have hN2 : 2 / δ < N := (le_max_right _ _).trans_lt hN
  have hn3 : 3 ≤ N + 3 := by omega
  obtain ⟨htpos, htle⟩ := tn_pos_le hn3
  have hdist : dist (tn (N + 3)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
    refine htle.trans_lt ?_
    rw [div_lt_iff₀ hδ] at hN2
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith
  obtain ⟨hlt, hU'⟩ := hball hdist
  have h3 := le_abs_xd hn3
  rw [← hf _ hU' (N + 3)] at h3
  have h4 : |(f (tn (N + 3))).2 (N + 3)| ≤ seminorm 0 (f (tn (N + 3))).2 := by
    simpa [wt] using le_seminorm 0 (f (tn (N + 3))).2 (N + 3)
  push_cast at h3
  linarith

/-- **`γ` is not `C¹`** on any open set containing `0`: if it were, `t ↦ dγ(t)(1)` would be
continuous at `0`, but its coordinates are the derivatives `xₙ'(t)`, which blow up at `tₙ → 0`
(`le_abs_xd`). -/
theorem not_contDiffMBOn_γ {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) :
    ¬ ContDiffMBOn 1 γ U := by
  intro h
  have hd : ContinuousOn (dMB γ) (U ×ˢ univ) := h.2.2
  have hc : ContinuousAt (fun t ↦ dMB γ (t, 1)) 0 :=
    (hd.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨h0, mem_univ _⟩)).comp
      (continuous_id.prodMk continuous_const).continuousAt
  refine not_continuousAt_of_coord (hU.mem_nhds h0) (fun t ht n ↦ ?_) hc
  have hdd : HasDirDerivAt γ t 1 (dMB γ (t, 1)) := h.2.1 t ht 1
  have : HasDerivAt (fun s ↦ xs s n) ((dMB γ (t, 1)).2 n) t := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine ((((continuous_coord n).comp continuous_snd).tendsto _).comp hdd).congr fun σ ↦ ?_
    simp [γ, xs]
  exact this.unique (hasDerivAt_xs n t)

/-- **The inverses of the derivatives do not depend continuously on the point**: along `γ`,
`dj(γ(t))⁻¹ (1, 0)` has coordinates `xₙ'(t)`, so it is not continuous at `t = 0`. -/
theorem not_continuous_dj_symm :
    ¬ Continuous fun q : (ℝ × RapidDecay) × (ℝ × RapidDecay) ↦ (dj q.1).symm q.2 := by
  intro h
  refine not_continuousAt_of_coord (U := univ) univ_mem (fun t _ n ↦ ?_)
    ((h.comp (continuous_γ.prodMk
      (continuous_const (y := ((1 : ℝ), (0 : RapidDecay)))))).continuousAt (x := 0))
  simp only [Function.comp_apply, dj_symm_apply, L_symm_apply, sub_apply, zero_apply,
    smul_apply, dL_apply, γ, x_apply, xd]
  field_simp [(a_pos n t).ne']
  ring

/-- `j⁻¹(t, c) = γ(t)`. -/
theorem jInv_comp : jInv ∘ (fun t : ℝ ↦ (t, cvec)) = γ := by
  funext t
  refine Prod.ext rfl (ext fun n ↦ ?_)
  simp only [Function.comp_apply, jInv, γ, L_symm_apply, x_apply, cvec, mk_apply]
  rw [div_eq_inv_mul]

/-- **The inverse of `j` is not `C¹`** on any open set containing `(0, c) = j(γ(0))`: otherwise
`γ = j⁻¹ ∘ (t ↦ (t, c))` would be `C¹` near `0`. -/
theorem not_contDiffMBOn_jInv {V : Set (ℝ × RapidDecay)} (hV : IsOpen V)
    (h0 : ((0 : ℝ), cvec) ∈ V) : ¬ ContDiffMBOn 1 jInv V := by
  intro h
  have hc : Continuous fun t : ℝ ↦ (t, cvec) := continuous_id.prodMk continuous_const
  refine not_contDiffMBOn_γ (hV.preimage hc) h0 ?_
  rw [← jInv_comp]
  exact ContDiffMBOn.comp (hV.preimage hc) hV h
    (ContDiffMBOn.prodMk (hV.preimage hc) (smoothMBOn_id _ 1) (contDiffMBOn_const 1 cvec _))
    fun _ ht ↦ ht

/-- **(H) fails somewhere.** By the theorem `ContDiffMBOn.of_comp_of_equiEmbedding`,
`j` cannot satisfy the hypothesis (H) of uniform embeddings near every point; it does satisfy its
pointwise version (`equiEmbeddingOn_singleton`). -/
theorem not_forall_equiEmbeddingNear : ¬ ∀ p, EquiEmbeddingNear j p := fun h ↦
  not_contDiffMBOn_γ isOpen_univ (mem_univ 0)
    (ContDiffMBOn.of_comp_of_equiEmbedding_of_smooth isOpen_univ smoothMBOn_j
      (fun p _ ↦ h p) 1 isOpen_univ continuous_γ.continuousOn (mapsTo_univ _ _)
      (smoothMBOn_j_comp_γ 1))

end Reflect

/-- **Pointwise invertible derivatives do not reflect smoothness in Fréchet spaces.** There are a
smooth bijection `j` of `ℝ × s` (in the sense of Michal–Bastiani) whose derivative `dj(p)` at
every point `p` is a continuous linear automorphism, and a continuous curve `γ : ℝ → ℝ × s`, such
that `j ∘ γ` is smooth but `γ` is not `C¹` on any neighborhood of `0`. Moreover:

* each `dj(p)` is an embedding in the sense of the pointwise version of the hypothesis (H) of
  `Calculus/BoundedBelowLC.lean` (`EquiEmbeddingOn j {p}`), but (H) itself (`EquiEmbeddingNear`)
  fails at some point;
* the inverses `dj(p)⁻¹` do not depend continuously on `p`: `(p, v) ↦ dj(p)⁻¹ v` is not
  continuous. -/
theorem not_reflect_smoothness :
    ∃ (j : ℝ × RapidDecay → ℝ × RapidDecay) (γ : ℝ → ℝ × RapidDecay),
      SmoothMBOn j univ ∧ Function.Bijective j ∧
      (∃ e : ℝ × RapidDecay → (ℝ × RapidDecay) ≃L[ℝ] (ℝ × RapidDecay),
        (∀ p v, dMB j (p, v) = e p v) ∧
        ¬ Continuous fun q : (ℝ × RapidDecay) × (ℝ × RapidDecay) ↦ (e q.1).symm q.2) ∧
      (∀ p, EquiEmbeddingOn j {p}) ∧ ¬ (∀ p, EquiEmbeddingNear j p) ∧
      Continuous γ ∧ SmoothMBOn (j ∘ γ) univ ∧
      ∀ U : Set ℝ, IsOpen U → (0 : ℝ) ∈ U → ¬ ContDiffMBOn 1 γ U :=
  ⟨Reflect.j, Reflect.γ, Reflect.smoothMBOn_j, Reflect.bijective_j,
    ⟨Reflect.dj, Reflect.dMB_j, Reflect.not_continuous_dj_symm⟩,
    Reflect.equiEmbeddingOn_singleton, Reflect.not_forall_equiEmbeddingNear,
    Reflect.continuous_γ, Reflect.smoothMBOn_j_comp_γ,
    fun _ hU h0 ↦ Reflect.not_contDiffMBOn_γ hU h0⟩

end RapidDecay

end LocallyConvex.Analysis.Counterexamples

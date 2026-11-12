/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Counterexamples.ODEExistence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Frobenius theorem fails in Fréchet spaces

**In Banach spaces**, a distribution of rank one spanned by a nonvanishing `C¹` vector field `X`
is integrable: through each point passes an integral curve of `X` (Picard–Lindelöf), and for
higher rank an involutive split distribution is integrable (`exists_frobenius` in
`Frobenius/Basic.lean`, and `Frobenius/Chart.lean`; [Lan99, Chapter VI, Theorem 1.1]).

**The Fréchet counterexample** (`RapidDecay.not_exists_tangent_curve`; A. Kriegl, P. W. Michor,
*The Convenient Setting of Global Analysis*, Math. Surveys Monogr. 53, AMS, 1997, 32.12,
Example 1, p. 330). On the Fréchet space `s` of rapidly decreasing sequences, the continuous
linear vector field `x ↦ D x`, `D x = (n² xₙ)ₙ` (`RapidDecay.sqMul`), spans a distribution of rank
one, `x ↦ ℝ · D x`, on the open set `{x | D x ≠ 0}`. A distribution of rank one is involutive.
But through `a = (e^{-(n+1)})ₙ` there is no curve tangent to it: if `c(0) = a` and
`c'(t) = f(t) D(c(t))` with `f` continuous and `f(0) ≠ 0` (a regular curve tangent to the
distribution, parametrized arbitrarily), then each coordinate satisfies `cₙ' = f n² cₙ`, so
`cₙ(t) = e^{n² φ(t)} aₙ` with `φ(t) = ∫₀ᵗ f`, and `φ(t) > 0` for some `t` arbitrarily close to
`0`, where `c(t)` would be unbounded. Hence there is no integral manifold through `a`.

## Main results

* `RapidDecay.not_exists_tangent_curve`: there is no curve `c` in `s` with `c(0) = (e^{-(n+1)})ₙ`
  and `c'(t) = f(t) D(c(t))` on `(-ε, ε)`, for `f` continuous with `f(0) ≠ 0` (Kriegl–Michor,
  32.12, Example 1).
* `RapidDecay.not_exists_integral_curve`: the Frobenius theorem fails on `s`: there are a
  continuous linear operator `D` and a point `a` with `D a ≠ 0` such that no curve through `a`
  is tangent to the rank-one distribution `x ↦ ℝ · D x`.
* `RapidDecay.exists_integral_pos`: if `f : ℝ → ℝ` is continuous with `f(0) ≠ 0`, then
  `∫₀ᵗ f > 0` for some `t ∈ (-ε, ε)`.

## Implementation notes

Kriegl–Michor use the operator `(x₀, x₁, …) ↦ (0, 1² x₁, 2² x₂, …)` composed with a shift and
the initial value `(1, 0, 0, …)`; we use the diagonal operator and the initial value of
`ODEExistence.lean`, which give the same conclusion with a shorter proof. KM reduce the general
tangent curve to a solution of `x' = D x` by a reparametrization; we integrate the coordinates
directly.

## References

* [A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*][KM97]
* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

namespace RapidDecay

/-- If `f` is continuous and `f(0) ≠ 0`, then `∫₀ᵗ f > 0` for some `t ∈ (-ε, ε)`. -/
theorem exists_integral_pos {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : ∃ t ∈ Ioo (-ε) ε, 0 < ∫ s in (0 : ℝ)..t, f s := by
  -- a sign-definite neighbourhood of `0`
  have key : ∀ g : ℝ → ℝ, Continuous g → 0 < g 0 →
      ∃ δ > 0, δ < ε ∧ ∀ s, |s| < δ → 0 < g s := by
    intro g hg hg0
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
      (hg.continuousAt.eventually (lt_mem_nhds hg0))
    refine ⟨min δ ε / 2, by positivity, by linarith [min_le_right δ ε], fun s hs ↦ hball ?_⟩
    rw [Real.dist_eq, sub_zero]
    linarith [min_le_left δ ε]
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · obtain ⟨δ, hδ, hδε, hg⟩ := key (fun s ↦ -f s) hf.neg (by linarith)
    refine ⟨-δ, ⟨by linarith, by linarith⟩, ?_⟩
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hf.neg.intervalIntegrable _ _)
      (fun x hx ↦ hg x ?_) (by linarith)
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  · obtain ⟨δ, hδ, hδε, hg⟩ := key f hf hpos
    refine ⟨δ, ⟨by linarith, hδε⟩, ?_⟩
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _)
      (fun x hx ↦ hg x ?_) hδ
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]

/-- **No curve is tangent to the line field `ℝ · D x` through `a = (e^{-(n+1)})ₙ`**: there is no
curve `c` in `s` with `c(0) = a` and `c'(t) = f(t) D(c(t))` on `(-ε, ε)`, for `f` continuous with
`f(0) ≠ 0` ([KM97, 32.12, Example 1]). -/
theorem not_exists_tangent_curve {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ (c : ℝ → RapidDecay) (f : ℝ → ℝ), c 0 = expSeq ∧ Continuous f ∧ f 0 ≠ 0 ∧
      ∀ t ∈ Ioo (-ε) ε, HasDirDerivAt c t 1 (f t • sqMul (c t)) := by
  rintro ⟨c, f, h0, hf, hf0, hc⟩
  set φ : ℝ → ℝ := fun t ↦ ∫ s in (0 : ℝ)..t, f s with hφ_def
  have hφ : ∀ t, HasDerivAt φ (f t) t := fun t ↦ (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hφ0 : φ 0 = 0 := by simp [hφ_def]
  -- the coordinates satisfy `cₙ' = f n² cₙ`
  have hd : ∀ n : ℕ, ∀ s ∈ Ioo (-ε) ε,
      HasDerivAt (fun s ↦ c s n) (f s * ((n : ℝ) ^ 2 * c s n)) s := fun n s hs ↦ by
    have h := (hc s hs).clm_comp_real (coordCLM n)
    simpa using hasDirDerivAt_one_iff.mp h
  -- hence `cₙ(t) = e^{n² φ(t)} aₙ`
  have hsol : ∀ n : ℕ, ∀ t ∈ Ioo (-ε) ε,
      c t n = Real.exp ((n : ℝ) ^ 2 * φ t) * Real.exp (-((n : ℝ) + 1)) := by
    intro n t ht
    set g : ℝ → ℝ := fun s ↦ Real.exp (-((n : ℝ) ^ 2 * φ s)) * c s n
    have hg : ∀ s ∈ Ioo (-ε) ε, HasDerivAt g 0 s := by
      intro s hs
      have h1 : HasDerivAt (fun s ↦ Real.exp (-((n : ℝ) ^ 2 * φ s)))
          (Real.exp (-((n : ℝ) ^ 2 * φ s)) * -((n : ℝ) ^ 2 * f s)) s :=
        ((hφ s).const_mul _).neg.exp
      convert h1.mul (hd n s hs) using 1
      ring
    have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hconst : g t = g 0 := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs ↦ (hg s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hg s hs).deriv) ht h0mem
    simp only [g, hφ0, mul_zero, neg_zero, Real.exp_zero, one_mul, h0, expSeq_apply] at hconst
    rw [← hconst, ← mul_assoc, ← Real.exp_add]
    simp
  -- but `φ(t) > 0` for some `t`, where `c(t)` is unbounded
  obtain ⟨t, ht, hpos⟩ := exists_integral_pos hf hf0 hε
  obtain ⟨C, hC⟩ := (c t).bound 0
  obtain ⟨n, hn⟩ := exists_lt_exp (φ t) hpos C
  have := hC n
  rw [wt, pow_zero, one_mul, hsol n t ht, abs_of_pos (by positivity)] at this
  linarith

/-- **The Frobenius theorem fails on the Fréchet space `s`**: there are a continuous linear
operator `D` and a point `a` with `D a ≠ 0` such that no curve through `a` is tangent to the
rank-one (hence involutive) distribution `x ↦ ℝ · D x` near `a`. -/
theorem not_exists_integral_curve :
    ∃ (D : RapidDecay →L[ℝ] RapidDecay) (a : RapidDecay), D a ≠ 0 ∧ ∀ ε > 0,
      ¬ ∃ (c : ℝ → RapidDecay) (f : ℝ → ℝ), c 0 = a ∧ Continuous f ∧ f 0 ≠ 0 ∧
        ∀ t ∈ Ioo (-ε) ε, HasDirDerivAt c t 1 (f t • D (c t)) := by
  refine ⟨sqMul, expSeq, fun h ↦ ?_, fun _ hε ↦ not_exists_tangent_curve hε⟩
  have := congrArg (fun x : RapidDecay ↦ x 1) h
  simp only [sqMul_apply, expSeq_apply, zero_apply] at this
  have hpos : (0 : ℝ) < ((1 : ℕ) : ℝ) ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) + 1)) := by positivity
  linarith

end RapidDecay

end LocallyConvex.Analysis.Counterexamples

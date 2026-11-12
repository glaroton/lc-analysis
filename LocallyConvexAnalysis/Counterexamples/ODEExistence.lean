/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Counterexamples.ODEUniqueness
public import LocallyConvexAnalysis.Counterexamples.ReflectSmoothness
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Existence of solutions of linear differential equations

If `A` is a continuous linear operator on a Banach space `E`, then `y' = A y`, `y(0) = y₀` has the
solution `y(t) = exp(t A) y₀`, defined for all `t ∈ ℝ`. For locally Lipschitz fields on Banach
spaces, local existence is the Picard–Lindelöf theorem ([GN26, Theorem 2.4.23, p. 196], and
Corollary 2.4.25, p. 198). We show that existence fails on Fréchet spaces: on the Fréchet space
`s` of rapidly decreasing sequences, the operator `D x = (n² xₙ)ₙ` is continuous and linear, but for
`a = (e^{-(n+1)})ₙ ∈ s` the equation `y' = D y`, `y(0) = a` has no solution on `[0, ε)` for any
`ε > 0`: each coordinate of a solution satisfies `yₙ' = n² yₙ`, so `yₙ(t) = e^{n² t} aₙ`, and for
`t > 0` this sequence is not even bounded.

This is the example of J. Milnor, *Remarks on infinite-dimensional Lie groups*, in *Relativity,
Groups and Topology II* (Les Houches, 1983), North-Holland, 1984, §3, the exercise after
Warning 3.6, p. 1025 (the heat equation `∂ₜ f = ∂ₓ² f` on `C^∞(S¹)` has unique solutions for
`t ≥ 0`, which usually do not extend to `t < 0`), as presented in K.-H. Neeb,
*Towards a Lie theory of locally convex groups*, Jpn. J. Math. 1 (2006), Example II.3.12
(numbering of arXiv:1501.06269): the heat equation with reversed time, `∂ₜ f = -∂ₓ² f`, on
`C^∞(S¹)`. We state it on the Fourier side:
the Fourier coefficients identify `C^∞(S¹)` with rapidly decreasing sequences indexed by `ℤ`, and
`-∂ₓ²` with multiplication by `n²`; we keep the indices `n ≥ 0`, which is enough. A simpler
example on the (complete, but not metrizable) direct sum `ℝ^(ℕ)`, with the right shift, is
[GN26, Example 2.4.2, p. 188].

## Main definitions

* `RapidDecay.sqMul`: the continuous linear operator `D x = (n² xₙ)ₙ` on `s`.
* `RapidDecay.expSeq`: the initial value `a = (e^{-(n+1)})ₙ ∈ s`.

## Main results

* `exists_linearODE_solution`: on a Banach space, `t ↦ exp(t A) y₀` solves `y' = A y`,
  `y(0) = y₀`, for all `t`.
* `RapidDecay.not_exists_solution`: for every `ε > 0` there is no curve `γ` in `s`, continuous
  from the right at `0`, with `γ(0) = a` and `γ' = D γ` on `(0, ε)`.
* `RapidDecay.not_exists_linearODE_solution`: the linear equation `y' = D y` on the Fréchet
  space `s` has no solution on any interval `[0, ε)` for some initial value; the locally convex
  counterpart of `exists_linearODE_solution`.

## Implementation notes

Completeness is not what fails: `s` is complete (`RapidDecay.completeSpace`). What fails is the
existence of `exp(t D)`, which needs a norm.

The derivative of a curve is the directional derivative `HasDirDerivAt γ t 1` of the
Michal–Bastiani calculus, which for curves in a normed space is the usual derivative
(`hasDirDerivAt_one_iff`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

/-- **Existence for linear equations in Banach spaces**: `t ↦ exp(t A) y₀` solves `y' = A y`,
`y(0) = y₀`, for all `t`. -/
theorem exists_linearODE_solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (y₀ : E) :
    ∃ γ : ℝ → E, γ 0 = y₀ ∧ ∀ t, HasDirDerivAt γ t 1 (A (γ t)) := by
  refine ⟨fun t ↦ NormedSpace.exp (t • A) y₀, by simp, fun t ↦ hasDirDerivAt_one_iff.mpr ?_⟩
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).clm_apply (hasDerivAt_const t y₀)
  simp only [map_zero, add_zero] at h
  exact h

namespace RapidDecay

/-- The coordinate `x ↦ xₙ`, as a continuous linear functional on `s`. -/
def coordCLM (n : ℕ) : RapidDecay →L[ℝ] ℝ :=
  ⟨{ toFun := fun y ↦ y n
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl }, continuous_coord n⟩

@[simp] theorem coordCLM_apply (n : ℕ) (y : RapidDecay) : coordCLM n y = y n := rfl

/-- The multiplier `n²` is polynomially bounded. -/
theorem polyBdd_sq : PolyBdd fun n ↦ ((n : ℝ)) ^ 2 :=
  ⟨1, zero_le_one, 2, fun n ↦ by
    rw [abs_of_nonneg (by positivity), one_mul, wt]
    exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) 2⟩

/-- The operator `D x = (n² xₙ)ₙ` on `s`: on the Fourier side, `-d²/dx²` on `C^∞(S¹)`. -/
def sqMul : RapidDecay →L[ℝ] RapidDecay := mulCLM _ polyBdd_sq

@[simp] theorem sqMul_apply (x : RapidDecay) (n : ℕ) : sqMul x n = (n : ℝ) ^ 2 * x n :=
  mulCLM_apply polyBdd_sq x n

/-- The initial value `a = (e^{-(n+1)})ₙ ∈ s`. -/
def expSeq : RapidDecay :=
  mk (fun n ↦ Real.exp (-((n : ℝ) + 1))) fun k ↦ ⟨k.factorial, fun n ↦ by
    have h := wt_mul_exp_le one_pos k n
    simp only [one_mul, one_pow, div_one] at h
    rwa [abs_of_pos (Real.exp_pos _)]⟩

@[simp] theorem expSeq_apply (n : ℕ) : expSeq n = Real.exp (-((n : ℝ) + 1)) := rfl

/-- A real function with `c' = λ c` on `(0, t)` and continuous on `[0, t]` is `e^{λ t} c(0)`. -/
theorem eq_exp_mul_of_hasDerivAt {c : ℝ → ℝ} {l t : ℝ} (ht : 0 < t)
    (hc : ContinuousOn c (Icc 0 t)) (hd : ∀ s ∈ Ioo 0 t, HasDerivAt c (l * c s) s) :
    c t = Real.exp (l * t) * c 0 := by
  set g : ℝ → ℝ := fun s ↦ Real.exp (-(l * s)) * c s
  have hg : ContinuousOn g (Icc 0 t) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn).mul hc
  have hg' : ∀ s ∈ Ioo 0 t, HasDerivAt g 0 s := by
    intro s hs
    have h1 : HasDerivAt (fun s ↦ Real.exp (-(l * s))) (Real.exp (-(l * s)) * -(l * 1)) s :=
      ((hasDerivAt_id s).const_mul l).neg.exp
    convert h1.mul (hd s hs) using 1
    ring
  obtain ⟨u, -, hu⟩ := exists_hasDerivAt_eq_slope g (fun _ ↦ 0) ht hg hg'
  have hgt : g t = g 0 := by
    have := hu.symm
    rw [div_eq_zero_iff, sub_eq_zero] at this
    exact this.resolve_right (by linarith)
  simp only [g, mul_zero, neg_zero, Real.exp_zero, one_mul] at hgt
  rw [← hgt, ← mul_assoc, ← Real.exp_add]
  simp

/-- `e^{n² t - (n+1)}` is unbounded in `n`, for `t > 0`. -/
theorem exists_lt_exp (t : ℝ) (ht : 0 < t) (C : ℝ) :
    ∃ n : ℕ, C < Real.exp ((n : ℝ) ^ 2 * t) * Real.exp (-((n : ℝ) + 1)) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max 1 ((|C| + 2) / t))
  refine ⟨n, ?_⟩
  have h1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans hn
  have h2 : (|C| + 2) / t ≤ n := (le_max_right _ _).trans hn
  have h3 : |C| + 2 ≤ n * t := by rwa [div_le_iff₀ ht] at h2
  have h4 : |C| + n + 1 ≤ (n : ℝ) ^ 2 * t := by nlinarith [abs_nonneg C]
  rw [← Real.exp_add]
  calc C ≤ |C| := le_abs_self C
    _ < (n : ℝ) ^ 2 * t + -((n : ℝ) + 1) + 1 := by linarith
    _ ≤ Real.exp ((n : ℝ) ^ 2 * t + -((n : ℝ) + 1)) := Real.add_one_le_exp _

/-- **No solutions in `s`**: for every `ε > 0` there is no curve `γ` in `s`, continuous from the
right at `0`, with `γ(0) = (e^{-(n+1)})ₙ` and `γ' = D γ` on `(0, ε)`, where `D x = (n² xₙ)ₙ`. -/
theorem not_exists_solution {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ γ : ℝ → RapidDecay, γ 0 = expSeq ∧ ContinuousWithinAt γ (Ici 0) 0 ∧
      ∀ t ∈ Ioo 0 ε, HasDirDerivAt γ t 1 (sqMul (γ t)) := by
  rintro ⟨γ, h0, hc0, hγ⟩
  set t := ε / 2 with ht_def
  have ht : 0 < t := by positivity
  have htε : t < ε := by rw [ht_def]; linarith
  -- each coordinate solves `cₙ' = n² cₙ`
  have hd : ∀ n : ℕ, ∀ s ∈ Ioo 0 ε,
      HasDerivAt (fun s ↦ γ s n) ((n : ℝ) ^ 2 * γ s n) s := fun n s hs ↦ by
    have h := (hγ s hs).clm_comp_real (coordCLM n)
    simpa using hasDirDerivAt_one_iff.mp h
  have hcont : ∀ n : ℕ, ContinuousOn (fun s ↦ γ s n) (Icc 0 t) := by
    intro n s hs
    rcases eq_or_lt_of_le hs.1 with rfl | hs0
    · exact ((continuous_coord n).continuousAt.comp_continuousWithinAt hc0).mono
        fun x hx ↦ hx.1
    · exact (hd n s ⟨hs0, hs.2.trans_lt htε⟩).continuousAt.continuousWithinAt
  have hsol : ∀ n : ℕ, γ t n = Real.exp ((n : ℝ) ^ 2 * t) * Real.exp (-((n : ℝ) + 1)) := by
    intro n
    have := eq_exp_mul_of_hasDerivAt ht (hcont n) fun s hs ↦ hd n s ⟨hs.1, hs.2.trans htε⟩
    rw [this, h0, expSeq_apply]
  -- but `γ(t)` is bounded
  obtain ⟨C, hC⟩ := (γ t).bound 0
  obtain ⟨n, hn⟩ := exists_lt_exp t ht C
  have := hC n
  rw [wt, pow_zero, one_mul, hsol n, abs_of_pos (by positivity)] at this
  linarith

/-- **The linear equation `y' = D y` on the Fréchet space `s` has no solutions** for some initial
value, on any interval `[0, ε)`: the locally convex counterpart of `exists_linearODE_solution`. -/
theorem not_exists_linearODE_solution :
    ∃ (D : RapidDecay →L[ℝ] RapidDecay) (a : RapidDecay), ∀ ε > 0,
      ¬ ∃ γ : ℝ → RapidDecay, γ 0 = a ∧ ContinuousWithinAt γ (Ici 0) 0 ∧
        ∀ t ∈ Ioo 0 ε, HasDirDerivAt γ t 1 (D (γ t)) :=
  ⟨sqMul, expSeq, fun _ hε ↦ not_exists_solution hε⟩

end RapidDecay

end LocallyConvex.Analysis.Counterexamples

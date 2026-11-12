/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MichalBastiani
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Uniqueness of solutions of linear differential equations

We compare linear differential equations `y' = A y`, `y(0) = 0`, with `A` continuous and linear,
in normed spaces and in locally convex spaces. In a normed space `E` (no completeness is needed),
the only solution is `y = 0`. This is the uniqueness theorem for Lipschitz fields (Mathlib's
`ODE_solution_unique_univ`; [GN26, Proposition 2.4.11]). On the Fréchet space `ℝ^ℕ`, with the
product topology, the left shift `A (x₀, x₁, …) = (x₁, x₂, …)` is continuous and linear, but
`y' = A y`, `y(0) = 0` has the nonzero solution `y(t) = (h(t), h'(t), h''(t), …)`, where
`h(t) = e^{-1/t}` for `t > 0` and `h(t) = 0` for `t ≤ 0` (Mathlib's `expNegInvGlue`) is smooth with
all derivatives zero at `0` ([GN26, Example 2.4.3], with `e^{-1/t²}`; see also R. S.
Hamilton, *The inverse function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982),
5.6.1).

Both statements use the same notion of derivative of a curve, the directional derivative
`HasDirDerivAt γ t 1` of the Michal–Bastiani calculus (`LocallyConvex.Analysis`), which for curves
in a normed space is the usual derivative.

## Main definitions

* `leftShift`: the left shift `(x₀, x₁, …) ↦ (x₁, x₂, …)`, a continuous linear map on `ℝ^ℕ`.
* `jetCurve`: the curve `t ↦ (h(t), h'(t), h''(t), …)` in `ℝ^ℕ`, with `h = expNegInvGlue`.

## Main results

* `hasDirDerivAt_one_iff`: for curves in a normed space, the directional derivative in the
  direction `1` is the usual derivative.
* `linearODE_eq_zero`: **in normed spaces**, if `A` is a continuous linear operator, the only
  solution of `y' = A y`, `y(0) = 0` is `y = 0` ([GN26, Proposition 2.4.11]).
* `iteratedDeriv_expNegInvGlue_zero`: all derivatives of `expNegInvGlue` vanish at `0`.
* `hasDirDerivAt_jetCurve`: `jetCurve` solves `y' = A y` for the left shift `A`.
* `exists_linearODE_ne_zero`: **the locally convex counterexample**: on `ℝ^ℕ` there are a
  continuous linear `A` and a nonzero solution of `y' = A y`, `y(0) = 0` ([GN26, Example 2.4.3]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

/-- For curves in a normed space, the directional derivative in the direction `1` is the
derivative. -/
theorem hasDirDerivAt_one_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E}
    {t : ℝ} {v : E} : HasDirDerivAt γ t 1 v ↔ HasDerivAt γ v t := by
  rw [hasDerivAt_iff_tendsto_slope_zero, HasDirDerivAt]
  simp only [smul_eq_mul, mul_one]

/-- **Uniqueness for linear equations in normed spaces**: if `A` is a continuous linear operator
on a normed space, the only solution of `y' = A y` with `y(0) = 0` is `0`. -/
theorem linearODE_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : E →L[ℝ] E)
    {γ : ℝ → E} (hγ : ∀ t, HasDirDerivAt γ t 1 (A (γ t))) (h0 : γ 0 = 0) : γ = 0 :=
  ODE_solution_unique_univ (v := fun _ ↦ A) (s := fun _ ↦ univ) (K := ‖A‖₊) (t₀ := 0)
    (fun _ ↦ A.lipschitzWith.lipschitzOnWith) (fun t ↦ ⟨hasDirDerivAt_one_iff.1 (hγ t), trivial⟩)
    (fun t ↦ ⟨by simp, trivial⟩) h0

/-- The left shift on `ℝ^ℕ`. -/
def leftShift : (ℕ → ℝ) →L[ℝ] (ℕ → ℝ) :=
  ContinuousLinearMap.pi fun n ↦ ContinuousLinearMap.proj (n + 1)

theorem leftShift_apply (x : ℕ → ℝ) (n : ℕ) : leftShift x n = x (n + 1) :=
  rfl

/-- The curve `t ↦ (h(t), h'(t), h''(t), …)` in `ℝ^ℕ`, with `h = expNegInvGlue`. -/
def jetCurve (t : ℝ) : ℕ → ℝ :=
  fun n ↦ iteratedDeriv n expNegInvGlue t

/-- All derivatives of `expNegInvGlue` vanish at `0`. -/
theorem iteratedDeriv_expNegInvGlue_zero (n : ℕ) : iteratedDeriv n expNegInvGlue 0 = 0 := by
  have hcont : Continuous (iteratedDeriv n expNegInvGlue) :=
    (expNegInvGlue.contDiff (n := ⊤)).continuous_iteratedDeriv n (by exact_mod_cast le_top)
  have hneg : Iio (0 : ℝ) ⊆ {x | iteratedDeriv n expNegInvGlue x = 0} := fun x hx ↦ by
    have hev : expNegInvGlue =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
      eventuallyEq_of_mem (Iio_mem_nhds hx) fun y hy ↦ expNegInvGlue.zero_of_nonpos (le_of_lt hy)
    rw [mem_ofPred_eq, hev.iteratedDeriv_eq n, iteratedDeriv_const]
    split_ifs <;> rfl
  have hcl := (isClosed_eq hcont continuous_const).closure_subset_iff.2 hneg
  rw [closure_Iio' (nonempty_Iio)] at hcl
  exact hcl (mem_Iic.2 le_rfl)

theorem hasDirDerivAt_jetCurve (t : ℝ) : HasDirDerivAt jetCurve t 1 (leftShift (jetCurve t)) := by
  rw [HasDirDerivAt, tendsto_pi_nhds]
  intro n
  have hd : HasDerivAt (iteratedDeriv n expNegInvGlue)
      (iteratedDeriv (n + 1) expNegInvGlue t) t := by
    rw [iteratedDeriv_succ]
    exact ((expNegInvGlue.contDiff (n := ⊤)).differentiable_iteratedDeriv n
      (by exact_mod_cast WithTop.coe_lt_top n) t).hasDerivAt
  have := hd.tendsto_slope_zero
  simpa [jetCurve, leftShift_apply, smul_eq_mul] using this

/-- **Non-uniqueness for linear equations in `ℝ^ℕ`**: the left shift `A` on the Fréchet space
`ℝ^ℕ` is continuous and linear, but `y' = A y`, `y(0) = 0` has a nonzero solution. -/
theorem exists_linearODE_ne_zero :
    ∃ (A : (ℕ → ℝ) →L[ℝ] (ℕ → ℝ)) (γ : ℝ → ℕ → ℝ),
      (∀ t, HasDirDerivAt γ t 1 (A (γ t))) ∧ γ 0 = 0 ∧ γ ≠ 0 := by
  refine ⟨leftShift, jetCurve, hasDirDerivAt_jetCurve, ?_, fun h ↦ ?_⟩
  · funext n
    exact iteratedDeriv_expNegInvGlue_zero n
  · have h1 := congrFun (congrFun h 1) 0
    simp only [jetCurve, iteratedDeriv_zero, Pi.zero_apply] at h1
    exact (expNegInvGlue.pos_of_pos one_pos).ne' h1

end LocallyConvex.Analysis.Counterexamples

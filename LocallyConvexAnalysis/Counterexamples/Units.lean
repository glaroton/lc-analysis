/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.ContinuousMap.LocallyConvex
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# The group of units is open in Banach algebras, but not in Fréchet algebras

In a complete normed ring the units form an open set (Mathlib's `Units.isOpen`, through the
Neumann series). We show that this fails for complete locally convex algebras: in the algebra
`C(ℝ, ℝ)` with the compact-open topology, a Fréchet algebra, the units, i.e. the functions that
never vanish, do not form an open set. The functions `fₙ` equal to `1` on `[-n, n]` and vanishing
at `n + 1` are not units, and they converge to `1` uniformly on compact sets
([GN26, Example 5.3.9(b)], for `C(M, ℂ)` with `M` not compact).

## Main definitions

* `plateau n`: the function equal to `1` on `[-n, n]`, to `0` outside `(-n-1, n+1)`, and affine
  in between.

## Main results

* `isOpen_isUnit`: the units of a complete normed ring form an open set.
* `plateau_not_isUnit`, `tendsto_plateau`: each `plateau n` vanishes somewhere, so it is not a
  unit, and `plateau n → 1` in the compact-open topology.
* `not_isOpen_isUnit_continuousMap`: the units of `C(ℝ, ℝ)` do not form an open set, although
  `C(ℝ, ℝ)` is a complete locally convex algebra ([GN26, Example 5.3.9(b)]).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

/-- **The units of a Banach algebra form an open set.** -/
theorem isOpen_isUnit {R : Type*} [NormedRing R] [CompleteSpace R] :
    IsOpen {x : R | IsUnit x} :=
  Units.isOpen

/-- `C(ℝ, ℝ)` with the compact-open topology is a locally convex space. -/
example : LocallyConvexSpace ℝ C(ℝ, ℝ) := inferInstance

/-- `C(ℝ, ℝ)` with the compact-open topology is complete. -/
example : CompleteSpace C(ℝ, ℝ) := inferInstance

/-- The function equal to `1` on `[-n, n]`, to `0` outside `(-n-1, n+1)`, and affine between. -/
def plateau (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun x ↦ min 1 (max 0 ((n : ℝ) + 1 - |x|)), by fun_prop⟩

theorem plateau_apply (n : ℕ) (x : ℝ) : plateau n x = min 1 (max 0 ((n : ℝ) + 1 - |x|)) :=
  rfl

theorem plateau_eq_one {n : ℕ} {x : ℝ} (hx : |x| ≤ n) : plateau n x = 1 := by
  rw [plateau_apply]
  exact min_eq_left (le_max_of_le_right (by linarith))

theorem plateau_not_isUnit (n : ℕ) : ¬ IsUnit (plateau n) := by
  rintro ⟨u, hu⟩
  have h := congrArg (fun f : C(ℝ, ℝ) ↦ f ((n : ℝ) + 1)) u.mul_inv
  simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply, hu, plateau_apply] at h
  have h0 : min (1 : ℝ) (max 0 ((n : ℝ) + 1 - |(n : ℝ) + 1|)) = 0 := by
    rw [abs_of_nonneg (by positivity), sub_self, max_self, min_eq_right zero_le_one]
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- The plateaux converge to `1` in the compact-open topology. -/
theorem tendsto_plateau : Tendsto plateau atTop (𝓝 1) := by
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [eventually_atTop]
  refine ⟨⌈R⌉₊, fun n hn x hx ↦ ?_⟩
  have hxR : |x| ≤ R := by simpa [Real.dist_eq] using hR hx
  have hRn : R ≤ n := (Nat.le_ceil R).trans (by exact_mod_cast hn)
  rw [ContinuousMap.one_apply, plateau_eq_one (hxR.trans hRn), dist_self]
  exact hε

/-- **The units of `C(ℝ, ℝ)` do not form an open set**, although `C(ℝ, ℝ)` is a complete locally
convex algebra. -/
theorem not_isOpen_isUnit_continuousMap : ¬ IsOpen {f : C(ℝ, ℝ) | IsUnit f} := by
  intro hO
  have hev := tendsto_plateau.eventually (hO.mem_nhds isUnit_one)
  obtain ⟨n, hn⟩ := hev.exists
  exact plateau_not_isUnit n hn

end LocallyConvex.Analysis.Counterexamples

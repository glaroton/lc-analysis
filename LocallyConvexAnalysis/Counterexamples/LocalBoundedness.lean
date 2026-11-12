/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.BanachHolomorphic
public import LocallyConvexAnalysis.MappingSpace.CkSuperposition
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Complex analytic maps need not be locally bounded

**With a normed target** (`ComplexAnalyticOn.exists_bounded`): a complex analytic map into a
normed space is continuous, hence bounded on a neighbourhood of each point. Between Banach
spaces, complex analyticity is equivalent to Gâteaux analyticity together with local boundedness
([GN26, Exercise 2.1.7, p. 142]).

**The locally convex counterexample** (`exists_complexAnalyticOn_not_bounded`,
[GN26, Exercise 2.1.10, p. 142]). On the Banach space `ℓ¹ = ℓ¹(ℕ, ℂ)`, the series
`f(x) = ∑ₖ 2^{k+1} x_k^{2k+2}` converges locally uniformly, and `f : ℓ¹ → ℂ` is complex analytic;
but `f` is unbounded on the unit ball (`f(r eₖ) = (2 r²)^{k+1}`, and `2 r² > 1` for
`r ∈ (1/√2, 1)`). Then `g(x) = (f((k + 1) x))ₖ` is a complex analytic map `ℓ¹ → ℂ^ℕ` which is
bounded on no neighbourhood of `0`: its `k`-th coordinate is unbounded on the ball of radius
`1 / (k + 1)`. Here `ℂ^ℕ` is a Fréchet space, complete but not normable.

As Glöckner–Neeb observe after the exercise, `g` is therefore not complex analytic in the sense of
N. Bourbaki, *Variétés différentielles et analytiques. Fascicule de résultats*, Hermann, 1967,
and the assertion 3.3.1 there is false.

## Main definitions

* `L1`: the Banach space `ℓ¹(ℕ, ℂ)`.
* `fSeries`: the function `f(x) = ∑ₖ 2^{k+1} x_k^{2k+2}` on `ℓ¹`.
* `gSeq`: the map `g(x) = (f((k + 1) x))ₖ`, `ℓ¹ → ℂ^ℕ`.

## Main results

* `ComplexAnalyticOn.exists_bounded`: a complex analytic map into a normed space is bounded on a
  neighbourhood of each point.
* `differentiable_fSeries`, `complexAnalyticOn_fSeries`: `f` is complex differentiable, hence
  complex analytic, on `ℓ¹` ([GN26, Exercise 2.1.10(a)]).
* `not_bddAbove_fSeries`: `f` is unbounded on the unit ball ([GN26, Exercise 2.1.10(b)]).
* `complexAnalyticOn_gSeq`, `exists_not_bddAbove_gSeq`, `not_isVonNBounded_gSeq`: `g` is complex
  analytic, and for every `0`-neighbourhood `U` some coordinate of `g` is unbounded on `U`, so
  `g(U)` is not bounded ([GN26, Exercise 2.1.10(c)]).
* `exists_complexAnalyticOn_not_bounded`: there is a complex analytic map from the Banach space
  `ℓ¹` to the Fréchet space `ℂ^ℕ` which is bounded on no neighbourhood of `0`
  ([GN26, Exercise 2.1.10]).

## Implementation notes

We use `ℕ`-indexed coordinates `x k` (Glöckner–Neeb index from `1`), hence the shift
`k ↦ k + 1`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

/-! ### Normed targets -/

/-- **Complex analytic maps into normed spaces are locally bounded**: they are continuous. -/
theorem ComplexAnalyticOn.exists_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F}
    {U : Set E} (hf : ComplexAnalyticOn f U) (hU : IsOpen U) {x : E} (hx : x ∈ U) :
    ∃ V ∈ 𝓝 x, Bornology.IsBounded (f '' V) := by
  have hc : ContinuousAt f x := (hf.1 x hx).continuousAt (hU.mem_nhds hx)
  refine ⟨f ⁻¹' ball (f x) 1, hc.preimage_mem_nhds (ball_mem_nhds _ one_pos), ?_⟩
  exact isBounded_ball.subset (image_preimage_subset _ _)

/-! ### The function `f` on `ℓ¹` -/

/-- The Banach space `ℓ¹(ℕ, ℂ)`. -/
abbrev L1 : Type := lp (fun _ : ℕ ↦ ℂ) 1

/-- The coordinate `x ↦ x k`, a continuous linear functional of norm `≤ 1`. -/
abbrev coord (k : ℕ) : L1 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 k

@[simp] theorem coord_apply (k : ℕ) (x : L1) : coord k x = x k := rfl

theorem norm_coord_le (k : ℕ) : ‖coord k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    change ‖(x : ∀ _ : ℕ, ℂ) k‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact lp.norm_apply_le_norm one_ne_zero x k

theorem norm_apply_le (x : L1) (k : ℕ) : ‖x k‖ ≤ ‖x‖ := lp.norm_apply_le_norm one_ne_zero x k

/-- The terms `2^{k+1} x_k^{2k+2}`. -/
def term (k : ℕ) (x : L1) : ℂ := 2 ^ (k + 1) * x k ^ (2 * k + 2)

/-- The derivatives of the terms. -/
def term' (k : ℕ) (x : L1) : L1 →L[ℂ] ℂ :=
  (2 ^ (k + 1) * ((2 * k + 2 : ℕ) * x k ^ (2 * k + 1))) • coord k

theorem hasFDerivAt_term (k : ℕ) (x : L1) : HasFDerivAt (term k) (term' k x) x := by
  have h := (((coord k).hasFDerivAt (x := x)).pow (2 * k + 2)).const_mul ((2 : ℂ) ^ (k + 1))
  rw [show 2 * k + 2 - 1 = 2 * k + 1 by omega] at h
  have e : term' k x = (2 : ℂ) ^ (k + 1) • ((2 * k + 2) • coord k x ^ (2 * k + 1)) • coord k := by
    ext v
    simp [term', nsmul_eq_mul]
    ring
  rw [e]
  exact h

theorem norm_term'_le (k : ℕ) (x : L1) :
    ‖term' k x‖ ≤ 2 ^ (k + 1) * ((2 * k + 2 : ℕ) * ‖x k‖ ^ (2 * k + 1)) := by
  rw [term', norm_smul]
  refine (mul_le_of_le_one_right (norm_nonneg _) (norm_coord_le k)).trans_eq ?_
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_two, Complex.norm_natCast]

/-- The function `f(x) = ∑ₖ 2^{k+1} x_k^{2k+2}`. -/
def fSeries (x : L1) : ℂ := ∑' k, term k x

/-- The coordinates of an element of `ℓ¹` tend to `0`. -/
theorem tendsto_coord (x : L1) : Tendsto (fun k ↦ ‖x k‖) atTop (𝓝 0) := by
  have h := (lp.memℓp x).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  simpa using h.tendsto_atTop_zero

/-- `(2k + 2) (1/2)^k` is summable. -/
theorem summable_geom_bound : Summable fun k : ℕ ↦ (2 * k + 2 : ℝ) * (1 / 2) ^ k := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 / 2 : ℝ)) (by norm_num)
  have h0 := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  convert (h1.mul_left 2).add (h0.mul_left 2) using 1
  ext k
  simp only [pow_one]
  ring

/-- The bounds for the derivatives near `x₀` are summable. -/
theorem summable_derivBound (x₀ : L1) :
    Summable fun k : ℕ ↦ 2 ^ (k + 1) * ((2 * k + 2 : ℕ) * (‖x₀ k‖ + 1 / 4) ^ (2 * k + 1)) := by
  refine Summable.of_norm_bounded_eventually_nat summable_geom_bound ?_
  have hev := (tendsto_coord x₀).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hev] with k hk
  have hb : ‖x₀ k‖ + 1 / 4 ≤ 1 / 2 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (2 : ℝ) ^ (k + 1) * ((2 * k + 2 : ℕ) * (‖x₀ k‖ + 1 / 4) ^ (2 * k + 1))
      ≤ 2 ^ (k + 1) * ((2 * k + 2 : ℕ) * (1 / 2) ^ (2 * k + 1)) := by gcongr
    _ = (2 * k + 2 : ℝ) * (1 / 2) ^ k := by
        have e1 : ((1 : ℝ) / 2) ^ (2 * k + 1) = (1 / 2) ^ k * (1 / 2) ^ (k + 1) := by
          rw [← pow_add]; congr 1; ring
        have e2 : (2 : ℝ) ^ (k + 1) * (1 / 2) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
        rw [e1]
        push_cast
        linear_combination ((2 * (k : ℝ) + 2) * (1 / 2) ^ k) * e2

/-- The series converges at every point. -/
theorem summable_term (x : L1) : Summable fun k ↦ term k x := by
  refine Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)) ?_
  have hev := (tendsto_coord x).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev] with k hk
  rw [term, norm_mul, norm_pow, norm_pow, Complex.norm_two]
  calc (2 : ℝ) ^ (k + 1) * ‖x k‖ ^ (2 * k + 2) ≤ 2 ^ (k + 1) * (1 / 2) ^ (2 * k + 2) := by
        gcongr
    _ = (1 / 2) ^ (k + 1) := by
        have e1 : ((1 : ℝ) / 2) ^ (2 * k + 2) = (1 / 2) ^ (k + 1) * (1 / 2) ^ (k + 1) := by
          rw [← pow_add]; congr 1; ring
        have e2 : (2 : ℝ) ^ (k + 1) * (1 / 2) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
        rw [e1]
        linear_combination ((1 : ℝ) / 2) ^ (k + 1) * e2
    _ ≤ (1 / 2) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)

/-- **`f` is complex differentiable** on `ℓ¹`: near `x₀` the derivatives of the terms are
bounded by a summable sequence, since the coordinates of `x₀` tend to `0`. -/
theorem differentiable_fSeries : Differentiable ℂ fSeries := by
  intro x₀
  have hs : x₀ ∈ ball x₀ (1 / 4) := mem_ball_self (by norm_num)
  refine (hasFDerivAt_tsum_of_isPreconnected (summable_derivBound x₀) isOpen_ball
    (convex_ball x₀ _).isPreconnected (fun k x _ ↦ hasFDerivAt_term k x) (fun k x hx ↦ ?_) hs
    (summable_term x₀) hs).differentiableAt
  refine (norm_term'_le k x).trans ?_
  have hxk : ‖x k‖ ≤ ‖x₀ k‖ + 1 / 4 := by
    have h1 : ‖x k - x₀ k‖ ≤ ‖x - x₀‖ := by
      simpa using norm_apply_le (x - x₀) k
    have h2 : ‖x - x₀‖ < 1 / 4 := mem_ball_iff_norm.mp hx
    have h3 := norm_le_insert' (x k) (x₀ k)
    linarith [norm_sub_rev (x k) (x₀ k)]
  gcongr

/-- `f` is complex analytic on `ℓ¹` ([GN26, Exercise 2.1.10(a)]). -/
theorem complexAnalyticOn_fSeries : ComplexAnalyticOn fSeries univ :=
  differentiable_fSeries.differentiableOn.complexAnalyticOn isOpen_univ

/-- `f(r eₖ) = 2^{k+1} r^{2k+2}`. -/
theorem fSeries_single (k : ℕ) (r : ℂ) :
    fSeries (lp.single 1 k r) = 2 ^ (k + 1) * r ^ (2 * k + 2) := by
  rw [fSeries, tsum_eq_single k]
  · simp [term]
  · intro j hj
    simp [term, hj]

/-- **`f` is unbounded on the unit ball** ([GN26, Exercise 2.1.10(b)], at `x = 0`). -/
theorem not_bddAbove_fSeries : ¬ BddAbove ((fun x ↦ ‖fSeries x‖) '' ball 0 1) := by
  rintro ⟨M, hM⟩
  -- `(9/8)^{k+1} → ∞`
  obtain ⟨k, hk⟩ := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 9 / 8)).eventually
    (eventually_gt_atTop M) |>.exists_forall_of_atTop
  have hmem : lp.single 1 k (3 / 4 : ℂ) ∈ ball (0 : L1) 1 := by
    rw [mem_ball_zero_iff, lp.norm_single (by norm_num)]
    norm_num
  have := hM ⟨_, hmem, rfl⟩
  simp only at this
  rw [fSeries_single, norm_mul, norm_pow, norm_pow, Complex.norm_two] at this
  have h98 : (2 : ℝ) ^ (k + 1) * ‖(3 / 4 : ℂ)‖ ^ (2 * k + 2) = (9 / 8) ^ (k + 1) := by
    rw [show ‖(3 / 4 : ℂ)‖ = 3 / 4 by norm_num, show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul,
      ← mul_pow]
    norm_num
  rw [h98] at this
  linarith [hk (k + 1) (Nat.le_succ k)]

/-! ### The map `g : ℓ¹ → ℂ^ℕ` -/

/-- `g(x) = (f((k + 1) x))ₖ`. -/
def gSeq (x : L1) : ℕ → ℂ := fun k ↦ fSeries (((k : ℂ) + 1) • x)

/-- The coordinates of `g` are complex analytic. -/
theorem complexAnalyticOn_gSeq_apply (k : ℕ) :
    ComplexAnalyticOn (fun x ↦ gSeq x k) univ := by
  have hs : Differentiable ℂ fun x : L1 ↦ ((k : ℂ) + 1) • x := by fun_prop
  change ComplexAnalyticOn (fSeries ∘ fun x : L1 ↦ ((k : ℂ) + 1) • x) univ
  exact (differentiable_fSeries.comp hs).differentiableOn.complexAnalyticOn isOpen_univ

/-- **`g` is complex analytic** ([GN26, Exercise 2.1.10(c)]): its coordinates are, and
`ℂ^ℕ` carries the product topology. -/
theorem complexAnalyticOn_gSeq : ComplexAnalyticOn gSeq univ := by
  have hhol : ∀ k, HolomorphicOn (fun x ↦ gSeq x k) univ := fun k ↦
    (complexAnalyticOn_iff_holomorphicOn isOpen_univ).1 (complexAnalyticOn_gSeq_apply k)
  have hd : ∀ x v, HasDirDerivAt gSeq x v (fun k ↦ dMB (fun x ↦ gSeq x k) (x, v)) :=
    fun x v ↦ tendsto_pi_nhds.2 fun k ↦
      ((hhol k).1 1).2.1 x (mem_univ x) v |>.congr fun _ ↦ rfl
  refine (complexAnalyticOn_iff_holomorphicOn isOpen_univ).2 ⟨fun n ↦ ?_, fun x _ c h ↦ ?_⟩
  · exact contDiffMBOn_pi isOpen_univ fun k ↦ (hhol k).1 n
  · rw [(hd x (c • h)).dMB_eq, (hd x h).dMB_eq]
    funext k
    exact (hhol k).2 x (mem_univ x) c h

/-- **`g` is bounded on no neighbourhood of `0`**: for every `0`-neighbourhood `U` some coordinate
of `g` is unbounded on `U` ([GN26, Exercise 2.1.10(c)]). -/
theorem exists_not_bddAbove_gSeq {U : Set L1} (hU : U ∈ 𝓝 0) :
    ∃ k, ¬ BddAbove ((fun x ↦ ‖gSeq x k‖) '' U) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / δ)
  refine ⟨k, fun ⟨M, hM⟩ ↦ not_bddAbove_fSeries ⟨M, ?_⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set x : L1 := ((k : ℂ) + 1)⁻¹ • y with hx
  have hne : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hxy : ((k : ℂ) + 1) • x = y := by rw [hx, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hxU : x ∈ U := by
    refine hball (mem_ball_zero_iff.mpr ?_)
    rw [hx, norm_smul, norm_inv, show ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 by norm_cast]
    have hy1 : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    rw [inv_mul_lt_iff₀ hk1]
    have : 1 < δ * ((k : ℝ) + 1) := by
      rw [div_lt_iff₀ hδ] at hk
      nlinarith
    linarith
  have := hM ⟨x, hxU, rfl⟩
  simpa [gSeq, hxy] using this

/-- `g(U)` is not von Neumann bounded for any `0`-neighbourhood `U`. -/
theorem not_isVonNBounded_gSeq {U : Set L1} (hU : U ∈ 𝓝 0) :
    ¬ Bornology.IsVonNBounded ℂ (gSeq '' U) := by
  intro hb
  obtain ⟨k, hk⟩ := exists_not_bddAbove_gSeq hU
  have hbk := hb.image (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ℕ ↦ ℂ) k)
  rw [NormedSpace.isVonNBounded_iff] at hbk
  obtain ⟨C, hC⟩ := hbk.exists_norm_le
  refine hk ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hC _ ⟨gSeq x, ⟨x, hx, rfl⟩, rfl⟩

/-- **A complex analytic map that is not locally bounded** ([GN26, Exercise 2.1.10]):
a complex analytic map from the Banach space `ℓ¹` to the Fréchet space `ℂ^ℕ` whose image of every
neighbourhood of `0` is unbounded. -/
theorem exists_complexAnalyticOn_not_bounded :
    ∃ g : L1 → (ℕ → ℂ), ComplexAnalyticOn g univ ∧
      ∀ U ∈ 𝓝 (0 : L1), ¬ Bornology.IsVonNBounded ℂ (g '' U) :=
  ⟨gSeq, complexAnalyticOn_gSeq, fun _ hU ↦ not_isVonNBounded_gSeq hU⟩

end LocallyConvex.Analysis.Counterexamples

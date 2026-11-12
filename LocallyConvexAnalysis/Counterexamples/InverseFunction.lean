/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.Rules
public import LocallyConvexAnalysis.MappingSpace.CkSuperposition
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# The inverse function theorem fails in Fréchet spaces

In Banach spaces, a map `f : E → E` strictly differentiable at `a` with derivative the identity
(for instance, `f` is `C¹` near `a` with `f'(a) = id`) maps neighbourhoods of `a` onto
neighbourhoods of `f(a)` (the inverse function theorem; Mathlib's
`HasStrictFDerivAt.map_nhds_eq_of_equiv`). We formalize R. S. Hamilton's counterexample in
Fréchet spaces (*The inverse function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982),
Counterexample 5.5.1, pp. 121–122).

Hamilton considers `P(f) = f - x f f'` on `C^∞[-1, 1]`: `P` is smooth, `P(0) = 0` and
`dP(0) = id`, but the image of `P` contains none of the functions `1/n + xⁿ/n!` (`n ≥ 2`), which
tend to `0`. His proof only looks at Taylor coefficients at `0`, and we formalize it on the space
of formal power series `ℝ[[x]] ≅ ℝ^ℕ`, a Fréchet space with the topology of coefficientwise
convergence. If `f = ∑ aₖ xᵏ`, then the coefficients of `P(f)` are
`P(a)ₖ = aₖ - ∑_{j ≤ k} j a_{k-j} aⱼ`. `P` is smooth (each coefficient is a polynomial in
finitely many coefficients), `P(0) = 0`, `dP(0) = id`, and `gₙ = (1/n, 0, …, 0, 1, 0, …)` (with
`1` in place `n`) tends to `0` in `ℝ^ℕ` but is not in the image of `P` for `n ≥ 2`: if
`P(a) = gₙ`, then `a₀ = 1/n`, then inductively `(1 - k/n) aₖ = 0`, so `aₖ = 0` for `0 < k < n`,
and finally the coefficient of `xⁿ` of `P(a)` is `(1 - n/n) aₙ = 0 ≠ 1`. (Hamilton needs the
factor `1/n!` in `xⁿ/n!` for convergence in `C^∞[-1, 1]`; in `ℝ^ℕ`, `eₙ → 0` already.)

What goes wrong: `dP(1/n) xᵏ = (1 - k/n) xᵏ`, so `dP` is not invertible at points arbitrarily
close to `0`, and in a Fréchet space this is compatible with `dP(0) = id`.

## Main definitions

* `gradP`: the map `P` on coefficients, `P(a)ₖ = aₖ - ∑_{j ≤ k} j a_{k-j} aⱼ`.
* `gSeqN`: the sequence `gₙ = (1/n) e₀ + eₙ` in `ℝ^ℕ`.

## Main results

* `image_mem_nhds_of_hasStrictFDerivAt`: **in Banach spaces**, a map strictly differentiable at
  `a` with derivative the identity maps neighbourhoods of `a` onto neighbourhoods of `f(a)`.
* `smoothMBOn_gradP`, `gradP_zero`, `hasDirDerivAt_gradP_zero`: `P` is smooth on `ℝ^ℕ`,
  `P(0) = 0` and `dP(0) = id`.
* `tendsto_gSeqN`, `gSeqN_not_mem_range`: `gₙ → 0` in `ℝ^ℕ`, and `gₙ` is not in the image of `P`
  for `n ≥ 2` ([Ham82, Counterexample 5.5.1]).
* `exists_smooth_not_open`: **the inverse function theorem fails on the Fréchet space `ℝ^ℕ`**
  ([Ham82, Counterexample 5.5.1]): there is a smooth `P` with `P(0) = 0` and `dP(0) = id` whose
  image is not a neighbourhood of `0`.

## References

* [R. S. Hamilton, *The inverse function theorem of Nash and Moser*][Ham82]
-/

@[expose] public section

open Set Filter Finset
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

/-! ### Banach spaces -/

/-- **Inverse function theorem in Banach spaces**: a map strictly differentiable at `a` with
derivative the identity maps neighbourhoods of `a` onto neighbourhoods of `f(a)`. -/
theorem image_mem_nhds_of_hasStrictFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E → E} {a : E}
    (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ E) a) {U : Set E} (hU : U ∈ 𝓝 a) :
    f '' U ∈ 𝓝 (f a) := by
  have h := HasStrictFDerivAt.map_nhds_eq_of_equiv (f' := ContinuousLinearEquiv.refl ℝ E) hf
  rw [← h]
  exact image_mem_map hU

/-! ### Formal power series -/

/-- The coefficients of `P(f) = f - x f f'` for `f = ∑ aₖ xᵏ`:
`P(a)ₖ = aₖ - ∑_{j ≤ k} j a_{k-j} aⱼ`. -/
def gradP (a : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦ a k + ∑ j ∈ range (k + 1), (-(j : ℝ)) • (a (k - j) * a j)

theorem gradP_apply (a : ℕ → ℝ) (k : ℕ) :
    gradP a k = a k - ∑ j ∈ range (k + 1), (j : ℝ) * a (k - j) * a j := by
  simp only [gradP, smul_eq_mul, neg_mul, sum_neg_distrib, mul_assoc]
  ring

/-- `P` is smooth on `ℝ^ℕ`: each coefficient is a polynomial in finitely many coefficients. -/
theorem smoothMBOn_gradP : SmoothMBOn gradP univ := by
  intro n
  refine contDiffMBOn_pi isOpen_univ fun k ↦ ?_
  have hproj : ∀ m, ContDiffMBOn n (fun a : ℕ → ℝ ↦ a m) univ := fun m ↦
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ℕ ↦ ℝ) m).contDiffMBOn n univ
  have hmul : ∀ j, ContDiffMBOn n (fun a : ℕ → ℝ ↦ a (k - j) * a j) univ := fun j ↦
    ContDiffMBOn.bilin (LinearMap.mul ℝ ℝ) (continuous_fst.mul continuous_snd) isOpen_univ
      (hproj (k - j)) (hproj j)
  refine (hproj k).add isOpen_univ (ContDiffMBOn.sum _ isOpen_univ fun j _ ↦ ?_)
  exact (hmul j).clm_comp' ((-(j : ℝ)) • ContinuousLinearMap.id ℝ ℝ) isOpen_univ

theorem gradP_zero : gradP 0 = 0 := by
  funext k
  simp [gradP]

/-- **`dP(0) = id`**. -/
theorem hasDirDerivAt_gradP_zero (h : ℕ → ℝ) : HasDirDerivAt gradP 0 h h := by
  refine tendsto_pi_nhds.2 fun k ↦ ?_
  set S : ℝ := ∑ j ∈ range (k + 1), (j : ℝ) * h (k - j) * h j
  have heq : ∀ t : ℝ, t ≠ 0 → (t⁻¹ • (gradP (0 + t • h) - gradP 0)) k = h k - t * S := by
    intro t ht
    simp only [zero_add, gradP_zero, sub_zero, Pi.smul_apply, smul_eq_mul, gradP_apply]
    rw [show ∑ j ∈ range (k + 1), (j : ℝ) * (t * h (k - j)) * (t * h j) = t ^ 2 * S by
      rw [mul_sum]; refine sum_congr rfl fun j _ ↦ ?_; ring]
    field_simp
  have hlim : Tendsto (fun t : ℝ ↦ h k - t * S) (𝓝[≠] 0) (𝓝 (h k)) := by
    have : Continuous fun t : ℝ ↦ h k - t * S := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun t ht ↦ (heq t ht).symm)

/-- The sequences `gₙ = (1/n) e₀ + eₙ`. -/
def gSeqN (n : ℕ) : ℕ → ℝ := fun k ↦ (if k = 0 then 1 / (n : ℝ) else 0) + if k = n then 1 else 0

/-- `gₙ → 0` in `ℝ^ℕ`. -/
theorem tendsto_gSeqN : Tendsto gSeqN atTop (𝓝 0) := by
  refine tendsto_pi_nhds.2 fun k ↦ ?_
  have h1 : Tendsto (fun n : ℕ ↦ if k = 0 then 1 / (n : ℝ) else 0) atTop (𝓝 0) := by
    split_ifs
    · exact tendsto_one_div_atTop_nhds_zero_nat
    · exact tendsto_const_nhds
  have h2 : ∀ᶠ n : ℕ in atTop, (if k = n then (1 : ℝ) else 0) = 0 := by
    filter_upwards [eventually_gt_atTop k] with n hn
    simp [hn.ne]
  simpa [gSeqN] using h1.add (tendsto_const_nhds.congr' (h2.mono fun _ h ↦ h.symm))

/-- **`gₙ` is not in the image of `P`** for `n ≥ 2` ([Ham82, Counterexample 5.5.1]). -/
theorem gSeqN_not_mem_range {n : ℕ} (hn : 2 ≤ n) : gSeqN n ∉ range gradP := by
  rintro ⟨a, ha⟩
  have hc : ∀ k, gradP a k = gSeqN n k := fun k ↦ congrFun ha k
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  -- `a₀ = 1/n`
  have ha0 : a 0 = 1 / n := by
    have := hc 0
    have hn0' : (0 : ℕ) ≠ n := by omega
    simp only [gradP_apply, zero_add, range_one, sum_singleton, CharP.cast_eq_zero, zero_mul,
      sub_zero, gSeqN, hn0', ↓reduceIte, add_zero] at this
    exact this
  -- the coefficient `k` when `a₁ = … = a_{k-1} = 0`
  have hcoef : ∀ k, 0 < k → (∀ i, 0 < i → i < k → a i = 0) →
      gradP a k = (1 - k / n) * a k := by
    intro k hk hz
    rw [gradP_apply, sum_eq_single k]
    · rw [Nat.sub_self, ha0]
      field_simp
    · intro j hj hjk
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · rw [hz j hj0 (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hj)) hjk), mul_zero]
    · intro h
      exact absurd (mem_range.mpr (Nat.lt_succ_self k)) h
  -- `aₖ = 0` for `0 < k < n`
  have hz : ∀ k, 0 < k → k < n → a k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hkn
      have h1 := hcoef k hk fun i hi hik ↦ ih i hik hi (hik.trans hkn)
      rw [hc k] at h1
      simp only [gSeqN, hk.ne', hkn.ne, ↓reduceIte, add_zero] at h1
      have hne : (1 : ℝ) - k / n ≠ 0 := by
        rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq hn0]
        exact_mod_cast hkn.ne
      exact (mul_eq_zero.mp h1.symm).resolve_left hne
  -- the coefficient `n`
  have h2 := hcoef n (by omega) fun i hi hin ↦ hz i hi hin
  have hn0' : n ≠ 0 := by omega
  rw [hc n, div_self hn0, sub_self, zero_mul] at h2
  simp only [gSeqN, hn0', ↓reduceIte, zero_add] at h2
  exact one_ne_zero h2

/-- **The inverse function theorem fails on the Fréchet space `ℝ^ℕ`** ([Ham82,
Counterexample 5.5.1]): `P` is smooth, `P(0) = 0` and `dP(0) = id`, but the image of `P` is not a
neighbourhood of `0`. -/
theorem exists_smooth_not_open :
    ∃ P : (ℕ → ℝ) → (ℕ → ℝ), SmoothMBOn P univ ∧ P 0 = 0 ∧ (∀ h, HasDirDerivAt P 0 h h) ∧
      range P ∉ 𝓝 0 := by
  refine ⟨gradP, smoothMBOn_gradP, gradP_zero, hasDirDerivAt_gradP_zero, fun hP ↦ ?_⟩
  obtain ⟨n, hn⟩ := ((tendsto_gSeqN.eventually hP).and (eventually_ge_atTop 2)).exists
  exact gSeqN_not_mem_range hn.2 hn.1

end LocallyConvex.Analysis.Counterexamples

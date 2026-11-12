/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.HomogeneousSeries

/-! # Weakly holomorphic maps into Mackey complete spaces

A continuous map `f : U → F` on an open set `U ⊆ ℂ` such that `ℓ ∘ f` is holomorphic for every
continuous functional `ℓ` is complex analytic, provided `F` is Mackey complete
(`CAnalyticOn.of_weak`). The Taylor coefficients are obtained as limits of averages over roots
of unity of the values of `f` on a circle (`exists_coeff_of_weak`): these discrete Cauchy
formulas converge with an error `C_q 2⁻ᴺ` for each continuous seminorm `q`
(`norm_avg_sub_coeff_le`), with the ratio `1/2` independent of `q`, so the approximations are
Mackey–Cauchy. The weak integrals of the project need `C¹` curves under Mackey completeness, and
the circle `θ ↦ f(x + ρ e^{iθ})` is not known to be `C¹` in `F` beforehand; the discrete
averages only use values of `f`.

## Main results

* `avg_rootN_pow`, `norm_avg_sub_coeff_le`: discrete Cauchy formula with aliasing error bound.
* `exists_coeff_of_weak`: the Taylor coefficients lie in `F`.
* `CAnalyticOn.of_weak`: weak holomorphy and continuity imply complex analyticity.
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology Real

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Discrete extraction of Taylor coefficients (scalar) -/

/-- The `N`-th root of unity `e^{2πi/N}`. -/
def rootN (N : ℕ) : ℂ := Complex.exp (2 * π * Complex.I / N)

/-- `N⁻¹ ∑_{i < N} (ωⁱ)ᵐ` is `1` if `N ∣ m` and `0` otherwise. -/
theorem avg_rootN_pow (N : ℕ) (hN : 0 < N) (m : ℕ) :
    (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, (rootN N ^ i) ^ m = if N ∣ m then 1 else 0 := by
  have hω : IsPrimitiveRoot (rootN N) N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have e : ∀ i, (rootN N ^ i) ^ m = (rootN N ^ m) ^ i := fun i ↦ by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [e]
  split_ifs with hd
  · rw [hω.pow_eq_one_iff_dvd m |>.2 hd]
    simp [hN0]
  · have hne : rootN N ^ m ≠ 1 := by rwa [Ne, hω.pow_eq_one_iff_dvd]
    rw [geom_sum_eq hne, ← pow_mul, mul_comm m N, pow_mul, hω.pow_eq_one, one_pow, sub_self,
      zero_div, mul_zero]

/-- **Discrete Cauchy formula with error bound.** Let `φ` be holomorphic on `B(x, ρ)`, continuous
on its closure, with `|φ| ≤ M` on the circle `|z - x| = ρ`, and let `cₙ = (ρ/2)ⁿ φ⁽ⁿ⁾(x)/n!`.
For `j < N`, the average `N⁻¹ ∑_{i < N} ω^{i (N - j)} φ(x + (ρ/2) ωⁱ)` differs from `cⱼ` by at
most `2 M 2⁻ᴺ`: aliasing only involves the coefficients of index `≥ N`. -/
theorem norm_avg_sub_coeff_le {φ : ℂ → ℂ} {x : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hd : DiffContOnCl ℂ φ (ball x ρ)) (hM : ∀ z ∈ sphere x ρ, ‖φ z‖ ≤ M) {j N : ℕ}
    (hjN : j < N) :
    ‖(N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, (rootN N ^ i) ^ (N - j) * φ (x + (ρ / 2 : ℝ) * rootN N ^ i)
      - ((ρ / 2 : ℝ) : ℂ) ^ j * (iteratedDeriv j φ x / j.factorial)‖ ≤
      2 * M * (1 / 2 : ℝ) ^ N := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hjN
  have hω0 : ‖rootN N‖ = 1 := (Complex.isPrimitiveRoot_exp N hN.ne').norm'_eq_one hN.ne'
  have hω1 : ∀ i, ‖rootN N ^ i‖ = 1 := fun i ↦ by rw [norm_pow, hω0, one_pow]
  set c : ℕ → ℂ := fun n ↦ ((ρ / 2 : ℝ) : ℂ) ^ n * (iteratedDeriv n φ x / n.factorial)
  have hc : ∀ n, ‖c n‖ ≤ M * (1 / 2 : ℝ) ^ n := by
    intro n
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hd hM
    have hfac : (0 : ℝ) < n.factorial := by positivity
    simp only [c, norm_mul, norm_pow, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_two, abs_of_pos hρ, Complex.norm_natCast]
    calc (ρ / 2) ^ n * (‖iteratedDeriv n φ x‖ / n.factorial)
        ≤ (ρ / 2) ^ n * (n.factorial * M / ρ ^ n / n.factorial) := by gcongr
      _ = M * (1 / 2 : ℝ) ^ n := by rw [div_pow, div_pow, one_pow]; field_simp
  -- Taylor expansion at the sample points
  have hT : ∀ i, HasSum (fun n ↦ c n * (rootN N ^ i) ^ n)
      (φ (x + (ρ / 2 : ℝ) * rootN N ^ i)) := by
    intro i
    have hz : x + (ρ / 2 : ℝ) * rootN N ^ i ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hω1, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
      linarith
    have := Complex.hasSum_taylorSeries_on_ball hd.differentiableOn hz
    convert this using 1
    funext n
    simp only [c, add_sub_cancel_left, smul_eq_mul, mul_pow]
    field_simp
  set δ : ℕ → ℂ := fun n ↦ if N ∣ (N - j + n) then 1 else 0
  have hS : HasSum (fun n ↦ c n * δ n) ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
      (rootN N ^ i) ^ (N - j) * φ (x + (ρ / 2 : ℝ) * rootN N ^ i)) := by
    have h := (hasSum_sum (s := Finset.range N) fun i _ ↦
      (hT i).mul_left ((rootN N ^ i) ^ (N - j))).mul_left ((N : ℂ)⁻¹)
    convert h using 1
    funext n
    simp only [δ, ← avg_rootN_pow N hN, Finset.mul_sum, pow_add]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  -- the error vanishes below `N`
  set e : ℕ → ℂ := fun n ↦ c n * δ n - (if n = j then c n else 0)
  have he : HasSum e ((N : ℂ)⁻¹ * ∑ i ∈ Finset.range N,
      (rootN N ^ i) ^ (N - j) * φ (x + (ρ / 2 : ℝ) * rootN N ^ i) - c j) :=
    hS.sub (hasSum_ite_eq j (c j) |>.congr_fun fun n ↦ by split_ifs <;> simp_all)
  have he0 : ∀ n < N, e n = 0 := by
    intro n hn
    simp only [e, δ]
    by_cases hnj : n = j
    · subst hnj
      have : N ∣ N - n + n := by rw [Nat.sub_add_cancel hn.le]
      simp [this]
    · have hnd : ¬ N ∣ N - j + n := by
        rintro ⟨k, hk⟩
        rcases k with _ | _ | k
        · omega
        · omega
        · have h2 : N * (k + 1 + 1) = N * k + 2 * N := by ring
          omega
      simp [hnj, hnd]
  have heN : ∀ n, ‖e n‖ ≤ (if n < N then 0 else M * (1 / 2 : ℝ) ^ n) := by
    intro n
    split_ifs with hn
    · rw [he0 n hn, norm_zero]
    · have hjn : n ≠ j := by omega
      simp only [e, hjn, ite_false, sub_zero, norm_mul]
      have hδ : ‖δ n‖ ≤ 1 := by simp only [δ]; split_ifs <;> simp
      calc ‖c n‖ * ‖δ n‖ ≤ M * (1 / 2 : ℝ) ^ n * 1 := by
            gcongr
            · exact (norm_nonneg _).trans (hc n)
            · exact hc n
        _ = _ := mul_one _
  have hg : HasSum (fun n ↦ if n < N then 0 else M * (1 / 2 : ℝ) ^ n)
      (2 * M * (1 / 2 : ℝ) ^ N) := by
    rw [← hasSum_nat_add_iff' N]
    have hsum0 : ∑ i ∈ Finset.range N, (if i < N then (0 : ℝ) else M * (1 / 2 : ℝ) ^ i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by simp [Finset.mem_range.1 hi]
    rw [hsum0, sub_zero]
    have := (hasSum_geometric_two).mul_left (M * (1 / 2 : ℝ) ^ N)
    convert this using 1
    · funext n
      simp only [show ¬ (n + N < N) by omega, ite_false, pow_add]; ring
    · ring
  exact he.norm_le_of_bounded hg heN

/-! ### Weak holomorphy in Mackey complete spaces -/

section Mackey

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [MackeyComplete F]

omit [ContinuousSMul ℂ F] [T2Space F] in
/-- **The Taylor coefficients of a weakly holomorphic map lie in a Mackey complete space.** If
`f` is continuous on `B̄(x, ρ)` and every `ℓ ∘ f` is holomorphic on `B(x, ρ)` and continuous on
its closure, then for each `j` there is `a ∈ F` with `ℓ a = (ℓ ∘ f)⁽ʲ⁾(x) / j!` for all `ℓ`.
The averages over `N`-th roots of unity of `f` on the circle of radius `ρ/2` approach the
coefficient with an error `C_q 2⁻ᴺ` (`norm_avg_sub_coeff_le`); the ratio is independent of `q`,
so they form a Mackey–Cauchy sequence. -/
theorem exists_coeff_of_weak {f : ℂ → F} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ContinuousOn f (closedBall x ρ))
    (hℓ : ∀ ℓ : F →L[ℂ] ℂ, DiffContOnCl ℂ (ℓ ∘ f) (ball x ρ)) (j : ℕ) :
    ∃ a : F, ∀ ℓ : F →L[ℂ] ℂ, ℓ a = iteratedDeriv j (ℓ ∘ f) x / j.factorial := by
  set S : ℕ → F := fun N ↦ (N : ℂ)⁻¹ • ∑ i ∈ Finset.range N,
    (rootN N ^ i) ^ (N - j) • f (x + (ρ / 2 : ℝ) * rootN N ^ i)
  set c : (F →L[ℂ] ℂ) → ℂ := fun ℓ ↦
    ((ρ / 2 : ℝ) : ℂ) ^ j * (iteratedDeriv j (ℓ ∘ f) x / j.factorial)
  have hS : ∀ ℓ : F →L[ℂ] ℂ, ∀ M, (∀ z ∈ sphere x ρ, ‖ℓ (f z)‖ ≤ M) → ∀ N, j < N →
      ‖ℓ (S N) - c ℓ‖ ≤ 2 * M * (1 / 2 : ℝ) ^ N := by
    intro ℓ M hM N hN
    have h := norm_avg_sub_coeff_le hρ (hℓ ℓ) hM hN
    simpa [S, c, map_smul, map_sum, smul_eq_mul] using h
  -- the telescoping series
  set v : ℕ → F := fun k ↦ S (j + (k + 1) + 1) - S (j + k + 1)
  have hv : ∀ q : Seminorm ℂ F, Continuous q → ∃ C, ∀ k, q (v k) ≤ C * (1 / 2 : ℝ) ^ k := by
    intro q hq
    obtain ⟨M, hM⟩ := exists_seminorm_bound_sphere (hc.mono sphere_subset_closedBall) hq
    set M' := max M 0
    refine ⟨4 * M', fun k ↦ seminorm_le_of_forall_clm hq fun ℓ hℓq ↦ ?_⟩
    have hM' : ∀ z ∈ sphere x ρ, ‖ℓ (f z)‖ ≤ M' := fun z hz ↦
      (hℓq _).trans ((hM z hz).trans (le_max_left _ _))
    have h1 := hS ℓ M' hM' (j + (k + 1) + 1) (by omega)
    have h2 := hS ℓ M' hM' (j + k + 1) (by omega)
    have hM0 : 0 ≤ M' := le_max_right _ _
    have hp1 : (1 / 2 : ℝ) ^ (j + (k + 1) + 1) ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hp2 : (1 / 2 : ℝ) ^ (j + k + 1) ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc ‖ℓ (v k)‖ = ‖(ℓ (S (j + (k + 1) + 1)) - c ℓ) - (ℓ (S (j + k + 1)) - c ℓ)‖ := by
          simp only [v, map_sub]; ring_nf
      _ ≤ ‖ℓ (S (j + (k + 1) + 1)) - c ℓ‖ + ‖ℓ (S (j + k + 1)) - c ℓ‖ := norm_sub_le _ _
      _ ≤ 2 * M' * (1 / 2 : ℝ) ^ (j + (k + 1) + 1) + 2 * M' * (1 / 2 : ℝ) ^ (j + k + 1) :=
          add_le_add h1 h2
      _ ≤ 2 * M' * (1 / 2 : ℝ) ^ k + 2 * M' * (1 / 2 : ℝ) ^ k := by gcongr
      _ = 4 * M' * (1 / 2 : ℝ) ^ k := by ring
  obtain ⟨s, hs⟩ := MackeyComplete.exists_hasSum_of_geometric (by norm_num) (by norm_num) hv
  have hlim : Tendsto (fun K ↦ S (j + K + 1)) atTop (𝓝 (s + S (j + 0 + 1))) := by
    have h := hs.tendsto_sum_nat.add_const (S (j + 0 + 1))
    refine h.congr fun K ↦ ?_
    rw [Finset.sum_range_sub (fun k ↦ S (j + k + 1)) K]
    abel
  have hval : ∀ ℓ : F →L[ℂ] ℂ, ℓ (s + S (j + 0 + 1)) = c ℓ := by
    intro ℓ
    obtain ⟨M, hM⟩ := exists_seminorm_bound_sphere (hc.mono sphere_subset_closedBall)
      (q := (normSeminorm ℂ ℂ).comp ℓ.toLinearMap) (continuous_norm.comp ℓ.continuous)
    have h1 : Tendsto (fun K ↦ ℓ (S (j + K + 1))) atTop (𝓝 (ℓ (s + S (j + 0 + 1)))) :=
      (ℓ.continuous.tendsto _).comp hlim
    have h2 : Tendsto (fun K ↦ ℓ (S (j + K + 1))) atTop (𝓝 (c ℓ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : Tendsto (fun K : ℕ ↦ 2 * M * (1 / 2 : ℝ) ^ (j + K + 1)) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).comp (tendsto_add_atTop_nat (j + 1))
        have e : ∀ K : ℕ, j + K + 1 = K + (j + 1) := fun K ↦ by ring
        simpa [Function.comp_def, e] using this.const_mul (2 * M)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun K ↦ norm_nonneg _) fun K ↦ hS ℓ M (fun z hz ↦ by simpa using hM z hz) _ (by omega)
    exact tendsto_nhds_unique h1 h2
  have hr : ((ρ / 2 : ℝ) : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast (half_pos hρ).ne')
  refine ⟨(((ρ / 2 : ℝ) : ℂ) ^ j)⁻¹ • (s + S (j + 0 + 1)), fun ℓ ↦ ?_⟩
  rw [map_smul, hval, smul_eq_mul]
  simp only [c]
  rw [← mul_assoc, inv_mul_cancel₀ hr, one_mul]

omit [ContinuousSMul ℂ F] [T2Space F] in
/-- **Weakly holomorphic continuous maps into Mackey complete spaces are complex analytic.** -/
theorem CAnalyticOn.of_weak {f : ℂ → F} {U : Set ℂ} (hU : IsOpen U) (hc : ContinuousOn f U)
    (hℓ : ∀ ℓ : F →L[ℂ] ℂ, DifferentiableOn ℂ (ℓ ∘ f) U) : CAnalyticOn f U := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  set ρ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  have hsub : closedBall x ρ ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hd : ∀ ℓ : F →L[ℂ] ℂ, DiffContOnCl ℂ (ℓ ∘ f) (ball x ρ) := fun ℓ ↦
    ((hℓ ℓ).mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  choose a ha using exists_coeff_of_weak hρ (hc.mono hsub) hd
  refine ⟨ρ, hρ, ball_subset_closedBall.trans hsub, a, ?_⟩
  have hW : WeakTaylorOn f a x ρ := fun ℓ ↦ ⟨hd ℓ, fun n ↦ ha n ℓ⟩
  exact hW.hasPowerSeriesOnDisc hρ (hc.mono (sphere_subset_closedBall.trans hsub))

end Mackey

end LocallyConvex.Analysis

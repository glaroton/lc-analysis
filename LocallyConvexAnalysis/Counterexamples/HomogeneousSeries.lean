/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.HomogeneousSeries

/-!
# Series of homogeneous polynomials: counterexamples

Two counterexamples in `ℓ²` to the conclusions of `LocallyConvexAnalysis.Analytic.HomogeneousSeries`
when its hypotheses are dropped.

## Main results

* **`E` not Baire** (Bochnak–Siciak II, Counterexample 5.1). On the finitely supported
  sequences with the norm of `ℓ²` (`finSeq`), `∑ (n xₙ)ⁿ` converges everywhere but its sum is
  not continuous at `0` (`not_continuousAt_bsSum`); in particular `finSeq` is not a Baire space
  (`not_baireSpace_finSeq`).
* **`F` not complete, one variable.** In `F = span {eₙ, (zⁿ)ₙ : ‖z‖ < 1} ⊆ ℓ²` (`geomSpan`),
  the power series `∑ zⁿ eₙ` converges on the whole unit disc (`hasPowerSeriesOnDisc_geomFun`),
  but its sum has no complex derivative at `1/2` (`not_hasCDerivAt_geomFun`), so it is not
  complex analytic on the disc (`not_cAnalyticOn_geomFun`). The derivative in `ℓ²` would be
  `∑ n 2^{1-n} eₙ`, whose coordinates are not eventually an exponential sum
  (`not_eventually_affine_eq_expSum`). Hence a disc of convergence need not be a disc of
  analyticity when `F` is incomplete: by `HasPowerSeriesOnDisc.hasCDerivAt_iff`, the derivative
  off the centre exists exactly when the derived series converges in `F`, and here it does
  not. The partial sums of `∑ n 2^{1-n} eₙ` are Mackey–Cauchy in `geomSpan`, so `geomSpan` is
  not Mackey complete (`not_mackeyComplete_geomSpan`): the counterexample shows that Mackey
  completeness of `F` is needed in `complexAnalyticOn_of_tendsto_sum`.

## References

* [J. Bochnak, J. Siciak, *Analytic functions in topological vector-spaces*][BS71b]
-/

@[expose] public section

open Set Filter Function Metric Finset
open scoped Topology Real Pointwise

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Counterexamples in `ℓ²` -/

section Counterexamples

/-- The Hilbert space `ℓ²(ℕ, ℂ)`. -/
local notation "ℓ²" => lp (fun _ : ℕ ↦ ℂ) 2

/-- The `n`-th coordinate functional on `ℓ²`. -/
def coordCLM (n : ℕ) : ℓ² →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ x n
      map_add' := fun x y ↦ by simp
      map_smul' := fun c x ↦ by simp } 1
    (fun x ↦ by rw [one_mul]; exact lp.norm_apply_le_norm (by norm_num) x n)

@[simp] theorem coordCLM_apply (n : ℕ) (x : ℓ²) : coordCLM n x = x n := rfl

/-! #### `E` not Baire (Bochnak–Siciak, Counterexample 5.1) -/

/-- The finitely supported sequences, with the norm of `ℓ²`: a normed space which is not
complete, and not a Baire space (`not_baireSpace_finSeq`). -/
def finSeq : Submodule ℂ ℓ² where
  carrier := {x | ∃ M, ∀ n ≥ M, x n = 0}
  add_mem' := by
    rintro x y ⟨M, hM⟩ ⟨M', hM'⟩
    exact ⟨max M M', fun n hn ↦ by
      simp [hM n (le_of_max_le_left hn), hM' n (le_of_max_le_right hn)]⟩
  zero_mem' := ⟨0, fun n _ ↦ by simp⟩
  smul_mem' := by
    rintro c x ⟨M, hM⟩
    exact ⟨M, fun n hn ↦ by simp [hM n hn]⟩

theorem mem_finSeq {x : ℓ²} : x ∈ finSeq ↔ ∃ M, ∀ n ≥ M, x n = 0 := Iff.rfl

/-- The terms `pₙ (x) = (n xₙ)ⁿ` of Bochnak–Siciak's Counterexample 5.1. -/
def bsTerm (n : ℕ) (x : finSeq) : ℂ := ((n : ℂ) * (x : ℓ²) n) ^ n

theorem isContHomPoly_bsTerm (n : ℕ) : IsContHomPoly ℂ n (bsTerm n) := by
  refine ⟨(ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun _ ↦ (n : ℂ) • (coordCLM n).comp finSeq.subtypeL), fun x ↦ ?_⟩
  simp [bsTerm, Finset.prod_const]

/-- At a finitely supported point only finitely many terms are nonzero. -/
theorem bsTerm_eventually_zero (x : finSeq) : ∃ M, ∀ n ≥ M, bsTerm n x = 0 := by
  obtain ⟨M, hM⟩ := mem_finSeq.1 x.2
  exact ⟨M + 1, fun n hn ↦ by simp [bsTerm, hM n (by omega), show n ≠ 0 by omega]⟩

/-- The series `∑ (n xₙ)ⁿ` converges at every point of `finSeq`. -/
theorem tendsto_bsSum (x : finSeq) :
    ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, bsTerm n x) atTop (𝓝 y) := by
  obtain ⟨M, hM⟩ := bsTerm_eventually_zero x
  refine ⟨∑ n ∈ range M, bsTerm n x, tendsto_atTop_of_eventually_const (i₀ := M) fun N hN ↦ ?_⟩
  rw [← Finset.sum_range_add_sum_Ico _ hN,
    Finset.sum_eq_zero (fun n hn ↦ hM n (Finset.mem_Ico.1 hn).1), add_zero]

/-- **Bochnak–Siciak, Counterexample 5.1.** On the space of finitely supported sequences with
the norm of `ℓ²`, the series of continuous homogeneous polynomials `∑ (n xₙ)ⁿ` converges
everywhere, but its sum is not continuous at `0` (hence not complex analytic). Thus
`continuousAt_zero_of_tendsto_sum` fails without the Baire property. -/
theorem not_continuousAt_bsSum {f : finSeq → ℂ}
    (hf : ∀ x, Tendsto (fun N ↦ ∑ n ∈ range N, bsTerm n x) atTop (𝓝 (f x))) :
    ¬ ContinuousAt f 0 := by
  have hval : ∀ x M, (∀ n ≥ M, bsTerm n x = 0) → f x = ∑ n ∈ range M, bsTerm n x := by
    intro x M hM
    refine tendsto_nhds_unique (hf x)
      (tendsto_atTop_of_eventually_const (i₀ := M) fun N hN ↦ ?_)
    rw [← Finset.sum_range_add_sum_Ico _ hN,
      Finset.sum_eq_zero (fun n hn ↦ hM n (Finset.mem_Ico.1 hn).1), add_zero]
  have h0 : f 0 = 1 := by
    rw [hval 0 1 (fun n hn ↦ by simp [bsTerm, show n ≠ 0 by omega])]
    simp [bsTerm]
  set xm : ℕ → finSeq := fun m ↦ ⟨lp.single 2 m ((2 : ℂ) / m), m + 1, fun n hn ↦ by
    simp [show n ≠ m by omega]⟩
  have hxm : ∀ m, 1 ≤ m → f (xm m) = 1 + 2 ^ m := by
    intro m hm
    have hterm : ∀ n, bsTerm n (xm m) = if n = 0 then 1 else if n = m then 2 ^ m else 0 := by
      intro n
      by_cases hn0 : n = 0
      · subst hn0; simp [bsTerm]
      · by_cases hnm : n = m
        · subst hnm
          have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
          simp [bsTerm, xm, hn0, mul_div_cancel₀ _ this]
        · simp [bsTerm, xm, hn0, hnm]
    rw [hval (xm m) (m + 1) ?_]
    · rw [Finset.sum_range_succ, Finset.sum_eq_single 0]
      · simp [hterm, show m ≠ 0 by omega]
      · intro n hn hn0
        have := Finset.mem_range.1 hn
        simp [hterm, hn0, show n ≠ m by omega]
      · intro h
        exact absurd (Finset.mem_range.2 (by omega)) h
    · intro n hn
      simp [hterm, show n ≠ 0 by omega, show n ≠ m by omega]
  intro hc
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / δ + 1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) < m := by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hδ]
    exact_mod_cast this.le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hd : dist (xm m) 0 < δ := by
    have hcoe : ((xm m : finSeq) : ℓ²) = lp.single 2 m ((2 : ℂ) / m) := rfl
    rw [dist_zero_right, ← Submodule.norm_coe, hcoe, lp.norm_single (by norm_num), norm_div,
      Complex.norm_ofNat, Complex.norm_natCast,
      div_lt_iff₀ hmpos]
    have h2 : 2 / δ < m := by linarith
    rw [div_lt_iff₀ hδ] at h2
    linarith
  have := hδf hd
  rw [hxm m hm1, h0, dist_eq_norm, add_sub_cancel_left, norm_pow, Complex.norm_ofNat] at this
  exact absurd this (not_lt.2 (one_le_pow₀ (by norm_num)))

/-- The space of finitely supported sequences with the norm of `ℓ²` is not a Baire space:
otherwise `continuousAt_zero_of_tendsto_sum` would contradict `not_continuousAt_bsSum`. -/
theorem not_baireSpace_finSeq : ¬ BaireSpace finSeq := by
  intro hB
  choose f hf using tendsto_bsSum
  exact not_continuousAt_bsSum hf
    (continuousAt_zero_of_tendsto_sum isContHomPoly_bsTerm univ_mem fun x _ ↦ hf x)

/-! #### `F` not complete, in one variable -/

theorem memℓp_geom {z : ℂ} (hz : ‖z‖ < 1) : Memℓp (fun n : ℕ ↦ z ^ n) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h : Summable fun n : ℕ ↦ (‖z‖ ^ 2) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith [norm_nonneg z])
  refine h.congr fun n ↦ ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_pow, ← pow_mul, mul_comm]

/-- The vector `(zⁿ)ₙ ∈ ℓ²` for `‖z‖ < 1` (and `0` otherwise). -/
def geomVec (z : ℂ) : ℓ² := if h : ‖z‖ < 1 then ⟨fun n ↦ z ^ n, memℓp_geom h⟩ else 0

theorem geomVec_apply {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) : geomVec z n = z ^ n := by
  simp [geomVec, hz]

/-- The incomplete space `F = span {eₙ, (zⁿ)ₙ : n ∈ ℕ, ‖z‖ < 1} ⊆ ℓ²`. -/
def geomSpan : Submodule ℂ ℓ² :=
  Submodule.span ℂ (Set.range (fun n ↦ lp.single 2 n (1 : ℂ)) ∪ geomVec '' ball 0 1)

/-- The map `z ↦ ∑ zⁿ eₙ` from the unit disc to `geomSpan` (and `0` outside). -/
def geomFun (z : ℂ) : geomSpan :=
  if h : ‖z‖ < 1 then
    ⟨geomVec z, Submodule.subset_span (Or.inr ⟨z, mem_ball_zero_iff.2 h, rfl⟩)⟩
  else 0

/-- The basis vector `eₙ ∈ geomSpan`. -/
def geomCoeff (n : ℕ) : geomSpan :=
  ⟨lp.single 2 n 1, Submodule.subset_span (Or.inl ⟨n, rfl⟩)⟩

theorem coe_geomFun {z : ℂ} (hz : ‖z‖ < 1) : (geomFun z : ℓ²) = geomVec z := by
  simp [geomFun, hz]

/-- The power series `∑ zⁿ eₙ` converges **in `geomSpan`** on the whole unit disc. -/
theorem hasPowerSeriesOnDisc_geomFun : HasPowerSeriesOnDisc geomFun geomCoeff 0 1 := by
  intro z hz
  rw [zero_add]
  have hL : Topology.IsInducing (geomSpan.subtype) := Topology.IsInducing.subtypeVal
  rw [← hL.hasSum_iff]
  convert lp.hasSum_single (E := fun _ : ℕ ↦ ℂ) (p := 2) ENNReal.ofNat_ne_top (geomVec z)
    using 1
  · funext n
    simp [geomCoeff, geomVec_apply hz, ← lp.single_smul]
  · simp [coe_geomFun hz]

/-- Every generator of `geomSpan` has eventually exponential coordinates. -/
theorem exists_pow_of_mem_gen {s : ℓ²}
    (hs : s ∈ Set.range (fun n ↦ lp.single 2 n (1 : ℂ)) ∪ geomVec '' ball 0 1) :
    ∃ μ : ℂ, ∃ K : ℕ, ∀ n > K, s n = μ ^ n := by
  rcases hs with ⟨k, rfl⟩ | ⟨z, hz, rfl⟩
  · exact ⟨0, k, fun n hn ↦ by
      simp [show n ≠ k by omega, show n ≠ 0 by omega]⟩
  · exact ⟨z, 0, fun n _ ↦ geomVec_apply (mem_ball_zero_iff.1 hz) n⟩

/-- The vector with coordinates `n 2^{1-n}` (the derivative of `∑ zⁿ eₙ` at `1/2`) does not lie
in `geomSpan`: its coordinates are not eventually an exponential sum
(`not_eventually_affine_eq_expSum`). -/
theorem not_forall_coord_eq_geomSpan (y : geomSpan) :
    ¬ ∀ n : ℕ, (y : ℓ²) n = n * (1 / 2 : ℂ) ^ (n - 1) := by
  intro hcoord
  obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 y.2
  choose μ K hμK using fun i ↦ exists_pow_of_mem_gen (g i).2
  set KK := ∑ i, K i
  refine not_eventually_affine_eq_expSum m c (fun i ↦ 2 * μ i) (a := 2) (b := 0) (KK + 1)
    two_ne_zero fun n hn ↦ ?_
  have hyn := congrArg (fun v : ℓ² ↦ v n) hg
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at hyn
  rw [hcoord n] at hyn
  have hK : ∀ i, n > K i := fun i ↦
    lt_of_le_of_lt (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (K j)) (Finset.mem_univ i))
      (by omega)
  simp only [fun i ↦ hμK i n (hK i)] at hyn
  have hn1 : 1 ≤ n := by omega
  have e : (2 : ℂ) * n + 0 = 2 ^ n * (n * (1 / 2 : ℂ) ^ (n - 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn1
    simp only [Nat.add_sub_cancel_left, pow_add, pow_one, one_div, inv_pow]
    field_simp
    push_cast
    ring
  rw [e, ← hyn, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Incomplete target, one variable.** The function `z ↦ ∑ zⁿ eₙ` with values in
`geomSpan` has no complex derivative at `1/2`: its derivative in `ℓ²` would be
`∑ n 2^{1-n} eₙ`, which does not lie in `geomSpan` (`not_eventually_affine_eq_expSum`). -/
theorem not_hasCDerivAt_geomFun (y : geomSpan) : ¬ HasCDerivAt geomFun (1 / 2) y := by
  intro h
  refine not_forall_coord_eq_geomSpan y fun n ↦ ?_
  set ℓ := (coordCLM n).comp geomSpan.subtypeL
  have h1 : Tendsto (fun w : ℂ ↦ w⁻¹ • (ℓ (geomFun (1 / 2 + w)) - ℓ (geomFun (1 / 2))))
      (𝓝[≠] 0) (𝓝 (ℓ y)) := by
    refine ((ℓ.continuous.tendsto y).comp h).congr fun w ↦ ?_
    simp only [Function.comp, map_smul, map_sub]
  have h2 : Tendsto (fun w : ℂ ↦ w⁻¹ • ((1 / 2 + w) ^ n - (1 / 2 : ℂ) ^ n)) (𝓝[≠] 0)
      (𝓝 (n * (1 / 2 : ℂ) ^ (n - 1))) := by
    have hd := hasDerivAt_pow n (1 / 2 : ℂ)
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    simpa using hd
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), ‖1 / 2 + w‖ < 1 := by
    have hc : Continuous fun w : ℂ ↦ ‖1 / 2 + w‖ := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  have h3 : (fun w : ℂ ↦ w⁻¹ • (ℓ (geomFun (1 / 2 + w)) - ℓ (geomFun (1 / 2)))) =ᶠ[𝓝[≠] 0]
      fun w : ℂ ↦ w⁻¹ • ((1 / 2 + w) ^ n - (1 / 2 : ℂ) ^ n) := by
    filter_upwards [nhdsWithin_le_nhds hnear] with w hw
    have hh : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
    have e : ∀ z : ℂ, ‖z‖ < 1 → ℓ (geomFun z) = z ^ n := fun z hz ↦ by
      simp only [ℓ, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, coordCLM_apply]
      rw [coe_geomFun hz, geomVec_apply hz]
    rw [e _ hw, e _ hh]
  exact tendsto_nhds_unique (h1.congr' h3) h2

/-- Without completeness of `F` the disc of convergence of a power series need not be a disc of
analyticity: `∑ zⁿ eₙ` converges in `geomSpan` on the unit disc (`hasPowerSeriesOnDisc_geomFun`)
but is not complex analytic there. -/
theorem not_cAnalyticOn_geomFun : ¬ CAnalyticOn geomFun (ball 0 1) := fun h ↦
  not_hasCDerivAt_geomFun _ (h.hasCDerivAt (by norm_num : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1))

/-- **`geomSpan` is not Mackey complete.** The partial sums of `∑ n 2^{1-n} eₙ` are
Mackey–Cauchy in `geomSpan` (the `eₙ` are unit vectors and the coefficients are summable), but
the limit in `ℓ²` is not in `geomSpan` (`not_forall_coord_eq_geomSpan`). So Mackey completeness
of `F` cannot be dropped from `complexAnalyticOn_of_tendsto_sum`, already for `E = ℂ`
(`not_cAnalyticOn_geomFun`). -/
theorem not_mackeyComplete_geomSpan : ¬ MackeyComplete geomSpan := by
  intro hM
  set t : ℕ → ℝ := fun n ↦ n * (1 / 2 : ℝ) ^ (n - 1)
  have ht0 : ∀ n, 0 ≤ t n := fun n ↦ by positivity
  have hts : Summable t := by
    refine ((summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left 2).congr fun n ↦ ?_
    rcases n with _ | n
    · simp [t]
    · simp only [t, Nat.add_sub_cancel, pow_succ]
      push_cast
      ring
  set u : ℕ → geomSpan := fun N ↦ ∑ n ∈ range N, (t n : ℂ) • geomCoeff n
  set r : ℕ → ℝ := fun k ↦ ∑' j, t (j + k) + (1 / 2 : ℝ) ^ k
  have hr0 : ∀ k, 0 < r k := fun k ↦
    add_pos_of_nonneg_of_pos (tsum_nonneg fun j ↦ ht0 _) (by positivity)
  have hr : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_sum_nat_add t).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    rw [zero_add] at h
    exact h
  have hnorm : ∀ n, ‖geomCoeff n‖ = 1 := fun n ↦ by
    rw [← Submodule.norm_coe]
    simp [geomCoeff, lp.norm_single]
  have hdiff : ∀ k l, k ≤ l → ‖u l - u k‖ ≤ r k := by
    intro k l hkl
    have e : u l - u k = ∑ n ∈ Ico k l, (t n : ℂ) • geomCoeff n := by
      simp only [u]
      rw [← Finset.sum_range_add_sum_Ico _ hkl]
      abel
    rw [e]
    calc ‖∑ n ∈ Ico k l, (t n : ℂ) • geomCoeff n‖ ≤ ∑ n ∈ Ico k l, t n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
          rw [norm_smul, hnorm, mul_one, Complex.norm_real, Real.norm_of_nonneg (ht0 n)]
      _ = ∑ j ∈ range (l - k), t (j + k) := by
          rw [Finset.sum_Ico_eq_sum_range]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [add_comm]
      _ ≤ ∑' j, t (j + k) :=
          (hts.comp_injective (add_left_injective k)).sum_le_tsum _ fun j _ ↦ ht0 _
      _ ≤ r k := le_add_of_nonneg_right (by positivity)
  have hB : Bornology.IsVonNBounded ℝ (closedBall (0 : geomSpan) 1) :=
    (NormedSpace.isVonNBounded_iff ℝ).2 isBounded_closedBall
  obtain ⟨y, hy⟩ := hM.exists_tendsto u (closedBall 0 1) r hB hr fun k l hkl ↦ by
    refine ⟨(r k)⁻¹ • (u l - u k), ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hr0 k).le)]
      exact inv_mul_le_one_of_le₀ (hdiff k l hkl) (hr0 k).le
    · change r k • ((r k)⁻¹ • (u l - u k)) = u l - u k
      rw [smul_smul, mul_inv_cancel₀ (hr0 k).ne', one_smul]
  refine not_forall_coord_eq_geomSpan y fun n ↦ ?_
  set ℓ := (coordCLM n).comp geomSpan.subtypeL
  have hcoord : ∀ N, n < N → ℓ (u N) = t n := by
    intro N hN
    simp only [ℓ, u, map_sum, map_smul, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, coordCLM_apply, geomCoeff, lp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single n]
    · simp
    · intro m _ hmn
      simp [Ne.symm hmn]
    · intro hn
      exact absurd (Finset.mem_range.2 hN) hn
  have hlim : Tendsto (fun N ↦ ℓ (u N)) atTop (𝓝 (t n : ℂ)) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n + 1, fun N hN ↦ (hcoord N (by omega)).symm⟩)
  have := tendsto_nhds_unique ((ℓ.continuous.tendsto y).comp hy) hlim
  simp only [ℓ, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    coordCLM_apply] at this
  rw [this]
  simp [t]

end Counterexamples

end LocallyConvex.Analysis

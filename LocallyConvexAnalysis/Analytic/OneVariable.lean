/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.Integral.FundamentalTheorem
public import LocallyConvexAnalysis.Calculus.MBFrechet
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Complex analytic maps of one variable with values in a locally convex space

[GN26, §2.1, Lemma 2.1.1] to
Lemma 2.1.10, for maps `f : U → F`, `U ⊆ ℂ` open, with values in a complex locally convex space
`F` which is **not assumed to be complete in any sense** (sequentially, Mackey, …).

GN's Proposition 2.1.6 assumes `F` Mackey complete, and their proofs of Corollaries 2.1.8 and
2.1.9 for general `F` pass through a completion `F̃`. Here no completion is used. Two devices
replace it:

* every sum or integral is *given* as an element of `F` (a value of `f`, a coefficient, a
  derivative), and convergence is checked seminorm by seminorm against a summable majorant
  (`tendsto_iff_hasSum_of_dominated`, `hasSum_of_tendsto_of_dominated`);
* estimates are transferred from scalar complex analysis through Hahn–Banach
  (`seminorm_le_of_forall_clm`): `q v = sup {‖ℓ v‖ : ℓ continuous, ‖ℓ‖ ≤ q}` for a continuous
  `ℂ`-seminorm `q`.

## Main definitions

* `HasPowerSeriesOnDisc f a z₀ r`: `f (z₀ + z) = ∑ zⁿ • aₙ` in `F` for `‖z‖ < r` (GN (2.7)).
* `HasCDerivAt f x y`, `cDeriv f x`: the complex derivative `lim_{w → 0} w⁻¹ (f (x + w) - f x)`
  (GN (2.1)).
* `CAnalyticOn f U`: `f` is locally a power series around each point of `U` (GN Definition
  2.1.2 and Remark 2.1.3 with `E = ℂ`).

## Main results (no completeness of `F` anywhere)

* `HasPowerSeriesOnDisc.exists_bound`: `ρⁿ q(aₙ)` is bounded for `ρ < r` (GN footnote to
  Remark 2.1.3); `HasPowerSeriesOnDisc.continuousOn`: power series are continuous on their disc.
* `HasPowerSeriesOnDisc.hasCDerivAt_iff`: termwise differentiation. At a point of the disc, the
  complex derivative exists iff the differentiated series converges in `F`, and then they agree
  (GN Lemma 2.1.10).
* `CAnalyticOn.cAnalyticOn_cDeriv`, `CAnalyticOn.hasPowerSeriesOnDisc_cDeriv`: derivatives of
  complex analytic maps are complex analytic, by termwise differentiation (GN Lemma 2.1.10).
* `CAnalyticOn.iteratedDMB_eq`, `CAnalyticOn.dMB_eq`, `CAnalyticOn.smoothMBOn`: complex analytic
  maps are Michal–Bastiani smooth (as maps of a real variable), with
  `d⁽ʲ⁾f(x, w₁, …, wⱼ) = w₁ ⋯ wⱼ • f⁽ʲ⁾(x)` (GN Lemma 2.1.1, (2.3)–(2.4)).
* `HasPowerSeriesOnDisc.coeff_unique`, `CAnalyticOn.coeff_eq`: the coefficients are unique and
  equal to `f⁽ⁿ⁾(x)/n!` (GN Corollary 2.1.8 (a)).
* `CAnalyticOn.hasPowerSeriesOnDisc`: the Taylor series converges in `F` on every open disc whose
  closure lies in `U` (GN Corollary 2.1.8 (b)).
* `HasPowerSeriesOnDisc.hasWeakIntegral`: Cauchy's formula for the coefficients as a weak
  integral in `F`, `∫₀^{2π} e^{-int} f(x + ρ e^{it}) dt = 2π ρⁿ aₙ` (GN Definition 2.1.4,
  (2.11) for `z = x`).
* `HasPowerSeriesOnDisc.seminorm_coeff_le`, `CAnalyticOn.seminorm_iterate_cDeriv_le`: Cauchy
  estimates (GN (2.12)).
* `cAnalyticOn_iff_smoothMBOn`: `f` is complex analytic iff it is Michal–Bastiani smooth with
  complex linear differentials `df(x, ·)` (GN Corollary 2.1.9, (b) ⇔ (c)).
* `CAnalyticOn.eqOn_of_preconnected_of_eventuallyEq`: identity theorem.

## Implementation notes

* Complex local convexity is expressed by `PolynormableSpace ℂ F` (the topology is given by the
  continuous `ℂ`-seminorms). When `F` is a real locally convex space via `IsScalarTower ℝ ℂ F`,
  this is automatic (`polynormableSpace_complex`); the statements involving the real
  Michal–Bastiani calculus and weak integrals of `LocallyConvex.Analysis` use the latter setting.
* `HasPowerSeriesOnDisc` uses unconditional sums (`HasSum`); GN's pointwise limits of partial
  sums give the same notion on open discs (`hasPowerSeriesOnDisc_of_tendsto`).
* For a single power series on a disc, the derivative at points other than the center is only
  known to exist when the differentiated series converges in `F`. For `CAnalyticOn` maps, which
  have expansions around every point, it always exists.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology Real

noncomputable section

namespace LocallyConvex.Analysis

universe v

/-! ### Complex seminorms and complex functionals -/

section Seminorms

variable {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]

open scoped ComplexOrder in
/-- A complex vector space which is locally convex as a real space is polynormable over `ℂ`:
its topology is defined by the continuous `ℂ`-seminorms. -/
theorem polynormableSpace_complex [Module ℝ F] [IsScalarTower ℝ ℂ F]
    [LocallyConvexSpace ℝ F] : PolynormableSpace ℂ F := by
  have : ContinuousSMul ℝ F := IsScalarTower.continuousSMul ℂ
  have : LocallyConvexSpace ℂ F := by
    refine (locallyConvexSpace_iff_exists_convex_subset_zero ℂ F).2 fun U hU ↦ ?_
    obtain ⟨S, hS, hSc, hSU⟩ :=
      (locallyConvexSpace_iff_exists_convex_subset_zero ℝ F).1 ‹_› U hU
    exact ⟨S, hS, convex_RCLike_iff_convex_real.2 hSc, hSU⟩
  exact LocallyConvexSpace.toPolynormableSpace

variable [PolynormableSpace ℂ F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- Convergence in `F` is convergence for every continuous `ℂ`-seminorm. -/
theorem tendsto_nhds_iff_seminorm {ι : Type*} {l : Filter ι} {u : ι → F} {y : F} :
    Tendsto u l (𝓝 y) ↔
      ∀ q : Seminorm ℂ F, Continuous q → ∀ ε > 0, ∀ᶠ i in l, q (u i - y) < ε := by
  rw [(PolynormableSpace.withSeminorms ℂ F).tendsto_nhds]
  exact ⟨fun h q hq ↦ h ⟨q, hq⟩, fun h q ↦ h q.1 q.2⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- Hahn–Banach: a continuous `ℂ`-seminorm is the supremum of the moduli of the continuous
`ℂ`-linear functionals it dominates. -/
theorem seminorm_le_of_forall_clm {q : Seminorm ℂ F} (hq : Continuous q) {v : F} {B : ℝ}
    (h : ∀ ℓ : F →L[ℂ] ℂ, (∀ w, ‖ℓ w‖ ≤ q w) → ‖ℓ v‖ ≤ B) : q v ≤ B := by
  let f : F →ₗ.[ℂ] ℂ := LinearPMap.mkSpanSingleton' v ((q v : ℝ) : ℂ) (by
    intro c hc
    rcases smul_eq_zero.1 hc with rfl | rfl
    · simp
    · simp)
  obtain ⟨g, hg, hgq⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm f.domain f.toFun hq (by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have : f ⟨c • v, hx⟩ = c • ((q v : ℝ) : ℂ) := LinearPMap.mkSpanSingleton'_apply _ _ _ _ _
      change ‖f ⟨c • v, hx⟩‖ ≤ q (c • v)
      rw [this, map_smul_eq_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg q v)])
  have hv : g v = ((q v : ℝ) : ℂ) := by
    rw [hg ⟨v, Submodule.mem_span_singleton_self v⟩]
    exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _
  have := h g hgq
  rwa [hv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg q v)] at this

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- A seminorm of the sum of a series is bounded by any summable majorant of the seminorms
of its terms. No completeness is involved: the sum is given. -/
theorem seminorm_le_of_hasSum {q : Seminorm ℂ F} (hq : Continuous q) {u : ℕ → F} {S : F}
    (hS : HasSum u S) {M : ℕ → ℝ} (hM : Summable M) (hle : ∀ n, q (u n) ≤ M n) :
    q S ≤ ∑' n, M n := by
  refine le_of_tendsto' ((hq.tendsto S).comp hS.tendsto_sum_nat) fun N ↦ ?_
  calc q (∑ i ∈ Finset.range N, u i) ≤ ∑ i ∈ Finset.range N, q (u i) :=
        Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
    _ ≤ ∑ i ∈ Finset.range N, M i := Finset.sum_le_sum fun i _ ↦ hle i
    _ ≤ ∑' n, M n := hM.sum_le_tsum _ fun i _ ↦ (apply_nonneg q _).trans (hle i)

omit [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- Tail estimate: `q (S - ∑_{i < N} uᵢ) ≤ ∑_{n ≥ N} Mₙ`. -/
theorem seminorm_sub_sum_le_of_hasSum {q : Seminorm ℂ F} (hq : Continuous q) {u : ℕ → F}
    {S : F} (hS : HasSum u S) {M : ℕ → ℝ} (hM : Summable M) (hle : ∀ n, q (u n) ≤ M n)
    (N : ℕ) : q (S - ∑ i ∈ Finset.range N, u i) ≤ ∑' n, M (n + N) :=
  seminorm_le_of_hasSum hq ((hasSum_nat_add_iff' N).2 hS) ((summable_nat_add_iff N).2 hM)
    fun n ↦ hle (n + N)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- If the partial sums of a series converge and, for every continuous seminorm `q`, the terms
are dominated by a summable real sequence, then the series converges unconditionally. -/
theorem hasSum_of_tendsto_of_dominated {u : ℕ → F} {y : F}
    (hlim : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, u i) atTop (𝓝 y))
    (hM : ∀ q : Seminorm ℂ F, Continuous q → ∃ M : ℕ → ℝ, Summable M ∧ ∀ n, q (u n) ≤ M n) :
    HasSum u y := by
  change Tendsto (fun s : Finset ℕ ↦ ∑ b ∈ s, u b) atTop (𝓝 y)
  refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
  obtain ⟨M, hMs, hMb⟩ := hM q hq
  have hM0 : ∀ n, 0 ≤ M n := fun n ↦ (apply_nonneg q _).trans (hMb n)
  obtain ⟨N, hN₁, hN₂⟩ : ∃ N, ∑' k, M (k + N) < ε / 2 ∧
      q (∑ i ∈ Finset.range N, u i - y) < ε / 2 := by
    have h1 := (tendsto_sum_nat_add M).eventually (gt_mem_nhds (half_pos hε))
    have h2 := (tendsto_nhds_iff_seminorm.1 hlim) q hq _ (half_pos hε)
    exact (h1.and h2).exists
  filter_upwards [eventually_ge_atTop (Finset.range N)] with s hs
  obtain ⟨K, hK⟩ : ∃ K, s ⊆ Finset.range K :=
    ⟨s.sup id + 1, fun n hn ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))⟩
  have hsplit : ∑ b ∈ s, u b - y =
      (∑ i ∈ Finset.range N, u i - y) + ∑ b ∈ s \ Finset.range N, u b := by
    rw [← Finset.sum_sdiff hs]; abel
  have htail : ∑ b ∈ s \ Finset.range N, M b ≤ ∑' k, M (k + N) := by
    calc ∑ b ∈ s \ Finset.range N, M b ≤ ∑ b ∈ Finset.Ico N (max N K), M b := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb ↦ ?_) fun b _ _ ↦ hM0 b
          obtain ⟨hb₁, hb₂⟩ := Finset.mem_sdiff.1 hb
          simp only [Finset.mem_range, not_lt] at hb₂
          exact Finset.mem_Ico.2 ⟨hb₂, lt_max_of_lt_right (Finset.mem_range.1 (hK hb₁))⟩
      _ = ∑ k ∈ Finset.range (max N K - N), M (k + N) := by
          rw [Finset.sum_Ico_eq_sum_range]; simp only [add_comm]
      _ ≤ ∑' k, M (k + N) :=
          ((summable_nat_add_iff N).2 hMs).sum_le_tsum _ fun k _ ↦ hM0 (k + N)
  calc q (∑ b ∈ s, u b - y)
      ≤ q (∑ i ∈ Finset.range N, u i - y) + q (∑ b ∈ s \ Finset.range N, u b) := by
        rw [hsplit]; exact map_add_le_add q _ _
    _ ≤ q (∑ i ∈ Finset.range N, u i - y) + ∑ b ∈ s \ Finset.range N, M b := by
        gcongr
        exact (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans
          (Finset.sum_le_sum fun b _ ↦ hMb b)
    _ < ε := by linarith

omit [ContinuousSMul ℂ F] in
/-- Interchange of a limit `w → 0` with a series, under a domination by a summable majorant
(for every continuous seminorm): `D w = ∑ uₙ(w)` tends to `y` iff `∑ uₙ(0) = y`. This is the
tool for termwise differentiation; both sums are *given* in `F`, and no completeness is used. -/
theorem tendsto_iff_hasSum_of_dominated {D : ℂ → F} {u : ℕ → ℂ → F} {y : F}
    (hu : ∀ n, ContinuousAt (u n) 0)
    (hD : ∀ᶠ w in 𝓝[≠] (0 : ℂ), HasSum (fun n ↦ u n w) (D w))
    (hM : ∀ q : Seminorm ℂ F, Continuous q →
      ∃ M : ℕ → ℝ, Summable M ∧ ∀ᶠ w in 𝓝 (0 : ℂ), ∀ n, q (u n w) ≤ M n) :
    Tendsto D (𝓝[≠] 0) (𝓝 y) ↔ HasSum (fun n ↦ u n 0) y := by
  have hS : ∀ N, Tendsto (fun w ↦ ∑ i ∈ Finset.range N, u i w) (𝓝 0)
      (𝓝 (∑ i ∈ Finset.range N, u i 0)) := fun N ↦ tendsto_finsetSum _ fun i _ ↦ hu i
  constructor
  · intro hlim
    refine hasSum_of_tendsto_of_dominated ?_ fun q hq ↦ ?_
    · refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
      obtain ⟨M, hMs, hMb⟩ := hM q hq
      filter_upwards [(tendsto_sum_nat_add M).eventually (gt_mem_nhds (half_pos hε))] with N hN
      -- `q (S_N(0) - y)` is a limit of `q (S_N(w) - D w) ≤ tail`.
      have hlim' : Tendsto (fun w ↦ q (∑ i ∈ Finset.range N, u i w - D w)) (𝓝[≠] 0)
          (𝓝 (q (∑ i ∈ Finset.range N, u i 0 - y))) :=
        (hq.tendsto _).comp (((hS N).mono_left nhdsWithin_le_nhds).sub hlim)
      have hle : q (∑ i ∈ Finset.range N, u i 0 - y) ≤ ∑' k, M (k + N) := by
        refine le_of_tendsto hlim' ?_
        filter_upwards [hD, nhdsWithin_le_nhds hMb] with w hw hwM
        rw [← map_neg_eq_map, neg_sub]
        exact seminorm_sub_sum_le_of_hasSum hq hw hMs hwM N
      exact hle.trans_lt (by linarith)
    · obtain ⟨M, hMs, hMb⟩ := hM q hq
      exact ⟨M, hMs, hMb.self_of_nhds⟩
  · intro hsum
    refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
    obtain ⟨M, hMs, hMb⟩ := hM q hq
    have h3 : 0 < ε / 3 := by positivity
    obtain ⟨N, hN₁, hN₂⟩ : ∃ N, ∑' k, M (k + N) < ε / 3 ∧
        q (∑ i ∈ Finset.range N, u i 0 - y) < ε / 3 := by
      have h1 := (tendsto_sum_nat_add M).eventually (gt_mem_nhds h3)
      have h2 := (tendsto_nhds_iff_seminorm.1 hsum.tendsto_sum_nat) q hq _ h3
      exact (h1.and h2).exists
    have h4 := (tendsto_nhds_iff_seminorm.1 (hS N)) q hq _ h3
    filter_upwards [hD, nhdsWithin_le_nhds hMb, nhdsWithin_le_nhds h4] with w hw hwM hw4
    have e : D w - y = (D w - ∑ i ∈ Finset.range N, u i w) +
        (∑ i ∈ Finset.range N, u i w - ∑ i ∈ Finset.range N, u i 0) +
        (∑ i ∈ Finset.range N, u i 0 - y) := by abel
    calc q (D w - y) ≤ q (D w - ∑ i ∈ Finset.range N, u i w) +
          q (∑ i ∈ Finset.range N, u i w - ∑ i ∈ Finset.range N, u i 0) +
          q (∑ i ∈ Finset.range N, u i 0 - y) := by
            rw [e]; exact (map_add_le_add q _ _).trans (add_le_add_left (map_add_le_add q _ _) _)
      _ < ε / 3 + ε / 3 + ε / 3 := by
            gcongr
            exact (seminorm_sub_sum_le_of_hasSum hq hw hMs hwM N).trans_lt hN₁
      _ = ε := by ring

end Seminorms

/-! ### Power series and complex derivatives -/

section PowerSeries

variable {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F]

/-- `f` is given on the open disc of radius `r` around `z₀` by the power series with
coefficients `a`: `f (z₀ + z) = ∑ zⁿ • aₙ` for `‖z‖ < r` ([GN26, (2.7)]). The sums are
required to exist *in `F`*: no completeness is assumed. -/
def HasPowerSeriesOnDisc (f : ℂ → F) (a : ℕ → F) (z₀ : ℂ) (r : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ < r → HasSum (fun n ↦ z ^ n • a n) (f (z₀ + z))

/-- `f` has complex derivative `y` at `x`: `w⁻¹ • (f (x + w) - f x) → y` as `w → 0` in `ℂ`
([GN26, (2.1)]). -/
def HasCDerivAt (f : ℂ → F) (x : ℂ) (y : F) : Prop :=
  Tendsto (fun w : ℂ ↦ w⁻¹ • (f (x + w) - f x)) (𝓝[≠] 0) (𝓝 y)

/-- The complex derivative `f'(x)` (junk value where it does not exist). -/
def cDeriv (f : ℂ → F) (x : ℂ) : F :=
  limUnder (𝓝[≠] (0 : ℂ)) fun w : ℂ ↦ w⁻¹ • (f (x + w) - f x)

variable {f : ℂ → F} {a : ℕ → F} {z₀ : ℂ} {r : ℝ}

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- The complex derivative is unique (`F` Hausdorff). -/
theorem HasCDerivAt.cDeriv_eq [T2Space F] {x : ℂ} {y : F} (h : HasCDerivAt f x y) :
    cDeriv f x = y :=
  h.limUnder_eq

/-- Continuity at `x` from the limit along the punctured neighbourhood. -/
theorem continuousAt_of_tendsto_punctured {X : Type*} [TopologicalSpace X] {g : ℂ → X} {x : ℂ}
    (h : Tendsto (fun w : ℂ ↦ g (x + w)) (𝓝[≠] 0) (𝓝 (g x))) : ContinuousAt g x := by
  have h2 : ContinuousAt (fun w : ℂ ↦ g (x + w)) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, add_zero]
    exact h
  have h3 : ContinuousAt (fun z : ℂ ↦ z - x) x := by fun_prop
  have := ContinuousAt.comp (f := fun z : ℂ ↦ z - x) (by simpa using h2) h3
  convert this using 1
  funext z
  simp

omit [PolynormableSpace ℂ F] in
/-- Complex differentiability implies continuity. -/
theorem HasCDerivAt.continuousAt {x : ℂ} {y : F} (h : HasCDerivAt f x y) :
    ContinuousAt f x := by
  have h1 : Tendsto (fun w : ℂ ↦ f x + w • (w⁻¹ • (f (x + w) - f x))) (𝓝[≠] 0)
      (𝓝 (f x + (0 : ℂ) • y)) :=
    tendsto_const_nhds.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul h)
  rw [zero_smul, add_zero] at h1
  refine continuousAt_of_tendsto_punctured (h1.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
  rw [smul_smul, mul_inv_cancel₀ hw, one_smul, add_sub_cancel]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- If `ρⁿ aₙ → 0` (e.g. if `∑ ρⁿ aₙ` converges), then for each continuous seminorm `q` the
numbers `ρⁿ q(aₙ)` are bounded ([GN26, footnote to Remark 2.1.3]). -/
theorem exists_bound_of_tendsto {q : Seminorm ℂ F} (hq : Continuous q) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ht : Tendsto (fun n ↦ (ρ : ℂ) ^ n • a n) atTop (𝓝 0)) :
    ∃ C, 0 ≤ C ∧ ∀ n, ρ ^ n * q (a n) ≤ C := by
  have ht := (hq.tendsto 0).comp ht
  rw [map_zero] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨C, ?_, fun n ↦ ?_⟩
  · exact (apply_nonneg q _).trans (hC ⟨0, rfl⟩)
  · have := hC ⟨n, rfl⟩
    simpa [map_smul_eq_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
      using this

omit [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- For `0 ≤ ρ < r`, the numbers `ρⁿ q(aₙ)` are bounded ([GN26, footnote to Remark 2.1.3]). -/
theorem HasPowerSeriesOnDisc.exists_bound (hf : HasPowerSeriesOnDisc f a z₀ r)
    {q : Seminorm ℂ F} (hq : Continuous q) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r) :
    ∃ C, 0 ≤ C ∧ ∀ n, ρ ^ n * q (a n) ≤ C :=
  exists_bound_of_tendsto hq hρ
    (hf ρ (by simpa [Complex.norm_real, abs_of_nonneg hρ])).summable.tendsto_atTop_zero

omit [ContinuousSMul ℂ F] in
/-- Glöckner–Neeb write the series (2.6)–(2.7) as pointwise limits of partial sums. On the
open disc this is equivalent to unconditional summability (`HasSum`), which is the definition
of `HasPowerSeriesOnDisc`. -/
theorem hasPowerSeriesOnDisc_of_tendsto
    (h : ∀ z : ℂ, ‖z‖ < r →
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N, z ^ n • a n) atTop (𝓝 (f (z₀ + z)))) :
    HasPowerSeriesOnDisc f a z₀ r := by
  intro z hz
  refine hasSum_of_tendsto_of_dominated (h z hz) fun q hq ↦ ?_
  set ρ := (‖z‖ + r) / 2
  have hzρ : ‖z‖ < ρ := by simp only [ρ]; linarith
  have hρr : ρ < r := by simp only [ρ]; linarith
  have hρ : 0 < ρ := (norm_nonneg z).trans_lt hzρ
  clear_value ρ
  have ht : Tendsto (fun n ↦ (ρ : ℂ) ^ n • a n) atTop (𝓝 0) := by
    have h1 := h ρ (by simpa [Complex.norm_real, abs_of_pos hρ])
    have h2 := (h1.comp (tendsto_add_atTop_nat 1)).sub h1
    rw [sub_self] at h2
    refine h2.congr fun n ↦ ?_
    simp [Finset.sum_range_succ]
  obtain ⟨C, -, hC⟩ := exists_bound_of_tendsto hq hρ.le ht
  refine ⟨fun n ↦ C * (‖z‖ / ρ) ^ n, (summable_geometric_of_lt_one (by positivity)
    ((div_lt_one hρ).2 hzρ)).mul_left C, fun n ↦ ?_⟩
  have hqa : q (a n) ≤ C / ρ ^ n := by
    rw [le_div_iff₀ (by positivity), mul_comm]; exact hC n
  rw [map_smul_eq_mul, norm_pow]
  calc ‖z‖ ^ n * q (a n) ≤ ‖z‖ ^ n * (C / ρ ^ n) := by gcongr
    _ = C * (‖z‖ / ρ) ^ n := by rw [div_pow]; ring

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- The value at the center is the constant coefficient. -/
theorem HasPowerSeriesOnDisc.apply_center [T2Space F] (hf : HasPowerSeriesOnDisc f a z₀ r)
    (hr : 0 < r) : f z₀ = a 0 := by
  have h := hf 0 (by simpa using hr)
  rw [add_zero] at h
  refine h.unique ?_
  convert hasSum_single (f := fun n : ℕ ↦ (0 : ℂ) ^ n • a n) 0 fun n hn ↦ by simp [hn]
  simp

private theorem norm_geom_sum₂_le {x y : ℂ} {σ : ℝ} (hx : ‖x‖ ≤ σ) (hy : ‖y‖ ≤ σ) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ n * σ ^ (n - 1) := by
  have hσ : 0 ≤ σ := (norm_nonneg _).trans hx
  calc ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖
      ≤ ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range n, σ ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hin : i + (n - 1 - i) = n - 1 := by
          have := Finset.mem_range.1 hi; omega
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖x‖ ^ i * ‖y‖ ^ (n - 1 - i) ≤ σ ^ i * σ ^ (n - 1 - i) := by gcongr
          _ = σ ^ (n - 1) := by rw [← pow_add, hin]
    _ = n * σ ^ (n - 1) := by simp

/-- The terms `((z + w)ⁿ - zⁿ)/w • aₙ` of a difference quotient of a power series, written as
polynomials in `w` (so that they make sense at `w = 0`, where they become `n zⁿ⁻¹ • aₙ`). -/
def dqTerm (a : ℕ → F) (z : ℂ) (n : ℕ) (w : ℂ) : F :=
  (∑ i ∈ Finset.range n, (z + w) ^ i * z ^ (n - 1 - i)) • a n

omit [PolynormableSpace ℂ F] in
/-- The difference quotients of a power series at an interior point `z₀ + z` are the sums of
the series `∑ dqTerm a z n w`, dominated (for every continuous seminorm) by a summable
sequence, uniformly for small `w`. -/
theorem HasPowerSeriesOnDisc.dqTerm_facts (hf : HasPowerSeriesOnDisc f a z₀ r) {z : ℂ}
    (hz : ‖z‖ < r) :
    (∀ n, ContinuousAt (dqTerm a z n) 0) ∧
    (∀ᶠ w in 𝓝[≠] (0 : ℂ),
      HasSum (fun n ↦ dqTerm a z n w) (w⁻¹ • (f (z₀ + z + w) - f (z₀ + z)))) ∧
    ∀ q : Seminorm ℂ F, Continuous q →
      ∃ M : ℕ → ℝ, Summable M ∧ ∀ᶠ w in 𝓝 (0 : ℂ), ∀ n, q (dqTerm a z n w) ≤ M n := by
  refine ⟨fun n ↦ ?_, ?_, fun q hq ↦ ?_⟩
  · exact ((continuous_finsetSum _ fun i _ ↦ by fun_prop).smul continuous_const).continuousAt
  · have hball : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ < r - ‖z‖ :=
      (continuous_norm.tendsto' (0 : ℂ) 0 norm_zero).eventually (gt_mem_nhds (by linarith))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with w (hw : w ≠ 0) hwr
    have h1 := hf (z + w) ((norm_add_le _ _).trans_lt (by linarith))
    have h2 := ((h1.sub (hf z hz)).const_smul w⁻¹)
    rw [← add_assoc] at h2
    convert h2 using 2 with n
    rw [← sub_smul, smul_smul, dqTerm]
    congr 1
    have := geom_sum₂_mul (z + w) z n
    rw [add_sub_cancel_left] at this
    rw [← this, mul_comm, mul_inv_cancel_right₀ hw]
  · set ρ := (‖z‖ + r) / 2
    set σ := (‖z‖ + ρ) / 2
    have hzρ : ‖z‖ < ρ := by simp only [ρ]; linarith
    have hρr : ρ < r := by simp only [ρ]; linarith
    have hzσ : ‖z‖ < σ := by simp only [σ]; linarith
    have hσρ : σ < ρ := by simp only [σ]; linarith
    have hσ : 0 < σ := (norm_nonneg z).trans_lt hzσ
    have hρ : 0 < ρ := hσ.trans hσρ
    clear_value σ ρ
    obtain ⟨C, hC0, hC⟩ := hf.exists_bound hq hρ.le hρr
    refine ⟨fun n ↦ C / σ * (n * (σ / ρ) ^ n), ?_, ?_⟩
    · refine Summable.mul_left _ ?_
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1
        (r := σ / ρ) (by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; exact
          (div_lt_one hρ).2 hσρ)
    · have hball : ∀ᶠ w in 𝓝 (0 : ℂ), ‖w‖ < σ - ‖z‖ :=
        (continuous_norm.tendsto' (0 : ℂ) 0 norm_zero).eventually (gt_mem_nhds (by linarith))
      filter_upwards [hball] with w hw n
      have hzw : ‖z + w‖ ≤ σ := (norm_add_le _ _).trans (by linarith)
      have hS := norm_geom_sum₂_le hzw hzσ.le n
      have hqa : q (a n) ≤ C / ρ ^ n := by
        rw [le_div_iff₀ (by positivity), mul_comm]; exact hC n
      have hS' : ‖∑ i ∈ Finset.range n, (z + w) ^ i * z ^ (n - 1 - i)‖ ≤ n * σ ^ n / σ := by
        rcases n with _ | n
        · simp
        · rw [mul_div_assoc, pow_succ, mul_div_cancel_right₀ _ hσ.ne']
          simpa using hS
      calc q (dqTerm a z n w)
          = ‖∑ i ∈ Finset.range n, (z + w) ^ i * z ^ (n - 1 - i)‖ * q (a n) :=
            map_smul_eq_mul _ _ _
        _ ≤ (n * σ ^ n / σ) * (C / ρ ^ n) := by gcongr
        _ = C / σ * (n * (σ / ρ) ^ n) := by rw [div_pow]; ring

/-- **Termwise differentiation** ([GN26, Lemma 2.1.10], without completeness): if
`f (z₀ + z) = ∑ zⁿ • aₙ` on the disc of radius `r`, then at each point `z₀ + z` of the disc,
`f` has complex derivative `y` **iff** the differentiated series `∑ n zⁿ⁻¹ • aₙ` converges to
`y` in `F`. In an incomplete space neither needs to exist (GN obtain `f'` in a completion). -/
theorem HasPowerSeriesOnDisc.hasCDerivAt_iff (hf : HasPowerSeriesOnDisc f a z₀ r) {z : ℂ}
    (hz : ‖z‖ < r) {y : F} :
    HasCDerivAt f (z₀ + z) y ↔ HasSum (fun n : ℕ ↦ ((n : ℂ) * z ^ (n - 1)) • a n) y := by
  obtain ⟨h1, h2, h3⟩ := hf.dqTerm_facts hz
  have hu0 : (fun n ↦ dqTerm a z n 0) = fun n : ℕ ↦ ((n : ℂ) * z ^ (n - 1)) • a n := by
    funext n; simp only [dqTerm, add_zero, geom_sum₂_self]
  rw [← hu0]
  exact tendsto_iff_hasSum_of_dominated h1 h2 h3

/-- **Continuity of power series** on their whole disc of convergence
([GN26, footnote to Remark 2.1.3], where continuity at the center is shown), without completeness of
`F`: `q (f (z₀ + z + w) - f (z₀ + z)) ≤ ‖w‖ ∑ Mₙ`. -/
theorem HasPowerSeriesOnDisc.continuousOn (hf : HasPowerSeriesOnDisc f a z₀ r) :
    ContinuousOn f (ball z₀ r) := fun y hy ↦ by
  have hz : ‖y - z₀‖ < r := by simpa [dist_eq_norm] using hy
  obtain ⟨-, h2, h3⟩ := hf.dqTerm_facts hz
  rw [add_sub_cancel] at h2
  refine (continuousAt_of_tendsto_punctured ?_).continuousWithinAt
  refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
  obtain ⟨M, hMs, hMb⟩ := h3 q hq
  have hw : Tendsto (fun w : ℂ ↦ ‖w‖ * ∑' n, M n) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_norm.tendsto' (0 : ℂ) 0 norm_zero).mul_const
      (∑' n, M n)).mono_left nhdsWithin_le_nhds
  filter_upwards [h2, nhdsWithin_le_nhds hMb, self_mem_nhdsWithin,
    hw.eventually (gt_mem_nhds hε)] with w hw2 hwM (hw0 : w ≠ 0) hwε
  calc q (f (y + w) - f y) = ‖w‖ * q (w⁻¹ • (f (y + w) - f y)) := by
        rw [map_smul_eq_mul, norm_inv, mul_inv_cancel_left₀ (norm_ne_zero_iff.2 hw0)]
    _ ≤ ‖w‖ * ∑' n, M n := by gcongr; exact seminorm_le_of_hasSum hq hw2 hMs hwM
    _ < ε := hwε

/-- At the center, the complex derivative of a power series is its linear coefficient. -/
theorem HasPowerSeriesOnDisc.hasCDerivAt (hf : HasPowerSeriesOnDisc f a z₀ r) (hr : 0 < r) :
    HasCDerivAt f z₀ (a 1) := by
  have := (hf.hasCDerivAt_iff (z := 0) (by simpa using hr) (y := a 1)).2 ?_
  · simpa using this
  convert hasSum_single (f := fun n : ℕ ↦ ((n : ℂ) * (0 : ℂ) ^ (n - 1)) • a n) 1
    fun n hn ↦ ?_ using 1
  · simp
  · rcases n with _ | _ | n
    · simp
    · exact absurd rfl hn
    · simp

/-- Continuity of power series ([GN26, footnote to Remark 2.1.3]). -/
theorem HasPowerSeriesOnDisc.continuousAt (hf : HasPowerSeriesOnDisc f a z₀ r) (hr : 0 < r) :
    ContinuousAt f z₀ :=
  (hf.hasCDerivAt hr).continuousAt

omit [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- The differentiated series, reindexed as a power series: `∑ n zⁿ⁻¹ aₙ = ∑ zⁿ (n+1) aₙ₊₁`. -/
theorem hasSum_deriv_series_iff {z : ℂ} {y : F} :
    HasSum (fun n : ℕ ↦ ((n : ℂ) * z ^ (n - 1)) • a n) y ↔
      HasSum (fun n : ℕ ↦ z ^ n • (((n : ℂ) + 1) • a (n + 1))) y := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, zero_smul,
    sub_zero, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, smul_smul, mul_comm]

/-! ### Complex analytic maps on open subsets of `ℂ` -/

/-- `f` is complex analytic on `U` ([GN26, Definition 2.1.2 and Remark 2.1.3] for
`E = ℂ`): around every point of `U`, `f` is given by a power series converging in `F`.
GN also require continuity; it is automatic (`CAnalyticOn.continuousOn`, GN footnote to
Remark 2.1.3). -/
def CAnalyticOn (f : ℂ → F) (U : Set ℂ) : Prop :=
  ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ a : ℕ → F, HasPowerSeriesOnDisc f a x r

variable {U : Set ℂ}

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- The domain of a complex analytic map is open. -/
theorem CAnalyticOn.isOpen (hf : CAnalyticOn f U) : IsOpen U :=
  Metric.isOpen_iff.2 fun x hx ↦ by
    obtain ⟨r, hr, hU, -⟩ := hf x hx
    exact ⟨r, hr, hU⟩

/-- Complex analytic maps are continuous ([GN26, footnote to Remark 2.1.3]). -/
theorem CAnalyticOn.continuousOn (hf : CAnalyticOn f U) : ContinuousOn f U := fun x hx ↦ by
  obtain ⟨r, hr, -, a, ha⟩ := hf x hx
  exact (ha.continuousAt hr).continuousWithinAt

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- `x + z` lies in the disc `B(x, r)` when `‖z‖ < r`. -/
theorem mem_ball_add {x z : ℂ} {r : ℝ} (hz : ‖z‖ < r) : x + z ∈ ball x r := by
  simpa [mem_ball, dist_eq_norm] using hz

variable [T2Space F]

/-- A complex analytic map has a complex derivative at each point of `U`
([GN26, Corollary 2.1.8 and Lemma 2.1.1]). -/
theorem CAnalyticOn.hasCDerivAt (hf : CAnalyticOn f U) {x : ℂ} (hx : x ∈ U) :
    HasCDerivAt f x (cDeriv f x) := by
  obtain ⟨r, hr, -, a, ha⟩ := hf x hx
  have h := ha.hasCDerivAt hr
  rwa [h.cDeriv_eq]

/-- The derivative of a complex analytic map is complex analytic, and it is obtained by termwise
differentiation ([GN26, Lemma 2.1.10]), without any completeness of `F`: on each disc
where `f (x + z) = ∑ zⁿ aₙ`, one has `f' (x + z) = ∑ zⁿ (n + 1) aₙ₊₁`. -/
theorem CAnalyticOn.hasPowerSeriesOnDisc_cDeriv (hf : CAnalyticOn f U) {x : ℂ} {r : ℝ}
    (hU : ball x r ⊆ U) (ha : HasPowerSeriesOnDisc f a x r) :
    HasPowerSeriesOnDisc (cDeriv f) (fun n ↦ ((n : ℂ) + 1) • a (n + 1)) x r := fun _ hz ↦
  hasSum_deriv_series_iff.1 ((ha.hasCDerivAt_iff hz).1 (hf.hasCDerivAt (hU (mem_ball_add hz))))

/-- The derivative of a complex analytic map is complex analytic
([GN26, Lemma 2.1.10]). -/
theorem CAnalyticOn.cAnalyticOn_cDeriv (hf : CAnalyticOn f U) : CAnalyticOn (cDeriv f) U :=
    fun x hx ↦ by
  obtain ⟨r, hr, hU, a, ha⟩ := hf x hx
  exact ⟨r, hr, hU, _, hf.hasPowerSeriesOnDisc_cDeriv hU ha⟩

/-- All iterated complex derivatives `f⁽ⁿ⁾` of a complex analytic map are complex analytic. -/
theorem CAnalyticOn.cAnalyticOn_iterate_cDeriv (hf : CAnalyticOn f U) (n : ℕ) :
    CAnalyticOn (cDeriv^[n] f) U := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.cAnalyticOn_cDeriv

end PowerSeries

/-! ### Scalar facts from Mathlib's complex analysis -/

section Scalar

variable {g : ℂ → ℂ} {c : ℕ → ℂ} {x : ℂ} {r : ℝ}

/-- A scalar power series in our sense is a power series in Mathlib's sense. -/
theorem hasFPowerSeriesOnBall_ofScalars (hr : 0 < r)
    (hg : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n ↦ z ^ n • c n) (g (x + z))) :
    HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ c) x (ENNReal.ofReal r) where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hr] at hρ
    have hs := (hg ρ (by simpa using hρ)).summable
    obtain ⟨C, hC⟩ := ((continuous_norm.tendsto 0).comp hs.tendsto_atTop_zero).bddAbove_range
    refine FormalMultilinearSeries.le_radius_of_bound _ C fun n ↦ ?_
    have := hC ⟨n, rfl⟩
    simp only [Function.comp_apply, norm_smul, norm_pow, Complex.norm_real, NNReal.norm_eq]
      at this
    rw [FormalMultilinearSeries.ofScalars_norm, mul_comm]
    exact this
  r_pos := ENNReal.ofReal_pos.2 hr
  hasSum {y} hy := by
    rw [Metric.eball_ofReal, mem_ball, dist_zero_right] at hy
    convert hg y hy using 1
    funext n
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, smul_eq_mul, mul_comm]

/-- A scalar power series is holomorphic on its disc. -/
theorem differentiableOn_of_hasSum (hr : 0 < r)
    (hg : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n ↦ z ^ n • c n) (g (x + z))) :
    DifferentiableOn ℂ g (ball x r) := by
  simpa [Metric.eball_ofReal] using (hasFPowerSeriesOnBall_ofScalars hr hg).differentiableOn

/-- The coefficients of a scalar power series are the Taylor coefficients. -/
theorem coeff_eq_iteratedDeriv_of_hasSum (hr : 0 < r)
    (hg : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n ↦ z ^ n • c n) (g (x + z))) (n : ℕ) :
    c n = iteratedDeriv n g x / n.factorial := by
  have h := hasFPowerSeriesOnBall_ofScalars hr hg
  have h2 := h.analyticAt.hasFPowerSeriesAt
  have := h.hasFPowerSeriesAt.eq_formalMultilinearSeries h2
  rw [FormalMultilinearSeries.ofScalars_series_eq_iff] at this
  exact congrFun this n

/-- Taylor remainder estimate for a holomorphic function on a closed disc, from the Cauchy
estimates: `|g (x + z) - ∑_{n < N} zⁿ g⁽ⁿ⁾(x)/n!| ≤ C sᴺ / (1 - s)`, `s = ‖z‖ / R`. -/
theorem norm_sub_taylor_le {R C : ℝ} (hR : 0 < R) (hg : DiffContOnCl ℂ g (ball x R))
    (hC : ∀ ζ ∈ sphere x R, ‖g ζ‖ ≤ C) {z : ℂ} (hz : ‖z‖ < R) (N : ℕ) :
    ‖g (x + z) - ∑ n ∈ Finset.range N, z ^ n * (iteratedDeriv n g x / n.factorial)‖ ≤
      C * (‖z‖ / R) ^ N / (1 - ‖z‖ / R) := by
  set s := ‖z‖ / R
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s < 1 := (div_lt_one hR).2 hz
  have hT := Complex.hasSum_taylorSeries_on_ball hg.differentiableOn (mem_ball_add hz)
  simp only [add_sub_cancel_left] at hT
  have hT' : HasSum (fun n ↦ z ^ n * (iteratedDeriv n g x / n.factorial)) (g (x + z)) := by
    convert hT using 1
    funext n
    rw [smul_eq_mul, smul_eq_mul]; ring
  have htail := (hasSum_nat_add_iff' N).2 hT'
  have hgeom : HasSum (fun n ↦ C * s ^ (n + N)) (C * s ^ N / (1 - s)) := by
    have := (hasSum_geometric_of_lt_one hs0 hs1).mul_left (C * s ^ N)
    convert this using 1
    · funext n; rw [pow_add]; ring
    · rw [div_eq_mul_inv]
  refine htail.norm_le_of_bounded hgeom fun n ↦ ?_
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n + N) hR hg hC
  have hfac : (0 : ℝ) < (n + N).factorial := by positivity
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc ‖z‖ ^ (n + N) * (‖iteratedDeriv (n + N) g x‖ / (n + N).factorial)
      ≤ ‖z‖ ^ (n + N) * ((n + N).factorial * C / R ^ (n + N) / (n + N).factorial) := by gcongr
    _ = C * s ^ (n + N) := by
        simp only [s, div_pow]; field_simp

/-- **Cauchy's formula for the coefficients**, scalar case: for `0 < ρ < r`,
`∫₀^{2π} e^{-int} g(x + ρ e^{it}) dt = 2π ρⁿ cₙ`. -/
theorem integral_exp_mul_eq_coeff {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hg : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n ↦ z ^ n • c n) (g (x + z))) (n : ℕ) :
    ∫ t in (0 : ℝ)..2 * π,
      Complex.exp (-(n * (t * Complex.I))) * g (x + ρ * Complex.exp (t * Complex.I)) =
      2 * π * ρ ^ n * c n := by
  have hd : DifferentiableOn ℂ g (closedBall x ρ) :=
    (differentiableOn_of_hasSum (hρ.trans hρr) hg).mono (closedBall_subset_ball hρr)
  have hC := hd.circleIntegral_one_div_sub_center_pow_smul hρ n
  rw [coeff_eq_iteratedDeriv_of_hasSum (hρ.trans hρr) hg n]
  simp only [circleIntegral, deriv_circleMap, circleMap_sub_center] at hC
  have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hpt : ∀ θ : ℝ, (circleMap 0 ρ θ * Complex.I) •
      ((1 / circleMap 0 ρ θ ^ (n + 1)) • g (circleMap x ρ θ)) =
      (Complex.I / (ρ : ℂ) ^ n) * (Complex.exp (-(n * (θ * Complex.I))) *
        g (x + ρ * Complex.exp (θ * Complex.I))) := by
    intro θ
    have he : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    simp only [circleMap, zero_add, smul_eq_mul, Complex.exp_neg, Complex.exp_nat_mul]
    field_simp
    ring
  simp only [hpt, intervalIntegral.integral_const_mul] at hC
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  rw [smul_eq_mul] at hC
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hC ⊢
  linear_combination hC

end Scalar

/-! ### From scalar to vector-valued: Cauchy estimates and Taylor expansions -/

section Lifting

variable {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F]
  {f : ℂ → F} {a : ℕ → F} {x : ℂ} {R : ℝ}

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- Continuous `ℂ`-linear functionals separate the points of `F`. -/
theorem eq_of_forall_clm_eq [T2Space F] {v w : F} (h : ∀ ℓ : F →L[ℂ] ℂ, ℓ v = ℓ w) : v = w := by
  have h0 : ∀ q : Seminorm ℂ F, Continuous q → q (v - w) ≤ 0 := fun q hq ↦
    seminorm_le_of_forall_clm hq fun ℓ _ ↦ by rw [map_sub, h ℓ, sub_self, norm_zero]
  have ht : Tendsto (fun _ : ℕ ↦ v - w) atTop (𝓝 0) :=
    tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ Eventually.of_forall fun _ ↦ by
      rw [sub_zero]; exact (h0 q hq).trans_lt hε
  exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds ht)

/-- Hypothesis shared by the lifting lemmas: for every continuous functional `ℓ`, `ℓ ∘ f` is
holomorphic on the disc `B(x, R)` and continuous on its closure, and `ℓ (aₙ)` is its `n`-th
Taylor coefficient at `x`. -/
def WeakTaylorOn (f : ℂ → F) (a : ℕ → F) (x : ℂ) (R : ℝ) : Prop :=
  ∀ ℓ : F →L[ℂ] ℂ, DiffContOnCl ℂ (ℓ ∘ f) (ball x R) ∧
    ∀ n, ℓ (a n) = iteratedDeriv n (ℓ ∘ f) x / n.factorial

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- **Cauchy estimates** in `F` ([GN26, (2.12)]): if `q (f ζ) ≤ M` on the circle
`|ζ - x| = R`, then `q (aₙ) ≤ M / Rⁿ`. -/
theorem WeakTaylorOn.seminorm_le (h : WeakTaylorOn f a x R) (hR : 0 < R) {q : Seminorm ℂ F}
    (hq : Continuous q) {M : ℝ} (hM : ∀ ζ ∈ sphere x R, q (f ζ) ≤ M) (n : ℕ) :
    q (a n) ≤ M / R ^ n := by
  refine seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_
  obtain ⟨hd, hc⟩ := h ℓ
  have hC : ∀ ζ ∈ sphere x R, ‖(ℓ ∘ f) ζ‖ ≤ M := fun ζ hζ ↦ (hℓ _).trans (hM ζ hζ)
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hd hC
  have hfac : (0 : ℝ) < n.factorial := by positivity
  rw [hc, norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖iteratedDeriv n (ℓ ∘ f) x‖ ≤ n.factorial * M / R ^ n := this
    _ = M / R ^ n * n.factorial := by ring

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- A continuous seminorm is bounded on the image of a circle under a continuous map. -/
theorem exists_seminorm_bound_sphere (hcont : ContinuousOn f (sphere x R)) {q : Seminorm ℂ F}
    (hq : Continuous q) : ∃ M, ∀ ζ ∈ sphere x R, q (f ζ) ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere x R).exists_bound_of_continuousOn
    (hq.comp_continuousOn hcont)
  exact ⟨M, fun ζ hζ ↦ (le_abs_self _).trans (hM ζ hζ)⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- **Vector-valued Taylor expansion without completeness.** If the scalar functions `ℓ ∘ f`
are holomorphic on a disc with Taylor coefficients `ℓ (aₙ)`, with `aₙ ∈ F` *given*, and `f` is
continuous on the boundary circle, then `f (x + z) = ∑ zⁿ aₙ` in `F` on the open disc.
The convergence is controlled seminorm by seminorm through Hahn–Banach and the scalar Cauchy
estimates; this replaces GN's passage to a completion `F̃` (proofs of Corollaries 2.1.8, 2.1.9). -/
theorem WeakTaylorOn.hasPowerSeriesOnDisc (h : WeakTaylorOn f a x R) (hR : 0 < R)
    (hcont : ContinuousOn f (sphere x R)) : HasPowerSeriesOnDisc f a x R := by
  intro z hz
  set s := ‖z‖ / R
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s < 1 := (div_lt_one hR).2 hz
  refine hasSum_of_tendsto_of_dominated ?_ fun q hq ↦ ?_
  · refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
    obtain ⟨M, hM⟩ := exists_seminorm_bound_sphere hcont hq
    have key : ∀ N, q (∑ i ∈ Finset.range N, z ^ i • a i - f (x + z)) ≤ M * s ^ N / (1 - s) := by
      intro N
      refine seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_
      obtain ⟨hd, hc⟩ := h ℓ
      have hC : ∀ ζ ∈ sphere x R, ‖(ℓ ∘ f) ζ‖ ≤ M := fun ζ hζ ↦ (hℓ _).trans (hM ζ hζ)
      have := norm_sub_taylor_le hR hd hC hz N
      rw [map_sub, map_sum, norm_sub_rev]
      simpa only [map_smul, smul_eq_mul, hc, Function.comp_apply] using this
    have ht : Tendsto (fun N ↦ M * s ^ N / (1 - s)) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).const_mul M).div_const (1 - s)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with N hN
    exact (key N).trans_lt hN
  · obtain ⟨M, hM⟩ := exists_seminorm_bound_sphere hcont hq
    refine ⟨fun n ↦ M * s ^ n, (summable_geometric_of_lt_one hs0 hs1).mul_left M, fun n ↦ ?_⟩
    rw [map_smul_eq_mul, norm_pow]
    calc ‖z‖ ^ n * q (a n) ≤ ‖z‖ ^ n * (M / R ^ n) := by gcongr; exact h.seminorm_le hR hq hM n
      _ = M * s ^ n := by simp only [s, div_pow]; ring

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- The coefficients of a power series in `F` are determined by the scalar functions `ℓ ∘ f`. -/
theorem HasPowerSeriesOnDisc.clm_apply (hf : HasPowerSeriesOnDisc f a x R) (hR : 0 < R)
    (ℓ : F →L[ℂ] ℂ) (n : ℕ) : ℓ (a n) = iteratedDeriv n (ℓ ∘ f) x / n.factorial :=
  coeff_eq_iteratedDeriv_of_hasSum (c := fun n ↦ ℓ (a n)) hR (fun z hz ↦ by
    convert (hf z hz).map ℓ ℓ.continuous using 1
    · funext n; simp
    · rfl) n

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- If `f` is a power series in `F`, every `ℓ ∘ f` is holomorphic on the disc. -/
theorem HasPowerSeriesOnDisc.differentiableOn_clm (hf : HasPowerSeriesOnDisc f a x R)
    (hR : 0 < R) (ℓ : F →L[ℂ] ℂ) : DifferentiableOn ℂ (ℓ ∘ f) (ball x R) :=
  differentiableOn_of_hasSum (c := fun n ↦ ℓ (a n)) hR (fun z hz ↦ by
    convert (hf z hz).map ℓ ℓ.continuous using 1
    · funext n; simp
    · rfl)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- **Uniqueness of the coefficients** ([GN26, Corollary 2.1.8] (a)). -/
theorem HasPowerSeriesOnDisc.coeff_unique [T2Space F] {b : ℕ → F} {R' : ℝ}
    (ha : HasPowerSeriesOnDisc f a x R) (hb : HasPowerSeriesOnDisc f b x R') (hR : 0 < R)
    (hR' : 0 < R') : a = b :=
  funext fun n ↦ eq_of_forall_clm_eq fun ℓ ↦ by rw [ha.clm_apply hR, hb.clm_apply hR']

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] in
/-- On a smaller closed disc, a power series satisfies the hypothesis `WeakTaylorOn`. -/
theorem HasPowerSeriesOnDisc.weakTaylorOn (hf : HasPowerSeriesOnDisc f a x R) {ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) : WeakTaylorOn f a x ρ := fun ℓ ↦
  ⟨((hf.differentiableOn_clm (hρ.trans hρR) ℓ).mono
      (closure_ball_subset_closedBall.trans (closedBall_subset_ball hρR))).diffContOnCl,
    hf.clm_apply (hρ.trans hρR) ℓ⟩

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- **Cauchy estimates** for a power series ([GN26, (2.12)]): for `0 < ρ < R`,
`ρⁿ q (aₙ) ≤ sup_{|ζ| = ρ} q (f (x + ζ))`. -/
theorem HasPowerSeriesOnDisc.seminorm_coeff_le (hf : HasPowerSeriesOnDisc f a x R) {ρ : ℝ}
    (hρ : 0 < ρ) (hρR : ρ < R) {q : Seminorm ℂ F} (hq : Continuous q) {M : ℝ}
    (hM : ∀ ζ ∈ sphere x ρ, q (f ζ) ≤ M) (n : ℕ) : q (a n) ≤ M / ρ ^ n :=
  (hf.weakTaylorOn hρ hρR).seminorm_le hρ hq hM n

/-! ### Taylor expansion of complex analytic maps (Corollary 2.1.8) -/

variable [T2Space F] {U : Set ℂ}

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
/-- A complex derivative in `F` gives the complex derivative of `ℓ ∘ g`. -/
theorem HasCDerivAt.hasDerivAt_clm {g : ℂ → F} {y : ℂ} {v : F} (h : HasCDerivAt g y v)
    (ℓ : F →L[ℂ] ℂ) : HasDerivAt (ℓ ∘ g) (ℓ v) y := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  refine ((ℓ.continuous.tendsto v).comp h).congr fun t ↦ ?_
  simp [map_smul, map_sub]

/-- `f` complex analytic implies `ℓ ∘ f` holomorphic ("weakly analytic", GN
Proposition 2.1.6 (d)). -/
theorem CAnalyticOn.differentiableOn_clm (hf : CAnalyticOn f U) (ℓ : F →L[ℂ] ℂ) :
    DifferentiableOn ℂ (ℓ ∘ f) U := fun _ hy ↦
  ((hf.hasCDerivAt hy).hasDerivAt_clm ℓ).differentiableAt.differentiableWithinAt

/-- The complex derivatives of `ℓ ∘ f` are `ℓ ∘ f⁽ⁿ⁾`. -/
theorem CAnalyticOn.iteratedDeriv_clm (hf : CAnalyticOn f U) (ℓ : F →L[ℂ] ℂ) (n : ℕ) :
    EqOn (iteratedDeriv n (ℓ ∘ f)) (ℓ ∘ cDeriv^[n] f) U := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (ℓ ∘ f) =ᶠ[𝓝 y] ℓ ∘ cDeriv^[n] f :=
      Filter.eventually_of_mem (hf.isOpen.mem_nhds hy) ih
    rw [hev.deriv_eq, (((hf.cAnalyticOn_iterate_cDeriv n).hasCDerivAt hy).hasDerivAt_clm ℓ).deriv,
      Function.comp_apply, Function.iterate_succ_apply']

/-- A complex analytic map satisfies `WeakTaylorOn` on each closed disc contained in `U`,
with the coefficients `f⁽ⁿ⁾(x)/n!`. -/
theorem CAnalyticOn.weakTaylorOn (hf : CAnalyticOn f U) (hR : 0 ≤ R)
    (hsub : closedBall x R ⊆ U) :
    WeakTaylorOn f (fun n ↦ (n.factorial : ℂ)⁻¹ • cDeriv^[n] f x) x R := fun ℓ ↦
  ⟨((hf.differentiableOn_clm ℓ).mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl,
    fun n ↦ by
      rw [map_smul, smul_eq_mul, hf.iteratedDeriv_clm ℓ n (hsub (mem_closedBall_self hR)),
        div_eq_inv_mul, Function.comp_apply]⟩

/-- **Taylor expansion on the largest closed disc** ([GN26, Corollary 2.1.8] (b)):
if `f` is complex analytic on `U` and `B̄(x, R) ⊆ U`, then
`f (x + z) = ∑ zⁿ f⁽ⁿ⁾(x) / n!` in `F` for `‖z‖ < R`. No completeness of `F` is used. -/
theorem CAnalyticOn.hasPowerSeriesOnDisc (hf : CAnalyticOn f U) (hR : 0 < R)
    (hsub : closedBall x R ⊆ U) :
    HasPowerSeriesOnDisc f (fun n ↦ (n.factorial : ℂ)⁻¹ • cDeriv^[n] f x) x R :=
  (hf.weakTaylorOn hR.le hsub).hasPowerSeriesOnDisc hR
    (hf.continuousOn.mono (sphere_subset_closedBall.trans hsub))

/-- **The coefficients are the Taylor coefficients** ([GN26, Corollary 2.1.8] (a)):
`aₙ = f⁽ⁿ⁾(x) / n!`. -/
theorem CAnalyticOn.coeff_eq (hf : CAnalyticOn f U) {r : ℝ} (hr : 0 < r) (hx : x ∈ U)
    (ha : HasPowerSeriesOnDisc f a x r) (n : ℕ) :
    a n = (n.factorial : ℂ)⁻¹ • cDeriv^[n] f x := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hf.isOpen x hx
  have hsub : closedBall x (ε / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεU
  exact congrFun (ha.coeff_unique (hf.hasPowerSeriesOnDisc (half_pos hε) hsub) hr
    (half_pos hε)) n

/-- **Cauchy estimates** for the derivatives ([GN26, (2.12)]):
`q (f⁽ⁿ⁾(x)) ≤ n! / Rⁿ · max_{|ζ - x| = R} q (f ζ)`. -/
theorem CAnalyticOn.seminorm_iterate_cDeriv_le (hf : CAnalyticOn f U) (hR : 0 < R)
    (hsub : closedBall x R ⊆ U) {q : Seminorm ℂ F} (hq : Continuous q) {M : ℝ}
    (hM : ∀ ζ ∈ sphere x R, q (f ζ) ≤ M) (n : ℕ) :
    q (cDeriv^[n] f x) ≤ n.factorial * M / R ^ n := by
  have h := (hf.weakTaylorOn hR.le hsub).seminorm_le hR hq hM n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  rw [map_smul_eq_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hfac] at h
  rwa [mul_div_assoc]

/-- **Identity theorem**: two complex analytic maps on a connected open set which agree near
one point agree everywhere. -/
theorem CAnalyticOn.eqOn_of_preconnected_of_eventuallyEq {g : ℂ → F} (hf : CAnalyticOn f U)
    (hg : CAnalyticOn g U) (hU : IsPreconnected U) (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) :
    EqOn f g U := fun y hy ↦ eq_of_forall_clm_eq fun ℓ ↦
  ((hf.differentiableOn_clm ℓ).analyticOnNhd hf.isOpen).eqOn_of_preconnected_of_eventuallyEq
    ((hg.differentiableOn_clm ℓ).analyticOnNhd hf.isOpen) hU hx
    (hfg.mono fun _ h ↦ by simp [h]) hy

end Lifting

/-! ### Relation with the real Michal–Bastiani calculus (Lemma 2.1.1) -/

section MichalBastiani

variable {F : Type v} [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]

omit [IsTopologicalAddGroup F] in
/-- The real scalar multiplication of a complex topological vector space is continuous. -/
theorem continuousSMul_real_of_complex : ContinuousSMul ℝ F := IsScalarTower.continuousSMul ℂ

attribute [local instance] continuousSMul_real_of_complex

omit [IsTopologicalAddGroup F] in
/-- A complex derivative gives all real directional derivatives:
`df(x, w) = w • f'(x)` ([GN26, (2.4)]). -/
theorem HasCDerivAt.hasDirDerivAt {f : ℂ → F} {x : ℂ} {y : F} (h : HasCDerivAt f x y) (w : ℂ) :
    HasDirDerivAt f x w (w • y) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp only [HasDirDerivAt, smul_zero, add_zero, sub_self, zero_smul]
    exact tendsto_const_nhds
  · have hm : Tendsto (fun t : ℝ ↦ (t : ℂ) * w) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦
        mul_ne_zero (by exact_mod_cast ht) hw⟩
      have : Continuous fun t : ℝ ↦ (t : ℂ) * w := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ((h.comp hm).const_smul w).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    simp only [Function.comp_apply]
    rw [Complex.real_smul, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hw, mul_one]
    simp

omit [IsTopologicalAddGroup F] in
/-- Directional derivatives of `z ↦ c • f z`, `c ∈ ℂ`. -/
theorem HasCDerivAt.hasDirDerivAt_const_smul {f : ℂ → F} {x : ℂ} {y : F}
    (h : HasCDerivAt f x y) (c w : ℂ) :
    HasDirDerivAt (fun z ↦ c • f z) x w (c • (w • y)) :=
  (Filter.Tendsto.const_smul (h.hasDirDerivAt w) c).congr fun t ↦ by
    rw [← smul_sub, smul_comm]

variable [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] polynormableSpace_complex

variable {f : ℂ → F} {U : Set ℂ}

/-- **[GN26, (2.3)]**: the iterated Michal–Bastiani differentials of a complex analytic
map are `d⁽ʲ⁾f (x, w₁, …, wⱼ) = w₁ ⋯ wⱼ • f⁽ʲ⁾(x)`. -/
theorem CAnalyticOn.iteratedDMB_eq (hf : CAnalyticOn f U) :
    ∀ (j : ℕ) {x : ℂ}, x ∈ U → ∀ v : Fin j → ℂ,
      iteratedDMB j f (x, v) = (∏ i, v i) • cDeriv^[j] f x
  | 0, x, _, v => by simp [iteratedDMB_zero]
  | j + 1, x, hx, v => by
    have hev : (fun z ↦ iteratedDMB j f (z, Fin.init v)) =ᶠ[𝓝 x]
        fun z ↦ (∏ i, Fin.init v i) • cDeriv^[j] f z :=
      Filter.eventually_of_mem (hf.isOpen.mem_nhds hx) fun z hz ↦
        hf.iteratedDMB_eq j hz (Fin.init v)
    rw [iteratedDMB_succ, dMB_congr_of_eventuallyEq hev,
      (((hf.cAnalyticOn_iterate_cDeriv j).hasCDerivAt hx).hasDirDerivAt_const_smul _ _).dMB_eq,
      Fin.prod_univ_castSucc, Function.iterate_succ_apply', mul_smul]
    rfl

/-- A complex analytic map has continuous iterated Michal–Bastiani differentials of all
orders ([GN26, Lemma 2.1.1 and Corollary 2.1.8]). -/
theorem CAnalyticOn.hasContIterDerivOn (hf : CAnalyticOn f U) (k : ℕ) :
    HasContIterDerivOn k f U := by
  refine ⟨fun j _ x hx v ↦ ?_, fun j _ ↦ ?_⟩
  · have hev : (fun z ↦ (∏ i, Fin.init v i) • cDeriv^[j] f z) =ᶠ[𝓝 x]
        fun z ↦ iteratedDMB j f (z, Fin.init v) :=
      Filter.eventually_of_mem (hf.isOpen.mem_nhds hx) fun z hz ↦
        (hf.iteratedDMB_eq j hz (Fin.init v)).symm
    have h := (((hf.cAnalyticOn_iterate_cDeriv j).hasCDerivAt hx).hasDirDerivAt_const_smul
      (∏ i, Fin.init v i) (v (Fin.last j))).congr_of_eventuallyEq hev
    rw [hf.iteratedDMB_eq (j + 1) hx v, Fin.prod_univ_castSucc, Function.iterate_succ_apply',
      mul_smul]
    exact h
  · have hc : ContinuousOn (fun p : ℂ × (Fin j → ℂ) ↦ (∏ i, p.2 i) • cDeriv^[j] f p.1)
        (U ×ˢ univ) := by
      refine ContinuousOn.smul (Continuous.continuousOn (by fun_prop)) ?_
      exact (hf.cAnalyticOn_iterate_cDeriv j).continuousOn.comp continuousOn_fst
        fun p hp ↦ hp.1
    exact hc.congr fun p hp ↦ hf.iteratedDMB_eq j hp.1 p.2

/-- **Complex analytic maps are smooth** in the real Michal–Bastiani sense
([GN26, Corollary 2.1.9], (c) ⇒ (b)); no completeness of `F` is needed. -/
theorem CAnalyticOn.smoothMBOn (hf : CAnalyticOn f U) : SmoothMBOn f U := fun k ↦
  (hf.hasContIterDerivOn k).contDiffMBOn hf.isOpen

/-- **[GN26, (2.4)]**: `df(x, w) = w • f'(x)`; in particular `df(x, ·)` is
complex linear. -/
theorem CAnalyticOn.dMB_eq (hf : CAnalyticOn f U) {x : ℂ} (hx : x ∈ U) (w : ℂ) :
    dMB f (x, w) = w • cDeriv f x :=
  ((hf.hasCDerivAt hx).hasDirDerivAt w).dMB_eq

/-! ### Corollary 2.1.9: complex analytic = real smooth with complex linear differential -/

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Directional derivatives of `ℓ ∘ g` for a continuous `ℂ`-linear functional `ℓ`. -/
theorem HasDirDerivAt.clm_comp {g : ℂ → F} {x w : ℂ} {y : F} (h : HasDirDerivAt g x w y)
    (ℓ : F →L[ℂ] ℂ) : HasDirDerivAt (ℓ ∘ g) x w (ℓ y) :=
  ((ℓ.continuous.tendsto y).comp h).congr fun t ↦ by
    simp only [Function.comp_apply, map_sub, ContinuousLinearMap.map_smul_of_tower]

/-- For a holomorphic scalar function, the complex derivative is the real directional
derivative in the direction `1`. -/
theorem deriv_eq_of_hasDirDerivAt_one {h : ℂ → ℂ} {y c : ℂ} (hd : DifferentiableAt ℂ h y)
    (hc : HasDirDerivAt h y 1 c) : deriv h y = c := by
  have h1 : HasCDerivAt h y (deriv h y) := hasDerivAt_iff_tendsto_slope_zero.1 hd.hasDerivAt
  have := (h1.hasDirDerivAt 1).dMB_eq
  rw [hc.dMB_eq, one_smul] at this
  exact this.symm

/-- **[GN26, Corollary 2.1.9], (b) ⇒ (c)**, without completeness: a map `f : U → F`,
`U ⊆ ℂ` open, which is smooth in the real Michal–Bastiani sense and whose differentials
`df(x, ·)` are complex linear, is complex analytic. GN pass through a completion of `F`; here
the coefficients `f⁽ⁿ⁾(x)/n! = d⁽ⁿ⁾f(x, 1, …, 1)/n!` lie in `F` by hypothesis, the scalar
functions `ℓ ∘ f` are holomorphic, and `WeakTaylorOn.hasPowerSeriesOnDisc` gives convergence
in `F`. -/
theorem cAnalyticOn_of_smoothMBOn (hU : IsOpen U) (hf : SmoothMBOn f U)
    (hlin : ∀ x ∈ U, ∀ w : ℂ, dMB f (x, w) = w • dMB f (x, 1)) : CAnalyticOn f U := by
  let D : ℕ → ℂ → F := fun n z ↦ iteratedDMB n f (z, fun _ ↦ (1 : ℂ))
  have hDd : ∀ n, ∀ z ∈ U, HasDirDerivAt (D n) z 1 (D (n + 1) z) := fun n z hz ↦
    (hf (n + 1)).hasContIterDerivOn.1 n (Nat.lt_succ_self n) z hz fun _ ↦ 1
  -- the scalar functions `ℓ ∘ f` are holomorphic
  have hhol : ∀ ℓ : F →L[ℂ] ℂ, DifferentiableOn ℂ (ℓ ∘ f) U := by
    intro ℓ z hz
    let ℓR : F →L[ℝ] ℂ := ℓ.restrictScalars ℝ
    have h2 : ContDiffMBOn (1 + 1) (ℓR ∘ f) U :=
      ContDiffMBOn.comp hU isOpen_univ (ℓR.contDiffMBOn 2 univ) (hf 2) (mapsTo_univ _ _)
    have hC : ContDiffOn ℝ 1 (ℓ ∘ f) U := h2.contDiffOn hU
    have hF :=
      ((hC.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    refine (hasFDerivAt_of_restrictScalars ℝ hF
      (f' := (1 : ℂ →L[ℂ] ℂ).smulRight (ℓ (dMB f (z, 1)))) ?_).differentiableAt
      |>.differentiableWithinAt
    refine ContinuousLinearMap.ext fun w ↦ ?_
    have h1 := (hF.hasDirDerivAt w).dMB_eq
    have h3 := (((hf 1).hasDirDerivAt hz w).clm_comp ℓ).dMB_eq
    rw [h1] at h3
    rw [h3, hlin z hz w, map_smul, smul_eq_mul]
    simp
  -- their iterated derivatives are `ℓ ∘ d⁽ⁿ⁾f(·, 1, …, 1)`
  have hiter : ∀ ℓ : F →L[ℂ] ℂ, ∀ n, DifferentiableOn ℂ (iteratedDeriv n (ℓ ∘ f)) U ∧
      EqOn (iteratedDeriv n (ℓ ∘ f)) (ℓ ∘ D n) U := by
    intro ℓ n
    induction n with
    | zero => exact ⟨by simpa using hhol ℓ, fun z _ ↦ by simp [D, iteratedDMB_zero]⟩
    | succ n ih =>
      refine ⟨by rw [iteratedDeriv_succ]; exact ih.1.deriv hU, fun z hz ↦ ?_⟩
      have hev : iteratedDeriv n (ℓ ∘ f) =ᶠ[𝓝 z] ℓ ∘ D n :=
        Filter.eventually_of_mem (hU.mem_nhds hz) ih.2
      rw [iteratedDeriv_succ, hev.deriv_eq]
      refine deriv_eq_of_hasDirDerivAt_one ?_ ((hDd n z hz).clm_comp ℓ)
      exact ((ih.1 z hz).differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq hev.symm
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  have hsub : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  refine ⟨ε / 2, half_pos hε, ball_subset_closedBall.trans hsub,
    fun n ↦ (n.factorial : ℂ)⁻¹ • D n x, ?_⟩
  refine WeakTaylorOn.hasPowerSeriesOnDisc (fun ℓ ↦ ⟨?_, fun n ↦ ?_⟩) (half_pos hε)
    ((hf 0).continuousOn.mono (sphere_subset_closedBall.trans hsub))
  · exact ((hhol ℓ).mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  · rw [map_smul, smul_eq_mul, (hiter ℓ n).2 (hsub (mem_closedBall_self (half_pos hε).le)),
      div_eq_inv_mul, Function.comp_apply]

/-- **[GN26, Corollary 2.1.9], (b) ⇔ (c)**, for an arbitrary (not necessarily complete)
complex locally convex space `F`: a map on an open subset of `ℂ` is complex analytic iff it is
smooth in the real Michal–Bastiani sense with complex linear differentials. -/
theorem cAnalyticOn_iff_smoothMBOn (hU : IsOpen U) :
    CAnalyticOn f U ↔ SmoothMBOn f U ∧ ∀ x ∈ U, ∀ w : ℂ, dMB f (x, w) = w • dMB f (x, 1) :=
  ⟨fun hf ↦ ⟨hf.smoothMBOn, fun x hx w ↦ by rw [hf.dMB_eq hx, hf.dMB_eq hx, one_smul]⟩,
    fun h ↦ cAnalyticOn_of_smoothMBOn hU h.1 h.2⟩

/-! ### Cauchy's formula for the coefficients as a weak integral (Corollary 2.1.8 (c)) -/

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- **Cauchy's integral formula for the coefficients, as a weak integral in `F`**
([GN26, Definition 2.1.4 and Corollary 2.1.8] (c)): if `f (x + z) = ∑ zⁿ aₙ` for
`‖z‖ < r` and `0 < ρ < r`, then the weak integral of `t ↦ e^{-int} f(x + ρ e^{it})` over
`[0, 2π]` exists in `F` and equals `2π ρⁿ aₙ`. In terms of GN's contour integrals this is
`aₙ = (2πi)⁻¹ ∮_{|ζ - x| = ρ} f(ζ) (ζ - x)^{-(n+1)} dζ`. The integral exists in the possibly
incomplete space `F` because its value is the coefficient `aₙ`, which is given. -/
theorem HasPowerSeriesOnDisc.hasWeakIntegral {a : ℕ → F} {x : ℂ} {r ρ : ℝ}
    (hf : HasPowerSeriesOnDisc f a x r) (hρ : 0 < ρ) (hρr : ρ < r) (n : ℕ) :
    HasWeakIntegral (fun t : ℝ ↦ Complex.exp (-(n * (t * Complex.I))) •
      f (x + ρ * Complex.exp (t * Complex.I))) 0 (2 * π) ((2 * π * ρ ^ n) • a n) := by
  intro φ
  let ℓ : F →L[ℂ] ℂ := StrongDual.extendRCLike φ
  have hre : ∀ v, φ v = (ℓ v).re := fun v ↦ by
    rw [← RCLike.re_to_complex]; exact (StrongDual.re_extendRCLike_apply φ v).symm
  have hs := integral_exp_mul_eq_coeff (g := ℓ ∘ f) (c := fun n ↦ ℓ (a n)) hρ hρr
    (fun z hz ↦ by
      convert (hf z hz).map ℓ ℓ.continuous using 1
      · funext n; simp
      · rfl) n
  have hcont : Continuous fun t : ℝ ↦ Complex.exp (-(n * (t * Complex.I))) *
      (ℓ ∘ f) (x + ρ * Complex.exp (t * Complex.I)) := by
    refine Continuous.mul (by fun_prop) ?_
    refine (hf.differentiableOn_clm (hρ.trans hρr) ℓ).continuousOn.comp_continuous
      (by fun_prop) fun t ↦ ?_
    simp [mem_ball, dist_eq_norm, abs_of_pos hρ, hρr]
  have hint : ∫ t in (0 : ℝ)..2 * π, (Complex.exp (-(n * (t * Complex.I))) *
      (ℓ ∘ f) (x + ρ * Complex.exp (t * Complex.I))).re =
      (∫ t in (0 : ℝ)..2 * π, Complex.exp (-(n * (t * Complex.I))) *
        (ℓ ∘ f) (x + ρ * Complex.exp (t * Complex.I))).re := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * π))
    simpa using this
  simp only [hre, ContinuousLinearMap.map_smul_of_tower, smul_eq_mul, Complex.real_smul]
  simp only [Function.comp_apply] at hint hs
  rw [hint, hs]
  simp

end MichalBastiani

end LocallyConvex.Analysis

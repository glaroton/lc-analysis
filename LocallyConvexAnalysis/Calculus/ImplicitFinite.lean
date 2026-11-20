/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MBFrechetFinite
public import LocallyConvexAnalysis.Calculus.Higher
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Implicit functions with parameters in a locally convex space

Let `E` be a locally convex space, `F` a finite-dimensional normed space, and
`Φ : E × F → F` a `C^k` map in the sense of Michal–Bastiani on an open set `U`, `k ≥ 1`. If
`φ : P → F` is continuous on an open set `P ⊆ E`, solves `Φ(p, φ(p)) = 0`, and the partial
derivative `∂₂Φ(p, φ(p))` is invertible, then `φ` is `C^k`, with

  `dφ(p)(q) = -∂₂Φ(p, φ(p))⁻¹ (d₁Φ(p, φ(p))(q))`.

This is the regularity half of the implicit function theorem with parameters in a locally convex
space ([GN26, Theorem 2.3.40], there with a Banach space `F` and `k ≥ 2`); we only need it for
finite-dimensional `F`, where the proof is elementary and uses no fixed point theorem. The
existence and continuity of `φ` are supplied separately in the applications (for instance by
compactness, in the inversion of diffeomorphisms of a compact manifold, [GN26, Lemma 13.1.8]).

## Main definitions

* `partialFDeriv₂ Φ z`: the partial derivative of `Φ` in the second variable at `z`, as a
  continuous linear map `F →L[ℝ] F`.

## Main results

* `hasFDerivAt_partialFDeriv₂`, `partialFDeriv₂_apply`: for `C^1` maps, `∂₂Φ(z)` is the Fréchet
  derivative of `Φ(z.1, ·)`, and `∂₂Φ(z) v = dΦ(z)(0, v)`.
* `ContDiffMBOn.contDiffMBOn_partialFDeriv₂`: `z ↦ ∂₂Φ(z)` is `C^{k-1}` for `C^k` maps `Φ`.
* `hasDirDerivAt_of_implicit`: the derivative of an implicit function.
* `contDiffMBOn_of_implicit`, `smoothMBOn_of_implicit`: implicit functions are `C^k`, resp.
  smooth.

## Implementation notes

The difference quotient of `φ` is controlled by the mean value inequality for `Φ(p + tq, ·)`
around `φ(p)` with the fixed operator `B = ∂₂Φ(p, φ(p))`: writing `Δ = φ(p + tq) - φ(p)`,

  `‖Φ(p + tq, φ(p)) - Φ(p, φ(p)) + B Δ‖ ≤ ε ‖Δ‖`,

so `t⁻¹ Δ + B⁻¹ (t⁻¹ (Φ(p + tq, φ(p)) - Φ(p, φ(p))))` is small compared with `t⁻¹ Δ`. Higher
derivatives follow by induction, since the formula for `dφ` involves `φ` only through
`C^{k-1}` operations.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The partial derivative of `Φ : E × F → F` in the second variable, as a continuous linear
map. -/
def partialFDeriv₂ (Φ : E × F → F) (z : E × F) : F →L[ℝ] F :=
  fderiv ℝ (fun y ↦ Φ (z.1, y)) z.2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [FiniteDimensional ℝ F] in
/-- The slice `y ↦ (p, y)` is `C^k`. -/
theorem contDiffMBOn_slice (k : ℕ) (p : E) {V : Set F} (hV : IsOpen V) :
    ContDiffMBOn k (fun y : F ↦ (p, y)) V :=
  ContDiffMBOn.prodMk hV (contDiffMBOn_const k p V) (smoothMBOn_id V k)

/-- For a `C^1` map `Φ`, `∂₂Φ(z)` is the Fréchet derivative of `Φ(z.1, ·)` at `z.2`, and
`∂₂Φ(z) v = dΦ(z)(0, v)`. -/
theorem hasFDerivAt_partialFDeriv₂ {Φ : E × F → F} {U : Set (E × F)} (hU : IsOpen U)
    (hΦ : ContDiffMBOn 1 Φ U) {z : E × F} (hz : z ∈ U) :
    HasFDerivAt (fun y ↦ Φ (z.1, y)) (partialFDeriv₂ Φ z) z.2 ∧
      ∀ v, partialFDeriv₂ Φ z v = dMB Φ (z, (0, v)) := by
  set V : Set F := (fun y : F ↦ (z.1, y)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hzV : z.2 ∈ V := by simpa [V] using hz
  have hs : ContDiffMBOn 1 (Φ ∘ fun y : F ↦ (z.1, y)) V :=
    ContDiffMBOn.comp hV hU hΦ (contDiffMBOn_slice 1 z.1 hV) fun y hy ↦ hy
  have hF : ContDiffOn ℝ 1 (fun y ↦ Φ (z.1, y)) V := hs.contDiffOn_of_finiteDimensional hV
  have hd : HasFDerivAt (fun y ↦ Φ (z.1, y)) (partialFDeriv₂ Φ z) z.2 :=
    ((hF.differentiableOn one_ne_zero z.2 hzV).differentiableAt (hV.mem_nhds hzV)).hasFDerivAt
  refine ⟨hd, fun v ↦ ?_⟩
  have h1 := hd.hasDirDerivAt v
  have h2 : HasDirDerivAt (fun y ↦ Φ (z.1, y)) z.2 v (dMB Φ (z, (0, v))) := by
    have := hΦ.2.1 z hz (0, v)
    refine this.congr fun t ↦ ?_
    simp only [smul_zero, Prod.smul_mk]
    rw [show z + ((0 : E), t • v) = (z.1, z.2 + t • v) from Prod.ext (by simp) rfl]
  exact tendsto_nhds_unique h1 h2

/-- `z ↦ ∂₂Φ(z)` is continuous on `U` for `C^1` maps `Φ`. -/
theorem continuousOn_partialFDeriv₂ {Φ : E × F → F} {U : Set (E × F)} (hU : IsOpen U)
    (hΦ : ContDiffMBOn 1 Φ U) : ContinuousOn (partialFDeriv₂ Φ) U := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  have hc : ContinuousOn (dMB Φ) (U ×ˢ univ) := hΦ.2.2
  refine (hc.comp (by fun_prop : Continuous fun z : E × F ↦ (z, ((0 : E), v))).continuousOn
    fun z hz ↦ ⟨hz, mem_univ _⟩).congr fun z hz ↦ ?_
  exact (hasFDerivAt_partialFDeriv₂ hU hΦ hz).2 v

/-- **The derivative of an implicit function.** If `φ` is continuous at `p`, solves
`Φ(·, φ(·)) = 0` near `p`, and `B = ∂₂Φ(p, φ(p))` is invertible, then `φ` has the directional
derivative `-B⁻¹ (dΦ(p, φ(p))(q, 0))` at `p` in the direction `q`. -/
theorem hasDirDerivAt_of_implicit {Φ : E × F → F} {U : Set (E × F)} (hU : IsOpen U)
    (hΦ : ContDiffMBOn 1 Φ U) {P : Set E} (hP : IsOpen P) {φ : E → F}
    (hφ : ContinuousOn φ P) (hmaps : ∀ p ∈ P, (p, φ p) ∈ U) (hzero : ∀ p ∈ P, Φ (p, φ p) = 0)
    {p : E} (hp : p ∈ P) (hB : IsUnit (partialFDeriv₂ Φ (p, φ p))) (q : E) :
    HasDirDerivAt φ p q (-(Ring.inverse (partialFDeriv₂ Φ (p, φ p)))
      (dMB Φ ((p, φ p), (q, 0)))) := by
  set B := partialFDeriv₂ Φ (p, φ p)
  set Bi := Ring.inverse B
  set a := dMB Φ ((p, φ p), (q, 0))
  have hBi : ∀ w, Bi (B w) = w := fun w ↦ by
    change (Bi * B) w = w
    rw [Ring.inverse_mul_cancel B hB]
    rfl
  set c := ‖Bi‖ + 1
  have hc : 0 < c := by positivity
  -- the difference quotient of `Φ` in the first variable
  have hR : Tendsto (fun t : ℝ ↦ Bi (t⁻¹ • (Φ (p + t • q, φ p) - Φ (p, φ p)))) (𝓝[≠] 0)
      (𝓝 (Bi a)) := by
    have := (hΦ.2.1 (p, φ p) (hmaps p hp) (q, 0))
    refine (Bi.continuous.tendsto a).comp (this.congr fun t ↦ ?_)
    simp
  -- the line through `p` in the direction `q`
  have hline : Tendsto (fun t : ℝ ↦ p + t • q) (𝓝[≠] 0) (𝓝 p) := by
    have : Continuous fun t : ℝ ↦ p + t • q := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hφp : ContinuousAt φ p := hφ.continuousAt (hP.mem_nhds hp)
  rw [HasDirDerivAt, Metric.tendsto_nhds]
  intro δ hδ
  -- choose `ε` with `c ε ≤ 1/2` and `2 c ε (‖Bi a‖ + 1) < δ / 2`
  set M := ‖Bi a‖ + 1
  set ε := min (1 / (2 * c)) (δ / (8 * c * M))
  have hM : 0 < M := by positivity
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hcε : c * ε ≤ 1 / 2 := by
    calc c * ε ≤ c * (1 / (2 * c)) := by gcongr; exact min_le_left _ _
      _ = 1 / 2 := by field_simp
  have hcεM : 2 * (c * ε) * M ≤ δ / 4 := by
    calc 2 * (c * ε) * M ≤ 2 * (c * (δ / (8 * c * M))) * M := by gcongr; exact min_le_right _ _
      _ = δ / 4 := by field_simp; ring
  -- a neighborhood of `(p, φ p)` where `∂₂Φ` is `ε`-close to `B`
  have hcont := (continuousOn_partialFDeriv₂ hU hΦ).continuousAt (hU.mem_nhds (hmaps p hp))
  have hN : {z | z ∈ U ∧ ‖partialFDeriv₂ Φ z - B‖ < ε} ∈ 𝓝 (p, φ p) := by
    have h2 : {z | ‖partialFDeriv₂ Φ z - B‖ < ε} ∈ 𝓝 (p, φ p) := by
      have := hcont.eventually (Metric.ball_mem_nhds B hε)
      filter_upwards [this] with z hz
      simpa [dist_eq_norm] using hz
    exact inter_mem (hU.mem_nhds (hmaps p hp)) h2
  obtain ⟨W, hW, R, hR0, hWR⟩ : ∃ W ∈ 𝓝 p, ∃ r > 0, W ×ˢ Metric.ball (φ p) r ⊆
      {z | z ∈ U ∧ ‖partialFDeriv₂ Φ z - B‖ < ε} := by
    obtain ⟨W, hW, V, hV, hWV⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
    exact ⟨W, hW, r, hr, (prod_mono subset_rfl hrV).trans hWV⟩
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), p + t • q ∈ W ∩ P ∧ φ (p + t • q) ∈ Metric.ball (φ p) R ∧
      dist (Bi (t⁻¹ • (Φ (p + t • q, φ p) - Φ (p, φ p)))) (Bi a) < min 1 (δ / 2) ∧ t ≠ 0 := by
    refine ((hline.eventually (inter_mem hW (hP.mem_nhds hp))).and
      ?_).and ((Metric.tendsto_nhds.1 hR _ (lt_min one_pos (by positivity))).and
        self_mem_nhdsWithin)
      |>.mono fun t ht ↦ ⟨ht.1.1, ht.1.2, ht.2⟩
    exact (hφp.tendsto.comp hline).eventually (Metric.ball_mem_nhds _ hR0)
  filter_upwards [hev] with t ⟨htW, htφ, htR, ht0⟩
  set Δ := φ (p + t • q) - φ p
  set r := Φ (p + t • q, φ p) - Φ (p, φ p)
  -- the mean value inequality for `Φ(p + t q, ·)` on the ball
  have hmv : ‖Φ (p + t • q, φ (p + t • q)) - Φ (p + t • q, φ p) - B Δ‖ ≤ ε * ‖Δ‖ := by
    have hball : ∀ y ∈ Metric.ball (φ p) R, (p + t • q, y) ∈ U ∧
        ‖partialFDeriv₂ Φ (p + t • q, y) - B‖ < ε := fun y hy ↦ hWR ⟨htW.1, hy⟩
    refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := fun y ↦ Φ (p + t • q, y)) (f' := fun y ↦ partialFDeriv₂ Φ (p + t • q, y))
      (fun y hy ↦ (hasFDerivAt_partialFDeriv₂ hU hΦ (hball y hy).1).1.hasFDerivWithinAt)
      (fun y hy ↦ (hball y hy).2.le) (convex_ball _ _) (Metric.mem_ball_self hR0) htφ
  rw [hzero _ htW.2, ← hzero p hp] at hmv
  -- hence `‖t⁻¹ Δ + Bi (t⁻¹ r)‖ ≤ c ε ‖t⁻¹ Δ‖`
  set u := t⁻¹ • Δ
  set b := Bi (t⁻¹ • r)
  have hub : ‖u + b‖ ≤ c * ε * ‖u‖ := by
    have h1 : u + b = Bi (t⁻¹ • (r + B Δ)) := by
      simp only [u, b, smul_add, map_add, map_smul, hBi]
      abel
    have h2 : ‖r + B Δ‖ ≤ ε * ‖Δ‖ := by
      have : Φ (p, φ p) - Φ (p + t • q, φ p) - B Δ = -(r + B Δ) := by simp only [r]; abel
      rw [this, norm_neg] at hmv
      exact hmv
    rw [h1]
    calc ‖Bi (t⁻¹ • (r + B Δ))‖ ≤ ‖Bi‖ * ‖t⁻¹ • (r + B Δ)‖ := Bi.le_opNorm _
      _ ≤ c * ‖t⁻¹ • (r + B Δ)‖ := by gcongr; linarith
      _ = c * (|t⁻¹| * ‖r + B Δ‖) := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ c * (|t⁻¹| * (ε * ‖Δ‖)) := by gcongr
      _ = c * ε * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]; ring
  have hbM : ‖b‖ ≤ M := by
    have : ‖b - Bi a‖ < 1 := by
      rw [← dist_eq_norm]; exact htR.trans_le (min_le_left _ _)
    calc ‖b‖ = ‖(b - Bi a) + Bi a‖ := by abel_nf
      _ ≤ ‖b - Bi a‖ + ‖Bi a‖ := norm_add_le _ _
      _ ≤ M := by simp only [M]; linarith
  have hu : ‖u‖ ≤ 2 * M := by
    have : ‖u‖ ≤ c * ε * ‖u‖ + M :=
      calc ‖u‖ = ‖(u + b) - b‖ := by abel_nf
        _ ≤ ‖u + b‖ + ‖b‖ := norm_sub_le _ _
        _ ≤ c * ε * ‖u‖ + M := add_le_add hub hbM
    nlinarith [norm_nonneg u]
  rw [dist_eq_norm]
  calc ‖u - -Bi a‖ = ‖(u + b) - (b - Bi a)‖ := by abel_nf
    _ ≤ ‖u + b‖ + ‖b - Bi a‖ := norm_sub_le _ _
    _ < δ / 4 * 2 + δ / 2 := by
      have h3 : ‖b - Bi a‖ < δ / 2 := by
        rw [← dist_eq_norm]; exact htR.trans_le (min_le_right _ _)
      have h4 : ‖u + b‖ ≤ δ / 4 * 2 := by
        calc ‖u + b‖ ≤ c * ε * ‖u‖ := hub
          _ ≤ c * ε * (2 * M) := by gcongr
          _ = 2 * (c * ε) * M := by ring
          _ ≤ δ / 4 := hcεM
          _ ≤ δ / 4 * 2 := by linarith
      linarith
    _ = δ := by ring

/-- **`∂₂Φ` is `C^k` for `C^{k+1}` maps `Φ`**, as a map into `F →L[ℝ] F` with the operator
norm.
Since `F` is finite-dimensional, `∂₂Φ(z) = ∑ᵢ cᵢ ⊗ dΦ(z)(0, bᵢ)` for a basis `bᵢ` with
coordinate functionals `cᵢ`. -/
theorem ContDiffMBOn.contDiffMBOn_partialFDeriv₂ {k : ℕ} {Φ : E × F → F} {U : Set (E × F)}
    (hU : IsOpen U) (hΦ : ContDiffMBOn (k + 1) Φ U) :
    ContDiffMBOn k (partialFDeriv₂ Φ) U := by
  set b := Module.finBasis ℝ F
  set c : Fin (Module.finrank ℝ F) → F →L[ℝ] ℝ := fun i ↦
    LinearMap.toContinuousLinearMap (b.coord i)
  have hΦ1 : ContDiffMBOn 1 Φ U := hΦ.of_le (by omega)
  have heq : EqOn (fun z ↦ ∑ i, ContinuousLinearMap.smulRightL ℝ F F (c i) (dMB Φ (z, (0, b i))))
      (partialFDeriv₂ Φ) U := by
    intro z hz
    ext v
    have hv : partialFDeriv₂ Φ z v = ∑ i, b.repr v i • partialFDeriv₂ Φ z (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      simp only [map_smul]
    rw [hv, sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(hasFDerivAt_partialFDeriv₂ hU hΦ1 hz).2]
    simp [c]
  refine ContDiffMBOn.congr_of_isOpen hU heq (ContDiffMBOn.sum _ hU fun i _ ↦ ?_)
  have hpair : ContDiffMBOn k (fun z : E × F ↦ (z, ((0 : E), b i))) U :=
    ContDiffMBOn.prodMk hU (smoothMBOn_id U k) (contDiffMBOn_const k _ U)
  have hd : ContDiffMBOn k (fun z ↦ dMB Φ (z, ((0 : E), b i))) U :=
    ContDiffMBOn.comp (g := dMB Φ) (f := fun z : E × F ↦ (z, ((0 : E), b i))) hU
      (hU.prod isOpen_univ) hΦ.2.2 hpair fun z hz ↦ ⟨hz, mem_univ _⟩
  exact ContDiffMBOn.comp hU isOpen_univ
    ((ContinuousLinearMap.smulRightL ℝ F F (c i)).contDiffMBOn k univ) hd (mapsTo_univ _ _)

omit [FiniteDimensional ℝ F] in
/-- Inversion of operators is smooth on the open set of invertible operators. -/
theorem contDiffMBOn_ringInverse [CompleteSpace F] (k : ℕ) :
    ContDiffMBOn k (Ring.inverse : (F →L[ℝ] F) → F →L[ℝ] F) {L | IsUnit L} := by
  refine ContDiffOn.contDiffMBOn Units.isOpen fun L hL ↦ ?_
  have := contDiffAt_ringInverse ℝ (n := (k : WithTop ℕ∞)) hL.unit
  rw [hL.unit_spec] at this
  exact this.contDiffWithinAt

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [FiniteDimensional ℝ F] in
/-- The evaluation `(L, w) ↦ L w` is smooth. -/
theorem contDiffMBOn_clm_apply (k : ℕ) :
    ContDiffMBOn k (fun x : (F →L[ℝ] F) × F ↦ x.1 x.2) univ :=
  ContDiffOn.contDiffMBOn isOpen_univ isBoundedBilinearMap_apply.contDiff.contDiffOn

/-- **Implicit functions are `C^k`.** Let `Φ : E × F → F` be `C^k` on an open set `U`, with `E`
locally convex and `F` finite-dimensional. If `φ` is continuous on an open set `P ⊆ E`, with
`(p, φ(p)) ∈ U`, `Φ(p, φ(p)) = 0` and `∂₂Φ(p, φ(p))` invertible for `p ∈ P`, then `φ` is `C^k` on
`P` (cf. [GN26, Theorem 2.3.40]). -/
theorem contDiffMBOn_of_implicit {k : ℕ} {Φ : E × F → F} {U : Set (E × F)} (hU : IsOpen U)
    (hΦ : ContDiffMBOn k Φ U) {P : Set E} (hP : IsOpen P) {φ : E → F}
    (hφ : ContinuousOn φ P) (hmaps : ∀ p ∈ P, (p, φ p) ∈ U) (hzero : ∀ p ∈ P, Φ (p, φ p) = 0)
    (hB : ∀ p ∈ P, IsUnit (partialFDeriv₂ Φ (p, φ p))) : ContDiffMBOn k φ P := by
  suffices h : ∀ j ≤ k, ContDiffMBOn j φ P from h k le_rfl
  intro j
  induction j with
  | zero => intro _; exact hφ
  | succ j ih =>
    intro hj
    have hφj := ih (by omega)
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hΦ1 : ContDiffMBOn 1 Φ U := hΦ.of_le (by omega)
    set D : E × E → F := fun x ↦
      -(Ring.inverse (partialFDeriv₂ Φ (x.1, φ x.1))) (dMB Φ ((x.1, φ x.1), (x.2, 0)))
    have hd : ∀ p ∈ P, ∀ q, HasDirDerivAt φ p q (D (p, q)) := fun p hp q ↦
      hasDirDerivAt_of_implicit hU hΦ1 hP hφ hmaps hzero hp (hB p hp) q
    have heq : EqOn D (dMB φ) (P ×ˢ univ) := fun x hx ↦ (hd x.1 hx.1 x.2).dMB_eq.symm
    have hPP : IsOpen (P ×ˢ (univ : Set E)) := hP.prod isOpen_univ
    -- the pieces of the formula for `D`
    have hfstφ : ContDiffMBOn j (φ ∘ ContinuousLinearMap.fst ℝ E E) (P ×ˢ univ) := by
      have := ContDiffMBOn.comp_clm (ContinuousLinearMap.fst ℝ E E) hP hφj
      have hpre : (ContinuousLinearMap.fst ℝ E E) ⁻¹' P = P ×ˢ univ := by ext; simp
      rwa [hpre] at this
    have hg0 : ContDiffMBOn j (fun x : E × E ↦ (x.1, φ x.1)) (P ×ˢ univ) :=
      ContDiffMBOn.prodMk hPP ((ContinuousLinearMap.fst ℝ E E).contDiffMBOn j _) hfstφ
    have hg1 : ContDiffMBOn j (fun x : E × E ↦ ((x.1, φ x.1), (x.2, (0 : F)))) (P ×ˢ univ) :=
      ContDiffMBOn.prodMk hPP hg0 (ContDiffMBOn.prodMk hPP
        ((ContinuousLinearMap.snd ℝ E E).contDiffMBOn j _) (contDiffMBOn_const j _ _))
    have hA : ContDiffMBOn j (fun x : E × E ↦ partialFDeriv₂ Φ (x.1, φ x.1)) (P ×ˢ univ) :=
      ContDiffMBOn.comp hPP hU ((hΦ.contDiffMBOn_partialFDeriv₂ hU).of_le (by omega)) hg0
        fun x hx ↦ hmaps x.1 hx.1
    have hAi : ContDiffMBOn j (fun x : E × E ↦ Ring.inverse (partialFDeriv₂ Φ (x.1, φ x.1)))
        (P ×ˢ univ) :=
      ContDiffMBOn.comp hPP Units.isOpen (contDiffMBOn_ringInverse j) hA
        fun x hx ↦ hB x.1 hx.1
    have hw : ContDiffMBOn j (fun x : E × E ↦ dMB Φ ((x.1, φ x.1), (x.2, (0 : F))))
        (P ×ˢ univ) :=
      ContDiffMBOn.comp (g := dMB Φ) (f := fun x : E × E ↦ ((x.1, φ x.1), (x.2, (0 : F)))) hPP
        (hU.prod isOpen_univ) (hΦ.2.2.of_le (by omega)) hg1
        fun x hx ↦ ⟨hmaps x.1 hx.1, mem_univ _⟩
    have happ := ContDiffMBOn.comp hPP isOpen_univ (contDiffMBOn_clm_apply j)
      (ContDiffMBOn.prodMk hPP hAi hw) (mapsTo_univ _ _)
    have hD : ContDiffMBOn j D (P ×ˢ univ) :=
      ContDiffMBOn.congr_of_isOpen hPP (fun x _ ↦ by simp [D])
        (ContDiffMBOn.comp hPP isOpen_univ ((-ContinuousLinearMap.id ℝ F).contDiffMBOn j univ)
          happ (mapsTo_univ _ _))
    refine ⟨hφ, fun p hp q ↦ ?_, ContDiffMBOn.congr_of_isOpen hPP heq hD⟩
    rw [← heq ⟨hp, mem_univ q⟩]
    exact hd p hp q

/-- **Implicit functions of smooth maps are smooth.** -/
theorem smoothMBOn_of_implicit {Φ : E × F → F} {U : Set (E × F)} (hU : IsOpen U)
    (hΦ : SmoothMBOn Φ U) {P : Set E} (hP : IsOpen P) {φ : E → F}
    (hφ : ContinuousOn φ P) (hmaps : ∀ p ∈ P, (p, φ p) ∈ U) (hzero : ∀ p ∈ P, Φ (p, φ p) = 0)
    (hB : ∀ p ∈ P, IsUnit (partialFDeriv₂ Φ (p, φ p))) : SmoothMBOn φ P := fun k ↦
  contDiffMBOn_of_implicit hU (hΦ k) hP hφ hmaps hzero hB

end LocallyConvex.Analysis

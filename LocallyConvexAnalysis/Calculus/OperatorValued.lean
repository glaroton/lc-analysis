/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.BoundedBelow
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Operator-valued maps on locally convex spaces

Let `E` be a locally convex space, `F₁`, `F₂` normed spaces and `g : U → L(F₁, F₂)`, with
`U ⊆ E` open. We show that if the uncurried map `ĝ(y, ξ) = g(y) ξ` is `C^{k+1}` in the sense of
Michal–Bastiani, then `g` is `C^k` as a map into `L(F₁, F₂)` **with the operator norm**. This
extends `contDiffOn_of_unc` (where `E` is normed and `F₁ = E`) to locally convex domains.

The point of the statement is that the operator norm topology is much finer than the topology of
pointwise convergence, and joint smoothness of `ĝ` must be turned into uniform estimates on the
unit ball of `F₁`. This uses only that `F₁` is normed: the derivative
`D(y, ξ, w) = ∂_w ĝ(y, ξ)` is linear in `ξ` and continuous at `(y₀, 0, 0)`, so it is bounded by
`C ‖ξ‖` for `y` near `y₀` and `w` in a neighborhood of `0`; the mean value inequality then gives
`‖g(y) − g(y₀)‖ ≤ ε`. The derivative of `g` in the direction `w` is the operator
`ξ ↦ D(y, ξ, w)`, and the induction runs over the domain `E × E` of the derivative.

## Main results

* `exists_bound_unc_clm`: the derivative `D(y, ξ, w)` is bounded by `C ‖ξ‖` for `y` near `y₀` and
  `w` in a neighborhood of `0`.
* `continuousOn_of_unc_clm`: if `ĝ` is `C^1`, then `g` is continuous for the operator norm.
* `hasDirDerivAt_of_unc_clm`: if `ĝ` is `C^1` and the operators `h(y, w) = (ξ ↦ D(y, ξ, w))`
  depend continuously on `(y, w)` for the operator norm, then `h(y, w)` is the derivative of `g`
  at `y` in the direction `w`, for the operator norm.
* `contDiffMBOn_of_unc_clm`: if `ĝ` is `C^{k+1}` on `U × F₁`, then `g : U → L(F₁, F₂)` is `C^k`
  for the operator norm.

## Implementation notes

If `F₁` is not normable, the corresponding statement is meaningless: no vector topology on
`L(F₁, F₂)` makes the evaluation continuous (Maissen, Math. Ann. 151 (1963),
Satz 1). No completeness is assumed.
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

variable {F₁ : Type v} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

section Fixed

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {g : E → F₁ →L[ℝ] F₂} {U : Set E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The derivative of a slice `z ↦ g(z) ξ`, in terms of the derivative of the uncurried map. -/
theorem hasDirDerivAt_slice_of_unc_clm
    (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) {y : E} (hy : y ∈ U)
    (ξ : F₁) (w : E) :
    HasDirDerivAt (fun z ↦ g z ξ) y w (dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0))) :=
  hasDirDerivAt_slice.mp (hg.2.1 (y, ξ) ⟨hy, mem_univ _⟩ (w, 0))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The derivative `D(y, ξ, w)` is homogeneous in `ξ`. -/
theorem dMB_unc_clm_smul (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ))
    {y : E} (hy : y ∈ U) (c : ℝ) (ξ : F₁) (w : E) :
    dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, c • ξ), (w, 0)) =
      c • dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0)) := by
  have h1 := hasDirDerivAt_slice_of_unc_clm hg hy (c • ξ) w
  have h2 := (hasDirDerivAt_slice_of_unc_clm hg hy ξ w).const_smul c
  simp only [map_smul] at h1
  exact tendsto_nhds_unique h1 h2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The derivative `D(y, ξ, w)` is additive in `ξ`. -/
theorem dMB_unc_clm_add (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ))
    {y : E} (hy : y ∈ U) (ξ η : F₁) (w : E) :
    dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ + η), (w, 0)) =
      dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0)) +
        dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, η), (w, 0)) := by
  have h1 := hasDirDerivAt_slice_of_unc_clm hg hy (ξ + η) w
  have h2 := (hasDirDerivAt_slice_of_unc_clm hg hy ξ w).add
    (hasDirDerivAt_slice_of_unc_clm hg hy η w)
  simp only [map_add] at h1
  exact tendsto_nhds_unique h1 h2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The line through `y₀` in the direction `w`, differentiated at `s`. -/
theorem hasDerivAt_line_of_unc_clm
    (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) {y₀ w : E} {s : ℝ}
    (hs : y₀ + s • w ∈ U) (ξ : F₁) :
    HasDerivAt (fun t : ℝ ↦ g (y₀ + t • w) ξ)
      (dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀ + s • w, ξ), (w, 0))) s := by
  have h := hasDerivAt_line_of_hasDirDerivAt (hasDirDerivAt_slice_of_unc_clm hg hs ξ w)
  have h0 : HasDerivAt (fun t : ℝ ↦ g (y₀ + s • w + t • w) ξ)
      (dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀ + s • w, ξ), (w, 0))) (s + -s) := by
    simpa using h
  have h' := HasDerivAt.comp_add_const s (-s) h0
  convert h' using 1
  funext t
  simp only [add_smul, neg_smul]
  congr 2
  abel

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] in
/-- **A uniform bound for the derivative**: near `y₀`, and for `w` near `0`,
`‖D(y, ξ, w)‖ ≤ C ‖ξ‖`. This uses that `D` is linear in `ξ` and continuous at `(y₀, 0, 0)`. -/
theorem exists_bound_unc_clm (hU : IsOpen U)
    (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ N ∈ 𝓝 y₀, Convex ℝ N ∧ N ⊆ U ∧ ∃ W ∈ 𝓝 (0 : E), ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ N, ∀ w ∈ W, ∀ ξ : F₁,
        ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0))‖ ≤ C * ‖ξ‖ := by
  have hopen : IsOpen ((U ×ˢ (univ : Set F₁)) ×ˢ (univ : Set (E × F₁))) :=
    (hU.prod isOpen_univ).prod isOpen_univ
  have hcont : ContinuousAt (dMB (fun p : E × F₁ ↦ g p.1 p.2))
      ((y₀, (0 : F₁)), ((0 : E), (0 : F₁))) :=
    (hg.2.2 : ContinuousOn (dMB (fun p : E × F₁ ↦ g p.1 p.2)) _).continuousAt
      (hopen.mem_nhds ⟨⟨hy₀, mem_univ _⟩, mem_univ _⟩)
  have hD0 : dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀, 0), (0, 0)) = 0 := by
    have := dMB_unc_clm_smul hg hy₀ 0 0 0
    rw [zero_smul, zero_smul] at this
    exact this
  have hev : ∀ᶠ q in 𝓝 ((y₀, (0 : F₁)), ((0 : E), (0 : F₁))),
      ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) q‖ < 1 := by
    have h1 : ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀, 0), (0, 0))‖ < 1 := by
      rw [hD0, norm_zero]; exact one_pos
    exact hcont.norm.eventually (gt_mem_nhds h1)
  have hφ : Continuous fun p : E × (F₁ × E) ↦ ((p.1, p.2.1), (p.2.2, (0 : F₁))) := by fun_prop
  have hev' : ∀ᶠ p in 𝓝 (y₀, ((0 : F₁), (0 : E))),
      ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((p.1, p.2.1), (p.2.2, 0))‖ < 1 :=
    (hφ.tendsto (y₀, ((0 : F₁), (0 : E)))).eventually hev
  obtain ⟨A, hA, B', hB', hAB⟩ := mem_nhds_prod_iff.mp hev'
  obtain ⟨B, hB, W, hW, hBW⟩ := mem_nhds_prod_iff.mp hB'
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hB
  obtain ⟨N, ⟨hN, hNc⟩, hNsub⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) y₀).mem_iff.mp (inter_mem hA (hU.mem_nhds hy₀))
  refine ⟨N, hN, hNc, fun y hy ↦ (hNsub hy).2, W, hW, 2 / δ, by positivity, ?_⟩
  intro y hy w hw ξ
  have hyU : y ∈ U := (hNsub hy).2
  by_cases hξ : ξ = 0
  · have := dMB_unc_clm_smul hg hyU 0 0 w
    rw [zero_smul, zero_smul] at this
    rw [hξ, this, norm_zero, norm_zero, mul_zero]
  have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = δ / (2 * ‖ξ‖) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hmem : (y, (c • ξ, w)) ∈ A ×ˢ B' := by
    refine ⟨(hNsub hy).1, hBW ⟨hball ?_, hw⟩⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hc.le]
    have : c * ‖ξ‖ = δ / 2 := by rw [hcdef]; field_simp
    rw [this]
    linarith
  have h1 : ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, c • ξ), (w, 0))‖ < 1 := by
    have := hAB hmem
    exact this
  rw [dMB_unc_clm_smul hg hyU c ξ w, norm_smul, Real.norm_of_nonneg hc.le] at h1
  have : ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0))‖ < 1 / c := by
    rw [lt_div_iff₀ hc]; linarith
  calc ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0))‖ ≤ 1 / c := this.le
    _ = 2 / δ * ‖ξ‖ := by rw [hcdef]; field_simp

omit [T2Space E] in
/-- **Continuity in the operator norm**: if `ĝ` is `C¹`, then `g : U → L(F₁, F₂)` is continuous
for the operator norm. -/
theorem continuousOn_of_unc_clm (hU : IsOpen U)
    (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) : ContinuousOn g U := by
  intro y₀ hy₀
  refine ContinuousAt.continuousWithinAt (Metric.tendsto_nhds.mpr fun ε hε ↦ ?_)
  obtain ⟨N, hN, hNc, hNU, W, hW, C, hC0, hbound⟩ := exists_bound_unc_clm hU hg hy₀
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = ε / (2 * (C + 1)) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; positivity
  have hS : {y | r⁻¹ • (y - y₀) ∈ W} ∈ 𝓝 y₀ := by
    have hc : Continuous fun y : E ↦ r⁻¹ • (y - y₀) := by fun_prop
    have ht : Tendsto (fun y ↦ r⁻¹ • (y - y₀)) (𝓝 y₀) (𝓝 0) :=
      hc.tendsto' y₀ 0 (by simp)
    exact ht hW
  filter_upwards [hN, hS] with y hyN hyS
  have hy₀N : y₀ ∈ N := mem_of_mem_nhds hN
  set w := y - y₀
  have hw : w = r • (r⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hbnd : ‖g y - g y₀‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ ↦ ?_
    have hseg : ∀ t ∈ Icc (0 : ℝ) 1, y₀ + t • w ∈ N := fun t ht ↦
      hNc.add_smul_sub_mem hy₀N hyN ht
    have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ ↦ g (y₀ + t • w) ξ)
        (dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀ + t • w, ξ), (w, 0))) (Icc 0 1) t :=
      fun t ht ↦ (hasDerivAt_line_of_unc_clm hg (hNU (hseg t ht)) ξ).hasDerivWithinAt
    have hb : ∀ t ∈ Ico (0 : ℝ) 1,
        ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀ + t • w, ξ), (w, 0))‖ ≤ ε / 2 * ‖ξ‖ := by
      intro t ht
      have hp := hseg t (Ico_subset_Icc_self ht)
      have hsm := hg.dMB_smul (x := (y₀ + t • w, ξ)) ⟨hNU hp, mem_univ _⟩ r (r⁻¹ • w, 0)
      rw [Prod.smul_mk, smul_zero, ← hw] at hsm
      rw [hsm, norm_smul, Real.norm_of_nonneg hr.le]
      have := hbound _ hp _ hyS ξ
      calc r * ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y₀ + t • w, ξ), (r⁻¹ • w, 0))‖
          ≤ r * (C * ‖ξ‖) := by gcongr
        _ ≤ ε / 2 * ‖ξ‖ := by
          rw [← mul_assoc]
          gcongr
          have : r * C ≤ r * (C + 1) := by nlinarith
          calc r * C ≤ r * (C + 1) := this
            _ = ε / 2 := by rw [hrdef]; field_simp
    have := norm_image_sub_le_of_norm_deriv_le_segment' hf hb 1 ⟨zero_le_one, le_rfl⟩
    simpa [w] using this
  rw [dist_eq_norm]
  linarith

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **The derivative in the operator norm**: if `ĝ` is `C¹` and `h(y, w) ξ = ∂_w ĝ(y, ξ)` defines
a map `h : U × E → L(F₁, F₂)` continuous for the operator norm, then `h(y, w)` is the directional
derivative of `g` at `y` in the direction `w`, for the operator norm. -/
theorem hasDirDerivAt_of_unc_clm (hU : IsOpen U)
    (hg : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) {h : E × E → F₁ →L[ℝ] F₂}
    (hh : ∀ y ∈ U, ∀ w ξ, h (y, w) ξ = dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0)))
    (hhc : ContinuousOn h (U ×ˢ univ)) {y : E} (hy : y ∈ U) (w : E) :
    HasDirDerivAt g y w (h (y, w)) := by
  unfold HasDirDerivAt
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hcs : ContinuousAt (fun s : ℝ ↦ h (y + s • w, w)) 0 := by
    have h1 : ContinuousAt h (y + (0 : ℝ) • w, w) := by
      rw [zero_smul, add_zero]
      exact hhc.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩)
    exact ContinuousAt.comp (g := h) (f := fun s : ℝ ↦ (y + s • w, w)) h1 (by fun_prop)
  have hline : ContinuousAt (fun s : ℝ ↦ y + s • w) 0 := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), y + s • w ∈ U ∧ ‖h (y + s • w, w) - h (y, w)‖ < ε / 2 := by
    refine (hline.eventually (hU.mem_nhds (by simpa using hy))).and ?_
    have := (hcs.eventually (Metric.ball_mem_nhds (h (y + (0 : ℝ) • w, w)) (half_pos hε)))
    filter_upwards [this] with s hs
    simpa [dist_eq_norm] using hs
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun {t} ht htδ ↦ ?_⟩
  have ht0 : t ≠ 0 := ht
  have hseg : ∀ s ∈ uIcc 0 t, dist s 0 < δ := fun s hs ↦ by
    rw [Real.dist_eq, sub_zero]
    calc |s| = |s - 0| := by rw [sub_zero]
      _ ≤ |t - 0| := abs_sub_left_of_mem_uIcc hs
      _ = dist t 0 := by rw [Real.dist_eq]
      _ < δ := htδ
  have hbnd : ‖t⁻¹ • (g (y + t • w) - g y) - h (y, w)‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ ↦ ?_
    set ψ : ℝ → F₂ := fun s ↦ g (y + s • w) ξ - s • h (y, w) ξ
    have hψ : ∀ s ∈ uIcc 0 t, HasDerivWithinAt ψ
        (dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y + s • w, ξ), (w, 0)) - h (y, w) ξ) (uIcc 0 t) s := by
      intro s hs
      have h1 := hasDerivAt_line_of_unc_clm hg (hδP (hseg s hs)).1 ξ
      have h2 := (hasDerivAt_id s).smul_const (h (y, w) ξ)
      have h3 := (h1.sub h2).hasDerivWithinAt (s := uIcc 0 t)
      rw [one_smul] at h3
      exact h3
    have hψb : ∀ s ∈ uIcc 0 t,
        ‖dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y + s • w, ξ), (w, 0)) - h (y, w) ξ‖ ≤
          ε / 2 * ‖ξ‖ := by
      intro s hs
      obtain ⟨hsU, hsn⟩ := hδP (hseg s hs)
      rw [← hh _ hsU]
      change ‖(h (y + s • w, w) - h (y, w)) ξ‖ ≤ _
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hψ hψb (convex_uIcc 0 t)
      left_mem_uIcc right_mem_uIcc
    have heq : (t⁻¹ • (g (y + t • w) - g y) - h (y, w)) ξ = t⁻¹ • (ψ t - ψ 0) := by
      simp only [ψ, FunLike.coe_sub, Pi.sub_apply, smul_apply,
        zero_smul, add_zero, sub_zero, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      abel
    rw [heq, norm_smul, norm_inv, sub_zero] at *
    calc ‖t‖⁻¹ * ‖ψ t - ψ 0‖ ≤ ‖t‖⁻¹ * (ε / 2 * ‖ξ‖ * ‖t‖) := by gcongr
      _ = ε / 2 * ‖ξ‖ := by field_simp
  rw [dist_eq_norm]
  linarith

end Fixed

/-- **Operator-valued maps**: let `E` be locally convex and `F₁`, `F₂` normed. If
`ĝ(y, ξ) = g(y) ξ` is `C^{k+1}` on `U × F₁` in the sense of Michal–Bastiani, then
`g : U → L(F₁, F₂)` is `C^k` for the operator norm. -/
theorem contDiffMBOn_of_unc_clm : ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {g : E → F₁ →L[ℝ] F₂} {U : Set E}, IsOpen U →
    ContDiffMBOn (k + 1) (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ) → ContDiffMBOn k g U := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ _ _ _ g U hU hg
    exact continuousOn_of_unc_clm hU hg
  | succ k ih =>
    intro E _ _ _ _ _ _ _ g U hU hg
    classical
    have hg1 : ContDiffMBOn 1 (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ) := hg.of_le (by omega)
    have hD : ContinuousOn (dMB (fun p : E × F₁ ↦ g p.1 p.2)) ((U ×ˢ univ) ×ˢ univ) := hg1.2.2
    -- the derivative of `g`, as an operator-valued map on `U × E`
    let hop : ∀ q : E × E, q.1 ∈ U → F₁ →L[ℝ] F₂ := fun q hq ↦
      { toFun := fun ξ ↦ dMB (fun p : E × F₁ ↦ g p.1 p.2) ((q.1, ξ), (q.2, 0))
        map_add' := fun ξ η ↦ dMB_unc_clm_add hg1 hq ξ η q.2
        map_smul' := fun c ξ ↦ dMB_unc_clm_smul hg1 hq c ξ q.2
        cont := hD.comp_continuous (by fun_prop) fun ξ ↦ ⟨⟨hq, mem_univ _⟩, mem_univ _⟩ }
    let h : E × E → F₁ →L[ℝ] F₂ := fun q ↦ if hq : q.1 ∈ U then hop q hq else 0
    have hh : ∀ y ∈ U, ∀ w ξ, h (y, w) ξ = dMB (fun p : E × F₁ ↦ g p.1 p.2) ((y, ξ), (w, 0)) :=
      fun y hy w ξ ↦ by simp [h, hy, hop]
    have hUE : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
    -- the uncurried derivative is `C^{k+1}`
    let L : (E × E) × F₁ →L[ℝ] (E × F₁) × (E × F₁) :=
      (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) F₁)).prod
        (ContinuousLinearMap.snd ℝ (E × E) F₁)).prod
      (((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) F₁)).prod 0)
    have hcomp : ContDiffMBOn (k + 1) (dMB (fun p : E × F₁ ↦ g p.1 p.2) ∘ L)
        ((U ×ˢ univ) ×ˢ univ) :=
      ContDiffMBOn.comp (hUE.prod isOpen_univ) ((hU.prod isOpen_univ).prod isOpen_univ) hg.2.2
        (L.contDiffMBOn _ _) fun p hp ↦ ⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩
    have hĥ : ContDiffMBOn (k + 1) (fun p : (E × E) × F₁ ↦ h p.1 p.2) ((U ×ˢ univ) ×ˢ univ) :=
      ContDiffMBOn.congr_of_isOpen (hUE.prod isOpen_univ)
        (fun p hp ↦ by rw [hh _ hp.1.1]; rfl) hcomp
    have hhk : ContDiffMBOn k h (U ×ˢ univ) := ih hUE hĥ
    have hhc : ContinuousOn h (U ×ˢ univ) := continuousOn_of_unc_clm hUE (hĥ.of_le (by omega))
    have hder : ∀ y ∈ U, ∀ w, HasDirDerivAt g y w (h (y, w)) :=
      fun y hy w ↦ hasDirDerivAt_of_unc_clm hU hg1 hh hhc hy w
    refine ⟨continuousOn_of_unc_clm hU hg1, fun y hy w ↦ ?_, ?_⟩
    · rw [(hder y hy w).dMB_eq]
      exact hder y hy w
    · exact ContDiffMBOn.congr_of_isOpen hUE (fun q hq ↦ ((hder q.1 hq.1 q.2).dMB_eq).symm) hhk

end LocallyConvex.Analysis

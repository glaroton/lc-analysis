/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import LocallyConvexAnalysis.Krein.HilbertComplexification
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Spectral projections and positive and negative parts of self-adjoint operators

Spectral facts on self-adjoint operators of real or complex Hilbert spaces, used in
`LocallyConvexAnalysis.Krein.OrthoComplemented` for the Gram operator of a subspace of a Krein
space. Mathlib's continuous functional calculus is available for complex C⋆-algebras only, so
for real spaces the results are obtained from the complexification
(`LocallyConvexAnalysis.Krein.HilbertComplexification`).

## Main results

* `exists_spectral_projection`: an invertible self-adjoint operator of a real or complex Hilbert
  space has a spectral projection onto its positive part, with `±⟪G x, x⟫ ≥ c ‖x‖²` on the range
  and the kernel; over `ℝ` through the complexification (`Metric/HilbertComplexification.lean`).
* `exists_posPart_negPart`, `exists_sign_decomposition`: a self-adjoint operator `G` of a real or
  complex Hilbert space, not necessarily invertible, has positive and negative parts
  `G = G⁺ - G⁻`, `G⁺ G⁻ = 0` (continuous functional calculus; over `ℝ` through the
  complexification and the uniqueness of `G^±`), and `E = ker G ⊕ (ker G⁺)^⊥ ⊕ (ker G⁻)^⊥` with
  all three components and all sums of two of them closed, `⟪G x, x⟫` positive definite on the
  second and negative definite on the third.

## References

* [J. Bognár, *Indefinite Inner Product Spaces*][Bog74]
-/

@[expose] public section

open Filter RCLike
open scoped Topology InnerProductSpace ComplexConjugate

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Spectral projections of an invertible self-adjoint operator -/

namespace FundamentalSymmetry

section Spectral

/-- Spectral bound: if `c f ≤ s t f` on the spectrum of the self-adjoint `G` and `x` is fixed by
`f(G)`, then `c ‖x‖² ≤ s re ⟪G x, x⟫`. -/
theorem le_re_inner_of_cfc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {G : E →L[ℂ] E} (hG : IsSelfAdjoint G) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ G)) (c s : ℝ)
    (hb : ∀ t ∈ spectrum ℝ G, c * f t ≤ s * (t * f t)) (x : E) (hx : cfc f G x = x) :
    c * ‖x‖ ^ 2 ≤ s * Complex.re ⟪G x, x⟫_ℂ := by
  have hid : ContinuousOn (fun t : ℝ ↦ t) (spectrum ℝ G) := continuousOn_id
  have hle := cfc_mono (a := G) hb (hf.const_smul c) ((hid.mul hf).const_smul s)
  rw [cfc_const_mul c f G hf, cfc_const_mul s (fun t ↦ t * f t) G (hid.mul hf),
    cfc_mul (fun t : ℝ ↦ t) f G hid hf, cfc_id' ℝ G] at hle
  have := (ContinuousLinearMap.le_def.1 hle).re_inner_nonneg_left x
  have e1 : ((s • (G * cfc f G) - c • cfc f G) x) = (s : ℂ) • G x - (c : ℂ) • x := by
    simp [hx, ← Complex.coe_smul]
  rw [e1, inner_sub_left, inner_smul_left, inner_smul_left] at this
  simp only [Complex.conj_ofReal, map_sub, inner_self_eq_norm_sq_to_K] at this
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at this
  have e2 : (((‖x‖ ^ 2 : ℝ)) : ℂ).re = ‖x‖ ^ 2 := Complex.ofReal_re _
  norm_cast at this
  erw [e2] at this
  linarith

/-- **Spectral splitting of an invertible self-adjoint operator**, complex case (continuous
functional calculus): there are a self-adjoint idempotent `P` and `c > 0` such that
`re ⟪G x, x⟫ ≥ c ‖x‖²` on the range of `P` and `≤ -c ‖x‖²` on its kernel; `P` commutes with every
operator commuting with `G`, in particular with `G`. `P` is the spectral projection of `G` onto
`(0, ∞)`, and `c` the distance from `0` to the spectrum. -/
theorem exists_spectral_projection_complex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {G : E →L[ℂ] E} (hGsa : IsSelfAdjoint G)
    (hunit : IsUnit G) :
    ∃ P : E →L[ℂ] E, ∃ c > 0, (∀ x, P (P x) = P x) ∧ (∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ) ∧
      (∀ x, G (P x) = P (G x)) ∧ (∀ x, P x = x → c * ‖x‖ ^ 2 ≤ Complex.re ⟪G x, x⟫_ℂ) ∧
      (∀ x, P x = 0 → c * ‖x‖ ^ 2 ≤ -Complex.re ⟪G x, x⟫_ℂ) ∧
      (∀ T : E →L[ℂ] E, (∀ x, G (T x) = T (G x)) → ∀ x, P (T x) = T (P x)) ∧
      P = cfc (fun t : ℝ ↦ if 0 < t then 1 else 0) G := by
  have h0 : (0 : ℝ) ∉ spectrum ℝ G := (spectrum.zero_notMem_iff ℝ).2 hunit
  obtain ⟨c, hc, hball⟩ := Metric.isOpen_iff.1 (spectrum.isClosed (𝕜 := ℝ) G).isOpen_compl 0 h0
  have hcabs : ∀ t ∈ spectrum ℝ G, c ≤ |t| := fun t ht ↦ by
    by_contra h
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h) ht
  have hne : ∀ t ∈ spectrum ℝ G, t ≠ 0 := fun t ht h ↦ h0 (h ▸ ht)
  -- the indicator functions of the half-lines, continuous on the spectrum
  let f : ℝ → ℝ := fun t ↦ if 0 < t then 1 else 0
  let g : ℝ → ℝ := fun t ↦ if t < 0 then 1 else 0
  have hcont : ∀ k : ℝ → ℝ, (∀ t, 0 < t → k t = k 1) → (∀ t, t < 0 → k t = k (-1)) →
      ContinuousOn k (spectrum ℝ G) := fun k hpos hneg t ht ↦ by
    refine ContinuousAt.continuousWithinAt ?_
    rcases (hne t ht).lt_or_gt with h | h
    · exact continuousAt_const.congr (by
        filter_upwards [eventually_lt_nhds h] with s hs using (hneg s hs).symm)
    · exact continuousAt_const.congr (by
        filter_upwards [eventually_gt_nhds h] with s hs using (hpos s hs).symm)
  have hf : ContinuousOn f (spectrum ℝ G) :=
    hcont f (fun t ht ↦ by simp [f, ht]) fun t ht ↦ by simp [f, ht.le.not_gt]
  have hg : ContinuousOn g (spectrum ℝ G) :=
    hcont g (fun t ht ↦ by simp [g, ht.le.not_gt]) fun t ht ↦ by simp [g, ht]
  set P := cfc f G with hPdef
  have hPP : ∀ x, P (P x) = P x := fun x ↦ by
    have : P * P = P := by
      rw [hPdef, ← cfc_mul f f G hf hf]
      exact cfc_congr fun t _ ↦ by by_cases h : 0 < t <;> simp [f, h]
    exact congrArg (fun T : E →L[ℂ] E ↦ T x) this
  have hPsa : ∀ x y, ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (cfc_predicate f G)
  have hGP : ∀ x, G (P x) = P (G x) := fun x ↦ by
    have := cfc_commute_cfc (fun t : ℝ ↦ t) f G
    rw [cfc_id' ℝ G] at this
    exact congrArg (fun T : E →L[ℂ] E ↦ T x) this.eq
  have hPN : ∀ x, P x + cfc g G x = x := fun x ↦ by
    have : P + cfc g G = 1 := by
      rw [hPdef, ← cfc_add (a := G) f g hf hg, ← cfc_one ℝ G]
      refine cfc_congr fun t ht ↦ ?_
      rcases (hne t ht).lt_or_gt with h | h
      · simp [f, g, h, h.not_gt]
      · simp [f, g, h, h.not_gt]
    exact congrArg (fun T : E →L[ℂ] E ↦ T x) this
  have hcomm : ∀ T : E →L[ℂ] E, (∀ x, G (T x) = T (G x)) → ∀ x, P (T x) = T (P x) :=
    fun T hT x ↦ by
      have hc : Commute G T := ContinuousLinearMap.ext fun y ↦ hT y
      exact congrArg (fun A : E →L[ℂ] E ↦ A x) (hc.cfc_real f).eq
  refine ⟨P, c, hc, hPP, hPsa, hGP, fun x hx ↦ ?_, fun x hx ↦ ?_, hcomm, hPdef⟩
  · have := le_re_inner_of_cfc hGsa f hf c 1 (fun t ht ↦ by
      by_cases h : 0 < t
      · simpa [f, h, abs_of_pos h] using hcabs t ht
      · simp [f, h]) x hx
    rwa [one_mul] at this
  · have hx' : cfc g G x = x := by have := hPN x; rwa [hx, zero_add] at this
    have := le_re_inner_of_cfc hGsa g hg c (-1) (fun t ht ↦ by
      by_cases h : t < 0
      · simpa [g, h, abs_of_neg h] using hcabs t ht
      · simp [g, h]) x hx'
    rwa [neg_one_mul] at this

/-- Two commuting idempotents `P`, `Q` with the same sign bounds for `G` (`re ⟪G x, x⟫ ≥ c ‖x‖²`
on the ranges, `≤ -c ‖x‖²` on the kernels) coincide. -/
theorem eq_of_spectral_bounds {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {G P Q : E →L[ℂ] E} {c : ℝ} (hc : 0 < c)
    (hPP : ∀ x, P (P x) = P x) (hQQ : ∀ x, Q (Q x) = Q x) (hPQ : ∀ x, P (Q x) = Q (P x))
    (hPpos : ∀ x, P x = x → c * ‖x‖ ^ 2 ≤ Complex.re ⟪G x, x⟫_ℂ)
    (hPneg : ∀ x, P x = 0 → c * ‖x‖ ^ 2 ≤ -Complex.re ⟪G x, x⟫_ℂ)
    (hQpos : ∀ x, Q x = x → c * ‖x‖ ^ 2 ≤ Complex.re ⟪G x, x⟫_ℂ)
    (hQneg : ∀ x, Q x = 0 → c * ‖x‖ ^ 2 ≤ -Complex.re ⟪G x, x⟫_ℂ) (x : E) : P x = Q x := by
  have hzero : ∀ y : E, c * ‖y‖ ^ 2 ≤ Complex.re ⟪G y, y⟫_ℂ →
      c * ‖y‖ ^ 2 ≤ -Complex.re ⟪G y, y⟫_ℂ → y = 0 := by
    intro y h1 h2
    have h3 : ‖y‖ ^ 2 ≤ 0 := by
      by_contra h
      have := mul_pos hc (lt_of_not_ge h)
      linarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h3 (sq_nonneg _)))
  have h1 : P (x - Q x) = 0 :=
    hzero _ (hPpos _ (hPP _)) (hQneg _ (by rw [← hPQ, map_sub Q, hQQ, sub_self, map_zero]))
  have h2 : Q (x - P x) = 0 :=
    hzero _ (hQpos _ (hQQ _)) (hPneg _ (by rw [hPQ, map_sub P, hPP, sub_self, map_zero]))
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, hPQ, ← h2]

open HilbertComplexification in
/-- **Restriction of a real operator on the complexification.** A `ℂ`-linear operator `P₀` on
`E_ℂ` commuting with the conjugation and with the complexification of the multiplication by
`I : 𝕜` maps real vectors to real vectors, and its restriction is a `𝕜`-linear operator `P` on
`E`: `P₀ (x + i 0) = P x + i 0`. -/
theorem exists_restrict_of_conj {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (P₀ : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E)
    (hconjP : ∀ z, conjugate (P₀ z) = P₀ (conjugate z))
    (hMP : ∀ z, P₀ (cx ((I : 𝕜) • (1 : E →L[𝕜] E)) z) = cx ((I : 𝕜) • (1 : E →L[𝕜] E)) (P₀ z)) :
    ∃ P : E →L[𝕜] E, ∀ x, P₀ (real x) = real (P x) := by
  have hreal : ∀ x : E, (P₀ (real x)).im = 0 := fun x ↦ by
    have h := congrArg HilbertComplexification.im (hconjP (real x))
    rw [conjugate_real, conjugate_im] at h
    have h2 : (2 : 𝕜) • (P₀ (real x)).im = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  obtain ⟨Pf, hP0⟩ : ∃ Pf : E → E, ∀ x, P₀ (real x) = real (Pf x) :=
    ⟨fun x ↦ (P₀ (real x)).re, fun x ↦ HilbertComplexification.ext rfl (hreal x)⟩
  set M : E →L[𝕜] E := (I : 𝕜) • (1 : E →L[𝕜] E)
  have hPadd : ∀ x y, Pf (x + y) = Pf x + Pf y := fun x y ↦ by
    have := congrArg HilbertComplexification.re (congrArg P₀ (real_add (𝕜 := 𝕜) x y))
    rwa [map_add, hP0, hP0, hP0] at this
  have hPreal : ∀ (r : ℝ) x, Pf ((r : 𝕜) • x) = (r : 𝕜) • Pf x := fun r x ↦ by
    have := congrArg HilbertComplexification.re (congrArg P₀ (real_ofReal_smul (𝕜 := 𝕜) r x))
    rw [map_smul, hP0, hP0, re_smul] at this
    simpa using this
  have hPI : ∀ x, Pf ((I : 𝕜) • x) = (I : 𝕜) • Pf x := fun x ↦ by
    have h : (real ((I : 𝕜) • x) : HilbertComplexification 𝕜 E) = cx M (real x) := by
      simp [M]
    have := congrArg HilbertComplexification.re (congrArg P₀ h)
    rw [hMP, hP0, hP0] at this
    simpa [M] using this
  have hdec : ∀ (c : 𝕜) (x : E),
      c • x = ((re c : ℝ) : 𝕜) • x + ((im c : ℝ) : 𝕜) • ((I : 𝕜) • x) :=
    fun c x ↦ by rw [smul_smul, ← add_smul, re_add_im]
  let PL : E →ₗ[𝕜] E :=
    { toFun := Pf
      map_add' := hPadd
      map_smul' := fun c x ↦ by
        rw [RingHom.id_apply, hdec c x, hPadd, hPreal, hPreal, hPI, ← hdec] }
  have hbound : ∀ x, ‖PL x‖ ≤ ‖P₀‖ * ‖x‖ := fun x ↦ by
    have := P₀.le_opNorm (real x)
    rwa [hP0, norm_real, norm_real] at this
  exact ⟨PL.mkContinuous ‖P₀‖ hbound, hP0⟩

open HilbertComplexification in
/-- The restriction of a self-adjoint operator of `E_ℂ` to `E` is self-adjoint. -/
theorem inner_restrict_symm {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {P₀ : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E}
    {P : E →L[𝕜] E} (hP0 : ∀ x, P₀ (real x) = real (P x))
    (hPsa : ∀ z w, ⟪P₀ z, w⟫_ℂ = ⟪z, P₀ w⟫_ℂ) (x y : E) : ⟪P x, y⟫_𝕜 = ⟪x, P y⟫_𝕜 := by
  have hre : ∀ x y, re ⟪P x, y⟫_𝕜 = re ⟪x, P y⟫_𝕜 := fun x y ↦ by
    have h := hPsa (real x) (real y)
    rw [hP0, hP0, inner_real, inner_real] at h
    exact_mod_cast h
  refine RCLike.ext (hre x y) ?_
  have h := hre x ((I : 𝕜) • y)
  rw [map_smul, inner_smul_right, inner_smul_right] at h
  simp only [RCLike.mul_re, RCLike.I_re, zero_mul, zero_sub, neg_inj] at h
  rwa [RCLike.I_im', RCLike.I_im'] at h

open HilbertComplexification in
/-- **Spectral splitting of an invertible self-adjoint operator**, over `ℝ` or `ℂ`: if `G` is
bounded, self-adjoint and bijective on the Hilbert space `E`, there are a self-adjoint idempotent
`P` commuting with `G` and `c > 0` such that `re ⟪G x, x⟫ ≥ c ‖x‖²` on the range of `P` and
`≤ -c ‖x‖²` on its kernel.

Over `ℝ` the continuous functional calculus is not available; we apply the complex case
(`exists_spectral_projection_complex`) to the complexification `G_ℂ` of `G` on
`E_ℂ = E × E` (`HilbertComplexification`). The spectral projection `P_ℂ` commutes with the
conjugation `C`: `C P_ℂ C` is again an idempotent commuting with `G_ℂ`, hence with `P_ℂ`, with
the same sign bounds, so it equals `P_ℂ` (`eq_of_spectral_bounds`). Thus `P_ℂ` maps real
vectors to real vectors, and its restriction is `P`; it is `𝕜`-linear since `P_ℂ` also commutes
with the complexification of the multiplication by `I`. We do not claim this argument is new. -/
theorem exists_spectral_projection {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {G : E →L[𝕜] E}
    (hGsa : ∀ x y, ⟪G x, y⟫_𝕜 = ⟪x, G y⟫_𝕜) (hG : Function.Bijective G) :
    ∃ P : E →L[𝕜] E, ∃ c > 0, (∀ x, P (P x) = P x) ∧ (∀ x y, ⟪P x, y⟫_𝕜 = ⟪x, P y⟫_𝕜) ∧
      (∀ x, G (P x) = P (G x)) ∧ (∀ x, P x = x → c * ‖x‖ ^ 2 ≤ re ⟪G x, x⟫_𝕜) ∧
      (∀ x, P x = 0 → c * ‖x‖ ^ 2 ≤ -re ⟪G x, x⟫_𝕜) ∧
      ∀ x, cfc (fun t : ℝ ↦ if 0 < t then 1 else 0) (cx G) (real x) = real (P x) := by
  let e := ContinuousLinearEquiv.ofBijective G (LinearMap.ker_eq_bot.2 hG.1)
    (LinearMap.range_eq_top.2 hG.2)
  have h1 : G * (e.symm : E →L[𝕜] E) = 1 :=
    ContinuousLinearMap.ext fun x ↦ show G (e.symm x) = x from e.apply_symm_apply x
  have h2 : (e.symm : E →L[𝕜] E) * G = 1 :=
    ContinuousLinearMap.ext fun x ↦ show e.symm (G x) = x from e.symm_apply_apply x
  have hsa : IsSelfAdjoint (cx G) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro z w
    simp only [ContinuousLinearMap.coe_coe]
    exact inner_cx G G hGsa z w
  have hunit : IsUnit (cx G) := ⟨⟨cx G, cx (e.symm : E →L[𝕜] E),
    by rw [← cx_mul, h1, cx_one], by rw [← cx_mul, h2, cx_one]⟩, rfl⟩
  obtain ⟨P₀, c, hc, hPP, hPsa, hGP, hpos, hneg, hcomm, hP₀def⟩ :=
    exists_spectral_projection_complex hsa hunit
  -- the conjugate `C P₀ C` coincides with `P₀`
  have hQG : ∀ z, cx G (conjOp P₀ z) = conjOp P₀ (cx G z) := fun z ↦ by
    simp only [conjOp_apply]
    rw [← conjugate_cx, hGP, conjugate_cx]
  have hPQ : ∀ z, P₀ (conjOp P₀ z) = conjOp P₀ (P₀ z) := hcomm _ hQG
  have hQQ : ∀ z, conjOp P₀ (conjOp P₀ z) = conjOp P₀ z := fun z ↦ by simp [hPP]
  have hre_conj : ∀ z, Complex.re ⟪cx G (conjugate z), conjugate z⟫_ℂ =
      Complex.re ⟪cx G z, z⟫_ℂ := fun z ↦ by
    rw [← conjugate_cx, inner_conjugate, Complex.conj_re]
  have hQpos : ∀ z, conjOp P₀ z = z → c * ‖z‖ ^ 2 ≤ Complex.re ⟪cx G z, z⟫_ℂ := fun z hz ↦ by
    have h : P₀ (conjugate z) = conjugate z := by simpa using congrArg conjugate hz
    have := hpos _ h
    rwa [norm_conjugate, hre_conj] at this
  have hQneg : ∀ z, conjOp P₀ z = 0 → c * ‖z‖ ^ 2 ≤ -Complex.re ⟪cx G z, z⟫_ℂ := fun z hz ↦ by
    have h : P₀ (conjugate z) = 0 := by simpa using congrArg conjugate hz
    have := hneg _ h
    rwa [norm_conjugate, hre_conj] at this
  have hconjP : ∀ z, conjugate (P₀ z) = P₀ (conjugate z) := fun z ↦ by
    rw [eq_of_spectral_bounds hc hPP hQQ hPQ hpos hneg hQpos hQneg (conjugate z)]
    simp
  -- `P₀` restricts to `E`
  have hMP : ∀ z, P₀ (cx ((I : 𝕜) • (1 : E →L[𝕜] E)) z) = cx ((I : 𝕜) • (1 : E →L[𝕜] E)) (P₀ z) :=
    hcomm _ fun z ↦ by ext <;> simp [map_smul]
  obtain ⟨P, hP0⟩ := exists_restrict_of_conj P₀ hconjP hMP
  refine ⟨P, c, hc, fun x ↦ ?_, inner_restrict_symm hP0 hPsa, fun x ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x ↦ by rw [← hP₀def]; exact hP0 x⟩
  · have h := hPP (real x)
    simp only [hP0] at h
    exact congrArg HilbertComplexification.re h
  · have h := hGP (real x)
    rw [hP0, cx_real, cx_real, hP0] at h
    exact congrArg HilbertComplexification.re h
  · have h0 : P₀ (real x) = real x := by rw [hP0, hx]
    have := hpos _ h0
    rwa [cx_real, inner_real, norm_real, Complex.ofReal_re] at this
  · have h0 : P₀ (real x) = 0 := by rw [hP0, hx, real_zero]
    have := hneg _ h0
    rwa [cx_real, inner_real, norm_real, Complex.ofReal_re] at this

/-- A positive operator vanishes where its quadratic form vanishes: if `A` is symmetric,
`re ⟪A z, z⟫ ≥ 0` for all `z` and `re ⟪A x, x⟫ = 0`, then `A x = 0`. -/
theorem apply_eq_zero_of_re_inner_eq_zero {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {A : E →L[𝕜] E}
    (hsym : ∀ x y, ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜) (hpos : ∀ z, 0 ≤ re ⟪A z, z⟫_𝕜) {x : E}
    (hx : re ⟪A x, x⟫_𝕜 = 0) : A x = 0 := by
  set y := A x
  set a := ‖y‖ ^ 2
  set c := re ⟪A y, y⟫_𝕜
  have hc : 0 ≤ c := hpos y
  have hquad : ∀ t : ℝ, 0 ≤ -2 * t * a + t ^ 2 * c := fun t ↦ by
    have h := hpos (x - (t : 𝕜) • y)
    have e1 : re ⟪A x, y⟫_𝕜 = a := by rw [inner_self_eq_norm_sq_to_K]; simp [a, y]
    have e2 : re ⟪A y, x⟫_𝕜 = a := by rw [hsym, ← inner_conj_symm, conj_re]; exact e1.trans rfl
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, conj_ofReal, map_sub, RCLike.mul_re, ofReal_re, ofReal_im, zero_mul,
      sub_zero] at h
    rw [hx, e1, e2] at h
    nlinarith [h]
  by_contra hy
  have ha : 0 < a := by positivity
  have := hquad (a / (c + 1))
  have hc1 : 0 < c + 1 := by linarith
  have key : -2 * (a / (c + 1)) * a + (a / (c + 1)) ^ 2 * c =
      a ^ 2 / (c + 1) * (c / (c + 1) - 2) := by field_simp; ring
  rw [key] at this
  have : c / (c + 1) < 1 := (div_lt_one hc1).2 (by linarith)
  nlinarith [div_pos (pow_pos ha 2) hc1]

end Spectral

section PosPart

/-- Positive and negative parts of a self-adjoint operator on a complex Hilbert space
(continuous functional calculus, `CFC.posPart`, `CFC.negPart`), with their uniqueness. -/
theorem exists_posPart_negPart_complex {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {G : F →L[ℂ] F} (hG : IsSelfAdjoint G) :
    ∃ A B : F →L[ℂ] F, A.IsPositive ∧ B.IsPositive ∧ A - B = G ∧ A * B = 0 ∧ B * A = 0 ∧
      (∀ T : F →L[ℂ] F, Commute G T → Commute A T ∧ Commute B T) ∧
      ∀ b c : F →L[ℂ] F, b.IsPositive → c.IsPositive → G = b - c → b * c = 0 →
        b = A ∧ c = B := by
  refine ⟨G⁺, G⁻, ContinuousLinearMap.nonneg_iff_isPositive.1 (CFC.posPart_nonneg G),
    ContinuousLinearMap.nonneg_iff_isPositive.1 (CFC.negPart_nonneg G),
    CFC.posPart_sub_negPart G hG, CFC.posPart_mul_negPart G, CFC.negPart_mul_posPart G,
    fun T hT ↦ ⟨hT.cfcₙ_real _, hT.cfcₙ_real _⟩, fun b c hb hc habc hbc ↦ ?_⟩
  have := CFC.posPart_negPart_unique habc hbc (ContinuousLinearMap.nonneg_iff_isPositive.2 hb)
    (ContinuousLinearMap.nonneg_iff_isPositive.2 hc)
  exact ⟨this.1.symm, this.2.symm⟩

open HilbertComplexification

/-- **Positive and negative parts of a self-adjoint operator**, over `ℝ` or `ℂ` (continuous
functional calculus, no invertibility): `G = G⁺ - G⁻` with `G⁺`, `G⁻` self-adjoint, positive
and `G⁺ G⁻ = G⁻ G⁺ = 0`. Over `ℝ` through the complexification: `C (G_ℂ)⁺ C` is again a positive
part of `G_ℂ`, so it equals `(G_ℂ)⁺` by uniqueness (`CFC.posPart_negPart_unique`), and
`(G_ℂ)^±` restrict to `E` (`exists_restrict_of_conj`). -/
theorem exists_posPart_negPart {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {G : E →L[𝕜] E}
    (hGsa : ∀ x y, ⟪G x, y⟫_𝕜 = ⟪x, G y⟫_𝕜) :
    ∃ A B : E →L[𝕜] E, (∀ x, G x = A x - B x) ∧ (∀ x, A (B x) = 0) ∧ (∀ x, B (A x) = 0) ∧
      (∀ x y, ⟪A x, y⟫_𝕜 = ⟪x, A y⟫_𝕜) ∧ (∀ x y, ⟪B x, y⟫_𝕜 = ⟪x, B y⟫_𝕜) ∧
      (∀ x, 0 ≤ re ⟪A x, x⟫_𝕜) ∧ (∀ x, 0 ≤ re ⟪B x, x⟫_𝕜) := by
  set C := cx G with hCdef
  have hsa : IsSelfAdjoint C := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro z w
    simp only [ContinuousLinearMap.coe_coe]
    exact inner_cx G G hGsa z w
  have hconj_sub : ∀ a b : HilbertComplexification 𝕜 E,
      conjugate (a - b) = conjugate a - conjugate b := fun a b ↦ by
    ext <;> simp; abel
  have hconjOp_mul : ∀ S T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E,
      conjOp (S * T) = conjOp S * conjOp T := fun S T ↦ by
    ext1 z; simp [conjOp_apply]
  have hconjOp_sub : ∀ S T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E,
      conjOp (S - T) = conjOp S - conjOp T := fun S T ↦ by
    ext1 z; simp [conjOp_apply, hconj_sub]
  have hconjC : conjOp C = C := by
    ext1 z; simp only [conjOp_apply, hCdef, conjugate_cx, conjugate_conjugate]
  have hconjpos : ∀ T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E,
      T.IsPositive → (conjOp T).IsPositive := fun T hT ↦ by
    refine ⟨fun z w ↦ ?_, fun z ↦ ?_⟩
    · change ⟪conjOp T z, w⟫_ℂ = ⟪z, conjOp T w⟫_ℂ
      have h1 := inner_conjugate (T (conjugate z)) (conjugate w)
      have h2 := inner_conjugate (conjugate z) (T (conjugate w))
      rw [conjugate_conjugate] at h1 h2
      rw [conjOp_apply, conjOp_apply, h1, h2, hT.inner_left_eq_inner_right]
    · change 0 ≤ Complex.re ⟪conjOp T z, z⟫_ℂ
      have h1 := inner_conjugate (T (conjugate z)) (conjugate z)
      rw [conjugate_conjugate] at h1
      rw [conjOp_apply, h1, Complex.conj_re]
      exact hT.re_inner_nonneg_left _
  obtain ⟨A₀, B₀, hA0, hB0, hCAB, hAB, hBA, hcommT, huniq⟩ :=
    exists_posPart_negPart_complex hsa
  have huniq' := huniq (conjOp A₀) (conjOp B₀) (hconjpos _ hA0) (hconjpos _ hB0)
    (by rw [← hconjOp_sub, hCAB, hconjC]) (by rw [← hconjOp_mul, hAB]; ext1 z; simp)
  have hconjA : ∀ z, conjugate (A₀ z) = A₀ (conjugate z) := fun z ↦ by
    have h := congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦
      T (conjugate z)) huniq'.1
    simp only [conjOp_apply, conjugate_conjugate] at h
    exact h
  have hconjB : ∀ z, conjugate (B₀ z) = B₀ (conjugate z) := fun z ↦ by
    have h := congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦
      T (conjugate z)) huniq'.2
    simp only [conjOp_apply, conjugate_conjugate] at h
    exact h
  set M : E →L[𝕜] E := (I : 𝕜) • (1 : E →L[𝕜] E) with hM
  have hcomm : Commute C (cx M) := by
    change C * cx M = cx M * C
    rw [hCdef, ← cx_mul, ← cx_mul]
    congr 1
    ext1 x
    simp [M]
  have hMA : ∀ z, A₀ (cx M z) = cx M (A₀ z) := fun z ↦
    congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦ T z)
      (hcommT _ hcomm).1.eq
  have hMB : ∀ z, B₀ (cx M z) = cx M (B₀ z) := fun z ↦
    congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦ T z)
      (hcommT _ hcomm).2.eq
  obtain ⟨A, hA⟩ := exists_restrict_of_conj A₀ hconjA hMA
  obtain ⟨B, hB⟩ := exists_restrict_of_conj B₀ hconjB hMB
  refine ⟨A, B, fun x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_,
    inner_restrict_symm hA hA0.inner_left_eq_inner_right,
    inner_restrict_symm hB hB0.inner_left_eq_inner_right, fun x ↦ ?_, fun x ↦ ?_⟩
  · have h := congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦
      T (real x)) hCAB
    simp only [sub_apply, hA, hB, hCdef, cx_real] at h
    exact (congrArg HilbertComplexification.re h).symm
  · have h := congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦
      T (real x)) hAB
    change A₀ (B₀ (real x)) = 0 at h
    rw [hB, hA, ← real_zero] at h
    exact congrArg HilbertComplexification.re h
  · have h := congrArg (fun T : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E ↦
      T (real x)) hBA
    change B₀ (A₀ (real x)) = 0 at h
    rw [hA, hB, ← real_zero] at h
    exact congrArg HilbertComplexification.re h
  · have := hA0.re_inner_nonneg_left (real x)
    rw [hA, inner_real] at this
    simpa using this
  · have := hB0.re_inner_nonneg_left (real x)
    rw [hB, inner_real] at this
    simpa using this

/-- **Sign decomposition of a self-adjoint operator** ([Bog74, proof of Theorem IV.5.2], without
spectral measures): for `G` bounded and self-adjoint on a real or complex Hilbert space `E`,
`E = N₀ ⊕ N₊ ⊕ N₋` with `N₀ = ker G`, `N₊ = (ker G⁺)^⊥`, `N₋ = (ker G⁻)^⊥` (`G^±` the positive
and negative parts of `G`, `exists_posPart_negPart`). The three components and the sum of any
two of them are closed (`N₀ ⊕ N₊ = ker G⁻`, `N₀ ⊕ N₋ = ker G⁺`, `N₊ ⊕ N₋ = N₀^⊥`), `⟪G x, x⟫`
is positive definite on `N₊` and negative definite on `N₋`, and `⟪G N₊, N₋⟫ = 0`. These are the
spectral subspaces of `G` for `{0}`, `(0, ∞)` and `(-∞, 0)`, but no Borel functional calculus is
needed: `N₊ ⊆ ker G⁻` because `G⁻ G⁺ = 0`. -/
theorem exists_sign_decomposition {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {G : E →L[𝕜] E}
    (hGsa : ∀ x y, ⟪G x, y⟫_𝕜 = ⟪x, G y⟫_𝕜) :
    ∃ N₀ Np Nm : Submodule 𝕜 E, (∀ x, x ∈ N₀ ↔ G x = 0) ∧ IsClosed (N₀ : Set E) ∧
      IsClosed (Np : Set E) ∧ IsClosed (Nm : Set E) ∧
      IsClosed ((N₀ ⊔ Np : Submodule 𝕜 E) : Set E) ∧
      IsClosed ((N₀ ⊔ Nm : Submodule 𝕜 E) : Set E) ∧
      IsClosed ((Np ⊔ Nm : Submodule 𝕜 E) : Set E) ∧
      N₀ ⊔ Np ⊔ Nm = ⊤ ∧ Disjoint Np Nm ∧ Disjoint N₀ (Np ⊔ Nm) ∧
      (∀ x ∈ Np, x ≠ 0 → 0 < re ⟪G x, x⟫_𝕜) ∧ (∀ x ∈ Nm, x ≠ 0 → re ⟪G x, x⟫_𝕜 < 0) ∧
      ∀ x ∈ Np, ∀ y ∈ Nm, ⟪G x, y⟫_𝕜 = 0 := by
  obtain ⟨A, B, hG, hAB, hBA, hAs, hBs, hAp, hBp⟩ := exists_posPart_negPart hGsa
  set KA : Submodule 𝕜 E := A.ker with hKA
  set KB : Submodule 𝕜 E := B.ker with hKB
  have hm : ∀ (T : E →L[𝕜] E) (x : E), x ∈ T.ker ↔ T x = 0 := fun _ _ ↦ Iff.rfl
  have hKAc : IsClosed (KA : Set E) := A.isClosed_ker
  have hKBc : IsClosed (KB : Set E) := B.isClosed_ker
  have hdec : ∀ K : Submodule 𝕜 E, IsClosed (K : Set E) → ∀ v, ∃ y ∈ K, ∃ z ∈ Kᗮ, v = y + z :=
    fun K hK v ↦ by
      have : CompleteSpace K := hK.completeSpace_coe
      exact K.exists_add_mem_mem_orthogonal v
  have hbot : ∀ (K : Submodule 𝕜 E) (x : E), x ∈ K → x ∈ Kᗮ → x = 0 := fun K x h1 h2 ↦
    inner_self_eq_zero.1 ((Submodule.mem_orthogonal K x).1 h2 x h1)
  have hNpB : ∀ y ∈ KAᗮ, B y = 0 := fun y hy ↦ by
    have h : ⟪y, B y⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal' _ y).1 hy _ ((hm _ _).2 (hAB y))
    exact apply_eq_zero_of_re_inner_eq_zero hBs hBp (by rw [hBs, h, map_zero])
  have hNmA : ∀ y ∈ KBᗮ, A y = 0 := fun y hy ↦ by
    have h : ⟪y, A y⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal' _ y).1 hy _ ((hm _ _).2 (hBA y))
    exact apply_eq_zero_of_re_inner_eq_zero hAs hAp (by rw [hAs, h, map_zero])
  have hsplit : ∀ x, ∃ b ∈ KA ⊓ KB, ∃ b' ∈ KBᗮ, ∃ a' ∈ KAᗮ, x = b + b' + a' := fun x ↦ by
    obtain ⟨a, ha, a', ha', rfl⟩ := hdec KA hKAc x
    obtain ⟨b, hb, b', hb', rfl⟩ := hdec KB hKBc a
    refine ⟨b, ⟨?_, hb⟩, b', hb', a', ha', rfl⟩
    have h := (hm _ _).1 ha
    change A (b + b') = 0 at h
    rw [map_add, hNmA b' hb', add_zero] at h
    exact h
  have hsupB : KA ⊓ KB ⊔ KAᗮ = KB := by
    refine le_antisymm (sup_le inf_le_right fun y hy ↦ (hm _ _).2 (hNpB y hy))
      fun x hx ↦ ?_
    obtain ⟨b, hb, b', hb', a', ha', rfl⟩ := hsplit x
    have h := (hm _ _).1 hx
    change B (b + b' + a') = 0 at h
    rw [map_add, map_add, hNpB a' ha', (hm _ _).1 hb.2, zero_add, add_zero] at h
    rw [hbot KB b' ((hm _ _).2 h) hb', add_zero]
    exact Submodule.add_mem_sup hb ha'
  have hsupA : KA ⊓ KB ⊔ KBᗮ = KA := by
    refine le_antisymm (sup_le inf_le_left fun y hy ↦ (hm _ _).2 (hNmA y hy))
      fun x hx ↦ ?_
    obtain ⟨b, hb, b', hb', a', ha', rfl⟩ := hsplit x
    have h := (hm _ _).1 hx
    change A (b + b' + a') = 0 at h
    rw [map_add, map_add, hNmA b' hb', (hm _ _).1 hb.1, zero_add, zero_add] at h
    rw [hbot KA a' ((hm _ _).2 h) ha', add_zero]
    exact Submodule.add_mem_sup hb hb'
  have hsupPM : KAᗮ ⊔ KBᗮ = (KA ⊓ KB)ᗮ := by
    refine le_antisymm (sup_le (Submodule.orthogonal_le inf_le_left)
      (Submodule.orthogonal_le inf_le_right)) fun x hx ↦ ?_
    obtain ⟨b, hb, b', hb', a', ha', rfl⟩ := hsplit x
    have hb'o : b' ∈ (KA ⊓ KB)ᗮ := Submodule.orthogonal_le inf_le_right hb'
    have ha'o : a' ∈ (KA ⊓ KB)ᗮ := Submodule.orthogonal_le inf_le_left ha'
    have hbo : b ∈ (KA ⊓ KB)ᗮ := by
      have := sub_mem (sub_mem hx ha'o) hb'o
      rwa [add_sub_cancel_right, add_sub_cancel_right] at this
    rw [hbot _ b hb hbo, zero_add, add_comm]
    exact Submodule.add_mem_sup ha' hb'
  refine ⟨KA ⊓ KB, KAᗮ, KBᗮ, fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩, hKAc.inter hKBc,
    Submodule.isClosed_orthogonal _, Submodule.isClosed_orthogonal _, by rw [hsupB]; exact hKBc,
    by rw [hsupA]; exact hKAc, by rw [hsupPM]; exact Submodule.isClosed_orthogonal _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [hG, (hm _ _).1 hx.1, (hm _ _).1 hx.2, sub_zero]
  · rw [hG, sub_eq_zero] at hx
    have hAx : A x = 0 := by
      have h : ⟪A (A x), x⟫_𝕜 = 0 := by rw [hx, hAB, inner_zero_left]
      rw [hAs] at h
      exact inner_self_eq_zero.1 h
    exact ⟨(hm _ _).2 hAx, (hm _ _).2 (hx ▸ hAx)⟩
  · refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨b, hb, b', hb', a', ha', rfl⟩ := hsplit x
    exact add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left hb))
      (Submodule.mem_sup_right hb')) (Submodule.mem_sup_left (Submodule.mem_sup_right ha'))
  · refine Submodule.disjoint_def.2 fun x hx hx' ↦ hbot KA x ((hm _ _).2 (hNmA x hx')) hx
  · rw [hsupPM]
    exact Submodule.orthogonal_disjoint _
  · intro x hx hx0
    have e : re ⟪G x, x⟫_𝕜 = re ⟪A x, x⟫_𝕜 := by rw [hG, hNpB x hx, sub_zero]
    rw [e]
    refine lt_of_le_of_ne (hAp x) fun h ↦ hx0 ?_
    exact hbot KA x ((hm _ _).2 (apply_eq_zero_of_re_inner_eq_zero hAs hAp h.symm)) hx
  · intro x hx hx0
    have e : re ⟪G x, x⟫_𝕜 = -re ⟪B x, x⟫_𝕜 := by
      rw [hG, hNmA x hx, zero_sub, inner_neg_left, map_neg]
    rw [e, neg_lt_zero]
    refine lt_of_le_of_ne (hBp x) fun h ↦ hx0 ?_
    exact hbot KB x ((hm _ _).2 (apply_eq_zero_of_re_inner_eq_zero hBs hBp h.symm)) hx
  · intro x hx y hy
    rw [hG, hNpB x hx, sub_zero, hAs, hNmA y hy, inner_zero_right]

end PosPart

end FundamentalSymmetry

end LocallyConvex.Analysis

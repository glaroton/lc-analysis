/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.OperatorValued
public import LocallyConvexAnalysis.Analytic.Operations
public import LocallyConvexAnalysis.Complex.NormedComplexification

/-!
# Analytic operator-valued maps

Let `E` be a locally convex space, `F₁`, `F₂` normed spaces, and `g : E → L(F₁, F₂)`. We show
that analyticity of the uncurried map `ĝ(y, ξ) = g(y) ξ` on `U × F₁` implies analyticity of
`g` on `U` **as a map into `L(F₁, F₂)` with the operator norm**, in the complex and in the real
analytic setting. This is the analytic counterpart of `contDiffMBOn_of_unc_clm`.

## Main results

* `complexAnalyticOn_of_unc_clm_of_dMB_smul` (the core statement): `E` complex locally convex,
  `F₁` real normed, `F₂` complex normed, `K : E → L_ℝ(F₁, F₂)`. If `K̂(z, ξ) = K(z) ξ` is smooth
  on `U × F₁` in the real Michal–Bastiani sense and its partial differential in the `z`-direction
  is complex linear, then `K` is complex analytic on `U`, for the complex structure of
  `L_ℝ(F₁, F₂)` given by `F₂`.
* `ComplexAnalyticOn.of_unc_clm`: `E` complex locally convex, `F₁`, `F₂` complex normed. If
  `(y, ξ) ↦ g(y) ξ` is complex analytic on `U × F₁`, then `g : U → L_ℂ(F₁, F₂)` is complex
  analytic.
* `RealAnalyticOn.of_unc_clm`: `E` real locally convex, `F₁`, `F₂` real normed. If
  `(y, ξ) ↦ g(y) ξ` is real analytic on `U × F₁`, then `g : U → L(F₁, F₂)` is real analytic.
  Here `U` need not be open.
* `RealAnalyticOn.of_unc_clm₂`: the bilinear version, e.g. for the local representatives
  `y ↦ Ω(y) ∈ L(E, L(E, ℝ))` of a differential `2`-form on a manifold modelled on a normed space.

**No completeness** of `E`, `F₁` or `F₂` is assumed.

## Proof

*Complex case.* By `contDiffMBOn_of_unc_clm`, `K` is smooth as a map into `L_ℝ(F₁, F₂)` with the
operator norm, and `dK(z, h) ξ = ∂_{(h, 0)} K̂(z, ξ)`. Hence `dK(z, ·)` is complex linear, and `K`
is complex analytic by [GN26, Theorem 2.1.12] (`complexAnalyticOn_iff_holomorphicOn`). For a
complex analytic `ĝ` with `g(y) ∈ L_ℂ(F₁, F₂)` this applies to `K(y) = g(y)` seen as a real
operator, and `g = P ∘ K` for the continuous complex linear projection
`P T = (T - i T i) / 2` of `L_ℝ(F₁, F₂)` onto `L_ℂ(F₁, F₂)` (`clmComplexPart`).

*Real case.* Let `H : (E × F₁)_ℂ → (F₂)_ℂ` be a complex analytic extension of `ĝ` on an open
neighbourhood `V` of the real points. The open neighbourhood `V` need not contain `W × F₁` for
any open `W ∋ y`, so `H(z, ·)` need not be defined on all of `(F₁)_ℂ`; we therefore do not use
`H` itself but its differential at `ξ = 0`:
`K(z) ξ = dH((z, 0), (0, ξ))` for `z ∈ W = {z ∈ E_ℂ | (z, 0) ∈ V}` and `ξ ∈ F₁`.
This is real linear and continuous in `ξ`, so `K(z) ∈ L_ℝ(F₁, (F₂)_ℂ)`, where `(F₂)_ℂ` carries
the rotation invariant norm (`NormedComplexification`). The map `(z, ξ) ↦ K(z) ξ` is smooth, and
complex linear in the `z`-direction since `dH` is complex analytic (`ComplexAnalyticOn.dMB`), so
the complex case applies to `K` on `W`. For real `z = y` and `ξ ∈ F₁` the line
`t ↦ (y, t ξ)` stays in the real points, where `H` agrees with `ĝ`, so
`K(y) ξ = g(y) ξ + i 0`. Finally `L_ℝ(F₁, (F₂)_ℂ) ≅ L(F₁, F₂)_ℂ`, `T ↦ Re ∘ T + i Im ∘ T`
(`clmToComplexification`), is continuous and complex linear, so it carries `K` to a complex
analytic extension of `g`.

We do not claim this argument is new. For `C^k` maps, a related passage to the operator norm is
[GN26, Lemma 2.3.18] (from `C^{ℓ+1}` into `L^k(E₁, …, E_k; F)` with the compact-open
topology to `FC^ℓ` for the operator norm).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

attribute [local instance] continuousSMul_real_of_complex

/-! ### The core statement -/

section Core

variable {Z : Type*} [AddCommGroup Z] [Module ℝ Z] [Module ℂ Z] [IsScalarTower ℝ ℂ Z]
  [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
  [LocallyConvexSpace ℝ Z] [T2Space Z]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]

omit [Module ℂ Z] [IsScalarTower ℝ ℂ Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
  [LocallyConvexSpace ℝ Z] [T2Space Z] in
/-- The operator `dK(z, h)` evaluated at `ξ` is the partial differential `∂_{(h, 0)} K̂(z, ξ)` of
the uncurried map. -/
theorem dMB_apply_of_unc_clm {K : Z → F₁ →L[ℝ] F₂} {U : Set Z}
    (hK : ContDiffMBOn 1 (fun p : Z × F₁ ↦ K p.1 p.2) (U ×ˢ univ)) (hK₁ : ContDiffMBOn 1 K U)
    {z : Z} (hz : z ∈ U) (h : Z) (ξ : F₁) :
    dMB K (z, h) ξ = dMB (fun p : Z × F₁ ↦ K p.1 p.2) ((z, ξ), (h, 0)) :=
  tendsto_nhds_unique ((hK₁.2.1 z hz h).clm_comp_real (ContinuousLinearMap.apply ℝ F₂ ξ))
    (hasDirDerivAt_slice_of_unc_clm hK hz ξ h)

/-- **Operator-valued maps with complex linear partial differentials are complex analytic.**
Let `Z` be a complex locally convex space, `F₁` a real normed space, `F₂` a complex normed
space and `K : Z → L_ℝ(F₁, F₂)`, where `L_ℝ(F₁, F₂)` carries the operator norm and the complex
structure of `F₂`. If `K̂(z, ξ) = K(z) ξ` is smooth on `U × F₁` in the real Michal–Bastiani sense
and `∂_{(c h, 0)} K̂(z, ξ) = c ∂_{(h, 0)} K̂(z, ξ)` for `c ∈ ℂ`, then `K` is complex analytic
on `U`. By `contDiffMBOn_of_unc_clm`, `K` is smooth for the operator norm, with
`dK(z, h) ξ = ∂_{(h, 0)} K̂(z, ξ)`; so `dK(z, ·)` is complex linear and
[GN26, Theorem 2.1.12] (`complexAnalyticOn_iff_holomorphicOn`) applies. No completeness is used. -/
theorem complexAnalyticOn_of_unc_clm_of_dMB_smul {K : Z → F₁ →L[ℝ] F₂} {U : Set Z}
    (hU : IsOpen U) (hK : SmoothMBOn (fun p : Z × F₁ ↦ K p.1 p.2) (U ×ˢ univ))
    (hKc : ∀ z ∈ U, ∀ (ξ : F₁) (c : ℂ) (h : Z),
      dMB (fun p : Z × F₁ ↦ K p.1 p.2) ((z, ξ), (c • h, 0)) =
        c • dMB (fun p : Z × F₁ ↦ K p.1 p.2) ((z, ξ), (h, 0))) :
    ComplexAnalyticOn K U := by
  have hs : SmoothMBOn K U := fun k ↦ contDiffMBOn_of_unc_clm k hU (hK (k + 1))
  refine (complexAnalyticOn_iff_holomorphicOn hU).2 ⟨hs, fun z hz c h ↦ ?_⟩
  ext ξ
  rw [smul_apply, dMB_apply_of_unc_clm (hK 1) (hs 1) hz,
    dMB_apply_of_unc_clm (hK 1) (hs 1) hz, hKc z hz ξ c h]

end Core

/-! ### The complex case -/

section ComplexCase

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]

/-- The complex linear part `ξ ↦ (T ξ - i T (i ξ)) / 2` of a real linear map `T`. -/
def clmComplexPartAux (T : F₁ →L[ℝ] F₂) : F₁ →L[ℂ] F₂ :=
  LinearMap.mkContinuous
    { toFun := fun ξ ↦ (2 : ℝ)⁻¹ • (T ξ - Complex.I • T (Complex.I • ξ))
      map_add' := fun ξ η ↦ by
        simp only [smul_add, map_add, smul_sub]
        abel
      map_smul' := fun c ξ ↦ by
        refine map_smul_of_map_I_smul
          (T := fun ξ ↦ (2 : ℝ)⁻¹ • (T ξ - Complex.I • T (Complex.I • ξ)))
          (fun v w ↦ ?_) (fun r w ↦ ?_) (fun w ↦ ?_) c ξ
        · simp only [smul_add, map_add, smul_sub]
          abel
        · rw [smul_comm Complex.I r w, map_smul, map_smul, smul_comm Complex.I r, ← smul_sub,
            smul_comm]
        · rw [smul_smul Complex.I Complex.I, Complex.I_mul_I, neg_one_smul, map_neg, smul_neg,
            sub_neg_eq_add, smul_comm Complex.I (2 : ℝ)⁻¹, smul_sub, smul_smul Complex.I Complex.I,
            Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm] }
    ‖T‖ fun ξ ↦ by
      change ‖(2 : ℝ)⁻¹ • (T ξ - Complex.I • T (Complex.I • ξ))‖ ≤ ‖T‖ * ‖ξ‖
      have h1 : ‖T (Complex.I • ξ)‖ ≤ ‖T‖ * ‖ξ‖ := by
        refine (T.le_opNorm _).trans ?_
        rw [norm_smul, Complex.norm_I, one_mul]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
      have h2 := norm_sub_le (T ξ) (Complex.I • T (Complex.I • ξ))
      rw [norm_smul, Complex.norm_I, one_mul] at h2
      linarith [T.le_opNorm ξ]

@[simp] theorem clmComplexPartAux_apply (T : F₁ →L[ℝ] F₂) (ξ : F₁) :
    clmComplexPartAux T ξ = (2 : ℝ)⁻¹ • (T ξ - Complex.I • T (Complex.I • ξ)) := rfl

theorem norm_clmComplexPartAux_le (T : F₁ →L[ℝ] F₂) : ‖clmComplexPartAux T‖ ≤ ‖T‖ := by
  unfold clmComplexPartAux
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

/-- The continuous complex linear projection `P T = (T - i T i) / 2` of `L_ℝ(F₁, F₂)` onto
`L_ℂ(F₁, F₂)`, for complex normed spaces `F₁`, `F₂`; `‖P‖ ≤ 1`, and `P T = T` for complex linear
`T` (`clmComplexPart_restrictScalars`). -/
def clmComplexPart : (F₁ →L[ℝ] F₂) →L[ℂ] (F₁ →L[ℂ] F₂) :=
  LinearMap.mkContinuous
    { toFun := clmComplexPartAux
      map_add' := fun S T ↦ by
        ext ξ
        simp only [clmComplexPartAux_apply, add_apply, smul_add, smul_sub]
        abel
      map_smul' := fun c T ↦ by
        ext ξ
        simp only [clmComplexPartAux_apply, smul_apply, RingHom.id_apply,
          smul_sub, smul_comm Complex.I c, smul_comm (2 : ℝ)⁻¹ c] }
    1 fun T ↦ by
      rw [one_mul]
      exact norm_clmComplexPartAux_le T

@[simp] theorem clmComplexPart_apply (T : F₁ →L[ℝ] F₂) (ξ : F₁) :
    clmComplexPart T ξ = (2 : ℝ)⁻¹ • (T ξ - Complex.I • T (Complex.I • ξ)) := rfl

/-- The projection `P` is the identity on complex linear maps. -/
@[simp] theorem clmComplexPart_restrictScalars (T : F₁ →L[ℂ] F₂) :
    clmComplexPart (T.restrictScalars ℝ) = T := by
  ext ξ
  rw [clmComplexPart_apply, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_smul,
    Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, ← two_smul ℝ, smul_smul,
    inv_mul_cancel₀ (two_ne_zero), one_smul]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]

/-- **Complex analytic operator-valued maps.** Let `E` be a complex locally convex space,
`F₁`, `F₂` complex normed spaces, `U ⊆ E` open and `g : E → L_ℂ(F₁, F₂)`. If
`(y, ξ) ↦ g(y) ξ` is complex analytic on `U × F₁`, then `g` is complex analytic on `U` as a map
into `L_ℂ(F₁, F₂)` with the operator norm. No completeness is assumed. -/
theorem ComplexAnalyticOn.of_unc_clm {g : E → F₁ →L[ℂ] F₂} {U : Set E} (hU : IsOpen U)
    (hg : ComplexAnalyticOn (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) :
    ComplexAnalyticOn g U := by
  have hhol := (complexAnalyticOn_iff_holomorphicOn (hU.prod isOpen_univ)).1 hg
  have hK : ComplexAnalyticOn (fun y ↦ (g y).restrictScalars ℝ) U := by
    refine complexAnalyticOn_of_unc_clm_of_dMB_smul hU hhol.1 fun z hz ξ c h ↦ ?_
    have := hhol.2 (z, ξ) ⟨hz, mem_univ _⟩ c (h, 0)
    rwa [Prod.smul_mk, smul_zero] at this
  have hP := (clmComplexPart.complexAnalyticOn isOpen_univ).comp hK hU isOpen_univ
    (mapsTo_univ _ _)
  refine hP.congr hU fun y _ ↦ ?_
  simp

end ComplexCase

/-! ### The real case -/

section RealCase

open Complexification NormedComplexification

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- The real part `E_ℂ → E`, on the normed complexification, as a continuous real linear map. -/
def NormedComplexification.reCLM : NormedComplexification F₂ →L[ℝ] F₂ where
  toFun p := re (toCx p)
  map_add' _ _ := rfl
  map_smul' r p := by
    change re ((r : ℂ) • toCx p) = r • re (toCx p)
    rw [re_smul]
    simp
  cont := lipschitzWith_re.continuous

/-- The imaginary part `E_ℂ → E`, on the normed complexification, as a continuous real linear
map. -/
def NormedComplexification.imCLM : NormedComplexification F₂ →L[ℝ] F₂ where
  toFun p := im (toCx p)
  map_add' _ _ := rfl
  map_smul' r p := by
    change im ((r : ℂ) • toCx p) = r • im (toCx p)
    rw [im_smul]
    simp
  cont := lipschitzWith_im.continuous

@[simp] theorem NormedComplexification.reCLM_apply (p : NormedComplexification F₂) :
    NormedComplexification.reCLM p = re (toCx p) := rfl

@[simp] theorem NormedComplexification.imCLM_apply (p : NormedComplexification F₂) :
    NormedComplexification.imCLM p = im (toCx p) := rfl

/-- The complex linear homeomorphism `L_ℝ(F₁, (F₂)_ℂ) → L(F₁, F₂)_ℂ`,
`T ↦ Re ∘ T + i Im ∘ T`; here `(F₂)_ℂ` carries the rotation invariant norm, `L_ℝ(F₁, (F₂)_ℂ)` the
operator norm and the complex structure of `(F₂)_ℂ`, and `L(F₁, F₂)_ℂ` the product topology. -/
def clmToComplexification :
    (F₁ →L[ℝ] NormedComplexification F₂) →L[ℂ] Complexification (F₁ →L[ℝ] F₂) where
  toFun T := mk (NormedComplexification.reCLM.comp T) (NormedComplexification.imCLM.comp T)
  map_add' S T := by ext <;> simp
  map_smul' c T := by ext <;> simp
  cont := continuous_mk
    (ContinuousLinearMap.compL ℝ F₁ _ F₂ NormedComplexification.reCLM).continuous
    (ContinuousLinearMap.compL ℝ F₁ _ F₂ NormedComplexification.imCLM).continuous

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- If `H` extends `ĝ(y, ξ) = g(y) ξ` at the real points of `U × F₁`, then
`dH((y, 0) + i 0, (0, ξ) + i 0) = g(y) ξ + i 0` for `y ∈ U`: the line `t ↦ (y, t ξ)` stays in
the real points, where `H` is linear in `ξ`. -/
theorem hasDirDerivAt_ext_unc_clm {g : E → F₁ →L[ℝ] F₂} {U : Set E}
    {H : Complexification (E × F₁) → Complexification F₂}
    (hH : ∀ x ∈ U ×ˢ (univ : Set F₁), H (ofReal x) = ofReal (g x.1 x.2)) {y : E} (hy : y ∈ U)
    (ξ : F₁) : HasDirDerivAt H (ofReal (y, 0)) (ofReal (0, ξ)) (ofReal (g y ξ)) := by
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  have hline : ofReal (y, (0 : F₁)) + t • ofReal ((0 : E), ξ) = ofReal (y, t • ξ) := by
    rw [← map_smul, ← map_add, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [hline, hH _ ⟨hy, mem_univ _⟩, hH _ ⟨hy, mem_univ _⟩, map_smul, map_zero, map_zero,
    sub_zero, map_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]

/-- **Real analytic operator-valued maps.** Let `E` be a real locally convex space, `F₁`, `F₂`
real normed spaces, `U ⊆ E` and `g : E → L(F₁, F₂)`. If `(y, ξ) ↦ g(y) ξ` is real analytic on
`U × F₁`, then `g` is real analytic on `U` as a map into `L(F₁, F₂)` with the operator norm.

If `H` is a complex analytic extension of `ĝ` on `V ⊆ (E × F₁)_ℂ`, then
`K(z) ξ = dH((z, 0), (0, ξ))` defines a complex analytic `K : W → L_ℝ(F₁, (F₂)_ℂ)` on
`W = {z | (z, 0) ∈ V}` (`complexAnalyticOn_of_unc_clm_of_dMB_smul`), which extends `g`
(`hasDirDerivAt_ext_unc_clm`); `clmToComplexification ∘ K` is the required extension. Neither
openness of `U` nor completeness is used. -/
theorem RealAnalyticOn.of_unc_clm {g : E → F₁ →L[ℝ] F₂} {U : Set E}
    (hg : RealAnalyticOn (fun p : E × F₁ ↦ g p.1 p.2) (U ×ˢ univ)) : RealAnalyticOn g U := by
  classical
  obtain ⟨V, hV, H, hH, hext⟩ := hg
  have hVV : IsOpen (V ×ˢ (univ : Set (Complexification (E × F₁)))) := hV.prod isOpen_univ
  have hD : ComplexAnalyticOn (Analysis.dMB H) (V ×ˢ univ) := hH.dMB hV
  have hDhol := (complexAnalyticOn_iff_holomorphicOn hVV).1 hD
  have hH1 : ContDiffMBOn 1 H V := hH.smoothMBOn hV 1
  -- the inclusions `z ↦ (z, 0)` and `ξ ↦ (0, ξ) + i 0`
  let ι₁ : Complexification E →L[ℂ] Complexification (E × F₁) :=
    (ContinuousLinearMap.inl ℝ E F₁).complexify
  let ι₂ : F₁ →L[ℝ] Complexification (E × F₁) := ofReal.comp (ContinuousLinearMap.inr ℝ E F₁)
  have hι₁ : ∀ y : E, ι₁ (ofReal y) = ofReal (y, 0) := fun y ↦
    (ContinuousLinearMap.inl ℝ E F₁).complexify_ofReal y
  let W : Set (Complexification E) := ι₁ ⁻¹' V
  have hW : IsOpen W := hV.preimage ι₁.continuous
  have hWU : IsOpen (W ×ˢ (univ : Set F₁)) := hW.prod isOpen_univ
  let L : Complexification E × F₁ →L[ℝ] Complexification (E × F₁) × Complexification (E × F₁) :=
    ((ι₁.restrictScalars ℝ).comp (ContinuousLinearMap.fst ℝ _ F₁)).prod
      (ι₂.comp (ContinuousLinearMap.snd ℝ _ F₁))
  have hL : ∀ p : Complexification E × F₁, L p = (ι₁ p.1, ι₂ p.2) := fun _ ↦ rfl
  let N : Complexification F₂ →L[ℝ] NormedComplexification F₂ := toNormed.restrictScalars ℝ
  -- the operator `K(z) ξ = dH((z, 0), (0, ξ))`
  let Kop : ∀ z, z ∈ W → F₁ →L[ℝ] NormedComplexification F₂ := fun z hz ↦
    { toFun := fun ξ ↦ N (Analysis.dMB H (ι₁ z, ι₂ ξ))
      map_add' := fun ξ η ↦ by rw [map_add, hH1.dMB_add hV hz, map_add]
      map_smul' := fun r ξ ↦ by rw [map_smul, hH1.dMB_smul hz, map_smul]; rfl
      cont := N.continuous.comp ((hH1.continuous_dMB hz).comp ι₂.continuous) }
  let K : Complexification E → F₁ →L[ℝ] NormedComplexification F₂ := fun z ↦
    if hz : z ∈ W then Kop z hz else 0
  have hKeq : EqOn (N ∘ (Analysis.dMB H ∘ L)) (fun p : Complexification E × F₁ ↦ K p.1 p.2)
      (W ×ˢ univ) := fun p hp ↦ by
    simp only [K, hp.1, ↓reduceDIte]
    rfl
  have hpre : L ⁻¹' (V ×ˢ univ) = W ×ˢ univ := by ext p; simp [hL, W]
  have hKs : SmoothMBOn (fun p : Complexification E × F₁ ↦ K p.1 p.2) (W ×ˢ univ) := fun k ↦ by
    have h1 := ContDiffMBOn.comp_clm L hVV (hD.smoothMBOn hVV k)
    rw [hpre] at h1
    exact ContDiffMBOn.congr_of_isOpen hWU hKeq
      (ContDiffMBOn.comp hWU isOpen_univ (N.contDiffMBOn k univ) h1 (mapsTo_univ _ _))
  -- the differential of `K̂`
  have hder : ∀ p ∈ W ×ˢ (univ : Set F₁), ∀ v,
      HasDirDerivAt (fun p : Complexification E × F₁ ↦ K p.1 p.2) p v
        (N (Analysis.dMB (Analysis.dMB H) (L p, L v))) := fun p hp v ↦ by
    have h1 : HasDirDerivAt (Analysis.dMB H ∘ L) p v (Analysis.dMB (Analysis.dMB H) (L p, L v)) :=
      ((hD.smoothMBOn hVV 1).2.1 (L p) (by rw [← mem_preimage, hpre]; exact hp) (L v)).congr
        fun t ↦ by simp
    exact (h1.clm_comp_real N).congr_of_eventuallyEq
      (hKeq.eventuallyEq_of_mem (hWU.mem_nhds hp))
  have hKc : ∀ z ∈ W, ∀ (ξ : F₁) (c : ℂ) (h : Complexification E),
      Analysis.dMB (fun p : Complexification E × F₁ ↦ K p.1 p.2) ((z, ξ), (c • h, 0)) =
        c • Analysis.dMB (fun p : Complexification E × F₁ ↦ K p.1 p.2) ((z, ξ), (h, 0)) := by
    intro z hz ξ c h
    rw [(hder (z, ξ) ⟨hz, mem_univ _⟩ _).dMB_eq, (hder (z, ξ) ⟨hz, mem_univ _⟩ _).dMB_eq]
    have hLc : L (c • h, 0) = c • L (h, 0) := by
      simp only [hL, map_smul, map_zero, Prod.smul_mk, smul_zero]
    rw [hLc, hDhol.2 (L (z, ξ)) ⟨hz, mem_univ _⟩ c]
    exact toNormed.map_smul c _
  have hK : ComplexAnalyticOn K W := complexAnalyticOn_of_unc_clm_of_dMB_smul hW hKs hKc
  refine ⟨W, hW, fun z ↦ clmToComplexification (K z),
    (clmToComplexification.complexAnalyticOn isOpen_univ).comp hK hW isOpen_univ
      (mapsTo_univ _ _), fun y hy ↦ ?_⟩
  have hyW : ofReal y ∈ W := by
    change ι₁ (ofReal y) ∈ V
    rw [hι₁]
    exact (hext (y, 0) ⟨hy, mem_univ _⟩).1
  refine ⟨hyW, ?_⟩
  have hKy : ∀ ξ, K (ofReal y) ξ = ofCx (ofReal (g y ξ)) := fun ξ ↦ by
    simp only [K, hyW, ↓reduceDIte]
    change toNormed (Analysis.dMB H (ι₁ (ofReal y), ofReal (0, ξ))) = _
    rw [hι₁, (hasDirDerivAt_ext_unc_clm (fun x hx ↦ (hext x hx).2) hy ξ).dMB_eq]
    rfl
  ext ξ
  · change re (toCx (K (ofReal y) ξ)) = g y ξ
    rw [hKy]
    rfl
  · change im (toCx (K (ofReal y) ξ)) = 0
    rw [hKy]
    rfl

/-- **Real analytic bilinear-operator-valued maps**: if `(y, ξ, η) ↦ Ω(y) ξ η` is real analytic
on `U × F₁ × F₂`, then `y ↦ Ω(y) ∈ L(F₁, L(F₂, F₃))` is real analytic on `U` for the operator
norm (apply `RealAnalyticOn.of_unc_clm` twice). For a differential `2`-form on a manifold
modelled on a normed space `E`, with `F₁ = F₂ = E` and `F₃ = ℝ`: joint real analyticity of the
local representative `(y, u, v) ↦ Ω(y)(u)(v)` gives real analyticity of `y ↦ Ω(y)` into
`L(E, L(E, ℝ))`. -/
theorem RealAnalyticOn.of_unc_clm₂ {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    {Ω : E → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {U : Set E}
    (hΩ : RealAnalyticOn (fun p : (E × F₁) × F₂ ↦ Ω p.1.1 p.1.2 p.2) ((U ×ˢ univ) ×ˢ univ)) :
    RealAnalyticOn Ω U :=
  RealAnalyticOn.of_unc_clm (RealAnalyticOn.of_unc_clm (g := fun p : E × F₁ ↦ Ω p.1 p.2) hΩ)

end RealCase

end LocallyConvex.Analysis

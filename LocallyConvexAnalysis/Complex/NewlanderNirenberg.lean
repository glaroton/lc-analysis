/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Complex.Nijenhuis
public import LocallyConvexAnalysis.Analytic.OperatorValued
public import LocallyConvexAnalysis.Analytic.Identity
public import LocallyConvexAnalysis.Analytic.RealInverse

/-!
# The local Newlander–Nirenberg theorem for real analytic almost complex structures

Let `E` be a real Banach space, `U ⊆ E` open and `J : U → L(E)` real analytic with `J(x)² = −1`
and vanishing Nijenhuis tensor. Then every `x₀ ∈ U` has a neighbourhood with a real analytic
chart `φ`, with real analytic inverse, into a complex Banach space whose differential is complex
linear for `J`: `Dφ(x)(J(x) a) = i Dφ(x) a` (`exists_holomorphic_chart`).

This is the local part of J.-P. Penot, *Sur le théorème de Frobenius*, Bull. Soc. Math. France
98 (1970), Théorème 3.5, (6) ⇒ (1), pp. 75–76.

## Main definitions

* `extendC`, `extendCL`: the complex linear extension `w ↦ T(Re w) + i T(Im w)` to `E_ℂ` of a
  real linear map `T : E → Y` into a complex space, and the continuous complex linear map
  `T ↦ extendC T`.
* `complexifyCLM`: the complexification `A_ℂ` of a real operator `A`, on the normed
  complexification `E_ℂ`.
* `clmOfComplexification`: the map `A + i B ↦ A + i B` from the complexification of `L(E)`
  (product topology) to `L_ℝ(E, E_ℂ)` with the operator norm.

## Main results

* `RealAnalyticOn.exists_holomorphic_extension_clm`: if `J : E → L(E)` is real analytic on `U`
  (in Milnor's sense), there are an open `W ⊆ E_ℂ` containing the real points of `U` and a
  holomorphic `F : W → L_ℂ(E_ℂ)` with `F(x + i0) = J(x)_ℂ` for `x ∈ U`.
* `eqOn_ball_of_ofReal`: two holomorphic maps on a ball around `x₀ + i0` in `E_ℂ` which agree at
  its real points agree on the ball.
* `exists_transverse_coordinate`: under the hypotheses of the theorem, there is a holomorphic `w`
  near `x₀ + i0`, complex linear for `J` at real points, whose differential at `x₀` restricts to a
  real isomorphism `E ≅ ker(J(x₀)_ℂ − i)`.
* `exists_holomorphic_chart`: **the local Newlander–Nirenberg theorem, real analytic case**
  ([Pen70, Théorème 3.5, (6) ⇒ (1)]): every `x₀ ∈ U` lies in the domain of a chart `φ`, real
  analytic with real analytic inverse, into the complex Banach space `ker(J(x₀)_ℂ − i)`, with
  `Dφ(x)(J(x) a) = i Dφ(x) a`.

## Implementation notes

The proof has five steps.

1. *Holomorphic extension.* Real analyticity in Milnor's sense gives a complex analytic
   extension of `J` to the complexification; composed with the complexification of operators
   (`complexifyCLM`) it is a holomorphic `F : W → L_ℂ(E_ℂ)` with `F(x + i0) = J(x)_ℂ`
   (`RealAnalyticOn.exists_holomorphic_extension_clm`).
2. *Propagation.* `F² = −1` and `N_F = 0` hold at the real points (`nijenhuis_eq_zero_of_ofReal`)
   and hence, by the identity theorem (`ComplexAnalyticOn.eqOn_of_eqOn_real`), on a ball around
   `x₀ + i0`.
3. *Frobenius.* The distribution `ker(F + i)` is then the field of graphs of a holomorphic map
   satisfying (Frob) (`exists_graph_frob_of_nijenhuis`), and the holomorphic Frobenius theorem
   (`exists_frobenius_chart_holomorphic`) gives `Φ` with `DΦ⁻¹` mapping `ker(F + i)` into
   `ker(F(z₀) + i) × 0`.
4. *The chart.* The transverse coordinate `w(z) = (Φ⁻¹(ℓ z))₂ ∈ ker(J₀_ℂ − i)` is holomorphic and
   kills `ker(F + i)`; restricted to `E` it satisfies `Dw(x)(J(x) a) = i Dw(x) a`, and its
   differential at `x₀` is a real isomorphism `E ≅ ker(J₀_ℂ − i)`, so the inverse function
   theorem applies.
5. *Real analyticity.* The chart is `w ∘ ι` with `w` holomorphic, hence real analytic
   (`ComplexAnalyticOn.realAnalyticOn`), and its inverse is real analytic by the real analytic
   inverse function theorem (`OpenPartialHomeomorph.realAnalyticOn_symm`).

Penot takes instead `x ↦ f(x, 0)` for the first component of the inverse chart; we do not claim
the present variant is new.

## References

* [J.-P. Penot, *Sur le théorème de Frobenius*][Pen70]
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

open Complexification NormedComplexification

universe u

section Complexify

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The complex linear extension `w ↦ T(Re w) + i T(Im w)` of a real linear map `T : E → Y`
into a complex space, as a linear map on `E_ℂ`. -/
def extendCₗ (T : E →L[ℝ] Y) : NormedComplexification E →ₗ[ℂ] Y where
  toFun w := T (re (toCx w)) + Complex.I • T (im (toCx w))
  map_add' v w := by simp only [toCx_add, re_add, im_add, map_add, smul_add]; abel
  map_smul' := by
    refine map_smul_of_map_I_smul (T := fun w ↦ T (re (toCx w)) + Complex.I • T (im (toCx w)))
      (fun v w ↦ ?_) (fun r w ↦ ?_) (fun w ↦ ?_)
    · simp only [toCx_add, re_add, im_add, map_add, smul_add]; abel
    · change T (re ((r : ℂ) • toCx w)) + Complex.I • T (im ((r : ℂ) • toCx w)) = _
      simp only [re_smul, im_smul, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero,
        add_zero, map_smul, smul_add]
      rw [smul_comm]
    · simp only [toCx_smul, re_smul, im_smul, Complex.I_re, Complex.I_im, zero_smul, one_smul,
        zero_sub, zero_add, map_neg, smul_add, I_smul_I_smul]
      abel

theorem extendCₗ_apply (T : E →L[ℝ] Y) (w : NormedComplexification E) :
    extendCₗ T w = T (re (toCx w)) + Complex.I • T (im (toCx w)) := rfl

theorem norm_extendCₗ_le (T : E →L[ℝ] Y) (w : NormedComplexification E) :
    ‖extendCₗ T w‖ ≤ 2 * ‖T‖ * ‖w‖ := by
  rw [extendCₗ_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Complex.norm_I, one_mul]
  have h1 := (T.le_opNorm (re (toCx w))).trans
    (mul_le_mul_of_nonneg_left (norm_re_le w) (norm_nonneg T))
  have h2 := (T.le_opNorm (im (toCx w))).trans
    (mul_le_mul_of_nonneg_left (norm_im_le w) (norm_nonneg T))
  linarith

/-- The complex linear extension of a real linear map `E → Y` to `E_ℂ`. -/
def extendC (T : E →L[ℝ] Y) : NormedComplexification E →L[ℂ] Y :=
  (extendCₗ T).mkContinuous (2 * ‖T‖) (norm_extendCₗ_le T)

@[simp] theorem extendC_apply (T : E →L[ℝ] Y) (w : NormedComplexification E) :
    extendC T w = T (re (toCx w)) + Complex.I • T (im (toCx w)) := rfl

theorem extendC_ofRealCLM (T : E →L[ℝ] Y) (a : E) : extendC T (ofRealCLM a) = T a := by
  simp

/-- `T ↦ extendC T`, a continuous complex linear map. -/
def extendCL : (E →L[ℝ] Y) →L[ℂ] (NormedComplexification E →L[ℂ] Y) :=
  LinearMap.mkContinuous
    { toFun := extendC
      map_add' := fun S T ↦ by
        ext w; simp only [extendC_apply, add_apply, smul_add]; abel
      map_smul' := fun c T ↦ by
        ext w
        simp only [extendC_apply, smul_apply, RingHom.id_apply, smul_add]
        rw [smul_comm] }
    2 fun T ↦ by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
      exact norm_extendCₗ_le T w

@[simp] theorem extendCL_apply (T : E →L[ℝ] Y) : extendCL T = extendC T := rfl

/-- Two complex linear maps on `E_ℂ` which agree on real vectors agree. -/
theorem NormedComplexification.clm_ext_ofReal {S T : NormedComplexification E →L[ℂ] Y}
    (h : ∀ a : E, S (ofRealCLM a) = T (ofRealCLM a)) : S = T := by
  ext w
  rw [eq_ofRealCLM_add_I_smul w, map_add, map_add, map_smul, map_smul, h, h]

/-- The complexification `A_ℂ` of a real operator, on the normed complexification. -/
def complexifyCLM (A : E →L[ℝ] E) : NormedComplexification E →L[ℂ] NormedComplexification E :=
  extendC (ofRealCLM.comp A)

theorem complexifyCLM_ofRealCLM (A : E →L[ℝ] E) (a : E) :
    complexifyCLM A (ofRealCLM a) = ofRealCLM (A a) := by
  rw [complexifyCLM, extendC_ofRealCLM]; rfl

end Complexify

section Extension

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `A + i B ↦ A + i B` from the complexification of `L(E)` (product topology) to
`L_ℝ(E, E_ℂ)` with the operator norm. -/
def clmOfComplexification :
    Complexification (E →L[ℝ] E) →L[ℂ] (E →L[ℝ] NormedComplexification E) where
  toFun p := ofRealCLM.comp (re p) + Complex.I • ofRealCLM.comp (im p)
  map_add' p q := by
    simp only [re_add, im_add, ContinuousLinearMap.comp_add, smul_add]; abel
  map_smul' := by
    refine map_smul_of_map_I_smul
      (T := fun p ↦ ofRealCLM.comp (re p) + Complex.I • ofRealCLM.comp (im p))
      (fun p q ↦ ?_) (fun r p ↦ ?_) (fun p ↦ ?_)
    · simp only [re_add, im_add, ContinuousLinearMap.comp_add, smul_add]; abel
    · simp only [re_real_smul, im_real_smul, ContinuousLinearMap.comp_smul, smul_add]
      rw [smul_comm]
    · simp only [re_smul, im_smul, Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_sub,
        zero_add, ContinuousLinearMap.comp_neg, smul_add]
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
      abel
  cont := ((ContinuousLinearMap.compL ℝ E E _ ofRealCLM).continuous.comp continuous_re).add
    (((ContinuousLinearMap.compL ℝ E E _ ofRealCLM).continuous.comp continuous_im).const_smul
      Complex.I)

@[simp] theorem clmOfComplexification_ofReal (A : E →L[ℝ] E) :
    clmOfComplexification (ofReal A) = ofRealCLM.comp A := by
  have h : clmOfComplexification (ofReal A) =
      ofRealCLM.comp (re (ofReal A)) + Complex.I • ofRealCLM.comp (im (ofReal A)) := rfl
  rw [h, re_ofReal, im_ofReal, ContinuousLinearMap.comp_zero, smul_zero, add_zero]

/-- **Holomorphic extension of a real analytic field of operators.** If `J : E → L(E)` is real
analytic on `U` (in Milnor's sense), there are an open `W ⊆ E_ℂ` containing the real points of
`U` and a holomorphic `F : W → L_ℂ(E_ℂ)` with `F(x + i0) = J(x)_ℂ` for `x ∈ U`. -/
theorem RealAnalyticOn.exists_holomorphic_extension_clm {J : E → E →L[ℝ] E} {U : Set E}
    (hJ : RealAnalyticOn J U) :
    ∃ W : Set (NormedComplexification E), IsOpen W ∧
      ∃ F : NormedComplexification E → NormedComplexification E →L[ℂ] NormedComplexification E,
        DifferentiableOn ℂ F W ∧
          ∀ x ∈ U, ofRealCLM x ∈ W ∧ F (ofRealCLM x) = complexifyCLM (J x) := by
  obtain ⟨V, hV, g, hg, hext⟩ := hJ
  set W : Set (NormedComplexification E) := ofNormed ⁻¹' V
  have hW : IsOpen W := hV.preimage ofNormed.continuous
  set F : NormedComplexification E → NormedComplexification E →L[ℂ] NormedComplexification E :=
    fun z ↦ extendCL (clmOfComplexification (g (ofNormed z)))
  have hFa : ComplexAnalyticOn F W :=
    ((extendCL.comp clmOfComplexification).complexAnalyticOn isOpen_univ).comp
      (hg.comp (ofNormed.complexAnalyticOn hW) hW hV fun _ hz ↦ hz) hW isOpen_univ
      (mapsTo_univ _ _)
  refine ⟨W, hW, F, hFa.differentiableOn hW, fun x hx ↦ ⟨(hext x hx).1, ?_⟩⟩
  change extendCL (clmOfComplexification (g (ofReal x))) = _
  rw [(hext x hx).2, clmOfComplexification_ofReal]
  rfl

end Extension

section Aux

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- If `ψ ∘ φ = id` near `p`, then `Dψ(φ p) ∘ Dφ(p) = id`. -/
theorem fderiv_comp_eq_id_of_leftInverse {φ : X → Y} {ψ : Y → X} {p : X}
    (hφ : DifferentiableAt 𝕜 φ p) (hψ : DifferentiableAt 𝕜 ψ (φ p))
    (h : ∀ᶠ q in 𝓝 p, ψ (φ q) = q) :
    (fderiv 𝕜 ψ (φ p)).comp (fderiv 𝕜 φ p) = ContinuousLinearMap.id 𝕜 X :=
  ((hψ.hasFDerivAt.comp p hφ.hasFDerivAt).congr_of_eventuallyEq
    (h.mono fun _ hq ↦ hq.symm : (fun q ↦ q) =ᶠ[𝓝 p] ψ ∘ φ)).unique (hasFDerivAt_id p)

end Aux

section HolomorphicAux

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- The derivative of a holomorphic map, evaluated along a holomorphic field, is holomorphic. -/
theorem differentiableOn_fderiv_apply {f : G → Y} {B : Set G} (hB : IsOpen B)
    (hf : DifferentiableOn ℂ f B) {v : G → G} (hv : DifferentiableOn ℂ v B) :
    DifferentiableOn ℂ (fun z ↦ fderiv ℂ f z (v z)) B := by
  have hD : DifferentiableOn ℂ (dMB f) (B ×ˢ univ) :=
    ((hf.complexAnalyticOn hB).dMB hB).differentiableOn (hB.prod isOpen_univ)
  have hc : DifferentiableOn ℂ (fun z ↦ dMB f (z, v z)) B :=
    hD.comp (differentiableOn_id.prodMk hv) fun z hz ↦ ⟨hz, mem_univ _⟩
  refine hc.congr fun z hz ↦ ?_
  exact ((((hf z hz).differentiableAt (hB.mem_nhds hz)).hasFDerivAt.restrictScalars ℝ).hasDirDerivAt
    (v z)).dMB_eq.symm

/-- Holomorphic maps are real smooth. -/
theorem DifferentiableOn.contDiffOn_real {f : G → Y} {B : Set G} (hB : IsOpen B)
    (hf : DifferentiableOn ℂ f B) : ContDiffOn ℝ ∞ f B :=
  (smoothMBOn_iff_contDiffOn hB).1 ((hf.complexAnalyticOn hB).smoothMBOn hB)

end HolomorphicAux

section Main

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Propagation from the real points.** Two holomorphic maps on a ball around `x₀ + i0` in
`E_ℂ` which agree at its real points agree on the ball. -/
theorem eqOn_ball_of_ofReal {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    {f g : NormedComplexification E → Y} {x₀ : E} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (ofRealCLM x₀) r))
    (hg : DifferentiableOn ℂ g (Metric.ball (ofRealCLM x₀) r)) (hr : 0 < r)
    (h : ∀ y : E, ofRealCLM y ∈ Metric.ball (ofRealCLM x₀) r → f (ofRealCLM y) = g (ofRealCLM y)) :
    EqOn f g (Metric.ball (ofRealCLM x₀) r) := by
  refine (hf.complexAnalyticOn Metric.isOpen_ball).eqOn_of_eqOn_real Metric.isOpen_ball
    (convex_ball _ _).isPreconnected (hg.complexAnalyticOn Metric.isOpen_ball)
    (LinearMap.range (ofRealCLM (E := E) : E →ₗ[ℝ] NormedComplexification E)) (fun w ↦ ?_)
    (Metric.mem_ball_self hr) ?_
  · exact ⟨ofRealCLM (re (toCx w)), ⟨_, rfl⟩, ofRealCLM (im (toCx w)), ⟨_, rfl⟩,
      eq_ofRealCLM_add_I_smul w⟩
  · rintro _ ⟨c, rfl⟩ hc
    have e : ofRealCLM x₀ + (ofRealCLM (E := E) : E →ₗ[ℝ] NormedComplexification E) c =
        ofRealCLM (x₀ + c) := (map_add ofRealCLM x₀ c).symm
    rw [e] at hc ⊢
    exact h _ hc

/-- The transverse coordinate of the proof of `exists_holomorphic_chart` (steps 1–4 of the
module documentation): a holomorphic
`w` near `x₀ + i0`, complex linear for `J` at real points, whose differential at `x₀` restricts to
a real isomorphism `E ≅ ker(J(x₀)_ℂ − i)`. -/
theorem exists_transverse_coordinate [CompleteSpace E] {J : E → E →L[ℝ] E} {U : Set E}
    (hU : IsOpen U) (hJ : RealAnalyticOn J U) (hsq : ∀ x ∈ U, ∀ v, J x (J x v) = -v)
    (hN : ∀ x ∈ U, nijenhuis ℝ J x = 0) {x₀ : E} (h₀ : x₀ ∈ U) :
    ∃ D : Set (NormedComplexification E), IsOpen D ∧ ofRealCLM x₀ ∈ D ∧
      ∃ w : NormedComplexification E → typeOneZero (complexifyCLM (J x₀)),
        DifferentiableOn ℂ w D ∧
        (∀ x ∈ U, ofRealCLM x ∈ D → ∀ a, fderiv ℂ w (ofRealCLM x) (ofRealCLM (J x a)) =
          Complex.I • fderiv ℂ w (ofRealCLM x) (ofRealCLM a)) ∧
        LinearMap.ker ((((fderiv ℂ w (ofRealCLM x₀)).restrictScalars ℝ).comp ofRealCLM :
          E →L[ℝ] typeOneZero (complexifyCLM (J x₀))) :
            E →ₗ[ℝ] typeOneZero (complexifyCLM (J x₀))) = ⊥ ∧
        LinearMap.range ((((fderiv ℂ w (ofRealCLM x₀)).restrictScalars ℝ).comp ofRealCLM :
          E →L[ℝ] typeOneZero (complexifyCLM (J x₀))) :
            E →ₗ[ℝ] typeOneZero (complexifyCLM (J x₀))) = ⊤ := by
  set G := NormedComplexification E
  have hJs : ContDiffOn ℝ ∞ J U := (smoothMBOn_iff_contDiffOn hU).1 (hJ.smoothMBOn hU)
  have hJd : ∀ x ∈ U, DifferentiableAt ℝ J x := fun x hx ↦
    (hJs.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
  -- 1. the holomorphic extension
  obtain ⟨W, hW, F, hFd, hFext⟩ := hJ.exists_holomorphic_extension_clm
  have hFr : ∀ x ∈ U, ∀ b, F (ofRealCLM x) (ofRealCLM b) = ofRealCLM (J x b) := fun x hx b ↦ by
    rw [(hFext x hx).2, complexifyCLM_ofRealCLM]
  set z₀ : G := ofRealCLM x₀
  -- 2. a ball around `z₀` whose real points lie in `U`
  obtain ⟨r₁, hr₁, hr₁W⟩ := Metric.isOpen_iff.1 hW z₀ (hFext x₀ h₀).1
  obtain ⟨r₂, hr₂, hr₂U⟩ := Metric.isOpen_iff.1 hU x₀ h₀
  set r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  set B := Metric.ball z₀ r
  have hB : IsOpen B := Metric.isOpen_ball
  have hBW : B ⊆ W := (Metric.ball_subset_ball (min_le_left _ _)).trans hr₁W
  have hBU : ∀ y : E, ofRealCLM y ∈ B → y ∈ U := fun y hy ↦ by
    refine hr₂U ?_
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    rw [← map_sub, norm_ofRealCLM] at hy
    exact hy.trans_le (min_le_right _ _)
  have hFB : DifferentiableOn ℂ F B := hFd.mono hBW
  -- `F² = −1` on `B`
  have hsqB : ∀ z ∈ B, ∀ v, F z (F z v) = -v := by
    have hcomp : DifferentiableOn ℂ (fun z ↦ (F z).comp (F z)) B := hFB.clm_comp hFB
    have heq := eqOn_ball_of_ofReal hcomp
      (differentiableOn_const (-ContinuousLinearMap.id ℂ G)) hr fun y hy ↦ ?_
    · intro z hz v
      have := congrArg (fun L : G →L[ℂ] G ↦ L v) (heq hz)
      simpa using this
    · refine clm_ext_ofReal fun b ↦ ?_
      have hyU := hBU y hy
      simp only [ContinuousLinearMap.comp_apply, neg_apply, hFr y hyU,
        hsq y hyU, map_neg]
      rfl
  -- `N_F = 0` on `B`
  have hNB : ∀ z ∈ B, nijenhuis ℂ F z = 0 := by
    intro z hz
    ext a b
    have hdiff : DifferentiableOn ℂ (fun z ↦ nijenhuis ℂ F z a b) B := by
      simp only [nijenhuis_apply]
      have h1 := (differentiableOn_fderiv_apply hB hFB (hFB.clm_apply (differentiableOn_const a)))
      have h2 := (differentiableOn_fderiv_apply hB hFB (hFB.clm_apply (differentiableOn_const b)))
      have h3 := differentiableOn_fderiv_apply hB hFB (differentiableOn_const (E := G) b)
      have h4 := differentiableOn_fderiv_apply hB hFB (differentiableOn_const (E := G) a)
      exact (((h1.clm_apply (differentiableOn_const b)).sub
        (h2.clm_apply (differentiableOn_const a))).add
        (hFB.clm_apply (h3.clm_apply (differentiableOn_const a)))).sub
        (hFB.clm_apply (h4.clm_apply (differentiableOn_const b)))
    have heq := eqOn_ball_of_ofReal hdiff (differentiableOn_const 0) hr fun y hy ↦ ?_
    · exact heq hz
    · have hyU := hBU y hy
      have hext : ∀ᶠ y' in 𝓝 y, ∀ b, F (ofRealCLM y') (ofRealCLM b) = ofRealCLM (J y' b) :=
        eventually_of_mem (hU.mem_nhds hyU) fun y' hy' ↦ hFr y' hy'
      have hFy : DifferentiableAt ℂ F (ofRealCLM y) := (hFB _ hy).differentiableAt (hB.mem_nhds hy)
      rw [nijenhuis_eq_zero_of_ofReal (hJd y hyU) hFy hext (hN y hyU)]
      rfl
  -- 3. the graph form of `ker(F + i)` and (Frob)
  set A := complexifyCLM (J x₀)
  have hz₀B : z₀ ∈ B := Metric.mem_ball_self hr
  have hA0 : F z₀ = A := (hFext x₀ h₀).2
  have hA : ∀ v, A (A v) = -v := fun v ↦ by rw [← hA0]; exact hsqB z₀ hz₀B v
  obtain ⟨O', hO', hz₀O', hO'B, hgraph, hfd, hfrob⟩ :=
    exists_graph_frob_of_nijenhuis hB hFB hsqB hNB hz₀B hA0 hA
  set ℓ := typeSplit hA
  set f := graphField F A hA
  have : CompleteSpace (typeZeroOne A) := (isClosed_typeZeroOne A).completeSpace_coe
  have : CompleteSpace (typeOneZero A) := (isClosed_typeOneZero A).completeSpace_coe
  have hO : IsOpen (ℓ '' O') := ℓ.toHomeomorph.isOpenMap _ hO'
  set q₀ := ℓ z₀
  have hq₀ : (q₀.1, q₀.2) ∈ ℓ '' O' := ⟨z₀, hz₀O', rfl⟩
  -- 4. the holomorphic Frobenius chart
  obtain ⟨Φ, hq₀s, hΦq₀, -, hΦtO, hΦa, hΦsa, -, hΦd, hΦmap⟩ :=
    exists_frobenius_chart_holomorphic hO hfd hfrob hq₀
  simp only [Prod.mk.eta] at hq₀s hΦq₀
  have hq₀t : q₀ ∈ Φ.target := by rw [← hΦq₀]; exact Φ.map_source hq₀s
  have hΦsq₀ : Φ.symm q₀ = q₀ := by
    have := Φ.left_inv hq₀s
    rwa [hΦq₀] at this
  have hΦdiff : DifferentiableOn ℂ Φ Φ.source := hΦa.differentiableOn Φ.open_source
  have hΦsdiff : DifferentiableOn ℂ Φ.symm Φ.target := hΦsa.differentiableOn Φ.open_target
  have hΦdq₀ : DifferentiableAt ℂ Φ q₀ := (hΦdiff q₀ hq₀s).differentiableAt
    (Φ.open_source.mem_nhds hq₀s)
  have hΦsdq₀ : DifferentiableAt ℂ Φ.symm q₀ := (hΦsdiff q₀ hq₀t).differentiableAt
    (Φ.open_target.mem_nhds hq₀t)
  have hLL' : (fderiv ℂ Φ q₀).comp (fderiv ℂ Φ.symm q₀) = ContinuousLinearMap.id ℂ _ := by
    have h := fderiv_comp_eq_id_of_leftInverse (φ := Φ.symm) (ψ := Φ) hΦsdq₀
      (by rw [hΦsq₀]; exact hΦdq₀)
      (eventually_of_mem (Φ.open_target.mem_nhds hq₀t) fun q hq ↦ Φ.right_inv hq)
    rwa [hΦsq₀] at h
  have hL'L : (fderiv ℂ Φ.symm q₀).comp (fderiv ℂ Φ q₀) = ContinuousLinearMap.id ℂ _ := by
    have h := fderiv_comp_eq_id_of_leftInverse (φ := Φ) (ψ := Φ.symm) hΦdq₀
      (by rw [hΦq₀]; exact hΦsdq₀)
      (eventually_of_mem (Φ.open_source.mem_nhds hq₀s) fun q hq ↦ Φ.left_inv hq)
    rwa [hΦq₀] at h
  -- 5. the transverse coordinate `w = (Φ⁻¹ ∘ ℓ)₂`
  set D : Set G := ℓ ⁻¹' Φ.target
  have hD : IsOpen D := Φ.open_target.preimage ℓ.continuous
  have hz₀D : z₀ ∈ D := hq₀t
  have hDO' : D ⊆ O' := fun z hz ↦ by
    obtain ⟨z', hz', he⟩ := hΦtO hz
    rwa [← ℓ.injective he]
  set w : G → typeOneZero A := fun z ↦ (Φ.symm (ℓ z)).2
  have hwh : ∀ z ∈ D, HasFDerivAt w ((ContinuousLinearMap.snd ℂ _ _).comp
      ((fderiv ℂ Φ.symm (ℓ z)).comp (ℓ : G →L[ℂ] typeZeroOne A × typeOneZero A))) z :=
    fun z hz ↦ (((hΦsdiff _ hz).differentiableAt (Φ.open_target.mem_nhds hz)).hasFDerivAt.comp
      z ℓ.hasFDerivAt).snd
  have hwd : DifferentiableOn ℂ w D := fun z hz ↦ (hwh z hz).differentiableAt.differentiableWithinAt
  have hwapp : ∀ z ∈ D, ∀ v, fderiv ℂ w z v = (fderiv ℂ Φ.symm (ℓ z) (ℓ v)).2 := fun z hz v ↦ by
    rw [(hwh z hz).fderiv]; rfl
  -- `Dw` kills `ker(F + i)`
  have hker : ∀ z ∈ D, ∀ v, F z v = -(Complex.I • v) → fderiv ℂ w z v = 0 := by
    intro z hz v hv
    have hmem : ℓ v ∈ ((f (ℓ z) : typeZeroOne A →ₗ[ℂ] typeOneZero A)).graph :=
      (LinearMap.mem_graph_iff _ _).2 ((hgraph z (hDO' hz) v).1 hv)
    have h := Submodule.mem_map_of_mem
      (f := ((fderiv ℂ Φ.symm (ℓ z) : _ →L[ℂ] _) :
        typeZeroOne A × typeOneZero A →ₗ[ℂ] typeZeroOne A × typeOneZero A)) hmem
    rw [hΦmap (ℓ z) hz] at h
    obtain ⟨u, hu⟩ := h
    rw [hwapp z hz]
    have hu' : fderiv ℂ Φ.symm (ℓ z) (ℓ v) = (u, 0) := hu.symm
    rw [hu']
  -- at `z₀`, the kernel of `Dw` is exactly `ker(F(z₀) + i)`
  have hker' : ∀ v, fderiv ℂ w z₀ v = 0 → F z₀ v = -(Complex.I • v) := by
    intro v hv
    rw [hwapp z₀ hz₀D] at hv
    set p := fderiv ℂ Φ.symm q₀ (ℓ v)
    have hp : p = (p.1, 0) := Prod.ext rfl hv
    have hℓv : ℓ v = fderiv ℂ Φ q₀ p := by
      have := congrArg (fun L : _ →L[ℂ] _ ↦ L (ℓ v)) hLL'
      exact this.symm
    rw [hp, hΦd q₀ hq₀s, hΦq₀] at hℓv
    refine (hgraph z₀ hz₀O' v).2 ?_
    rw [hℓv]
  have hsurj : ∀ m : typeOneZero A, ∃ v, fderiv ℂ w z₀ v = m := by
    intro m
    refine ⟨ℓ.symm (fderiv ℂ Φ q₀ (0, m)), ?_⟩
    rw [hwapp z₀ hz₀D, ContinuousLinearEquiv.apply_symm_apply]
    have := congrArg (fun L : _ →L[ℂ] _ ↦ L (0, m)) hL'L
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [this]
  -- `Dw(x)(J(x) a) = i Dw(x) a` at real points
  have hJw : ∀ x ∈ U, ofRealCLM x ∈ D → ∀ a, fderiv ℂ w (ofRealCLM x) (ofRealCLM (J x a)) =
      Complex.I • fderiv ℂ w (ofRealCLM x) (ofRealCLM a) := by
    intro x hxU hxD a
    set v := ofRealCLM a + Complex.I • ofRealCLM (J x a)
    have hv : F (ofRealCLM x) v = -(Complex.I • v) := by
      simp only [v, map_add, map_smul, hFr x hxU, hsq x hxU, map_neg, smul_add, smul_neg,
        I_smul_I_smul]
      abel
    have h := hker _ hxD v hv
    simp only [v, map_add, map_smul] at h
    have h2 : Complex.I • fderiv ℂ w (ofRealCLM x) (ofRealCLM a) +
        Complex.I • Complex.I • fderiv ℂ w (ofRealCLM x) (ofRealCLM (J x a)) = 0 := by
      rw [← smul_add, h, smul_zero]
    rw [I_smul_I_smul] at h2
    linear_combination (norm := module) -h2
  -- 6. `Dw(x₀)` restricted to `E` is a real isomorphism
  set L₀ : E →L[ℝ] typeOneZero A :=
    ((fderiv ℂ w z₀).restrictScalars ℝ).comp ofRealCLM
  have hinj : LinearMap.ker (L₀ : E →ₗ[ℝ] typeOneZero A) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun a ha ↦ ?_
    have h := hker' (ofRealCLM a) ha
    rw [hA0, complexifyCLM_ofRealCLM] at h
    have him := congrArg (fun p : G ↦ im (toCx p)) (eq_neg_iff_add_eq_zero.1 h)
    change im (ofReal (J x₀ a) + Complex.I • ofReal a) = im (0 : Complexification E) at him
    simp only [im_add, im_smul, im_ofReal, re_ofReal, Complex.I_re, Complex.I_im, zero_smul,
      one_smul, zero_add] at him
    exact him.trans rfl
  have hrange : LinearMap.range (L₀ : E →ₗ[ℝ] typeOneZero A) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun m ↦ ?_
    obtain ⟨v, hv⟩ := hsurj m
    refine ⟨re (toCx v) + J x₀ (im (toCx v)), ?_⟩
    change fderiv ℂ w z₀ (ofRealCLM (re (toCx v) + J x₀ (im (toCx v)))) = m
    rw [map_add, map_add, hJw x₀ h₀ hz₀D, ← map_smul, ← map_add, ← eq_ofRealCLM_add_I_smul, hv]
  exact ⟨D, hD, hz₀D, w, hwd, hJw, hinj, hrange⟩

/-- **The local Newlander–Nirenberg theorem, real analytic case** (Penot, *Sur le théorème de
Frobenius*, Bull. Soc. Math. France 98 (1970), Théorème 3.5, (6) ⇒ (1), pp. 75–76). Let `E` be a
real Banach space, `U ⊆ E` open and `J : U → L(E)` real analytic with `J(x)² = −1` and vanishing
Nijenhuis tensor. Then every `x₀ ∈ U` lies in the domain of a chart `φ`, real analytic with real
analytic inverse (in particular smooth), into the complex Banach space `ker(J(x₀)_ℂ − i)`
(isomorphic to `(E, J(x₀))`), whose differential is complex linear for `J`:
`Dφ(x)(J(x) a) = i Dφ(x) a`. -/
theorem exists_holomorphic_chart [CompleteSpace E] {J : E → E →L[ℝ] E} {U : Set E}
    (hU : IsOpen U) (hJ : RealAnalyticOn J U) (hsq : ∀ x ∈ U, ∀ v, J x (J x v) = -v)
    (hN : ∀ x ∈ U, nijenhuis ℝ J x = 0) {x₀ : E} (h₀ : x₀ ∈ U) :
    ∃ φ : OpenPartialHomeomorph E (typeOneZero (complexifyCLM (J x₀))),
      x₀ ∈ φ.source ∧ φ.source ⊆ U ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      (∀ x ∈ φ.source, ∀ a, fderiv ℝ φ x (J x a) = Complex.I • fderiv ℝ φ x a) ∧
      RealAnalyticOn φ φ.source ∧ RealAnalyticOn φ.symm φ.target := by
  set A := complexifyCLM (J x₀)
  obtain ⟨D, hD, hz₀D, w, hwd, hJw', hinj, hrange⟩ :=
    exists_transverse_coordinate hU hJ hsq hN h₀
  -- the restriction to the real points
  set V₀ : Set E := U ∩ ofRealCLM ⁻¹' D
  have hV₀ : IsOpen V₀ := hU.inter (hD.preimage ofRealCLM.continuous)
  have hx₀V : x₀ ∈ V₀ := ⟨h₀, hz₀D⟩
  set φ₀ : E → typeOneZero A := fun x ↦ w (ofRealCLM x)
  have hwC : ContDiffOn ℝ ∞ w D := DifferentiableOn.contDiffOn_real hD hwd
  have hφC : ContDiffOn ℝ ∞ φ₀ V₀ :=
    hwC.comp ofRealCLM.contDiff.contDiffOn fun x hx ↦ hx.2
  have hφd : ∀ x ∈ V₀, HasFDerivAt φ₀
      (((fderiv ℂ w (ofRealCLM x)).restrictScalars ℝ).comp ofRealCLM) x := fun x hx ↦
    (((hwd _ hx.2).differentiableAt (hD.mem_nhds hx.2)).hasFDerivAt.restrictScalars ℝ).comp x
      ofRealCLM.hasFDerivAt
  have hJw : ∀ x ∈ V₀, ∀ a, fderiv ℂ w (ofRealCLM x) (ofRealCLM (J x a)) =
      Complex.I • fderiv ℂ w (ofRealCLM x) (ofRealCLM a) := fun x hx a ↦ hJw' x hx.1 hx.2 a
  -- `Dφ₀(x₀)` is a real isomorphism
  set L₀ : E →L[ℝ] typeOneZero A :=
    ((fderiv ℂ w (ofRealCLM x₀)).restrictScalars ℝ).comp ofRealCLM
  set e := ContinuousLinearEquiv.ofBijective L₀ hinj hrange
  have hder : HasFDerivAt φ₀ (e : E →L[ℝ] typeOneZero A) x₀ := hφd x₀ hx₀V
  -- the inverse function theorem
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set H := (hφC.contDiffAt (hV₀.mem_nhds hx₀V)).toOpenPartialHomeomorph φ₀ hder hn
  set S := V₀ ∩ fderiv ℝ φ₀ ⁻¹' range ((↑) : (E ≃L[ℝ] typeOneZero A) → E →L[ℝ] typeOneZero A)
  have hS : IsOpen S := (hφC.continuousOn_fderiv_of_isOpen hV₀ (by simp)).isOpen_inter_preimage
    hV₀ ContinuousLinearEquiv.isOpen
  have hx₀S : x₀ ∈ S := ⟨hx₀V, e, hder.fderiv.symm⟩
  set φ := H.restrOpen S hS
  have hsrc : φ.source ⊆ S := fun x hx ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source] at hx; exact hx.2
  have hsrcV : φ.source ⊆ V₀ := fun x hx ↦ (hsrc hx).1
  have hx₀src : x₀ ∈ φ.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hder hn, hx₀S⟩
  -- real analyticity: `φ = w ∘ ι` with `w` holomorphic, and the analytic inverse function theorem
  have hcoe : (⇑φ : E → typeOneZero A) = φ₀ := by
    simp only [φ, H, OpenPartialHomeomorph.coe_restrOpen, ContDiffAt.toOpenPartialHomeomorph_coe]
  have hφa : RealAnalyticOn φ φ.source := by
    rw [hcoe]
    exact (((hwd.complexAnalyticOn hD).realAnalyticOn hD).comp_clm ofRealCLM).mono
      fun x hx ↦ (hsrcV hx).2
  have hφe : ∀ x ∈ φ.source, ∃ e' : E ≃L[ℝ] typeOneZero A,
      HasFDerivAt φ (e' : E →L[ℝ] typeOneZero A) x := fun x hx ↦ by
    obtain ⟨hpV, e', he'⟩ := hsrc hx
    refine ⟨e', ?_⟩
    rw [hcoe, he', (hφd _ hpV).fderiv]
    exact hφd _ hpV
  refine ⟨φ, hx₀src, fun x hx ↦ (hsrcV hx).1, hφC.mono hsrcV, ?_, fun x hx a ↦ ?_, hφa,
    φ.realAnalyticOn_symm hφa hφe⟩
  · intro z hz
    obtain ⟨hpV, e', he'⟩ := hsrc (φ.map_target hz)
    have hd : HasFDerivAt φ (e' : E →L[ℝ] typeOneZero A) (φ.symm z) := by
      rw [he', (hφd _ hpV).fderiv]; exact hφd _ hpV
    exact (φ.contDiffAt_symm hz hd (hφC.contDiffAt (hV₀.mem_nhds hpV))).contDiffWithinAt
  · have hxV := hsrcV hx
    rw [hcoe, (hφd x hxV).fderiv]
    exact hJw x hxV a

end Main

end LocallyConvex.Analysis

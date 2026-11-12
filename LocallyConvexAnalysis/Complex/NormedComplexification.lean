/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Real
public import Mathlib.Analysis.Complex.Circle

/-!
# A complex norm on the complexification of a real normed space

Let `E` be a real normed space. Its complexification `E_ℂ = E × E` (`Complexification E`,
[GN26, Definition 2.2.1]) carries the product topology, which is defined by the norm
`max (‖u‖, ‖v‖)`; but this norm is not a complex norm: `‖i (u + i v)‖ = ‖-v + i u‖` is fine, but
`‖e^{iθ} (u + i v)‖` need not be `‖u + i v‖`. To use the Banach space tools of Mathlib over `ℂ`
(the inverse function theorem, holomorphic functions on Banach spaces) we equip a copy of `E_ℂ`
with the **rotation invariant norm**
`‖u + i v‖_ℂ = sup_{|w| = 1} ‖Re (w (u + i v))‖ = sup_θ ‖cos θ u - sin θ v‖`.

## Main definitions and results

* `NormedComplexification E`: a type synonym of `Complexification E` with the complex normed
  space structure given by the norm above (`NormedComplexification.instNormedSpace`), induced by
  the injective map `profile : E_ℂ → C(S¹, E)`, `p ↦ (w ↦ Re (w p))`.
* `NormedComplexification.norm_re_le`, `norm_im_le`, `norm_le`:
  `max (‖u‖, ‖v‖) ≤ ‖u + i v‖_ℂ ≤ ‖u‖ + ‖v‖`; hence `‖u + i 0‖_ℂ = ‖u‖` (`norm_ofRealCLM`), and
  the norm defines the product topology: `toNormed : E_ℂ →L[ℂ] NormedComplexification E` and
  `ofNormed` are mutually inverse continuous complex linear maps.
* `NormedComplexification.instCompleteSpace`: if `E` is a Banach space, so is
  `NormedComplexification E`.
* `Complexification.toComplexCLM`: the complex linear homeomorphism `ℝ_ℂ ≅ ℂ`.

## Implementation notes

* The norm is Taylor's complexification of the norm of `E`, the smallest *reasonable*
  complexification norm (G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real
  Banach spaces, polynomials and multilinear maps*, Studia Math. 134 (1999), Proposition 3, p. 4);
  Glöckner and Neeb use the largest one, the Minkowski functional of the absolutely convex hull of
  the unit ball of `E`
  (*Infinite-Dimensional Lie Groups*, Exercise 2.3.7, p. 181). Any complex norm extending
  `‖·‖` and defining the product topology serves our purpose; the supremum over the circle is
  convenient because it is induced by a map into a normed space.
* `NormedComplexification E` is a separate type, not an instance on `Complexification E`: the
  latter already carries the product topology, and a norm instance on it would create a second,
  only propositionally equal, topology. Its real structure is the restriction of scalars of the
  complex one (`NormedSpace.complexToReal`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u

/-- The complexification `E_ℂ` of a real normed space `E`, with the rotation invariant norm
`‖u + i v‖ = sup_{|w| = 1} ‖Re (w (u + i v))‖`. -/
def NormedComplexification (E : Type u) : Type u := Complexification E

namespace NormedComplexification

open Complexification

variable {E : Type u}

/-- The underlying point of `E_ℂ`. -/
def toCx (p : NormedComplexification E) : Complexification E := p

/-- A point of `E_ℂ`, in the normed copy. -/
def ofCx (p : Complexification E) : NormedComplexification E := p

@[simp] theorem toCx_ofCx (p : Complexification E) : toCx (ofCx p) = p := rfl
@[simp] theorem ofCx_toCx (p : NormedComplexification E) : ofCx (toCx p) = p := rfl

section Algebra

variable [AddCommGroup E]

instance : AddCommGroup (NormedComplexification E) :=
  inferInstanceAs (AddCommGroup (Complexification E))

@[simp] theorem toCx_add (p q : NormedComplexification E) : toCx (p + q) = toCx p + toCx q := rfl
@[simp] theorem toCx_sub (p q : NormedComplexification E) : toCx (p - q) = toCx p - toCx q := rfl
@[simp] theorem toCx_zero : toCx (0 : NormedComplexification E) = 0 := rfl

variable [Module ℝ E]

instance : Module ℂ (NormedComplexification E) :=
  inferInstanceAs (Module ℂ (Complexification E))

@[simp] theorem toCx_smul (c : ℂ) (p : NormedComplexification E) :
    toCx (c • p) = c • toCx p := rfl

/-- `Re (c p) = Re c • Re p - Im c • Im p`, for `c ∈ ℂ` and `p ∈ E_ℂ`. -/
def rot (c : ℂ) (p : Complexification E) : E :=
  c.re • re p - c.im • im p

theorem rot_eq_re_smul (c : ℂ) (p : Complexification E) : rot c p = re (c • p) := rfl

theorem rot_mul (c d : ℂ) (p : Complexification E) : rot c (d • p) = rot (c * d) p := by
  simp only [rot, re_smul, im_smul, Complex.mul_re, Complex.mul_im, smul_sub, smul_add,
    smul_smul, sub_smul, add_smul]
  abel

theorem rot_one (p : Complexification E) : rot 1 p = re p := by simp [rot]

theorem rot_negI (p : Complexification E) : rot (-Complex.I) p = im p := by simp [rot]

theorem rot_real_smul (r : ℝ) (c : ℂ) (p : Complexification E) :
    rot ((r : ℂ) * c) p = r • rot c p := by
  simp only [rot, Complex.re_ofReal_mul, Complex.im_ofReal_mul, smul_sub, smul_smul]

end Algebra

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **profile** `p ↦ (w ↦ Re (w p))` of a point of `E_ℂ` on the unit circle. -/
def profile : NormedComplexification E →+ C(Circle, E) where
  toFun p := ⟨fun w ↦ rot (w : ℂ) (toCx p), by
    unfold rot
    exact ((Complex.continuous_re.comp continuous_subtype_val).smul continuous_const).sub
      ((Complex.continuous_im.comp continuous_subtype_val).smul continuous_const)⟩
  map_zero' := by ext w; simp [rot]
  map_add' p q := by
    ext w
    simp only [rot, toCx_add, re_add, im_add, smul_add, ContinuousMap.coe_mk,
      ContinuousMap.add_apply]
    abel

@[simp] theorem profile_apply (p : NormedComplexification E) (w : Circle) :
    profile p w = rot (w : ℂ) (toCx p) := rfl

/-- The point `-i` of the unit circle. -/
def negI : Circle := ⟨-Complex.I, mem_sphere_zero_iff_norm.2 (by simp)⟩

theorem coe_negI : (negI : ℂ) = -Complex.I := rfl

theorem profile_injective : Injective (profile : NormedComplexification E → C(Circle, E)) := by
  intro p q h
  have h1 := congrArg (fun φ : C(Circle, E) ↦ φ 1) h
  have h2 := congrArg (fun φ : C(Circle, E) ↦ φ negI) h
  simp only [profile_apply, Circle.coe_one, rot_one] at h1
  rw [profile_apply, profile_apply, coe_negI, rot_negI, rot_negI] at h2
  exact Complexification.ext h1 h2

instance instNormedAddCommGroup : NormedAddCommGroup (NormedComplexification E) :=
  NormedAddCommGroup.induced (NormedComplexification E) C(Circle, E) profile profile_injective

theorem norm_def (p : NormedComplexification E) : ‖p‖ = ‖profile p‖ := rfl

theorem norm_rot_le (p : NormedComplexification E) (w : Circle) : ‖rot (w : ℂ) (toCx p)‖ ≤ ‖p‖ :=
  (profile p).norm_coe_le_norm w

/-- `‖u‖ ≤ ‖u + i v‖`. -/
theorem norm_re_le (p : NormedComplexification E) : ‖re (toCx p)‖ ≤ ‖p‖ := by
  simpa [rot_one] using norm_rot_le p 1

/-- `‖v‖ ≤ ‖u + i v‖`. -/
theorem norm_im_le (p : NormedComplexification E) : ‖im (toCx p)‖ ≤ ‖p‖ := by
  simpa [coe_negI, rot_negI] using norm_rot_le p negI

/-- `‖u + i v‖ ≤ ‖u‖ + ‖v‖`. -/
theorem norm_le (p : NormedComplexification E) : ‖p‖ ≤ ‖re (toCx p)‖ + ‖im (toCx p)‖ := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
  rw [profile_apply, rot]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      ((Complex.abs_re_le_norm _).trans (Circle.norm_coe w).le)
  · rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      ((Complex.abs_im_le_norm _).trans (Circle.norm_coe w).le)

/-- `‖Re (c p)‖ ≤ |c| ‖p‖`. -/
theorem norm_rot_le_mul (c : ℂ) (p : NormedComplexification E) :
    ‖rot c (toCx p)‖ ≤ ‖c‖ * ‖p‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [rot]
  have hn : (‖c‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hc
  set w : Circle := ⟨c / (‖c‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, norm_norm, div_self hn])⟩
  have hcw : c = (‖c‖ : ℂ) * (w : ℂ) := by
    change c = (‖c‖ : ℂ) * (c / (‖c‖ : ℂ))
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn)]
  calc ‖rot c (toCx p)‖ = ‖rot ((‖c‖ : ℂ) * (w : ℂ)) (toCx p)‖ := by rw [← hcw]
    _ = ‖c‖ * ‖rot (w : ℂ) (toCx p)‖ := by rw [rot_real_smul, norm_smul, norm_norm]
    _ ≤ ‖c‖ * ‖p‖ := mul_le_mul_of_nonneg_left (norm_rot_le p w) (norm_nonneg c)

instance instNormedSpace : NormedSpace ℂ (NormedComplexification E) where
  norm_smul_le c p := by
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun w ↦ ?_
    rw [profile_apply, toCx_smul, rot_mul]
    refine (norm_rot_le_mul _ p).trans ?_
    rw [norm_mul, Circle.norm_coe, one_mul]

/-- The real part is `1`-Lipschitz. -/
theorem lipschitzWith_re :
    LipschitzWith 1 fun p : NormedComplexification E ↦ re (toCx p) :=
  LipschitzWith.of_dist_le_mul fun p q ↦ by
    rw [dist_eq_norm (re (toCx p)), dist_eq_norm p q, NNReal.coe_one, one_mul, ← re_sub,
      ← toCx_sub]
    exact norm_re_le _

/-- The imaginary part is `1`-Lipschitz. -/
theorem lipschitzWith_im :
    LipschitzWith 1 fun p : NormedComplexification E ↦ im (toCx p) :=
  LipschitzWith.of_dist_le_mul fun p q ↦ by
    rw [dist_eq_norm (im (toCx p)), dist_eq_norm p q, NNReal.coe_one, one_mul, ← im_sub,
      ← toCx_sub]
    exact norm_im_le _

/-- If `E` is a Banach space, so is `E_ℂ` with the rotation invariant norm. -/
instance instCompleteSpace [CompleteSpace E] : CompleteSpace (NormedComplexification E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (lipschitzWith_re.uniformContinuous.comp_cauchySeq hx)
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete
    (lipschitzWith_im.uniformContinuous.comp_cauchySeq hx)
  refine ⟨ofCx (mk a b), tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_le _) ?_
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 ha)
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 hb)
  simpa using h1.add h2

/-- The identity `E_ℂ → E_ℂ`, from the product topology to the normed one, as a continuous
complex linear map. -/
def toNormed : Complexification E →L[ℂ] NormedComplexification E where
  toFun := ofCx
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    refine continuous_iff_continuousAt.2 fun p ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun q ↦ norm_le _) ?_
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (continuous_re.tendsto p)
    have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (continuous_im.tendsto p)
    simpa using h1.add h2

/-- The identity `E_ℂ → E_ℂ`, from the normed topology to the product one, as a continuous
complex linear map. -/
def ofNormed : NormedComplexification E →L[ℂ] Complexification E where
  toFun := toCx
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_mk lipschitzWith_re.continuous lipschitzWith_im.continuous

@[simp] theorem toNormed_apply (p : Complexification E) : toNormed p = ofCx p := rfl
@[simp] theorem ofNormed_apply (p : NormedComplexification E) : ofNormed p = toCx p := rfl

/-- The real space `E` inside `E_ℂ`, `u ↦ u + i 0`, as a continuous real linear map. -/
def ofRealCLM : E →L[ℝ] NormedComplexification E where
  toFun u := ofCx (ofReal u)
  map_add' u v := by
    change ofReal (u + v) = ofReal u + ofReal v
    exact map_add _ _ _
  map_smul' r u := by
    change ofReal (r • u) = (r : ℂ) • ofReal u
    rw [ofReal_smul, map_smul]
  cont := toNormed.continuous.comp ofReal.continuous

@[simp] theorem ofRealCLM_apply (u : E) : ofRealCLM u = ofCx (ofReal u) := rfl

@[simp] theorem re_toCx_ofRealCLM (u : E) : re (toCx (ofRealCLM u)) = u := rfl
@[simp] theorem im_toCx_ofRealCLM (u : E) : im (toCx (ofRealCLM u)) = 0 := rfl

/-- `‖u + i 0‖ = ‖u‖`. -/
theorem norm_ofRealCLM (u : E) : ‖ofRealCLM u‖ = ‖u‖ := by
  refine le_antisymm ((norm_le _).trans ?_) ?_
  · rw [re_toCx_ofRealCLM, im_toCx_ofRealCLM, norm_zero, add_zero]
  · simpa only [re_toCx_ofRealCLM] using norm_re_le (ofRealCLM u)

end NormedComplexification

namespace Complexification

/-- The complex linear homeomorphism `ℝ_ℂ → ℂ`, `u + i v ↦ u + i v`. -/
def toComplexCLM : Complexification ℝ →L[ℂ] ℂ where
  toFun p := ⟨re p, im p⟩
  map_add' _ _ := Complex.ext rfl rfl
  map_smul' _ _ := Complex.ext (by simp) (by simp)
  cont := Complex.equivRealProdCLM.symm.continuous.comp (continuous_re.prodMk continuous_im)

@[simp] theorem toComplexCLM_ofReal (r : ℝ) : toComplexCLM (ofReal r) = (r : ℂ) :=
  Complex.ext rfl rfl

end Complexification

end LocallyConvex.Analysis

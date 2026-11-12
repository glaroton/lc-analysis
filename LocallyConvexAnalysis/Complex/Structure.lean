/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Complex.NewlanderNirenberg
public import LocallyConvexAnalysis.ODE.FlowParamReal

/-!
# Complex structures on real locally convex spaces

A **complex structure** on a real topological vector space `E` is a continuous linear `J` with
`J² = -1`. Then `(a + i b) v = a v + b J v` makes `E` a complex topological vector space,
`WithComplexStructure J hJ` (complex locally convex if `E` is locally convex).

## Main results

* `WithComplexStructure.equivOfIntertwining`: a real isomorphism `S` with `J' S = S J` is a complex
  linear isomorphism `(E, J) ≅ (E, J')`.
* `WithComplexStructure.nonempty_equiv_of_norm_lt`: **close complex structures are conjugate**:
  on a Banach space, if `‖(J' - J) J‖ < 2` then `S = 1 - J' J` is invertible and intertwines `J` and
  `J'`, so `(E, J) ≅ (E, J')`.
* `WithComplexStructure.equivTypeOneZero`: on a real normed space, `v ↦ (v - i J v) / 2` is an
  isomorphism of complex topological vector spaces `(E, J) ≅ ker(J_ℂ - i)` onto the space of
  vectors of type `(1, 0)` of the complexification (the model of the holomorphic charts of the
  Newlander–Nirenberg theorem, `exists_holomorphic_chart`).

These are used in lc-manifolds to put a single complex model on the holomorphic atlas of the
Newlander–Nirenberg theorem: the models `ker(J(x)_ℂ - i)` at different points are isomorphic to
`(E, J(x))`, and these to each other for nearby points.
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E]

set_option linter.unusedVariables false in
/-- `E` with the complex structure `J`: `(a + i b) v = a v + b J v`. A type synonym of `E`. -/
@[nolint unusedArguments]
def WithComplexStructure (J : E →L[ℝ] E) (hJ : ∀ v, J (J v) = -v) : Type _ := E

namespace WithComplexStructure

variable {J : E →L[ℝ] E} {hJ : ∀ v, J (J v) = -v}

instance : AddCommGroup (WithComplexStructure J hJ) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (WithComplexStructure J hJ) := inferInstanceAs (Module ℝ E)
instance : TopologicalSpace (WithComplexStructure J hJ) := inferInstanceAs (TopologicalSpace E)
instance : IsTopologicalAddGroup (WithComplexStructure J hJ) :=
  inferInstanceAs (IsTopologicalAddGroup E)
instance : ContinuousSMul ℝ (WithComplexStructure J hJ) := inferInstanceAs (ContinuousSMul ℝ E)
instance [LocallyConvexSpace ℝ E] : LocallyConvexSpace ℝ (WithComplexStructure J hJ) :=
  inferInstanceAs (LocallyConvexSpace ℝ E)
instance [T2Space E] : T2Space (WithComplexStructure J hJ) := inferInstanceAs (T2Space E)

variable (J hJ) in
/-- The identity `E → (E, J)`, a real linear homeomorphism. -/
def ofE : E ≃L[ℝ] WithComplexStructure J hJ := ContinuousLinearEquiv.refl ℝ E

variable (J hJ) in
/-- The identity `(E, J) → E`. -/
def toE : WithComplexStructure J hJ ≃L[ℝ] E := ContinuousLinearEquiv.refl ℝ E

instance : SMul ℂ (WithComplexStructure J hJ) :=
  ⟨fun z v ↦ ofE J hJ (z.re • toE J hJ v + z.im • J (toE J hJ v))⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem toE_smul (z : ℂ) (v : WithComplexStructure J hJ) :
    toE J hJ (z • v) = z.re • toE J hJ v + z.im • J (toE J hJ v) := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
@[simp] theorem toE_ofE (v : E) : toE J hJ (ofE J hJ v) = v := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
@[simp] theorem ofE_toE (v : WithComplexStructure J hJ) : ofE J hJ (toE J hJ v) = v := rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem toE_injective : Injective (toE J hJ) := (toE J hJ).injective

instance : Module ℂ (WithComplexStructure J hJ) where
  one_smul v := toE_injective (by simp [toE_smul])
  mul_smul z w v := toE_injective (by
    simp only [toE_smul, map_add, map_smul, hJ, Complex.mul_re, Complex.mul_im, smul_neg]
    module)
  smul_zero z := toE_injective (by simp [toE_smul])
  smul_add z v w := toE_injective (by
    simp only [toE_smul, map_add, smul_add]
    abel)
  add_smul z w v := toE_injective (by
    simp only [toE_smul, Complex.add_re, Complex.add_im, add_smul, map_add]
    abel)
  zero_smul v := toE_injective (by simp [toE_smul])

instance : IsScalarTower ℝ ℂ (WithComplexStructure J hJ) where
  smul_assoc r z v := toE_injective (by
    simp only [toE_smul, Complex.smul_re, Complex.smul_im, smul_eq_mul, map_smul, mul_smul,
      smul_add])

instance : ContinuousSMul ℂ (WithComplexStructure J hJ) where
  continuous_smul := by
    have h : Continuous fun p : ℂ × WithComplexStructure J hJ ↦
        ofE J hJ (p.1.re • toE J hJ p.2 + p.1.im • J (toE J hJ p.2)) :=
      (ofE J hJ).continuous.comp
        (((Complex.continuous_re.comp continuous_fst).smul
          ((toE J hJ).continuous.comp continuous_snd)).add
        ((Complex.continuous_im.comp continuous_fst).smul
          (J.continuous.comp ((toE J hJ).continuous.comp continuous_snd))))
    exact h

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- `J` is the multiplication by `i`. -/
theorem toE_I_smul (v : WithComplexStructure J hJ) :
    toE J hJ (Complex.I • v) = J (toE J hJ v) := by
  simp [toE_smul]

/-! ### Isomorphisms of complex structures -/

variable {J' : E →L[ℝ] E} {hJ' : ∀ v, J' (J' v) = -v}

/-- A real isomorphism `S` with `J' S = S J` is a complex isomorphism `(E, J) ≅ (E, J')`. -/
def equivOfIntertwining (S : E ≃L[ℝ] E) (hS : ∀ v, J' (S v) = S (J v)) :
    WithComplexStructure J hJ ≃L[ℂ] WithComplexStructure J' hJ' where
  toFun v := ofE J' hJ' (S (toE J hJ v))
  invFun v := ofE J hJ (S.symm (toE J' hJ' v))
  map_add' v w := by simp only [map_add]
  map_smul' z v := toE_injective (by
    simp only [toE_ofE, toE_smul, map_add, map_smul, hS, RingHom.id_apply])
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := (ofE J' hJ').continuous.comp (S.continuous.comp (toE J hJ).continuous)
  continuous_invFun := (ofE J hJ).continuous.comp (S.symm.continuous.comp (toE J' hJ').continuous)

/-- **Close complex structures are conjugate.** On a Banach space, if `‖(J' - J) J‖ < 2`, then
`S = 1 - J' J` is invertible and `J' S = S J`, so `(E, J) ≅ (E, J')` as complex topological
vector spaces. -/
theorem nonempty_equiv_of_norm_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {J J' : F →L[ℝ] F} {hJ : ∀ v, J (J v) = -v} {hJ' : ∀ v, J' (J' v) = -v}
    (h : ‖(J' - J) * J‖ < 2) :
    Nonempty (WithComplexStructure J hJ ≃L[ℂ] WithComplexStructure J' hJ') := by
  set T : F →L[ℝ] F := (2⁻¹ : ℝ) • ((J' - J) * J)
  have hT : ‖T‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    linarith
  set S : F →L[ℝ] F := 1 - J' * J
  have hSeq : S = (2 : ℝ) • (1 - T) := by
    have hJJ : J * J = -1 := ContinuousLinearMap.ext fun v ↦ by simp [hJ]
    simp only [S, T, sub_mul, hJJ]
    module
  have hu : IsUnit S := by
    rw [hSeq, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.2 (by norm_num : (2 : ℝ) ≠ 0)).map _).mul
      (Units.oneSub T hT).isUnit
  obtain ⟨u, hu'⟩ := hu
  let e : F ≃L[ℝ] F := ContinuousLinearEquiv.ofUnit u
  have he : ∀ v, e v = S v := fun v ↦ by rw [← hu']; rfl
  refine ⟨equivOfIntertwining e fun v ↦ ?_⟩
  rw [he, he]
  change J' (v - J' (J v)) = J v - J' (J (J v))
  rw [map_sub, hJ', hJ, map_neg, sub_neg_eq_add, sub_neg_eq_add, add_comm]

end WithComplexStructure

/-! ### The space of vectors of type `(1, 0)` -/

section TypeOneZero

open Complexification NormedComplexification

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {J : F →L[ℝ] F}
  {hJ : ∀ v, J (J v) = -v}

theorem complexifyCLM_sq (hJ : ∀ v, J (J v) = -v) (w : NormedComplexification F) :
    complexifyCLM J (complexifyCLM J w) = -w := by
  rw [eq_ofRealCLM_add_I_smul w]
  simp only [map_add, map_smul, complexifyCLM_ofRealCLM, hJ, map_neg, smul_neg, neg_add]

/-- `(1 - i J_ℂ)(v + i0)/2 = v/2 - i J v/2`. -/
theorem pProj_ofRealCLM (v : F) :
    pProj (complexifyCLM J) (ofRealCLM v) =
      ofRealCLM ((2 : ℝ)⁻¹ • v) + Complex.I • ofRealCLM (-((2 : ℝ)⁻¹ • J v)) := by
  rw [pProj_apply, complexifyCLM_ofRealCLM, map_neg, map_smul, map_smul, ← Complex.coe_smul,
    ← Complex.coe_smul]
  push_cast
  module

theorem reL_pProj_ofRealCLM (v : F) :
    reL (pProj (complexifyCLM J) (ofRealCLM v)) = (2 : ℝ)⁻¹ • v := by
  rw [pProj_ofRealCLM]
  exact re_ofRealCLM_add_I_smul _ _

/-- A vector of type `(1, 0)` is `pProj` of twice its real part. -/
theorem pProj_ofRealCLM_two_reL (hJ : ∀ v, J (J v) = -v) (w : NormedComplexification F)
    (hw : qProj (complexifyCLM J) w = 0) :
    pProj (complexifyCLM J) (ofRealCLM ((2 : ℝ) • reL w)) = w := by
  set a := re (toCx w)
  set b := im (toCx w)
  have hdec : w = ofRealCLM a + Complex.I • ofRealCLM b := eq_ofRealCLM_add_I_smul w
  have hJw : complexifyCLM J w = Complex.I • w := by
    have h := apply_pProj (complexifyCLM_sq hJ) w
    have e : pProj (complexifyCLM J) w = w := by
      have := qProj_add_pProj (complexifyCLM J) w
      rwa [hw, zero_add] at this
    rwa [e] at h
  have hcomp : ofRealCLM (J a) + Complex.I • ofRealCLM (J b) =
      ofRealCLM (-b) + Complex.I • ofRealCLM a := by
    have h := hJw
    rw [hdec] at h
    simp only [map_add, map_smul, complexifyCLM_ofRealCLM, smul_add, I_smul_I_smul] at h
    rw [h, add_comm, map_neg]
  have hJa : J a = -b := by
    have := congrArg (fun z : NormedComplexification F ↦ re (toCx z)) hcomp
    simpa only [re_ofRealCLM_add_I_smul] using this
  have hre : reL w = a := rfl
  rw [pProj_ofRealCLM, hre, map_smul J, smul_smul, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul, one_smul, hJa, neg_neg]
  exact hdec.symm

namespace WithComplexStructure

/-- `v ↦ (v - i J v) / 2`, from `(E, J)` to `ker(J_ℂ - i)`. -/
def toTypeOneZero : WithComplexStructure J hJ →L[ℂ] typeOneZero (complexifyCLM J) where
  toFun v := ⟨pProj (complexifyCLM J) (ofRealCLM (toE J hJ v)),
    LinearMap.mem_ker.2 (qProj_pProj (complexifyCLM_sq hJ) _)⟩
  map_add' v w := Subtype.ext (by simp only [map_add, Submodule.coe_add])
  map_smul' z v := by
    refine Subtype.ext ?_
    have h : pProj (complexifyCLM J) (ofRealCLM (J (toE J hJ v))) =
        Complex.I • pProj (complexifyCLM J) (ofRealCLM (toE J hJ v)) := by
      rw [← complexifyCLM_ofRealCLM, ← apply_pProj (complexifyCLM_sq hJ)]
      simp only [pProj_apply, map_smul, map_sub]
    have hr : ∀ (r : ℝ) (x : F), ofRealCLM (r • x) = (r : ℂ) • ofRealCLM x := fun r x ↦ by
      rw [map_smul, Complex.coe_smul]
    change pProj (complexifyCLM J) (ofRealCLM (z.re • toE J hJ v + z.im • J (toE J hJ v))) =
      z • pProj (complexifyCLM J) (ofRealCLM (toE J hJ v))
    rw [map_add, hr, hr, map_add, map_smul, map_smul, h, smul_smul, ← add_smul,
      Complex.re_add_im]
  cont := ((pProj (complexifyCLM J)).continuous.comp
    (ofRealCLM.continuous.comp (toE J hJ).continuous)).subtype_mk _

theorem val_toTypeOneZero (v : WithComplexStructure J hJ) :
    (toTypeOneZero v : NormedComplexification F) =
      pProj (complexifyCLM J) (ofRealCLM (toE J hJ v)) := rfl

/-- `w ↦ 2 Re w`, the inverse map. -/
def ofTypeOneZero (w : typeOneZero (complexifyCLM J)) : WithComplexStructure J hJ :=
  ofE J hJ ((2 : ℝ) • reL (w : NormedComplexification F))

theorem continuous_ofTypeOneZero : Continuous (ofTypeOneZero (J := J) (hJ := hJ)) :=
  (ofE J hJ).continuous.comp ((reL.continuous.comp continuous_subtype_val).const_smul _)

theorem toTypeOneZero_ofTypeOneZero (w : typeOneZero (complexifyCLM J)) :
    toTypeOneZero (ofTypeOneZero (hJ := hJ) w) = w :=
  Subtype.ext (pProj_ofRealCLM_two_reL hJ _ w.2)

theorem injective_toTypeOneZero : Injective (toTypeOneZero (J := J) (hJ := hJ)) := fun v w h ↦ by
  have h' := congrArg (fun w : typeOneZero (complexifyCLM J) ↦
    reL (w : NormedComplexification F)) h
  simp only [val_toTypeOneZero, reL_pProj_ofRealCLM] at h'
  exact toE_injective (smul_right_injective F (by norm_num : (2 : ℝ)⁻¹ ≠ 0) h')

/-- `v ↦ (v - i J v) / 2` as a linear equivalence. -/
def linearEquivTypeOneZero : WithComplexStructure J hJ ≃ₗ[ℂ] typeOneZero (complexifyCLM J) :=
  LinearEquiv.ofBijective toTypeOneZero.toLinearMap
    ⟨injective_toTypeOneZero, fun w ↦ ⟨ofTypeOneZero w, toTypeOneZero_ofTypeOneZero w⟩⟩

theorem linearEquivTypeOneZero_symm_apply (w : typeOneZero (complexifyCLM J)) :
    (linearEquivTypeOneZero (hJ := hJ)).symm w = ofTypeOneZero w :=
  (LinearEquiv.symm_apply_eq _).2 (toTypeOneZero_ofTypeOneZero w).symm

/-- **`(E, J) ≅ ker(J_ℂ - i)`** as complex topological vector spaces, `v ↦ (v - i J v) / 2`. -/
def equivTypeOneZero : WithComplexStructure J hJ ≃L[ℂ] typeOneZero (complexifyCLM J) where
  toLinearEquiv := linearEquivTypeOneZero
  continuous_toFun := toTypeOneZero.continuous
  continuous_invFun := continuous_ofTypeOneZero.congr fun w ↦
    (linearEquivTypeOneZero_symm_apply w).symm

end WithComplexStructure

end TypeOneZero

end LocallyConvex.Analysis

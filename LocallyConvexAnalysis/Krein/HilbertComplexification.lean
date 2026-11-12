/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The complexification of a real (or complex) inner product space

For an inner product space `E` over `𝕜 = ℝ` or `ℂ`, regarded as a real inner product space with
`⟪x, y⟫_ℝ = re ⟪x, y⟫_𝕜`, the **complexification** `E_ℂ = E × E` (with `(x, y)` standing for
`x + i y`) is a complex inner product space:
`(a + i b) (x, y) = (a x - b y, a y + b x)` and
`⟪(x, y), (u, v)⟫ = re ⟪x, u⟫ + re ⟪y, v⟫ + i (re ⟪x, v⟫ - re ⟪y, u⟫)`,
with `‖(x, y)‖² = ‖x‖² + ‖y‖²`; it is complete when `E` is. Every continuous `𝕜`-linear operator
`T` of `E` extends to the `ℂ`-linear operator `T_ℂ (x, y) = (T x, T y)`, and the conjugation
`(x, y) ↦ (x, -y)` is a conjugate-linear isometric involution commuting with every `T_ℂ`;
`C A C` is `ℂ`-linear for every `ℂ`-linear `A`.

This is the device that brings the continuous functional calculus of the complex C⋆-algebra
`E_ℂ →L[ℂ] E_ℂ` to bear on real Hilbert spaces
(`LocallyConvexAnalysis/Krein/OrthoComplemented.lean`).
Mathlib has no complexification of inner product spaces in this version; the construction is
standard and only what is needed is developed. Nothing is claimed to be new.

## Main definitions

* `HilbertComplexification 𝕜 E`: the complexification `E_ℂ = E × E`, with real and imaginary
  parts `HilbertComplexification.re`, `HilbertComplexification.im`.
* `HilbertComplexification.core`: the complex inner product
  `⟪(x, y), (u, v)⟫ = re ⟪x, u⟫ + re ⟪y, v⟫ + i (re ⟪x, v⟫ - re ⟪y, u⟫)`, from which `E_ℂ` gets
  its normed space and inner product space structures; it is complete when `E` is.
* `HilbertComplexification.cx T`: the complexification `T_ℂ (x, y) = (T x, T y)` of a continuous
  `𝕜`-linear operator `T`.
* `HilbertComplexification.conjugate`: the conjugation `(x, y) ↦ (x, -y)`.
* `HilbertComplexification.conjOp A`: the operator `C A C`, `C` the conjugation, which is
  `ℂ`-linear for every `ℂ`-linear `A`.

## Main results

* `HilbertComplexification.norm_sq`: `‖(x, y)‖² = ‖x‖² + ‖y‖²`.
* `HilbertComplexification.cx_mul`, `HilbertComplexification.inner_cx`: `T ↦ T_ℂ` is
  multiplicative, and `T_ℂ` and `T'_ℂ` are adjoint to each other when `T` and `T'` are.
* `HilbertComplexification.conjugate_smul`, `HilbertComplexification.norm_conjugate`,
  `HilbertComplexification.inner_conjugate`: the conjugation is conjugate-linear and isometric,
  and `⟪C z, C w⟫ = conj ⟪z, w⟫`.
* `HilbertComplexification.conjugate_cx`: the conjugation commutes with every `T_ℂ`.
-/

@[expose] public section

open RCLike
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace LocallyConvex.Analysis

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem re_inner_ofReal_smul_left (r : ℝ) (x y : E) :
    re ⟪(r : 𝕜) • x, y⟫_𝕜 = r * re ⟪x, y⟫_𝕜 := by
  rw [inner_smul_left, conj_ofReal, re_ofReal_mul]

theorem re_inner_ofReal_smul_right (r : ℝ) (x y : E) :
    re ⟪x, (r : 𝕜) • y⟫_𝕜 = r * re ⟪x, y⟫_𝕜 := by
  rw [inner_smul_right, re_ofReal_mul]

/-- The **complexification** `E × E` of the inner product space `E` (over `ℝ` or `ℂ`, regarded as
a real space); `(x, y)` stands for `x + i y`. -/
@[nolint unusedArguments]
def HilbertComplexification (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] : Type _ :=
  E × E

namespace HilbertComplexification

instance : AddCommGroup (HilbertComplexification 𝕜 E) := inferInstanceAs (AddCommGroup (E × E))

/-- The vector `x + i y`. -/
def mk (x y : E) : HilbertComplexification 𝕜 E := (x, y)

/-- The real part. -/
def re (z : HilbertComplexification 𝕜 E) : E := Prod.fst (α := E) (β := E) z

/-- The imaginary part. -/
def im (z : HilbertComplexification 𝕜 E) : E := Prod.snd (α := E) (β := E) z

@[simp] theorem re_mk (x y : E) : (mk x y : HilbertComplexification 𝕜 E).re = x := rfl
@[simp] theorem im_mk (x y : E) : (mk x y : HilbertComplexification 𝕜 E).im = y := rfl
@[simp] theorem mk_re_im (z : HilbertComplexification 𝕜 E) : mk z.re z.im = z := rfl

@[ext] theorem ext {z w : HilbertComplexification 𝕜 E} (h1 : z.re = w.re) (h2 : z.im = w.im) :
    z = w :=
  Prod.ext h1 h2

@[simp] theorem re_add (z w : HilbertComplexification 𝕜 E) : (z + w).re = z.re + w.re := rfl
@[simp] theorem im_add (z w : HilbertComplexification 𝕜 E) : (z + w).im = z.im + w.im := rfl
@[simp] theorem re_sub (z w : HilbertComplexification 𝕜 E) : (z - w).re = z.re - w.re := rfl
@[simp] theorem im_sub (z w : HilbertComplexification 𝕜 E) : (z - w).im = z.im - w.im := rfl
@[simp] theorem re_neg (z : HilbertComplexification 𝕜 E) : (-z).re = -z.re := rfl
@[simp] theorem im_neg (z : HilbertComplexification 𝕜 E) : (-z).im = -z.im := rfl
@[simp] theorem re_zero : (0 : HilbertComplexification 𝕜 E).re = 0 := rfl
@[simp] theorem im_zero : (0 : HilbertComplexification 𝕜 E).im = 0 := rfl

instance : SMul ℂ (HilbertComplexification 𝕜 E) where
  smul c z := mk ((c.re : 𝕜) • z.re - (c.im : 𝕜) • z.im) ((c.re : 𝕜) • z.im + (c.im : 𝕜) • z.re)

@[simp] theorem re_smul (c : ℂ) (z : HilbertComplexification 𝕜 E) :
    (c • z).re = (c.re : 𝕜) • z.re - (c.im : 𝕜) • z.im := rfl
@[simp] theorem im_smul (c : ℂ) (z : HilbertComplexification 𝕜 E) :
    (c • z).im = (c.re : 𝕜) • z.im + (c.im : 𝕜) • z.re := rfl

instance : Module ℂ (HilbertComplexification 𝕜 E) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by
    ext <;> simp only [re_smul, im_smul, Complex.mul_re, Complex.mul_im] <;> push_cast <;> module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [re_smul, im_smul, re_add, im_add] <;> module
  add_smul c d z := by
    ext <;> simp only [re_smul, im_smul, re_add, im_add, Complex.add_re, Complex.add_im] <;>
      push_cast <;> module
  zero_smul z := by ext <;> simp

/-- The complex inner product of the complexification. -/
@[instance_reducible]
def core : InnerProductSpace.Core ℂ (HilbertComplexification 𝕜 E) where
  inner z w := ⟨RCLike.re ⟪z.re, w.re⟫_𝕜 + RCLike.re ⟪z.im, w.im⟫_𝕜,
    RCLike.re ⟪z.re, w.im⟫_𝕜 - RCLike.re ⟪z.im, w.re⟫_𝕜⟩
  conj_inner_symm z w := by
    apply Complex.ext
    · simp only [Complex.conj_re]
      rw [inner_re_symm (𝕜 := 𝕜) w.re, inner_re_symm (𝕜 := 𝕜) w.im]
    · simp only [Complex.conj_im]
      rw [inner_re_symm (𝕜 := 𝕜) w.re, inner_re_symm (𝕜 := 𝕜) w.im]
      ring
  re_inner_nonneg z := by
    change 0 ≤ RCLike.re ⟪z.re, z.re⟫_𝕜 + RCLike.re ⟪z.im, z.im⟫_𝕜
    exact add_nonneg inner_self_nonneg inner_self_nonneg
  add_left z w v := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left z w c := by
    apply Complex.ext
    · simp only [re_smul, im_smul, inner_sub_left, inner_add_left, map_sub, map_add,
        re_inner_ofReal_smul_left, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp only [re_smul, im_smul, inner_sub_left, inner_add_left, map_sub, map_add,
        re_inner_ofReal_smul_left, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
  definite z hz := by
    have h0 : RCLike.re ⟪z.re, z.re⟫_𝕜 + RCLike.re ⟪z.im, z.im⟫_𝕜 = 0 :=
      congrArg Complex.re hz
    have h1 := inner_self_nonneg (𝕜 := 𝕜) (x := z.re)
    have h2 := inner_self_nonneg (𝕜 := 𝕜) (x := z.im)
    have hr : z.re = 0 := by
      have : ‖z.re‖ ^ 2 = 0 := by rw [@norm_sq_eq_re_inner 𝕜]; linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    have hi : z.im = 0 := by
      have : ‖z.im‖ ^ 2 = 0 := by rw [@norm_sq_eq_re_inner 𝕜]; linarith
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    ext
    · exact hr
    · exact hi

instance : NormedAddCommGroup (HilbertComplexification 𝕜 E) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ core

instance : InnerProductSpace ℂ (HilbertComplexification 𝕜 E) :=
  InnerProductSpace.ofCore (core (𝕜 := 𝕜) (E := E)).toCore

theorem inner_re (z w : HilbertComplexification 𝕜 E) :
    (⟪z, w⟫_ℂ).re = RCLike.re ⟪z.re, w.re⟫_𝕜 + RCLike.re ⟪z.im, w.im⟫_𝕜 := rfl

theorem inner_im (z w : HilbertComplexification 𝕜 E) :
    (⟪z, w⟫_ℂ).im = RCLike.re ⟪z.re, w.im⟫_𝕜 - RCLike.re ⟪z.im, w.re⟫_𝕜 := rfl

theorem norm_sq (z : HilbertComplexification 𝕜 E) : ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex, inner_re, ← norm_sq_eq_re_inner,
    ← norm_sq_eq_re_inner]

theorem norm_eq (z : HilbertComplexification 𝕜 E) : ‖z‖ = √(‖z.re‖ ^ 2 + ‖z.im‖ ^ 2) := by
  rw [← norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem norm_re_le (z : HilbertComplexification 𝕜 E) : ‖z.re‖ ≤ ‖z‖ := by
  rw [norm_eq]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.im‖])

theorem norm_im_le (z : HilbertComplexification 𝕜 E) : ‖z.im‖ ≤ ‖z‖ := by
  rw [norm_eq]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.re‖])

theorem norm_le_add (z : HilbertComplexification 𝕜 E) : ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ := by
  rw [norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg z.re, norm_nonneg z.im]

/-- The real vector `x + i 0`. -/
def real (x : E) : HilbertComplexification 𝕜 E := mk x 0

@[simp] theorem re_real (x : E) : (real x : HilbertComplexification 𝕜 E).re = x := rfl
@[simp] theorem im_real (x : E) : (real x : HilbertComplexification 𝕜 E).im = 0 := rfl

theorem real_add (x y : E) : (real (x + y) : HilbertComplexification 𝕜 E) = real x + real y := by
  ext <;> simp

@[simp] theorem real_zero : (real 0 : HilbertComplexification 𝕜 E) = 0 := by ext <;> simp

theorem real_ofReal_smul (r : ℝ) (x : E) :
    (real ((r : 𝕜) • x) : HilbertComplexification 𝕜 E) = (r : ℂ) • real x := by
  ext <;> simp only [re_real, im_real, re_smul, im_smul, Complex.ofReal_re, Complex.ofReal_im,
    RCLike.ofReal_zero, zero_smul, smul_zero, sub_zero, add_zero]

@[simp] theorem norm_mk_zero (x : E) : ‖(mk x 0 : HilbertComplexification 𝕜 E)‖ = ‖x‖ := by
  rw [norm_eq]; simp

@[simp] theorem inner_mk_zero (x y : E) :
    ⟪(mk x 0 : HilbertComplexification 𝕜 E), mk y 0⟫_ℂ = (RCLike.re ⟪x, y⟫_𝕜 : ℂ) := by
  apply Complex.ext <;> simp [inner_re, inner_im]

@[simp] theorem norm_real (x : E) : ‖(real x : HilbertComplexification 𝕜 E)‖ = ‖x‖ := norm_mk_zero x

@[simp] theorem inner_real (x y : E) :
    ⟪(real x : HilbertComplexification 𝕜 E), real y⟫_ℂ = (RCLike.re ⟪x, y⟫_𝕜 : ℂ) :=
  inner_mk_zero x y

/-- The real part as an additive map. -/
def reHom : HilbertComplexification 𝕜 E →+ E where
  toFun := re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The imaginary part as an additive map. -/
def imHom : HilbertComplexification 𝕜 E →+ E where
  toFun := im
  map_zero' := rfl
  map_add' _ _ := rfl

instance [CompleteSpace E] : CompleteSpace (HilbertComplexification 𝕜 E) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hre : LipschitzWith 1 (reHom (𝕜 := 𝕜) (E := E)) := by
    have := AddMonoidHomClass.lipschitz_of_bound (reHom (𝕜 := 𝕜) (E := E)) 1 fun z ↦
      (one_mul ‖z‖).symm ▸ norm_re_le z
    simpa using this
  have him : LipschitzWith 1 (imHom (𝕜 := 𝕜) (E := E)) := by
    have := AddMonoidHomClass.lipschitz_of_bound (imHom (𝕜 := 𝕜) (E := E)) 1 fun z ↦
      (one_mul ‖z‖).symm ▸ norm_im_le z
    simpa using this
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete (hre.uniformContinuous.comp_cauchySeq hu)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (him.uniformContinuous.comp_cauchySeq hu)
  refine ⟨mk x y, tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 hx
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 hy
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (norm_le_add _).trans_eq ?_)
    (by simpa using h1.add h2)
  rfl

/-! ### Complexified operators and the conjugation -/

theorem norm_le_of_sq {z w : HilbertComplexification 𝕜 E} {C : ℝ} (hC : 0 ≤ C)
    (h1 : ‖w.re‖ ≤ C * ‖z.re‖) (h2 : ‖w.im‖ ≤ C * ‖z.im‖) : ‖w‖ ≤ C * ‖z‖ := by
  rw [norm_eq, norm_eq, ← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have a1 : ‖w.re‖ ^ 2 ≤ (C * ‖z.re‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have a2 : ‖w.im‖ ^ 2 ≤ (C * ‖z.im‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith

/-- The complexification `T_ℂ (x, y) = (T x, T y)` of a continuous `𝕜`-linear operator. -/
def cx (T : E →L[𝕜] E) : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E :=
  LinearMap.mkContinuous
    { toFun := fun z ↦ mk (T z.re) (T z.im)
      map_add' := fun z w ↦ by ext <;> simp
      map_smul' := fun c z ↦ by ext <;> simp [map_sub, map_add, map_smul] }
    ‖T‖ fun z ↦ norm_le_of_sq (norm_nonneg _) (T.le_opNorm _) (T.le_opNorm _)

@[simp] theorem cx_re (T : E →L[𝕜] E) (z : HilbertComplexification 𝕜 E) :
    (cx T z).re = T z.re := rfl
@[simp] theorem cx_im (T : E →L[𝕜] E) (z : HilbertComplexification 𝕜 E) :
    (cx T z).im = T z.im := rfl

@[simp] theorem cx_one : cx (1 : E →L[𝕜] E) = 1 := by ext z <;> rfl

theorem cx_mul (S T : E →L[𝕜] E) : cx (S * T) = cx S * cx T := by ext z <;> rfl

theorem inner_cx (T T' : E →L[𝕜] E) (hT : ∀ x y, ⟪T x, y⟫_𝕜 = ⟪x, T' y⟫_𝕜)
    (z w : HilbertComplexification 𝕜 E) : ⟪cx T z, w⟫_ℂ = ⟪z, cx T' w⟫_ℂ := by
  apply Complex.ext <;> simp only [inner_re, inner_im, cx_re, cx_im, hT]

/-- The conjugation `(x, y) ↦ (x, -y)`. -/
def conjugate (z : HilbertComplexification 𝕜 E) : HilbertComplexification 𝕜 E := mk z.re (-z.im)

@[simp] theorem conjugate_re (z : HilbertComplexification 𝕜 E) : (conjugate z).re = z.re := rfl
@[simp] theorem conjugate_im (z : HilbertComplexification 𝕜 E) : (conjugate z).im = -z.im := rfl
@[simp] theorem conjugate_conjugate (z : HilbertComplexification 𝕜 E) :
    conjugate (conjugate z) = z := by
  ext <;> simp

@[simp] theorem conjugate_zero : conjugate (0 : HilbertComplexification 𝕜 E) = 0 := by ext <;> simp

theorem conjugate_add (z w : HilbertComplexification 𝕜 E) :
    conjugate (z + w) = conjugate z + conjugate w := by
  ext <;> simp [add_comm]

theorem conjugate_smul (c : ℂ) (z : HilbertComplexification 𝕜 E) :
    conjugate (c • z) = (starRingEnd ℂ c) • conjugate z := by
  ext <;> simp [smul_neg]
  abel

theorem norm_conjugate (z : HilbertComplexification 𝕜 E) : ‖conjugate z‖ = ‖z‖ := by
  rw [norm_eq, norm_eq]; simp

theorem inner_conjugate (z w : HilbertComplexification 𝕜 E) :
    ⟪conjugate z, conjugate w⟫_ℂ = starRingEnd ℂ ⟪z, w⟫_ℂ := by
  apply Complex.ext <;> simp only [inner_re, inner_im, conjugate_re, conjugate_im, Complex.conj_re,
    Complex.conj_im, inner_neg_left, inner_neg_right, map_neg, neg_neg]
  ring

theorem conjugate_cx (T : E →L[𝕜] E) (z : HilbertComplexification 𝕜 E) :
    conjugate (cx T z) = cx T (conjugate z) := by
  ext <;> simp

@[simp] theorem conjugate_real (x : E) :
    conjugate (real x : HilbertComplexification 𝕜 E) = real x := by
  ext <;> simp

@[simp] theorem cx_real (T : E →L[𝕜] E) (x : E) :
    cx T (real x : HilbertComplexification 𝕜 E) = real (T x) := by
  ext <;> simp

/-- `C A C` for a `ℂ`-linear `A`, `C` the conjugation: again `ℂ`-linear. -/
def conjOp (A : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E) :
    HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E :=
  LinearMap.mkContinuous
    { toFun := fun z ↦ conjugate (A (conjugate z))
      map_add' := fun z w ↦ by simp only [conjugate_add, map_add]
      map_smul' := fun c z ↦ by
        simp only [conjugate_smul, map_smul, RingHom.id_apply]
        simp }
    ‖A‖ fun z ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, norm_conjugate]
      exact (A.le_opNorm _).trans_eq (by rw [norm_conjugate])

@[simp] theorem conjOp_apply (A : HilbertComplexification 𝕜 E →L[ℂ] HilbertComplexification 𝕜 E)
    (z : HilbertComplexification 𝕜 E) : conjOp A z = conjugate (A (conjugate z)) := rfl

end HilbertComplexification

end LocallyConvex.Analysis

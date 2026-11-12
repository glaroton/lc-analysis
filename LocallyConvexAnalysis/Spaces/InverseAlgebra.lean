/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Identity
public import LocallyConvexAnalysis.Calculus.Rules

/-! # Inversion in continuous inverse algebras

A unital locally convex algebra is a *continuous inverse algebra* if its group of units is open
and inversion is continuous ([GN26, Definition 1.3.7]); complete normed algebras are
examples. We show that inversion is smooth, complex analytic in the complex case, and real
analytic in the real case ([GN26, Corollary 1.3.8, Example 2.1.15, Proposition 2.2.13]).

## Main results

* `ContinuousInverseAlgebra`, `NormedRing.continuousInverseAlgebra`.
* `hasDirDerivAt_inverse`, `smoothMBOn_inverse`: `dι(x, h) = -x⁻¹ h x⁻¹`, and `ι` is smooth.
* `complexAnalyticOn_inverse`: inversion in a complex continuous inverse algebra is complex
  analytic.
* The ring structure of the complexification `A_ℂ` of a real algebra (GN Definition 2.2.15),
  `isOpen_units_of_mem_nhds_one`, `continuousOn_inverse_of_continuousAt_one` (GN Lemma 2.2.14),
  `Complexification.continuousInverseAlgebra` (GN Lemma 2.2.17).
* `realAnalyticOn_inverse`: **inversion in a real continuous inverse algebra is real analytic**
  (GN Proposition 2.2.13).

## Implementation notes

* Inversion is `Ring.inverse` (`x⁻¹ʳ`), defined on the whole algebra with junk value `0`.
* Real and complex algebra structures are given by module structures with `IsScalarTower` and
  `SMulCommClass` instances rather than `Algebra`: `Algebra ℂ A` would induce a second real
  module structure on `A_ℂ` (`Module.complexToReal`), different from the product structure.
* No completeness is assumed anywhere.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology Ring

noncomputable section

namespace LocallyConvex.Analysis

universe u

/-- A unital topological ring is a *continuous inverse algebra* ([GN26, Definition 1.3.7]) if its
group of units is open and inversion is continuous on it. Inversion is `Ring.inverse` (`x⁻¹ʳ`, with
junk value `0` off the units). -/
class ContinuousInverseAlgebra (A : Type*) [Ring A] [TopologicalSpace A] : Prop where
  isOpen_units : IsOpen {a : A | IsUnit a}
  continuousOn_inverse : ContinuousOn (Ring.inverse : A → A) {a : A | IsUnit a}

/-- **Complete normed rings are continuous inverse algebras** ([GN26, Exercise 1.3.9]). -/
instance (priority := 100) NormedRing.continuousInverseAlgebra (R : Type*) [NormedRing R]
    [CompleteSpace R] : ContinuousInverseAlgebra R where
  isOpen_units := Units.isOpen
  continuousOn_inverse := fun _ hx ↦
    (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt

/-! ### Smoothness of inversion -/

section Smooth

variable {A : Type u} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [IsTopologicalRing A]
  [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A] [ContinuousInverseAlgebra A]

omit [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousInverseAlgebra A] in
/-- `ι(a) - ι(x) = -t ι(a) h ι(x)` for units `x` and `a = x + t h`. -/
theorem inverse_add_smul_sub {x h : A} (hx : IsUnit x) {t : ℝ} (ha : IsUnit (x + t • h)) :
    (x + t • h)⁻¹ʳ - x⁻¹ʳ = -(t • ((x + t • h)⁻¹ʳ * h * x⁻¹ʳ)) := by
  have e : (x + t • h)⁻¹ʳ - x⁻¹ʳ = (x + t • h)⁻¹ʳ * (x - (x + t • h)) * x⁻¹ʳ := by
    rw [mul_sub, sub_mul, Ring.inverse_mul_cancel _ ha, one_mul,
      Ring.mul_inverse_cancel_right _ _ hx]
  rw [e, sub_add_cancel_left, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]

omit [LocallyConvexSpace ℝ A] [T2Space A] in
/-- **The derivative of inversion** ([GN26, Corollary 1.3.8]):
`dι(x, h) = -x⁻¹ h x⁻¹`. -/
theorem hasDirDerivAt_inverse {x : A} (hx : IsUnit x) (h : A) :
    HasDirDerivAt (Ring.inverse : A → A) x h (-(x⁻¹ʳ * h * x⁻¹ʳ)) := by
  have hU : {a : A | IsUnit a} ∈ 𝓝 x := ContinuousInverseAlgebra.isOpen_units.mem_nhds hx
  have hι : ContinuousAt (Ring.inverse : A → A) x :=
    ContinuousInverseAlgebra.continuousOn_inverse.continuousAt hU
  have hl : Continuous fun t : ℝ ↦ x + t • h := continuous_const.add (continuous_id.smul
    continuous_const)
  have hev : ∀ᶠ t : ℝ in 𝓝 0, IsUnit (x + t • h) := by
    have : (fun t : ℝ ↦ x + t • h) ⁻¹' {a : A | IsUnit a} ∈ 𝓝 (0 : ℝ) :=
      hl.continuousAt.preimage_mem_nhds (by rw [zero_smul, add_zero]; exact hU)
    exact this
  have hlim : Tendsto (fun t : ℝ ↦ -((x + t • h)⁻¹ʳ * h * x⁻¹ʳ)) (𝓝 0)
      (𝓝 (-(x⁻¹ʳ * h * x⁻¹ʳ))) := by
    have h1 : Tendsto (fun t : ℝ ↦ (x + t • h)⁻¹ʳ) (𝓝 0) (𝓝 x⁻¹ʳ) := by
      have h0 : Tendsto (fun t : ℝ ↦ x + t • h) (𝓝 0) (𝓝 x) := by
        simpa using hl.tendsto 0
      exact hι.tendsto.comp h0
    exact ((h1.mul_const h).mul_const _).neg
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
  rw [inverse_add_smul_sub hx ht, smul_neg, smul_smul, inv_mul_cancel₀ ht0, one_smul]

omit [LocallyConvexSpace ℝ A] in
theorem dMB_inverse {x : A} (hx : IsUnit x) (h : A) :
    dMB (Ring.inverse : A → A) (x, h) = -(x⁻¹ʳ * h * x⁻¹ʳ) :=
  (hasDirDerivAt_inverse hx h).dMB_eq

/-- **Inversion in a continuous inverse algebra is smooth** ([GN26, Corollary 1.3.8]):
by induction, `dι(x, h) = -ι(x) h ι(x)` is `Cᵏ` when `ι` is. -/
theorem contDiffMBOn_inverse : ∀ k, ContDiffMBOn k (Ring.inverse : A → A) {a : A | IsUnit a} := by
  intro k
  induction k with
  | zero => exact ContinuousInverseAlgebra.continuousOn_inverse
  | succ k ih =>
    have hS : IsOpen {a : A | IsUnit a} := ContinuousInverseAlgebra.isOpen_units
    have hSS : IsOpen ({a : A | IsUnit a} ×ˢ (univ : Set A)) := hS.prod isOpen_univ
    refine ⟨ContinuousInverseAlgebra.continuousOn_inverse,
      fun x hx h ↦ by rw [dMB_inverse hx h]; exact hasDirDerivAt_inverse hx h, ?_⟩
    -- `p ↦ ι(p.1)` and `p ↦ p.2` on `S × A`
    have hι₁ : ContDiffMBOn k (fun p : A × A ↦ p.1⁻¹ʳ) ({a : A | IsUnit a} ×ˢ univ) := by
      have := ContDiffMBOn.comp_clm (ContinuousLinearMap.fst ℝ A A) hS ih
      rw [Set.prod_univ]
      exact this
    have hsnd : ContDiffMBOn k (fun p : A × A ↦ p.2) ({a : A | IsUnit a} ×ˢ univ) :=
      (ContinuousLinearMap.snd ℝ A A).contDiffMBOn k _
    have hmul : Continuous fun p : A × A ↦ LinearMap.mul ℝ A p.1 p.2 := by
      simp only [LinearMap.mul_apply']; exact continuous_fst.mul continuous_snd
    have hnmul : Continuous fun p : A × A ↦ (-LinearMap.mul ℝ A) p.1 p.2 := by
      simp only [LinearMap.neg_apply, LinearMap.mul_apply']
      exact (continuous_fst.mul continuous_snd).neg
    have h1 := ContDiffMBOn.bilin (LinearMap.mul ℝ A) hmul hSS hι₁ hsnd
    have h2 := ContDiffMBOn.bilin (-LinearMap.mul ℝ A) hnmul hSS h1 hι₁
    refine ContDiffMBOn.congr_of_isOpen hSS (fun p hp ↦ ?_) h2
    simp only [LinearMap.neg_apply, LinearMap.mul_apply']
    exact (dMB_inverse hp.1 p.2).symm

/-- Inversion is smooth on the group of units. -/
theorem smoothMBOn_inverse : SmoothMBOn (Ring.inverse : A → A) {a : A | IsUnit a} :=
  contDiffMBOn_inverse

end Smooth

/-! ### Complex continuous inverse algebras -/

section Complex

variable {A : Type u} [Ring A] [Module ℝ A] [Module ℂ A] [IsScalarTower ℝ ℂ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℂ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousInverseAlgebra A]

attribute [local instance] continuousSMul_real_of_complex

/-- **Inversion in a complex continuous inverse algebra is complex analytic**
([GN26, Example 2.1.15]): it is smooth with complex linear differential `h ↦ -x⁻¹ h x⁻¹`. -/
theorem complexAnalyticOn_inverse :
    ComplexAnalyticOn (Ring.inverse : A → A) {a : A | IsUnit a} := by
  have hS : IsOpen {a : A | IsUnit a} := ContinuousInverseAlgebra.isOpen_units
  refine (complexAnalyticOn_iff_holomorphicOn hS).2 ⟨smoothMBOn_inverse, fun x hx c h ↦ ?_⟩
  rw [dMB_inverse hx, dMB_inverse hx, mul_smul_comm, smul_mul_assoc, smul_neg]

end Complex

/-! ### The complexification of a real algebra -/

namespace Complexification

section Ring

variable {A : Type u} [Ring A]

/-- `(x₁ + i y₁)(x₂ + i y₂) = (x₁ x₂ - y₁ y₂) + i (x₁ y₂ + y₁ x₂)`
([GN26, Definition 2.2.15]). -/
instance : Mul (Complexification A) :=
  ⟨fun p q ↦ mk (re p * re q - im p * im q) (re p * im q + im p * re q)⟩

instance : One (Complexification A) := ⟨mk 1 0⟩

@[simp] theorem re_mul (p q : Complexification A) : re (p * q) = re p * re q - im p * im q := rfl
@[simp] theorem im_mul (p q : Complexification A) : im (p * q) = re p * im q + im p * re q := rfl
@[simp] theorem re_one : re (1 : Complexification A) = 1 := rfl
@[simp] theorem im_one : im (1 : Complexification A) = 0 := rfl

instance : Ring (Complexification A) where
  __ := (inferInstance : AddCommGroup (Complexification A))
  mul_assoc p q r := by ext <;> simp only [re_mul, im_mul] <;> noncomm_ring
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  left_distrib p q r := by ext <;> simp only [re_mul, im_mul, re_add, im_add] <;> noncomm_ring
  right_distrib p q r := by ext <;> simp only [re_mul, im_mul, re_add, im_add] <;> noncomm_ring
  zero_mul p := by ext <;> simp
  mul_zero p := by ext <;> simp

/-- `E ↪ E_ℂ` is multiplicative. -/
theorem ofRealₗ_mul [Module ℝ A] (a b : A) : ofRealₗ (a * b) = ofRealₗ a * ofRealₗ b := by
  ext <;> simp

theorem ofRealₗ_one [Module ℝ A] : ofRealₗ (1 : A) = 1 := rfl

variable [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]

instance : IsScalarTower ℝ (Complexification A) (Complexification A) :=
  ⟨fun r p q ↦ by ext <;> simp [smul_mul_assoc, smul_sub, smul_add]⟩

instance : SMulCommClass ℝ (Complexification A) (Complexification A) :=
  ⟨fun r p q ↦ by ext <;> simp [mul_smul_comm, smul_sub, smul_add]⟩

instance : IsScalarTower ℂ (Complexification A) (Complexification A) :=
  ⟨fun c p q ↦ by
    ext <;> simp [smul_mul_assoc, smul_sub, smul_add, sub_mul, add_mul] <;> abel⟩

instance : SMulCommClass ℂ (Complexification A) (Complexification A) :=
  ⟨fun c p q ↦ by
    ext <;> simp [mul_smul_comm, smul_sub, smul_add, mul_sub, mul_add] <;> abel⟩

end Ring

section Topology

variable {A : Type u} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

instance : ContinuousMul (Complexification A) := ⟨by
  refine continuous_mk ?_ ?_
  · exact ((continuous_re.comp continuous_fst).mul (continuous_re.comp continuous_snd)).sub
      ((continuous_im.comp continuous_fst).mul (continuous_im.comp continuous_snd))
  · exact ((continuous_re.comp continuous_fst).mul (continuous_im.comp continuous_snd)).add
      ((continuous_im.comp continuous_fst).mul (continuous_re.comp continuous_snd))⟩

instance : IsTopologicalRing (Complexification A) where

end Topology

end Complexification

/-! ### Continuous inverse algebras: units near `1` -/

section Units

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- A two-sided inverse is the ring inverse. -/
theorem Ring.inverse_eq_of_mul_eq_one {a b : R} (h₁ : a * b = 1) (h₂ : b * a = 1) :
    Ring.inverse a = b := by
  have ha : IsUnit a := ⟨⟨a, b, h₁, h₂⟩, rfl⟩
  calc Ring.inverse a = Ring.inverse a * (a * b) := by rw [h₁, mul_one]
    _ = b := by rw [← mul_assoc, Ring.inverse_mul_cancel _ ha, one_mul]

/-- **Units form an open set as soon as they form a neighbourhood of `1`**
([GN26, Lemma 2.2.14] (a)). -/
theorem isOpen_units_of_mem_nhds_one (h : {a : R | IsUnit a} ∈ 𝓝 (1 : R)) :
    IsOpen {a : R | IsUnit a} := by
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have hc : Continuous fun z : R ↦ Ring.inverse x * z := continuous_const.mul continuous_id
  have hpre : (fun z : R ↦ Ring.inverse x * z) ⁻¹' {a : R | IsUnit a} ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (by rw [Ring.inverse_mul_cancel _ hx]; exact h)
  refine Filter.mem_of_superset hpre fun z hz ↦ ?_
  have : z = x * (Ring.inverse x * z) := by rw [Ring.mul_inverse_cancel_left _ _ hx]
  rw [mem_ofPred_eq, this]
  exact hx.mul hz

/-- **Inversion is continuous as soon as it is continuous at `1`** ([GN26, Lemma 2.2.14]
(b)). -/
theorem continuousOn_inverse_of_continuousAt_one (hS : IsOpen {a : R | IsUnit a})
    (h : ContinuousAt (Ring.inverse : R → R) 1) :
    ContinuousOn (Ring.inverse : R → R) {a : R | IsUnit a} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hc : Continuous fun z : R ↦ Ring.inverse x * z := continuous_const.mul continuous_id
  have h1 : ContinuousAt (fun z : R ↦ Ring.inverse (Ring.inverse x * z) * Ring.inverse x) x := by
    refine ContinuousAt.mul ?_ continuousAt_const
    have h' : ContinuousAt (Ring.inverse : R → R) (Ring.inverse x * x) := by
      rw [Ring.inverse_mul_cancel _ hx]; exact h
    exact h'.comp (f := fun z : R ↦ Ring.inverse x * z) hc.continuousAt
  refine h1.congr ?_
  filter_upwards [hS.mem_nhds hx] with z hz
  have hu : IsUnit (Ring.inverse x * z) := hx.ringInverse.mul hz
  symm
  refine Ring.inverse_eq_of_mul_eq_one ?_ ?_
  · calc z * (Ring.inverse (Ring.inverse x * z) * Ring.inverse x)
        = x * ((Ring.inverse x * z) * Ring.inverse (Ring.inverse x * z)) * Ring.inverse x := by
          simp only [← mul_assoc, Ring.mul_inverse_cancel _ hx, one_mul]
      _ = 1 := by rw [Ring.mul_inverse_cancel _ hu, mul_one, Ring.mul_inverse_cancel _ hx]
  · calc Ring.inverse (Ring.inverse x * z) * Ring.inverse x * z
        = Ring.inverse (Ring.inverse x * z) * (Ring.inverse x * z) := by rw [mul_assoc]
      _ = 1 := Ring.inverse_mul_cancel _ hu

end Units

/-! ### The complexification of a continuous inverse algebra -/

section ComplexifyCIA

/-- The algebra behind [GN26, Lemma 2.2.17]: with `c = a⁻¹ b` and `d = (1 + c²)⁻¹`,
`(a + i b)⁻¹ = d a⁻¹ - i d c a⁻¹`. -/
theorem complexify_inverse_identities {R : Type*} [Ring R] {a b ai d : R} (h1 : a * ai = 1)
    (h2 : ai * a = 1) (hd1 : d * (1 + ai * b * (ai * b)) = 1)
    (hd2 : (1 + ai * b * (ai * b)) * d = 1) :
    a * (d * ai) - b * -(d * (ai * b) * ai) = 1 ∧ a * -(d * (ai * b) * ai) + b * (d * ai) = 0 ∧
      d * ai * a - -(d * (ai * b) * ai) * b = 1 ∧ d * ai * b + -(d * (ai * b) * ai) * a = 0 := by
  set c := ai * b with hc
  set u := 1 + c * c
  have hb : b = a * c := by rw [hc, ← mul_assoc, h1, one_mul]
  have hcu : c * u = u * c := by simp only [u, mul_add, add_mul, mul_one, one_mul, mul_assoc]
  have hcd : c * d = d * c := by
    calc c * d = (d * u) * c * d := by rw [hd1, one_mul]
      _ = d * (u * c) * d := by simp only [mul_assoc]
      _ = d * (c * u) * d := by rw [hcu]
      _ = d * c * (u * d) := by simp only [mul_assoc]
      _ = d * c := by rw [hd2, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc a * (d * ai) - b * -(d * c * ai) = a * ((d + c * d * c) * ai) := by rw [hb]; noncomm_ring
      _ = a * ((d * u) * ai) := by rw [hcd]; simp only [u]; noncomm_ring
      _ = 1 := by rw [hd1, one_mul, h1]
  · calc a * -(d * c * ai) + b * (d * ai) = a * ((c * d - d * c) * ai) := by rw [hb]; noncomm_ring
      _ = 0 := by rw [hcd, sub_self, zero_mul, mul_zero]
  · calc d * ai * a - -(d * c * ai) * b = d * (ai * a) + d * c * c := by
          rw [hc]; noncomm_ring
      _ = d * u := by rw [h2]; simp only [u]; noncomm_ring
      _ = 1 := hd1
  · calc d * ai * b + -(d * c * ai) * a = d * c - d * c * (ai * a) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [h2, mul_one, sub_self]

variable {A : Type u} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [ContinuousInverseAlgebra A]

open Complexification

/-- **The complexification of a continuous inverse algebra is a continuous inverse algebra**
([GN26, Lemma 2.2.17]): near `1`, `(a + i b)⁻¹ = (1 + c²)⁻¹ (1 - i c) a⁻¹`, `c = a⁻¹ b`,
depends continuously on `(a, b)`; Lemma 2.2.14 concludes. -/
instance Complexification.continuousInverseAlgebra :
    ContinuousInverseAlgebra (Complexification A) := by
  have hSA : IsOpen {a : A | IsUnit a} := ContinuousInverseAlgebra.isOpen_units
  have hιA : ContinuousOn (Ring.inverse : A → A) {a : A | IsUnit a} :=
    ContinuousInverseAlgebra.continuousOn_inverse
  set c : Complexification A → A := fun p ↦ Ring.inverse (re p) * im p
  set u : Complexification A → A := fun p ↦ 1 + c p * c p
  set O₁ : Set (Complexification A) := re ⁻¹' {a : A | IsUnit a}
  have hO₁ : IsOpen O₁ := hSA.preimage continuous_re
  have hιre : ContinuousOn (fun p : Complexification A ↦ Ring.inverse (re p)) O₁ :=
    hιA.comp continuous_re.continuousOn fun p hp ↦ hp
  have hc : ContinuousOn c O₁ := hιre.mul continuous_im.continuousOn
  have hu : ContinuousOn u O₁ := continuousOn_const.add (hc.mul hc)
  set W := O₁ ∩ u ⁻¹' {a : A | IsUnit a}
  have hW : IsOpen W := hu.isOpen_inter_preimage hO₁ hSA
  set F : Complexification A → Complexification A := fun p ↦
    mk (Ring.inverse (u p) * Ring.inverse (re p))
      (-(Ring.inverse (u p) * c p * Ring.inverse (re p)))
  have hkey : ∀ p ∈ W, p * F p = 1 ∧ F p * p = 1 := by
    intro p hp
    obtain ⟨e1, e2, e3, e4⟩ := complexify_inverse_identities (b := im p)
      (Ring.mul_inverse_cancel _ hp.1) (Ring.inverse_mul_cancel _ hp.1)
      (Ring.inverse_mul_cancel _ hp.2) (Ring.mul_inverse_cancel _ hp.2)
    refine ⟨?_, ?_⟩ <;> ext
    · simp only [F, re_mul, re_mk, im_mk, re_one]; exact e1
    · simp only [F, im_mul, re_mk, im_mk, im_one]; exact e2
    · simp only [F, re_mul, re_mk, im_mk, re_one]; exact e3
    · simp only [F, im_mul, re_mk, im_mk, im_one]; exact e4
  have h1W : (1 : Complexification A) ∈ W := by
    refine ⟨by simp [O₁], ?_⟩
    simp [u, c]
  have hsub : W ⊆ {p : Complexification A | IsUnit p} := fun p hp ↦
    ⟨⟨p, F p, (hkey p hp).1, (hkey p hp).2⟩, rfl⟩
  have hopen : IsOpen {p : Complexification A | IsUnit p} :=
    isOpen_units_of_mem_nhds_one (Filter.mem_of_superset (hW.mem_nhds h1W) hsub)
  refine ⟨hopen, continuousOn_inverse_of_continuousAt_one hopen ?_⟩
  have hιu : ContinuousOn (fun p ↦ Ring.inverse (u p)) W :=
    hιA.comp (hu.mono inter_subset_left) fun p hp ↦ hp.2
  have hιre' : ContinuousOn (fun p : Complexification A ↦ Ring.inverse (re p)) W :=
    hιre.mono inter_subset_left
  have hF : ContinuousOn F W :=
    (hιu.mul hιre').prodMk ((hιu.mul (hc.mono inter_subset_left)).mul hιre').neg
  have hFat : ContinuousAt F 1 := hF.continuousAt (hW.mem_nhds h1W)
  refine hFat.congr ?_
  filter_upwards [hW.mem_nhds h1W] with p hp
  exact (Ring.inverse_eq_of_mul_eq_one (hkey p hp).1 (hkey p hp).2).symm

end ComplexifyCIA

/-! ### Real analyticity of inversion -/

section RealAnalytic

variable {A : Type u} [Ring A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [TopologicalSpace A] [IsTopologicalRing A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A]
  [T2Space A] [ContinuousInverseAlgebra A]

open Complexification

/-- **Inversion in a real continuous inverse algebra is real analytic**
([GN26, Proposition 2.2.13]): inversion in `A_ℂ`, a complex continuous inverse algebra by Lemma
2.2.17 (`Complexification.continuousInverseAlgebra`), is complex analytic
(`complexAnalyticOn_inverse`) and extends inversion in `A`. -/
theorem realAnalyticOn_inverse : RealAnalyticOn (Ring.inverse : A → A) {a : A | IsUnit a} := by
  refine ⟨{p : Complexification A | IsUnit p}, ContinuousInverseAlgebra.isOpen_units,
    Ring.inverse, complexAnalyticOn_inverse, fun x hx ↦ ?_⟩
  have h1 : ofReal x * ofReal (Ring.inverse x) = (1 : Complexification A) := by
    change ofRealₗ x * ofRealₗ (Ring.inverse x) = 1
    rw [← ofRealₗ_mul, Ring.mul_inverse_cancel _ hx, ofRealₗ_one]
  have h2 : ofReal (Ring.inverse x) * ofReal x = (1 : Complexification A) := by
    change ofRealₗ (Ring.inverse x) * ofRealₗ x = 1
    rw [← ofRealₗ_mul, Ring.inverse_mul_cancel _ hx, ofRealₗ_one]
  exact ⟨⟨⟨_, _, h1, h2⟩, rfl⟩, Ring.inverse_eq_of_mul_eq_one h1 h2⟩

end RealAnalytic

end LocallyConvex.Analysis

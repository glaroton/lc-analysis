/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Complex

/-!
# Real analytic maps between locally convex spaces

[GN26, §2.2]: real analytic maps
in the sense of Milnor, defined through complex analytic extensions to the complexification.
As in `LocallyConvexAnalysis.Analytic.Complex`, **no completeness** of the spaces is assumed.

## Main definitions

* `Complexification E`: the complexification `E_ℂ = E × E` of a real locally convex space, with
  `(x + i y)(u, v) = (x u - y v, x v + y u)` (GN Definition 2.2.1); `Complexification.ofReal`
  is the inclusion `E → E_ℂ`.
* `RealAnalyticOn f U`: `f` extends to a complex analytic map on an open neighbourhood of `U`
  in `E_ℂ` (Milnor; GN Definition 2.2.2; Glöckner, Banach Center Publ. 55 (2002), Def. 2.3).
* `BSAnalyticOn f U`: `f` is continuous and locally a pointwise sum of continuous real
  homogeneous polynomials (Bochnak–Siciak, Studia Math. 39 (1971), Definition 5.6).

## Main results (no completeness)

* `RealAnalyticOn.of_local`: real analyticity is a local property (GN Lemma 2.2.3).
* `RealAnalyticOn.comp`: compositions of real analytic maps are real analytic
  (GN Proposition 2.2.4), using `ComplexAnalyticOn.comp`.
* `RealAnalyticOn.smoothMBOn`: real analytic maps are smooth, and
  `RealAnalyticOn.iteratedDMB_ext`: their differentials are those of any complex analytic
  extension (GN Lemma 2.2.5).
* `RealAnalyticOn.exists_taylor`: real analytic maps are locally the sum of their Taylor series
  (GN Lemma 2.2.6); hence `RealAnalyticOn.bsAnalyticOn`: they are analytic in the sense of
  Bochnak and Siciak.
* `ComplexAnalyticOn.realAnalyticOn`: complex analytic maps are real analytic
  (GN Proposition 2.2.11).
* Examples: `ContinuousLinearMap.realAnalyticOn`, `realAnalyticOn_const`.
* Operations on complex analytic maps: `ComplexAnalyticOn.comp`, `.mono`, `.congr`,
  `.of_local`, `ContinuousLinearMap.complexAnalyticOn`, `complexAnalyticOn_const`.

## Implementation notes

* `Complexification E` is a type synonym of `E × E`, so it carries the product topology and
  real structure; the complex structure is defined by hand, and `IsScalarTower ℝ ℂ` holds. The
  complex analytic theory of `LocallyConvexAnalysis.Analytic.Complex` applies to it, with the real
  Michal–Bastiani calculus of `E × E`.
* **Locality without the identity theorem in `E_ℂ`.** GN prove Lemma 2.2.3 by gluing local
  extensions defined on convex sets `(x + W) + i W`, which agree on overlaps by the identity
  theorem for complex analytic maps on the connected set `E_ℂ ⊇ V_x ∩ V_y` (GN Theorem 2.1.16
  (c)). Here (`Complexification.eqOn_box_inter`) it suffices to apply the identity theorem for
  holomorphic functions of one variable, composed with continuous complex linear functionals,
  along the complex line `z ↦ a + z b` through a point `a + i b` of the overlap: the line meets
  the convex overlap in a convex set containing `0`, `i` and a real interval around `0`, on
  which both extensions equal `f`.
* **Complex implies real analytic without conjugate spaces.** GN's extension
  `ψ⁻¹ ∘ (f × f̄) ∘ φ` (Lemmas 2.2.9 and 2.2.10) is written as
  `α ∘ f ∘ π₊ + β ∘ f ∘ π₋`, where `π₋` and `β` are conjugate linear; both terms are real smooth
  with complex linear differentials (`HolomorphicOn.clm_comp_comp`), which by Theorem 2.1.12
  is complex analyticity.
* The converse of `RealAnalyticOn.bsAnalyticOn` ([GN26, Remark 2.2.7], [BS71b, Theorem 7.1])
  is `realAnalyticOn_of_bsAnalyticOn` in `LocallyConvexAnalysis.Analytic.RealSeries`.
* The identity theorems (GN Theorems 2.1.16 and 2.2.8) and complex analytic extensions with
  values in a complex space (GN Proposition 2.2.12) are in
  `LocallyConvexAnalysis.Analytic.Identity`.
* Inversion in continuous inverse algebras (GN Proposition 2.2.13) is in
  `LocallyConvexAnalysis.Spaces.InverseAlgebra`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [J. Bochnak, J. Siciak, *Analytic functions in topological vector-spaces*][BS71b]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### The complexification of a real space -/

/-- The *complexification* `E_ℂ = E × E` of a real vector space `E`
([GN26, Definition 2.2.1]): the pair `(u, v)` stands for `u + i v`. It is a type synonym of `E × E`,
carrying the product topology and real structure, and the complex scalar multiplication
`(x + i y) (u, v) = (x u - y v, x v + y u)`. -/
def Complexification (E : Type u) : Type u := E × E

namespace Complexification

variable {E : Type u}

/-- The point `u + i v` of `E_ℂ`. -/
def mk (u v : E) : Complexification E := (u, v)

/-- The real part. -/
def re (p : Complexification E) : E := Prod.fst (α := E) (β := E) p

/-- The imaginary part. -/
def im (p : Complexification E) : E := Prod.snd (α := E) (β := E) p

@[simp] theorem re_mk (u v : E) : re (mk u v) = u := rfl

@[simp] theorem im_mk (u v : E) : im (mk u v) = v := rfl

@[simp] theorem mk_re_im (p : Complexification E) : mk (re p) (im p) = p := rfl

@[ext] theorem ext {p q : Complexification E} (h₁ : re p = re q) (h₂ : im p = im q) : p = q :=
  Prod.ext h₁ h₂

section Topology

variable [TopologicalSpace E]

instance : TopologicalSpace (Complexification E) := inferInstanceAs (TopologicalSpace (E × E))

theorem continuous_re : Continuous (re : Complexification E → E) := continuous_fst

theorem continuous_im : Continuous (im : Complexification E → E) := continuous_snd

theorem continuous_mk {X : Type*} [TopologicalSpace X] {f g : X → E} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x ↦ mk (f x) (g x) :=
  hf.prodMk hg

instance [T2Space E] : T2Space (Complexification E) := inferInstanceAs (T2Space (E × E))

end Topology

variable [AddCommGroup E]

instance : AddCommGroup (Complexification E) := inferInstanceAs (AddCommGroup (E × E))

@[simp] theorem re_add (p q : Complexification E) : re (p + q) = re p + re q := rfl
@[simp] theorem im_add (p q : Complexification E) : im (p + q) = im p + im q := rfl
@[simp] theorem re_sub (p q : Complexification E) : re (p - q) = re p - re q := rfl
@[simp] theorem im_sub (p q : Complexification E) : im (p - q) = im p - im q := rfl
@[simp] theorem re_neg (p : Complexification E) : re (-p) = -re p := rfl
@[simp] theorem im_neg (p : Complexification E) : im (-p) = -im p := rfl
@[simp] theorem re_zero : re (0 : Complexification E) = 0 := rfl
@[simp] theorem im_zero : im (0 : Complexification E) = 0 := rfl
variable [Module ℝ E]

instance : Module ℝ (Complexification E) := inferInstanceAs (Module ℝ (E × E))

@[simp] theorem re_real_smul (r : ℝ) (p : Complexification E) : re (r • p) = r • re p := rfl
@[simp] theorem im_real_smul (r : ℝ) (p : Complexification E) : im (r • p) = r • im p := rfl

instance : SMul ℂ (Complexification E) :=
  ⟨fun z p ↦ mk (z.re • re p - z.im • im p) (z.re • im p + z.im • re p)⟩

@[simp] theorem re_smul (z : ℂ) (p : Complexification E) :
    re (z • p) = z.re • re p - z.im • im p := rfl

@[simp] theorem im_smul (z : ℂ) (p : Complexification E) :
    im (z • p) = z.re • im p + z.im • re p := rfl

instance : Module ℂ (Complexification E) where
  one_smul p := by ext <;> simp
  mul_smul z w p := by ext <;> simp [smul_sub, smul_add, smul_smul] <;> module
  smul_zero z := by ext <;> simp
  smul_add z p q := by ext <;> simp [smul_add] <;> abel
  add_smul z w p := by ext <;> simp [add_smul] <;> abel
  zero_smul p := by ext <;> simp

instance : IsScalarTower ℝ ℂ (Complexification E) :=
  ⟨fun r z p ↦ by ext <;> simp [smul_sub, smul_add, smul_smul]⟩

/-- The real space `E` inside its complexification, `u ↦ u + i 0`. -/
def ofRealₗ : E →ₗ[ℝ] Complexification E where
  toFun u := mk u 0
  map_add' u v := by ext <;> simp
  map_smul' r u := by ext <;> simp

@[simp] theorem re_ofRealₗ (u : E) : re (ofRealₗ u) = u := rfl
@[simp] theorem im_ofRealₗ (u : E) : im (ofRealₗ u) = 0 := rfl

theorem mk_eq_add_I_smul (u v : E) : mk u v = ofRealₗ u + Complex.I • ofRealₗ v := by
  ext <;> simp

/-- A real scalar acts on `E_ℂ` as the corresponding complex scalar. -/
theorem ofReal_smul (r : ℝ) (p : Complexification E) : (r : ℂ) • p = r • p := by
  ext
  · rw [re_smul, re_real_smul]; simp
  · rw [im_smul, im_real_smul]; simp

section TopologicalVectorSpace

variable [TopologicalSpace E]

/-- The real part, as a continuous real linear map. -/
def reCLM : Complexification E →L[ℝ] E where
  toFun := re
  map_add' := re_add
  map_smul' := re_real_smul
  cont := continuous_re

/-- The imaginary part, as a continuous real linear map. -/
def imCLM : Complexification E →L[ℝ] E where
  toFun := im
  map_add' := im_add
  map_smul' := im_real_smul
  cont := continuous_im

/-- The inclusion `E → E_ℂ`, `u ↦ u + i 0`, as a continuous real linear map. -/
def ofReal : E →L[ℝ] Complexification E where
  toLinearMap := ofRealₗ
  cont := continuous_mk continuous_id continuous_const

@[simp] theorem reCLM_apply (p : Complexification E) : reCLM p = re p := rfl
@[simp] theorem imCLM_apply (p : Complexification E) : imCLM p = im p := rfl
@[simp] theorem re_ofReal (u : E) : re (ofReal u) = u := rfl
@[simp] theorem im_ofReal (u : E) : im (ofReal u) = 0 := rfl

theorem ofReal_injective : Injective (ofReal : E → Complexification E) := fun u v h ↦ by
  simpa using congrArg re h

/-- `x ↦ A x + i B x`, for continuous real linear maps `A`, `B`. -/
def mkCLM {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] (A B : X →L[ℝ] E) :
    X →L[ℝ] Complexification E where
  toFun x := mk (A x) (B x)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp
  cont := continuous_mk A.continuous B.continuous

@[simp] theorem re_mkCLM {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (A B : X →L[ℝ] E) (x : X) : re (mkCLM A B x) = A x := rfl

@[simp] theorem im_mkCLM {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (A B : X →L[ℝ] E) (x : X) : im (mkCLM A B x) = B x := rfl

variable [IsTopologicalAddGroup E]

instance : IsTopologicalAddGroup (Complexification E) :=
  inferInstanceAs (IsTopologicalAddGroup (E × E))

variable [ContinuousSMul ℝ E]

instance : ContinuousSMul ℝ (Complexification E) := inferInstanceAs (ContinuousSMul ℝ (E × E))

instance [LocallyConvexSpace ℝ E] : LocallyConvexSpace ℝ (Complexification E) :=
  inferInstanceAs (LocallyConvexSpace ℝ (E × E))

instance : ContinuousSMul ℂ (Complexification E) := by
  refine ⟨continuous_mk ?_ ?_⟩
  · exact ((Complex.continuous_re.comp continuous_fst).smul (continuous_re.comp continuous_snd)).sub
      ((Complex.continuous_im.comp continuous_fst).smul (continuous_im.comp continuous_snd))
  · exact ((Complex.continuous_re.comp continuous_fst).smul (continuous_im.comp continuous_snd)).add
      ((Complex.continuous_im.comp continuous_fst).smul (continuous_re.comp continuous_snd))

end TopologicalVectorSpace

end Complexification

/-! ### Operations on complex analytic maps -/

section ComplexOperations

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
  [LocallyConvexSpace ℝ G] [T2Space G]

attribute [local instance] continuousSMul_real_of_complex

variable {f : E → F} {U V : Set E}

omit [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem HolomorphicOn.mono (hf : HolomorphicOn f U) (hVU : V ⊆ U) : HolomorphicOn f V :=
  ⟨fun k ↦ (hf.1 k).mono hVU, fun x hx ↦ hf.2 x (hVU hx)⟩

omit [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] in
theorem HolomorphicOn.congr (hf : HolomorphicOn f U) (hU : IsOpen U) {g : E → F}
    (h : EqOn f g U) : HolomorphicOn g U := by
  refine ⟨fun k ↦ ContDiffMBOn.congr_of_isOpen hU h (hf.1 k), fun x hx c v ↦ ?_⟩
  have hev : f =ᶠ[𝓝 x] g := h.eventuallyEq_of_mem (hU.mem_nhds hx)
  rw [← dMB_congr_of_eventuallyEq hev, ← dMB_congr_of_eventuallyEq hev]
  exact hf.2 x hx c v

omit [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
theorem HolomorphicOn.of_local (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ HolomorphicOn f (U ∩ W)) : HolomorphicOn f U := by
  refine ⟨fun k ↦ ContDiffMBOn.of_local hU fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨W, hW, hxW, hf⟩ := h x hx
    exact ⟨W, hW, hxW, hf.1 k⟩
  · obtain ⟨W, -, hxW, hf⟩ := h x hx
    exact hf.2 x ⟨hx, hxW⟩

theorem HolomorphicOn.comp {g : F → G} {V : Set F} (hg : HolomorphicOn g V)
    (hf : HolomorphicOn f U) (hU : IsOpen U) (hV : IsOpen V) (hUV : MapsTo f U V) :
    HolomorphicOn (g ∘ f) U := by
  refine ⟨fun k ↦ ContDiffMBOn.comp hU hV (hg.1 k) (hf.1 k) hUV, fun x hx c v ↦ ?_⟩
  rw [ContDiffMBOn.dMB_comp hV (hg.1 1) (hf.1 1) hUV hx,
    ContDiffMBOn.dMB_comp hV (hg.1 1) (hf.1 1) hUV hx, hf.2 x hx, hg.2 _ (hUV hx)]

/-- Complex analyticity passes to open subsets. -/
theorem ComplexAnalyticOn.mono (hf : ComplexAnalyticOn f U) (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) : ComplexAnalyticOn f V :=
  (complexAnalyticOn_iff_holomorphicOn hV).2
    (((complexAnalyticOn_iff_holomorphicOn hU).1 hf).mono hVU)

/-- Complex analyticity on an open set only depends on the values there. -/
theorem ComplexAnalyticOn.congr (hf : ComplexAnalyticOn f U) (hU : IsOpen U) {g : E → F}
    (h : EqOn f g U) : ComplexAnalyticOn g U :=
  (complexAnalyticOn_iff_holomorphicOn hU).2
    (((complexAnalyticOn_iff_holomorphicOn hU).1 hf).congr hU h)

/-- Complex analyticity is a local property. -/
theorem ComplexAnalyticOn.of_local (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ ComplexAnalyticOn f (U ∩ W)) :
    ComplexAnalyticOn f U :=
  (complexAnalyticOn_iff_holomorphicOn hU).2 <| HolomorphicOn.of_local hU fun x hx ↦ by
    obtain ⟨W, hW, hxW, hf⟩ := h x hx
    exact ⟨W, hW, hxW, (complexAnalyticOn_iff_holomorphicOn (hU.inter hW)).1 hf⟩

/-- **Compositions of complex analytic maps are complex analytic** (Glöckner–Neeb, used in the
proof of Proposition 2.2.4), without completeness: by Theorem 2.1.12 this is the chain rule of
the real Michal–Bastiani calculus. -/
theorem ComplexAnalyticOn.comp {g : F → G} {V : Set F} (hg : ComplexAnalyticOn g V)
    (hf : ComplexAnalyticOn f U) (hU : IsOpen U) (hV : IsOpen V) (hUV : MapsTo f U V) :
    ComplexAnalyticOn (g ∘ f) U :=
  (complexAnalyticOn_iff_holomorphicOn hU).2 <|
    ((complexAnalyticOn_iff_holomorphicOn hV).1 hg).comp
      ((complexAnalyticOn_iff_holomorphicOn hU).1 hf) hU hV hUV

/-- Continuous complex linear maps are complex analytic. -/
theorem _root_.ContinuousLinearMap.complexAnalyticOn (L : E →L[ℂ] F) (hU : IsOpen U) :
    ComplexAnalyticOn L U := by
  refine (complexAnalyticOn_iff_holomorphicOn hU).2 ⟨(L.restrictScalars ℝ).smoothMBOn U,
    fun x _ c v ↦ ?_⟩
  have hd : ∀ w, HasDirDerivAt L x w (L w) := (L.restrictScalars ℝ).hasDirDerivAt x
  rw [(hd _).dMB_eq, (hd _).dMB_eq, map_smul]

/-- Constant maps are complex analytic. -/
theorem complexAnalyticOn_const (c : F) (hU : IsOpen U) : ComplexAnalyticOn (fun _ : E ↦ c) U := by
  have hd : ∀ x v : E, HasDirDerivAt (fun _ : E ↦ c) x v 0 := fun x v ↦ by
    simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
  refine (complexAnalyticOn_iff_holomorphicOn hU).2 ⟨fun k ↦ contDiffMBOn_const k c U,
    fun x _ c' v ↦ ?_⟩
  rw [(hd x _).dMB_eq, (hd x _).dMB_eq, smul_zero]

end ComplexOperations

/-! ### Real analytic maps -/

section Definitions

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

open Complexification

/-- `f` is *real analytic* on `U` in the sense of Milnor ([GN26, Definition 2.2.2];
Glöckner, Banach Center Publ. 55 (2002), Definition 2.3): it extends to a complex analytic map
`g : E_ℂ → F_ℂ` on an open neighbourhood `V` of `U` in `E_ℂ`, i.e.
`g (x + i 0) = f x + i 0` for `x ∈ U`. -/
def RealAnalyticOn (f : E → F) (U : Set E) : Prop :=
  ∃ V : Set (Complexification E), IsOpen V ∧ ∃ g : Complexification E → Complexification F,
    ComplexAnalyticOn g V ∧ ∀ x ∈ U, ofReal x ∈ V ∧ g (ofReal x) = ofReal (f x)

/-- `f` is *analytic in the sense of Bochnak and Siciak* on `U` (Bochnak–Siciak, Studia Math. 39
(1971), Definition 5.6, for real scalars): `f` is continuous on `U` and, around each `x ∈ U`, it
is the pointwise limit of a series of continuous real homogeneous polynomials,
`f (x + y) = ∑ₖ pₖ (y)` for `y` in a `0`-neighbourhood. This is the real analogue of
`ComplexAnalyticOn`; it is weaker than `RealAnalyticOn` (`RealAnalyticOn.bsAnalyticOn`). -/
def BSAnalyticOn (f : E → F) (U : Set E) : Prop :=
  ContinuousOn f U ∧ ∀ x ∈ U, ∃ p : ℕ → E → F, (∀ n, IsContHomPoly ℝ n (p n)) ∧
    ∃ Y ∈ 𝓝 (0 : E), (∀ y ∈ Y, x + y ∈ U) ∧
      ∀ y ∈ Y, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, p n y) atTop (𝓝 (f (x + y)))

/-- Real analyticity passes to subsets. -/
theorem RealAnalyticOn.mono {f : E → F} {U U' : Set E} (hf : RealAnalyticOn f U) (h : U' ⊆ U) :
    RealAnalyticOn f U' := by
  obtain ⟨V, hV, g, hg, hext⟩ := hf
  exact ⟨V, hV, g, hg, fun x hx ↦ hext x (h hx)⟩

/-- Real analyticity depends only on the values on the set. -/
theorem RealAnalyticOn.congr {f g : E → F} {U : Set E} (hf : RealAnalyticOn f U)
    (h : EqOn g f U) : RealAnalyticOn g U := by
  obtain ⟨V, hV, G, hG, hext⟩ := hf
  exact ⟨V, hV, G, hG, fun x hx ↦ ⟨(hext x hx).1, by rw [(hext x hx).2, h hx]⟩⟩

end Definitions

section RealAnalytic

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {H : Type w} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
  [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H]

open Complexification

variable {f : E → F} {U : Set E}

/-- **Compositions of real analytic maps are real analytic** ([GN26, Proposition 2.2.4]):
compose complex analytic extensions. -/
theorem RealAnalyticOn.comp {g : F → H} {V : Set F} (hg : RealAnalyticOn g V)
    (hf : RealAnalyticOn f U) (hUV : MapsTo f U V) : RealAnalyticOn (g ∘ f) U := by
  obtain ⟨V₁, hV₁, g₁, hg₁, hg₁e⟩ := hg
  obtain ⟨U₁, hU₁, f₁, hf₁, hf₁e⟩ := hf
  have hU₂ : IsOpen (U₁ ∩ f₁ ⁻¹' V₁) := hf₁.1.isOpen_inter_preimage hU₁ hV₁
  refine ⟨U₁ ∩ f₁ ⁻¹' V₁, hU₂, g₁ ∘ f₁,
    hg₁.comp (hf₁.mono hU₁ hU₂ inter_subset_left) hU₂ hV₁ fun z hz ↦ hz.2, fun x hx ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hf₁e x hx
  obtain ⟨h3, h4⟩ := hg₁e (f x) (hUV hx)
  refine ⟨⟨h1, ?_⟩, ?_⟩
  · change f₁ (ofReal x) ∈ V₁
    rwa [h2]
  · simp [h2, h4]

/-- **Real analytic maps are smooth** ([GN26, Lemma 2.2.5]): `f = Re ∘ g ∘ ι` on `U`,
where `g` is a complex analytic extension, hence smooth (Theorem 2.1.12), and `ι : E → E_ℂ`,
`Re : F_ℂ → F` are continuous and real linear. -/
theorem RealAnalyticOn.smoothMBOn (hf : RealAnalyticOn f U) (hU : IsOpen U) : SmoothMBOn f U := by
  obtain ⟨V, hV, g, hg, hext⟩ := hf
  have hgs := hg.smoothMBOn hV
  intro k
  have h1 : ContDiffMBOn k (g ∘ ofReal) (ofReal ⁻¹' V) :=
    ContDiffMBOn.comp_clm ofReal hV (hgs k)
  have h2 : ContDiffMBOn k (reCLM ∘ (g ∘ ofReal)) (ofReal ⁻¹' V) :=
    ContDiffMBOn.comp (hV.preimage ofReal.continuous) isOpen_univ (reCLM.contDiffMBOn k univ) h1
      (mapsTo_univ _ _)
  refine ContDiffMBOn.congr_of_isOpen hU (fun x hx ↦ ?_) (h2.mono fun x hx ↦ (hext x hx).1)
  simp [(hext x hx).2]

/-- **The differentials of a real analytic map are those of its complex analytic extensions**
([GN26, Lemma 2.2.5]): `d⁽ⁿ⁾g(x, v₁, …, vₙ) = d⁽ⁿ⁾f(x, v₁, …, vₙ)` for `x ∈ U` and
`vᵢ ∈ E`, the right hand side seen in `F ⊆ F_ℂ`. -/
theorem RealAnalyticOn.iteratedDMB_ext (hU : IsOpen U) {V : Set (Complexification E)}
    (hV : IsOpen V) {g : Complexification E → Complexification F} (hg : ComplexAnalyticOn g V)
    (hext : ∀ x ∈ U, ofReal x ∈ V ∧ g (ofReal x) = ofReal (f x)) (n : ℕ) {x : E} (hx : x ∈ U)
    (v : Fin n → E) :
    iteratedDMB n g (ofReal x, fun i ↦ ofReal (v i)) = ofReal (iteratedDMB n f (x, v)) := by
  have hf : SmoothMBOn f U := RealAnalyticOn.smoothMBOn ⟨V, hV, g, hg, hext⟩ hU
  have e := iteratedDMB_comp_linearMap g
    ((ofReal : E →L[ℝ] Complexification E) : E →ₗ[ℝ] Complexification E) n x v
  simp only [ContinuousLinearMap.coe_coe] at e
  rw [← e]
  have hev : (g ∘ (ofReal : E →L[ℝ] Complexification E)) =ᶠ[𝓝 x]
      fun z ↦ ofReal (f z) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun z hz ↦ (hext z hz).2
  rw [iteratedDMB_congr_of_eventuallyEq n hev v,
    iteratedDMB_clm_comp hU (hf n) ofReal n le_rfl x hx v]

/-- **Taylor expansion of real analytic maps** ([GN26, Lemma 2.2.6]): around each
`x ∈ U`, `f (x + y) = ∑ₙ d⁽ⁿ⁾f(x, y, …, y)/n!` on a `0`-neighbourhood, as a limit of partial sums
in `F`. No completeness of `F` is used. -/
theorem RealAnalyticOn.exists_taylor (hf : RealAnalyticOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) : ∃ Y ∈ 𝓝 (0 : E), (∀ y ∈ Y, x + y ∈ U) ∧ ∀ y ∈ Y,
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
        (n.factorial : ℝ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y)) atTop (𝓝 (f (x + y))) := by
  obtain ⟨V, hV, g, hg, hext⟩ := hf
  have hhol := (complexAnalyticOn_iff_holomorphicOn hV).1 hg
  obtain ⟨Y₁, hY₁, -, hsum⟩ := hhol.exists_taylor hV (hext x hx).1
  have hY : ofReal ⁻¹' Y₁ ∩ (fun y ↦ x + y) ⁻¹' U ∈ 𝓝 (0 : E) := by
    refine inter_mem (ofReal.continuous.continuousAt.preimage_mem_nhds (by simpa using hY₁)) ?_
    exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds hx)
  refine ⟨_, hY, fun y hy ↦ hy.2, fun y hy ↦ ?_⟩
  have h := hsum (ofReal y) hy.1
  rw [← map_add, (hext (x + y) hy.2).2] at h
  have hterm : ∀ n, (n.factorial : ℂ)⁻¹ • iteratedDMB n g (ofReal x, fun _ ↦ ofReal y) =
      ofReal ((n.factorial : ℝ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y)) := by
    intro n
    rw [RealAnalyticOn.iteratedDMB_ext hU hV hg hext n hx (fun _ ↦ y), map_smul,
      ← ofReal_smul]
    push_cast
    rfl
  have hS : ∀ N, ∑ n ∈ Finset.range N,
      (n.factorial : ℂ)⁻¹ • iteratedDMB n g (ofReal x, fun _ ↦ ofReal y) =
      ofReal (∑ n ∈ Finset.range N, (n.factorial : ℝ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y)) :=
    fun N ↦ by rw [map_sum]; exact Finset.sum_congr rfl fun n _ ↦ hterm n
  simpa [Function.comp_def] using (reCLM.continuous.tendsto _).comp (h.congr hS)

/-- The Taylor polynomials `y ↦ d⁽ⁿ⁾f(x, y, …, y)/n!` of a `Cⁿ` map are continuous real
homogeneous polynomials ([GN26, Lemma 1.6.9]). -/
theorem ContDiffMBOn.isContHomPoly_taylor {n : ℕ} (hf : ContDiffMBOn n f U) (hU : IsOpen U)
    {x : E} (hx : x ∈ U) :
    IsContHomPoly ℝ n fun y ↦ (n.factorial : ℝ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y) := by
  obtain ⟨M, hM, -⟩ := hf.exists_iteratedDMB_multilinear hU hx
  exact ⟨(n.factorial : ℝ)⁻¹ • M, fun y ↦ by simp [hM]⟩

/-- **Real analytic maps are analytic in the sense of Bochnak and Siciak**: continuous and
locally the sum of a series of continuous homogeneous polynomials, the Taylor series
([GN26, Lemma 2.2.6]; the converse holds when `E` is a Fréchet space, GN Remark 2.2.7). -/
theorem RealAnalyticOn.bsAnalyticOn (hf : RealAnalyticOn f U) (hU : IsOpen U) :
    BSAnalyticOn f U := by
  have hs := hf.smoothMBOn hU
  refine ⟨hs 0, fun x hx ↦ ?_⟩
  obtain ⟨Y, hY, hYU, hsum⟩ := hf.exists_taylor hU hx
  exact ⟨_, fun n ↦ (hs n).isContHomPoly_taylor hU hx, Y, hY, hYU, hsum⟩

/-! ### Real analyticity is a local property -/

/-- The convex set `(x + C) + i C ⊆ E_ℂ` used to glue local extensions
([GN26, proof of Lemma 2.2.3]). -/
def Complexification.box (x : E) (C : Set E) : Set (Complexification E) :=
  {p | re p - x ∈ C ∧ im p ∈ C}

omit [Module ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] [ContinuousSMul ℝ E] in
theorem Complexification.isOpen_box (x : E) {C : Set E} (hC : IsOpen C) : IsOpen (box x C) :=
  (hC.preimage (continuous_re.sub continuous_const)).inter (hC.preimage continuous_im)

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
theorem Complexification.convex_box (x : E) {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ (box x C) := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · have e : re (a • p + b • q) - x = a • (re p - x) + b • (re q - x) := by
      simp only [re_add, re_real_smul]
      linear_combination (norm := module) hab • x
    rw [e]
    exact hC hp.1 hq.1 ha hb hab
  · simpa using hC hp.2 hq.2 ha hb hab

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem Complexification.ofReal_mem_box {x y : E} {C : Set E} :
    ofReal y ∈ box x C ↔ y - x ∈ C ∧ (0 : E) ∈ C :=
  Iff.rfl

/-- Local extension on a box: if `f` is real analytic on a neighbourhood of `x ∈ U`, it has a
complex analytic extension on `(x + C) + i C` for some convex open `0`-neighbourhood `C` with
`x + C ⊆ U`. -/
theorem RealAnalyticOn.exists_box (hf : RealAnalyticOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) :
    ∃ C : Set E, IsOpen C ∧ Convex ℝ C ∧ (0 : E) ∈ C ∧ (∀ c ∈ C, x + c ∈ U) ∧
      ∃ g : Complexification E → Complexification F, ComplexAnalyticOn g (box x C) ∧
        ∀ c ∈ C, g (ofReal (x + c)) = ofReal (f (x + c)) := by
  obtain ⟨V, hV, g, hg, hext⟩ := hf
  have hN : (fun e : E × E ↦ mk (x + e.1) e.2) ⁻¹' V ∈ 𝓝 ((0 : E), (0 : E)) := by
    have hc : Continuous fun e : E × E ↦ mk (x + e.1) e.2 :=
      continuous_mk (continuous_const.add continuous_fst) continuous_snd
    refine hc.continuousAt.preimage_mem_nhds ?_
    have : mk (x + 0) (0 : E) = ofReal x := by ext <;> simp
    rw [this]
    exact hV.mem_nhds (hext x hx).1
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hN
  have hD : (fun c ↦ x + c) ⁻¹' U ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds hx)
  obtain ⟨C, ⟨hC0, hCo, hCc⟩, hCsub⟩ :=
    (LocallyConvexSpace.convex_open_basis_zero ℝ E).mem_iff.1 (inter_mem (inter_mem hA hB) hD)
  refine ⟨C, hCo, hCc, hC0, fun c hc ↦ (hCsub hc).2, g,
    hg.mono hV (isOpen_box x hCo) fun p hp ↦ ?_, fun c hc ↦ (hext _ (hCsub hc).2).2⟩
  have h := hAB (show (re p - x, im p) ∈ A ×ˢ B from ⟨(hCsub hp.1).1.1, (hCsub hp.2).1.2⟩)
  have e : mk (x + (re p - x)) (im p) = p := by ext <;> simp
  simpa [e] using h

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Two complex analytic maps on boxes `(x + C) + i C` and `(x' + C') + i C'` which agree at the
real points of the intersection agree on the whole intersection. Glöckner–Neeb use the identity
theorem in `E_ℂ` (Theorem 2.1.16 (c)); here it suffices to apply the one variable identity
theorem along the complex line `z ↦ a + z b` through each point `a + i b` of the intersection,
since this line meets the convex intersection in a convex set containing `0`, `i` and a real
interval around `0`. -/
theorem Complexification.eqOn_box_inter {x x' : E} {C C' : Set E} (hC : IsOpen C)
    (hCc : Convex ℝ C) (hC' : IsOpen C') (hCc' : Convex ℝ C') (h0 : (0 : E) ∈ C)
    (h0' : (0 : E) ∈ C') {g g' : Complexification E → Complexification F}
    (hg : ComplexAnalyticOn g (box x C)) (hg' : ComplexAnalyticOn g' (box x' C'))
    (hgg' : ∀ y, ofReal y ∈ box x C ∩ box x' C' → g (ofReal y) = g' (ofReal y)) :
    EqOn g g' (box x C ∩ box x' C') := by
  have := polynormableSpace_complex (F := Complexification F)
  intro p hp
  set S := box x C ∩ box x' C'
  have hSo : IsOpen S := (isOpen_box x hC).inter (isOpen_box x' hC')
  have hSc : Convex ℝ S := (convex_box x hCc).inter (convex_box x' hCc')
  set a := ofReal (re p)
  set b := ofReal (im p)
  set D := {z : ℂ | a + z • b ∈ S}
  have hφ : Continuous fun z : ℂ ↦ a + z • b :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hDo : IsOpen D := hSo.preimage hφ
  have hDc : Convex ℝ D := by
    let L : ℂ →ₗ[ℝ] Complexification E := (LinearMap.id : ℂ →ₗ[ℝ] ℂ).smulRight b
    exact (hSc.translate_preimage_right a).linear_preimage L
  have ha : a ∈ S := ⟨⟨hp.1.1, h0⟩, ⟨hp.2.1, h0'⟩⟩
  have h0D : (0 : ℂ) ∈ D := by simpa [D] using ha
  have hID : a + Complex.I • b = p := by
    ext <;> simp [a, b]
  have hreal : ∀ t : ℝ, a + (t : ℂ) • b = ofReal (re p + t • im p) := fun t ↦ by
    rw [ofReal_smul, map_add, map_smul]
  refine eq_of_forall_clm_eq fun ℓ ↦ ?_
  have hd : ∀ {y : E} {K : Set E} {G : Complexification E → Complexification F},
      ComplexAnalyticOn G (box y K) → IsOpen K → S ⊆ box y K →
      AnalyticOnNhd ℂ (fun z : ℂ ↦ ℓ (G (a + z • b))) D := by
    intro y K G hG hK hSK
    have hA := hG.gateauxAnalyticOn (isOpen_box y hK) a (hSK ha) b
    exact ((hA.differentiableOn_clm ℓ).mono fun z hz ↦ hSK hz).analyticOnNhd hDo
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), ℓ (g (a + z • b)) = ℓ (g' (a + z • b)) := by
    have hev : ∀ᶠ t : ℝ in 𝓝 0, (t : ℂ) ∈ D :=
      Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (by simpa using hDo.mem_nhds h0D)
    have hev' : ∀ᶠ t : ℝ in 𝓝[≠] 0,
        ℓ (g (a + (t : ℂ) • b)) = ℓ (g' (a + (t : ℂ) • b)) := by
      refine (hev.filter_mono nhdsWithin_le_nhds).mono fun t ht ↦ ?_
      have ht' : a + (t : ℂ) • b ∈ S := ht
      rw [hreal] at ht' ⊢
      rw [hgg' _ ht']
    have hT : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      have := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
        (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0)
        fun t ht ↦ by simpa using ht
      simpa using this
    exact hT.frequently hev'.frequently
  have hI : Complex.I ∈ D := by
    change a + Complex.I • b ∈ S
    rw [hID]; exact hp
  have := (hd hg hC inter_subset_left).eqOn_of_preconnected_of_frequently_eq
    (hd hg' hC' inter_subset_right) hDc.isPreconnected h0D hfreq hI
  simpa [hID] using this

/-- **Real analyticity is a local property** ([GN26, Lemma 2.2.3]): if every point of
the open set `U` has a neighbourhood `W` with `f` real analytic on `U ∩ W`, then `f` is real
analytic on `U`. The local extensions, restricted to convex boxes `(x + C) + i C`, agree on
overlaps (`Complexification.eqOn_box_inter`) and glue to an extension on their union. -/
theorem RealAnalyticOn.of_local (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ RealAnalyticOn f (U ∩ W)) : RealAnalyticOn f U := by
  have hbox : ∀ x : U, ∃ C : Set E, IsOpen C ∧ Convex ℝ C ∧ (0 : E) ∈ C ∧
      ∃ g : Complexification E → Complexification F, ComplexAnalyticOn g (box (x : E) C) ∧
        ∀ c ∈ C, g (ofReal ((x : E) + c)) = ofReal (f ((x : E) + c)) := by
    rintro ⟨x, hx⟩
    obtain ⟨W, hW, hxW, hf⟩ := h x hx
    obtain ⟨C, hCo, hCc, hC0, -, g, hg, hgf⟩ := hf.exists_box (hU.inter hW) ⟨hx, hxW⟩
    exact ⟨C, hCo, hCc, hC0, g, hg, hgf⟩
  choose C hCo hCc hC0 g hg hgf using hbox
  set B : U → Set (Complexification E) := fun x ↦ box (x : E) (C x)
  have hBo : ∀ x, IsOpen (B x) := fun x ↦ isOpen_box _ (hCo x)
  have hreal : ∀ x : U, ∀ y, ofReal y ∈ B x → g x (ofReal y) = ofReal (f y) := by
    intro x y hy
    simpa using hgf x (y - x) (ofReal_mem_box.1 hy).1
  have hagree : ∀ x x' : U, EqOn (g x) (g x') (B x ∩ B x') := fun x x' ↦
    eqOn_box_inter (hCo x) (hCc x) (hCo x') (hCc x') (hC0 x) (hC0 x') (hg x) (hg x')
      fun y hy ↦ by rw [hreal x y hy.1, hreal x' y hy.2]
  classical
  let G : Complexification E → Complexification F := fun p ↦
    if hp : ∃ x : U, p ∈ B x then g hp.choose p else 0
  have hG : ∀ x : U, EqOn G (g x) (B x) := by
    intro x p hp
    have hex : ∃ x : U, p ∈ B x := ⟨x, hp⟩
    simp only [G, hex, ↓reduceDIte]
    exact hagree _ _ ⟨hex.choose_spec, hp⟩
  refine ⟨⋃ x, B x, isOpen_iUnion hBo, G, ?_, fun y hy ↦ ?_⟩
  · refine ComplexAnalyticOn.of_local (isOpen_iUnion hBo) fun p hp ↦ ?_
    obtain ⟨x, hx⟩ := mem_iUnion.1 hp
    refine ⟨B x, hBo x, hx, ?_⟩
    rw [inter_eq_right.2 (subset_iUnion B x)]
    exact (hg x).congr (hBo x) fun q hq ↦ (hG x hq).symm
  · have hy' : ofReal y ∈ B ⟨y, hy⟩ := ofReal_mem_box.2 ⟨by simpa using hC0 _, hC0 _⟩
    exact ⟨mem_iUnion.2 ⟨_, hy'⟩, (hG _ hy').trans (hreal _ y hy')⟩

/-! ### Examples -/

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The complexification `L_ℂ (u + i v) = L u + i L v` of a continuous real linear map, a
continuous complex linear map `E_ℂ → F_ℂ`. -/
def _root_.ContinuousLinearMap.complexify (L : E →L[ℝ] F) :
    Complexification E →L[ℂ] Complexification F where
  toFun p := mk (L (re p)) (L (im p))
  map_add' p q := by ext <;> simp
  map_smul' z p := by ext <;> simp [map_sub, map_add, map_smul]
  cont := continuous_mk (L.continuous.comp continuous_re) (L.continuous.comp continuous_im)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
@[simp] theorem _root_.ContinuousLinearMap.complexify_ofReal (L : E →L[ℝ] F) (x : E) :
    L.complexify (ofReal x) = ofReal (L x) := by
  ext <;> simp [ContinuousLinearMap.complexify]

/-- Continuous real linear maps are real analytic. -/
theorem _root_.ContinuousLinearMap.realAnalyticOn (L : E →L[ℝ] F) (U : Set E) :
    RealAnalyticOn L U :=
  ⟨univ, isOpen_univ, L.complexify, L.complexify.complexAnalyticOn isOpen_univ,
    fun x _ ↦ ⟨mem_univ _, L.complexify_ofReal x⟩⟩

/-- Constant maps are real analytic. -/
theorem realAnalyticOn_const (c : F) (U : Set E) : RealAnalyticOn (fun _ : E ↦ c) U :=
  ⟨univ, isOpen_univ, fun _ ↦ ofReal c, complexAnalyticOn_const _ isOpen_univ,
    fun _ _ ↦ ⟨mem_univ _, rfl⟩⟩

end RealAnalytic

/-! ### Complex analytic maps are real analytic -/

section ComplexToReal

/-- A real scalar acts as the corresponding complex scalar. -/
theorem ofReal_smul_eq {X : Type*} [AddCommGroup X] [Module ℝ X] [Module ℂ X]
    [IsScalarTower ℝ ℂ X] (r : ℝ) (w : X) : (r : ℂ) • w = r • w :=
  algebraMap_smul ℂ r w

/-- `c w = (Re c) w + (Im c) (i w)`. -/
theorem smul_eq_re_smul_add_im_smul {X : Type*} [AddCommGroup X] [Module ℝ X] [Module ℂ X]
    [IsScalarTower ℝ ℂ X] (c : ℂ) (w : X) : c • w = c.re • w + c.im • (Complex.I • w) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, ofReal_smul_eq, ofReal_smul_eq]

/-- A real linear map between complex vector spaces which commutes with `i` is complex
linear. -/
theorem map_smul_of_map_I_smul {X Y : Type*} [AddCommGroup X] [Module ℝ X] [Module ℂ X]
    [IsScalarTower ℝ ℂ X] [AddCommGroup Y] [Module ℝ Y] [Module ℂ Y] [IsScalarTower ℝ ℂ Y]
    {T : X → Y} (hadd : ∀ v w, T (v + w) = T v + T w) (hsmul : ∀ (r : ℝ) w, T (r • w) = r • T w)
    (hI : ∀ w, T (Complex.I • w) = Complex.I • T w) (c : ℂ) (w : X) : T (c • w) = c • T w := by
  rw [smul_eq_re_smul_add_im_smul, hadd, hsmul, hsmul, hI, ← smul_eq_re_smul_add_im_smul]

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]
  {E' : Type u} [AddCommGroup E'] [Module ℝ E'] [Module ℂ E'] [IsScalarTower ℝ ℂ E']
  [TopologicalSpace E'] [IsTopologicalAddGroup E'] [ContinuousSMul ℂ E']
  [LocallyConvexSpace ℝ E'] [T2Space E']
  {F' : Type v} [AddCommGroup F'] [Module ℝ F'] [Module ℂ F'] [IsScalarTower ℝ ℂ F']
  [TopologicalSpace F'] [IsTopologicalAddGroup F'] [ContinuousSMul ℂ F']
  [LocallyConvexSpace ℝ F'] [T2Space F']

attribute [local instance] continuousSMul_real_of_complex

variable {f : E → F} {U : Set E}

/-- Sums of maps which are smooth with complex linear differentials. -/
theorem HolomorphicOn.add {g : E → F} (hf : HolomorphicOn f U) (hg : HolomorphicOn g U)
    (hU : IsOpen U) : HolomorphicOn (fun x ↦ f x + g x) U := by
  have hd : ∀ x ∈ U, ∀ w, dMB (fun x ↦ f x + g x) (x, w) = dMB f (x, w) + dMB g (x, w) :=
    fun x hx w ↦ (((hf.1 1).2.1 x hx w).add ((hg.1 1).2.1 x hx w)).dMB_eq
  refine ⟨fun k ↦ (hf.1 k).add hU (hg.1 k), fun x hx c w ↦ ?_⟩
  rw [hd x hx, hd x hx, hf.2 x hx, hg.2 x hx, smul_add]

/-- **Conjugate compositions**: if `f` is smooth with complex linear differentials, `A` and `B` are
continuous real linear maps and `A (i w) = ε A w`, `B (ε y) = i B y` (e.g. both complex linear,
`ε = i`, or both conjugate linear, `ε = -i`), then `B ∘ f ∘ A` is smooth with complex linear
differentials. -/
theorem HolomorphicOn.clm_comp_comp (hf : HolomorphicOn f U) (hU : IsOpen U)
    (A : E' →L[ℝ] E) (B : F →L[ℝ] F') (ε : ℂ) (hA : ∀ w, A (Complex.I • w) = ε • A w)
    (hB : ∀ y, B (ε • y) = Complex.I • B y) :
    HolomorphicOn (fun p ↦ B (f (A p))) (A ⁻¹' U) := by
  have hAU : IsOpen (A ⁻¹' U) := hU.preimage A.continuous
  refine ⟨fun k ↦ ?_, fun p hp c w ↦ ?_⟩
  · have h1 : ContDiffMBOn k (f ∘ A) (A ⁻¹' U) := ContDiffMBOn.comp_clm A hU (hf.1 k)
    exact ContDiffMBOn.comp hAU isOpen_univ (B.contDiffMBOn k univ) h1 (mapsTo_univ _ _)
  have hd : ∀ v, dMB (fun p ↦ B (f (A p))) (p, v) = B (dMB f (A p, A v)) := fun v ↦ by
    have h : HasDirDerivAt (f ∘ A) p v (dMB f (A p, A v)) :=
      ((hf.1 1).2.1 _ hp (A v)).congr fun t ↦ by simp [map_add, map_smul]
    exact (h.clm_comp_real B).dMB_eq
  have hD1 : ContDiffMBOn 1 f U := hf.1 1
  refine map_smul_of_map_I_smul (T := fun v ↦ dMB (fun p ↦ B (f (A p))) (p, v))
    (fun v w ↦ ?_) (fun r w ↦ ?_) (fun w ↦ ?_) c w
  · simp only [hd, map_add, hD1.dMB_add hU hp]
  · simp only [hd, map_smul, hD1.dMB_smul hp]
  · simp only [hd, hA, hf.2 _ hp, hB]

open Complexification in
/-- **Complex analytic maps are real analytic** ([GN26, Proposition 2.2.11]), without
completeness. With `π± (u + i v) = u ± i v` (`π₊ : E_ℂ → E` complex linear, `π₋` conjugate
linear) and `α y = (y - i (i y))/2`, `β y = (y + i (i y))/2` (the outer `i` of `F_ℂ`, the inner
one of `F`; `α` complex linear, `β` conjugate linear), the map
`g = α ∘ f ∘ π₊ + β ∘ f ∘ π₋` is complex analytic on `π₊⁻¹(U) ∩ π₋⁻¹(U)` and extends `f`.
This is GN's extension `ψ⁻¹ ∘ (f × f̄) ∘ φ` written without the conjugate spaces `Ē`, `F̄`. -/
theorem ComplexAnalyticOn.realAnalyticOn (hf : ComplexAnalyticOn f U) (hU : IsOpen U) :
    RealAnalyticOn f U := by
  have hhol := (complexAnalyticOn_iff_holomorphicOn hU).1 hf
  let J : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  let JF : F →L[ℝ] F := (Complex.I • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
  let πp : Complexification E →L[ℝ] E := reCLM + J.comp imCLM
  let πm : Complexification E →L[ℝ] E := reCLM - J.comp imCLM
  let α : F →L[ℝ] Complexification F :=
    mkCLM ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ F) ((2 : ℝ)⁻¹ • -JF)
  let β : F →L[ℝ] Complexification F :=
    mkCLM ((2 : ℝ)⁻¹ • ContinuousLinearMap.id ℝ F) ((2 : ℝ)⁻¹ • JF)
  have hπp : ∀ w, πp (Complex.I • w) = Complex.I • πp w := fun w ↦ by
    simp [πp, J, smul_add, smul_smul]; abel
  have hπm : ∀ w, πm (Complex.I • w) = (-Complex.I) • πm w := fun w ↦ by
    simp [πm, J, smul_sub, smul_smul]; abel
  have hα : ∀ y, α (Complex.I • y) = Complex.I • α y := fun y ↦ by
    ext <;> simp [α, JF, smul_smul, smul_comm (2 : ℝ)⁻¹ Complex.I]
  have hβ : ∀ y, β ((-Complex.I) • y) = Complex.I • β y := fun y ↦ by
    ext <;> simp [β, JF, smul_smul, smul_comm (2 : ℝ)⁻¹ Complex.I]
  set Ω := πp ⁻¹' U ∩ πm ⁻¹' U
  have hΩ : IsOpen Ω := (hU.preimage πp.continuous).inter (hU.preimage πm.continuous)
  have hg : HolomorphicOn (fun p ↦ α (f (πp p)) + β (f (πm p))) Ω :=
    ((hhol.clm_comp_comp hU πp α _ hπp hα).mono inter_subset_left).add
      ((hhol.clm_comp_comp hU πm β _ hπm hβ).mono inter_subset_right) hΩ
  refine ⟨Ω, hΩ, _, (complexAnalyticOn_iff_holomorphicOn hΩ).2 hg, fun x hx ↦ ⟨?_, ?_⟩⟩
  · simpa [Ω, πp, πm] using hx
  · ext
    · simp [πp, πm, α, β, ← add_smul]
      norm_num
    · simp [πp, πm, α, β, JF]

end ComplexToReal

end LocallyConvex.Analysis

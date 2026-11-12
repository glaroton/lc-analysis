/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Real
public import LocallyConvexAnalysis.Calculus.Rules

/-!
# Operations on analytic maps

Algebraic operations on complex and real analytic maps between locally convex spaces, and the
differential of a real analytic map. As everywhere in `LocallyConvexAnalysis`, **no completeness**
of the spaces is assumed.

## Main results

* `ComplexAnalyticOn.prodMk`, `.add`, `.const_smul`, `.sum`, `ComplexAnalyticOn.bilin`: pairs,
  sums, scalar multiples and continuous complex bilinear images of complex analytic maps are
  complex analytic. The proofs go through `complexAnalyticOn_iff_holomorphicOn`
  ([GN26, Theorem 2.1.12]): smoothness with complex linear differentials.
* `Complexification.prodCLM`: the complex linear homeomorphism `(E × F)_ℂ ≅ E_ℂ × F_ℂ`.
* `RealAnalyticOn.prodMk`, `.clm_comp`, `.comp_clm`, `.add`, `.const_smul`, `.sum`,
  `RealAnalyticOn.bilin`: the same operations on real analytic maps; for `bilin`, the
  complexification `β_ℂ` of a continuous real bilinear map `β` (`Complexification.bilinComplexify`).
* `RealAnalyticOn.dMB`: **the differential `df : U × E → F` of a real analytic map is real
  analytic**. Glöckner and Neeb use this without comment for `r = ω` when they make `TM` a
  `C^{r-1}`-manifold ([GN26, Lemma 3.3.8(d)]); [Glo02, Lemma 2.6] states the complex case. If `g`
  is a complex analytic extension of `f`, then `dg` is complex analytic
  (`ComplexAnalyticOn.dMB`, [Glo02, Lemma 2.6]) and `dg ∘ (E × E)_ℂ ≅ E_ℂ × E_ℂ` extends `df`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [H. Glöckner, *Infinite-dimensional Lie groups without completeness restrictions*][Glo02]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

/-! ### Complex analytic maps -/

section Complex

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type v} [AddCommGroup G] [Module ℝ G] [Module ℂ G] [IsScalarTower ℝ ℂ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G]
  [LocallyConvexSpace ℝ G] [T2Space G]

attribute [local instance] continuousSMul_real_of_complex

variable {f : E → F} {U : Set E}

omit [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F]
  [IsScalarTower ℝ ℂ G] [IsTopologicalAddGroup G] [ContinuousSMul ℂ G] [LocallyConvexSpace ℝ G] in
/-- Pairs of maps which are smooth with complex linear differentials. -/
theorem HolomorphicOn.prodMk {g : E → G} (hf : HolomorphicOn f U) (hg : HolomorphicOn g U)
    (hU : IsOpen U) : HolomorphicOn (fun x ↦ (f x, g x)) U := by
  refine ⟨fun k ↦ (hf.1 k).prodMk hU (hg.1 k), fun x hx c w ↦ ?_⟩
  have hd : ∀ w, dMB (fun x ↦ (f x, g x)) (x, w) = (dMB f (x, w), dMB g (x, w)) := fun w ↦
    (((hf.1 1).2.1 x hx w).prodMk ((hg.1 1).2.1 x hx w)).dMB_eq
  rw [hd, hd, hf.2 x hx, hg.2 x hx, Prod.smul_mk]

/-- Pairs of complex analytic maps are complex analytic. -/
theorem ComplexAnalyticOn.prodMk {g : E → G} (hf : ComplexAnalyticOn f U)
    (hg : ComplexAnalyticOn g U) (hU : IsOpen U) : ComplexAnalyticOn (fun x ↦ (f x, g x)) U :=
  (complexAnalyticOn_iff_holomorphicOn hU).2 <|
    ((complexAnalyticOn_iff_holomorphicOn hU).1 hf).prodMk
      ((complexAnalyticOn_iff_holomorphicOn hU).1 hg) hU

/-- Sums of complex analytic maps are complex analytic. -/
theorem ComplexAnalyticOn.add {g : E → F} (hf : ComplexAnalyticOn f U)
    (hg : ComplexAnalyticOn g U) (hU : IsOpen U) : ComplexAnalyticOn (fun x ↦ f x + g x) U :=
  (complexAnalyticOn_iff_holomorphicOn hU).2 <|
    ((complexAnalyticOn_iff_holomorphicOn hU).1 hf).add
      ((complexAnalyticOn_iff_holomorphicOn hU).1 hg) hU

/-- Complex multiples of complex analytic maps are complex analytic. -/
theorem ComplexAnalyticOn.const_smul (hf : ComplexAnalyticOn f U) (hU : IsOpen U) (c : ℂ) :
    ComplexAnalyticOn (fun x ↦ c • f x) U :=
  ((c • ContinuousLinearMap.id ℂ F).complexAnalyticOn isOpen_univ).comp hf hU isOpen_univ
    (mapsTo_univ _ _)

/-- Finite sums of complex analytic maps are complex analytic. -/
theorem ComplexAnalyticOn.sum {ι : Type*} (s : Finset ι) {f : ι → E → F} (hU : IsOpen U)
    (hf : ∀ i ∈ s, ComplexAnalyticOn (f i) U) : ComplexAnalyticOn (fun x ↦ ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using complexAnalyticOn_const (0 : F) hU
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) hU

section Bilinear

variable {A B : Type u} [AddCommGroup A] [Module ℝ A] [Module ℂ A] [IsScalarTower ℝ ℂ A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℂ A]
  [LocallyConvexSpace ℝ A] [T2Space A]
  [AddCommGroup B] [Module ℝ B] [Module ℂ B] [IsScalarTower ℝ ℂ B]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul ℂ B]
  [LocallyConvexSpace ℝ B] [T2Space B]

/-- **Continuous complex bilinear maps are complex analytic**: they are smooth
(`contDiffMBOn_bilin`), with complex linear differentials `(a, b) ↦ β(x, b) + β(a, y)`. Joint
continuity is assumed, as in `ContDiffMBOn.bilin`. -/
theorem complexAnalyticOn_bilin (β : A →ₗ[ℂ] B →ₗ[ℂ] F)
    (hβ : Continuous fun p : A × B ↦ β p.1 p.2) :
    ComplexAnalyticOn (fun p : A × B ↦ β p.1 p.2) univ := by
  let βℝ : A →ₗ[ℝ] B →ₗ[ℝ] F := LinearMap.mk₂ ℝ (fun a b ↦ β a b)
    (fun a a' b ↦ by simp) (fun r a b ↦ by simp only [← ofReal_smul_eq r, map_smul,
      LinearMap.smul_apply])
    (fun a b b' ↦ by simp) (fun r a b ↦ by simp only [← ofReal_smul_eq r, map_smul])
  have hβℝ : ∀ a b, βℝ a b = β a b := fun _ _ ↦ rfl
  refine (complexAnalyticOn_iff_holomorphicOn isOpen_univ).2 ⟨fun k ↦ ?_, fun p _ c q ↦ ?_⟩
  · simpa [hβℝ] using contDiffMBOn_bilin βℝ hβ k
  · have h := fun q ↦ (hasDirDerivAt_bilin βℝ p q).dMB_eq
    simp only [hβℝ] at h
    rw [h q, h (c • q)]
    simp only [ Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply, smul_add]

/-- Continuous complex bilinear images of complex analytic maps are complex analytic. -/
theorem ComplexAnalyticOn.bilin (β : A →ₗ[ℂ] B →ₗ[ℂ] F)
    (hβ : Continuous fun p : A × B ↦ β p.1 p.2) {f : E → A} {g : E → B}
    (hf : ComplexAnalyticOn f U) (hg : ComplexAnalyticOn g U) (hU : IsOpen U) :
    ComplexAnalyticOn (fun x ↦ β (f x) (g x)) U :=
  (complexAnalyticOn_bilin β hβ).comp (hf.prodMk hg hU) hU isOpen_univ (mapsTo_univ _ _)

end Bilinear

end Complex

/-! ### Complexifications of products and of bilinear maps -/

namespace Complexification

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The complex linear homeomorphism `(E × F)_ℂ → E_ℂ × F_ℂ`,
`(u, v) + i (u', v') ↦ (u + i u', v + i v')`. -/
def prodCLM : Complexification (E × F) →L[ℂ] Complexification E × Complexification F where
  toFun p := (mk (re p).1 (im p).1, mk (re p).2 (im p).2)
  map_add' p q := by ext <;> simp
  map_smul' z p := by ext <;> simp
  cont := (continuous_mk (continuous_fst.comp continuous_re)
      (continuous_fst.comp continuous_im)).prodMk
    (continuous_mk (continuous_snd.comp continuous_re) (continuous_snd.comp continuous_im))

@[simp] theorem prodCLM_ofReal (x : E × F) :
    prodCLM (ofReal x) = (ofReal x.1, ofReal x.2) := by
  ext <;> rfl

variable {A : Type*} [AddCommGroup A] [Module ℝ A] {B : Type*} [AddCommGroup B] [Module ℝ B]
  {C : Type*} [AddCommGroup C] [Module ℝ C]

/-- The complexification `β_ℂ (a + i a', b + i b') = β(a, b) - β(a', b') + i (β(a, b') + β(a', b))`
of a real bilinear map. -/
def bilinComplexify (β : A →ₗ[ℝ] B →ₗ[ℝ] C) :
    Complexification A →ₗ[ℂ] Complexification B →ₗ[ℂ] Complexification C :=
  LinearMap.mk₂ ℂ
    (fun p q ↦ mk (β (re p) (re q) - β (im p) (im q)) (β (re p) (im q) + β (im p) (re q)))
    (fun p p' q ↦ by ext <;> simp <;> abel)
    (fun z p q ↦ by ext <;> simp [smul_sub, smul_add] <;> module)
    (fun p q q' ↦ by ext <;> simp <;> abel)
    (fun z p q ↦ by ext <;> simp [smul_sub, smul_add] <;> module)

@[simp] theorem bilinComplexify_apply (β : A →ₗ[ℝ] B →ₗ[ℝ] C) (p : Complexification A)
    (q : Complexification B) :
    bilinComplexify β p q =
      mk (β (re p) (re q) - β (im p) (im q)) (β (re p) (im q) + β (im p) (re q)) := rfl

theorem bilinComplexify_ofReal (β : A →ₗ[ℝ] B →ₗ[ℝ] C) (a : A) (b : B) :
    bilinComplexify β (ofRealₗ a) (ofRealₗ b) = ofRealₗ (β a b) := by
  ext <;> simp

theorem continuous_bilinComplexify [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [IsTopologicalAddGroup C] (β : A →ₗ[ℝ] B →ₗ[ℝ] C)
    (hβ : Continuous fun p : A × B ↦ β p.1 p.2) :
    Continuous fun p : Complexification A × Complexification B ↦ bilinComplexify β p.1 p.2 := by
  have h : ∀ (g₁ : Complexification A × Complexification B → A)
      (g₂ : Complexification A × Complexification B → B), Continuous g₁ → Continuous g₂ →
      Continuous fun p ↦ β (g₁ p) (g₂ p) := fun g₁ g₂ h₁ h₂ ↦ hβ.comp (h₁.prodMk h₂)
  have r₁ : Continuous fun p : Complexification A × Complexification B ↦ re p.1 :=
    continuous_re.comp continuous_fst
  have i₁ : Continuous fun p : Complexification A × Complexification B ↦ im p.1 :=
    continuous_im.comp continuous_fst
  have r₂ : Continuous fun p : Complexification A × Complexification B ↦ re p.2 :=
    continuous_re.comp continuous_snd
  have i₂ : Continuous fun p : Complexification A × Complexification B ↦ im p.2 :=
    continuous_im.comp continuous_snd
  exact continuous_mk ((h _ _ r₁ r₂).sub (h _ _ i₁ i₂)) ((h _ _ r₁ i₂).add (h _ _ i₁ r₂))

end Complexification

/-! ### Real analytic maps -/

section Real

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {E' : Type u} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E'] [IsTopologicalAddGroup E']
  [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type v} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

open Complexification

variable {f : E → F} {U : Set E}

/-- Composition with a continuous linear map on the left. -/
theorem RealAnalyticOn.clm_comp (hf : RealAnalyticOn f U) (L : F →L[ℝ] G) :
    RealAnalyticOn (fun x ↦ L (f x)) U :=
  (L.realAnalyticOn univ).comp hf (mapsTo_univ _ _)

/-- Composition with a continuous linear map on the right. -/
theorem RealAnalyticOn.comp_clm {g : E' → F} {V : Set E'} (hg : RealAnalyticOn g V)
    (L : E →L[ℝ] E') : RealAnalyticOn (fun x ↦ g (L x)) (L ⁻¹' V) :=
  hg.comp (L.realAnalyticOn _) fun _ hx ↦ hx

/-- **Pairs of real analytic maps are real analytic**: if `f₁`, `g₁` are complex analytic
extensions of `f`, `g`, then `(f₁, g₁)`, read in `(F × G)_ℂ ≅ F_ℂ × G_ℂ`, extends `(f, g)`. -/
theorem RealAnalyticOn.prodMk {g : E → G} (hf : RealAnalyticOn f U) (hg : RealAnalyticOn g U) :
    RealAnalyticOn (fun x ↦ (f x, g x)) U := by
  obtain ⟨V₁, hV₁, f₁, hf₁, hf₁e⟩ := hf
  obtain ⟨V₂, hV₂, g₁, hg₁, hg₁e⟩ := hg
  -- the inverse of `prodCLM`, as a complex linear map
  let Q : Complexification F × Complexification G →L[ℂ] Complexification (F × G) :=
    { toFun := fun p ↦ mk (re p.1, re p.2) (im p.1, im p.2)
      map_add' := fun p q ↦ by ext <;> rfl
      map_smul' := fun z p ↦ by ext <;> rfl
      cont := continuous_mk ((continuous_re.comp continuous_fst).prodMk
          (continuous_re.comp continuous_snd))
        ((continuous_im.comp continuous_fst).prodMk (continuous_im.comp continuous_snd)) }
  have hV : IsOpen (V₁ ∩ V₂) := hV₁.inter hV₂
  refine ⟨V₁ ∩ V₂, hV, fun z ↦ Q (f₁ z, g₁ z),
    (Q.complexAnalyticOn isOpen_univ).comp ((hf₁.mono hV₁ hV inter_subset_left).prodMk
      (hg₁.mono hV₂ hV inter_subset_right) hV) hV isOpen_univ (mapsTo_univ _ _),
    fun x hx ↦ ⟨⟨(hf₁e x hx).1, (hg₁e x hx).1⟩, ?_⟩⟩
  beta_reduce
  rw [(hf₁e x hx).2, (hg₁e x hx).2]
  rfl

/-- Sums of real analytic maps are real analytic. -/
theorem RealAnalyticOn.add {g : E → F} (hf : RealAnalyticOn f U) (hg : RealAnalyticOn g U) :
    RealAnalyticOn (fun x ↦ f x + g x) U :=
  (hf.prodMk hg).clm_comp (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F)

/-- Real multiples of real analytic maps are real analytic. -/
theorem RealAnalyticOn.const_smul (hf : RealAnalyticOn f U) (c : ℝ) :
    RealAnalyticOn (fun x ↦ c • f x) U :=
  hf.clm_comp (c • ContinuousLinearMap.id ℝ F)

/-- Negatives of real analytic maps are real analytic. -/
theorem RealAnalyticOn.neg (hf : RealAnalyticOn f U) : RealAnalyticOn (fun x ↦ -f x) U :=
  hf.clm_comp (-ContinuousLinearMap.id ℝ F)

/-- Differences of real analytic maps are real analytic. -/
theorem RealAnalyticOn.sub {g : E → F} (hf : RealAnalyticOn f U) (hg : RealAnalyticOn g U) :
    RealAnalyticOn (fun x ↦ f x - g x) U := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Finite sums of real analytic maps are real analytic. -/
theorem RealAnalyticOn.sum {ι : Type*} (s : Finset ι) {f : ι → E → F}
    (hf : ∀ i ∈ s, RealAnalyticOn (f i) U) : RealAnalyticOn (fun x ↦ ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using realAnalyticOn_const (0 : F) U
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

section Bilinear

variable {A B : Type u} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul ℝ A] [LocallyConvexSpace ℝ A] [T2Space A]
  [AddCommGroup B] [Module ℝ B] [TopologicalSpace B]
  [IsTopologicalAddGroup B] [ContinuousSMul ℝ B] [LocallyConvexSpace ℝ B] [T2Space B]

/-- **Continuous real bilinear images of real analytic maps are real analytic**: the
complexification `β_ℂ` of `β` is a continuous complex bilinear map, hence complex analytic, and
`β_ℂ (f₁, g₁)` extends `β (f, g)`. -/
theorem RealAnalyticOn.bilin (β : A →ₗ[ℝ] B →ₗ[ℝ] F) (hβ : Continuous fun p : A × B ↦ β p.1 p.2)
    {f : E → A} {g : E → B} (hf : RealAnalyticOn f U) (hg : RealAnalyticOn g U) :
    RealAnalyticOn (fun x ↦ β (f x) (g x)) U := by
  obtain ⟨V₁, hV₁, f₁, hf₁, hf₁e⟩ := hf
  obtain ⟨V₂, hV₂, g₁, hg₁, hg₁e⟩ := hg
  have hV : IsOpen (V₁ ∩ V₂) := hV₁.inter hV₂
  refine ⟨V₁ ∩ V₂, hV, fun z ↦ bilinComplexify β (f₁ z) (g₁ z),
    ComplexAnalyticOn.bilin (bilinComplexify β) (continuous_bilinComplexify β hβ)
      (hf₁.mono hV₁ hV inter_subset_left) (hg₁.mono hV₂ hV inter_subset_right) hV,
    fun x hx ↦ ⟨⟨(hf₁e x hx).1, (hg₁e x hx).1⟩, ?_⟩⟩
  beta_reduce
  rw [(hf₁e x hx).2, (hg₁e x hx).2]
  exact bilinComplexify_ofReal β _ _

end Bilinear

/-- **The differential of a real analytic map is real analytic** on `U × E`. If `g` is a complex
analytic extension of `f` on `V ⊆ E_ℂ`, then `dg` is complex analytic on `V × E_ℂ`
(`ComplexAnalyticOn.dMB`), and `dg ∘ prodCLM` extends `df` because
`dg(x + i 0, v + i 0) = df(x, v) + i 0` (`RealAnalyticOn.iteratedDMB_ext`). -/
theorem RealAnalyticOn.dMB (hf : RealAnalyticOn f U) (hU : IsOpen U) :
    RealAnalyticOn (dMB f) (U ×ˢ univ) := by
  obtain ⟨V, hV, g, hg, hext⟩ := hf
  have hVV : IsOpen (V ×ˢ (univ : Set (Complexification E))) := hV.prod isOpen_univ
  have hW : IsOpen (prodCLM ⁻¹' (V ×ˢ univ) : Set (Complexification (E × E))) :=
    hVV.preimage prodCLM.continuous
  refine ⟨_, hW, fun p ↦ LocallyConvex.Analysis.dMB g (prodCLM p),
    (hg.dMB hV).comp (prodCLM.complexAnalyticOn hW) hW hVV fun p hp ↦ hp,
    fun p hp ↦ ⟨?_, ?_⟩⟩
  · simpa using (hext p.1 hp.1).1
  · simp only [prodCLM_ofReal]
    simpa [iteratedDMB_one] using RealAnalyticOn.iteratedDMB_ext hU hV hg hext 1 hp.1 ![p.2]

end Real

end LocallyConvex.Analysis

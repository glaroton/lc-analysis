/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.Rules
public import LocallyConvexAnalysis.Calculus.MBFrechet

/-!
# Operations on `C^k` maps

Elementary operations on directional derivatives and `C^k` maps in the sense of Michal–Bastiani
that are used throughout lc-analysis and lc-manifolds: finite sums, maps into products, scalar
multiples and products with real functions, differences, products of maps, restriction of the
codomain to a closed subspace, evaluation of operator-valued maps, curves through a point, and
the locality of the differential. None of this needs completeness.

## Main results

* `hasDirDerivAt_pi`, `HasDirDerivAt.sum`, `HasDirDerivAt.clm_apply`, `HasDirDerivAt.smul_fun`:
  directional derivatives of maps into products, of finite sums, of evaluations of
  operator-valued maps, and of products of a real function with a vector-valued one.
* `hasDirDerivAt_line`, `hasDirDerivAt_of_line`: a derivative of `φ : ℝ × E → G` in the
  direction `(1, 0)` is the derivative of the curve `t ↦ φ(t, y)`.
* `contDiffMBOn_pi`, `ContDiffMBOn.const_smul`, `ContDiffMBOn.sub`, `ContDiffMBOn.smul_fun`,
  `ContDiffMBOn.prodMap`, `SmoothMBOn.prodMap`: `C^k` maps are stable under these operations.
* `ContDiffMBOn.codRestrict`, `contDiffMBOn_of_isClosedEmbedding`: a `C^k` map with values in a
  closed subspace is `C^k` into the subspace.
* `dMB_eq_add_of_eqOn`, `dMB_eq_smul_of_eqOn`, `dMB_eq_zero_of_eqOn`,
  `dMB_eq_comp_of_eventuallyEq`, `dMB_comp_affine`: the differential only depends on the map near
  the point; the chain rule along affine maps.
* `SmoothMBOn.dMB_dir`: directional derivatives of a smooth map in a fixed direction are smooth.
* `dMB_eq_fderiv`, `dMB_dMB_eq_fderiv_fderiv`: on normed spaces, the first and second
  Michal–Bastiani differentials of `C¹` and `C²` maps are the Fréchet derivatives.
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

/-! ### Directional derivatives -/

section DirDeriv

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- Directional derivatives of maps into a product are taken componentwise. -/
theorem hasDirDerivAt_pi {ι : Type*} {f : E → ι → F} {x h : E} {y : ι → F} :
    HasDirDerivAt f x h y ↔ ∀ k, HasDirDerivAt (fun z ↦ f z k) x h (y k) := by
  simp only [HasDirDerivAt, tendsto_pi_nhds]
  rfl

/-- Directional derivatives of finite sums. -/
theorem HasDirDerivAt.sum [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] {ι : Type*}
    (s : Finset ι) {g : ι → E → F} {x h : E} {y : ι → F}
    (hg : ∀ i ∈ s, HasDirDerivAt (g i) x h (y i)) :
    HasDirDerivAt (fun z ↦ ∑ i ∈ s, g i z) x h (∑ i ∈ s, y i) :=
  (tendsto_finsetSum s hg).congr fun t ↦ by
    simp only [← Finset.sum_sub_distrib, Finset.smul_sum]

/-- The derivative of an operator-valued map, evaluated at a vector. -/
theorem HasDirDerivAt.clm_apply {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {Φ : E → F₁ →L[ℝ] F₂} {y a : E}
    {D : F₁ →L[ℝ] F₂} (h : HasDirDerivAt Φ y a D) (ξ : F₁) :
    HasDirDerivAt (fun z ↦ Φ z ξ) y a (D ξ) :=
  h.clm_comp_real (ContinuousLinearMap.apply ℝ F₂ ξ)

/-- The product rule for a real function times a vector-valued function. -/
theorem HasDirDerivAt.smul_fun [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {g : E → ℝ} {Y : E → F} {y v : E} {a : ℝ} {b : F}
    (hg : HasDirDerivAt g y v a) (hgc : ContinuousAt g y) (hY : HasDirDerivAt Y y v b) :
    HasDirDerivAt (fun z ↦ g z • Y z) y v (a • Y y + g y • b) := by
  have hl : Tendsto (fun t : ℝ ↦ y + t • v) (𝓝[≠] 0) (𝓝 y) := by
    have : Continuous fun t : ℝ ↦ y + t • v := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hgl : Tendsto (fun t : ℝ ↦ g (y + t • v)) (𝓝[≠] 0) (𝓝 (g y)) := hgc.tendsto.comp hl
  have h1 := hgl.smul hY
  have h2 := hg.smul_const (Y y)
  refine (h2.add h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  simp only [smul_eq_mul]
  module

/-- The directional derivative of the scalar multiplication `ℝ × F → F`. -/
theorem hasDirDerivAt_smul_pair [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] (r s : ℝ × F) :
    HasDirDerivAt (fun r : ℝ × F ↦ r.1 • r.2) r s (r.1 • s.2 + s.1 • r.2) := by
  have key : ∀ t : ℝ, t ≠ 0 → t⁻¹ • ((r + t • s).1 • (r + t • s).2 - r.1 • r.2) =
      r.1 • s.2 + s.1 • r.2 + t • (s.1 • s.2) := by
    intro t ht
    have : (r + t • s).1 • (r + t • s).2 - r.1 • r.2 =
        t • (r.1 • s.2 + s.1 • r.2 + t • (s.1 • s.2)) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      module
    rw [this, smul_smul, inv_mul_cancel₀ ht, one_smul]
  have hc : Continuous fun t : ℝ ↦ r.1 • s.2 + s.1 • r.2 + t • (s.1 • s.2) := by fun_prop
  have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  simp only [zero_smul, add_zero] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  exact (key t ht).symm

/-- A derivative of `φ : ℝ × E → G` in the direction `(1, 0)` is the derivative of the curve
`t ↦ φ(t, y)`. -/
theorem hasDirDerivAt_line {φ : ℝ × E → F} {a : ℝ} {y : E} {L : F}
    (h : HasDirDerivAt φ (a, y) (1, 0) L) : HasDirDerivAt (fun t : ℝ ↦ φ (t, y)) a 1 L := by
  unfold HasDirDerivAt at h ⊢
  convert h using 2 with s
  simp

/-- The converse of `hasDirDerivAt_line`. -/
theorem hasDirDerivAt_of_line {φ : ℝ × E → F} {a : ℝ} {y : E} {L : F}
    (h : HasDirDerivAt (fun t : ℝ ↦ φ (t, y)) a 1 L) : HasDirDerivAt φ (a, y) (1, 0) L := by
  unfold HasDirDerivAt at h ⊢
  convert h using 2 with s
  simp

/-- Differentials along affine maps: `d(g ∘ (L + c))(x, v) = dg(L x + c, L v)`. -/
theorem dMB_comp_affine {E' : Type*} [AddCommGroup E'] [Module ℝ E'] (g : E' → F)
    (L : E →ₗ[ℝ] E') (c : E') (x v : E) :
    dMB (fun x ↦ g (L x + c)) (x, v) = dMB g (L x + c, L v) := by
  unfold dMB
  congr 1
  funext t
  simp [map_add, map_smul, add_right_comm]

end DirDeriv

/-! ### `C^k` maps -/

section ContDiff

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **`C^k` maps into a product** are the maps whose components are `C^k`. -/
theorem contDiffMBOn_pi {ι : Type*} {Y : ι → Type*} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℝ (Y a)] [∀ a, TopologicalSpace (Y a)] [∀ a, T2Space (Y a)]
    {k : ℕ} {f : E → ∀ a, Y a} {W : Set E} (hW : IsOpen W)
    (h : ∀ a, ContDiffMBOn k (fun x ↦ f x a) W) : ContDiffMBOn k f W := by
  induction k generalizing E with
  | zero => exact continuousOn_pi.2 h
  | succ k ih =>
    have hd : ∀ x ∈ W, ∀ v, HasDirDerivAt f x v (fun a ↦ dMB (fun x ↦ f x a) (x, v)) := by
      intro x hx v
      exact tendsto_pi_nhds.2 fun a ↦ (h a).2.1 x hx v
    have hdeq : ∀ p ∈ W ×ˢ (univ : Set E), dMB f p = fun a ↦ dMB (fun x ↦ f x a) p :=
      fun p hp ↦ (hd p.1 hp.1 p.2).dMB_eq
    refine ⟨continuousOn_pi.2 fun a ↦ (h a).continuousOn, fun x hx v ↦ ?_, ?_⟩
    · rw [hdeq (x, v) ⟨hx, mem_univ v⟩]
      exact hd x hx v
    · refine ContDiffMBOn.congr_of_isOpen (hW.prod isOpen_univ) (fun p hp ↦ (hdeq p hp).symm) ?_
      exact ih (hW.prod isOpen_univ) fun a ↦ (h a).2.2

/-- **`C^k` maps into a closed subspace**: if `ι : X → Y` is a continuous linear topological
embedding with closed range and `ι ∘ h` is `C^k`, then `h` is `C^k`. -/
theorem contDiffMBOn_of_isClosedEmbedding {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [T2Space X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [T2Space Y] (ι : X →L[ℝ] Y) (hι : Topology.IsEmbedding ι) (hcl : IsClosed (range ι)) {k : ℕ}
    {h : E → X} {W : Set E} (hW : IsOpen W) (hh : ContDiffMBOn k (fun x ↦ ι (h x)) W) :
    ContDiffMBOn k h W := by
  induction k generalizing E with
  | zero => exact hι.isInducing.continuousOn_iff.2 hh
  | succ k ih =>
    have hmem : ∀ x ∈ W, ∀ v, dMB (fun x ↦ ι (h x)) (x, v) ∈ range ι := by
      intro x hx v
      refine hcl.mem_of_tendsto (hh.2.1 x hx v) (Eventually.of_forall fun t ↦ ?_)
      exact ⟨t⁻¹ • (h (x + t • v) - h x), by simp⟩
    choose! D hD using hmem
    have hd : ∀ x ∈ W, ∀ v, HasDirDerivAt h x v (D x v) := by
      intro x hx v
      rw [HasDirDerivAt, hι.tendsto_nhds_iff, hD x hx v]
      refine (hh.2.1 x hx v).congr fun t ↦ ?_
      simp
    have hdeq : ∀ p ∈ W ×ˢ (univ : Set E), ι (dMB h p) = dMB (fun x ↦ ι (h x)) p := fun p hp ↦ by
      rw [(hd p.1 hp.1 p.2).dMB_eq]
      exact hD p.1 hp.1 p.2
    refine ⟨hι.isInducing.continuousOn_iff.2 hh.continuousOn, fun x hx v ↦ ?_, ?_⟩
    · rw [(hd x hx v).dMB_eq]
      exact hd x hx v
    · exact ih (hW.prod isOpen_univ) (ContDiffMBOn.congr_of_isOpen (hW.prod isOpen_univ)
        (fun p hp ↦ (hdeq p hp).symm) hh.2.2)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- A `C^k` map with values in a closed subspace `T` is `C^k` as a map into `T`. -/
theorem ContDiffMBOn.codRestrict {T : Submodule ℝ F} (hT : IsClosed (T : Set F)) {k : ℕ}
    {h : E → F} {h' : E → T} {V : Set E} (hV : IsOpen V) (hh : ContDiffMBOn k h V)
    (he : ∀ x ∈ V, (h' x : F) = h x) : ContDiffMBOn k h' V :=
  contDiffMBOn_of_isClosedEmbedding T.subtypeL Topology.IsEmbedding.subtypeVal
    (by rwa [Submodule.coe_subtypeL, Submodule.coe_subtype, Subtype.range_coe]) hV
    (ContDiffMBOn.congr_of_isOpen hV (fun x hx ↦ (he x hx).symm) hh)

/-- Multiples of `C^k` maps are `C^k`. -/
theorem ContDiffMBOn.const_smul {k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (c : ℝ) : ContDiffMBOn k (fun x ↦ c • f x) U :=
  ContDiffMBOn.comp hU isOpen_univ ((c • ContinuousLinearMap.id ℝ F).contDiffMBOn k univ) hf
    (mapsTo_univ _ _)

/-- Differences of `C^k` maps are `C^k`. -/
theorem ContDiffMBOn.sub {k : ℕ} {f g : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) : ContDiffMBOn k (fun x ↦ f x - g x) U :=
  ContDiffMBOn.congr_of_isOpen hU (fun _ _ ↦ by simp)
    (ContDiffMBOn.comp (F₁ := F × F) hU isOpen_univ
      ((ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ)
      (hf.prodMk hU hg) (mapsTo_univ _ _))

/-- The scalar multiplication `ℝ × F → F` is smooth. -/
theorem contDiffMBOn_smul_pair (k : ℕ) : ContDiffMBOn k (fun r : ℝ × F ↦ r.1 • r.2) univ := by
  induction k with
  | zero => exact continuous_smul.continuousOn
  | succ k ih =>
    have heq : dMB (fun r : ℝ × F ↦ r.1 • r.2) = fun q ↦ q.1.1 • q.2.2 + q.2.1 • q.1.2 :=
      funext fun q ↦ (hasDirDerivAt_smul_pair q.1 q.2).dMB_eq
    refine ⟨continuous_smul.continuousOn, fun r _ s ↦ ?_, ?_⟩
    · rw [heq]; exact hasDirDerivAt_smul_pair r s
    · rw [heq, univ_prod_univ]
      let L₁ : (ℝ × F) × (ℝ × F) →L[ℝ] ℝ × F :=
        ((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.fst ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ ℝ F).comp (ContinuousLinearMap.snd ℝ _ _))
      let L₂ : (ℝ × F) × (ℝ × F) →L[ℝ] ℝ × F :=
        ((ContinuousLinearMap.fst ℝ ℝ F).comp (ContinuousLinearMap.snd ℝ _ _)).prod
          ((ContinuousLinearMap.snd ℝ ℝ F).comp (ContinuousLinearMap.fst ℝ _ _))
      have h₁ := ContDiffMBOn.comp_clm L₁ isOpen_univ ih
      have h₂ := ContDiffMBOn.comp_clm L₂ isOpen_univ ih
      rw [preimage_univ] at h₁ h₂
      exact h₁.add isOpen_univ h₂

/-- The product rule for a real function times a vector-valued function. -/
theorem ContDiffMBOn.smul_fun {k : ℕ} {f : E → ℝ} {g : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) : ContDiffMBOn k (fun x ↦ f x • g x) U :=
  ContDiffMBOn.comp (g := fun r : ℝ × F ↦ r.1 • r.2) hU isOpen_univ (contDiffMBOn_smul_pair k)
    (hf.prodMk hU hg) (mapsTo_univ _ _)

/-- Products of `C^k` maps are `C^k`. -/
theorem ContDiffMBOn.prodMap {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
    {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F'] [IsTopologicalAddGroup F']
    [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F'] {k : ℕ} {g : E → F}
    {h : E' → F'} {U : Set E} {V : Set E'} (hU : IsOpen U) (hV : IsOpen V)
    (hg : ContDiffMBOn k g U) (hh : ContDiffMBOn k h V) :
    ContDiffMBOn k (fun p : E × E' ↦ (g p.1, h p.2)) (U ×ˢ V) := by
  have hUV : IsOpen (U ×ˢ V) := hU.prod hV
  have h1 : ContDiffMBOn k (g ∘ ContinuousLinearMap.fst ℝ E E') (U ×ˢ V) :=
    hg.comp hUV hU ((ContinuousLinearMap.fst ℝ E E').contDiffMBOn k _) fun p hp ↦ hp.1
  have h2 : ContDiffMBOn k (h ∘ ContinuousLinearMap.snd ℝ E E') (U ×ˢ V) :=
    hh.comp hUV hV ((ContinuousLinearMap.snd ℝ E E').contDiffMBOn k _) fun p hp ↦ hp.2
  exact h1.prodMk hUV h2

/-- Products of smooth maps are smooth. -/
theorem SmoothMBOn.prodMap {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
    {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F'] [IsTopologicalAddGroup F']
    [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F'] {g : E → F} {h : E' → F'}
    {U : Set E} {V : Set E'} (hU : IsOpen U) (hV : IsOpen V) (hg : SmoothMBOn g U)
    (hh : SmoothMBOn h V) : SmoothMBOn (fun p : E × E' ↦ (g p.1, h p.2)) (U ×ˢ V) := fun k ↦
  (hg k).prodMap hU hV (hh k)

/-- Directional derivatives of a smooth map in a fixed direction are smooth. -/
theorem SmoothMBOn.dMB_dir {G : E → F} {U : Set E} (hU : IsOpen U) (hG : SmoothMBOn G U)
    (d : E) : SmoothMBOn (fun z ↦ dMB G (z, d)) U := fun n ↦
  ((hG (n + 1)).2.2).comp (F₁ := E × E) hU (hU.prod isOpen_univ)
    (ContDiffMBOn.prodMk hU (smoothMBOn_id U n) (contDiffMBOn_const n d U))
    fun _ hz ↦ ⟨hz, mem_univ _⟩

/-! ### Locality of the differential -/

variable {g g₁ g₂ : E → F} {U : Set E} {y : E}

omit [LocallyConvexSpace ℝ E] [T2Space E] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- The differential of a map that agrees with a sum near the point. -/
theorem dMB_eq_add_of_eqOn (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffMBOn 1 g₁ U)
    (h₂ : ContDiffMBOn 1 g₂ U) (hg : EqOn g (fun z ↦ g₁ z + g₂ z) U) (u : E) :
    dMB g (y, u) = dMB g₁ (y, u) + dMB g₂ (y, u) :=
  (((h₁.2.1 y hy u).add (h₂.2.1 y hy u)).congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- The differential of a map that agrees with a multiple near the point. -/
theorem dMB_eq_smul_of_eqOn (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffMBOn 1 g₁ U) (c : ℝ)
    (hg : EqOn g (fun z ↦ c • g₁ z) U) (u : E) : dMB g (y, u) = c • dMB g₁ (y, u) :=
  (((h₁.2.1 y hy u).const_smul c).congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- The differential of a map that vanishes near the point. -/
theorem dMB_eq_zero_of_eqOn (hU : IsOpen U) (hy : y ∈ U) (hg : EqOn g 0 U) (u : E) :
    dMB g (y, u) = 0 := by
  have h0 : HasDirDerivAt (fun _ : E ↦ (0 : F)) y u 0 := by
    simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds
  exact (h0.congr_of_eventuallyEq
    (eventuallyEq_of_mem (hU.mem_nhds hy) fun _ hz ↦ (hg hz).symm)).dMB_eq

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The chain rule for a map that agrees with a composition near the point. -/
theorem dMB_eq_comp_of_eventuallyEq {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
    {g₀ : E → F} {g₁ : F → G} {h : E → G} {U : Set E} {V : Set F} (hV : IsOpen V)
    (hg₁ : ContDiffMBOn 1 g₁ V) (hg₀ : ContDiffMBOn 1 g₀ U) (hUV : MapsTo g₀ U V) {y : E}
    (hy : y ∈ U) (hh : h =ᶠ[𝓝 y] g₁ ∘ g₀) (v : E) :
    dMB h (y, v) = dMB g₁ (g₀ y, dMB g₀ (y, v)) := by
  rw [dMB_congr_of_eventuallyEq hh]
  exact ContDiffMBOn.dMB_comp hV hg₁ hg₀ hUV hy v

end ContDiff

/-! ### Comparison with Fréchet derivatives -/

section Normed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a normed space, the Michal–Bastiani differential of a `C¹` map is its Fréchet derivative. -/
theorem dMB_eq_fderiv {f : E → F} {T : Set E} (hT : IsOpen T) (hf : ContDiffOn ℝ 1 f T) {y : E}
    (hy : y ∈ T) (a : E) : dMB f (y, a) = fderiv ℝ f y a := by
  have hd : HasFDerivAt f (fderiv ℝ f y) y :=
    ((hf.contDiffAt (hT.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
  exact (hd.hasDirDerivAt a).dMB_eq

/-- On a normed space, the second Michal–Bastiani differential of a `C²` map is its second
Fréchet derivative: `dMB (dMB f) ((y, b), (a, 0)) = D²f(y)(a)(b)`. -/
theorem dMB_dMB_eq_fderiv_fderiv {f : E → F} {T : Set E} (hT : IsOpen T)
    (hf : ContDiffOn ℝ 2 f T) {y : E} (hy : y ∈ T) (a b : E) :
    dMB (dMB f) ((y, b), (a, 0)) = fderiv ℝ (fderiv ℝ f) y a b := by
  have hev : dMB f =ᶠ[𝓝 (y, b)] fun p : E × E ↦ fderiv ℝ f p.1 p.2 := by
    have hTE : T ×ˢ (univ : Set E) ∈ 𝓝 (y, b) := (hT.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩
    filter_upwards [hTE] with p hp
    exact dMB_eq_fderiv hT (hf.of_le (by norm_num)) hp.1 p.2
  rw [dMB_congr_of_eventuallyEq hev]
  have hfy : ContDiffAt ℝ 2 f y := hf.contDiffAt (hT.mem_nhds hy)
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
    ((hfy.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hfst : HasFDerivAt (fun p : E × E ↦ fderiv ℝ f p.1)
      ((fderiv ℝ (fderiv ℝ f) y).comp (ContinuousLinearMap.fst ℝ E E)) (y, b) :=
    hD.comp (y, b) hasFDerivAt_fst
  have happ := hfst.clm_apply (hasFDerivAt_snd (p := (y, b)))
  rw [(happ.hasDirDerivAt (a, 0)).dMB_eq]
  simp

end Normed

end LocallyConvex.Analysis

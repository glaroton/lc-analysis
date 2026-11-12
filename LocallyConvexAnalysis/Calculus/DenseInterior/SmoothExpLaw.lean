/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.DenseInterior.CklInfty

/-!
# The exponential law for `C^{∞,∞}` maps on sets with dense interior

Reference: [GN26, Definition 1.7.10 and Theorem 1.7.30] (pp. 90, 102), for `k = ℓ = ∞`.

## Main declarations

* `SmoothLCMap F V hV`: the space `C^∞(V, F)` of smooth maps on a set `V` with dense interior,
  with the compact-open `C^∞` topology, the initial topology with respect to the inclusions
  `C^∞(V, F) → C^j(V, F)` (equivalently, to all differentials `d^(j)`,
  `SmoothLCMap.continuous_iff'`).
* `SmoothLCMap.contDiffLC_iff`: a map into `C^∞(V, F)` is `C^k` if and only if its compositions
  with the inclusions into `C^j(V, F)` are.
* `SmoothLCMap₂ F U hU V hV`: the space `C^{∞,∞}(U × V, F)`.
* `SmoothLCMap₂.curry`, `SmoothLCMap₂.isEmbedding_curry`: `Φ : f ↦ f^∨` is a linear topological
  embedding `C^{∞,∞}(U × V, F) → C^∞(U, C^∞(V, F))`;
* `SmoothLCMap₂.curryEquivOf`: under the hypotheses (a) or (b) of Theorem 1.7.30 for all finite
  orders (`ExpLawEval`), `Φ` is an isomorphism of topological vector spaces.

## Implementation notes

`C^∞(V, F)` is identified with the closed subspace of compatible families in `∏ⱼ C^j(V, F)`.
This reduces `C^k` maps into `C^∞(V, F)` to `C^k` maps into the factors (`ContDiffLC.pi`,
`contDiffLC_subtype_iff`), and the topology of `C(Z, C^∞(V, F))` to that of the `C(Z, C^j(V, F))`
(`continuous_continuousMap_of_isInducing`, by uniform convergence on compact sets). The law for
`k = ℓ = ∞` then follows from the laws for finite orders (`Calculus/DenseInterior/ExpLaw.lean`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology Uniformity

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### Continuous maps into products -/

section ContinuousMapPi

/-- A map into `C(Z, ∏ⱼ Yⱼ)` is continuous if and only if its components into the `C(Z, Yⱼ)` are
(compact-open topologies; the `Yⱼ` are uniform spaces). -/
theorem continuous_continuousMap_pi_iff {W Z : Type*} [TopologicalSpace W] [TopologicalSpace Z]
    {ι : Type*} {Y : ι → Type*} [∀ j, UniformSpace (Y j)] {Φ : W → C(Z, ∀ j, Y j)} :
    Continuous Φ ↔ ∀ j, Continuous fun w ↦ (ContinuousMap.eval j).comp (Φ w) := by
  refine ⟨fun h j ↦ (ContinuousMap.continuous_postcomp _).comp h, fun h ↦ ?_⟩
  refine continuous_iff_continuousAt.2 fun w ↦ ?_
  rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  have hj := fun j ↦ (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
    ((h j).continuousAt (x := w))) K hK
  simp only [tendstoUniformlyOn_iff_tendsto] at hj ⊢
  rw [Pi.uniformity, tendsto_iInf]
  intro j
  rw [tendsto_comap_iff]
  exact hj j

/-- If the topology of `X` is induced by `T : X → ∏ⱼ Yⱼ`, a map into `C(Z, X)` is continuous if
and only if its compositions with the components of `T` are. -/
theorem continuous_continuousMap_of_isInducing {W Z X : Type*} [TopologicalSpace W]
    [TopologicalSpace Z] [TopologicalSpace X] {ι : Type*} {Y : ι → Type*}
    [∀ j, UniformSpace (Y j)] {T : X → ∀ j, Y j} (hT : Topology.IsInducing T)
    {Φ : W → C(Z, X)} :
    Continuous Φ ↔ ∀ j, Continuous fun w ↦ (ContinuousMap.eval j).comp
      ((⟨T, hT.continuous⟩ : C(X, ∀ j, Y j)).comp (Φ w)) := by
  rw [(ContinuousMap.isInducing_postcomp (X := Z) ⟨T, hT.continuous⟩ hT).continuous_iff,
    continuous_continuousMap_pi_iff]
  rfl

end ContinuousMapPi

/-! ### `C^k` maps into products -/

section Pi

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {ι : Type w} {Fi : ι → Type v} [∀ a, AddCommGroup (Fi a)] [∀ a, Module ℝ (Fi a)]
  [∀ a, TopologicalSpace (Fi a)] [∀ a, IsTopologicalAddGroup (Fi a)]
  [∀ a, ContinuousSMul ℝ (Fi a)] [∀ a, LocallyConvexSpace ℝ (Fi a)] [∀ a, T2Space (Fi a)]

omit [∀ (a : ι), IsTopologicalAddGroup (Fi a)] [∀ (a : ι), ContinuousSMul ℝ (Fi a)]
  [∀ (a : ι), LocallyConvexSpace ℝ (Fi a)] in
/-- **`C^k` maps into products** ([GN26, Lemma 1.4.6], for arbitrary products): a family of
`C^k` maps defines a `C^k` map into the product. -/
theorem ContDiffLC.pi {k : ℕ} {f : ∀ a, E → Fi a} {U : Set E} (hU : HasDenseInterior U)
    (hf : ∀ a, ContDiffLC k (f a) U) : ContDiffLC k (fun x a ↦ f a x) U := by
  induction k generalizing E f U with
  | zero => exact continuousOn_pi.2 hf
  | succ k ih =>
    have hD : ∀ x ∈ interior U, ∀ h, HasDirDerivAt (fun z a ↦ f a z) x h
        (fun a ↦ dLC (f a) U (x, h)) := fun x hx h ↦ HasDirDerivAt.pi fun a ↦ by
      have : dLC (f a) U (x, h) = dMB (f a) (x, h) := by simp [dLC, hx]
      rw [this]
      exact (hf a).hasDirDerivAt hx h
    exact (ContDiffLC.of_hasDirDerivAt hU (continuousOn_pi.2 fun a ↦ (hf a).continuousOn) hD
      (ih hU.prod_univ fun a ↦ (hf a).contDiffLC_dLC)).1

/-- `C^k` maps into products are the families of `C^k` maps. -/
theorem contDiffLC_pi_iff {k : ℕ} {f : ∀ a, E → Fi a} {U : Set E} (hU : HasDenseInterior U) :
    ContDiffLC k (fun x a ↦ f a x) U ↔ ∀ a, ContDiffLC k (f a) U :=
  ⟨fun h a ↦ h.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := Fi) a) hU, ContDiffLC.pi hU⟩

end Pi

/-! ### The space `C^∞(V, F)` -/

section SmoothSpace

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- Evaluation at a point is continuous on `C^k(V, F)`. -/
theorem ContDiffLCMap.continuous_apply {k : ℕ} {V : Set E} {hV : HasDenseInterior V} (x : E) :
    Continuous fun γ : ContDiffLCMap F k V hV ↦ γ x := by
  by_cases hx : x ∈ V
  · exact (continuous_eval_const ((⟨x, hx⟩ : V), (Fin.elim0 : Fin 0 → E))).comp
      (ContDiffLCMap.continuous_iteratedD 0 (Nat.zero_le k))
  · simp_rw [fun γ : ContDiffLCMap F k V hV ↦ γ.apply_of_notMem hx]
    exact continuous_const

variable (F) in
/-- The smooth maps on a set `V` with dense interior, extended by `0` outside `V`. -/
def smoothLCSubmodule (V : Set E) (hV : HasDenseInterior V) : Submodule ℝ (E → F) where
  carrier := {f | SmoothLC f V ∧ ∀ x ∉ V, f x = 0}
  add_mem' {f g} hf hg :=
    ⟨fun k ↦ (hf.1 k).add hV (hg.1 k), fun x hx ↦ by simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨fun k ↦ contDiffLC_const k (0 : F) hV, fun _ _ ↦ rfl⟩
  smul_mem' c f hf := ⟨fun k ↦ (hf.1 k).const_smul hV c, fun x hx ↦ by simp [hf.2 x hx]⟩

variable (F) in
/-- **The space `C^∞(V, F)`** of smooth maps on a set `V` with dense interior
([GN26, Definition 1.7.10]), extended by `0` outside `V`. -/
def SmoothLCMap (V : Set E) (hV : HasDenseInterior V) : Type (max u v) :=
  smoothLCSubmodule F V hV

namespace SmoothLCMap

variable {V : Set E} {hV : HasDenseInterior V}

instance : AddCommGroup (SmoothLCMap F V hV) :=
  inferInstanceAs (AddCommGroup (smoothLCSubmodule F V hV))

instance : Module ℝ (SmoothLCMap F V hV) :=
  inferInstanceAs (Module ℝ (smoothLCSubmodule F V hV))

instance : FunLike (SmoothLCMap F V hV) E F where
  coe γ := Subtype.val (γ : smoothLCSubmodule F V hV)
  coe_injective := Subtype.val_injective

/-- The element of `C^∞(V, F)` given by a map that is smooth on `V` and vanishes outside `V`. -/
def mk (f : E → F) (hf : SmoothLC f V) (h0 : ∀ x ∉ V, f x = 0) : SmoothLCMap F V hV :=
  ⟨f, hf, h0⟩

@[simp]
theorem coe_mk (f : E → F) (hf : SmoothLC f V) (h0 : ∀ x ∉ V, f x = 0) :
    ⇑(mk (hV := hV) f hf h0) = f :=
  rfl

theorem smoothLC (γ : SmoothLCMap F V hV) : SmoothLC γ V :=
  (γ : smoothLCSubmodule F V hV).2.1

theorem apply_of_notMem (γ : SmoothLCMap F V hV) {x : E} (hx : x ∉ V) : γ x = 0 :=
  (γ : smoothLCSubmodule F V hV).2.2 x hx

@[ext]
theorem ext {γ η : SmoothLCMap F V hV} (h : ∀ x, γ x = η x) : γ = η :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_zero : ⇑(0 : SmoothLCMap F V hV) = 0 :=
  rfl

@[simp]
theorem coe_add (γ η : SmoothLCMap F V hV) : ⇑(γ + η) = γ + η :=
  rfl

@[simp]
theorem coe_smul (c : ℝ) (γ : SmoothLCMap F V hV) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The inclusion `C^∞(V, F) → C^j(V, F)`. -/
def toContDiff (j : ℕ) : SmoothLCMap F V hV →ₗ[ℝ] ContDiffLCMap F j V hV where
  toFun γ := ContDiffLCMap.mk γ (γ.smoothLC j) fun _ hx ↦ γ.apply_of_notMem hx
  map_add' _ _ := ContDiffLCMap.ext fun _ ↦ rfl
  map_smul' _ _ := ContDiffLCMap.ext fun _ ↦ rfl

@[simp]
theorem toContDiff_apply (j : ℕ) (γ : SmoothLCMap F V hV) (x : E) : toContDiff j γ x = γ x :=
  rfl

/-- `γ ↦ (γ)_{j ∈ ℕ} ∈ ∏ⱼ C^j(V, F)`. -/
def toPi : SmoothLCMap F V hV →ₗ[ℝ] ∀ j : ℕ, ContDiffLCMap F j V hV :=
  LinearMap.pi toContDiff

@[simp]
theorem toPi_apply (γ : SmoothLCMap F V hV) (j : ℕ) : toPi γ j = toContDiff j γ :=
  rfl

theorem toPi_injective : Function.Injective (toPi (F := F) (hV := hV)) :=
  fun _ _ h ↦ ext fun x ↦ congrArg (fun φ ↦ φ 0 x) h

/-- **The compact-open `C^∞` topology** on `C^∞(V, F)` ([GN26, Definition 1.7.10]): the
initial topology with respect to the inclusions into the `C^j(V, F)`, `j ∈ ℕ`. -/
instance : TopologicalSpace (SmoothLCMap F V hV) :=
  .induced toPi inferInstance

theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (F := F) (hV := hV)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

instance : IsTopologicalAddGroup (SmoothLCMap F V hV) :=
  isTopologicalAddGroup_induced toPi

instance : ContinuousSMul ℝ (SmoothLCMap F V hV) :=
  continuousSMul_induced toPi

instance : LocallyConvexSpace ℝ (SmoothLCMap F V hV) :=
  LocallyConvexSpace.induced toPi

instance : T2Space (SmoothLCMap F V hV) :=
  isEmbedding_toPi.t2Space

theorem continuous_toPi : Continuous (toPi (F := F) (hV := hV)) :=
  continuous_induced_dom

theorem continuous_toContDiff (j : ℕ) : Continuous (toContDiff (F := F) (hV := hV) j) :=
  (_root_.continuous_apply j).comp continuous_toPi

/-- The inclusion `C^∞(V, F) → C^j(V, F)` as a continuous linear map. -/
def toContDiffCLM (j : ℕ) : SmoothLCMap F V hV →L[ℝ] ContDiffLCMap F j V hV :=
  ⟨toContDiff j, continuous_toContDiff j⟩

@[simp]
theorem toContDiffCLM_apply (j : ℕ) (γ : SmoothLCMap F V hV) :
    toContDiffCLM j γ = toContDiff j γ :=
  rfl

/-- A map into `C^∞(V, F)` is continuous if and only if its compositions with the inclusions into
the `C^j(V, F)` are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → SmoothLCMap F V hV} :
    Continuous φ ↔ ∀ j, Continuous fun x ↦ toContDiff j (φ x) :=
  ⟨fun h j ↦ (continuous_toContDiff j).comp h,
    fun h ↦ continuous_induced_rng.2 (continuous_pi h)⟩

/-- **[GN26, Definition 1.7.10]** for `k = ∞`: a map into `C^∞(V, F)` is continuous if and
only if its compositions with all the differentials `d^(j) : C^∞(V, F) → C(V × E^j, F)` are. -/
theorem continuous_iff' {X : Type*} [TopologicalSpace X] {φ : X → SmoothLCMap F V hV} :
    Continuous φ ↔
      ∀ j, Continuous fun x ↦ ContDiffLCMap.iteratedD j le_rfl (toContDiff j (φ x)) := by
  refine ⟨fun h j ↦ (ContDiffLCMap.continuous_iteratedD j le_rfl).comp
    ((continuous_toContDiff j).comp h), fun h ↦ continuous_iff.2 fun j ↦ ?_⟩
  refine ContDiffLCMap.continuous_iff.2 fun i hi ↦ (h i).congr fun x ↦ ?_
  rfl

/-- The range of `C^∞(V, F)` in `∏ⱼ C^j(V, F)`: the compatible families. -/
theorem range_toPi :
    (LinearMap.range (toPi (F := F) (hV := hV)) : Set (∀ j : ℕ, ContDiffLCMap F j V hV)) =
      {φ | ∀ j x, φ j x = φ 0 x} := by
  ext φ
  constructor
  · rintro ⟨γ, rfl⟩ j x
    rfl
  · intro hφ
    have hf : SmoothLC (φ 0) V := fun j ↦
      (φ j).contDiffLC.congr fun x _ ↦ hφ j x
    refine ⟨mk (φ 0) hf fun x hx ↦ (φ 0).apply_of_notMem hx, ?_⟩
    funext j
    exact ContDiffLCMap.ext fun x ↦ (hφ j x).symm

/-- The compatible families form a closed subspace of `∏ⱼ C^j(V, F)`. -/
theorem isClosed_range_toPi :
    IsClosed (LinearMap.range (toPi (F := F) (hV := hV)) :
      Set (∀ j : ℕ, ContDiffLCMap F j V hV)) := by
  rw [range_toPi]
  simp only [ofPred_forall]
  exact isClosed_iInter fun j ↦ isClosed_iInter fun x ↦ isClosed_eq
    ((ContDiffLCMap.continuous_apply x).comp (_root_.continuous_apply j))
    ((ContDiffLCMap.continuous_apply x).comp (_root_.continuous_apply 0))

/-- `C^∞(V, F)` is linearly homeomorphic to the subspace of compatible families. -/
def equivRange : SmoothLCMap F V hV ≃L[ℝ] LinearMap.range (toPi (F := F) (hV := hV)) where
  toLinearEquiv := LinearEquiv.ofInjective toPi toPi_injective
  continuous_toFun := continuous_toPi.subtype_mk _
  continuous_invFun := by
    rw [isEmbedding_toPi.continuous_iff]
    refine continuous_subtype_val.congr fun s ↦ ?_
    exact (LinearEquiv.ofInjective_symm_apply toPi (h := toPi_injective) s).symm

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]

/-- **`C^k` maps into `C^∞(V, F)`**: a map into `C^∞(V, F)` is `C^k` on `U` if and only if its
compositions with the inclusions into the `C^j(V, F)` are. -/
theorem contDiffLC_iff {U : Set E₁} (hUc : IsLocallyConvexSubset U) (hU : HasDenseInterior U)
    {k : ℕ} {g : E₁ → SmoothLCMap F V hV} :
    ContDiffLC k g U ↔ ∀ j, ContDiffLC k (fun x ↦ toContDiff j (g x)) U := by
  refine ⟨fun h j ↦ h.clm_comp (toContDiffCLM j) hU, fun h ↦ ?_⟩
  set S := LinearMap.range (toPi (F := F) (hV := hV))
  let g' : E₁ → S := fun x ↦ equivRange (g x)
  have h' : ContDiffLC k g' U := by
    rw [contDiffLC_subtype_iff isClosed_range_toPi.isSeqClosed hUc hU]
    exact ContDiffLC.pi hU h
  exact (h'.clm_comp (equivRange (F := F) (hV := hV)).symm.toContinuousLinearMap hU).congr
    fun x _ ↦ (equivRange (F := F) (hV := hV)).symm_apply_apply (g x)

end SmoothLCMap

end SmoothSpace

/-! ### Postcomposition with continuous linear maps -/

section Postcomp

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {X : Type v} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {Y : Type w} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
  [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y]

/-- `d^(m)(L ∘ γ) = L ∘ d^(m) γ` for a continuous linear map `L`. -/
theorem iteratedDLC_clm_comp {k m : ℕ} {U : Set E} (hU : HasDenseInterior U) {γ : E → X}
    (hγ : ContDiffLC k γ U) (L : X →L[ℝ] Y) (hm : m ≤ k) :
    EqOn (iteratedDLC m (fun z ↦ L (γ z)) U) (fun p ↦ L (iteratedDLC m γ U p)) (U ×ˢ univ) :=
  iteratedDLC_unique hU ((hγ.clm_comp L hU).continuousOn_iteratedDLC hm)
    (L.continuous.comp_continuousOn (hγ.continuousOn_iteratedDLC hm))
    (fun _ hp ↦ iteratedDLC_eq_iteratedDMB hp.1) fun p hp ↦ by
      rw [iteratedDLC_eq_iteratedDMB hp.1]
      exact (iteratedDMB_clm_comp isOpen_interior hγ.contDiffMBOn_interior L m hm p.1 hp.1
        p.2).symm

namespace ContDiffLCMap

variable {k : ℕ} {U : Set E} {hU : HasDenseInterior U}

/-- Postcomposition `γ ↦ L ∘ γ : C^k(U, X) → C^k(U, Y)` with a continuous linear map `L`. -/
def postcomp (L : X →L[ℝ] Y) : ContDiffLCMap X k U hU →ₗ[ℝ] ContDiffLCMap Y k U hU where
  toFun γ := mk (fun z ↦ L (γ z)) (γ.contDiffLC.clm_comp L hU) fun x hx ↦ by
    simp [γ.apply_of_notMem hx]
  map_add' _ _ := ext fun _ ↦ by simp
  map_smul' _ _ := ext fun _ ↦ by simp

@[simp]
theorem postcomp_apply (L : X →L[ℝ] Y) (γ : ContDiffLCMap X k U hU) (x : E) :
    postcomp L γ x = L (γ x) :=
  rfl

theorem iteratedD_postcomp (L : X →L[ℝ] Y) (m : ℕ) (hm : m ≤ k) (γ : ContDiffLCMap X k U hU) :
    iteratedD m hm (postcomp L γ) = (L : C(X, Y)).comp (iteratedD m hm γ) :=
  ContinuousMap.ext fun p ↦ iteratedDLC_clm_comp hU γ.contDiffLC L hm ⟨p.1.2, mem_univ _⟩

theorem continuous_postcomp (L : X →L[ℝ] Y) :
    Continuous (postcomp (k := k) (hU := hU) L) :=
  continuous_iff.2 fun m hm ↦ by
    simp_rw [iteratedD_postcomp]
    exact (ContinuousMap.continuous_postcomp _).comp (continuous_iteratedD m hm)

/-- Postcomposition with `L` as a continuous linear map. -/
def postcompCLM (L : X →L[ℝ] Y) : ContDiffLCMap X k U hU →L[ℝ] ContDiffLCMap Y k U hU :=
  ⟨postcomp L, continuous_postcomp L⟩

end ContDiffLCMap

end Postcomp

/-! ### `C^k` maps with values in `C^∞(V, F)` -/

section Outer

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {U : Set E₁} {hU : HasDenseInterior U} {V : Set E₂} {hV : HasDenseInterior V}

/-- A map into `C^i(U, C^∞(V, F))` is continuous if and only if its compositions with the
postcompositions by the inclusions `C^∞(V, F) → C^j(V, F)` are. -/
theorem SmoothLCMap.continuous_contDiffLCMap_iff {i : ℕ} {W : Type*} [TopologicalSpace W]
    {Φ : W → ContDiffLCMap (SmoothLCMap F V hV) i U hU} :
    Continuous Φ ↔
      ∀ j, Continuous fun w ↦ ContDiffLCMap.postcomp (SmoothLCMap.toContDiffCLM j) (Φ w) := by
  refine ⟨fun h j ↦ (ContDiffLCMap.continuous_postcomp _).comp h, fun h ↦ ?_⟩
  refine ContDiffLCMap.continuous_iff.2 fun m hm ↦ ?_
  let : ∀ j : ℕ, UniformSpace (ContDiffLCMap F j V hV) := fun _ ↦
    IsTopologicalAddGroup.rightUniformSpace _
  refine (continuous_continuousMap_of_isInducing
    (SmoothLCMap.isEmbedding_toPi (F := F) (hV := hV)).isInducing).2 fun j ↦ ?_
  refine ((ContDiffLCMap.continuous_iteratedD m hm).comp (h j)).congr fun w ↦ ?_
  rw [Function.comp_apply, ContDiffLCMap.iteratedD_postcomp]
  rfl

end Outer

/-! ### The space `C^{∞,∞}(U × V, F)` and the exponential law -/

section SmoothExpLaw

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (F) in
/-- The `C^{∞,∞}` maps on `U × V`, extended by `0` outside `U × V`. -/
def smoothLCSubmodule₂ (U : Set E₁) (hU : HasDenseInterior U) (V : Set E₂)
    (hV : HasDenseInterior V) : Submodule ℝ (E₁ × E₂ → F) where
  carrier := {f | ContDiffLC₂UpTo ⊤ ⊤ f U V ∧ ∀ p ∉ U ×ˢ V, f p = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add hU hV hg.1, fun p hp ↦ by simp [hf.2 p hp, hg.2 p hp]⟩
  zero_mem' := ⟨contDiffLC₂UpTo_const hU hV 0, fun _ _ ↦ rfl⟩
  smul_mem' c f hf := ⟨hf.1.const_smul hU hV c, fun p hp ↦ by simp [hf.2 p hp]⟩

variable (F) in
/-- **The space `C^{∞,∞}(U × V, F)`** ([GN26, Definition 1.7.17] for `k = ℓ = ∞`), with
the initial topology with respect to the inclusions into the `C^{k,ℓ}(U × V, F)`. -/
def SmoothLCMap₂ (U : Set E₁) (hU : HasDenseInterior U) (V : Set E₂) (hV : HasDenseInterior V) :
    Type (max u v) :=
  smoothLCSubmodule₂ F U hU V hV

namespace SmoothLCMap₂

variable {U : Set E₁} {hU : HasDenseInterior U} {V : Set E₂} {hV : HasDenseInterior V}

instance : AddCommGroup (SmoothLCMap₂ F U hU V hV) :=
  inferInstanceAs (AddCommGroup (smoothLCSubmodule₂ F U hU V hV))

instance : Module ℝ (SmoothLCMap₂ F U hU V hV) :=
  inferInstanceAs (Module ℝ (smoothLCSubmodule₂ F U hU V hV))

instance : FunLike (SmoothLCMap₂ F U hU V hV) (E₁ × E₂) F where
  coe γ := Subtype.val (γ : smoothLCSubmodule₂ F U hU V hV)
  coe_injective := Subtype.val_injective

/-- The element of `C^{∞,∞}(U × V, F)` given by a `C^{∞,∞}` map vanishing outside `U × V`. -/
def mk (f : E₁ × E₂ → F) (hf : ContDiffLC₂UpTo ⊤ ⊤ f U V) (h0 : ∀ p ∉ U ×ˢ V, f p = 0) :
    SmoothLCMap₂ F U hU V hV :=
  ⟨f, hf, h0⟩

@[simp]
theorem coe_mk (f : E₁ × E₂ → F) (hf : ContDiffLC₂UpTo ⊤ ⊤ f U V) (h0 : ∀ p ∉ U ×ˢ V, f p = 0) :
    ⇑(mk (hU := hU) (hV := hV) f hf h0) = f :=
  rfl

theorem contDiffLC₂UpTo (γ : SmoothLCMap₂ F U hU V hV) : ContDiffLC₂UpTo ⊤ ⊤ γ U V :=
  (γ : smoothLCSubmodule₂ F U hU V hV).2.1

theorem apply_of_notMem (γ : SmoothLCMap₂ F U hU V hV) {p : E₁ × E₂} (hp : p ∉ U ×ˢ V) :
    γ p = 0 :=
  (γ : smoothLCSubmodule₂ F U hU V hV).2.2 p hp

@[ext]
theorem ext {γ η : SmoothLCMap₂ F U hU V hV} (h : ∀ p, γ p = η p) : γ = η :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_add (γ η : SmoothLCMap₂ F U hU V hV) : ⇑(γ + η) = γ + η :=
  rfl

@[simp]
theorem coe_smul (c : ℝ) (γ : SmoothLCMap₂ F U hU V hV) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The inclusion `C^{∞,∞}(U × V, F) → C^{k,ℓ}(U × V, F)`. -/
def toContDiff₂ (k ℓ : ℕ) : SmoothLCMap₂ F U hU V hV →ₗ[ℝ] ContDiffLCMap₂ F k ℓ U hU V hV where
  toFun γ := ContDiffLCMap₂.mk γ (γ.contDiffLC₂UpTo k ℓ le_top le_top)
    fun _ hp ↦ γ.apply_of_notMem hp
  map_add' _ _ := ContDiffLCMap₂.ext fun _ ↦ rfl
  map_smul' _ _ := ContDiffLCMap₂.ext fun _ ↦ rfl

@[simp]
theorem toContDiff₂_apply (k ℓ : ℕ) (γ : SmoothLCMap₂ F U hU V hV) (p : E₁ × E₂) :
    toContDiff₂ k ℓ γ p = γ p :=
  rfl

/-- `γ ↦ (γ)_{(k, ℓ) ∈ ℕ²}`. -/
def toPi : SmoothLCMap₂ F U hU V hV →ₗ[ℝ] ∀ q : ℕ × ℕ, ContDiffLCMap₂ F q.1 q.2 U hU V hV :=
  LinearMap.pi fun q ↦ toContDiff₂ q.1 q.2

theorem toPi_injective : Function.Injective (toPi (F := F) (hU := hU) (hV := hV)) :=
  fun _ _ h ↦ ext fun p ↦ congrArg (fun φ ↦ φ (0, 0) p) h

/-- The compact-open `C^{∞,∞}` topology: the initial topology with respect to the inclusions into
the `C^{k,ℓ}(U × V, F)`. -/
instance : TopologicalSpace (SmoothLCMap₂ F U hU V hV) :=
  .induced toPi inferInstance

theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (F := F) (hU := hU) (hV := hV)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

instance : IsTopologicalAddGroup (SmoothLCMap₂ F U hU V hV) :=
  isTopologicalAddGroup_induced toPi

instance : ContinuousSMul ℝ (SmoothLCMap₂ F U hU V hV) :=
  continuousSMul_induced toPi

instance : LocallyConvexSpace ℝ (SmoothLCMap₂ F U hU V hV) :=
  LocallyConvexSpace.induced toPi

instance : T2Space (SmoothLCMap₂ F U hU V hV) :=
  isEmbedding_toPi.t2Space

theorem continuous_toContDiff₂ (k ℓ : ℕ) :
    Continuous (toContDiff₂ (F := F) (hU := hU) (hV := hV) k ℓ) := by
  have h : Continuous (toPi (F := F) (hU := hU) (hV := hV)) := continuous_induced_dom
  exact (_root_.continuous_apply ((k, ℓ) : ℕ × ℕ)).comp h

open Classical in
/-- The partial maps `f(x, ·) ∈ C^∞(V, F)` (and `0` for `x ∉ U`). -/
def curryFun (f : SmoothLCMap₂ F U hU V hV) (x : E₁) : SmoothLCMap F V hV :=
  if hx : x ∈ U then
    SmoothLCMap.mk (fun y ↦ if y ∈ V then f (x, y) else 0)
      (fun j ↦ (f.contDiffLC₂UpTo.contDiffLC_right hU hV hx j le_top).congr fun y hy ↦ by
        simp [hy])
      fun y hy ↦ by simp [hy]
  else 0

theorem curryFun_apply (f : SmoothLCMap₂ F U hU V hV) (x : E₁) (y : E₂) :
    curryFun f x y = f (x, y) := by
  classical
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ V
    · simp only [curryFun, hx, dite_true]
      change (if y ∈ V then f (x, y) else 0) = f (x, y)
      simp [hy]
    · simp only [curryFun, hx, dite_true]
      change (if y ∈ V then f (x, y) else 0) = f (x, y)
      simp [hy, f.apply_of_notMem (p := (x, y)) fun h ↦ hy h.2]
  · simp [curryFun, hx, f.apply_of_notMem (p := (x, y)) fun h ↦ hx h.1]

/-- The partial maps into `C^j(V, F)` are those of the finite order exponential law. -/
theorem toContDiff_curryFun (f : SmoothLCMap₂ F U hU V hV) (i j : ℕ) (x : E₁) :
    SmoothLCMap.toContDiff j (curryFun f x) = ContDiffLCMap₂.curry (toContDiff₂ i j f) x :=
  ContDiffLCMap.ext fun y ↦ by
    rw [SmoothLCMap.toContDiff_apply, curryFun_apply, ContDiffLCMap₂.curry_apply_apply,
      toContDiff₂_apply]

variable (hUc : IsLocallyConvexSubset U)
include hUc

/-- **`f^∨ : U → C^∞(V, F)` is smooth** ([GN26, Theorem 1.7.30] for `k = ℓ = ∞`). -/
theorem smoothLC_curryFun (f : SmoothLCMap₂ F U hU V hV) : SmoothLC (curryFun f) U := fun i ↦
  (SmoothLCMap.contDiffLC_iff hUc hU).2 fun j ↦
    (ContDiffLCMap₂.curry (toContDiff₂ i j f)).contDiffLC.congr fun x _ ↦
      (toContDiff_curryFun f i j x).symm

/-- **The curried map** `Φ(f) = f^∨ ∈ C^∞(U, C^∞(V, F))` of `f ∈ C^{∞,∞}(U × V, F)`. -/
def curry (f : SmoothLCMap₂ F U hU V hV) : SmoothLCMap (SmoothLCMap F V hV) U hU :=
  SmoothLCMap.mk (curryFun f) (smoothLC_curryFun hUc f) fun x hx ↦ by simp [curryFun, hx]

/-- `Φ(f)(x)(y) = f(x, y)`. -/
@[simp]
theorem curry_apply_apply (f : SmoothLCMap₂ F U hU V hV) (x : E₁) (y : E₂) :
    curry hUc f x y = f (x, y) :=
  curryFun_apply f x y

/-- `Φ` as a linear map. -/
def curryLM : SmoothLCMap₂ F U hU V hV →ₗ[ℝ] SmoothLCMap (SmoothLCMap F V hV) U hU where
  toFun := curry hUc
  map_add' _ _ := SmoothLCMap.ext fun _ ↦ SmoothLCMap.ext fun _ ↦ by
    simp only [SmoothLCMap.coe_add, Pi.add_apply, curry_apply_apply, coe_add]
  map_smul' _ _ := SmoothLCMap.ext fun _ ↦ SmoothLCMap.ext fun _ ↦ by
    simp only [SmoothLCMap.coe_smul, Pi.smul_apply, curry_apply_apply, coe_smul,
      RingHom.id_apply]

theorem curry_injective : Function.Injective (curry (F := F) (hU := hU) (hV := hV) hUc) :=
  fun f g h ↦ ext fun p ↦ by
    rw [← curry_apply_apply hUc f p.1 p.2, ← curry_apply_apply hUc g p.1 p.2, h]

/-- The components of `Φ(f)` in `C^i(U, C^j(V, F))` are the finite order `Φ`'s. -/
theorem postcomp_toContDiff_curry (f : SmoothLCMap₂ F U hU V hV) (i j : ℕ) :
    ContDiffLCMap.postcomp (SmoothLCMap.toContDiffCLM j)
        (SmoothLCMap.toContDiff i (curry hUc f)) =
      ContDiffLCMap₂.curry (toContDiff₂ i j f) :=
  ContDiffLCMap.ext fun x ↦ toContDiff_curryFun f i j x

/-- `Φ` is continuous. -/
theorem continuous_curry : Continuous (curry (F := F) (hU := hU) (hV := hV) hUc) :=
  SmoothLCMap.continuous_iff.2 fun i ↦ SmoothLCMap.continuous_contDiffLCMap_iff.2 fun j ↦ by
    simp_rw [postcomp_toContDiff_curry]
    exact ContDiffLCMap₂.continuous_curry.comp (continuous_toContDiff₂ i j)

/-- **[GN26, Theorem 1.7.30]** for `k = ℓ = ∞`, sets with dense interior:
`Φ : C^{∞,∞}(U × V, F) → C^∞(U, C^∞(V, F))`, `f ↦ f^∨`, is a linear topological embedding. -/
theorem isEmbedding_curry : Topology.IsEmbedding (curry (F := F) (hU := hU) (hV := hV) hUc) := by
  refine ⟨?_, curry_injective hUc⟩
  let G : SmoothLCMap (SmoothLCMap F V hV) U hU →
      ∀ q : ℕ × ℕ, ContDiffLCMap (ContDiffLCMap F q.2 V hV) q.1 U hU := fun h q ↦
    ContDiffLCMap.postcomp (SmoothLCMap.toContDiffCLM q.2) (SmoothLCMap.toContDiff q.1 h)
  have hG : Continuous G := continuous_pi fun q ↦
    (ContDiffLCMap.continuous_postcomp _).comp (SmoothLCMap.continuous_toContDiff q.1)
  have hGc : G ∘ curry hUc = Pi.map (fun q : ℕ × ℕ ↦ ContDiffLCMap₂.curry (F := F) (hU := hU)
      (hV := hV) (k := q.1) (ℓ := q.2)) ∘ toPi := by
    funext f q
    exact postcomp_toContDiff_curry hUc f q.1 q.2
  refine Topology.IsInducing.of_comp (continuous_curry hUc) hG ?_
  rw [hGc]
  exact (Topology.IsInducing.piMap fun q ↦ ContDiffLCMap₂.isEmbedding_curry.isInducing).comp
    isEmbedding_toPi.isInducing

/-- `Φ` as a continuous linear map. -/
def curryCLM : SmoothLCMap₂ F U hU V hV →L[ℝ] SmoothLCMap (SmoothLCMap F V hV) U hU :=
  ⟨curryLM hUc, continuous_curry hUc⟩

omit hUc in
/-- The map `g^∧(x, y) = g(x)(y)` of `g ∈ C^∞(U, C^∞(V, F))`, under `ExpLawEval` for all finite
orders. -/
def uncurryOf (hev : ∀ i j, ExpLawEval i j U V F) (g : SmoothLCMap (SmoothLCMap F V hV) U hU) :
    SmoothLCMap₂ F U hU V hV :=
  mk (fun p ↦ g p.1 p.2)
    (fun i j _ _ ↦ (ContDiffLCMap₂.uncurryOf (hev i j) (ContDiffLCMap.postcomp
      (SmoothLCMap.toContDiffCLM j) (SmoothLCMap.toContDiff i g))).contDiffLC₂)
    fun p hp ↦ by
      by_cases h1 : p.1 ∈ U
      · exact (g p.1).apply_of_notMem fun h2 ↦ hp ⟨h1, h2⟩
      · simp [g.apply_of_notMem h1]

theorem curry_uncurryOf (hev : ∀ i j, ExpLawEval i j U V F)
    (g : SmoothLCMap (SmoothLCMap F V hV) U hU) : curry hUc (uncurryOf hev g) = g :=
  SmoothLCMap.ext fun x ↦ SmoothLCMap.ext fun y ↦ by
    rw [curry_apply_apply]
    rfl

/-- **The exponential law for `k = ℓ = ∞`** ([GN26, Theorem 1.7.30]), for locally convex
`U` and `V` with dense interior: under `ExpLawEval` for all finite orders,
`Φ : C^{∞,∞}(U × V, F) → C^∞(U, C^∞(V, F))` is an isomorphism of topological vector spaces. -/
def curryEquivOf (hev : ∀ i j, ExpLawEval i j U V F) :
    SmoothLCMap₂ F U hU V hV ≃L[ℝ] SmoothLCMap (SmoothLCMap F V hV) U hU where
  toLinearMap := curryLM hUc
  invFun := uncurryOf hev
  left_inv f := curry_injective hUc (curry_uncurryOf hUc hev (curry hUc f))
  right_inv := curry_uncurryOf hUc hev
  continuous_toFun := continuous_curry hUc
  continuous_invFun := by
    rw [(isEmbedding_curry hUc).isInducing.continuous_iff]
    exact continuous_id.congr fun g ↦ (curry_uncurryOf hUc hev g).symm

/-- **[GN26, Theorem 1.7.30(a)]** for `k = ℓ = ∞`: if `V` is locally compact. -/
def curryEquiv [LocallyCompactSpace V] :
    SmoothLCMap₂ F U hU V hV ≃L[ℝ] SmoothLCMap (SmoothLCMap F V hV) U hU :=
  curryEquivOf hUc fun _ _ ↦ expLawEval_of_locallyCompactSpace hV

/-- **[GN26, Theorem 1.7.30(b)]** for `k = ℓ = ∞`: if all `U × V × E₁^i × E₂^j` are
`k_ℝ`-spaces. -/
def curryEquivOfKRSpace
    (h : ∀ i j, KRSpace ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂))))) :
    SmoothLCMap₂ F U hU V hV ≃L[ℝ] SmoothLCMap (SmoothLCMap F V hV) U hU :=
  curryEquivOf hUc fun _ _ ↦ expLawEval_of_krSpace fun i _ j _ ↦ h i j

/-- **The exponential law for smooth maps on Fréchet spaces**: if `E₁` and `E₂` are first
countable, `Φ : C^{∞,∞}(U × V, F) → C^∞(U, C^∞(V, F))` is an isomorphism of topological vector
spaces. -/
def curryEquivOfFirstCountable [FirstCountableTopology E₁] [FirstCountableTopology E₂] :
    SmoothLCMap₂ F U hU V hV ≃L[ℝ] SmoothLCMap (SmoothLCMap F V hV) U hU :=
  curryEquivOfKRSpace hUc fun _ _ ↦ KRSpace.of_firstCountableTopology _

end SmoothLCMap₂

end SmoothExpLaw

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.MappingSpace.CkTopology

/-!
# The compact-open `C^∞` topology

Let `E`, `F` be locally convex spaces and `U ⊆ E` open. The space `C^∞(U, F)` of smooth maps in
the sense of Michal–Bastiani carries the **compact-open `C^∞` topology**, the initial topology
with respect to all the differentials `d^(j) : C^∞(U, F) → C(U × E^j, F)`, `j ∈ ℕ`
([GN26, Definition 1.7.10]). This file treats the case `k = ∞` of
`LocallyConvexAnalysis.MappingSpace.CkTopology`.

## Main definitions

* `SmoothMBMap F U`: the space `C^∞(U, F)` with the compact-open `C^∞` topology, and
  `SmoothMBMap.toCk k : C^∞(U, F) → C^k(U, F)`.

## Main results

* `SmoothMBMap.continuous_iff`: the topology of `C^∞(U, F)` is initial with respect to the
  inclusions into the `C^k(U, F)`.
* `SmoothMBMap.isEmbedding_toPi`, `SmoothMBMap.isClosed_range_toPi`,
  `SmoothMBMap.compRightOfContDiffCLM`, `SmoothMBMap.continuous_compGraph`,
  `SmoothMBMap.continuous_compLeftOfContDiff`, `SmoothMBMap.prodEquiv`: the results of
  `LocallyConvexAnalysis.MappingSpace.CkTopology` for `k = ∞` ([GN26, Lemma 1.7.15, Propositions
  1.7.11 and 1.7.12, Corollaries 1.7.13 and 1.7.14]), deduced from the finite orders.

## Implementation notes

* **The order `k = ∞`.** `ContDiffMBOn` is defined by recursion on `k ∈ ℕ`, so instead of indexing
  by `ℕ∞` we use a separate type `SmoothMBMap F U`, whose topology is initial with respect to all
  the `d^(j)`, `j ∈ ℕ`, equivalently with respect to the inclusions into the `C^k(U, F)`
  (`SmoothMBMap.continuous_iff`). The operations on `C^∞` are assembled from the finite-order
  ones with `SmoothMBMap.ofForall`, and their continuity follows from `continuous_iff`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### The space `C^∞(U, F)` -/

section Smooth

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (F) in
/-- The smooth maps on the open set `U`, extended by `0` outside `U`, as a submodule of
`E → F`: the intersection of the submodules of `C^k` maps. -/
def smoothMBSubmodule (U : Opens E) : Submodule ℝ (E → F) :=
  ⨅ k, contDiffMBSubmodule F k U

variable (F) in
/-- **The space `C^∞(U, F)`** of smooth maps (in the sense of Michal–Bastiani) on an open set
`U ⊆ E`, extended by `0` outside `U`. It carries the compact-open `C^∞` topology, the initial
topology with respect to all the differentials `d^(j) : C^∞(U, F) → C(U × E^j, F)`, `j ∈ ℕ`
([GN26, Definition 1.7.10] with `k = ∞`), equivalently with respect to the inclusions
`C^∞(U, F) → C^k(U, F)` (`SmoothMBMap.continuous_iff`). -/
def SmoothMBMap (U : Opens E) : Type (max u v) := smoothMBSubmodule F U

namespace SmoothMBMap

variable {U : Opens E}

/-- The vector space operations of `C^∞(U, F)` are pointwise. -/
instance : AddCommGroup (SmoothMBMap F U) :=
  inferInstanceAs (AddCommGroup (smoothMBSubmodule F U))

/-- The vector space operations of `C^∞(U, F)` are pointwise. -/
instance : Module ℝ (SmoothMBMap F U) :=
  inferInstanceAs (Module ℝ (smoothMBSubmodule F U))

/-- An element of `C^∞(U, F)` is a map `E → F`. -/
instance : FunLike (SmoothMBMap F U) E F where
  coe γ := Subtype.val (γ : smoothMBSubmodule F U)
  coe_injective := Subtype.val_injective

/-- An element of `C^∞(U, F)` is `C^k` on `U` for every `k`. -/
theorem contDiffMBOn (γ : SmoothMBMap F U) (k : ℕ) : ContDiffMBOn k γ U :=
  (Submodule.mem_iInf _ |>.1 (γ : smoothMBSubmodule F U).2 k).1

/-- An element of `C^∞(U, F)` is smooth on `U`. -/
theorem smoothMBOn (γ : SmoothMBMap F U) : SmoothMBOn γ U :=
  γ.contDiffMBOn

/-- An element of `C^∞(U, F)` vanishes outside `U`. -/
theorem apply_of_notMem (γ : SmoothMBMap F U) {x : E} (hx : x ∉ U) : γ x = 0 :=
  (Submodule.mem_iInf _ |>.1 (γ : smoothMBSubmodule F U).2 0).2 x hx

/-- The element of `C^∞(U, F)` given by a map that is smooth on `U` and vanishes outside `U`. -/
def mk (f : E → F) (hf : SmoothMBOn f U) (h0 : ∀ x ∉ U, f x = 0) : SmoothMBMap F U :=
  ⟨f, (Submodule.mem_iInf _).2 fun k ↦ ⟨hf k, h0⟩⟩

/-- The underlying map of `SmoothMBMap.mk f hf h0` is `f`. -/
@[simp]
theorem coe_mk (f : E → F) (hf : SmoothMBOn f U) (h0 : ∀ x ∉ U, f x = 0) : ⇑(mk f hf h0) = f :=
  rfl

/-- Elements of `C^∞(U, F)` are equal if they agree as maps. -/
@[ext]
theorem ext {γ η : SmoothMBMap F U} (h : ∀ x, γ x = η x) : γ = η :=
  DFunLike.ext _ _ h

/-- Addition in `C^∞(U, F)` is pointwise. -/
@[simp]
theorem coe_add (γ η : SmoothMBMap F U) : ⇑(γ + η) = γ + η :=
  rfl

/-- Scalar multiplication in `C^∞(U, F)` is pointwise. -/
@[simp]
theorem coe_smul (c : ℝ) (γ : SmoothMBMap F U) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The inclusion `C^∞(U, F) → C^k(U, F)`. -/
def toCk (k : ℕ) (γ : SmoothMBMap F U) : ContDiffMBMap F k U :=
  ContDiffMBMap.mk γ (γ.contDiffMBOn k) fun _ hx ↦ γ.apply_of_notMem hx

/-- The inclusion `C^∞(U, F) → C^k(U, F)` does not change the underlying map. -/
@[simp]
theorem coe_toCk (k : ℕ) (γ : SmoothMBMap F U) : ⇑(toCk k γ) = γ :=
  rfl

/-- The inclusion `C^∞(U, F) → C^k(U, F)` as a linear map. -/
def toCkL (k : ℕ) : SmoothMBMap F U →ₗ[ℝ] ContDiffMBMap F k U where
  toFun := toCk k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The element of `C^∞(U, F)` defined by a compatible family `φ k ∈ C^k(U, F)`, all with the
same underlying map. -/
def ofForall (φ : ∀ k, ContDiffMBMap F k U) (h : ∀ k, ⇑(φ k) = φ 0) : SmoothMBMap F U :=
  mk (φ 0) (fun k ↦ h k ▸ (φ k).contDiffMBOn) fun _ hx ↦ (φ 0).apply_of_notMem hx

/-- The components of `ofForall φ h` are the `φ k`. -/
theorem toCk_ofForall (φ : ∀ k, ContDiffMBMap F k U) (h : ∀ k, ⇑(φ k) = φ 0) (k : ℕ) :
    toCk k (ofForall φ h) = φ k :=
  ContDiffMBMap.ext fun x ↦ (congrFun (h k) x).symm

/-- The linear map `Φ : C^∞(U, F) → ∏_{j ∈ ℕ} C(U × E^j, F)`, `γ ↦ (d^(j)γ)_j`. -/
def toPi : SmoothMBMap F U →ₗ[ℝ] ∀ j : ℕ, C(U × (Fin j → E), F) :=
  LinearMap.pi fun j ↦ (ContDiffMBMap.iteratedDL j le_rfl).comp (toCkL j)

/-- The components of `toPi γ` are the differentials of `γ`. -/
theorem toPi_apply (γ : SmoothMBMap F U) (j : ℕ) :
    toPi γ j = ContDiffMBMap.iteratedD j le_rfl (toCk j γ) :=
  rfl

/-- The differentials `d^(j)`, `j ∈ ℕ`, separate the points of `C^∞(U, F)`. -/
theorem toPi_injective : Function.Injective (toPi (F := F) (U := U)) := by
  intro γ η h
  ext x
  by_cases hx : x ∈ U
  · exact congrArg (fun φ ↦ φ 0 (⟨x, hx⟩, Fin.elim0)) h
  · rw [γ.apply_of_notMem hx, η.apply_of_notMem hx]

/-- **The compact-open `C^∞` topology** ([GN26, Definition 1.7.10], `k = ∞`). -/
instance : TopologicalSpace (SmoothMBMap F U) :=
  .induced toPi inferInstance

/-- **[GN26, Lemma 1.7.15]** (`k = ∞`, embedding part). -/
theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (F := F) (U := U)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

/-- `C^∞(U, F)` is a topological additive group. -/
instance : IsTopologicalAddGroup (SmoothMBMap F U) :=
  isTopologicalAddGroup_induced toPi

/-- Scalar multiplication on `C^∞(U, F)` is continuous. -/
instance : ContinuousSMul ℝ (SmoothMBMap F U) :=
  continuousSMul_induced toPi

/-- `C^∞(U, F)` is locally convex. -/
instance : LocallyConvexSpace ℝ (SmoothMBMap F U) :=
  LocallyConvexSpace.induced toPi

/-- `C^∞(U, F)` is Hausdorff. -/
instance : T2Space (SmoothMBMap F U) :=
  isEmbedding_toPi.t2Space

/-- The inclusion `C^∞(U, F) → C^k(U, F)` is continuous. -/
theorem continuous_toCk (k : ℕ) : Continuous (toCk (F := F) (U := U) k) :=
  ContDiffMBMap.continuous_iff.2 fun j _ ↦
    (continuous_apply j).comp (continuous_induced_dom : Continuous (toPi (F := F) (U := U)))

/-- The inclusion `C^∞(U, F) → C^k(U, F)` as a continuous linear map. -/
def toCkCLM (k : ℕ) : SmoothMBMap F U →L[ℝ] ContDiffMBMap F k U :=
  ⟨toCkL k, continuous_toCk k⟩

/-- A map into `C^∞(U, F)` is continuous if and only if its compositions with the inclusions
into `C^k(U, F)`, `k ∈ ℕ`, are continuous: the compact-open `C^∞` topology is the initial
topology with respect to these inclusions. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → SmoothMBMap F U} :
    Continuous φ ↔ ∀ k, Continuous fun x ↦ toCk k (φ x) :=
  ⟨fun h k ↦ (continuous_toCk k).comp h, fun h ↦ continuous_induced_rng.2 <|
    continuous_pi fun j ↦ (ContDiffMBMap.continuous_iteratedD j le_rfl).comp (h j)⟩

/-- Continuity of a map into `C^∞(U, F)` built with `ofForall` from continuous maps into the
spaces `C^k(U, F)`. -/
theorem continuous_ofForall {X : Type*} [TopologicalSpace X] {φ : X → ∀ k, ContDiffMBMap F k U}
    (h : ∀ x k, ⇑(φ x k) = φ x 0) (hc : ∀ k, Continuous fun x ↦ φ x k) :
    Continuous fun x ↦ ofForall (φ x) (h x) :=
  continuous_iff.2 fun k ↦ (hc k).congr fun x ↦ (toCk_ofForall (φ x) (h x) k).symm

/-- **[GN26, Lemma 1.7.15]** (`k = ∞`, closed image). -/
theorem isClosed_range_toPi : IsClosed (range (toPi (F := F) (U := U))) := by
  refine closure_subset_iff_isClosed.1 fun h hh ↦ ?_
  -- the truncations of `h` are in the closed images of the `C^k` spaces
  let T : ∀ k, (∀ j : ℕ, C(U × (Fin j → E), F)) → ∀ j : Fin (k + 1), C(U × (Fin j → E), F) :=
    fun k h j ↦ h j
  have hT : ∀ k, Continuous (T k) := fun k ↦ continuous_pi fun j ↦ continuous_apply _
  have hcomm : ∀ k (γ : SmoothMBMap F U), T k (toPi γ) = ContDiffMBMap.toPi (toCk k γ) :=
    fun _ _ ↦ rfl
  have hk : ∀ k, ∃ γ : ContDiffMBMap F k U, ContDiffMBMap.toPi γ = T k h := fun k ↦ by
    have : T k h ∈ closure (range (ContDiffMBMap.toPi (F := F) (k := k) (U := U))) := by
      refine map_mem_closure (t := range (ContDiffMBMap.toPi (F := F) (k := k) (U := U)))
        (hT k) hh ?_
      rintro _ ⟨γ, rfl⟩
      exact ⟨toCk k γ, (hcomm k γ).symm⟩
    rwa [ContDiffMBMap.isClosed_range_toPi.closure_eq] at this
  choose φ hφ using hk
  have hφ0 : ∀ k, ⇑(φ k) = φ 0 := fun k ↦ by
    funext x
    by_cases hx : x ∈ U
    · have h1 := congrArg (fun ψ ↦ ψ 0 (⟨x, hx⟩, Fin.elim0)) (hφ k)
      have h2 := congrArg (fun ψ ↦ ψ 0 (⟨x, hx⟩, Fin.elim0)) (hφ 0)
      exact h1.trans h2.symm
    · rw [(φ k).apply_of_notMem hx, (φ 0).apply_of_notMem hx]
  refine ⟨ofForall φ hφ0, funext fun j ↦ ?_⟩
  rw [toPi_apply, toCk_ofForall]
  exact congrFun (hφ j) (Fin.last j)

end SmoothMBMap

end Smooth

/-! ### Operations on `C^∞(U, F)` -/

section SmoothOperations

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

namespace SmoothMBMap

variable {U : Opens E}

/-- Pullback `γ ↦ γ ∘ L` along a continuous linear map `L : E₁ → E`,
`C^∞(U, F) → C^∞(L⁻¹(U), F)`, as a continuous linear map ([GN26, Proposition 1.7.11],
`r = ∞`, linear case). -/
def compRightCLM (L : E₁ →L[ℝ] E) :
    SmoothMBMap F U →L[ℝ] SmoothMBMap F (Opens.comap (L : C(E₁, E)) U) where
  toFun γ := ofForall (fun k ↦ ContDiffMBMap.compRight L (toCk k γ)) fun _ ↦ rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    (ContDiffMBMap.compRightCLM L).continuous.comp (continuous_toCk k)

/-- Postcomposition `γ ↦ g ∘ γ` with a continuous linear map `g : F → G`,
`C^∞(U, F) → C^∞(U, G)`, as a continuous linear map ([GN26, Corollary 1.7.13], `k = ∞`,
linear case). -/
def compLeftCLM (g : F →L[ℝ] G) : SmoothMBMap F U →L[ℝ] SmoothMBMap G U where
  toFun γ := ofForall (fun k ↦ ContDiffMBMap.compLeft g (toCk k γ)) fun _ ↦ rfl
  map_add' γ η := by
    ext x
    exact congrFun (congrArg DFunLike.coe
      ((ContDiffMBMap.compLeftCLM g).map_add (toCk 0 γ) (toCk 0 η))) x
  map_smul' c γ := by
    ext x
    exact congrFun (congrArg DFunLike.coe
      ((ContDiffMBMap.compLeftCLM g).map_smul c (toCk 0 γ))) x
  cont := continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    (ContDiffMBMap.compLeftCLM g).continuous.comp (continuous_toCk k)

/-- `(γ, η) ↦ (x ↦ (γ x, η x))`, `C^∞(U, F) × C^∞(U, G) → C^∞(U, F × G)`, as a continuous linear
map. -/
def prodMkCLM : SmoothMBMap F U × SmoothMBMap G U →L[ℝ] SmoothMBMap (F × G) U where
  toFun p := ofForall (fun k ↦ ContDiffMBMap.prodMk (toCk k p.1) (toCk k p.2)) fun _ ↦ rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    ContDiffMBMap.prodMkCLM.continuous.comp
      (((continuous_toCk k).comp continuous_fst).prodMk ((continuous_toCk k).comp continuous_snd))

/-- **[GN26, Corollary 1.7.14]** (`k = ∞`):
`C^∞(U, F × G) ≅ C^∞(U, F) × C^∞(U, G)` as topological vector spaces. -/
def prodEquiv : SmoothMBMap (F × G) U ≃L[ℝ] SmoothMBMap F U × SmoothMBMap G U :=
  ContinuousLinearEquiv.equivOfInverse
    ((compLeftCLM (ContinuousLinearMap.fst ℝ F G)).prod
      (compLeftCLM (ContinuousLinearMap.snd ℝ F G)))
    prodMkCLM (fun γ ↦ by ext x <;> rfl) fun p ↦ by ext x <;> rfl

/-- The differential `d : C^∞(U, F) → C^∞(U × E, F)` as a continuous linear map. -/
def dCLM : SmoothMBMap F U →L[ℝ] SmoothMBMap F (Opens.prodUniv U) where
  toFun γ := ofForall (fun k ↦ ContDiffMBMap.dMap (toCk (k + 1) γ)) fun _ ↦ rfl
  map_add' γ η := by
    ext p
    simp only [ofForall, coe_add, Pi.add_apply]
    exact congrFun (congrArg DFunLike.coe (ContDiffMBMap.dMap_add (toCk 1 γ) (toCk 1 η))) p
  map_smul' c γ := by
    ext p
    simp only [ofForall, coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact congrFun (congrArg DFunLike.coe (ContDiffMBMap.dMap_smul c (toCk 1 γ))) p
  cont := continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    ContDiffMBMap.continuous_dMap.comp (continuous_toCk (k + 1))

end SmoothMBMap

end SmoothOperations

section SmoothSuperposition

variable {Z : Type u} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z] [T2Space Z]
  {E : Type w} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace SmoothMBMap

variable {U : Opens Z}

/-- The superposition operator `f_* : C^∞(U, E) → C^∞(U, F)`, `γ ↦ f ∘ (id_U, γ)`, for
`f : Z × E → F` smooth on `U × E`. -/
def compGraph {f : Z × E → F} (hf : SmoothMBOn f ((U : Set Z) ×ˢ univ)) (γ : SmoothMBMap E U) :
    SmoothMBMap F U :=
  ofForall (fun k ↦ ContDiffMBMap.compGraph (hf k) (toCk k γ)) fun _ ↦ rfl

/-- **[GN26, Proposition 1.7.12]** (`r = ∞`): superposition operators
`f_* : C^∞(U, E) → C^∞(U, F)` are continuous. -/
theorem continuous_compGraph {f : Z × E → F} (hf : SmoothMBOn f ((U : Set Z) ×ˢ univ)) :
    Continuous (compGraph hf) :=
  continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    (ContDiffMBMap.continuous_compGraph (hf k)).comp (continuous_toCk k)

/-- The superposition operator `C^∞(U, g) : C^∞(U, E) → C^∞(U, F)`, `γ ↦ g ∘ γ`, for a smooth
map `g : E → F`. -/
def compLeftOfContDiff {g : E → F} (hg : SmoothMBOn g univ) (γ : SmoothMBMap E U) :
    SmoothMBMap F U :=
  ofForall (fun k ↦ ContDiffMBMap.compLeftOfContDiff (hg k) (toCk k γ)) fun _ ↦ rfl

/-- **[GN26, Corollary 1.7.13]** (`k = ∞`): `γ ↦ g ∘ γ` is continuous on `C^∞(U, E)`. -/
theorem continuous_compLeftOfContDiff {g : E → F} (hg : SmoothMBOn g univ) :
    Continuous (compLeftOfContDiff (U := U) hg) :=
  continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    (ContDiffMBMap.continuous_compLeftOfContDiff (hg k)).comp (continuous_toCk k)

end SmoothMBMap

end SmoothSuperposition

section SmoothPullback

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type w} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace SmoothMBMap

variable {U : Opens E₁} {V : Opens E₂}

/-- **[GN26, Proposition 1.7.11]** (`r = ∞`): for `f : E₁ → E₂` smooth on `U` with
`f(U) ⊆ V`, the pullback `f^* : C^∞(V, F) → C^∞(U, F)`, `γ ↦ γ ∘ f`, is continuous linear. -/
def compRightOfContDiffCLM {f : E₁ → E₂} (hf : SmoothMBOn f U) (hUV : MapsTo f U V) :
    SmoothMBMap F V →L[ℝ] SmoothMBMap F U where
  toFun γ := ofForall (fun k ↦ ContDiffMBMap.compRightOfContDiff (hf k) hUV (toCk k γ))
    fun _ ↦ rfl
  map_add' γ η := by
    ext x
    exact congrFun (congrArg DFunLike.coe
      ((ContDiffMBMap.compRightOfContDiffCLM (hf 0) hUV).map_add (toCk 0 γ) (toCk 0 η))) x
  map_smul' c γ := by
    ext x
    exact congrFun (congrArg DFunLike.coe
      ((ContDiffMBMap.compRightOfContDiffCLM (hf 0) hUV).map_smul c (toCk 0 γ))) x
  cont := continuous_ofForall (fun _ _ ↦ rfl) fun k ↦
    (ContDiffMBMap.continuous_compRightOfContDiff (hf k) hUV).comp (continuous_toCk k)

end SmoothMBMap

end SmoothPullback

end LocallyConvex.Analysis

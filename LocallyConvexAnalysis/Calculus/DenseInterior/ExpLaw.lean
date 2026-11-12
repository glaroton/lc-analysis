/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.DenseInterior.CklRules
public import LocallyConvexAnalysis.Calculus.ExponentialLaw
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The exponential law on sets with dense interior

Reference: [GN26, Definitions 1.7.10] and 1.7.17, Theorem 1.7.30 (p. 102) and its proof (pp.
103–106). For open `U`, `V` the same results are in `LocallyConvexAnalysis.MappingSpace.CkTopology`,
`LocallyConvexAnalysis.Calculus.CklMaps` and `LocallyConvexAnalysis.Calculus.ExponentialLaw`; here
`U ⊆ E₁` and `V ⊆ E₂` are sets with dense interior (Definition 1.4.4).

## Main definitions

* `ContDiffLCMap F k V hV`: the space `C^k(V, F)` with the compact-open `C^k` topology, the initial
  topology with respect to `d^(j) : C^k(V, F) → C(V × E^j, F)`, `j ≤ k`; a locally convex
  Hausdorff space. As in the open case, maps are extended by `0` outside `V`.
* `ContDiffLCMap₂ F k ℓ U hU V hV`: the space `C^{k,ℓ}(U × V, F)` with the compact-open `C^{k,ℓ}`
  topology.
* `curryLC`, `ContDiffLCMap₂.curry`: the partial map `f^∨(x) = f(x, ·) ∈ C^ℓ(V, F)`.

## Main results

* `ContDiffLC₂.contDiffLC_curryLC`: for `f` of class `C^{k,ℓ}` on `U × V`, `f^∨ : U → C^ℓ(V, F)` is
  `C^k` ([GN26, Theorem 1.7.30]).
* `iteratedDLC_iteratedDLC_curryLC`, `ContDiffLCMap₂.iteratedD_iteratedD_curry`: the formula
  `d^(j)(d^(i)(f^∨)(x, v))(y, w) = d^(i,j) f(x, y, v, w)` ([GN26, (1.98)]).
* `ContDiffLCMap₂.isEmbedding_curry`: `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`, `f ↦ f^∨`, is a
  linear topological embedding ([GN26, Theorem 1.7.30]).
* `ContDiffLCMap₂.curryEquiv`: if `V` is locally compact, `Φ` is an isomorphism of topological
  vector spaces, with inverse `g ↦ g^∧` ([GN26, Theorem 1.7.30(a)]).

## Implementation notes

* **Departure from Glöckner–Neeb in the proof that `f^∨` is `C^k`.** Glöckner–Neeb differentiate
  `f^∨` through the continuous extension of difference quotients of `C^{1,0}` maps (Lemma 1.7.6)
  and an induction on the order of the differentials (1.99). Here the induction runs through the
  recursive characterization of `C^{k,ℓ}` (`ContDiffLC₂.contDiffLC₂_partialDLC₁`): the derivative
  of `f^∨` at interior points is `(d^(1,0) f)^∨` (`hasDirDerivAt_curryLC`), the convergence of the
  difference quotients in `C^ℓ(V, F)` being uniform on compact subsets of `V × E₂^j` by the mean
  value inclusion with a parameter (`eventually_forall_quotient_mem_param`). The parameter ranges
  over all of `V`, also over its boundary. We do not claim this argument is new.
* **Locally compact `V`.** Glöckner–Neeb's hypothesis (a) is used as stated, `LocallyCompactSpace V`
  for the subspace `V`. For nonempty `V` it forces `E₂` to be locally compact
  (`HasDenseInterior.locallyCompactSpace`), which gives the continuity of the evaluation on
  `C(V × E₂^j, F) × (V × E₂^j)`. Hypothesis (b), on `k_ℝ`-spaces (`KRSpace`), gives the same
  continuity on compact sets (`KRSpace.continuous_eval`), since `F` is completely regular
  (`curryEquivOfKRSpace`). First countable spaces are `k_ℝ`-spaces, so the law holds for Fréchet
  spaces (`curryEquivOfFirstCountable`). Only finite `k`, `ℓ` are considered.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### Linearity of the differentials on sets with dense interior -/

section Linearity

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k : ℕ} {V : Set E}

/-- `d^(j)(f + g) = d^(j) f + d^(j) g` on `V × E^j`. -/
theorem iteratedDLC_add (hV : HasDenseInterior V) {f g : E → F} (hf : ContDiffLC k f V)
    (hg : ContDiffLC k g V) {j : ℕ} (hj : j ≤ k) :
    EqOn (iteratedDLC j (fun x ↦ f x + g x) V)
      (fun p ↦ iteratedDLC j f V p + iteratedDLC j g V p) (V ×ˢ univ) :=
  iteratedDLC_unique hV ((hf.add hV hg).continuousOn_iteratedDLC hj)
    ((hf.continuousOn_iteratedDLC hj).add (hg.continuousOn_iteratedDLC hj))
    (fun p hp ↦ iteratedDLC_eq_iteratedDMB hp.1) fun p hp ↦ by
      rw [iteratedDLC_eq_iteratedDMB hp.1, iteratedDLC_eq_iteratedDMB hp.1]
      exact (iteratedDMB_add isOpen_interior hf.contDiffMBOn_interior
        hg.contDiffMBOn_interior hj hp.1 p.2).symm

/-- `d^(j)(c • f) = c • d^(j) f` on `V × E^j`. -/
theorem iteratedDLC_const_smul (hV : HasDenseInterior V) {f : E → F} (hf : ContDiffLC k f V)
    (c : ℝ) {j : ℕ} (hj : j ≤ k) :
    EqOn (iteratedDLC j (fun x ↦ c • f x) V) (fun p ↦ c • iteratedDLC j f V p) (V ×ˢ univ) :=
  iteratedDLC_unique hV ((hf.const_smul hV c).continuousOn_iteratedDLC hj)
    ((hf.continuousOn_iteratedDLC hj).const_smul c)
    (fun p hp ↦ iteratedDLC_eq_iteratedDMB hp.1) fun p hp ↦ by
      rw [iteratedDLC_eq_iteratedDMB hp.1]
      exact (iteratedDMB_const_smul isOpen_interior hf.contDiffMBOn_interior c hj hp.1 p.2).symm

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- `d^(j) f` only depends on `f|V`. -/
theorem iteratedDLC_congr (hV : HasDenseInterior V) {f g : E → F} (hf : ContDiffLC k f V)
    (h : EqOn f g V) {j : ℕ} (hj : j ≤ k) :
    EqOn (iteratedDLC j f V) (iteratedDLC j g V) (V ×ˢ univ) :=
  iteratedDLC_unique hV (hf.continuousOn_iteratedDLC hj)
    ((hf.congr h).continuousOn_iteratedDLC hj)
    (fun p hp ↦ iteratedDLC_eq_iteratedDMB hp.1) fun p hp ↦ by
      rw [iteratedDLC_eq_iteratedDMB hp.1]
      exact iteratedDMB_congr_of_eventuallyEq j
        ((h.mono interior_subset).eventuallyEq_of_mem (isOpen_interior.mem_nhds hp.1)).symm p.2

end Linearity

/-! ### Difference quotients depending on a parameter -/

section Quotients

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Difference quotients with a parameter.** Let `x ↦ g(x, z)` have directional derivatives
`D(x, z)` in the direction `w` at all `x` in the open set `O`, for all parameters `z ∈ S`, with
`D` continuous on `O × S`. Then `t⁻¹ (g(x + t w, z) - g(x, z)) → D(p, z₀)` as `(x, z, t)` tends to
`(p, z₀, 0)` with `z ∈ S`, `t ≠ 0`. The parameters `z` may lie in any subset `S` of a topological
space (for instance, a set with dense interior); compare `tendsto_quotient_of_hasDirDerivAt`. -/
theorem tendsto_quotient_of_hasDirDerivAt_param {Z : Type*} [TopologicalSpace Z]
    {g : E × Z → F} {O : Set E} (hO : IsOpen O) {S : Set Z} {w : E} {D : E × Z → F}
    (hd : ∀ q ∈ O, ∀ z ∈ S, HasDirDerivAt (fun x ↦ g (x, z)) q w (D (q, z)))
    (hD : ContinuousOn D (O ×ˢ S)) {p : E} (hp : p ∈ O) {z₀ : Z} (hz₀ : z₀ ∈ S) :
    Tendsto (fun r : (E × Z) × ℝ ↦ r.2⁻¹ • (g (r.1.1 + r.2 • w, r.1.2) - g r.1))
      (𝓝[{r | r.1.2 ∈ S ∧ r.2 ≠ 0}] ((p, z₀), 0)) (𝓝 (D (p, z₀))) := by
  refine Filter.tendsto_def.mpr fun N hN ↦ ?_
  obtain ⟨W, hW, hWcl, hWc, hWN⟩ := exists_closed_convex_nhds_subset hN
  have hev : ∀ᶠ q in 𝓝 (p, z₀), q.2 ∈ S → q.1 ∈ O ∧ D q ∈ W := by
    have h1 := (hD (p, z₀) ⟨hp, hz₀⟩).eventually_mem hW
    rw [eventually_nhdsWithin_iff] at h1
    have h2 : ∀ᶠ q : E × Z in 𝓝 (p, z₀), q.1 ∈ O :=
      continuous_fst.continuousAt.preimage_mem_nhds (hO.mem_nhds hp)
    filter_upwards [h1, h2] with q hq1 hq2 hqS using ⟨hq2, hq1 ⟨hq2, hqS⟩⟩
  have htube : ∀ᶠ r : (E × Z) × ℝ in 𝓝 ((p, z₀), 0), ∀ s ∈ Icc (0 : ℝ) 1,
      r.1.2 ∈ S → r.1.1 + (s * r.2) • w ∈ O ∧ D (r.1.1 + (s * r.2) • w, r.1.2) ∈ W := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ ↦ ?_
    have hΨ : Continuous fun z : ((E × Z) × ℝ) × ℝ ↦ (z.1.1.1 + (z.2 * z.1.2) • w, z.1.1.2) := by
      fun_prop
    have : Tendsto (fun z : ((E × Z) × ℝ) × ℝ ↦ (z.1.1.1 + (z.2 * z.1.2) • w, z.1.1.2))
        (𝓝 (((p, z₀), (0 : ℝ)), s)) (𝓝 (p, z₀)) := by
      simpa using hΨ.tendsto (((p, z₀), (0 : ℝ)), s)
    filter_upwards [this.eventually hev] with z hz
    exact hz
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [htube] with r hr hrm
  obtain ⟨hrS, ht⟩ := hrm
  refine hWN ((Set.mem_smul_set_iff_inv_smul_mem₀ ht W _).mp ?_)
  have hpts : ∀ s : ℝ, r.1.1 + s • (r.2 • w) = r.1.1 + (s * r.2) • w := fun s ↦ by
    rw [smul_smul]
  have hd' : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt (fun x ↦ g (x, r.1.2)) (r.1.1 + s • (r.2 • w))
      (r.2 • w) (r.2 • D (r.1.1 + (s * r.2) • w, r.1.2)) := fun s hs ↦ by
    rw [hpts s]; exact (hd _ (hr s hs hrS).1 _ hrS).smul_dir r.2
  have hD' : ContinuousOn (fun s : ℝ ↦ r.2 • D (r.1.1 + (s * r.2) • w, r.1.2)) (Icc 0 1) :=
    (continuous_const_smul _).comp_continuousOn (hD.comp
      (by fun_prop : Continuous fun s : ℝ ↦ (r.1.1 + (s * r.2) • w, r.1.2)).continuousOn
      fun s hs ↦ ⟨(hr s hs hrS).1, hrS⟩)
  exact sub_mem_of_hasDirDerivAt hd' hD' (hWc.smul r.2) (hWcl.smul_of_ne_zero ht)
    (fun s hs ↦ Set.smul_mem_smul_set (hr s hs hrS).2)

/-- **Uniform convergence of difference quotients with a parameter on compact sets**: compare
`eventually_forall_quotient_mem`. -/
theorem eventually_forall_quotient_mem_param {Z X : Type*} [TopologicalSpace Z]
    [TopologicalSpace X] {g : E × Z → F} {O : Set E} (hO : IsOpen O) {S : Set Z} {h : E}
    {D : E × Z → F} (hd : ∀ q ∈ O, ∀ z ∈ S, HasDirDerivAt (fun x ↦ g (x, z)) q h (D (q, z)))
    (hD : ContinuousOn D (O ×ˢ S)) {P : X → E × Z} (hP : Continuous P) {K : Set X}
    (hK : IsCompact K) (hKO : MapsTo P K (O ×ˢ S)) {N : Set F} (hN : IsOpen N)
    (hKN : MapsTo (D ∘ P) K N) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ K, t ≠ 0 → t⁻¹ • (g ((P z).1 + t • h, (P z).2) - g (P z)) ∈ N := by
  have key : ∀ z ∈ K, ∀ᶠ q : ℝ × X in 𝓝 (0, z),
      (P q.2).2 ∈ S → q.1 ≠ 0 → q.1⁻¹ • (g ((P q.2).1 + q.1 • h, (P q.2).2) - g (P q.2)) ∈ N := by
    intro z hz
    have T := tendsto_quotient_of_hasDirDerivAt_param hO hd hD (hKO hz).1 (hKO hz).2
    have ev := eventually_nhdsWithin_iff.1 (T (hN.mem_nhds (hKN hz)))
    have hc : Continuous fun q : ℝ × X ↦ (P q.2, q.1) := by fun_prop
    have := (hc.tendsto (0, z)).eventually ev
    filter_upwards [this] with q hq hqS hq0
    exact hq ⟨hqS, hq0⟩
  filter_upwards [hK.eventually_forall_of_forall_eventually (P := fun (t : ℝ) (z : X) ↦
    (P z).2 ∈ S → t ≠ 0 → t⁻¹ • (g ((P z).1 + t • h, (P z).2) - g (P z)) ∈ N) key]
    with t ht z hz ht0
  exact ht z hz (hKO hz).2 ht0

end Quotients

/-! ### The space `C^k(V, F)` for `V` with dense interior -/

section Space

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (F) in
/-- The `C^k` maps on a set `V` with dense interior, extended by `0` outside `V`, as a submodule
of `E → F`. -/
def contDiffLCSubmodule (k : ℕ) (V : Set E) (hV : HasDenseInterior V) : Submodule ℝ (E → F) where
  carrier := {f | ContDiffLC k f V ∧ ∀ x ∉ V, f x = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add hV hg.1, fun x hx ↦ by simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨contDiffLC_const k (0 : F) hV, fun _ _ ↦ rfl⟩
  smul_mem' c f hf := ⟨hf.1.const_smul hV c, fun x hx ↦ by simp [hf.2 x hx]⟩

variable (F) in
/-- **The space `C^k(V, F)`** of `C^k` maps on a set `V` with dense interior
([GN26, Definition 1.7.10], for the sets of Definition 1.4.4), extended by `0` outside `V`. -/
def ContDiffLCMap (k : ℕ) (V : Set E) (hV : HasDenseInterior V) : Type (max u v) :=
  contDiffLCSubmodule F k V hV

namespace ContDiffLCMap

variable {k : ℕ} {V : Set E} {hV : HasDenseInterior V}

instance : AddCommGroup (ContDiffLCMap F k V hV) :=
  inferInstanceAs (AddCommGroup (contDiffLCSubmodule F k V hV))

instance : Module ℝ (ContDiffLCMap F k V hV) :=
  inferInstanceAs (Module ℝ (contDiffLCSubmodule F k V hV))

instance : FunLike (ContDiffLCMap F k V hV) E F where
  coe γ := Subtype.val (γ : contDiffLCSubmodule F k V hV)
  coe_injective := Subtype.val_injective

/-- The element of `C^k(V, F)` given by a map that is `C^k` on `V` and vanishes outside `V`. -/
def mk (f : E → F) (hf : ContDiffLC k f V) (h0 : ∀ x ∉ V, f x = 0) : ContDiffLCMap F k V hV :=
  ⟨f, hf, h0⟩

@[simp]
theorem coe_mk (f : E → F) (hf : ContDiffLC k f V) (h0 : ∀ x ∉ V, f x = 0) :
    ⇑(mk (hV := hV) f hf h0) = f :=
  rfl

theorem contDiffLC (γ : ContDiffLCMap F k V hV) : ContDiffLC k γ V :=
  (γ : contDiffLCSubmodule F k V hV).2.1

theorem apply_of_notMem (γ : ContDiffLCMap F k V hV) {x : E} (hx : x ∉ V) : γ x = 0 :=
  (γ : contDiffLCSubmodule F k V hV).2.2 x hx

@[ext]
theorem ext {γ η : ContDiffLCMap F k V hV} (h : ∀ x, γ x = η x) : γ = η :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_zero : ⇑(0 : ContDiffLCMap F k V hV) = 0 :=
  rfl

@[simp]
theorem coe_add (γ η : ContDiffLCMap F k V hV) : ⇑(γ + η) = γ + η :=
  rfl

@[simp]
theorem coe_smul (c : ℝ) (γ : ContDiffLCMap F k V hV) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The `j`-th differential `d^(j)γ ∈ C(V × E^j, F)` of `γ ∈ C^k(V, F)`, for `j ≤ k`. -/
def iteratedD (j : ℕ) (hj : j ≤ k) (γ : ContDiffLCMap F k V hV) : C(V × (Fin j → E), F) where
  toFun p := iteratedDLC j γ V (p.1, p.2)
  continuous_toFun := (γ.contDiffLC.continuousOn_iteratedDLC hj).comp_continuous
    (continuous_subtype_val.prodMap continuous_id) fun p ↦ ⟨p.1.2, mem_univ _⟩

@[simp]
theorem iteratedD_apply (j : ℕ) (hj : j ≤ k) (γ : ContDiffLCMap F k V hV)
    (p : V × (Fin j → E)) : iteratedD j hj γ p = iteratedDLC j γ V (p.1, p.2) :=
  rfl

/-- `d^(j) : C^k(V, F) → C(V × E^j, F)` as a linear map. -/
def iteratedDL (j : ℕ) (hj : j ≤ k) : ContDiffLCMap F k V hV →ₗ[ℝ] C(V × (Fin j → E), F) where
  toFun := iteratedD j hj
  map_add' γ η := by
    ext p
    exact iteratedDLC_add hV γ.contDiffLC η.contDiffLC hj ⟨p.1.2, mem_univ _⟩
  map_smul' c γ := by
    ext p
    exact iteratedDLC_const_smul hV γ.contDiffLC c hj ⟨p.1.2, mem_univ _⟩

/-- `γ ↦ (d^(j)γ)_{j ≤ k}`. -/
def toPi : ContDiffLCMap F k V hV →ₗ[ℝ] ∀ j : Fin (k + 1), C(V × (Fin j → E), F) :=
  LinearMap.pi fun j ↦ iteratedDL j (Nat.lt_succ_iff.mp j.2)

theorem toPi_injective : Function.Injective (toPi (F := F) (k := k) (hV := hV)) := by
  intro γ η h
  ext x
  by_cases hx : x ∈ V
  · exact congrArg (fun φ ↦ φ 0 (⟨x, hx⟩, Fin.elim0)) h
  · rw [γ.apply_of_notMem hx, η.apply_of_notMem hx]

/-- **The compact-open `C^k` topology** on `C^k(V, F)` ([GN26, Definition 1.7.10]): the
initial topology with respect to the maps `d^(j) : C^k(V, F) → C(V × E^j, F)`, `j ≤ k`. -/
instance : TopologicalSpace (ContDiffLCMap F k V hV) :=
  .induced toPi inferInstance

theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (F := F) (k := k) (hV := hV)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

instance : IsTopologicalAddGroup (ContDiffLCMap F k V hV) :=
  isTopologicalAddGroup_induced toPi

instance : ContinuousSMul ℝ (ContDiffLCMap F k V hV) :=
  continuousSMul_induced toPi

instance : LocallyConvexSpace ℝ (ContDiffLCMap F k V hV) :=
  LocallyConvexSpace.induced toPi

instance : T2Space (ContDiffLCMap F k V hV) :=
  isEmbedding_toPi.t2Space

theorem continuous_toPi : Continuous (toPi (F := F) (k := k) (hV := hV)) :=
  continuous_induced_dom

theorem continuous_iteratedD (j : ℕ) (hj : j ≤ k) :
    Continuous (iteratedD (F := F) (hV := hV) j hj) :=
  (continuous_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1))).comp continuous_toPi

/-- `d^(j) : C^k(V, F) → C(V × E^j, F)` as a continuous linear map. -/
def iteratedDCLM (j : ℕ) (hj : j ≤ k) : ContDiffLCMap F k V hV →L[ℝ] C(V × (Fin j → E), F) :=
  ⟨iteratedDL j hj, continuous_iteratedD j hj⟩

/-- A map into `C^k(V, F)` is continuous if and only if its compositions with the
differentials `d^(j)`, `j ≤ k`, are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → ContDiffLCMap F k V hV} :
    Continuous φ ↔ ∀ j (hj : j ≤ k), Continuous fun x ↦ iteratedD j hj (φ x) := by
  refine ⟨fun h j hj ↦ (continuous_iteratedD j hj).comp h, fun h ↦ ?_⟩
  refine continuous_induced_rng.2 (continuous_pi fun j ↦ ?_)
  exact h j (Nat.lt_succ_iff.mp j.2)

end ContDiffLCMap

end Space

/-! ### The partial maps `f^∨(x) = f(x, ·)` -/

section Curry

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {U : Set E₁} {V : Set E₂}

open scoped Classical in
/-- The partial map `f^∨(x) = f(x, ·) ∈ C^ℓ(V, F)` of a `C^{k,ℓ}` map `f` on `U × V`
([GN26, Lemma 1.7.18]), extended by `0` outside `V`; it is `0` for `x ∉ U`. -/
def curryLC {f : E₁ × E₂ → F} (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ k ℓ f U V) (x : E₁) : ContDiffLCMap F ℓ V hV :=
  if hx : x ∈ U then
    ContDiffLCMap.mk (fun y ↦ if y ∈ V then f (x, y) else 0)
      ((hf.contDiffLC_right hU hV hx).1.congr fun y hy ↦ by simp [hy])
      fun y hy ↦ by simp [hy]
  else 0

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
theorem curryLC_apply {f : E₁ × E₂ → F} (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ k ℓ f U V) {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V) :
    curryLC hU hV hf x y = f (x, y) := by
  simp [curryLC, hx, hy]

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- `d^(j)(f^∨(x))(y, w) = d^(0,j) f(x, y, w)` for `x ∈ U`, `y ∈ V` ([GN26, (1.85)]). -/
theorem iteratedDLC_curryLC {f : E₁ × E₂ → F} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLC₂ k ℓ f U V) {x : E₁} (hx : x ∈ U) {j : ℕ}
    (hj : j ≤ ℓ) : EqOn (iteratedDLC j (curryLC hU hV hf x) V)
      (fun p ↦ iteratedDLC₂ 0 j f U V ((x, p.1), Fin.elim0, p.2)) (V ×ˢ univ) := by
  have h1 := iteratedDLC_congr hV (curryLC hU hV hf x).contDiffLC
    (g := fun y ↦ f (x, y)) (fun y hy ↦ curryLC_apply hU hV hf hx hy) hj
  exact fun p hp ↦ (h1 hp).trans ((hf.contDiffLC_right hU hV hx).2 j hj _
    (hf.continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) hj)
    (iteratedDLC₂_eqOn_interior 0 j f U V) hp)

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- `f^∨ : U → C^ℓ(V, F)` is continuous ([GN26, proof of Theorem 1.7.30]). -/
theorem continuousOn_curryLC {f : E₁ × E₂ → F} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLC₂ k ℓ f U V) :
    ContinuousOn (curryLC hU hV hf) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine ContDiffLCMap.continuous_iff.2 fun j hj ↦ ?_
  let ζ : C(U × (V × (Fin j → E₂)), F) :=
    ⟨fun q ↦ iteratedDLC₂ 0 j f U V (((q.1 : E₁), (q.2.1 : E₂)), Fin.elim0, q.2.2),
      (hf.continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) hj).comp_continuous (by fun_prop)
        fun q ↦ ⟨⟨q.1.2, q.2.1.2⟩, mem_univ _⟩⟩
  refine ζ.curry.continuous.congr fun q ↦ ContinuousMap.ext fun p ↦ ?_
  exact (iteratedDLC_curryLC hU hV hf q.2 hj
    (show ((p.1 : E₂), p.2) ∈ V ×ˢ univ from ⟨p.1.2, mem_univ _⟩)).symm

/-- **The derivative of `f^∨`**: at `x ∈ U⁰`, `f^∨` has directional derivative
`(d^(1,0) f)^∨(x, a) = d^(1,0) f(x, ·, a)` in `C^ℓ(V, F)` in the direction `a`
([GN26, proof of Theorem 1.7.30]). -/
theorem hasDirDerivAt_curryLC {f : E₁ × E₂ → F} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLC₂ (k + 1) ℓ f U V) {x : E₁} (hx : x ∈ interior U)
    (a : E₁) : HasDirDerivAt (curryLC hU hV hf) x a
      (curryLC hU.prod_univ hV (hf.contDiffLC₂_partialDLC₁ hU hV) (x, a)) := by
  rw [HasDirDerivAt, ContDiffLCMap.isEmbedding_toPi.tendsto_nhds_iff, tendsto_pi_nhds]
  intro j
  have hj : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp j.2
  have e : ∀ γ : ContDiffLCMap F ℓ V hV, ContDiffLCMap.toPi γ j = ContDiffLCMap.iteratedD j hj γ :=
    fun _ ↦ rfl
  simp only [Function.comp_def, e, show ContDiffLCMap.iteratedD (F := F) (hV := hV) j hj =
    ⇑(ContDiffLCMap.iteratedDL j hj) from rfl, map_smul, map_sub]
  rw [ContinuousMap.tendsto_nhds_compactOpen]
  intro K hK N hN hKN
  have hD := fun i (hi : i ≤ k + 1) ↦ hf.continuousOn_iteratedDLC₂ hU hV hi hj
  have ev := eventually_forall_quotient_mem_param isOpen_interior (h := a)
    (S := V ×ˢ (univ : Set (Fin j → E₂)))
    (g := fun q : E₁ × (E₂ × (Fin j → E₂)) ↦
      iteratedDLC₂ 0 j f U V ((q.1, q.2.1), Fin.elim0, q.2.2))
    (D := fun q ↦ iteratedDLC₂ 1 j f U V ((q.1, q.2.1), fun _ ↦ a, q.2.2))
    (fun q hq z hz ↦ ?_) ((hD 1 (by omega)).comp (by fun_prop)
      fun q hq ↦ ⟨⟨interior_subset hq.1, hq.2.1⟩, mem_univ _⟩)
    (P := fun p : V × (Fin j → E₂) ↦ (x, ((p.1 : E₂), p.2))) (by fun_prop) hK
    (fun p _ ↦ ⟨hx, p.1.2, mem_univ _⟩) hN (fun p hp ↦ by
      have := hKN hp
      simp only [ContDiffLCMap.iteratedDL, LinearMap.coe_mk, AddHom.coe_mk,
        ContDiffLCMap.iteratedD_apply] at this
      rw [iteratedDLC_curryLC hU.prod_univ hV _ (show (x, a) ∈ U ×ˢ univ from
        ⟨interior_subset hx, mem_univ _⟩) hj
        (show ((p.1 : E₂), p.2) ∈ V ×ˢ univ from ⟨p.1.2, mem_univ _⟩)] at this
      beta_reduce at this
      rw [hf.iteratedDLC₂_zero_partialDLC₁ hU hV hj (interior_subset hx) p.1.2] at this
      exact this)
  · have hxU : ∀ᶠ t : ℝ in 𝓝 0, x + t • a ∈ interior U := by
      have hc : Continuous fun t : ℝ ↦ x + t • a := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this (isOpen_interior.mem_nhds hx)
    filter_upwards [nhdsWithin_le_nhds ev, nhdsWithin_le_nhds hxU, self_mem_nhdsWithin]
      with t ht htU ht0 p hp
    have h := ht p hp ht0
    simp only [ContDiffLCMap.iteratedDL, LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContDiffLCMap.iteratedD_apply]
    rw [iteratedDLC_curryLC hU hV hf (interior_subset htU) hj
      (show ((p.1 : E₂), p.2) ∈ V ×ˢ univ from ⟨p.1.2, mem_univ _⟩),
      iteratedDLC_curryLC hU hV hf (interior_subset hx) hj
      (show ((p.1 : E₂), p.2) ∈ V ×ˢ univ from ⟨p.1.2, mem_univ _⟩)]
    exact h
  · -- the derivative of `x ↦ d^(0,j) f(x, y, w)` at interior points, for `y ∈ V`
    obtain ⟨h1, h2⟩ := hf.contDiffLC_left hU hV hj hz.1 z.2
      (hf.continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) hj) (iteratedDLC₂_eqOn_interior 0 j f U V)
    have h3 := h1.hasDirDerivAt hq a
    rw [← dLC_of_mem_interior _ (p := (q, a)) hq] at h3
    have h4 := h2 1 (by omega) _ (hD 1 (by omega)) (iteratedDLC₂_eqOn_interior 1 j f U V)
      (show (q, fun _ ↦ a) ∈ U ×ˢ univ from ⟨interior_subset hq, mem_univ _⟩)
    have h5 : dLC (fun x ↦ iteratedDLC₂ 0 j f U V ((x, z.1), Fin.elim0, z.2)) U (q, a) =
        iteratedDLC₂ 1 j f U V ((q, z.1), fun _ ↦ a, z.2) := h4
    rw [h5] at h3
    exact h3

/-- **[GN26, Theorem 1.7.30]** (first part), for sets with dense interior: if `f` is
`C^{k,ℓ}` on `U × V`, then `f^∨ : U → C^ℓ(V, F)`, `x ↦ f(x, ·)`, is `C^k`. -/
theorem ContDiffLC₂.contDiffLC_curryLC {f : E₁ × E₂ → F} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLC₂ k ℓ f U V) :
    ContDiffLC k (curryLC hU hV hf) U := by
  induction k generalizing E₁ f U with
  | zero => exact continuousOn_curryLC hU hV hf
  | succ k ih =>
    exact (ContDiffLC.of_hasDirDerivAt hU (continuousOn_curryLC hU hV hf)
      (fun x hx a ↦ hasDirDerivAt_curryLC hU hV hf hx a)
      (ih hU.prod_univ (hf.contDiffLC₂_partialDLC₁ hU hV))).1

end Curry

/-! ### Linear operations on `C^{k,ℓ}` maps -/

section Linear₂

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {U : Set E₁} {V : Set E₂} {f g : E₁ × E₂ → F}

/-- Sums of `C^{k,ℓ}` maps are `C^{k,ℓ}`. -/
theorem ContDiffLC₂.add (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ k ℓ f U V) (hg : ContDiffLC₂ k ℓ g U V) :
    ContDiffLC₂ k ℓ (fun p ↦ f p + g p) U V :=
  ((hf.prodMk hU hV hg).clm_comp (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F)
    hU hV).congr fun _ _ ↦ rfl

/-- Multiples of `C^{k,ℓ}` maps are `C^{k,ℓ}`. -/
theorem ContDiffLC₂.const_smul (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ k ℓ f U V) (c : ℝ) : ContDiffLC₂ k ℓ (fun p ↦ c • f p) U V :=
  (hf.clm_comp (c • ContinuousLinearMap.id ℝ F) hU hV).congr fun _ _ ↦ rfl

/-- Constant maps are `C^{k,ℓ}`. -/
theorem contDiffLC₂_const (hU : HasDenseInterior U) (hV : HasDenseInterior V) (c : F) :
    ContDiffLC₂ k ℓ (fun _ ↦ c) U V :=
  (contDiffLC_const (k + ℓ) c (hU.prod hV)).contDiffLC₂

omit [LocallyConvexSpace ℝ F] in
/-- `d^(i,j)(f + g) = d^(i,j) f + d^(i,j) g` on `U × V × E₁^i × E₂^j`. -/
theorem iteratedDLC₂_add (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ k ℓ f U V) (hg : ContDiffLC₂ k ℓ g U V) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ ℓ) : EqOn (iteratedDLC₂ i j (fun p ↦ f p + g p) U V)
      (fun q ↦ iteratedDLC₂ i j f U V q + iteratedDLC₂ i j g U V q) ((U ×ˢ V) ×ˢ univ) := by
  refine iteratedDLC₂_eqOn_of_continuousOn hU hV ((hf.continuousOn_iteratedDLC₂ hU hV hi hj).add
    (hg.continuousOn_iteratedDLC₂ hU hV hi hj)) ?_
  rintro ⟨⟨x, y⟩, v, w⟩ hp
  change iteratedDLC₂ i j f U V _ + iteratedDLC₂ i j g U V _ = _
  rw [iteratedDLC₂_eqOn_interior i j f U V hp, iteratedDLC₂_eqOn_interior i j g U V hp]
  exact (hf.2.1.iteratedDMB₂_add isOpen_interior isOpen_interior hg.2.1 hi hj hp.1.1 hp.1.2 v
    w).symm

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- `d^(i,j)(c • f) = c • d^(i,j) f` on `U × V × E₁^i × E₂^j`. -/
theorem iteratedDLC₂_const_smul (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ k ℓ f U V) (c : ℝ) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ) :
    EqOn (iteratedDLC₂ i j (fun p ↦ c • f p) U V) (fun q ↦ c • iteratedDLC₂ i j f U V q)
      ((U ×ˢ V) ×ˢ univ) := by
  refine iteratedDLC₂_eqOn_of_continuousOn hU hV
    ((hf.continuousOn_iteratedDLC₂ hU hV hi hj).const_smul c) ?_
  rintro ⟨⟨x, y⟩, v, w⟩ hp
  change c • iteratedDLC₂ i j f U V _ = _
  rw [iteratedDLC₂_eqOn_interior i j f U V hp]
  exact (hf.2.1.iteratedDMB₂_const_smul isOpen_interior isOpen_interior c hi hj hp.1.1 hp.1.2 v
    w).symm

end Linear₂

/-! ### The space `C^{k,ℓ}(U × V, F)` for `U`, `V` with dense interior -/

section Space₂

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (F) in
/-- The `C^{k,ℓ}` maps on `U × V`, extended by `0` outside `U × V`, as a submodule. -/
def contDiffLCSubmodule₂ (k ℓ : ℕ) (U : Set E₁) (hU : HasDenseInterior U) (V : Set E₂)
    (hV : HasDenseInterior V) : Submodule ℝ (E₁ × E₂ → F) where
  carrier := {f | ContDiffLC₂ k ℓ f U V ∧ ∀ p ∉ U ×ˢ V, f p = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add hU hV hg.1, fun p hp ↦ by simp [hf.2 p hp, hg.2 p hp]⟩
  zero_mem' := ⟨contDiffLC₂_const hU hV 0, fun _ _ ↦ rfl⟩
  smul_mem' c f hf := ⟨hf.1.const_smul hU hV c, fun p hp ↦ by simp [hf.2 p hp]⟩

variable (F) in
/-- **The space `C^{k,ℓ}(U × V, F)`** for `U`, `V` with dense interior, with the compact-open
`C^{k,ℓ}` topology ([GN26, Definition 1.7.17]). -/
def ContDiffLCMap₂ (k ℓ : ℕ) (U : Set E₁) (hU : HasDenseInterior U) (V : Set E₂)
    (hV : HasDenseInterior V) : Type (max u v) :=
  contDiffLCSubmodule₂ F k ℓ U hU V hV

namespace ContDiffLCMap₂

variable {k ℓ : ℕ} {U : Set E₁} {hU : HasDenseInterior U} {V : Set E₂} {hV : HasDenseInterior V}

instance : AddCommGroup (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  inferInstanceAs (AddCommGroup (contDiffLCSubmodule₂ F k ℓ U hU V hV))

instance : Module ℝ (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  inferInstanceAs (Module ℝ (contDiffLCSubmodule₂ F k ℓ U hU V hV))

instance : FunLike (ContDiffLCMap₂ F k ℓ U hU V hV) (E₁ × E₂) F where
  coe γ := Subtype.val (γ : contDiffLCSubmodule₂ F k ℓ U hU V hV)
  coe_injective := Subtype.val_injective

/-- The element of `C^{k,ℓ}(U × V, F)` given by a `C^{k,ℓ}` map vanishing outside `U × V`. -/
def mk (f : E₁ × E₂ → F) (hf : ContDiffLC₂ k ℓ f U V) (h0 : ∀ p ∉ U ×ˢ V, f p = 0) :
    ContDiffLCMap₂ F k ℓ U hU V hV :=
  ⟨f, hf, h0⟩

@[simp]
theorem coe_mk (f : E₁ × E₂ → F) (hf : ContDiffLC₂ k ℓ f U V) (h0 : ∀ p ∉ U ×ˢ V, f p = 0) :
    ⇑(mk (hU := hU) (hV := hV) f hf h0) = f :=
  rfl

theorem contDiffLC₂ (γ : ContDiffLCMap₂ F k ℓ U hU V hV) : ContDiffLC₂ k ℓ γ U V :=
  (γ : contDiffLCSubmodule₂ F k ℓ U hU V hV).2.1

theorem apply_of_notMem (γ : ContDiffLCMap₂ F k ℓ U hU V hV) {p : E₁ × E₂} (hp : p ∉ U ×ˢ V) :
    γ p = 0 :=
  (γ : contDiffLCSubmodule₂ F k ℓ U hU V hV).2.2 p hp

@[ext]
theorem ext {γ η : ContDiffLCMap₂ F k ℓ U hU V hV} (h : ∀ p, γ p = η p) : γ = η :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_add (γ η : ContDiffLCMap₂ F k ℓ U hU V hV) : ⇑(γ + η) = γ + η :=
  rfl

@[simp]
theorem coe_smul (c : ℝ) (γ : ContDiffLCMap₂ F k ℓ U hU V hV) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The mixed differential `d^(i,j)γ ∈ C(U × V × E₁^i × E₂^j, F)`, `i ≤ k`, `j ≤ ℓ`. -/
def iteratedD₂ (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) (γ : ContDiffLCMap₂ F k ℓ U hU V hV) :
    C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) where
  toFun p := iteratedDLC₂ i j γ U V (((p.1.1 : E₁), (p.1.2 : E₂)), p.2.1, p.2.2)
  continuous_toFun := (γ.contDiffLC₂.continuousOn_iteratedDLC₂ hU hV hi hj).comp_continuous
    (by fun_prop) fun p ↦ ⟨⟨p.1.1.2, p.1.2.2⟩, mem_univ _⟩

@[simp]
theorem iteratedD₂_apply (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) (γ : ContDiffLCMap₂ F k ℓ U hU V hV)
    (p : (U × V) × (Fin i → E₁) × (Fin j → E₂)) :
    iteratedD₂ i j hi hj γ p =
      iteratedDLC₂ i j γ U V (((p.1.1 : E₁), (p.1.2 : E₂)), p.2.1, p.2.2) :=
  rfl

/-- `d^(i,j)` as a linear map. -/
def iteratedDL₂ (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) :
    ContDiffLCMap₂ F k ℓ U hU V hV →ₗ[ℝ] C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) where
  toFun := iteratedD₂ i j hi hj
  map_add' γ η := by
    ext p
    exact iteratedDLC₂_add hU hV γ.contDiffLC₂ η.contDiffLC₂ hi hj
      ⟨⟨p.1.1.2, p.1.2.2⟩, mem_univ _⟩
  map_smul' c γ := by
    ext p
    exact iteratedDLC₂_const_smul hU hV γ.contDiffLC₂ c hi hj ⟨⟨p.1.1.2, p.1.2.2⟩, mem_univ _⟩

/-- `γ ↦ (d^(i,j)γ)_{i ≤ k, j ≤ ℓ}`. -/
def toPi : ContDiffLCMap₂ F k ℓ U hU V hV →ₗ[ℝ]
    ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)), C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    iteratedDL₂ i j (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)

theorem toPi_injective :
    Function.Injective (toPi (F := F) (k := k) (ℓ := ℓ) (hU := hU) (hV := hV)) := by
  intro γ η h
  ext p
  by_cases hp : p ∈ U ×ˢ V
  · have := congrArg (fun φ ↦ φ 0 0 ((⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), Fin.elim0, Fin.elim0)) h
    simp only [toPi, LinearMap.pi_apply, iteratedDL₂, LinearMap.coe_mk, AddHom.coe_mk,
      iteratedD₂_apply] at this
    have hD0 := fun (δ : ContDiffLCMap₂ F k ℓ U hU V hV) ↦ iteratedDLC₂_eqOn_of_continuousOn
      (i := 0) (j := 0) hU hV (δ.contDiffLC₂.1.comp continuous_fst.continuousOn fun q hq ↦ hq.1)
      (fun _ _ ↦ rfl) (show ((p.1, p.2), (Fin.elim0 : Fin 0 → E₁), (Fin.elim0 : Fin 0 → E₂)) ∈ _
        from ⟨hp, mem_univ _⟩)
    exact (hD0 γ).symm.trans (this.trans (hD0 η))
  · rw [γ.apply_of_notMem hp, η.apply_of_notMem hp]

/-- **The compact-open `C^{k,ℓ}` topology** ([GN26, Definition 1.7.17]). -/
instance : TopologicalSpace (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  .induced toPi inferInstance

theorem isEmbedding_toPi :
    Topology.IsEmbedding (toPi (F := F) (k := k) (ℓ := ℓ) (hU := hU) (hV := hV)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

instance : IsTopologicalAddGroup (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  isTopologicalAddGroup_induced toPi

instance : ContinuousSMul ℝ (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  continuousSMul_induced toPi

instance : LocallyConvexSpace ℝ (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  LocallyConvexSpace.induced toPi

instance : T2Space (ContDiffLCMap₂ F k ℓ U hU V hV) :=
  isEmbedding_toPi.t2Space

theorem continuous_iteratedD₂ (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) :
    Continuous (iteratedD₂ (F := F) (hU := hU) (hV := hV) i j hi hj) := by
  have h : Continuous (toPi (F := F) (k := k) (ℓ := ℓ) (hU := hU) (hV := hV)) :=
    continuous_induced_dom
  exact (continuous_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (ℓ + 1))).comp
    ((continuous_apply (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (k + 1))).comp h)

end ContDiffLCMap₂

end Space₂

/-! ### The curried map and the exponential law -/

section ExpLaw

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {U : Set E₁} {V : Set E₂}

/-- **[GN26, (1.98)]**, for sets with dense interior:
`d^(j)(d^(i)(f^∨)(x, v))(y, w) = d^(i,j) f(x, y, v, w)` for `x ∈ U`, `y ∈ V`. -/
theorem iteratedDLC_iteratedDLC_curryLC {f : E₁ × E₂ → F} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) (hf : ContDiffLC₂ k ℓ f U V) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ)
    {y : E₂} (hy : y ∈ V) (w : Fin j → E₂) :
    EqOn (fun q : E₁ × (Fin i → E₁) ↦
        iteratedDLC j (iteratedDLC (F := ContDiffLCMap F ℓ V hV) i (curryLC hU hV hf) U q) V (y, w))
      (fun q ↦ iteratedDLC₂ i j f U V ((q.1, y), q.2, w)) (U ×ˢ univ) := by
  let Λ : ContDiffLCMap F ℓ V hV →L[ℝ] F := (ContinuousMap.evalCLM ℝ ((⟨y, hy⟩ : V), w)).comp
    (ContDiffLCMap.iteratedDCLM j hj)
  have hΛ : ∀ γ : ContDiffLCMap F ℓ V hV, Λ γ = iteratedDLC j γ V (y, w) := fun _ ↦ rfl
  have hc := hf.contDiffLC_curryLC hU hV
  obtain ⟨h1, h2⟩ := hf.contDiffLC_left hU hV hj hy w
    (hf.continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) hj) (iteratedDLC₂_eqOn_interior 0 j f U V)
  have hφ : ∀ x ∈ U, Λ (curryLC hU hV hf x) = iteratedDLC₂ 0 j f U V ((x, y), Fin.elim0, w) :=
    fun x hx ↦ (hΛ _).trans (iteratedDLC_curryLC hU hV hf hx hj
      (show (y, w) ∈ V ×ˢ univ from ⟨hy, mem_univ _⟩))
  refine iteratedDLC_unique hU (f := fun x ↦ iteratedDLC₂ 0 j f U V ((x, y), Fin.elim0, w))
    (Λ.continuous.comp_continuousOn (hc.continuousOn_iteratedDLC hi))
    ((hf.continuousOn_iteratedDLC₂ hU hV hi hj).comp (by fun_prop)
      fun q hq ↦ ⟨⟨hq.1, hy⟩, mem_univ _⟩) (fun q hq ↦ ?_) (fun q hq ↦ ?_)
  · change Λ (iteratedDLC (F := ContDiffLCMap F ℓ V hV) i (curryLC hU hV hf) U q) = _
    rw [iteratedDLC_eq_iteratedDMB hq.1, ← iteratedDMB_clm_comp isOpen_interior
      hc.contDiffMBOn_interior Λ i hi q.1 hq.1 q.2]
    exact iteratedDMB_congr_of_eventuallyEq i (Filter.eventually_of_mem
      (isOpen_interior.mem_nhds hq.1) fun x hx ↦ hφ x (interior_subset hx)) q.2
  · have h3 := h2 i hi _ (hf.continuousOn_iteratedDLC₂ hU hV hi hj)
      (iteratedDLC₂_eqOn_interior i j f U V) (show q ∈ U ×ˢ univ from
        ⟨interior_subset hq.1, mem_univ _⟩)
    exact h3.symm.trans (iteratedDLC_eq_iteratedDMB hq.1)

namespace ContDiffLCMap₂

variable {hU : HasDenseInterior U} {hV : HasDenseInterior V}

/-- **The curried map** `Φ(f) = f^∨ ∈ C^k(U, C^ℓ(V, F))` of `f ∈ C^{k,ℓ}(U × V, F)`
([GN26, Theorem 1.7.30]). -/
def curry (f : ContDiffLCMap₂ F k ℓ U hU V hV) : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU :=
  ContDiffLCMap.mk (curryLC hU hV f.contDiffLC₂) (f.contDiffLC₂.contDiffLC_curryLC hU hV)
    fun x hx ↦ by simp [curryLC, hx]

/-- `Φ(f)(x)(y) = f(x, y)`. -/
@[simp]
theorem curry_apply_apply (f : ContDiffLCMap₂ F k ℓ U hU V hV) (x : E₁) (y : E₂) :
    curry f x y = f (x, y) := by
  change curryLC hU hV f.contDiffLC₂ x y = f (x, y)
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ V
    · exact curryLC_apply hU hV _ hx hy
    · simp [curryLC, hx, hy, f.apply_of_notMem (p := (x, y)) fun h ↦ hy h.2]
  · simp [curryLC, hx, f.apply_of_notMem (p := (x, y)) fun h ↦ hx h.1]

/-- **[GN26, (1.98)]**: `d^(j)(d^(i)(f^∨)(x, v))(y, w) = d^(i,j) f(x, y, v, w)`. -/
theorem iteratedD_iteratedD_curry (f : ContDiffLCMap₂ F k ℓ U hU V hV) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ ℓ) (q : U × (Fin i → E₁)) (p : V × (Fin j → E₂)) :
    ContDiffLCMap.iteratedD j hj (ContDiffLCMap.iteratedD i hi (curry f) q) p =
      iteratedDLC₂ i j f U V (((q.1 : E₁), (p.1 : E₂)), q.2, p.2) :=
  iteratedDLC_iteratedDLC_curryLC hU hV f.contDiffLC₂ hi hj p.1.2 p.2
    (show ((q.1 : E₁), q.2) ∈ U ×ˢ univ from ⟨q.1.2, mem_univ _⟩)

/-- `Φ : f ↦ f^∨` as a linear map. -/
def curryLM : ContDiffLCMap₂ F k ℓ U hU V hV →ₗ[ℝ] ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU
    where
  toFun := curry
  map_add' _ _ := ContDiffLCMap.ext fun _ ↦ ContDiffLCMap.ext fun _ ↦ by
    simp only [ContDiffLCMap.coe_add, Pi.add_apply, curry_apply_apply, coe_add]
  map_smul' _ _ := ContDiffLCMap.ext fun _ ↦ ContDiffLCMap.ext fun _ ↦ by
    simp only [ContDiffLCMap.coe_smul, Pi.smul_apply, curry_apply_apply, coe_smul,
      RingHom.id_apply]

/-- `Φ` is injective. -/
theorem curry_injective :
    Function.Injective (curry (F := F) (k := k) (ℓ := ℓ) (hU := hU) (hV := hV)) :=
  fun f g h ↦ ext fun p ↦ by
    simpa using congrArg (fun γ : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU ↦ γ p.1 p.2) h

/-- `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))` is continuous. -/
theorem continuous_curry :
    Continuous (curry (F := F) (k := k) (ℓ := ℓ) (hU := hU) (hV := hV)) := by
  refine ContDiffLCMap.continuous_iff.2 fun i hi ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K hK ↦ ?_
  refine ContDiffLCMap.continuous_iff.2 fun j hj ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K' hK' ↦ ?_
  let σ : (U × (Fin i → E₁)) × (V × (Fin j → E₂)) → (U × V) × (Fin i → E₁) × (Fin j → E₂) :=
    fun z ↦ ((z.1.1, z.2.1), z.1.2, z.2.2)
  have hσ : Continuous σ := by fun_prop
  have h := ContinuousMap.continuous_eval_comp_restrict (W := F) hσ (hK.prod hK')
  have h2 : Continuous fun r : (ContDiffLCMap₂ F k ℓ U hU V hV × K) × K' ↦
      (iteratedD₂ i j hi hj r.1.1, (⟨((r.1.2 : U × (Fin i → E₁)), (r.2 : V × (Fin j → E₂))),
        ⟨r.1.2.2, r.2.2⟩⟩ : (K ×ˢ K' : Set _))) :=
    ((continuous_iteratedD₂ i j hi hj).comp continuous_fst.fst).prodMk (by fun_prop)
  refine (h.comp h2).congr fun r ↦ ?_
  exact (iteratedD_iteratedD_curry r.1.1 hi hj _ _).symm

/-- If `φ : X → C^{k,ℓ}(U × V, F)` becomes continuous after composition with `Φ`, then all its
mixed differentials are continuous. -/
theorem continuous_iteratedD₂_of_continuous_curry {X : Type*} [tX : TopologicalSpace X]
    {φ : X → ContDiffLCMap₂ F k ℓ U hU V hV} (hφ : Continuous fun x ↦ curry (φ x)) (i j : ℕ)
    (hi : i ≤ k) (hj : j ≤ ℓ) : Continuous fun x ↦ iteratedD₂ i j hi hj (φ x) := by
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K hK ↦ ?_
  let σ₁ : (U × V) × (Fin i → E₁) × (Fin j → E₂) → U × (Fin i → E₁) := fun z ↦ (z.1.1, z.2.1)
  let σ₂ : (U × V) × (Fin i → E₁) × (Fin j → E₂) → V × (Fin j → E₂) := fun z ↦ (z.1.2, z.2.2)
  have hA : Continuous fun q : X × K ↦
      ContDiffLCMap.iteratedD i hi (curry (φ q.1)) (σ₁ q.2) :=
    (ContinuousMap.continuous_eval_comp_restrict (W := ContDiffLCMap F ℓ V hV)
      (by fun_prop : Continuous σ₁) hK).comp
      (((ContDiffLCMap.continuous_iteratedD i hi).comp (hφ.comp continuous_fst)).prodMk
        continuous_snd)
  have hB : Continuous fun q : X × K ↦ ContDiffLCMap.iteratedD j hj
      (ContDiffLCMap.iteratedD i hi (curry (φ q.1)) (σ₁ q.2)) (σ₂ q.2) :=
    (ContinuousMap.continuous_eval_comp_restrict (W := F) (by fun_prop : Continuous σ₂) hK).comp
      (((ContDiffLCMap.continuous_iteratedD j hj).comp hA).prodMk continuous_snd)
  refine hB.congr fun q ↦ ?_
  exact iteratedD_iteratedD_curry (φ q.1) hi hj _ _

/-- If `φ : X → C^{k,ℓ}(U × V, F)` becomes continuous after composition with `Φ`, then so does
`γ ↦ (d^(i,j)γ)_{i,j}`. -/
theorem continuous_toPi_of_continuous_curry {X : Type*} [tX : TopologicalSpace X]
    {φ : X → ContDiffLCMap₂ F k ℓ U hU V hV} (hφ : Continuous fun x ↦ curry (φ x)) :
    Continuous fun x ↦ toPi (φ x) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_iteratedD₂_of_continuous_curry hφ i j
    (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)

/-- **[GN26, Theorem 1.7.30]** (second part), for sets with dense interior:
`Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`, `f ↦ f^∨`, is a topological embedding. -/
theorem isEmbedding_curry :
    Topology.IsEmbedding (curry (F := F) (k := k) (ℓ := ℓ) (hU := hU) (hV := hV)) := by
  refine ⟨(Topology.isInducing_iff _).2 ?_, curry_injective⟩
  refine le_antisymm (continuous_iff_le_induced.1 continuous_curry) ?_
  have h := continuous_toPi_of_continuous_curry (X := ContDiffLCMap₂ F k ℓ U hU V hV)
    (tX := TopologicalSpace.induced curry inferInstance) (φ := id) continuous_induced_dom
  exact continuous_iff_le_induced.1 h

/-- `Φ` as a continuous linear map. -/
def curryCLM : ContDiffLCMap₂ F k ℓ U hU V hV →L[ℝ] ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU :=
  ⟨curryLM, continuous_curry⟩

end ContDiffLCMap₂

end ExpLaw

/-! ### `k_ℝ`-spaces -/

section KRSpace

/-- **[GN26, Remark A.6.15(c), p. 875]**: `X` is a *`k_ℝ`-space* if every real-valued
function on `X` whose restrictions to compact subsets are continuous is continuous. Glöckner–Neeb
also require `X` to be Hausdorff, which is not needed here. Every k-space is a `k_ℝ`-space
([GN26, Remark A.6.16(a), p. 875]); locally compact and first countable (e.g. metrizable)
spaces are k-spaces (`KRSpace.of_compactlyCoherentSpace`, `KRSpace.of_firstCountableTopology`). -/
def KRSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : X → ℝ, (∀ K : Set X, IsCompact K → ContinuousOn f K) → Continuous f

/-- On a `k_ℝ`-space, a map into a completely regular space whose restrictions to compact sets
are continuous is continuous ([GN26, Remark A.6.15(c)]). -/
theorem KRSpace.continuous_of_continuousOn {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompletelyRegularSpace Y] (hX : KRSpace X) {h : X → Y}
    (hh : ∀ K : Set X, IsCompact K → ContinuousOn h K) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun x W hW ↦ ?_
  obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
  obtain ⟨φ, hφc, hφx, hφK⟩ := CompletelyRegularSpace.completely_regular (h x) W'ᶜ
    hW'o.isClosed_compl fun h' ↦ h' hxW'
  have hc : Continuous fun z ↦ (φ (h z) : ℝ) :=
    hX _ fun K hK ↦ (continuous_subtype_val.comp hφc).comp_continuousOn (hh K hK)
  have hmem : (fun z ↦ (φ (h z) : ℝ)) ⁻¹' Iio 1 ∈ 𝓝 x :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp [hφx]))
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hmem fun z hz ↦ hW'W ?_
  by_contra hzW
  have h1 := hφK hzW
  simp only [mem_preimage, mem_Iio] at hz
  rw [h1] at hz
  simp at hz

/-- On a `k_ℝ`-space, the evaluation of a continuous family of continuous maps at a continuously
varying point is continuous: on a compact set `K`, the points lie in the compact set `b(K)`, where
the evaluation is continuous. -/
theorem KRSpace.continuous_eval {Z X Y : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    [TopologicalSpace Y] [CompletelyRegularSpace Y] (hZ : KRSpace Z)
    {Γ : Z → C(X, Y)} {b : Z → X} (hΓ : Continuous Γ) (hb : Continuous b) :
    Continuous fun z ↦ Γ z (b z) := by
  refine hZ.continuous_of_continuousOn fun K hK ↦ ?_
  have : CompactSpace (b '' K) := isCompact_iff_compactSpace.1 (hK.image hb)
  rw [continuousOn_iff_continuous_domRestrict]
  have h1 : Continuous fun z : K ↦ (Γ z).restrict (b '' K) :=
    (ContinuousMap.continuous_restrict _).comp (hΓ.comp continuous_subtype_val)
  have h2 : Continuous fun z : K ↦ (⟨b z, mem_image_of_mem b z.2⟩ : b '' K) :=
    (hb.comp continuous_subtype_val).subtype_mk _
  exact (ContinuousEval.continuous_eval.comp (h1.prodMk h2)).congr fun z ↦ rfl

/-- Compactly coherent spaces (in particular k-spaces, locally compact spaces and sequential
spaces) are `k_ℝ`-spaces: preimages of open sets meet each compact set in a relatively open
set. -/
theorem KRSpace.of_compactlyCoherentSpace (X : Type*) [TopologicalSpace X]
    [CompactlyCoherentSpace X] : KRSpace X := fun _ hf ↦
  continuous_def.2 fun O hO ↦ CompactlyCoherentSpace.isOpen_iff.2 fun K hK ↦
    (continuousOn_iff_continuous_domRestrict.1 (hf K hK)).isOpen_preimage O hO

/-- First countable spaces (in particular metrizable spaces) are `k_ℝ`-spaces. -/
theorem KRSpace.of_firstCountableTopology (X : Type*) [TopologicalSpace X]
    [FirstCountableTopology X] : KRSpace X :=
  KRSpace.of_compactlyCoherentSpace X

/-- Topological groups are completely regular: their topology comes from a uniform structure. -/
theorem completelyRegularSpace_of_isTopologicalAddGroup (G : Type*) [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] : CompletelyRegularSpace G := by
  let := IsTopologicalAddGroup.rightUniformSpace G
  infer_instance

end KRSpace

/-! ### The exponential law for locally compact `V`, or under `k_ℝ` hypotheses -/

section LocallyCompact

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {U : Set E₁} {V : Set E₂}

omit [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] [Module ℝ E₂] in
/-- If a nonempty set `V` with dense interior is locally compact, then so is the ambient
space. -/
theorem HasDenseInterior.locallyCompactSpace (hV : HasDenseInterior V) (hne : V.Nonempty)
    [LocallyCompactSpace V] : LocallyCompactSpace E₂ := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hx⟩ : (interior V).Nonempty := closure_nonempty_iff.1 ⟨y, hV hy⟩
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (⟨x, interior_subset hx⟩ : V)
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup (hK.image continuous_subtype_val)
    (x := x) ?_
  obtain ⟨u, hu, huK⟩ := (mem_nhds_subtype V _ K).1 hKn
  filter_upwards [hu, isOpen_interior.mem_nhds hx] with z hz hzi
  exact ⟨⟨z, interior_subset hzi⟩, huK hz, rfl⟩

/-- The continuity of evaluations behind the exponential law: for `i ≤ k` and `j ≤ ℓ`, the
evaluation of a continuous family of maps in `C(V × E₂^j, F)`, parametrized by
`(U × V) × E₁^i × E₂^j`, at a continuously varying point of `V × E₂^j` is continuous. It holds if
`V` is locally compact (`expLawEval_of_locallyCompactSpace`, [GN26, Theorem 1.7.30(a)]) and if
the spaces `U × V × E₁^i × E₂^j` are `k_ℝ`-spaces (`expLawEval_of_krSpace`,
[GN26, Theorem 1.7.30(b)]). -/
def ExpLawEval (k ℓ : ℕ) (U : Set E₁) (V : Set E₂) (F : Type v) [TopologicalSpace F] : Prop :=
  ∀ i ≤ k, ∀ j ≤ ℓ, ∀ (Γ : ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) →
    C(V × (Fin j → E₂), F)) (b : ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) →
    V × (Fin j → E₂)), Continuous Γ → Continuous b → Continuous fun z ↦ Γ z (b z)

omit [AddCommGroup E₁] [Module ℝ E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
  [LocallyConvexSpace ℝ E₁] [Module ℝ E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂]
  [Module ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- **Hypothesis (a)** of [GN26, Theorem 1.7.30]: `V` locally compact. -/
theorem expLawEval_of_locallyCompactSpace (hV : HasDenseInterior V) [LocallyCompactSpace V] :
    ExpLawEval k ℓ U V F := by
  intro i _ j _ Γ b hΓ hb
  by_cases hne : V.Nonempty
  · have := hV.locallyCompactSpace hne
    exact continuous_eval.comp (hΓ.prodMk hb)
  · have : IsEmpty ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) :=
      ⟨fun z ↦ hne ⟨_, z.2.1.2⟩⟩
    exact continuous_of_discreteTopology

omit [AddCommGroup E₁] [Module ℝ E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁] [AddCommGroup E₂] [Module ℝ E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [Module ℝ F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
omit [T2Space E₂] in
/-- **Hypothesis (b)** of [GN26, Theorem 1.7.30]: `U × V × E₁^i × E₂^j` is a `k_ℝ`-space
for all `i ≤ k` and `j ≤ ℓ` (here in the form `(U × V) × E₁^i × E₂^j`). -/
theorem expLawEval_of_krSpace
    (h : ∀ i ≤ k, ∀ j ≤ ℓ, KRSpace ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂))))) :
    ExpLawEval k ℓ U V F := by
  intro i hi j hj Γ b hΓ hb
  have := completelyRegularSpace_of_isTopologicalAddGroup F
  exact (h i hi j hj).continuous_eval hΓ hb

/-- Under `ExpLawEval` (for instance, for `V` locally compact), `g^∧(x, y) = g(x)(y)` is `C^{k,ℓ}`
for every `C^k` map `g : U → C^ℓ(V, F)`, with
`d^(i,j) g^∧(x, y, v, w) = d^(j)(d^(i) g(x, v))(y, w)`. -/
theorem contDiffLC₂_uncurryLC {hU : HasDenseInterior U} {hV : HasDenseInterior V}
    (hev : ExpLawEval k ℓ U V F) {g : E₁ → ContDiffLCMap F ℓ V hV}
    (hg : ContDiffLC k g U) : ContDiffLC₂ k ℓ (fun p ↦ g p.1 p.2) U V := by
  classical
  -- the candidate mixed differentials
  let D : ∀ i j : ℕ, (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) → F := fun i j q ↦
    iteratedDLC j (iteratedDLC (F := ContDiffLCMap F ℓ V hV) i g U (q.1.1, q.2.1)) V (q.1.2, q.2.2)
  have hDc : ∀ i (hi : i ≤ k) j (hj : j ≤ ℓ), ContinuousOn (D i j) ((U ×ˢ V) ×ˢ univ) := by
    intro i hi j hj
    rw [continuousOn_iff_continuous_domRestrict]
    let γ : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU := ContDiffLCMap.mk
      (fun x ↦ if x ∈ U then g x else 0) (hg.congr fun x hx ↦ by simp [hx]) fun x hx ↦ by simp [hx]
    have hγ : ∀ q : U × (Fin i → E₁), ContDiffLCMap.iteratedD i hi γ q =
        iteratedDLC i g U ((q.1 : E₁), q.2) := fun q ↦
      (iteratedDLC_congr hU hg (fun x hx ↦ by simp [γ, hx]) hi
        (show ((q.1 : E₁), q.2) ∈ U ×ˢ univ from ⟨q.1.2, mem_univ _⟩)).symm
    have hc : Continuous fun z : ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) ↦
        ContDiffLCMap.iteratedD j hj (ContDiffLCMap.iteratedD i hi γ
          (⟨z.1.1.1, z.2.1.1⟩, z.1.2.1)) (⟨z.1.1.2, z.2.1.2⟩, z.1.2.2) :=
      hev i hi j hj _ _ ((ContDiffLCMap.continuous_iteratedD j hj).comp
        ((ContDiffLCMap.iteratedD i hi γ).continuous.comp (by fun_prop))) (by fun_prop)
    refine hc.congr fun z ↦ ?_
    simp only [ContDiffLCMap.iteratedD_apply, hγ]
    rfl
  have hDe : ∀ i (hi : i ≤ k) j (hj : j ≤ ℓ),
      EqOn (D i j) (iteratedDMB₂ i j fun p ↦ g p.1 p.2) ((interior U ×ˢ interior V) ×ˢ univ) := by
    rintro i hi j hj ⟨⟨x, y⟩, v, w⟩ ⟨⟨hx, hy⟩, -⟩
    let Λ : ContDiffLCMap F ℓ V hV →L[ℝ] F :=
      (ContinuousMap.evalCLM ℝ ((⟨y, interior_subset hy⟩ : V), w)).comp
        (ContDiffLCMap.iteratedDCLM j hj)
    have hΛ : (fun x' ↦ iteratedDMB j (fun y' ↦ g x' y') (y, w)) = fun x' ↦ Λ (g x') :=
      funext fun x' ↦ (iteratedDLC_eq_iteratedDMB (p := (y, w)) hy).symm
    change Λ (iteratedDLC i g U (x, v)) =
      iteratedDMB i (fun x' ↦ iteratedDMB j (fun y' ↦ g x' y') (y, w)) (x, v)
    rw [hΛ, iteratedDLC_eq_iteratedDMB (p := (x, v)) hx]
    exact (iteratedDMB_clm_comp isOpen_interior hg.contDiffMBOn_interior Λ i hi x hx v).symm
  refine ⟨?_, ⟨fun x hx ↦ (g x).contDiffLC.contDiffMBOn_interior, fun j hj y hy w ↦ ?_,
    fun i hi j hj ↦ ?_⟩, fun i hi j hj ↦ ⟨D i j, hDc i hi j hj, hDe i hi j hj⟩⟩
  · exact (hDc 0 (Nat.zero_le _) 0 (Nat.zero_le _)).comp
      (f := fun p : E₁ × E₂ ↦ (p, ((Fin.elim0 : Fin 0 → E₁), (Fin.elim0 : Fin 0 → E₂))))
      (by fun_prop) fun p hp ↦ ⟨hp, mem_univ _⟩
  · let Λ : ContDiffLCMap F ℓ V hV →L[ℝ] F :=
      (ContinuousMap.evalCLM ℝ ((⟨y, interior_subset hy⟩ : V), w)).comp
        (ContDiffLCMap.iteratedDCLM j hj)
    have hΛ : (fun x' ↦ iteratedDMB j (fun y' ↦ g x' y') (y, w)) = fun x' ↦ Λ (g x') :=
      funext fun x' ↦ (iteratedDLC_eq_iteratedDMB (p := (y, w)) hy).symm
    rw [hΛ]
    exact ContDiffMBOn.comp isOpen_interior isOpen_univ (Λ.contDiffMBOn k univ)
      hg.contDiffMBOn_interior (mapsTo_univ _ _)
  · exact ((hDc i hi j hj).mono (prod_mono (prod_mono interior_subset interior_subset)
      le_rfl)).congr fun q hq ↦ (hDe i hi j hj hq).symm

namespace ContDiffLCMap₂

variable {hU : HasDenseInterior U} {hV : HasDenseInterior V}

/-- The map `g^∧(x, y) = g(x)(y)` of `g ∈ C^k(U, C^ℓ(V, F))`, under `ExpLawEval`. -/
def uncurryOf (hev : ExpLawEval k ℓ U V F) (g : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU) :
    ContDiffLCMap₂ F k ℓ U hU V hV :=
  mk (fun p ↦ g p.1 p.2) (contDiffLC₂_uncurryLC (hU := hU) hev g.contDiffLC) fun p hp ↦ by
    by_cases h1 : p.1 ∈ U
    · exact (g p.1).apply_of_notMem fun h2 ↦ hp ⟨h1, h2⟩
    · simp [g.apply_of_notMem h1]

/-- `Φ(g^∧) = g`. -/
theorem curry_uncurryOf (hev : ExpLawEval k ℓ U V F)
    (g : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU) : curry (uncurryOf hev g) = g :=
  ContDiffLCMap.ext fun x ↦ ContDiffLCMap.ext fun y ↦ by
    rw [curry_apply_apply]
    rfl

/-- **The exponential law** under `ExpLawEval`: `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`,
`f ↦ f^∨`, is an isomorphism of topological vector spaces, with inverse `g ↦ g^∧`. -/
def curryEquivOf (hev : ExpLawEval k ℓ U V F) :
    ContDiffLCMap₂ F k ℓ U hU V hV ≃L[ℝ] ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU where
  toLinearMap := curryLM
  invFun := uncurryOf hev
  left_inv f := curry_injective (curry_uncurryOf hev (curry f))
  right_inv := curry_uncurryOf hev
  continuous_toFun := continuous_curry
  continuous_invFun := by
    rw [isEmbedding_curry.isInducing.continuous_iff]
    exact continuous_id.congr fun g ↦ (curry_uncurryOf hev g).symm

/-- **[GN26, Theorem 1.7.30(b)]** (exponential law), for sets with dense interior: if
`U × V × E₁^i × E₂^j` is a `k_ℝ`-space for all `i ≤ k` and `j ≤ ℓ`, then `Φ` is an isomorphism of
topological vector spaces. -/
def curryEquivOfKRSpace
    (h : ∀ i ≤ k, ∀ j ≤ ℓ, KRSpace ((U ×ˢ V) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂))))) :
    ContDiffLCMap₂ F k ℓ U hU V hV ≃L[ℝ] ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU :=
  curryEquivOf (expLawEval_of_krSpace h)

/-- **The exponential law for first countable spaces**, in particular for Fréchet spaces: if
`E₁` and `E₂` are first countable, the sets `(U × V) × E₁^i × E₂^j` are first countable, hence
`k_ℝ`-spaces, and `Φ` is an isomorphism of topological vector spaces
([GN26, Theorem 1.7.30(b), p. 102]). -/
def curryEquivOfFirstCountable [FirstCountableTopology E₁] [FirstCountableTopology E₂] :
    ContDiffLCMap₂ F k ℓ U hU V hV ≃L[ℝ] ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU :=
  curryEquivOfKRSpace fun _ _ _ _ ↦ KRSpace.of_firstCountableTopology _

variable [LocallyCompactSpace V]

/-- The map `g^∧(x, y) = g(x)(y)` of `g ∈ C^k(U, C^ℓ(V, F))`, for `V` locally compact. -/
def uncurry (g : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU) :
    ContDiffLCMap₂ F k ℓ U hU V hV :=
  uncurryOf (expLawEval_of_locallyCompactSpace hV) g

/-- `Φ(g^∧) = g`. -/
theorem curry_uncurry (g : ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU) : curry (uncurry g) = g :=
  curry_uncurryOf _ g

/-- **[GN26, Theorem 1.7.30(a)]** (exponential law), for sets with dense interior: if `V` is
locally compact, then `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`, `f ↦ f^∨`, is an isomorphism
of topological vector spaces, with inverse `g ↦ g^∧`, `g^∧(x, y) = g(x)(y)`. -/
def curryEquiv :
    ContDiffLCMap₂ F k ℓ U hU V hV ≃L[ℝ] ContDiffLCMap (ContDiffLCMap F ℓ V hV) k U hU :=
  curryEquivOf (expLawEval_of_locallyCompactSpace hV)

end ContDiffLCMap₂

end LocallyCompact

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.CklMaps

/-!
# The exponential law for `C^{k,ℓ}` maps

Let `E₁`, `E₂`, `F` be locally convex spaces, `U ⊆ E₁` and `V ⊆ E₂` open, and `k, ℓ ∈ ℕ`. For
`f ∈ C^{k,ℓ}(U × V, F)` let `f^∨(x) = f(x, ·)`. We prove ([GN26, Theorem 1.7.30]) that
`f^∨ : U → C^ℓ(V, F)` is `C^k`, that `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`, `f ↦ f^∨`, is
linear and a topological embedding, and that `Φ` is an isomorphism of topological vector spaces if
`E₂` is locally compact.

## Main results

* `ContDiffMBMap₂.contDiffMBOn_partialMap`: `f^∨` is `C^k` (Theorem 1.7.30), with
  `d^(i)(f^∨)(x, v) = d^(i,0) f(x, ·, v)` (`ContDiffMBMap₂.iteratedDMB_partialMap`, (1.99)).
* `ContDiffMBMap₂.iteratedD_iteratedD_curry`:
  `d^(j)(d^(i)(f^∨)(x, v))(y, w) = d^(i,j) f(x, y, v, w)` ([GN26, (1.98)]).
* `ContDiffMBMap₂.isEmbedding_curry`, `ContDiffMBMap₂.curryCLM`: `Φ` is a continuous linear
  topological embedding (Theorem 1.7.30).
* `ContDiffMBMap₂.curryEquiv`: if `E₂` is locally compact, `Φ` is an isomorphism of topological
  vector spaces, with inverse `g ↦ g^∧`, `g^∧(x, y) = g(x)(y)` (Theorem 1.7.30(a)).

## Implementation notes

* **Hypothesis (a).** Glöckner–Neeb assume that `V` is locally compact. For a nonempty open
  subset `V` of a topological vector space this is equivalent to the local compactness of `E₂`,
  which is the hypothesis used here (`[LocallyCompactSpace E₂]`). Hypothesis (b) of
  Theorem 1.7.30 (`k_ℝ`-spaces, in particular Fréchet spaces) is treated for sets with dense
  interior, open sets included, in `Calculus/DenseInterior/ExpLaw.lean` (`curryEquivOfKRSpace`,
  `curryEquivOfFirstCountable`).
* **Departures from Glöckner–Neeb.** For the differentiability of `f^∨`, Glöckner–Neeb use the
  continuous extension of difference quotients (their Lemma 1.7.6) and Proposition A.6.17; here
  the convergence of the difference quotients in `C^ℓ(V, F)` comes from their uniform convergence
  on compact sets (`eventually_forall_quotient_mem`), and Bastiani's characterization of `C^k`
  maps (`HasContIterDerivOn.contDiffMBOn`) is used. For the embedding, instead of Lemma A.6.4 and
  Proposition A.6.17 we restrict to compact sets, on which evaluation is continuous
  (`ContinuousMap.continuous_eval_comp_restrict`). For the surjectivity, instead of the
  evaluation map (Lemma 1.7.25) and the chain rule for `C^{r,s}` maps (Proposition 1.7.26, with
  Faà di Bruno's formula), the differentials of `g^∧` are written directly as
  `d^(j)(d^(i) g(x, v))(y, w)`, using the continuity of evaluation on the locally compact space
  `V × E₂^j`. We do not claim these arguments are new.
* Only open `U`, `V` and finite `k`, `ℓ` are treated.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u u' v

/-! ### Joint continuity of evaluations on compact sets -/

section CompactOpen

variable {Y W Z : Type*} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace W]
  [TopologicalSpace Z]

/-- Evaluation `(φ, z) ↦ φ (σ z)` is continuous on `C(Y, W) × K` for `K` compact and `σ`
continuous (`Y` Hausdorff). -/
theorem ContinuousMap.continuous_eval_comp_restrict {σ : Z → Y} (hσ : Continuous σ) {K : Set Z}
    (hK : IsCompact K) : Continuous fun q : C(Y, W) × K ↦ q.1 (σ q.2) :=
  (ContinuousMap.continuous_eval_restrict (A := W) (hK.image hσ)).comp
    (continuous_fst.prodMk ((hσ.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk
      fun q ↦ mem_image_of_mem σ q.2.2))

end CompactOpen

/-! ### The partial maps `f^∨(x) = f(x, ·)` and their derivatives -/

section Curry

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace ContDiffMBMap₂

variable {k ℓ : ℕ} {U : Opens E₁} {V : Opens E₂}

/-- The partial map `f^∨(x) = f(x, ·) ∈ C^ℓ(V, F)` of `f ∈ C^{k,ℓ}(U × V, F)`
([GN26, Lemma 1.7.18]); it is `0` for `x ∉ U`. -/
def partialMap (f : ContDiffMBMap₂ F k ℓ U V) (x : E₁) : ContDiffMBMap F ℓ V :=
  ContDiffMBMap.mk (fun y ↦ f (x, y)) (by
      by_cases hx : x ∈ U
      · exact f.contDiffMBOn₂.contDiffMBOn_right x hx
      · exact ContDiffMBOn.congr_of_isOpen V.isOpen
          (fun y _ ↦ (f.apply_of_notMem fun h ↦ hx h.1).symm)
          (contDiffMBOn_const ℓ (0 : F) (V : Set E₂)))
    fun _ hy ↦ f.apply_of_notMem fun h ↦ hy h.2

/-- `f^∨(x)(y) = f(x, y)`. -/
@[simp]
theorem partialMap_apply (f : ContDiffMBMap₂ F k ℓ U V) (x : E₁) (y : E₂) :
    partialMap f x y = f (x, y) :=
  rfl

/-- `f^∨(x) = 0` for `x ∉ U`. -/
theorem partialMap_of_notMem (f : ContDiffMBMap₂ F k ℓ U V) {x : E₁} (hx : x ∉ U) :
    partialMap f x = 0 :=
  ContDiffMBMap.ext fun _ ↦ f.apply_of_notMem fun h ↦ hx h.1

/-- `d^(i,0) f(x, y, v) = 0` for `y ∉ V`. -/
theorem iteratedDMB₂_of_notMem (f : ContDiffMBMap₂ F k ℓ U V) (i : ℕ) (x : E₁) {y : E₂}
    (hy : y ∉ V) (v : Fin i → E₁) : iteratedDMB₂ i 0 f ((x, y), v, Fin.elim0) = 0 := by
  have h : (fun x' ↦ iteratedDMB 0 (fun y' ↦ f (x', y')) (y, (Fin.elim0 : Fin 0 → E₂))) =
      fun _ ↦ (0 : F) := funext fun x' ↦ f.apply_of_notMem fun h ↦ hy h.2
  change iteratedDMB i (fun x' ↦ iteratedDMB 0 (fun y' ↦ f (x', y')) (y, Fin.elim0)) (x, v) = 0
  rw [h, iteratedDMB_const_zero]

/-- The candidate for the `i`-th differential of `f^∨`:
`(x, v) ↦ d^(i,0) f(x, ·, v) ∈ C^ℓ(V, F)` for `x ∈ U` (and `0` otherwise). -/
def derivMap (f : ContDiffMBMap₂ F k ℓ U V) {i : ℕ} (hi : i ≤ k) (x : E₁) (v : Fin i → E₁) :
    ContDiffMBMap F ℓ V := by
  classical
  exact if hx : x ∈ U then
    ContDiffMBMap.mk (fun y ↦ iteratedDMB₂ i 0 f ((x, y), v, Fin.elim0))
      (f.contDiffMBOn₂.contDiffMBOn_right_iteratedDMB₂ U.isOpen V.isOpen hi hx v)
      fun _ hy ↦ iteratedDMB₂_of_notMem f i x hy v
  else 0

/-- `d^(j)(d^(i,0) f(x, ·, v))(y, w) = d^(i,j) f(x, y, v, w)` for `x ∈ U`, `y ∈ V`. -/
theorem iteratedDMB_derivMap (f : ContDiffMBMap₂ F k ℓ U V) {i : ℕ} (hi : i ≤ k) {x : E₁}
    (hx : x ∈ U) (v : Fin i → E₁) {j : ℕ} (hj : j ≤ ℓ) {y : E₂} (hy : y ∈ V)
    (w : Fin j → E₂) :
    iteratedDMB j (derivMap f hi x v) (y, w) = iteratedDMB₂ i j f ((x, y), v, w) := by
  have e : ⇑(derivMap f hi x v) = fun y ↦ iteratedDMB₂ i 0 f ((x, y), v, Fin.elim0) := by
    simp [derivMap, hx]
  rw [e]
  exact f.contDiffMBOn₂.iteratedDMB_right U.isOpen V.isOpen hi hx v j hj y hy w

/-- **The derivative of `x ↦ d^(i,0) f(x, ·, v)`** in `C^ℓ(V, F)`: its directional derivative
in the direction `a` is `d^(i+1,0) f(x, ·, v, a)` (compare the proof of
[GN26, Theorem 1.7.30]). -/
theorem hasDirDerivAt_derivMap (f : ContDiffMBMap₂ F k ℓ U V) {i : ℕ} (hi : i < k) {x : E₁}
    (hx : x ∈ U) (v : Fin (i + 1) → E₁) :
    HasDirDerivAt (fun x' ↦ derivMap f hi.le x' (Fin.init v)) x (v (Fin.last i))
      (derivMap f (show i + 1 ≤ k from hi) x v) := by
  rw [HasDirDerivAt, ContDiffMBMap.isEmbedding_toPi.tendsto_nhds_iff, tendsto_pi_nhds]
  intro j
  have hj : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp j.2
  have e : ∀ γ : ContDiffMBMap F ℓ V, ContDiffMBMap.toPi γ j = ContDiffMBMap.iteratedD j hj γ :=
    fun _ ↦ rfl
  simp only [Function.comp_def, e, show ContDiffMBMap.iteratedD (F := F) (U := V) j hj =
    ⇑(ContDiffMBMap.iteratedDL j hj) from rfl, map_smul, map_sub]
  rw [ContinuousMap.tendsto_nhds_compactOpen]
  intro K hK O hO hKO
  set a := v (Fin.last i)
  have hUo : IsOpen ((U : Set E₁) ×ˢ ((V : Set E₂) ×ˢ (univ : Set (Fin j → E₂)))) :=
    U.isOpen.prod (V.isOpen.prod isOpen_univ)
  have ev := eventually_forall_quotient_mem hUo (h := ((a, 0) : E₁ × (E₂ × (Fin j → E₂))))
    (g := fun q ↦ iteratedDMB₂ i j f ((q.1, q.2.1), Fin.init v, q.2.2))
    (D := fun q ↦ iteratedDMB₂ (i + 1) j f ((q.1, q.2.1), v, q.2.2))
    (fun q hq ↦ hasDirDerivAt_slice.2
      (f.contDiffMBOn₂.hasDirDerivAt_left hi hj hq.1 hq.2.1 v q.2.2))
    ((f.contDiffMBOn₂.continuousOn (i + 1) hi j hj).comp (by fun_prop)
      fun q hq ↦ ⟨⟨hq.1, hq.2.1⟩, mem_univ _⟩)
    (P := fun p : V × (Fin j → E₂) ↦ (x, ((p.1 : E₂), p.2))) (by fun_prop) hK
    (fun p _ ↦ ⟨hx, p.1.2, mem_univ _⟩) hO (fun p hp ↦ by
      have := hKO hp
      simp only [ContDiffMBMap.iteratedDL, LinearMap.coe_mk, AddHom.coe_mk,
        ContDiffMBMap.iteratedD_apply] at this
      rwa [iteratedDMB_derivMap f _ hx v hj p.1.2] at this)
  have hxU : ∀ᶠ t : ℝ in 𝓝 0, x + t • a ∈ U := by
    have hc : Continuous fun t : ℝ ↦ x + t • a := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this (U.isOpen.mem_nhds hx)
  filter_upwards [nhdsWithin_le_nhds ev, nhdsWithin_le_nhds hxU, self_mem_nhdsWithin]
    with t ht htU ht0 p hp
  have h := ht p hp ht0
  simp only [ContDiffMBMap.iteratedDL, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContDiffMBMap.iteratedD_apply]
  rw [iteratedDMB_derivMap f _ htU _ hj p.1.2, iteratedDMB_derivMap f _ hx _ hj p.1.2]
  simpa using h

/-- **The differentials of `f^∨`**: `d^(i)(f^∨)(x, v) = d^(i,0) f(x, ·, v)` for `x ∈ U`
([GN26, (1.99)]). -/
theorem iteratedDMB_partialMap (f : ContDiffMBMap₂ F k ℓ U V) :
    ∀ i (hi : i ≤ k), ∀ x ∈ U, ∀ v : Fin i → E₁,
      iteratedDMB i (partialMap f) (x, v) = derivMap f hi x v := by
  intro i
  induction i with
  | zero =>
    intro hi x hx v
    refine ContDiffMBMap.ext fun y ↦ ?_
    simp only [derivMap, hx, dite_true, ContDiffMBMap.coe_mk]
    rw [Subsingleton.elim v Fin.elim0]
    rfl
  | succ i ih =>
    intro hi x hx v
    rw [iteratedDMB_succ]
    have hev : (fun x' ↦ iteratedDMB i (partialMap f) (x', Fin.init v)) =ᶠ[𝓝 x]
        fun x' ↦ derivMap f (by omega) x' (Fin.init v) :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun x' hx' ↦ ih (by omega) x' hx' _
    rw [dMB_congr_of_eventuallyEq hev]
    exact (hasDirDerivAt_derivMap f hi hx v).dMB_eq

/-- `(x, v) ↦ d^(i,0) f(x, ·, v) ∈ C^ℓ(V, F)` is continuous on `U × E₁^i`. -/
theorem continuousOn_derivMap (f : ContDiffMBMap₂ F k ℓ U V) {i : ℕ} (hi : i ≤ k) :
    ContinuousOn (fun q : E₁ × (Fin i → E₁) ↦ derivMap f hi q.1 q.2) ((U : Set E₁) ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine ContDiffMBMap.continuous_iff.2 fun j hj ↦ ?_
  let ζ : C(((U : Set E₁) ×ˢ (univ : Set (Fin i → E₁))) × (V × (Fin j → E₂)), F) :=
    ⟨fun q ↦ iteratedDMB₂ i j f ((q.1.1.1, (q.2.1 : E₂)), q.1.1.2, q.2.2),
      (f.contDiffMBOn₂.continuousOn i hi j hj).comp_continuous (by fun_prop)
        fun q ↦ ⟨⟨q.1.2.1, q.2.1.2⟩, mem_univ _⟩⟩
  refine ζ.curry.continuous.congr fun q ↦ ContinuousMap.ext fun p ↦ ?_
  exact (iteratedDMB_derivMap f hi q.2.1 q.1.2 hj p.1.2 p.2).symm

/-- **[GN26, Theorem 1.7.30]** (first part): for `f ∈ C^{k,ℓ}(U × V, F)`, the map
`f^∨ : U → C^ℓ(V, F)`, `x ↦ f(x, ·)`, is `C^k`. -/
theorem contDiffMBOn_partialMap (f : ContDiffMBMap₂ F k ℓ U V) :
    ContDiffMBOn k (partialMap f) U := by
  refine HasContIterDerivOn.contDiffMBOn U.isOpen ⟨fun i hi x hx v ↦ ?_, fun i hi ↦ ?_⟩
  · rw [iteratedDMB_partialMap f (i + 1) hi x hx v]
    have hev : (fun x' ↦ derivMap f hi.le x' (Fin.init v)) =ᶠ[𝓝 x]
        fun x' ↦ iteratedDMB i (partialMap f) (x', Fin.init v) :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun x' hx' ↦
        (iteratedDMB_partialMap f i hi.le x' hx' _).symm
    exact (hasDirDerivAt_derivMap f hi hx v).congr_of_eventuallyEq hev
  · exact (continuousOn_derivMap f hi).congr fun q hq ↦
      iteratedDMB_partialMap f i hi q.1 hq.1 q.2

/-- **The curried map** `Φ(f) = f^∨ ∈ C^k(U, C^ℓ(V, F))` of `f ∈ C^{k,ℓ}(U × V, F)`
([GN26, Theorem 1.7.30]). -/
def curry (f : ContDiffMBMap₂ F k ℓ U V) : ContDiffMBMap (ContDiffMBMap F ℓ V) k U :=
  ContDiffMBMap.mk (partialMap f) (contDiffMBOn_partialMap f) fun _ hx ↦ partialMap_of_notMem f hx

/-- `Φ(f)(x)(y) = f(x, y)`. -/
@[simp]
theorem curry_apply_apply (f : ContDiffMBMap₂ F k ℓ U V) (x : E₁) (y : E₂) :
    curry f x y = f (x, y) :=
  rfl

/-- **[GN26, (1.98)]**: `d^(j)(d^(i)(f^∨)(x, v))(y, w) = d^(i,j) f(x, y, v, w)`. -/
theorem iteratedD_iteratedD_curry (f : ContDiffMBMap₂ F k ℓ U V) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ ℓ) (q : U × (Fin i → E₁)) (p : V × (Fin j → E₂)) :
    ContDiffMBMap.iteratedD j hj (ContDiffMBMap.iteratedD i hi (curry f) q) p =
      iteratedDMB₂ i j f (((q.1 : E₁), (p.1 : E₂)), q.2, p.2) := by
  simp only [ContDiffMBMap.iteratedD_apply]
  rw [show ⇑(curry f) = partialMap f from rfl, iteratedDMB_partialMap f i hi q.1 q.1.2 q.2]
  exact iteratedDMB_derivMap f hi q.1.2 q.2 hj p.1.2 p.2

/-- `Φ : f ↦ f^∨` as a linear map. -/
def curryLM : ContDiffMBMap₂ F k ℓ U V →ₗ[ℝ] ContDiffMBMap (ContDiffMBMap F ℓ V) k U where
  toFun := curry
  map_add' _ _ := ContDiffMBMap.ext fun _ ↦ ContDiffMBMap.ext fun _ ↦ rfl
  map_smul' _ _ := ContDiffMBMap.ext fun _ ↦ ContDiffMBMap.ext fun _ ↦ rfl

/-- `Φ` is injective. -/
theorem curry_injective : Function.Injective (curry (F := F) (k := k) (ℓ := ℓ) (U := U) (V := V)) :=
  fun f g h ↦ ext fun p ↦ by
    simpa using congrArg (fun γ : ContDiffMBMap (ContDiffMBMap F ℓ V) k U ↦ γ p.1 p.2) h

/-- `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))` is continuous. -/
theorem continuous_curry : Continuous (curry (F := F) (k := k) (ℓ := ℓ) (U := U) (V := V)) := by
  refine ContDiffMBMap.continuous_iff.2 fun i hi ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K hK ↦ ?_
  refine ContDiffMBMap.continuous_iff.2 fun j hj ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K' hK' ↦ ?_
  let σ : (U × (Fin i → E₁)) × (V × (Fin j → E₂)) → (U × V) × (Fin i → E₁) × (Fin j → E₂) :=
    fun z ↦ ((z.1.1, z.2.1), z.1.2, z.2.2)
  have hσ : Continuous σ := by fun_prop
  have h := ContinuousMap.continuous_eval_comp_restrict (W := F) hσ (hK.prod hK')
  have h2 : Continuous fun r : (ContDiffMBMap₂ F k ℓ U V × K) × K' ↦
      (iteratedD₂ i j hi hj r.1.1, (⟨((r.1.2 : U × (Fin i → E₁)), (r.2 : V × (Fin j → E₂))),
        ⟨r.1.2.2, r.2.2⟩⟩ : (K ×ˢ K' : Set _))) :=
    ((continuous_iteratedD₂ i j hi hj).comp continuous_fst.fst).prodMk (by fun_prop)
  refine (h.comp h2).congr fun r ↦ ?_
  exact (iteratedD_iteratedD_curry r.1.1 hi hj _ _).symm

/-- If `φ : X → C^{k,ℓ}(U × V, F)` becomes continuous after composition with `Φ`, then all its
mixed differentials are continuous. -/
theorem continuous_iteratedD₂_of_continuous_curry {X : Type*} [tX : TopologicalSpace X]
    {φ : X → ContDiffMBMap₂ F k ℓ U V} (hφ : Continuous fun x ↦ curry (φ x)) (i j : ℕ)
    (hi : i ≤ k) (hj : j ≤ ℓ) : Continuous fun x ↦ iteratedD₂ i j hi hj (φ x) := by
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K hK ↦ ?_
  let σ₁ : (U × V) × (Fin i → E₁) × (Fin j → E₂) → U × (Fin i → E₁) := fun z ↦ (z.1.1, z.2.1)
  let σ₂ : (U × V) × (Fin i → E₁) × (Fin j → E₂) → V × (Fin j → E₂) := fun z ↦ (z.1.2, z.2.2)
  have hA : Continuous fun q : X × K ↦
      ContDiffMBMap.iteratedD i hi (curry (φ q.1)) (σ₁ q.2) :=
    (ContinuousMap.continuous_eval_comp_restrict (W := ContDiffMBMap F ℓ V)
      (by fun_prop : Continuous σ₁) hK).comp
      (((ContDiffMBMap.continuous_iteratedD i hi).comp (hφ.comp continuous_fst)).prodMk
        continuous_snd)
  have hB : Continuous fun q : X × K ↦ ContDiffMBMap.iteratedD j hj
      (ContDiffMBMap.iteratedD i hi (curry (φ q.1)) (σ₁ q.2)) (σ₂ q.2) :=
    (ContinuousMap.continuous_eval_comp_restrict (W := F) (by fun_prop : Continuous σ₂) hK).comp
      (((ContDiffMBMap.continuous_iteratedD j hj).comp hA).prodMk continuous_snd)
  refine hB.congr fun q ↦ ?_
  exact iteratedD_iteratedD_curry (φ q.1) hi hj _ _

/-- If `φ : X → C^{k,ℓ}(U × V, F)` becomes continuous after composition with `Φ`, then so does
`γ ↦ (d^(i,j)γ)_{i,j}`. -/
theorem continuous_toPi_of_continuous_curry {X : Type*} [tX : TopologicalSpace X]
    {φ : X → ContDiffMBMap₂ F k ℓ U V} (hφ : Continuous fun x ↦ curry (φ x)) :
    Continuous fun x ↦ toPi (φ x) :=
  continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_iteratedD₂_of_continuous_curry hφ i j
    (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)

/-- **[GN26, Theorem 1.7.30]** (second part): `Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`,
`f ↦ f^∨`, is a topological embedding. -/
theorem isEmbedding_curry :
    Topology.IsEmbedding (curry (F := F) (k := k) (ℓ := ℓ) (U := U) (V := V)) := by
  refine ⟨(Topology.isInducing_iff _).2 ?_, curry_injective⟩
  refine le_antisymm (continuous_iff_le_induced.1 continuous_curry) ?_
  have h := continuous_toPi_of_continuous_curry (X := ContDiffMBMap₂ F k ℓ U V)
    (tX := TopologicalSpace.induced curry inferInstance) (φ := id) continuous_induced_dom
  exact continuous_iff_le_induced.1 h

/-- `Φ` as a continuous linear map. -/
def curryCLM : ContDiffMBMap₂ F k ℓ U V →L[ℝ] ContDiffMBMap (ContDiffMBMap F ℓ V) k U :=
  ⟨curryLM, continuous_curry⟩

/-! ### Surjectivity for locally compact `E₂` -/

section LocallyCompact

variable [LocallyCompactSpace E₂]

/-- The map `g^∧(x, y) = g(x)(y)` of `g ∈ C^k(U, C^ℓ(V, F))`, for `E₂` locally compact. -/
def uncurry (g : ContDiffMBMap (ContDiffMBMap F ℓ V) k U) : ContDiffMBMap₂ F k ℓ U V :=
  have hV : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  -- `d^(0,j) g^∧(·, y, w)` is a continuous linear image of `g`
  let L : ∀ {j : ℕ}, j ≤ ℓ → ∀ {y : E₂}, y ∈ V → (Fin j → E₂) → ContDiffMBMap F ℓ V →L[ℝ] F :=
    fun hj y hy w ↦ (ContinuousMap.evalCLM ℝ ((⟨y, hy⟩ : V), w)).comp
      (ContDiffMBMap.iteratedDCLM _ hj)
  have hL : ∀ {j : ℕ} (hj : j ≤ ℓ) {y : E₂} (hy : y ∈ V) (w : Fin j → E₂),
      (fun x ↦ iteratedDMB j (fun y' ↦ g x y') (y, w)) = fun x ↦ L hj hy w (g x) :=
    fun _ _ _ _ ↦ rfl
  mk (fun p ↦ g p.1 p.2)
    { contDiffMBOn_right := fun x _ ↦ (g x).contDiffMBOn
      contDiffMBOn_left := fun j hj y hy w ↦ by
        rw [hL hj hy w]
        exact ContDiffMBOn.comp U.isOpen isOpen_univ ((L hj hy w).contDiffMBOn k univ)
          g.contDiffMBOn (mapsTo_univ _ _)
      continuousOn := fun i hi j hj ↦ by
        rw [continuousOn_iff_continuous_domRestrict]
        have hc : Continuous fun z : (((U : Set E₁) ×ˢ (V : Set E₂)) ×ˢ
            (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) ↦
            ContDiffMBMap.iteratedD j hj (ContDiffMBMap.iteratedD i hi g
              (⟨z.1.1.1, z.2.1.1⟩, z.1.2.1)) (⟨z.1.1.2, z.2.1.2⟩, z.1.2.2) :=
          continuous_eval.comp
            (((ContDiffMBMap.continuous_iteratedD j hj).comp
              ((ContDiffMBMap.iteratedD i hi g).continuous.comp
                (by fun_prop))).prodMk (by fun_prop))
        refine hc.congr fun z ↦ Eq.symm ?_
        change iteratedDMB i (fun x ↦ iteratedDMB j (fun y' ↦ g x y') (z.1.1.2, z.1.2.2))
          (z.1.1.1, z.1.2.1) = _
        rw [hL hj z.2.1.2 z.1.2.2]
        exact iteratedDMB_clm_comp U.isOpen g.contDiffMBOn (L hj z.2.1.2 z.1.2.2) i hi
          z.1.1.1 z.2.1.1 z.1.2.1 }
    fun p hp ↦ by
      by_cases h1 : p.1 ∈ U
      · exact (g p.1).apply_of_notMem fun h2 ↦ hp ⟨h1, h2⟩
      · simp [g.apply_of_notMem h1]

/-- `Φ(g^∧) = g`. -/
theorem curry_uncurry (g : ContDiffMBMap (ContDiffMBMap F ℓ V) k U) : curry (uncurry g) = g :=
  ContDiffMBMap.ext fun _ ↦ ContDiffMBMap.ext fun _ ↦ rfl

/-- **[GN26, Theorem 1.7.30(a)]** (exponential law): if `E₂` is locally compact, then
`Φ : C^{k,ℓ}(U × V, F) → C^k(U, C^ℓ(V, F))`, `f ↦ f^∨`, is an isomorphism of topological vector
spaces, with inverse `g ↦ g^∧`, `g^∧(x, y) = g(x)(y)`. -/
def curryEquiv : ContDiffMBMap₂ F k ℓ U V ≃L[ℝ] ContDiffMBMap (ContDiffMBMap F ℓ V) k U where
  toLinearMap := curryLM
  invFun := uncurry
  left_inv f := curry_injective (curry_uncurry (curry f))
  right_inv := curry_uncurry
  continuous_toFun := continuous_curry
  continuous_invFun := by
    rw [isEmbedding_curry.isInducing.continuous_iff]
    exact continuous_id.congr fun g ↦ (curry_uncurry g).symm

end LocallyCompact

end ContDiffMBMap₂

end Curry

end LocallyConvex.Analysis

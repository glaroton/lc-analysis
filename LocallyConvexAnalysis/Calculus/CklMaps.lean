/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.MappingSpace.SmoothTopology

/-!
# `C^{k,ℓ}` maps

Let `E₁`, `E₂`, `F` be locally convex spaces and `U ⊆ E₁`, `V ⊆ E₂` open. A map
`f : U × V → F` is `C^{k,ℓ}` if the mixed differentials

  `d^(i,j) f(x, y, v₁, …, vᵢ, w₁, …, wⱼ)`
  `  = (D_{(vᵢ,0)} ⋯ D_{(v₁,0)} D_{(0,wⱼ)} ⋯ D_{(0,w₁)} f)(x, y)`

exist for `i ≤ k`, `j ≤ ℓ` and are continuous on `U × V × E₁^i × E₂^j` ([GN26, Definition 1.7.17]).
We define these maps, prove the version of Schwarz's theorem needed for the exponential law, and
make `C^{k,ℓ}(U × V, F)` a locally convex space with the compact-open `C^{k,ℓ}` topology.

## Main definitions

* `iteratedDMB₂ i j f`: the mixed differential `d^(i,j) f`.
* `ContDiffMBOn₂ k ℓ f U V`: `f` is `C^{k,ℓ}` on `U × V`.
* `ContDiffMBMap₂ F k ℓ U V`: the space `C^{k,ℓ}(U × V, F)`, for `U : Opens E₁`, `V : Opens E₂`,
  with the compact-open `C^{k,ℓ}` topology, and `ContDiffMBMap₂.iteratedD₂`: the continuous linear
  maps `d^(i,j) : C^{k,ℓ}(U × V, F) → C(U × V × E₁^i × E₂^j, F)`.

## Main results

* `contDiffMBOn₂_iff`: `ContDiffMBOn₂` is [GN26, Definition 1.7.17] (for open `U`, `V`).
* `hasDirDerivAt_comm`: mixed partial derivatives commute (compare [GN26, Lemma 1.3.16]),
  without completeness.
* `ContDiffMBOn₂.hasDirDerivAt_right`, `ContDiffMBOn₂.contDiffMBOn_right_iteratedDMB₂`: for
  `f` of class `C^{k,ℓ}`, `y ↦ d^(i,0) f(x, y, v)` is `C^ℓ` with differentials `d^(i,j) f`
  (the part of [GN26, Proposition 1.7.21 and Corollary 1.7.22] used for the exponential
  law).
* `ContDiffMBMap₂.instLocallyConvexSpaceReal`, `ContDiffMBMap₂.instT2Space`: `C^{k,ℓ}(U × V, F)`
  is a locally convex Hausdorff space ([GN26, Definition 1.7.17]).
* `ContDiffMBOn.contDiffMBOn₂`, `ContDiffMBMap₂.ofContDiffMBMapCLM`: `C^{k+ℓ}` maps are
  `C^{k,ℓ}`, and the inclusion `C^{k+ℓ}(U × V, F) → C^{k,ℓ}(U × V, F)` is continuous linear
  ([GN26, Proposition 1.7.33(a)]).

## Implementation notes

* **Definition.** `ContDiffMBOn₂` is stated in the form of
  [GN26, Lemma 1.7.18 and Remark 1.7.19(b)]: the partial maps `f(x, ·)` are `C^ℓ`, the maps
  `x ↦ d^(0,j) f(x, y, w)` are `C^k`, and the `d^(i,j) f` are jointly continuous. By Proposition
  1.3.10 this is equivalent to Glöckner–Neeb's definition (`contDiffMBOn₂_iff`), and it gives direct
  access to the library's results on `C^k` maps. As in `MappingSpace/CkTopology.lean`, elements of
  `C^{k,ℓ}(U × V, F)` are maps on `E₁ × E₂` vanishing outside `U × V`, and only open `U`, `V` and
  finite `k`, `ℓ` are treated.
* **Departure from Glöckner–Neeb in Lemma 1.3.16.** Glöckner–Neeb interchange mixed partial
  derivatives by differentiating a weak integral in a completion. Here `hasDirDerivAt_comm`
  differentiates the difference quotients and passes to the limit with
  `hasDirDerivAt_of_tendsto` (mean value inclusion), the uniform convergence on compact sets
  coming from `tendsto_quotient_of_hasDirDerivAt`. No completeness is needed. We do not claim this
  argument is new. Here only the case of Proposition 1.7.21 needed for the exponential law (one
  derivative in the second variable moved past derivatives in the first) is proved; the general
  case is in `Calculus/CklSchwarz.lean` (`ContDiffMBOn₂.iteratedDMB_append_perm`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u u' v

/-! ### Difference quotients and mixed partial derivatives -/

section Mixed

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Difference quotients converge uniformly on compact sets.** If `g` has directional
derivatives `D q` in the direction `h` at all points `q` of the open set `U`, with `D` continuous
on `U`, and `P : X → U` is continuous, then for every compact `K ⊆ X` and every open `O ⊇ D(P(K))`,
the difference quotients `t⁻¹ • (g (P z + t • h) - g (P z))` lie in `O` for all `z ∈ K` and all
small `t ≠ 0`. -/
theorem eventually_forall_quotient_mem {X : Type*} [TopologicalSpace X] {g : E → F} {U : Set E}
    (hU : IsOpen U) {h : E} {D : E → F} (hd : ∀ q ∈ U, HasDirDerivAt g q h (D q))
    (hD : ContinuousOn D U) {P : X → E} (hP : Continuous P) {K : Set X} (hK : IsCompact K)
    (hKU : MapsTo P K U) {O : Set F} (hO : IsOpen O) (hKO : MapsTo (D ∘ P) K O) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ z ∈ K, t ≠ 0 → t⁻¹ • (g (P z + t • h) - g (P z)) ∈ O := by
  refine hK.eventually_forall_of_forall_eventually fun z hz ↦ ?_
  have T := tendsto_quotient_of_hasDirDerivAt hU hd hD (hKU hz)
  have ev := eventually_nhdsWithin_iff.1 (T (hO.mem_nhds (hKO hz)))
  have hc : Continuous fun q : ℝ × X ↦ (P q.2, q.1) := by fun_prop
  have := (hc.tendsto (0, z)).eventually ev
  filter_upwards [this] with q hq hq0
  exact hq hq0

/-- **Mixed partial derivatives commute** (compare [GN26, Lemma 1.3.16]). Let `U` be open,
and let `g` have directional derivatives `A z` in the direction `a` and `B z` in the direction `b`
at all `z ∈ U`, where `B` is continuous and has continuous directional derivatives `M z` in the
direction `a`. Then `A` has directional derivative `M z` in the direction `b` at every `z ∈ U`.

Glöckner–Neeb differentiate a weak integral (in a completion); here the difference quotients of
`g` in the direction `a` are differentiated in the direction `b` and
`hasDirDerivAt_of_tendsto` is applied, so no completeness is needed. -/
theorem hasDirDerivAt_comm {g A B M : E → F} {U : Set E} (hU : IsOpen U) {a b : E}
    (hA : ∀ z ∈ U, HasDirDerivAt g z a (A z)) (hB : ∀ z ∈ U, HasDirDerivAt g z b (B z))
    (hBc : ContinuousOn B U) (hM : ∀ z ∈ U, HasDirDerivAt B z a (M z))
    (hMc : ContinuousOn M U) {x : E} (hx : x ∈ U) : HasDirDerivAt A x b (M x) := by
  -- a neighborhood `W` of `x` and `W₂` of `0` with `W + W₂ • a ⊆ U`
  have hc : Continuous fun q : E × ℝ ↦ q.1 + q.2 • a := by fun_prop
  have hpre : (fun q : E × ℝ ↦ q.1 + q.2 • a) ⁻¹' U ∈ 𝓝 (x, (0 : ℝ)) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hx)
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 hpre
  have hWU : ∀ z ∈ interior W₁, ∀ r ∈ W₂, z + r • a ∈ U := fun z hz r hr ↦
    hW (mk_mem_prod (interior_subset hz) hr)
  have hW0 : ∀ z ∈ interior W₁, z ∈ U := fun z hz ↦ by
    simpa using hWU z hz 0 (mem_of_mem_nhds hW₂)
  have hr : ∀ᶠ r : ℝ in 𝓝[≠] 0, r ∈ W₂ := nhdsWithin_le_nhds hW₂
  refine hasDirDerivAt_of_tendsto (l := 𝓝[≠] (0 : ℝ))
    (g := fun r z ↦ r⁻¹ • (g (z + r • a) - g z)) (D := fun r z ↦ r⁻¹ • (B (z + r • a) - B z))
    isOpen_interior ?_ ?_ (fun z hz ↦ hA z (hW0 z hz)) ?_ (hMc.mono hW0)
    (mem_interior_iff_mem_nhds.2 hW₁)
  · filter_upwards [hr] with r hr z hz
    exact (((hB _ (hWU z hz r hr)).comp_add_const).sub (hB z (hW0 z hz))).const_smul r⁻¹
  · filter_upwards [hr] with r hr
    exact continuousOn_const.smul ((hBc.comp (by fun_prop) fun z hz ↦ hWU z hz r hr).sub
      (hBc.mono hW0))
  · intro K hKW hK O hO hKO
    have h := eventually_forall_quotient_mem hU hM hMc continuous_id hK
      (fun z hz ↦ hW0 z (hKW hz)) hO hKO
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with r hr hr0 z hz
    exact hr z hz hr0

end Mixed

/-! ### `C^{k,ℓ}` maps -/

section Definition

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The mixed differentials
`d^(i,j) f (x, y, v₁, …, vᵢ, w₁, …, wⱼ) = (D_{(vᵢ,0)} ⋯ D_{(v₁,0)} D_{(0,wⱼ)} ⋯ D_{(0,w₁)} f)(x, y)`
of `f : E₁ × E₂ → F` ([GN26, Definition 1.7.17]): first `j` derivatives in the second
variable, then `i` derivatives in the first one. Junk values where the derivatives do not
exist. -/
def iteratedDMB₂ (i j : ℕ) (f : E₁ × E₂ → F) (p : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂)) :
    F :=
  iteratedDMB i (fun x ↦ iteratedDMB j (fun y ↦ f (x, y)) (p.1.2, p.2.2)) (p.1.1, p.2.1)

/-- **`C^{k,ℓ}` maps** on `U × V`, for `U ⊆ E₁` and `V ⊆ E₂` open
([GN26, Definition 1.7.17]). We use the form given by Lemma 1.7.18 and Remark 1.7.19(b): the partial
maps `f(x, ·)` are `C^ℓ` on `V`, the maps `x ↦ d^(0,j) f(x, y, w)` are `C^k` on `U`, and the mixed
differentials `d^(i,j) f` (`i ≤ k`, `j ≤ ℓ`) are continuous on `U × V × E₁^i × E₂^j`. By
Proposition 1.3.10 (`contDiffMBOn_iff_hasContIterDerivOn`) applied to the partial maps, this
says exactly that the iterated directional derivatives defining `d^(i,j) f` exist on `U × V` and
are continuous there, which is Glöckner–Neeb's definition for open `U` and `V`
(`contDiffMBOn₂_iff`). -/
structure ContDiffMBOn₂ [ContinuousSMul ℝ F] (k ℓ : ℕ) (f : E₁ × E₂ → F) (U : Set E₁)
    (V : Set E₂) : Prop where
  /-- The partial maps `f(x, ·)` are `C^ℓ` ([GN26, Lemma 1.7.18]). -/
  contDiffMBOn_right : ∀ x ∈ U, ContDiffMBOn ℓ (fun y ↦ f (x, y)) V
  /-- The maps `x ↦ d^(0,j) f(x, y, w)` are `C^k` ([GN26, Remark 1.7.19(b)]). -/
  contDiffMBOn_left : ∀ j ≤ ℓ, ∀ y ∈ V, ∀ w : Fin j → E₂,
    ContDiffMBOn k (fun x ↦ iteratedDMB j (fun y ↦ f (x, y)) (y, w)) U
  /-- The mixed differentials are continuous. -/
  continuousOn : ∀ i ≤ k, ∀ j ≤ ℓ,
    ContinuousOn (iteratedDMB₂ i j f) (((U ×ˢ V) : Set (E₁ × E₂)) ×ˢ univ)

end Definition

section Schwarz

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The derivative of `d^(i,j) f` in the first variable is `d^(i+1,j) f`. -/
theorem ContDiffMBOn₂.hasDirDerivAt_left (hf : ContDiffMBOn₂ k ℓ f U V) {i j : ℕ} (hi : i < k)
    (hj : j ≤ ℓ) {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V) (v : Fin (i + 1) → E₁)
    (w : Fin j → E₂) :
    HasDirDerivAt (fun x' ↦ iteratedDMB₂ i j f ((x', y), Fin.init v, w)) x (v (Fin.last i))
      (iteratedDMB₂ (i + 1) j f ((x, y), v, w)) :=
  (hf.contDiffMBOn_left j hj y hy w).hasContIterDerivOn.1 i hi x hx v

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **Mixed differentials, Schwarz** (the case needed from [GN26, Proposition 1.7.21]):
the derivative of `d^(i,j) f` in the second variable is `d^(i,j+1) f`, for `i ≤ k`, `j < ℓ`. -/
theorem ContDiffMBOn₂.hasDirDerivAt_right (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) : ∀ i ≤ k, ∀ j < ℓ, ∀ x ∈ U, ∀ y ∈ V, ∀ (v : Fin i → E₁)
      (w : Fin j → E₂) (b : E₂), HasDirDerivAt (fun y' ↦ iteratedDMB₂ i j f ((x, y'), v, w)) y b
        (iteratedDMB₂ i (j + 1) f ((x, y), v, Fin.snoc w b)) := by
  intro i
  induction i with
  | zero =>
    intro _ j hj x hx y hy v w b
    have h := (hf.contDiffMBOn_right x hx).hasContIterDerivOn.1 j hj y hy (Fin.snoc w b)
    simp only [Fin.init_snoc, Fin.snoc_last] at h
    exact h
  | succ i ih =>
    intro hi j hj x hx y hy v w b
    have hUV : IsOpen (U ×ˢ V) := hU.prod hV
    have h := hasDirDerivAt_comm (E := E₁ × E₂) hUV (a := (v (Fin.last i), 0)) (b := (0, b))
      (g := fun p ↦ iteratedDMB₂ i j f (p, Fin.init v, w))
      (A := fun p ↦ iteratedDMB₂ (i + 1) j f (p, v, w))
      (B := fun p ↦ iteratedDMB₂ i (j + 1) f (p, Fin.init v, Fin.snoc w b))
      (M := fun p ↦ iteratedDMB₂ (i + 1) (j + 1) f (p, v, Fin.snoc w b))
      (fun p hp ↦ hasDirDerivAt_slice.2 (hf.hasDirDerivAt_left (by omega) hj.le hp.1 hp.2 v w))
      (fun p hp ↦ hasDirDerivAt_slice₂.2 (ih (by omega) j hj p.1 hp.1 p.2 hp.2 _ w b))
      ((hf.continuousOn i (by omega) (j + 1) hj).comp (by fun_prop)
        fun p hp ↦ ⟨hp, mem_univ _⟩)
      (fun p hp ↦ hasDirDerivAt_slice.2 (hf.hasDirDerivAt_left (by omega) hj hp.1 hp.2 v _))
      ((hf.continuousOn (i + 1) hi (j + 1) hj).comp (by fun_prop)
        fun p hp ↦ ⟨hp, mem_univ _⟩)
      (show (x, y) ∈ U ×ˢ V from ⟨hx, hy⟩)
    exact hasDirDerivAt_slice₂.1 h

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The iterated differentials of `y ↦ d^(i,0) f(x, y, v)` are the `d^(i,j) f(x, y, v, ·)`. -/
theorem ContDiffMBOn₂.iteratedDMB_right (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) {i : ℕ} (hi : i ≤ k) {x : E₁} (hx : x ∈ U) (v : Fin i → E₁) :
    ∀ j ≤ ℓ, ∀ y ∈ V, ∀ w : Fin j → E₂,
      iteratedDMB j (fun y' ↦ iteratedDMB₂ i 0 f ((x, y'), v, Fin.elim0)) (y, w) =
        iteratedDMB₂ i j f ((x, y), v, w) := by
  intro j
  induction j with
  | zero =>
    intro _ y _ w
    rw [Subsingleton.elim w Fin.elim0]
    rfl
  | succ j ih =>
    intro hj y hy w
    rw [iteratedDMB_succ]
    have hev : (fun y' ↦ iteratedDMB j (fun y' ↦ iteratedDMB₂ i 0 f ((x, y'), v, Fin.elim0))
        (y', Fin.init w)) =ᶠ[𝓝 y] fun y' ↦ iteratedDMB₂ i j f ((x, y'), v, Fin.init w) :=
      Filter.eventually_of_mem (hV.mem_nhds hy) fun y' hy' ↦ ih (by omega) y' hy' _
    rw [dMB_congr_of_eventuallyEq hev]
    have h := hf.hasDirDerivAt_right hU hV i hi j (by omega) x hx y hy v (Fin.init w)
      (w (Fin.last j))
    rw [Fin.snoc_init_self] at h
    exact h.dMB_eq

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- **[GN26, Corollary 1.7.22]** (the part used for the exponential law): for `x ∈ U`,
`i ≤ k` and `v ∈ E₁^i`, the map `y ↦ d^(i,0) f(x, y, v)` is `C^ℓ` on `V`, with differentials
`d^(i,j) f(x, ·, v, ·)` (`ContDiffMBOn₂.iteratedDMB_right`). -/
theorem ContDiffMBOn₂.contDiffMBOn_right_iteratedDMB₂ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) {i : ℕ} (hi : i ≤ k) {x : E₁} (hx : x ∈ U)
    (v : Fin i → E₁) :
    ContDiffMBOn ℓ (fun y ↦ iteratedDMB₂ i 0 f ((x, y), v, Fin.elim0)) V := by
  refine HasContIterDerivOn.contDiffMBOn hV ⟨fun j hj y hy w ↦ ?_, fun j hj ↦ ?_⟩
  · rw [hf.iteratedDMB_right hU hV hi hx v (j + 1) hj y hy w]
    have hev : (fun y' ↦ iteratedDMB₂ i j f ((x, y'), v, Fin.init w)) =ᶠ[𝓝 y]
        fun y' ↦ iteratedDMB j (fun y' ↦ iteratedDMB₂ i 0 f ((x, y'), v, Fin.elim0))
          (y', Fin.init w) :=
      Filter.eventually_of_mem (hV.mem_nhds hy) fun y' hy' ↦
        (hf.iteratedDMB_right hU hV hi hx v j hj.le y' hy' _).symm
    have h := hf.hasDirDerivAt_right hU hV i hi j hj x hx y hy v (Fin.init w) (w (Fin.last j))
    rw [Fin.snoc_init_self] at h
    exact h.congr_of_eventuallyEq hev
  · refine ((hf.continuousOn i hi j hj).comp
      (f := fun p : E₂ × (Fin j → E₂) ↦ (((x, p.1) : E₁ × E₂), v, p.2)) (by fun_prop)
      fun p (hp : p ∈ V ×ˢ (univ : Set (Fin j → E₂))) ↦ ⟨⟨hx, hp.1⟩, mem_univ _⟩).congr
      fun p hp ↦ ?_
    exact hf.iteratedDMB_right hU hV hi hx v j hj p.1 hp.1 p.2

/-- **[GN26, Definition 1.7.17]** (open `U`, `V`), literally: `f` is `C^{k,ℓ}` if and only
if the iterated directional derivatives `d^(i,j) f` (first in the second variable, then in the
first one) exist on `U × V` for `i ≤ k`, `j ≤ ℓ`, and are continuous on `U × V × E₁^i × E₂^j`. -/
theorem contDiffMBOn₂_iff (hU : IsOpen U) (hV : IsOpen V) :
    ContDiffMBOn₂ k ℓ f U V ↔
      (∀ j < ℓ, ∀ x ∈ U, ∀ y ∈ V, ∀ w : Fin (j + 1) → E₂,
        HasDirDerivAt (fun y' ↦ iteratedDMB₂ 0 j f ((x, y'), Fin.elim0, Fin.init w)) y
          (w (Fin.last j)) (iteratedDMB₂ 0 (j + 1) f ((x, y), Fin.elim0, w))) ∧
      (∀ i < k, ∀ j ≤ ℓ, ∀ x ∈ U, ∀ y ∈ V, ∀ (v : Fin (i + 1) → E₁) (w : Fin j → E₂),
        HasDirDerivAt (fun x' ↦ iteratedDMB₂ i j f ((x', y), Fin.init v, w)) x (v (Fin.last i))
          (iteratedDMB₂ (i + 1) j f ((x, y), v, w))) ∧
      (∀ i ≤ k, ∀ j ≤ ℓ,
        ContinuousOn (iteratedDMB₂ i j f) (((U ×ˢ V) : Set (E₁ × E₂)) ×ˢ univ)) := by
  refine ⟨fun hf ↦ ⟨fun j hj x hx y hy w ↦ (hf.contDiffMBOn_right x hx).hasContIterDerivOn.1 j hj
    y hy w, fun i hi j hj x hx y hy v w ↦ hf.hasDirDerivAt_left hi hj hx hy v w,
    hf.continuousOn⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨fun x hx ↦ ?_, fun j hj y hy w ↦ ?_, h3⟩⟩
  · refine HasContIterDerivOn.contDiffMBOn hV ⟨fun j hj y hy w ↦ h1 j hj x hx y hy w,
      fun j hj ↦ ?_⟩
    exact (h3 0 (Nat.zero_le k) j hj).comp
      (f := fun p : E₂ × (Fin j → E₂) ↦ (((x, p.1) : E₁ × E₂), (Fin.elim0 : Fin 0 → E₁), p.2))
      (by fun_prop) fun p (hp : p ∈ V ×ˢ (univ : Set (Fin j → E₂))) ↦ ⟨⟨hx, hp.1⟩, mem_univ _⟩
  · refine HasContIterDerivOn.contDiffMBOn hU ⟨fun i hi x hx v ↦ h2 i hi j hj x hx y hy v w,
      fun i hi ↦ ?_⟩
    exact (h3 i hi j hj).comp
      (f := fun p : E₁ × (Fin i → E₁) ↦ (((p.1, y) : E₁ × E₂), p.2, w))
      (by fun_prop) fun p (hp : p ∈ U ×ˢ (univ : Set (Fin i → E₁))) ↦ ⟨⟨hp.1, hy⟩, mem_univ _⟩

end Schwarz

/-! ### Algebraic operations and `C^{k+ℓ} ⊆ C^{k,ℓ}` -/

section Algebra

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {U : Set E₁} {V : Set E₂}

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [ContinuousSMul ℝ F] in
/-- The iterated differentials of the zero map vanish. -/
theorem iteratedDMB_const_zero {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] :
    ∀ (j : ℕ) (p : E × (Fin j → E)), iteratedDMB j (fun _ : E ↦ (0 : F)) p = 0
  | 0, _ => rfl
  | j + 1, p => by
    rw [show p = (p.1, p.2) from rfl, iteratedDMB_succ]
    simp only [iteratedDMB_const_zero j]
    exact (show HasDirDerivAt (fun _ : E ↦ (0 : F)) p.1 (p.2 (Fin.last j)) 0 by
      simp only [HasDirDerivAt, sub_self, smul_zero]; exact tendsto_const_nhds).dMB_eq

omit [LocallyConvexSpace ℝ F] in
/-- Mixed differentials of a sum. -/
theorem ContDiffMBOn₂.iteratedDMB₂_add (hU : IsOpen U) (hV : IsOpen V) {f g : E₁ × E₂ → F}
    (hf : ContDiffMBOn₂ k ℓ f U V) (hg : ContDiffMBOn₂ k ℓ g U V) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ ℓ) {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V) (v : Fin i → E₁) (w : Fin j → E₂) :
    iteratedDMB₂ i j (fun p ↦ f p + g p) ((x, y), v, w) =
      iteratedDMB₂ i j f ((x, y), v, w) + iteratedDMB₂ i j g ((x, y), v, w) := by
  have hev : (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y') + g (x', y')) (y, w)) =ᶠ[𝓝 x]
      fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w) +
        iteratedDMB j (fun y' ↦ g (x', y')) (y, w) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun x' hx' ↦
      iteratedDMB_add hV (hf.contDiffMBOn_right x' hx') (hg.contDiffMBOn_right x' hx') hj hy w
  change iteratedDMB i (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y') + g (x', y')) (y, w)) (x, v) = _
  rw [iteratedDMB_congr_of_eventuallyEq i hev]
  exact iteratedDMB_add hU (hf.contDiffMBOn_left j hj y hy w) (hg.contDiffMBOn_left j hj y hy w)
    hi hx v

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂]
  [T2Space E₂] [LocallyConvexSpace ℝ F] in
/-- Mixed differentials of a multiple. -/
theorem ContDiffMBOn₂.iteratedDMB₂_const_smul (hU : IsOpen U) (hV : IsOpen V) {f : E₁ × E₂ → F}
    (hf : ContDiffMBOn₂ k ℓ f U V) (c : ℝ) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ ℓ) {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V) (v : Fin i → E₁) (w : Fin j → E₂) :
    iteratedDMB₂ i j (fun p ↦ c • f p) ((x, y), v, w) = c • iteratedDMB₂ i j f ((x, y), v, w) := by
  have hev : (fun x' ↦ iteratedDMB j (fun y' ↦ c • f (x', y')) (y, w)) =ᶠ[𝓝 x]
      fun x' ↦ c • iteratedDMB j (fun y' ↦ f (x', y')) (y, w) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun x' hx' ↦
      iteratedDMB_const_smul hV (hf.contDiffMBOn_right x' hx') c hj hy w
  change iteratedDMB i (fun x' ↦ iteratedDMB j (fun y' ↦ c • f (x', y')) (y, w)) (x, v) = _
  rw [iteratedDMB_congr_of_eventuallyEq i hev]
  exact iteratedDMB_const_smul hU (hf.contDiffMBOn_left j hj y hy w) c hi hx v

/-- Sums of `C^{k,ℓ}` maps are `C^{k,ℓ}`. -/
theorem ContDiffMBOn₂.add (hU : IsOpen U) (hV : IsOpen V) {f g : E₁ × E₂ → F}
    (hf : ContDiffMBOn₂ k ℓ f U V) (hg : ContDiffMBOn₂ k ℓ g U V) :
    ContDiffMBOn₂ k ℓ (fun p ↦ f p + g p) U V where
  contDiffMBOn_right x hx := (hf.contDiffMBOn_right x hx).add hV (hg.contDiffMBOn_right x hx)
  contDiffMBOn_left j hj y hy w :=
    ContDiffMBOn.congr_of_isOpen hU (fun x' hx' ↦ (iteratedDMB_add hV (hf.contDiffMBOn_right x' hx')
      (hg.contDiffMBOn_right x' hx') hj hy w).symm)
      ((hf.contDiffMBOn_left j hj y hy w).add hU (hg.contDiffMBOn_left j hj y hy w))
  continuousOn i hi j hj :=
    ((hf.continuousOn i hi j hj).add (hg.continuousOn i hi j hj)).congr fun p hp ↦
      hf.iteratedDMB₂_add hU hV hg hi hj hp.1.1 hp.1.2 p.2.1 p.2.2

/-- Multiples of `C^{k,ℓ}` maps are `C^{k,ℓ}`. -/
theorem ContDiffMBOn₂.const_smul (hU : IsOpen U) (hV : IsOpen V) {f : E₁ × E₂ → F}
    (hf : ContDiffMBOn₂ k ℓ f U V) (c : ℝ) : ContDiffMBOn₂ k ℓ (fun p ↦ c • f p) U V where
  contDiffMBOn_right x hx := (hf.contDiffMBOn_right x hx).const_smul hV c
  contDiffMBOn_left j hj y hy w :=
    ContDiffMBOn.congr_of_isOpen hU (fun x' hx' ↦ (iteratedDMB_const_smul hV
      (hf.contDiffMBOn_right x' hx') c hj hy w).symm)
      ((hf.contDiffMBOn_left j hj y hy w).const_smul hU c)
  continuousOn i hi j hj :=
    ((hf.continuousOn i hi j hj).const_smul c).congr fun p hp ↦
      hf.iteratedDMB₂_const_smul hU hV c hi hj hp.1.1 hp.1.2 p.2.1 p.2.2

omit [LocallyConvexSpace ℝ F] [IsTopologicalAddGroup F] in
/-- The zero map is `C^{k,ℓ}`. -/
theorem contDiffMBOn₂_zero : ContDiffMBOn₂ k ℓ (fun _ : E₁ × E₂ ↦ (0 : F)) U V where
  contDiffMBOn_right _ _ := contDiffMBOn_const ℓ (0 : F) V
  contDiffMBOn_left j _ y _ w := by
    simp only [iteratedDMB_const_zero]
    exact contDiffMBOn_const k (0 : F) U
  continuousOn i _ j _ := by
    have : iteratedDMB₂ i j (fun _ : E₁ × E₂ ↦ (0 : F)) = fun _ ↦ 0 := by
      funext p
      simp only [iteratedDMB₂, iteratedDMB_const_zero]
    rw [this]
    exact continuousOn_const

end Algebra

/-! ### The space `C^{k,ℓ}(U × V, F)` -/

section Space

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (F) in
/-- The `C^{k,ℓ}` maps on `U × V`, extended by `0` outside `U × V`, as a submodule of
`E₁ × E₂ → F`. -/
def contDiffMBSubmodule₂ (k ℓ : ℕ) (U : Opens E₁) (V : Opens E₂) : Submodule ℝ (E₁ × E₂ → F) where
  carrier := {f | ContDiffMBOn₂ k ℓ f U V ∧ ∀ p ∉ (U : Set E₁) ×ˢ (V : Set E₂), f p = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add U.isOpen V.isOpen hg.1, fun p hp ↦ by
    simp [hf.2 p hp, hg.2 p hp]⟩
  zero_mem' := ⟨contDiffMBOn₂_zero, fun _ _ ↦ rfl⟩
  smul_mem' c f hf := ⟨hf.1.const_smul U.isOpen V.isOpen c, fun p hp ↦ by simp [hf.2 p hp]⟩

variable (F) in
/-- **The space `C^{k,ℓ}(U × V, F)`** of `C^{k,ℓ}` maps on `U × V`, extended by `0` outside
`U × V`, with the compact-open `C^{k,ℓ}` topology ([GN26, Definition 1.7.17]): the initial
topology with respect to the mixed differentials
`d^(i,j) : C^{k,ℓ}(U × V, F) → C(U × V × E₁^i × E₂^j, F)`, `i ≤ k`, `j ≤ ℓ`. -/
def ContDiffMBMap₂ (k ℓ : ℕ) (U : Opens E₁) (V : Opens E₂) : Type (max u u' v) :=
  contDiffMBSubmodule₂ F k ℓ U V

namespace ContDiffMBMap₂

variable {k ℓ : ℕ} {U : Opens E₁} {V : Opens E₂}

/-- The vector space operations of `C^{k,ℓ}(U × V, F)` are pointwise. -/
instance : AddCommGroup (ContDiffMBMap₂ F k ℓ U V) :=
  inferInstanceAs (AddCommGroup (contDiffMBSubmodule₂ F k ℓ U V))

/-- The vector space operations of `C^{k,ℓ}(U × V, F)` are pointwise. -/
instance : Module ℝ (ContDiffMBMap₂ F k ℓ U V) :=
  inferInstanceAs (Module ℝ (contDiffMBSubmodule₂ F k ℓ U V))

/-- An element of `C^{k,ℓ}(U × V, F)` is a map `E₁ × E₂ → F`. -/
instance : FunLike (ContDiffMBMap₂ F k ℓ U V) (E₁ × E₂) F where
  coe γ := Subtype.val (γ : contDiffMBSubmodule₂ F k ℓ U V)
  coe_injective := Subtype.val_injective

/-- The element of `C^{k,ℓ}(U × V, F)` given by a `C^{k,ℓ}` map vanishing outside `U × V`. -/
def mk (f : E₁ × E₂ → F) (hf : ContDiffMBOn₂ k ℓ f U V)
    (h0 : ∀ p ∉ (U : Set E₁) ×ˢ (V : Set E₂), f p = 0) : ContDiffMBMap₂ F k ℓ U V :=
  ⟨f, hf, h0⟩

/-- The underlying map of `ContDiffMBMap₂.mk f hf h0` is `f`. -/
@[simp]
theorem coe_mk (f : E₁ × E₂ → F) (hf : ContDiffMBOn₂ k ℓ f U V)
    (h0 : ∀ p ∉ (U : Set E₁) ×ˢ (V : Set E₂), f p = 0) : ⇑(mk f hf h0) = f :=
  rfl

/-- An element of `C^{k,ℓ}(U × V, F)` is `C^{k,ℓ}` on `U × V`. -/
theorem contDiffMBOn₂ (γ : ContDiffMBMap₂ F k ℓ U V) : ContDiffMBOn₂ k ℓ γ U V :=
  (γ : contDiffMBSubmodule₂ F k ℓ U V).2.1

/-- An element of `C^{k,ℓ}(U × V, F)` vanishes outside `U × V`. -/
theorem apply_of_notMem (γ : ContDiffMBMap₂ F k ℓ U V) {p : E₁ × E₂}
    (hp : p ∉ (U : Set E₁) ×ˢ (V : Set E₂)) : γ p = 0 :=
  (γ : contDiffMBSubmodule₂ F k ℓ U V).2.2 p hp

/-- Elements of `C^{k,ℓ}(U × V, F)` are equal if they agree as maps. -/
@[ext]
theorem ext {γ η : ContDiffMBMap₂ F k ℓ U V} (h : ∀ p, γ p = η p) : γ = η :=
  DFunLike.ext _ _ h

/-- Addition in `C^{k,ℓ}(U × V, F)` is pointwise. -/
@[simp]
theorem coe_add (γ η : ContDiffMBMap₂ F k ℓ U V) : ⇑(γ + η) = γ + η :=
  rfl

/-- Scalar multiplication in `C^{k,ℓ}(U × V, F)` is pointwise. -/
@[simp]
theorem coe_smul (c : ℝ) (γ : ContDiffMBMap₂ F k ℓ U V) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The mixed differential `d^(i,j)γ ∈ C(U × V × E₁^i × E₂^j, F)`, `i ≤ k`, `j ≤ ℓ`. -/
def iteratedD₂ (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) (γ : ContDiffMBMap₂ F k ℓ U V) :
    C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) where
  toFun p := iteratedDMB₂ i j γ (((p.1.1 : E₁), (p.1.2 : E₂)), p.2.1, p.2.2)
  continuous_toFun := (γ.contDiffMBOn₂.continuousOn i hi j hj).comp_continuous (by fun_prop)
    fun p ↦ ⟨⟨p.1.1.2, p.1.2.2⟩, mem_univ _⟩

/-- `d^(i,j)γ(x, y, v, w) = iteratedDMB₂ i j γ ((x, y), v, w)`. -/
@[simp]
theorem iteratedD₂_apply (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) (γ : ContDiffMBMap₂ F k ℓ U V)
    (p : (U × V) × (Fin i → E₁) × (Fin j → E₂)) :
    iteratedD₂ i j hi hj γ p = iteratedDMB₂ i j γ (((p.1.1 : E₁), (p.1.2 : E₂)), p.2.1, p.2.2) :=
  rfl

/-- `d^(i,j)` as a linear map. -/
def iteratedDL₂ (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) :
    ContDiffMBMap₂ F k ℓ U V →ₗ[ℝ] C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) where
  toFun := iteratedD₂ i j hi hj
  map_add' γ η := by
    ext p
    exact γ.contDiffMBOn₂.iteratedDMB₂_add U.isOpen V.isOpen η.contDiffMBOn₂ hi hj p.1.1.2
      p.1.2.2 p.2.1 p.2.2
  map_smul' c γ := by
    ext p
    exact γ.contDiffMBOn₂.iteratedDMB₂_const_smul U.isOpen V.isOpen c hi hj p.1.1.2 p.1.2.2
      p.2.1 p.2.2

/-- The linear map `γ ↦ (d^(i,j)γ)_{i ≤ k, j ≤ ℓ}`. -/
def toPi : ContDiffMBMap₂ F k ℓ U V →ₗ[ℝ]
    ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)), C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    iteratedDL₂ i j (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2)

/-- The mixed differentials separate the points of `C^{k,ℓ}(U × V, F)`. -/
theorem toPi_injective :
    Function.Injective (toPi (F := F) (k := k) (ℓ := ℓ) (U := U) (V := V)) := by
  intro γ η h
  ext p
  by_cases hp : p ∈ (U : Set E₁) ×ˢ (V : Set E₂)
  · exact congrArg (fun φ ↦ φ 0 0 ((⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), Fin.elim0, Fin.elim0)) h
  · rw [γ.apply_of_notMem hp, η.apply_of_notMem hp]

/-- **The compact-open `C^{k,ℓ}` topology** ([GN26, Definition 1.7.17]). -/
instance : TopologicalSpace (ContDiffMBMap₂ F k ℓ U V) :=
  .induced toPi inferInstance

/-- `γ ↦ (d^(i,j)γ)_{i,j}` is a linear topological embedding. -/
theorem isEmbedding_toPi :
    Topology.IsEmbedding (toPi (F := F) (k := k) (ℓ := ℓ) (U := U) (V := V)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

/-- `C^{k,ℓ}(U × V, F)` is a topological additive group. -/
instance : IsTopologicalAddGroup (ContDiffMBMap₂ F k ℓ U V) :=
  isTopologicalAddGroup_induced toPi

/-- Scalar multiplication on `C^{k,ℓ}(U × V, F)` is continuous. -/
instance : ContinuousSMul ℝ (ContDiffMBMap₂ F k ℓ U V) :=
  continuousSMul_induced toPi

/-- `C^{k,ℓ}(U × V, F)` is locally convex. -/
instance : LocallyConvexSpace ℝ (ContDiffMBMap₂ F k ℓ U V) :=
  LocallyConvexSpace.induced toPi

/-- `C^{k,ℓ}(U × V, F)` is Hausdorff. -/
instance : T2Space (ContDiffMBMap₂ F k ℓ U V) :=
  isEmbedding_toPi.t2Space

/-- `d^(i,j) : C^{k,ℓ}(U × V, F) → C(U × V × E₁^i × E₂^j, F)` is continuous. -/
theorem continuous_iteratedD₂ (i j : ℕ) (hi : i ≤ k) (hj : j ≤ ℓ) :
    Continuous (iteratedD₂ (F := F) (U := U) (V := V) i j hi hj) := by
  have h : Continuous (toPi (F := F) (k := k) (ℓ := ℓ) (U := U) (V := V)) := continuous_induced_dom
  exact (continuous_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (ℓ + 1))).comp
    ((continuous_apply (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (k + 1))).comp h)

/-- A map into `C^{k,ℓ}(U × V, F)` is continuous if and only if its compositions with all the
mixed differentials are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → ContDiffMBMap₂ F k ℓ U V} :
    Continuous φ ↔ ∀ i j (hi : i ≤ k) (hj : j ≤ ℓ), Continuous fun x ↦ iteratedD₂ i j hi hj (φ x) :=
  ⟨fun h i j hi hj ↦ (continuous_iteratedD₂ i j hi hj).comp h, fun h ↦
    continuous_induced_rng.2 (continuous_pi fun i ↦ continuous_pi fun j ↦
      h i j (Nat.lt_succ_iff.mp i.2) (Nat.lt_succ_iff.mp j.2))⟩

end ContDiffMBMap₂

end Space

/-! ### `C^{k+ℓ}` maps are `C^{k,ℓ}`: Proposition 1.7.33(a) -/

section Inclusion

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁] [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
  [LocallyConvexSpace ℝ E₂] [T2Space E₂] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
  [T2Space F] [ContinuousSMul ℝ F] in
omit [TopologicalSpace E₂] in
/-- Differentials of a slice `y ↦ g (x, y)` are differentials of `g` in directions `(0, w)`. -/
theorem iteratedDMB_slice₂ : ∀ (j : ℕ) (g : E₁ × E₂ → F) (x : E₁) (y : E₂) (w : Fin j → E₂),
    iteratedDMB j (fun y' ↦ g (x, y')) (y, w) = iteratedDMB j g ((x, y), fun s ↦ (0, w s))
  | 0, _, _, _, _ => rfl
  | j + 1, g, x, y, w => by
    rw [iteratedDMB_succ, iteratedDMB_succ, dMB_slice₂]
    simp only [iteratedDMB_slice₂ j]
    rfl

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `d^(i)` of `z ↦ d^(j) g(z, w)` is `d^(j+i) g`: the directions are concatenated. -/
theorem iteratedDMB_iteratedDMB {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (g : E → F) (j : ℕ) (w : Fin j → E) :
    ∀ (i : ℕ) (z : E) (v : Fin i → E),
      iteratedDMB i (fun z' ↦ iteratedDMB j g (z', w)) (z, v) =
        iteratedDMB (j + i) g (z, Fin.append w v)
  | 0, z, v => by
    rw [Fin.append_right_nil w v rfl]
    rfl
  | i + 1, z, v => by
    rw [iteratedDMB_succ]
    have e : (fun z' ↦ iteratedDMB i (fun z' ↦ iteratedDMB j g (z', w)) (z', Fin.init v)) =
        fun z' ↦ iteratedDMB (j + i) g (z', Fin.append w (Fin.init v)) :=
      funext fun z' ↦ iteratedDMB_iteratedDMB g j w i z' _
    rw [e]
    change _ = iteratedDMB ((j + i) + 1) g (z, Fin.append (m := j) (n := i + 1) w v)
    rw [iteratedDMB_succ]
    have h1 : Fin.init (Fin.append (m := j) (n := i + 1) w v) = Fin.append w (Fin.init v) := by
      funext t
      refine Fin.addCases (fun s ↦ ?_) (fun s ↦ ?_) t
      · simp only [Fin.init]
        rw [show (Fin.castAdd i s).castSucc = Fin.castAdd (i + 1) s from rfl, Fin.append_left,
          Fin.append_left]
      · simp only [Fin.init]
        rw [show (Fin.natAdd j s).castSucc = Fin.natAdd j s.castSucc from rfl, Fin.append_right,
          Fin.append_right]
        rfl
    have h2 : Fin.append (m := j) (n := i + 1) w v (Fin.last (j + i)) = v (Fin.last i) := by
      rw [show Fin.last (j + i) = Fin.natAdd j (Fin.last i) from rfl, Fin.append_right]
    rw [h1, h2]

omit [ContinuousSMul ℝ F] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁] [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
  [LocallyConvexSpace ℝ E₂] [T2Space E₂] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F]
  [T2Space F] in
/-- The mixed differentials as differentials on `E₁ × E₂`:
`d^(i,j) f(x, y, v, w) = d^(j+i) f((x, y), (0, w₁), …, (0, wⱼ), (v₁, 0), …, (vᵢ, 0))`
([GN26, (1.107)]). This is an identity between iterated limits and needs no hypothesis on
`f`. -/
theorem iteratedDMB₂_eq_iteratedDMB (f : E₁ × E₂ → F) (i j : ℕ)
    (p : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂)) :
    iteratedDMB₂ i j f p = iteratedDMB (j + i) f
      (p.1, Fin.append (fun s ↦ ((0 : E₁), p.2.2 s)) fun s ↦ (p.2.1 s, (0 : E₂))) := by
  have e : (fun x ↦ iteratedDMB j (fun y ↦ f (x, y)) (p.1.2, p.2.2)) =
      fun x ↦ iteratedDMB j f ((x, p.1.2), fun s ↦ (0, p.2.2 s)) :=
    funext fun x ↦ iteratedDMB_slice₂ j f x p.1.2 p.2.2
  change iteratedDMB i (fun x ↦ iteratedDMB j (fun y ↦ f (x, y)) (p.1.2, p.2.2)) (p.1.1, p.2.1) = _
  rw [e, iteratedDMB_slice i (fun z ↦ iteratedDMB j f (z, fun s ↦ (0, p.2.2 s))),
    iteratedDMB_iteratedDMB]

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂]
  [T2Space E₂] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] [Module ℝ E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [Module ℝ E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] in
/-- `(x, y, v, w) ↦ ((x, y), (0, w₁), …, (0, wⱼ), (v₁, 0), …, (vᵢ, 0))` is continuous. -/
theorem continuous_append_directions (i j : ℕ) :
    Continuous fun p : (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂) ↦
      (p.1, Fin.append (fun s ↦ ((0 : E₁), p.2.2 s)) fun s ↦ (p.2.1 s, (0 : E₂))) := by
  refine continuous_fst.prodMk (continuous_pi fun t ↦ ?_)
  refine Fin.addCases (fun s ↦ ?_) (fun s ↦ ?_) t
  · simp only [Fin.append_left]
    fun_prop
  · simp only [Fin.append_right]
    fun_prop

/-- **[GN26, Proposition 1.7.33(a)]**: every map that is `C^{k+ℓ}` on `U × V` is
`C^{k,ℓ}` there. -/
theorem ContDiffMBOn.contDiffMBOn₂ {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffMBOn (k + ℓ) f (U ×ˢ V)) :
    ContDiffMBOn₂ k ℓ f U V where
  contDiffMBOn_right x hx := by
    have hp : ContDiffMBOn ℓ (fun y : E₂ ↦ (x, y)) V :=
      ContDiffMBOn.prodMk hV (contDiffMBOn_const ℓ x V)
        ((ContinuousLinearMap.id ℝ E₂).contDiffMBOn ℓ V)
    exact ContDiffMBOn.comp hV (hU.prod hV) (hf.of_le (by omega)) hp fun y hy ↦ ⟨hx, hy⟩
  contDiffMBOn_left j hj y hy w := by
    have hp : ContDiffMBOn k (fun x : E₁ ↦ (x, y)) U :=
      ContDiffMBOn.prodMk hU ((ContinuousLinearMap.id ℝ E₁).contDiffMBOn k U)
        (contDiffMBOn_const k y U)
    have h := (hf.of_le (show j + k ≤ k + ℓ by omega)).contDiffMBOn_iteratedDMB_slice
      (k := j) (r := k) (hU.prod hV) (fun s ↦ (0, w s))
    have e : (fun x ↦ iteratedDMB j (fun y' ↦ f (x, y')) (y, w)) =
        (fun z ↦ iteratedDMB j f (z, fun s ↦ (0, w s))) ∘ fun x ↦ (x, y) :=
      funext fun x ↦ iteratedDMB_slice₂ j f x y w
    rw [e]
    exact ContDiffMBOn.comp hU (hU.prod hV) h hp fun x hx ↦ ⟨hx, hy⟩
  continuousOn i hi j hj := by
    have h := (hf.hasContIterDerivOn.2 (j + i) (by omega)).comp
      (continuous_append_directions i j).continuousOn
      fun p (hp : p ∈ ((U ×ˢ V : Set (E₁ × E₂))) ×ˢ (univ : Set ((Fin i → E₁) × (Fin j → E₂)))) ↦
        ⟨hp.1, mem_univ _⟩
    exact h.congr fun p _ ↦ iteratedDMB₂_eq_iteratedDMB f i j p

/-- The open set `U × V ⊆ E₁ × E₂`. -/
def Opens.prod (U : Opens E₁) (V : Opens E₂) : Opens (E₁ × E₂) :=
  ⟨(U : Set E₁) ×ˢ (V : Set E₂), U.isOpen.prod V.isOpen⟩

namespace ContDiffMBMap₂

variable {k ℓ : ℕ} {U : Opens E₁} {V : Opens E₂}

/-- The inclusion `C^{k+ℓ}(U × V, F) → C^{k,ℓ}(U × V, F)`. -/
def ofContDiffMBMap (γ : ContDiffMBMap F (k + ℓ) (Opens.prod U V)) : ContDiffMBMap₂ F k ℓ U V :=
  mk γ (γ.contDiffMBOn.contDiffMBOn₂ U.isOpen V.isOpen) fun _ hp ↦ γ.apply_of_notMem hp

/-- **[GN26, Proposition 1.7.33(a)]**: the inclusion
`C^{k+ℓ}(U × V, F) → C^{k,ℓ}(U × V, F)` is continuous linear. -/
def ofContDiffMBMapCLM :
    ContDiffMBMap F (k + ℓ) (Opens.prod U V) →L[ℝ] ContDiffMBMap₂ F k ℓ U V where
  toFun := ofContDiffMBMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_iff.2 fun i j hi hj ↦ by
    let A : C((U × V) × (Fin i → E₁) × (Fin j → E₂), (Opens.prod U V) × (Fin (j + i) → E₁ × E₂)) :=
      ⟨fun p ↦ (⟨((p.1.1 : E₁), (p.1.2 : E₂)), p.1.1.2, p.1.2.2⟩,
        Fin.append (fun s ↦ ((0 : E₁), p.2.2 s)) fun s ↦ (p.2.1 s, (0 : E₂))), by
        refine Continuous.prodMk (Continuous.subtype_mk (by fun_prop) _) ?_
        exact continuous_snd.comp ((continuous_append_directions i j).comp
          (f := fun p : (U × V) × (Fin i → E₁) × (Fin j → E₂) ↦
            ((((p.1.1 : E₁), (p.1.2 : E₂)) : E₁ × E₂), p.2.1, p.2.2)) (by fun_prop))⟩
    have e : ∀ γ : ContDiffMBMap F (k + ℓ) (Opens.prod U V),
        iteratedD₂ i j hi hj (ofContDiffMBMap γ) =
          (ContDiffMBMap.iteratedD (j + i) (by omega) γ).comp A := fun γ ↦
      ContinuousMap.ext fun p ↦ iteratedDMB₂_eq_iteratedDMB γ i j _
    simp only [e]
    exact (ContinuousMap.continuous_precomp A).comp (ContDiffMBMap.continuous_iteratedD _ _)

end ContDiffMBMap₂

end Inclusion

end LocallyConvex.Analysis

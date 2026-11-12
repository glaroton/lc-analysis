/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.ExponentialLaw

/-!
# `C^{k,k}` maps are `C^k`, and the exponential law for smooth maps

Let `E₁`, `E₂`, `F` be locally convex spaces and `U ⊆ E₁`, `V ⊆ E₂` open. We prove
[GN26, Proposition 1.7.33(b)]: `C^{k,k}` maps on `U × V` are `C^k`; [GN26, Corollary 1.7.34]:
smooth maps on `U × V` are the `C^{∞,∞}` maps; and [GN26, Corollary 1.7.35], the exponential
law for smooth maps.

## Main definitions

* `ContDiffMBMap₂.toContDiffMBMap`, `ContDiffMBMap₂.toContDiffMBMapCLM`: the inclusion
  `μ : C^{k,k}(U × V, F) → C^k(U × V, F)`.
* `SmoothMBMap₂ F U V`: the space `C^{∞,∞}(U × V, F)` with the initial topology with respect to
  all the mixed differentials `d^(i,j)` ([GN26, Definition 1.7.17] with `k = ℓ = ∞`).
* `SmoothMBMap.partialMap`, `SmoothMBMap.curry`, `SmoothMBMap.curryCLM`: the partial map
  `f^∨(x) = f(x, ·) ∈ C^∞(V, F)` and `Φ : C^∞(U × V, F) → C^∞(U, C^∞(V, F))`, `f ↦ f^∨`.
* `SmoothMBMap.uncurry`: `g ↦ g^∧`, `g^∧(x, y) = g(x)(y)`, for `E₂` locally compact.

## Main results

* `ContDiffMBOn₂.contDiffMBOn_prod`, `ContDiffMBMap₂.toContDiffMBMapCLM`: every `C^{k,k}` map on
  `U × V` is `C^k`, and the inclusion `μ : C^{k,k}(U × V, F) → C^k(U × V, F)` is continuous
  linear ([GN26, Proposition 1.7.33(b)]).
* `smoothMBOn_prod_iff`: a map on `U × V` is smooth if and only if it is `C^{∞,∞}`, and
  `SmoothMBMap₂.equivSmooth`: `C^∞(U × V, F) = C^{∞,∞}(U × V, F)` as locally convex spaces
  ([GN26, Corollary 1.7.34]).
* `SmoothMBMap.smoothMBOn_partialMap`, `SmoothMBMap.isEmbedding_curry`,
  `SmoothMBMap.curryEquiv`: the exponential law for smooth maps. For a smooth map `f` on
  `U × V`, `f^∨ : U → C^∞(V, F)` is smooth, and `Φ` is a linear topological embedding, an
  isomorphism of topological vector spaces if `E₂` is locally compact
  ([GN26, Corollary 1.7.35]).
* `SmoothMBMap.smoothMBOn_iff_smoothMBOn_uncurry`: for `E₂` locally compact,
  `g : U → C^∞(V, F)` is smooth if and only if `(x, y) ↦ g(x)(y)` is smooth
  ([GN26, Remark 1.7.31(b)], smooth case).
* `SmoothMBMap.contDiffMBOn_iff`: a map into `C^∞(V, F)` is `C^k` if and only if its
  compositions with the inclusions `C^∞(V, F) → C^ℓ(V, F)` are.

## Implementation notes

* **Departure from Glöckner–Neeb in Proposition 1.7.33(b).** Glöckner–Neeb prove the explicit
  formula (1.108) for `d^(m) f` in terms of the `d^(a,m-a) f` and deduce both statements from
  it. Here the induction is on the recursive definition of `C^k`: by the rule on partial
  differentials (`contDiffMBOn_one_of_partials`), `df((x, y), (a, b))` equals
  `d^(1,0) f(x, y, a) + d^(0,1) f(x, y, b)`, and this map of `((x, a), (y, b))` is `C^{k,k}`,
  with mixed differentials given by explicit formulas (`iteratedDMB₂_splitD₁`,
  `iteratedDMB₂_splitD₂`) that rest on the formula for the differentials of `dγ`
  (`ContDiffMBOn.iteratedDMB_dMB`). The continuity of `μ` follows by the same induction from the
  criterion `ContDiffMBMap.continuous_of_continuous_dMap`. The case `m = 1` of (1.108) is
  `ContDiffMBOn₂.contDiffMBOn_one`; the general case is `ContDiffMBOn₂.iteratedDMB_eq_sum` in
  `Calculus/CklSchwarz.lean`. We do not claim these arguments are new.
* **The exponential law for smooth maps** is deduced from the finite-order case
  (`ContDiffMBMap₂.curry`), as Glöckner–Neeb do, through `SmoothMBMap.contDiffMBOn_iff` and the
  formula (1.98).
* As in `Calculus/ExponentialLaw.lean`, the hypothesis "`V` locally compact" of Glöckner–Neeb is
  replaced by the local compactness of `E₂`, which is equivalent for nonempty open `V`; their
  alternative hypothesis on `k_ℝ`-spaces is treated for sets with dense interior, open sets
  included, in `Calculus/DenseInterior/SmoothExpLaw.lean` (`curryEquivOfKRSpace`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u u' v

section Sum

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- Iterated differentials of a finite sum of `C^k` maps. -/
theorem iteratedDMB_finset_sum {ι : Type*} (s : Finset ι) {g : ι → E → F} {W : Set E}
    (hW : IsOpen W) {k : ℕ} (hg : ∀ t ∈ s, ContDiffMBOn k (g t) W) {j : ℕ} (hj : j ≤ k) {x : E}
    (hx : x ∈ W) (v : Fin j → E) :
    iteratedDMB j (fun z ↦ ∑ t ∈ s, g t z) (x, v) = ∑ t ∈ s, iteratedDMB j (g t) (x, v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using iteratedDMB_const_zero (F := F) j (x, v)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [iteratedDMB_add hW (hg a (Finset.mem_insert_self a s))
      (ContDiffMBOn.sum s hW fun t ht ↦ hg t (Finset.mem_insert_of_mem ht)) hj hx v,
      ih fun t ht ↦ hg t (Finset.mem_insert_of_mem ht)]

end Sum

/-! ### The differential of a `C^{k+1,k+1}` map, split into its partial differentials -/

section Split

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

/-- The first partial differential `((x, a), (y, b)) ↦ d^(1,0) f(x, y, a)`. -/
def splitD₁ (f : E₁ × E₂ → F) (p : (E₁ × E₁) × (E₂ × E₂)) : F :=
  iteratedDMB₂ 1 0 f ((p.1.1, p.2.1), fun _ ↦ p.1.2, Fin.elim0)

/-- The second partial differential `((x, a), (y, b)) ↦ d^(0,1) f(x, y, b)`. -/
def splitD₂ (f : E₁ × E₂ → F) (p : (E₁ × E₁) × (E₂ × E₂)) : F :=
  iteratedDMB₂ 0 1 f ((p.1.1, p.2.1), Fin.elim0, fun _ ↦ p.2.2)

/-- The differential of `f`, with the variables regrouped:
`((x, a), (y, b)) ↦ d^(1,0) f(x, y, a) + d^(0,1) f(x, y, b)`. -/
def splitD (f : E₁ × E₂ → F) (p : (E₁ × E₁) × (E₂ × E₂)) : F :=
  splitD₁ f p + splitD₂ f p

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The differentials of `splitD₁ f` in the second variable. -/
theorem iteratedDMB_splitD₁_right (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) {j : ℕ} (hj : j ≤ k + 1) {xa : E₁ × E₁}
    (hxa : xa.1 ∈ U) {y : E₂} (hy : y ∈ V) (b : E₂) (ww : Fin j → E₂ × E₂) :
    iteratedDMB j (fun yb ↦ splitD₁ f (xa, yb)) ((y, b), ww) =
      dMB (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, fun t ↦ (ww t).1)) xa := by
  have e : (fun yb : E₂ × E₂ ↦ splitD₁ f (xa, yb)) =
      (fun y' ↦ iteratedDMB₂ 1 0 f ((xa.1, y'), fun _ ↦ xa.2, Fin.elim0)) ∘
        (LinearMap.fst ℝ E₂ E₂) := rfl
  rw [e, iteratedDMB_comp_linearMap]
  exact hf.iteratedDMB_right hU hV (i := 1) (by omega) hxa _ j hj y hy _

omit [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The mixed differentials of `splitD₁ f`. -/
theorem iteratedDMB₂_splitD₁ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ k + 1)
    {x a : E₁} {y b : E₂} (hx : x ∈ U) (hy : y ∈ V) (vv : Fin i → E₁ × E₁)
    (ww : Fin j → E₂ × E₂) :
    iteratedDMB₂ i j (splitD₁ f) (((x, a), (y, b)), vv, ww) =
      iteratedDMB₂ (i + 1) j f ((x, y), Fin.cons a fun s ↦ (vv s).1, fun t ↦ (ww t).1) +
        ∑ s, iteratedDMB₂ i j f ((x, y), update (fun s ↦ (vv s).1) s (vv s).2,
          fun t ↦ (ww t).1) := by
  have hφ := hf.contDiffMBOn_left j hj y hy fun t ↦ (ww t).1
  change iteratedDMB i (fun xa ↦ iteratedDMB j (fun yb ↦ splitD₁ f (xa, yb)) ((y, b), ww))
    ((x, a), vv) = _
  rw [iteratedDMB_congr_of_eventuallyEq i (Filter.eventually_of_mem
    ((hU.prod isOpen_univ).mem_nhds (show (x, a) ∈ U ×ˢ (univ : Set E₁) from ⟨hx, mem_univ a⟩))
    fun xa hxa ↦ iteratedDMB_splitD₁_right hU hV hf hj hxa.1 hy b ww)]
  exact hφ.iteratedDMB_dMB hU i hi x hx a (fun s ↦ (vv s).1) fun s ↦ (vv s).2

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] in
/-- The differentials of `splitD₂ f` in the second variable. -/
theorem iteratedDMB_splitD₂_right (hV : IsOpen V) (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V)
    {j : ℕ} (hj : j ≤ k) {xa : E₁ × E₁} (hxa : xa.1 ∈ U) {y : E₂} (hy : y ∈ V) (b : E₂)
    (ww : Fin j → E₂ × E₂) :
    iteratedDMB j (fun yb ↦ splitD₂ f (xa, yb)) ((y, b), ww) =
      iteratedDMB (j + 1) (fun y' ↦ f (xa.1, y')) (y, Fin.cons b fun t ↦ (ww t).1) +
        ∑ t, iteratedDMB j (fun y' ↦ f (xa.1, y')) (y, update (fun t ↦ (ww t).1) t (ww t).2) :=
  (hf.contDiffMBOn_right xa.1 hxa).iteratedDMB_dMB hV j hj y hy b (fun t ↦ (ww t).1)
    fun t ↦ (ww t).2

/-- The mixed differentials of `splitD₂ f`. -/
theorem iteratedDMB₂_splitD₂ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) {i j : ℕ} (hi : i ≤ k + 1) (hj : j ≤ k)
    {x a : E₁} {y b : E₂} (hx : x ∈ U) (hy : y ∈ V) (vv : Fin i → E₁ × E₁)
    (ww : Fin j → E₂ × E₂) :
    iteratedDMB₂ i j (splitD₂ f) (((x, a), (y, b)), vv, ww) =
      iteratedDMB₂ i (j + 1) f ((x, y), fun s ↦ (vv s).1, Fin.cons b fun t ↦ (ww t).1) +
        ∑ t, iteratedDMB₂ i j f ((x, y), fun s ↦ (vv s).1,
          update (fun t ↦ (ww t).1) t (ww t).2) := by
  set w : Fin j → E₂ := fun t ↦ (ww t).1
  let ψ₁ : E₁ → F := fun x' ↦ iteratedDMB (j + 1) (fun y' ↦ f (x', y')) (y, Fin.cons b w)
  let ψ₂ : Fin j → E₁ → F := fun t x' ↦
    iteratedDMB j (fun y' ↦ f (x', y')) (y, update w t (ww t).2)
  have h₁ : ContDiffMBOn (k + 1) ψ₁ U := hf.contDiffMBOn_left (j + 1) (by omega) y hy _
  have h₂ : ContDiffMBOn (k + 1) (fun x' ↦ ∑ t, ψ₂ t x') U :=
    ContDiffMBOn.sum _ hU fun t _ ↦ hf.contDiffMBOn_left j (by omega) y hy _
  change iteratedDMB i (fun xa ↦ iteratedDMB j (fun yb ↦ splitD₂ f (xa, yb)) ((y, b), ww))
    ((x, a), vv) = _
  rw [iteratedDMB_congr_of_eventuallyEq i (g₂ := (fun x' ↦ ψ₁ x' + ∑ t, ψ₂ t x') ∘
      (LinearMap.fst ℝ E₁ E₁)) (Filter.eventually_of_mem
    ((hU.prod isOpen_univ).mem_nhds (show (x, a) ∈ U ×ˢ (univ : Set E₁) from ⟨hx, mem_univ a⟩))
    fun xa hxa ↦ iteratedDMB_splitD₂_right hV hf hj hxa.1 hy b ww),
    iteratedDMB_comp_linearMap]
  simp only [LinearMap.fst_apply]
  rw [iteratedDMB_add hU h₁ h₂ hi hx,
    iteratedDMB_finset_sum _ hU (fun t _ ↦ hf.contDiffMBOn_left j (by omega) y hy _) hi hx]
  rfl

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Continuity of the mixed differentials along continuous maps. -/
theorem ContDiffMBOn₂.continuousOn_comp {k ℓ : ℕ} (hf : ContDiffMBOn₂ k ℓ f U V) {i j : ℕ}
    (hi : i ≤ k) (hj : j ≤ ℓ) {D : Type*} [TopologicalSpace D] {S : Set D}
    {σ : D → (E₁ × E₂) × (Fin i → E₁) × (Fin j → E₂)} (hσ : Continuous σ)
    (hS : MapsTo σ S (((U ×ˢ V) : Set (E₁ × E₂)) ×ˢ univ)) :
    ContinuousOn (fun p ↦ iteratedDMB₂ i j f (σ p)) S :=
  (hf.continuousOn i hi j hj).comp hσ.continuousOn hS

/-- `splitD₁ f` is `C^{k,k}` on `(U × E₁) × (V × E₂)` if `f` is `C^{k+1,k+1}` on `U × V`. -/
theorem contDiffMBOn₂_splitD₁ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) :
    ContDiffMBOn₂ k k (splitD₁ f) (U ×ˢ univ) (V ×ˢ univ) where
  contDiffMBOn_right xa hxa := by
    have h := (hf.contDiffMBOn_right_iteratedDMB₂ hU hV (i := 1) (by omega) hxa.1
      (fun _ ↦ xa.2)).comp_clm (ContinuousLinearMap.fst ℝ E₂ E₂) hV
    rw [show (ContinuousLinearMap.fst ℝ E₂ E₂) ⁻¹' V = V ×ˢ univ by ext; simp] at h
    exact h.of_le (by omega)
  contDiffMBOn_left j hj yb hyb ww :=
    ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ)
      (fun xa hxa ↦ (iteratedDMB_splitD₁_right hU hV hf (by omega) hxa.1 hyb.1 yb.2 ww).symm)
      (hf.contDiffMBOn_left j (by omega) yb.1 hyb.1 _).2.2
  continuousOn i hi j hj := by
    have h₁ := hf.continuousOn_comp (i := i + 1) (j := j) (by omega) (by omega)
      (S := ((U ×ˢ (univ : Set E₁)) ×ˢ (V ×ˢ (univ : Set E₂))) ×ˢ univ)
      (σ := fun p : ((E₁ × E₁) × (E₂ × E₂)) × (Fin i → E₁ × E₁) × (Fin j → E₂ × E₂) ↦
        ((p.1.1.1, p.1.2.1), Fin.cons p.1.1.2 fun s ↦ (p.2.1 s).1, fun t ↦ (p.2.2 t).1))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1.1, hp.1.2.1⟩, mem_univ _⟩
    have h₂ := continuousOn_finsetSum (Finset.univ : Finset (Fin i)) fun s _ ↦
      hf.continuousOn_comp (i := i) (j := j) (by omega) (by omega)
      (S := ((U ×ˢ (univ : Set E₁)) ×ˢ (V ×ˢ (univ : Set E₂))) ×ˢ univ)
      (σ := fun p : ((E₁ × E₁) × (E₂ × E₂)) × (Fin i → E₁ × E₁) × (Fin j → E₂ × E₂) ↦
        ((p.1.1.1, p.1.2.1), update (fun s ↦ (p.2.1 s).1) s (p.2.1 s).2, fun t ↦ (p.2.2 t).1))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1.1, hp.1.2.1⟩, mem_univ _⟩
    refine (h₁.add h₂).congr fun p hp ↦ ?_
    exact iteratedDMB₂_splitD₁ hU hV hf hi (by omega) hp.1.1.1 hp.1.2.1 p.2.1 p.2.2

/-- `splitD₂ f` is `C^{k,k}` on `(U × E₁) × (V × E₂)` if `f` is `C^{k+1,k+1}` on `U × V`. -/
theorem contDiffMBOn₂_splitD₂ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) :
    ContDiffMBOn₂ k k (splitD₂ f) (U ×ˢ univ) (V ×ˢ univ) where
  contDiffMBOn_right xa hxa :=
    ContDiffMBOn.congr_of_isOpen (hV.prod isOpen_univ) (fun _ _ ↦ rfl)
      (hf.contDiffMBOn_right xa.1 hxa.1).2.2
  contDiffMBOn_left j hj yb hyb ww := by
    have h₁ : ContDiffMBOn (k + 1) (fun x' ↦
        iteratedDMB (j + 1) (fun y' ↦ f (x', y')) (yb.1, Fin.cons yb.2 fun t ↦ (ww t).1) +
          ∑ t, iteratedDMB j (fun y' ↦ f (x', y'))
            (yb.1, update (fun t ↦ (ww t).1) t (ww t).2)) U :=
      (hf.contDiffMBOn_left (j + 1) (by omega) yb.1 hyb.1 _).add hU
        (ContDiffMBOn.sum _ hU fun t _ ↦ hf.contDiffMBOn_left j (by omega) yb.1 hyb.1 _)
    have h₂ := h₁.comp_clm (ContinuousLinearMap.fst ℝ E₁ E₁) hU
    rw [show (ContinuousLinearMap.fst ℝ E₁ E₁) ⁻¹' U = U ×ˢ univ by ext; simp] at h₂
    exact ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ)
      (fun xa hxa ↦ (iteratedDMB_splitD₂_right hV hf hj hxa.1 hyb.1 yb.2 ww).symm)
      (h₂.of_le (by omega))
  continuousOn i hi j hj := by
    have h₁ := hf.continuousOn_comp (i := i) (j := j + 1) (by omega) (by omega)
      (S := ((U ×ˢ (univ : Set E₁)) ×ˢ (V ×ˢ (univ : Set E₂))) ×ˢ univ)
      (σ := fun p : ((E₁ × E₁) × (E₂ × E₂)) × (Fin i → E₁ × E₁) × (Fin j → E₂ × E₂) ↦
        ((p.1.1.1, p.1.2.1), (fun s ↦ (p.2.1 s).1), Fin.cons p.1.2.2 fun t ↦ (p.2.2 t).1))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1.1, hp.1.2.1⟩, mem_univ _⟩
    have h₂ := continuousOn_finsetSum (Finset.univ : Finset (Fin j)) fun t _ ↦
      hf.continuousOn_comp (i := i) (j := j) (by omega) (by omega)
      (S := ((U ×ˢ (univ : Set E₁)) ×ˢ (V ×ˢ (univ : Set E₂))) ×ˢ univ)
      (σ := fun p : ((E₁ × E₁) × (E₂ × E₂)) × (Fin i → E₁ × E₁) × (Fin j → E₂ × E₂) ↦
        ((p.1.1.1, p.1.2.1), (fun s ↦ (p.2.1 s).1), update (fun t ↦ (p.2.2 t).1) t (p.2.2 t).2))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1.1, hp.1.2.1⟩, mem_univ _⟩
    refine (h₁.add h₂).congr fun p hp ↦ ?_
    exact iteratedDMB₂_splitD₂ hU hV hf (by omega) hj hp.1.1.1 hp.1.2.1 p.2.1 p.2.2

/-- `splitD f` is `C^{k,k}` on `(U × E₁) × (V × E₂)` if `f` is `C^{k+1,k+1}` on `U × V`. -/
theorem contDiffMBOn₂_splitD (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) :
    ContDiffMBOn₂ k k (splitD f) (U ×ˢ univ) (V ×ˢ univ) :=
  (contDiffMBOn₂_splitD₁ hU hV hf).add (hU.prod isOpen_univ) (hV.prod isOpen_univ)
    (contDiffMBOn₂_splitD₂ hU hV hf)

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **The rule on partial differentials** for `C^{k+1,k+1}` maps (the case `m = 1` of
[GN26, (1.108)]): `f` is `C^1` on `U × V`, with
`df((x, y), (a, b)) = d^(1,0) f(x, y, a) + d^(0,1) f(x, y, b)`. -/
theorem ContDiffMBOn₂.contDiffMBOn_one (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) (k + 1) f U V) :
    ContDiffMBOn 1 f (U ×ˢ V) ∧ ∀ p ∈ U ×ˢ V, ∀ a b,
      dMB f (p, (a, b)) = splitD f ((p.1, a), (p.2, b)) :=
  contDiffMBOn_one_of_partials (hU.prod hV)
    (d₁ := fun p a ↦ splitD₁ f ((p.1, a), (p.2, 0)))
    (d₂ := fun p b ↦ splitD₂ f ((p.1, 0), (p.2, b)))
    (fun p hp a ↦ hasDirDerivAt_slice.2
      (hf.hasDirDerivAt_left (i := 0) (j := 0) (by omega) (by omega) hp.1 hp.2 (fun _ ↦ a)
        Fin.elim0))
    (fun p hp b ↦ hasDirDerivAt_slice₂.2 ((hf.contDiffMBOn_right p.1 hp.1).hasDirDerivAt hp.2 b))
    (hf.continuousOn_comp (i := 1) (j := 0) (by omega) (by omega) (by fun_prop)
      fun q hq ↦ ⟨hq.1, mem_univ _⟩)
    (hf.continuousOn_comp (i := 0) (j := 1) (by omega) (by omega) (by fun_prop)
      fun q hq ↦ ⟨hq.1, mem_univ _⟩)

end Split

/-! ### Proposition 1.7.33(b): `C^{k,k}` maps are `C^k` -/

section KK

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- The linear map `((x, y), (a, b)) ↦ ((x, a), (y, b))`. -/
def regroupCLM (E₁ : Type u) [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    (E₂ : Type u') [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂] :
    (E₁ × E₂) × (E₁ × E₂) →L[ℝ] (E₁ × E₁) × (E₂ × E₂) :=
  (ContinuousLinearEquiv.prodProdProdComm ℝ E₁ E₂ E₁ E₂ :
    (E₁ × E₂) × (E₁ × E₂) →L[ℝ] (E₁ × E₁) × (E₂ × E₂))

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- `regroupCLM ((x, y), (a, b)) = ((x, a), (y, b))`. -/
@[simp]
theorem regroupCLM_apply (p : (E₁ × E₂) × (E₁ × E₂)) :
    regroupCLM E₁ E₂ p = ((p.1.1, p.2.1), (p.1.2, p.2.2)) :=
  rfl

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The preimage of `(U × E₁) × (V × E₂)` under the regrouping is `(U × V) × (E₁ × E₂)`. -/
theorem regroupCLM_preimage (U : Set E₁) (V : Set E₂) :
    regroupCLM E₁ E₂ ⁻¹' ((U ×ˢ univ) ×ˢ (V ×ˢ univ)) = (U ×ˢ V) ×ˢ univ := by
  ext ⟨⟨x, y⟩, a, b⟩
  simp

/-- **[GN26, Proposition 1.7.33(b)]**: every `C^{k,k}` map on `U × V` is `C^k` there.

Glöckner–Neeb prove the explicit formula (1.108) for `d^(k) f` by induction. Here the induction
is on the recursive definition of `C^k`: by the rule on partial differentials,
`df((x, y), (a, b)) = d^(1,0) f(x, y, a) + d^(0,1) f(x, y, b)`, and the right hand side, as a
function of `((x, a), (y, b))`, is `C^{k,k}` (`contDiffMBOn₂_splitD`). -/
theorem ContDiffMBOn₂.contDiffMBOn_prod {k : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffMBOn₂ k k f U V) :
    ContDiffMBOn k f (U ×ˢ V) := by
  induction k generalizing E₁ E₂ with
  | zero =>
    exact (hf.continuousOn_comp (i := 0) (j := 0) le_rfl le_rfl
      (σ := fun p : E₁ × E₂ ↦ (p, Fin.elim0, Fin.elim0)) (by fun_prop)
      fun p hp ↦ ⟨hp, mem_univ _⟩)
  | succ k ih =>
    obtain ⟨h1, heq⟩ := hf.contDiffMBOn_one hU hV
    have hG := (ih (hU.prod isOpen_univ) (hV.prod isOpen_univ)
      (contDiffMBOn₂_splitD hU hV hf)).comp_clm (regroupCLM E₁ E₂)
      ((hU.prod isOpen_univ).prod (hV.prod isOpen_univ))
    rw [regroupCLM_preimage] at hG
    refine ⟨h1.1, h1.2.1, ContDiffMBOn.congr_of_isOpen ((hU.prod hV).prod isOpen_univ)
      (fun p hp ↦ (heq p.1 hp.1 p.2.1 p.2.2).symm) hG⟩

end KK

section Congr

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {f g : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] [ContinuousSMul ℝ F] in
/-- Mixed differentials only depend on the values on the open set `U × V`. -/
theorem iteratedDMB₂_congr (hU : IsOpen U) (hV : IsOpen V) (h : EqOn f g (U ×ˢ V)) (i j : ℕ)
    {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V) (v : Fin i → E₁) (w : Fin j → E₂) :
    iteratedDMB₂ i j f ((x, y), v, w) = iteratedDMB₂ i j g ((x, y), v, w) := by
  change iteratedDMB i (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w)) (x, v) =
    iteratedDMB i (fun x' ↦ iteratedDMB j (fun y' ↦ g (x', y')) (y, w)) (x, v)
  refine iteratedDMB_congr_of_eventuallyEq i (Filter.eventually_of_mem (hU.mem_nhds hx)
    fun x' hx' ↦ ?_) v
  exact iteratedDMB_congr_of_eventuallyEq j (Filter.eventually_of_mem (hV.mem_nhds hy)
    fun y' hy' ↦ h ⟨hx', hy'⟩) w

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Being `C^{k,ℓ}` only depends on the values on the open set `U × V`. -/
theorem ContDiffMBOn₂.congr (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffMBOn₂ k ℓ f U V)
    (h : EqOn f g (U ×ˢ V)) : ContDiffMBOn₂ k ℓ g U V where
  contDiffMBOn_right x hx := ContDiffMBOn.congr_of_isOpen hV (fun _ hy ↦ h ⟨hx, hy⟩)
    (hf.contDiffMBOn_right x hx)
  contDiffMBOn_left j hj y hy w := ContDiffMBOn.congr_of_isOpen hU
    (fun _ hx ↦ iteratedDMB₂_congr hU hV h 0 j hx hy Fin.elim0 w) (hf.contDiffMBOn_left j hj y hy w)
  continuousOn i hi j hj := (hf.continuousOn i hi j hj).congr fun p hp ↦
    (iteratedDMB₂_congr hU hV h i j hp.1.1 hp.1.2 p.2.1 p.2.2).symm

end Congr

section Inclusion

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace ContDiffMBMap₂

variable {k : ℕ} {U : Opens E₁} {V : Opens E₂}

/-- The inclusion `μ : C^{k,k}(U × V, F) → C^k(U × V, F)`
([GN26, Proposition 1.7.33(b)]). -/
def toContDiffMBMap (f : ContDiffMBMap₂ F k k U V) : ContDiffMBMap F k (Opens.prod U V) :=
  ContDiffMBMap.mk f (f.contDiffMBOn₂.contDiffMBOn_prod U.isOpen V.isOpen)
    fun _ hp ↦ f.apply_of_notMem hp

/-- `μ` does not change the underlying map. -/
@[simp]
theorem coe_toContDiffMBMap (f : ContDiffMBMap₂ F k k U V) : ⇑(toContDiffMBMap f) = f :=
  rfl

/-- The `0`-th differential of `μ f` is that of `f`, continuously. -/
theorem continuous_iteratedD_zero_toContDiffMBMap :
    Continuous fun f : ContDiffMBMap₂ F k k U V ↦
      ContDiffMBMap.iteratedD 0 (Nat.zero_le k) (toContDiffMBMap f) := by
  let A : C((Opens.prod U V) × (Fin 0 → E₁ × E₂), (U × V) × (Fin 0 → E₁) × (Fin 0 → E₂)) :=
    ⟨fun p ↦ ((⟨p.1.1.1, p.1.2.1⟩, ⟨p.1.1.2, p.1.2.2⟩), Fin.elim0, Fin.elim0),
      Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk (by fun_prop) _)
        (Continuous.subtype_mk (by fun_prop) _)) continuous_const⟩
  have e : ∀ f : ContDiffMBMap₂ F k k U V, ContDiffMBMap.iteratedD 0 (Nat.zero_le k)
      (toContDiffMBMap f) = (iteratedD₂ 0 0 (Nat.zero_le k) (Nat.zero_le k) f).comp A :=
    fun f ↦ ContinuousMap.ext fun _ ↦ rfl
  simp only [e]
  exact (ContinuousMap.continuous_precomp A).comp (continuous_iteratedD₂ _ _ _ _)

/-- The split differential `((x, a), (y, b)) ↦ d^(1,0) f(x, y, a) + d^(0,1) f(x, y, b)` of
`f ∈ C^{k+1,k+1}(U × V, F)`, as an element of `C^{k,k}((U × E₁) × (V × E₂), F)`. -/
def splitDMap (f : ContDiffMBMap₂ F (k + 1) (k + 1) U V) :
    ContDiffMBMap₂ F k k (Opens.prodUniv U) (Opens.prodUniv V) :=
  mk (((Opens.prodUniv U : Set (E₁ × E₁)) ×ˢ (Opens.prodUniv V : Set (E₂ × E₂))).indicator
      (splitD f))
    (ContDiffMBOn₂.congr (Opens.prodUniv U).isOpen (Opens.prodUniv V).isOpen
      (by rw [Opens.coe_prodUniv, Opens.coe_prodUniv]
          exact contDiffMBOn₂_splitD U.isOpen V.isOpen f.contDiffMBOn₂)
      fun _ hp ↦ (indicator_of_mem hp _).symm)
    fun _ hp ↦ indicator_of_notMem hp _

/-- The mixed differentials of the split differential, in terms of those of `f`. -/
theorem iteratedDMB₂_splitDMap (f : ContDiffMBMap₂ F (k + 1) (k + 1) U V) {i j : ℕ} (hi : i ≤ k)
    (hj : j ≤ k) {x a : E₁} {y b : E₂} (hx : x ∈ U) (hy : y ∈ V) (vv : Fin i → E₁ × E₁)
    (ww : Fin j → E₂ × E₂) :
    iteratedDMB₂ i j (splitDMap f) (((x, a), (y, b)), vv, ww) =
      (iteratedDMB₂ (i + 1) j f ((x, y), Fin.cons a fun s ↦ (vv s).1, fun t ↦ (ww t).1) +
        ∑ s, iteratedDMB₂ i j f ((x, y), update (fun s ↦ (vv s).1) s (vv s).2,
          fun t ↦ (ww t).1)) +
      (iteratedDMB₂ i (j + 1) f ((x, y), fun s ↦ (vv s).1, Fin.cons b fun t ↦ (ww t).1) +
        ∑ t, iteratedDMB₂ i j f ((x, y), fun s ↦ (vv s).1,
          update (fun t ↦ (ww t).1) t (ww t).2)) := by
  have hU' := U.isOpen.prod (isOpen_univ (X := E₁))
  have hV' := V.isOpen.prod (isOpen_univ (X := E₂))
  rw [iteratedDMB₂_congr (f := ⇑(splitDMap f)) (g := splitD ⇑f) (Opens.prodUniv U).isOpen
      (Opens.prodUniv V).isOpen (fun _ hp ↦ indicator_of_mem hp (splitD ⇑f)) i j
      (show (x, a) ∈ Opens.prodUniv U from hx) (show (y, b) ∈ Opens.prodUniv V from hy) vv ww]
  rw [show splitD f = fun p ↦ splitD₁ f p + splitD₂ f p from rfl,
    (contDiffMBOn₂_splitD₁ U.isOpen V.isOpen f.contDiffMBOn₂).iteratedDMB₂_add hU' hV'
      (contDiffMBOn₂_splitD₂ U.isOpen V.isOpen f.contDiffMBOn₂) hi hj
      (show (x, a) ∈ (U : Set E₁) ×ˢ univ from ⟨hx, mem_univ _⟩)
      (show (y, b) ∈ (V : Set E₂) ×ˢ univ from ⟨hy, mem_univ _⟩) vv ww,
    iteratedDMB₂_splitD₁ U.isOpen V.isOpen f.contDiffMBOn₂ hi (by omega) hx hy vv ww,
    iteratedDMB₂_splitD₂ U.isOpen V.isOpen f.contDiffMBOn₂ (by omega) hj hx hy vv ww]

/-- `f ↦ splitDMap f` is continuous. -/
theorem continuous_splitDMap :
    Continuous (splitDMap (F := F) (k := k) (U := U) (V := V)) := by
  refine continuous_iff.2 fun i j hi hj ↦ ?_
  let X := (Opens.prodUniv U × Opens.prodUniv V) × (Fin i → E₁ × E₁) × (Fin j → E₂ × E₂)
  let A : ∀ {i' j' : ℕ} (σ : X → (Fin i' → E₁) × (Fin j' → E₂)), Continuous σ →
      C(X, (U × V) × (Fin i' → E₁) × (Fin j' → E₂)) := fun σ hσ ↦
    ⟨fun p ↦ ((⟨p.1.1.1.1, p.1.1.2⟩, ⟨p.1.2.1.1, p.1.2.2⟩), σ p),
      Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk (by fun_prop) _)
        (Continuous.subtype_mk (by fun_prop) _)) hσ⟩
  have hA : ∀ (i' j' : ℕ) (hi' : i' ≤ k + 1) (hj' : j' ≤ k + 1)
      (σ : X → (Fin i' → E₁) × (Fin j' → E₂)) (hσ : Continuous σ),
      Continuous fun f : ContDiffMBMap₂ F (k + 1) (k + 1) U V ↦
        (iteratedD₂ i' j' hi' hj' f).comp (A σ hσ) := fun i' j' hi' hj' σ hσ ↦
    (ContinuousMap.continuous_precomp (A σ hσ)).comp (continuous_iteratedD₂ i' j' hi' hj')
  have h := ((hA (i + 1) j (by omega) (by omega)
      (fun p ↦ (Fin.cons p.1.1.1.2 fun s ↦ (p.2.1 s).1, fun t ↦ (p.2.2 t).1)) (by fun_prop)).add
    (continuous_finsetSum Finset.univ fun s _ ↦ hA i j (by omega) (by omega)
      (fun p ↦ (update (fun s ↦ (p.2.1 s).1) s (p.2.1 s).2, fun t ↦ (p.2.2 t).1))
      (by fun_prop))).add
    ((hA i (j + 1) (by omega) (by omega)
      (fun p ↦ (fun s ↦ (p.2.1 s).1, Fin.cons p.1.2.1.2 fun t ↦ (p.2.2 t).1)) (by fun_prop)).add
    (continuous_finsetSum Finset.univ fun t _ ↦ hA i j (by omega) (by omega)
      (fun p ↦ (fun s ↦ (p.2.1 s).1, update (fun t ↦ (p.2.2 t).1) t (p.2.2 t).2))
      (by fun_prop)))
  refine h.congr fun f ↦ ContinuousMap.ext fun p ↦ ?_
  simp only [Pi.add_apply, ContinuousMap.add_apply, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, iteratedD₂_apply, A]
  exact (iteratedDMB₂_splitDMap f hi hj (x := (p.1.1 : E₁ × E₁).1) (a := (p.1.1 : E₁ × E₁).2)
    (y := (p.1.2 : E₂ × E₂).1) (b := (p.1.2 : E₂ × E₂).2) p.1.1.2 p.1.2.2 p.2.1 p.2.2).symm

/-- **[GN26, Proposition 1.7.33(b)]**: the inclusion `μ : C^{k,k}(U × V, F) → C^k(U × V, F)`
is continuous.

Glöckner–Neeb deduce this from the formula (1.108). Here it follows by induction on `k` from the
continuity criterion `ContDiffMBMap.continuous_of_continuous_dMap`: the differential of `μ f` is,
up to the regrouping `((x, y), (a, b)) ↦ ((x, a), (y, b))`, the split differential of `f`, which
depends continuously on `f` (`ContDiffMBMap₂.continuous_splitDMap`). -/
theorem continuous_toContDiffMBMap :
    Continuous (toContDiffMBMap (F := F) (k := k) (U := U) (V := V)) := by
  induction k generalizing E₁ E₂ with
  | zero =>
    refine ContDiffMBMap.continuous_iff.2 fun j hj ↦ ?_
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact continuous_iteratedD_zero_toContDiffMBMap
  | succ k ih =>
    refine ContDiffMBMap.continuous_of_continuous_dMap
      continuous_iteratedD_zero_toContDiffMBMap ?_
    refine ContDiffMBMap.continuous_iff.2 fun j hj ↦ ?_
    let R : C((Opens.prodUniv (Opens.prod U V)) × (Fin j → (E₁ × E₂) × (E₁ × E₂)),
        (Opens.prod (Opens.prodUniv U) (Opens.prodUniv V)) × (Fin j → (E₁ × E₁) × (E₂ × E₂))) :=
      ⟨fun p ↦ (⟨regroupCLM E₁ E₂ p.1, ⟨p.1.2.1, p.1.2.2⟩⟩, fun t ↦ regroupCLM E₁ E₂ (p.2 t)),
        Continuous.prodMk (Continuous.subtype_mk (by fun_prop) _) (by fun_prop)⟩
    have e : ∀ f : ContDiffMBMap₂ F (k + 1) (k + 1) U V,
        ContDiffMBMap.iteratedD j hj (ContDiffMBMap.dMap (toContDiffMBMap f)) =
          (ContDiffMBMap.iteratedD j hj (toContDiffMBMap (splitDMap f))).comp R := by
      intro f
      ext p
      simp only [ContDiffMBMap.iteratedD_apply, ContinuousMap.comp_apply]
      have hp : ((p.1 : (E₁ × E₂) × (E₁ × E₂)).1) ∈ (U : Set E₁) ×ˢ (V : Set E₂) := p.1.2
      rw [iteratedDMB_congr_of_eventuallyEq j
        (ContDiffMBMap.dMap_eventuallyEq (toContDiffMBMap f) p.1.2)]
      have hev : dMB ⇑(toContDiffMBMap f) =ᶠ[𝓝 (p.1 : (E₁ × E₂) × (E₁ × E₂))]
          splitD ⇑f ∘ (regroupCLM E₁ E₂ : (E₁ × E₂) × (E₁ × E₂) →ₗ[ℝ] (E₁ × E₁) × (E₂ × E₂)) :=
        Filter.eventually_of_mem (((U.isOpen.prod V.isOpen).prod isOpen_univ).mem_nhds
          (show (p.1 : (E₁ × E₂) × (E₁ × E₂)) ∈ ((U : Set E₁) ×ˢ (V : Set E₂)) ×ˢ univ from
            ⟨hp, mem_univ _⟩)) fun q hq ↦
          (f.contDiffMBOn₂.contDiffMBOn_one U.isOpen V.isOpen).2 q.1 hq.1 q.2.1 q.2.2
      rw [iteratedDMB_congr_of_eventuallyEq j hev, iteratedDMB_comp_linearMap]
      have hev' : ⇑(toContDiffMBMap (splitDMap f)) =ᶠ[𝓝 (regroupCLM E₁ E₂ p.1)] splitD ⇑f :=
        Filter.eventually_of_mem ((Opens.prod (Opens.prodUniv U) (Opens.prodUniv V)).isOpen.mem_nhds
          (show regroupCLM E₁ E₂ p.1 ∈ Opens.prod (Opens.prodUniv U) (Opens.prodUniv V) from
            ⟨hp.1, hp.2⟩)) fun q hq ↦ indicator_of_mem hq (splitD ⇑f)
      exact (iteratedDMB_congr_of_eventuallyEq j hev' _).symm
    simp only [e]
    exact (ContinuousMap.continuous_precomp R).comp
      ((ContDiffMBMap.continuous_iteratedD j hj).comp (ih.comp continuous_splitDMap))

/-- **[GN26, Proposition 1.7.33(b)]**: `μ : C^{k,k}(U × V, F) → C^k(U × V, F)` as a
continuous linear map. -/
def toContDiffMBMapCLM : ContDiffMBMap₂ F k k U V →L[ℝ] ContDiffMBMap F k (Opens.prod U V) where
  toFun := toContDiffMBMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_toContDiffMBMap

end ContDiffMBMap₂

end Inclusion

/-! ### `C^k` maps into `C^∞(V, F)` -/

section SmoothTarget

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {V : Opens E₂}

namespace SmoothMBMap

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [AddCommGroup E] [Module ℝ E] in
/-- A map into `C^∞(V, F)` is continuous on `W` if and only if its compositions with the
inclusions into the `C^ℓ(V, F)` are. -/
theorem continuousOn_iff {g : E → SmoothMBMap F V} {W : Set E} :
    ContinuousOn g W ↔ ∀ ℓ, ContinuousOn (fun x ↦ toCk ℓ (g x)) W := by
  refine ⟨fun h ℓ ↦ (continuous_toCk ℓ).comp_continuousOn h, fun h ↦ ?_⟩
  rw [isEmbedding_toPi.isInducing.continuousOn_iff]
  exact continuousOn_pi.2 fun j ↦
    (ContDiffMBMap.continuous_iteratedD j le_rfl).comp_continuousOn (h j)

/-- **`C^k` maps into `C^∞(V, F)`**: a map `g : E → C^∞(V, F)` is `C^k` on the open set `W` if and
only if its compositions with the inclusions `C^∞(V, F) → C^ℓ(V, F)` are `C^k`, for all `ℓ`. -/
theorem contDiffMBOn_iff {k : ℕ} {g : E → SmoothMBMap F V} {W : Set E} (hW : IsOpen W) :
    ContDiffMBOn k g W ↔ ∀ ℓ, ContDiffMBOn k (fun x ↦ toCk ℓ (g x)) W := by
  refine ⟨fun hg ℓ ↦ ContDiffMBOn.comp hW isOpen_univ ((toCkCLM ℓ).contDiffMBOn k univ) hg
    (mapsTo_univ _ _), fun h ↦ ?_⟩
  induction k generalizing E with
  | zero => exact continuousOn_iff.2 h
  | succ k ih =>
    -- the derivatives of the `toCk ℓ ∘ g` have the same underlying maps
    have hcompat : ∀ p : E × E, p.1 ∈ W → ∀ ℓ,
        ⇑(dMB (fun x ↦ toCk ℓ (g x)) p) = ⇑(dMB (fun x ↦ toCk 0 (g x)) p) := by
      intro p hp ℓ
      have hd := ((h ℓ).hasDirDerivAt hp p.2).clm_comp_real
        (ContDiffMBMap.ofLECLM (F := F) (U := V) (Nat.zero_le ℓ))
      exact (congrArg DFunLike.coe hd.dMB_eq).symm
    classical
    let D : E × E → SmoothMBMap F V := fun p ↦
      if hp : p.1 ∈ W then ofForall (fun ℓ ↦ dMB (fun x ↦ toCk ℓ (g x)) p) (hcompat p hp) else 0
    have hD : ∀ p : E × E, p.1 ∈ W → ∀ ℓ, toCk ℓ (D p) = dMB (fun x ↦ toCk ℓ (g x)) p := by
      intro p hp ℓ
      simp only [D, hp, dite_true, toCk_ofForall]
    have hder : ∀ x ∈ W, ∀ v, HasDirDerivAt g x v (D (x, v)) := by
      intro x hx v
      rw [HasDirDerivAt, isEmbedding_toPi.tendsto_nhds_iff, tendsto_pi_nhds]
      intro j
      have h1 := ((h j).hasDirDerivAt hx v).clm_comp_real
        (ContDiffMBMap.iteratedDCLM (F := F) (U := V) j le_rfl)
      rw [toPi_apply, hD (x, v) hx j]
      refine h1.congr fun t ↦ ?_
      simp only [Function.comp_apply, toPi_apply]
      have e1 : toCk j (t⁻¹ • (g (x + t • v) - g x)) =
          t⁻¹ • (toCk j (g (x + t • v)) - toCk j (g x)) := by
        rw [show toCk j = ⇑(toCkL (F := F) (U := V) j) from rfl, map_smul, map_sub]
      rw [e1]
      change _ = ContDiffMBMap.iteratedDCLM j le_rfl (t⁻¹ • _)
      rw [map_smul, map_sub]
    have hdeq : ∀ p ∈ W ×ˢ (univ : Set E), dMB g p = D p := fun p hp ↦
      (hder p.1 hp.1 p.2).dMB_eq
    refine ⟨continuousOn_iff.2 fun ℓ ↦ (h ℓ).continuousOn, fun x hx v ↦ ?_, ?_⟩
    · rw [hdeq (x, v) ⟨hx, mem_univ v⟩]
      exact hder x hx v
    · refine ih (hW.prod isOpen_univ) fun ℓ ↦ ?_
      refine ContDiffMBOn.congr_of_isOpen (hW.prod isOpen_univ) (fun p hp ↦ ?_) (h ℓ).2.2
      rw [hdeq p hp, hD p hp.1 ℓ]

/-- A map into `C^∞(V, F)` is smooth if and only if its compositions with the inclusions into
the `C^ℓ(V, F)` are smooth. -/
theorem smoothMBOn_iff {g : E → SmoothMBMap F V} {W : Set E} (hW : IsOpen W) :
    SmoothMBOn g W ↔ ∀ ℓ, SmoothMBOn (fun x ↦ toCk ℓ (g x)) W :=
  ⟨fun hg ℓ k ↦ (contDiffMBOn_iff hW).1 (hg k) ℓ, fun h k ↦ (contDiffMBOn_iff hW).2 fun ℓ ↦ h ℓ k⟩

end SmoothMBMap

end SmoothTarget

/-! ### Corollary 1.7.34: `C^∞ = C^{∞,∞}` -/

section SmoothTwo

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **[GN26, Corollary 1.7.34]**: a map on `U × V` is smooth if and only if it is
`C^{k,ℓ}` for all `k, ℓ ∈ ℕ` (that is, `C^{∞,∞}`). -/
theorem smoothMBOn_prod_iff {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂} (hU : IsOpen U)
    (hV : IsOpen V) : SmoothMBOn f (U ×ˢ V) ↔ ∀ k ℓ, ContDiffMBOn₂ k ℓ f U V :=
  ⟨fun hf k ℓ ↦ (hf (k + ℓ)).contDiffMBOn₂ hU hV, fun hf k ↦ (hf k k).contDiffMBOn_prod hU hV⟩

variable (F) in
/-- The `C^{∞,∞}` maps on `U × V`, extended by `0`, as a submodule of `E₁ × E₂ → F`. -/
def smoothMBSubmodule₂ (U : Opens E₁) (V : Opens E₂) : Submodule ℝ (E₁ × E₂ → F) :=
  ⨅ (k : ℕ) (ℓ : ℕ), contDiffMBSubmodule₂ F k ℓ U V

variable (F) in
/-- **The space `C^{∞,∞}(U × V, F)`** with the compact-open `C^{∞,∞}` topology, the initial
topology with respect to all the mixed differentials `d^(i,j)`, `i, j ∈ ℕ`
([GN26, Definition 1.7.17] with `k = ℓ = ∞`). -/
def SmoothMBMap₂ (U : Opens E₁) (V : Opens E₂) : Type (max u u' v) := smoothMBSubmodule₂ F U V

namespace SmoothMBMap₂

variable {U : Opens E₁} {V : Opens E₂}

/-- The vector space operations of `C^{∞,∞}(U × V, F)` are pointwise. -/
instance : AddCommGroup (SmoothMBMap₂ F U V) :=
  inferInstanceAs (AddCommGroup (smoothMBSubmodule₂ F U V))

/-- The vector space operations of `C^{∞,∞}(U × V, F)` are pointwise. -/
instance : Module ℝ (SmoothMBMap₂ F U V) :=
  inferInstanceAs (Module ℝ (smoothMBSubmodule₂ F U V))

/-- An element of `C^{∞,∞}(U × V, F)` is a map `E₁ × E₂ → F`. -/
instance : FunLike (SmoothMBMap₂ F U V) (E₁ × E₂) F where
  coe γ := Subtype.val (γ : smoothMBSubmodule₂ F U V)
  coe_injective := Subtype.val_injective

/-- Membership in `C^{∞,∞}(U × V, F)`. -/
theorem mem_iff {f : E₁ × E₂ → F} : f ∈ smoothMBSubmodule₂ F U V ↔
    (∀ k ℓ, ContDiffMBOn₂ k ℓ f U V) ∧ ∀ p ∉ (U : Set E₁) ×ˢ (V : Set E₂), f p = 0 := by
  simp only [smoothMBSubmodule₂, Submodule.mem_iInf]
  exact ⟨fun h ↦ ⟨fun k ℓ ↦ (h k ℓ).1, (h 0 0).2⟩, fun h k ℓ ↦ ⟨h.1 k ℓ, h.2⟩⟩

/-- An element of `C^{∞,∞}(U × V, F)` is `C^{k,ℓ}` for all `k, ℓ`. -/
theorem contDiffMBOn₂ (γ : SmoothMBMap₂ F U V) (k ℓ : ℕ) : ContDiffMBOn₂ k ℓ γ U V :=
  (mem_iff.1 (γ : smoothMBSubmodule₂ F U V).2).1 k ℓ

/-- An element of `C^{∞,∞}(U × V, F)` vanishes outside `U × V`. -/
theorem apply_of_notMem (γ : SmoothMBMap₂ F U V) {p : E₁ × E₂}
    (hp : p ∉ (U : Set E₁) ×ˢ (V : Set E₂)) : γ p = 0 :=
  (mem_iff.1 (γ : smoothMBSubmodule₂ F U V).2).2 p hp

/-- The element of `C^{∞,∞}(U × V, F)` given by a `C^{∞,∞}` map vanishing outside `U × V`. -/
def mk (f : E₁ × E₂ → F) (hf : ∀ k ℓ, ContDiffMBOn₂ k ℓ f U V)
    (h0 : ∀ p ∉ (U : Set E₁) ×ˢ (V : Set E₂), f p = 0) : SmoothMBMap₂ F U V :=
  ⟨f, mem_iff.2 ⟨hf, h0⟩⟩

/-- Elements of `C^{∞,∞}(U × V, F)` are equal if they agree as maps. -/
@[ext]
theorem ext {γ η : SmoothMBMap₂ F U V} (h : ∀ p, γ p = η p) : γ = η :=
  DFunLike.ext _ _ h

/-- The inclusion `C^{∞,∞}(U × V, F) → C^{k,ℓ}(U × V, F)`. -/
def toCk₂ (k ℓ : ℕ) (γ : SmoothMBMap₂ F U V) : ContDiffMBMap₂ F k ℓ U V :=
  ContDiffMBMap₂.mk γ (γ.contDiffMBOn₂ k ℓ) fun _ hp ↦ γ.apply_of_notMem hp

/-- The inclusion `C^{∞,∞}(U × V, F) → C^{k,ℓ}(U × V, F)` as a linear map. -/
def toCkL₂ (k ℓ : ℕ) : SmoothMBMap₂ F U V →ₗ[ℝ] ContDiffMBMap₂ F k ℓ U V where
  toFun := toCk₂ k ℓ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `γ ↦ (d^(i,j)γ)_{i,j ∈ ℕ}`, linear. -/
def toPi : SmoothMBMap₂ F U V →ₗ[ℝ]
    ∀ i j : ℕ, C((U × V) × (Fin i → E₁) × (Fin j → E₂), F) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (ContDiffMBMap₂.iteratedDL₂ i j le_rfl le_rfl).comp (toCkL₂ i j)

/-- The mixed differentials separate the points of `C^{∞,∞}(U × V, F)`. -/
theorem toPi_injective : Function.Injective (toPi (F := F) (U := U) (V := V)) := by
  intro γ η h
  ext p
  by_cases hp : p ∈ (U : Set E₁) ×ˢ (V : Set E₂)
  · have := congrArg (fun φ ↦ φ 0 0 ((⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), Fin.elim0, Fin.elim0)) h
    exact this
  · rw [γ.apply_of_notMem hp, η.apply_of_notMem hp]

/-- **The compact-open `C^{∞,∞}` topology**. -/
instance : TopologicalSpace (SmoothMBMap₂ F U V) :=
  .induced toPi inferInstance

/-- `γ ↦ (d^(i,j)γ)_{i,j}` is a linear topological embedding. -/
theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (F := F) (U := U) (V := V)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

/-- `C^{∞,∞}(U × V, F)` is a topological additive group. -/
instance : IsTopologicalAddGroup (SmoothMBMap₂ F U V) :=
  isTopologicalAddGroup_induced toPi

/-- Scalar multiplication on `C^{∞,∞}(U × V, F)` is continuous. -/
instance : ContinuousSMul ℝ (SmoothMBMap₂ F U V) :=
  continuousSMul_induced toPi

/-- `C^{∞,∞}(U × V, F)` is locally convex. -/
instance : LocallyConvexSpace ℝ (SmoothMBMap₂ F U V) :=
  LocallyConvexSpace.induced toPi

/-- `C^{∞,∞}(U × V, F)` is Hausdorff. -/
instance : T2Space (SmoothMBMap₂ F U V) :=
  isEmbedding_toPi.t2Space

/-- The inclusion `C^{∞,∞}(U × V, F) → C^{k,ℓ}(U × V, F)` is continuous. -/
theorem continuous_toCk₂ (k ℓ : ℕ) : Continuous (toCk₂ (F := F) (U := U) (V := V) k ℓ) := by
  have h : Continuous (toPi (F := F) (U := U) (V := V)) := continuous_induced_dom
  exact ContDiffMBMap₂.continuous_iff.2 fun i j _ _ ↦
    ((continuous_apply j).comp ((continuous_apply i).comp h)).congr fun _ ↦
      ContinuousMap.ext fun _ ↦ rfl

/-- A map into `C^{∞,∞}(U × V, F)` is continuous if and only if its compositions with the
inclusions into the `C^{k,ℓ}(U × V, F)` are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → SmoothMBMap₂ F U V} :
    Continuous φ ↔ ∀ k ℓ, Continuous fun x ↦ toCk₂ k ℓ (φ x) :=
  ⟨fun h k ℓ ↦ (continuous_toCk₂ k ℓ).comp h, fun h ↦ continuous_induced_rng.2 <|
    continuous_pi fun i ↦ continuous_pi fun j ↦
      ((ContDiffMBMap₂.continuous_iteratedD₂ i j le_rfl le_rfl).comp (h i j)).congr fun _ ↦ rfl⟩

/-- **[GN26, Corollary 1.7.34]**: `C^∞(U × V, F) = C^{∞,∞}(U × V, F)` as locally convex
spaces: the compact-open `C^∞` and `C^{∞,∞}` topologies coincide. -/
def equivSmooth : SmoothMBMap F (Opens.prod U V) ≃L[ℝ] SmoothMBMap₂ F U V where
  toFun f := mk f ((smoothMBOn_prod_iff U.isOpen V.isOpen).1 f.smoothMBOn)
    fun _ hp ↦ f.apply_of_notMem hp
  invFun g := SmoothMBMap.mk g ((smoothMBOn_prod_iff U.isOpen V.isOpen).2 g.contDiffMBOn₂)
    fun _ hp ↦ g.apply_of_notMem hp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_iff.2 fun k ℓ ↦
    ((ContDiffMBMap₂.ofContDiffMBMapCLM (F := F) (k := k) (ℓ := ℓ) (U := U)
      (V := V)).continuous.comp (SmoothMBMap.continuous_toCk (k + ℓ))).congr fun _ ↦ rfl
  continuous_invFun := SmoothMBMap.continuous_iff.2 fun k ↦
    (ContDiffMBMap₂.continuous_toContDiffMBMap.comp (continuous_toCk₂ k k)).congr fun _ ↦ rfl

end SmoothMBMap₂

end SmoothTwo

/-! ### Corollary 1.7.35: the exponential law for smooth maps -/

section SmoothExp

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace SmoothMBMap

variable {U : Opens E₁} {V : Opens E₂}

/-- A smooth map on `U × V` as a `C^{k,ℓ}` map. -/
def toCk₂ (k ℓ : ℕ) (f : SmoothMBMap F (Opens.prod U V)) : ContDiffMBMap₂ F k ℓ U V :=
  ContDiffMBMap₂.ofContDiffMBMap (toCk (k + ℓ) f)

/-- `C^∞(U × V, F) → C^{k,ℓ}(U × V, F)` is continuous. -/
theorem continuous_toCk₂ (k ℓ : ℕ) :
    Continuous (toCk₂ (F := F) (U := U) (V := V) k ℓ) :=
  ContDiffMBMap₂.ofContDiffMBMapCLM.continuous.comp (continuous_toCk (k + ℓ))

/-- The partial map `f^∨(x) = f(x, ·) ∈ C^∞(V, F)` of a smooth map `f` on `U × V`. -/
def partialMap (f : SmoothMBMap F (Opens.prod U V)) (x : E₁) : SmoothMBMap F V :=
  mk (fun y ↦ f (x, y)) (fun ℓ ↦ (ContDiffMBMap₂.partialMap (toCk₂ 0 ℓ f) x).contDiffMBOn)
    fun _ hy ↦ f.apply_of_notMem fun h ↦ hy h.2

/-- The compositions of `f^∨` with the inclusions `C^∞(V, F) → C^ℓ(V, F)` are the partial maps
of `f` regarded as a `C^{k,ℓ}` map. -/
theorem toCk_partialMap (f : SmoothMBMap F (Opens.prod U V)) (k ℓ : ℕ) :
    (fun x ↦ toCk ℓ (partialMap f x)) = ContDiffMBMap₂.partialMap (toCk₂ k ℓ f) :=
  funext fun _ ↦ ContDiffMBMap.ext fun _ ↦ rfl

/-- **[GN26, Corollary 1.7.35]** (first part): `f^∨ : U → C^∞(V, F)` is smooth. -/
theorem smoothMBOn_partialMap (f : SmoothMBMap F (Opens.prod U V)) :
    SmoothMBOn (partialMap f) U := fun k ↦ (contDiffMBOn_iff U.isOpen).2 fun ℓ ↦ by
  rw [toCk_partialMap f k ℓ]
  exact ContDiffMBMap₂.contDiffMBOn_partialMap _

/-- The curried map `Φ(f) = f^∨ ∈ C^∞(U, C^∞(V, F))` of a smooth map `f` on `U × V`. -/
def curry (f : SmoothMBMap F (Opens.prod U V)) : SmoothMBMap (SmoothMBMap F V) U :=
  mk (partialMap f) (smoothMBOn_partialMap f) fun _ hx ↦
    SmoothMBMap.ext fun _ ↦ f.apply_of_notMem fun h ↦ hx h.1

/-- `Φ(f)(x)(y) = f(x, y)`. -/
@[simp]
theorem curry_apply_apply (f : SmoothMBMap F (Opens.prod U V)) (x : E₁) (y : E₂) :
    curry f x y = f (x, y) :=
  rfl

/-- **[GN26, (1.98)]** for smooth maps:
`d^(j)(d^(i)(f^∨)(x, v))(y, w) = d^(i,j) f(x, y, v, w)`. -/
theorem iteratedD_iteratedD_curry (f : SmoothMBMap F (Opens.prod U V)) {i j k ℓ : ℕ}
    (hi : i ≤ k) (hj : j ≤ ℓ) (q : U × (Fin i → E₁)) (p : V × (Fin j → E₂)) :
    ContDiffMBMap.iteratedD j hj (toCk ℓ (ContDiffMBMap.iteratedD i hi (toCk k (curry f)) q)) p =
      iteratedDMB₂ i j f (((q.1 : E₁), (p.1 : E₂)), q.2, p.2) := by
  have h := iteratedDMB_clm_comp U.isOpen ((smoothMBOn_partialMap f) k)
    (toCkCLM (F := F) (U := V) ℓ) i hi q.1 q.1.2 q.2
  have e : ContDiffMBMap.iteratedD i hi (toCk k (curry f)) q =
      iteratedDMB i (partialMap f) ((q.1 : E₁), q.2) := rfl
  rw [e, show toCk ℓ = ⇑(toCkCLM (F := F) (U := V) ℓ) from rfl, ← h]
  have e2 : (fun z ↦ toCkCLM (F := F) (U := V) ℓ (partialMap f z)) =
      ⇑(ContDiffMBMap₂.curry (toCk₂ k ℓ f)) := toCk_partialMap f k ℓ
  rw [e2]
  exact ContDiffMBMap₂.iteratedD_iteratedD_curry (toCk₂ k ℓ f) hi hj q p

/-- `Φ` is injective. -/
theorem curry_injective : Function.Injective (curry (F := F) (U := U) (V := V)) :=
  fun f g h ↦ SmoothMBMap.ext fun p ↦ by
    simpa using congrArg (fun γ : SmoothMBMap (SmoothMBMap F V) U ↦ γ p.1 p.2) h

/-- `Φ : C^∞(U × V, F) → C^∞(U, C^∞(V, F))` is continuous. -/
theorem continuous_curry : Continuous (curry (F := F) (U := U) (V := V)) := by
  refine continuous_iff.2 fun k ↦ ContDiffMBMap.continuous_iff.2 fun i hi ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K hK ↦ ?_
  refine continuous_iff.2 fun ℓ ↦ ContDiffMBMap.continuous_iff.2 fun j hj ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K' hK' ↦ ?_
  let σ : (U × (Fin i → E₁)) × (V × (Fin j → E₂)) → (U × V) × (Fin i → E₁) × (Fin j → E₂) :=
    fun z ↦ ((z.1.1, z.2.1), z.1.2, z.2.2)
  have hσ : Continuous σ := by fun_prop
  have h := ContinuousMap.continuous_eval_comp_restrict (W := F) hσ (hK.prod hK')
  have h2 : Continuous fun r : (SmoothMBMap F (Opens.prod U V) × K) × K' ↦
      (ContDiffMBMap₂.iteratedD₂ i j le_rfl le_rfl (toCk₂ i j r.1.1),
        (⟨((r.1.2 : U × (Fin i → E₁)), (r.2 : V × (Fin j → E₂))), ⟨r.1.2.2, r.2.2⟩⟩ :
          (K ×ˢ K' : Set _))) :=
    ((ContDiffMBMap₂.continuous_iteratedD₂ i j le_rfl le_rfl).comp
      ((continuous_toCk₂ i j).comp continuous_fst.fst)).prodMk (by fun_prop)
  refine (h.comp h2).congr fun r ↦ ?_
  exact (iteratedD_iteratedD_curry r.1.1 hi hj _ _).symm

/-- If `φ : X → C^∞(U × V, F)` becomes continuous after composition with `Φ`, then so do its
compositions with the inclusions into the `C^{m,m}(U × V, F)`. -/
theorem continuous_toCk₂_of_continuous_curry {X : Type*} [tX : TopologicalSpace X]
    {φ : X → SmoothMBMap F (Opens.prod U V)} (hφ : Continuous fun x ↦ curry (φ x)) (m : ℕ) :
    Continuous fun x ↦ toCk₂ m m (φ x) := by
  refine ContDiffMBMap₂.continuous_iff.2 fun i j hi hj ↦ ?_
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K hK ↦ ?_
  let σ₁ : (U × V) × (Fin i → E₁) × (Fin j → E₂) → U × (Fin i → E₁) := fun z ↦ (z.1.1, z.2.1)
  let σ₂ : (U × V) × (Fin i → E₁) × (Fin j → E₂) → V × (Fin j → E₂) := fun z ↦ (z.1.2, z.2.2)
  have hA : Continuous fun q : X × K ↦
      ContDiffMBMap.iteratedD i le_rfl (toCk i (curry (φ q.1))) (σ₁ q.2) :=
    (ContinuousMap.continuous_eval_comp_restrict (W := SmoothMBMap F V)
      (by fun_prop : Continuous σ₁) hK).comp
      (((ContDiffMBMap.continuous_iteratedD i le_rfl).comp
        ((continuous_toCk i).comp (hφ.comp continuous_fst))).prodMk continuous_snd)
  have hB : Continuous fun q : X × K ↦ ContDiffMBMap.iteratedD j le_rfl
      (toCk j (ContDiffMBMap.iteratedD i le_rfl (toCk i (curry (φ q.1))) (σ₁ q.2))) (σ₂ q.2) :=
    (ContinuousMap.continuous_eval_comp_restrict (W := F) (by fun_prop : Continuous σ₂) hK).comp
      (((ContDiffMBMap.continuous_iteratedD j le_rfl).comp
        ((continuous_toCk j).comp hA)).prodMk continuous_snd)
  refine hB.congr fun q ↦ ?_
  exact iteratedD_iteratedD_curry (φ q.1) le_rfl le_rfl _ _

/-- If `φ : X → C^∞(U × V, F)` becomes continuous after composition with `Φ`, then so does
`γ ↦ (d^(m)γ)_m`. -/
theorem continuous_toPi_of_continuous_curry {X : Type*} [tX : TopologicalSpace X]
    {φ : X → SmoothMBMap F (Opens.prod U V)} (hφ : Continuous fun x ↦ curry (φ x)) :
    Continuous fun x ↦ toPi (φ x) :=
  continuous_pi fun m ↦ ((ContDiffMBMap.continuous_iteratedD m le_rfl).comp
    (ContDiffMBMap₂.continuous_toContDiffMBMap.comp
      (continuous_toCk₂_of_continuous_curry hφ m))).congr fun _ ↦ rfl

/-- **[GN26, Corollary 1.7.35]**: `Φ : C^∞(U × V, F) → C^∞(U, C^∞(V, F))`, `f ↦ f^∨`, is a
topological embedding. -/
theorem isEmbedding_curry : Topology.IsEmbedding (curry (F := F) (U := U) (V := V)) := by
  refine ⟨(Topology.isInducing_iff _).2 ?_, curry_injective⟩
  refine le_antisymm (continuous_iff_le_induced.1 continuous_curry) ?_
  have h := continuous_toPi_of_continuous_curry (X := SmoothMBMap F (Opens.prod U V))
    (tX := TopologicalSpace.induced curry inferInstance) (φ := id) continuous_induced_dom
  exact continuous_iff_le_induced.1 h

/-- `Φ` as a continuous linear map. -/
def curryCLM : SmoothMBMap F (Opens.prod U V) →L[ℝ] SmoothMBMap (SmoothMBMap F V) U where
  toFun := curry
  map_add' _ _ := SmoothMBMap.ext fun _ ↦ SmoothMBMap.ext fun _ ↦ rfl
  map_smul' _ _ := SmoothMBMap.ext fun _ ↦ SmoothMBMap.ext fun _ ↦ rfl
  cont := continuous_curry

section LocallyCompact

variable [LocallyCompactSpace E₂]

/-- The map `g^∧(x, y) = g(x)(y)` of `g ∈ C^∞(U, C^∞(V, F))`, for `E₂` locally compact. -/
def uncurry (g : SmoothMBMap (SmoothMBMap F V) U) : SmoothMBMap F (Opens.prod U V) :=
  mk (fun p ↦ g p.1 p.2) ((smoothMBOn_prod_iff U.isOpen V.isOpen).2 fun k ℓ ↦
      (ContDiffMBMap₂.uncurry (ContDiffMBMap.mk (fun x ↦ toCk ℓ (g x))
        ((contDiffMBOn_iff U.isOpen).1 (g.contDiffMBOn k) ℓ)
        fun x hx ↦ by
          rw [g.apply_of_notMem hx]
          exact ContDiffMBMap.ext fun _ ↦ rfl)).contDiffMBOn₂)
    fun p hp ↦ by
      by_cases h1 : p.1 ∈ U
      · exact (g p.1).apply_of_notMem fun h2 ↦ hp ⟨h1, h2⟩
      · rw [g.apply_of_notMem h1]; rfl

/-- `Φ(g^∧) = g`. -/
theorem curry_uncurry (g : SmoothMBMap (SmoothMBMap F V) U) : curry (uncurry g) = g :=
  SmoothMBMap.ext fun _ ↦ SmoothMBMap.ext fun _ ↦ rfl

/-- **[GN26, Corollary 1.7.35]** (exponential law for smooth maps): if `E₂` is locally
compact, `Φ : C^∞(U × V, F) → C^∞(U, C^∞(V, F))`, `f ↦ f^∨`, is an isomorphism of topological
vector spaces, with inverse `g ↦ g^∧`. -/
def curryEquiv : SmoothMBMap F (Opens.prod U V) ≃L[ℝ] SmoothMBMap (SmoothMBMap F V) U where
  toLinearMap := curryCLM.toLinearMap
  invFun := uncurry
  left_inv f := curry_injective (curry_uncurry (curry f))
  right_inv := curry_uncurry
  continuous_toFun := continuous_curry
  continuous_invFun := by
    rw [isEmbedding_curry.isInducing.continuous_iff]
    exact continuous_id.congr fun g ↦ (curry_uncurry g).symm

/-- **[GN26, Remark 1.7.31(b)]**, smooth case: for `E₂` locally compact and
`g : E₁ → C^∞(V, F)` vanishing outside `U`, `g` is smooth on `U` if and only if
`g^∧ : (x, y) ↦ g(x)(y)` is smooth on `U × V`. -/
theorem smoothMBOn_iff_smoothMBOn_uncurry {g : E₁ → SmoothMBMap F V} (hg0 : ∀ x ∉ U, g x = 0) :
    SmoothMBOn g U ↔ SmoothMBOn (fun p ↦ g p.1 p.2) ((U : Set E₁) ×ˢ (V : Set E₂)) := by
  constructor
  · intro hg
    exact (uncurry (mk g hg hg0)).smoothMBOn
  · intro hg
    have h0 : ∀ p ∉ ((Opens.prod U V : Opens (E₁ × E₂)) : Set (E₁ × E₂)), g p.1 p.2 = 0 := by
      intro p hp
      by_cases h1 : p.1 ∈ U
      · exact (g p.1).apply_of_notMem fun h2 ↦ hp ⟨h1, h2⟩
      · rw [hg0 p.1 h1]; rfl
    have h := smoothMBOn_partialMap (mk (fun p ↦ g p.1 p.2) hg h0)
    intro k
    exact ContDiffMBOn.congr_of_isOpen U.isOpen
      (fun x _ ↦ SmoothMBMap.ext fun _ ↦ rfl) (h k)

end LocallyCompact

end SmoothMBMap

end SmoothExp

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.DenseInterior.ExpLaw

/-!
# `C^{k,ℓ}` maps on sets with dense interior, `k, ℓ ∈ ℕ₀ ∪ {∞}`

Reference: [GN26, Definition 1.7.17, p. 94], where `k, ℓ ∈ ℕ₀ ∪ {∞}`.

`ContDiffLC₂ k ℓ f U V` (`Calculus/DenseInterior/Ckl.lean`) is defined for finite `k`, `ℓ`. A map is
`C^{k,ℓ}` for `k, ℓ ∈ ℕ∞` (`ContDiffLC₂UpTo`) if it is `C^{i,j}` for all finite `i ≤ k`,
`j ≤ ℓ`: Definition 1.7.17 asks for the continuous extensions of the `d^(i,j) f` with `i ≤ k`,
`j ≤ ℓ`, each of which involves only finitely many derivatives. For finite `k`, `ℓ` the two notions
agree (`contDiffLC₂UpTo_coe_iff`), and the results for finite orders pass to `k, ℓ = ∞`.

The exponential law as an isomorphism `C^{∞,∞}(U × V, F) ≅ C^∞(U, C^∞(V, F))`, which needs the
space `C^∞(V, F)` with its projective limit topology, is in
`Calculus/DenseInterior/SmoothExpLaw.lean`.

## Main definitions

* `ContDiffLC₂UpTo k ℓ f U V`: `f` is `C^{i,j}` on `U × V` for all finite `i ≤ k`, `j ≤ ℓ`
  ([GN26, Definition 1.7.17]).

## Main results

* `contDiffLC₂UpTo_coe_iff`: for finite `k`, `ℓ`, `ContDiffLC₂UpTo` is `ContDiffLC₂`.
* `ContDiffLC₂UpTo.of_le`, `ContDiffLC₂UpTo.congr`, `ContDiffLC₂UpTo.clm_comp`,
  `ContDiffLC₂UpTo.prodMk`, `ContDiffLC₂UpTo.add`, `ContDiffLC₂UpTo.const_smul`,
  `contDiffLC₂UpTo_const`, `contDiffLC₂UpTo_prodMk_iff`, `ContDiffLC₂UpTo.pi`,
  `contDiffLC₂UpTo_pi_iff`: `C^{k,ℓ}` maps are stable under the basic operations, and a map into
  a product is `C^{k,ℓ}` if and only if its components are ([GN26, Lemma 1.7.20]).
* `ContDiffLC₂UpTo.contDiffLC_right`, `ContDiffLC₂UpTo.smoothLC_right`: the partial maps
  `f(x, ·)` are `C^j` for all finite `j ≤ ℓ`, and smooth if `ℓ = ∞` ([GN26, Lemma 1.7.18]).
* `ContDiffLC₂UpTo.contDiffLC_left`: for finite `j ≤ ℓ`, `y ∈ V` and `w ∈ E₂^j`, the map
  `x ↦ d^(0,j) f(x, y, w)` is `C^i` for all finite `i ≤ k` ([GN26, Remark 1.7.19(b)]).
* `ContDiffLC₂UpTo.comp_prodMap`: `g ∘ (f₁ × f₂)` is `C^{r,s}` if `g` is `C^{r,s}`, `f₁` is
  `C^r` and `f₂` is `C^s` ([GN26, Lemma 1.7.26]); `ContDiffLC₂UpTo.comp_left`: `g ∘ f` is
  `C^{r,s}` if `f` is `C^{r,s}` and `g` is `C^{r+s}` ([GN26, Lemma 1.7.28]).
* `contDiffLC₂UpTo_of_contDiffLC`, `SmoothLC.contDiffLC₂UpTo`: `C^{k+ℓ}` maps on `U × V` are
  `C^{k,ℓ}`, and smooth maps are `C^{∞,∞}` ([GN26, Proposition 1.7.33(a)]).
* `ContDiffLC₂UpTo.contDiffLC_curryLC`: `f^∨ : U → C^j(V, F)` is `C^i` for finite `i ≤ k`,
  `j ≤ ℓ` ([GN26, Theorem 1.7.30], first part).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {k ℓ : ℕ∞} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

/-- **`C^{k,ℓ}` maps for `k, ℓ ∈ ℕ₀ ∪ {∞}`** ([GN26, Definition 1.7.17]): `f` is `C^{i,j}`
on `U × V` for all finite `i ≤ k` and `j ≤ ℓ`. -/
def ContDiffLC₂UpTo (k ℓ : ℕ∞) (f : E₁ × E₂ → F) (U : Set E₁) (V : Set E₂) : Prop :=
  ∀ i j : ℕ, (i : ℕ∞) ≤ k → (j : ℕ∞) ≤ ℓ → ContDiffLC₂ i j f U V

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- For finite orders, `ContDiffLC₂UpTo` is `ContDiffLC₂`. -/
theorem contDiffLC₂UpTo_coe_iff {k ℓ : ℕ} :
    ContDiffLC₂UpTo k ℓ f U V ↔ ContDiffLC₂ k ℓ f U V :=
  ⟨fun h ↦ h k ℓ le_rfl le_rfl, fun h i j hi hj ↦ h.of_le (by exact_mod_cast hi)
    (by exact_mod_cast hj)⟩

namespace ContDiffLC₂UpTo

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
theorem of_le {k' ℓ' : ℕ∞} (hf : ContDiffLC₂UpTo k ℓ f U V) (hk : k' ≤ k) (hl : ℓ' ≤ ℓ) :
    ContDiffLC₂UpTo k' ℓ' f U V :=
  fun i j hi hj ↦ hf i j (hi.trans hk) (hj.trans hl)

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
theorem congr {g : E₁ × E₂ → F} (hf : ContDiffLC₂UpTo k ℓ f U V) (h : EqOn f g (U ×ˢ V)) :
    ContDiffLC₂UpTo k ℓ g U V :=
  fun i j hi hj ↦ (hf i j hi hj).congr h

theorem clm_comp (L : F →L[ℝ] G) (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂UpTo k ℓ f U V) : ContDiffLC₂UpTo k ℓ (fun p ↦ L (f p)) U V :=
  fun i j hi hj ↦ (hf i j hi hj).clm_comp L hU hV

theorem prodMk {g : E₁ × E₂ → G} (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂UpTo k ℓ f U V) (hg : ContDiffLC₂UpTo k ℓ g U V) :
    ContDiffLC₂UpTo k ℓ (fun p ↦ (f p, g p)) U V :=
  fun i j hi hj ↦ (hf i j hi hj).prodMk hU hV (hg i j hi hj)

theorem add {g : E₁ × E₂ → F} (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂UpTo k ℓ f U V) (hg : ContDiffLC₂UpTo k ℓ g U V) :
    ContDiffLC₂UpTo k ℓ (fun p ↦ f p + g p) U V :=
  fun i j hi hj ↦ (hf i j hi hj).add hU hV (hg i j hi hj)

theorem const_smul (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂UpTo k ℓ f U V) (c : ℝ) : ContDiffLC₂UpTo k ℓ (fun p ↦ c • f p) U V :=
  fun i j hi hj ↦ (hf i j hi hj).const_smul hU hV c

end ContDiffLC₂UpTo

theorem contDiffLC₂UpTo_const (hU : HasDenseInterior U) (hV : HasDenseInterior V) (c : F) :
    ContDiffLC₂UpTo k ℓ (fun _ : E₁ × E₂ ↦ c) U V :=
  fun _ _ _ _ ↦ contDiffLC₂_const hU hV c

theorem contDiffLC₂UpTo_prodMk_iff {g : E₁ × E₂ → G} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) :
    ContDiffLC₂UpTo k ℓ (fun p ↦ (f p, g p)) U V ↔
      ContDiffLC₂UpTo k ℓ f U V ∧ ContDiffLC₂UpTo k ℓ g U V :=
  ⟨fun h ↦ ⟨fun i j hi hj ↦ ((contDiffLC₂_prodMk_iff hU hV).1 (h i j hi hj)).1,
    fun i j hi hj ↦ ((contDiffLC₂_prodMk_iff hU hV).1 (h i j hi hj)).2⟩,
    fun h ↦ h.1.prodMk hU hV h.2⟩

/-- **[GN26, Lemma 1.7.20]**, for `k, ℓ ∈ ℕ∞`: maps into products. -/
theorem ContDiffLC₂UpTo.pi {ι : Type w} {Fi : ι → Type v} [∀ a, AddCommGroup (Fi a)]
    [∀ a, Module ℝ (Fi a)] [∀ a, TopologicalSpace (Fi a)] [∀ a, IsTopologicalAddGroup (Fi a)]
    [∀ a, ContinuousSMul ℝ (Fi a)] [∀ a, LocallyConvexSpace ℝ (Fi a)] [∀ a, T2Space (Fi a)]
    {f : ∀ a, E₁ × E₂ → Fi a} (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ∀ a, ContDiffLC₂UpTo k ℓ (f a) U V) : ContDiffLC₂UpTo k ℓ (fun p a ↦ f a p) U V :=
  fun i j hi hj ↦ ContDiffLC₂.pi hU hV fun a ↦ hf a i j hi hj

/-- **[GN26, Lemma 1.7.20]**, for `k, ℓ ∈ ℕ∞`. -/
theorem contDiffLC₂UpTo_pi_iff {ι : Type w} {Fi : ι → Type v} [∀ a, AddCommGroup (Fi a)]
    [∀ a, Module ℝ (Fi a)] [∀ a, TopologicalSpace (Fi a)] [∀ a, IsTopologicalAddGroup (Fi a)]
    [∀ a, ContinuousSMul ℝ (Fi a)] [∀ a, LocallyConvexSpace ℝ (Fi a)] [∀ a, T2Space (Fi a)]
    {f : ∀ a, E₁ × E₂ → Fi a} (hU : HasDenseInterior U) (hV : HasDenseInterior V) :
    ContDiffLC₂UpTo k ℓ (fun p a ↦ f a p) U V ↔ ∀ a, ContDiffLC₂UpTo k ℓ (f a) U V :=
  ⟨fun h a i j hi hj ↦ (contDiffLC₂_pi_iff hU hV).1 (h i j hi hj) a,
    ContDiffLC₂UpTo.pi hU hV⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- **[GN26, Lemma 1.7.18]**, for `k, ℓ ∈ ℕ∞`: the partial maps `f(x, ·)` are `C^j` for
all finite `j ≤ ℓ`. -/
theorem ContDiffLC₂UpTo.contDiffLC_right (hf : ContDiffLC₂UpTo k ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) {x : E₁} (hx : x ∈ U) (j : ℕ)
    (hj : (j : ℕ∞) ≤ ℓ) : ContDiffLC j (fun y ↦ f (x, y)) V :=
  ((hf 0 j (by simp) hj).contDiffLC_right hU hV hx).1

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- For `ℓ = ∞` the partial maps `f(x, ·)` are smooth. -/
theorem ContDiffLC₂UpTo.smoothLC_right (hf : ContDiffLC₂UpTo k ⊤ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) {x : E₁} (hx : x ∈ U) :
    SmoothLC (fun y ↦ f (x, y)) V :=
  fun j ↦ hf.contDiffLC_right hU hV hx j le_top

omit [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **[GN26, Remark 1.7.19(b)]**, for `k, ℓ ∈ ℕ∞`: for `y ∈ V`, `w ∈ E₂^j` and finite
`j ≤ ℓ`, the map `x ↦ d^(0,j) f(x, y, w)` (the continuous extension, `iteratedDLC₂`) is `C^i`
for all finite `i ≤ k`. -/
theorem ContDiffLC₂UpTo.contDiffLC_left (hf : ContDiffLC₂UpTo k ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) {j : ℕ} (hj : (j : ℕ∞) ≤ ℓ) {y : E₂}
    (hy : y ∈ V) (w : Fin j → E₂) (i : ℕ) (hi : (i : ℕ∞) ≤ k) :
    ContDiffLC i (fun x ↦ iteratedDLC₂ 0 j f U V ((x, y), Fin.elim0, w)) U :=
  ((hf i j hi hj).contDiffLC_left hU hV le_rfl hy w
    ((hf i j hi hj).continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) le_rfl)
    (iteratedDLC₂_eqOn_interior 0 j f U V)).1

/-- **[GN26, Proposition 1.7.33(a)]**, for `k, ℓ ∈ ℕ∞`: a map which is `C^n` on `U × V`
for all finite `n ≤ k + ℓ` is `C^{k,ℓ}`. -/
theorem contDiffLC₂UpTo_of_contDiffLC
    (hf : ∀ n : ℕ, (n : ℕ∞) ≤ k + ℓ → ContDiffLC n f (U ×ˢ V)) : ContDiffLC₂UpTo k ℓ f U V :=
  fun i j hi hj ↦ (hf (i + j) (by push_cast; exact add_le_add hi hj)).contDiffLC₂

/-- Smooth maps on `U × V` are `C^{∞,∞}`. -/
theorem SmoothLC.contDiffLC₂UpTo (hf : SmoothLC f (U ×ˢ V)) : ContDiffLC₂UpTo k ℓ f U V :=
  contDiffLC₂UpTo_of_contDiffLC fun n _ ↦ hf n

/-- **[GN26, Theorem 1.7.30]**, first part, for `k, ℓ ∈ ℕ∞`: `f^∨ : U → C^j(V, F)` is `C^i`
for all finite `i ≤ k` and `j ≤ ℓ`. -/
theorem ContDiffLC₂UpTo.contDiffLC_curryLC (hf : ContDiffLC₂UpTo k ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) (i j : ℕ) (hi : (i : ℕ∞) ≤ k)
    (hj : (j : ℕ∞) ≤ ℓ) : ContDiffLC i (curryLC hU hV (hf i j hi hj)) U :=
  (hf i j hi hj).contDiffLC_curryLC hU hV

section Chain

variable {F₁ : Type u} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [LocallyConvexSpace ℝ F₁] [T2Space F₁]
  {F₂ : Type u} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [LocallyConvexSpace ℝ F₂] [T2Space F₂]

/-- **[GN26, Lemma 1.7.26]**, for `r, s ∈ ℕ∞`: `g ∘ (f₁ × f₂)` is `C^{r,s}` if `g` is
`C^{r,s}`, `f₁` is `C^i` for all finite `i ≤ r` and `f₂` is `C^j` for all finite `j ≤ s`. -/
theorem ContDiffLC₂UpTo.comp_prodMap {r s : ℕ∞} {g : F₁ × F₂ → F} {f₁ : E₁ → F₁}
    {f₂ : E₂ → F₂} {U₁ : Set E₁} {U₂ : Set E₂} {V₁ : Set F₁} {V₂ : Set F₂}
    (hU₁ : HasDenseInterior U₁) (hU₂ : HasDenseInterior U₂) (hV₁c : IsLocallyConvexSubset V₁)
    (hV₁ : HasDenseInterior V₁) (hV₂c : IsLocallyConvexSubset V₂) (hV₂ : HasDenseInterior V₂)
    (hg : ContDiffLC₂UpTo r s g V₁ V₂) (hf₁ : ∀ i : ℕ, (i : ℕ∞) ≤ r → ContDiffLC i f₁ U₁)
    (hf₂ : ∀ j : ℕ, (j : ℕ∞) ≤ s → ContDiffLC j f₂ U₂) (h₁ : MapsTo f₁ U₁ V₁)
    (h₂ : MapsTo f₂ U₂ V₂) : ContDiffLC₂UpTo r s (fun p ↦ g (f₁ p.1, f₂ p.2)) U₁ U₂ :=
  fun i j hi hj ↦ (hg i j hi hj).comp_prodMap hU₁ hU₂ hV₁c hV₁ hV₂c hV₂ (hf₁ i hi) (hf₂ j hj)
    h₁ h₂

/-- **[GN26, Lemma 1.7.28]**, for `r, s ∈ ℕ∞`: `g ∘ f` is `C^{r,s}` if `f` is `C^{r,s}` and
`g` is `C^n` for all finite `n ≤ r + s`. -/
theorem ContDiffLC₂UpTo.comp_left {r s : ℕ∞} {f : E₁ × E₂ → F₁} {g : F₁ → F} {W : Set F₁}
    (hUc : IsLocallyConvexSubset U) (hU : HasDenseInterior U) (hVc : IsLocallyConvexSubset V)
    (hV : HasDenseInterior V) (hWc : IsLocallyConvexSubset W) (hW : HasDenseInterior W)
    (hf : ContDiffLC₂UpTo r s f U V) (hg : ∀ n : ℕ, (n : ℕ∞) ≤ r + s → ContDiffLC n g W)
    (hfW : MapsTo f (U ×ˢ V) W) : ContDiffLC₂UpTo r s (fun p ↦ g (f p)) U V :=
  fun i j hi hj ↦ (hf i j hi hj).comp_left hUc hU hVc hV hWc hW
    (hg (i + j) (by push_cast; exact add_le_add hi hj)) hfW

end Chain

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.DenseInterior.Ckl
public import LocallyConvexAnalysis.Calculus.SmoothExponentialLaw

/-!
# Rules for `C^{k,ℓ}` maps on sets with dense interior

Reference: [GN26, §1.7], pp. 95–100. We continue `LocallyConvexAnalysis.Calculus.DenseInterior.Ckl`.

## Main results

* `ContDiffLC₂.contDiffLC₂_partialDLC₁`, `ContDiffLC₂.succ_of`: **recursion in the first variable**.
  A map `f` is `C^{k+1,ℓ}` on `U × V` if and only if it is `C^{0,ℓ}` and its first partial
  differential `((x, a), y) ↦ d^(1,0) f(x, y, a)` is `C^{k,ℓ}` on `(U × E₁) × V`.
* `ContDiffLC₂.contDiffLC₂_partialDLC₂`, `ContDiffLC₂.zero_succ_of`: **recursion in the second
  variable**. A map is `C^{0,ℓ+1}` if and only if it is continuous and its second partial
  differential `(x, (y, b)) ↦ d^(0,1) f(x, y, b)` is `C^{0,ℓ}` on `U × (V × E₂)`.
* `ContDiffLC₂.of_le`, `ContDiffLC₂.congr`, `ContDiffLC₂.clm_comp`: monotonicity, locality, and
  composition with continuous linear maps.
* `contDiffLC₂_pi_iff`, `contDiffLC₂_prodMk_iff`: mappings to products
  ([GN26, Proposition 1.7.20]).
* `ContDiffLC₂.dLC_left`, `ContDiffLC₂.dLC_right`: the partial maps `f(·, y)` and `f(x, ·)` are
  `C^k` and `C^ℓ`, with differentials `d^(1,0) f` and `d^(0,1) f`, also at boundary points.
* `ContDiffLC₂.comp_prodMap`: **chain rule 1**, `(x, y) ↦ g(f₁ x, f₂ y)` is `C^{r,s}` for `g` of
  class `C^{r,s}`, `f₁` of class `C^r` and `f₂` of class `C^s`
  ([GN26, Proposition 1.7.26]).
* `ContDiffLC₂.comp_left`: **chain rule 2**, `g ∘ f` is `C^{r,s}` for `f` of class `C^{r,s}` and
  `g` of class `C^{r+s}` ([GN26, Proposition 1.7.28]).

## Implementation notes

* **Departure from Glöckner–Neeb in Propositions 1.7.26 and 1.7.28.** Glöckner–Neeb compute the
  mixed differentials of the composite with Faà di Bruno's formula ((1.91)–(1.97)). We prove the
  recursive characterization above instead, with explicit formulas for the mixed differentials of
  the partial differentials (`iteratedDMB₂_partialD₁`, `iteratedDMB_partialD₂_right`, which rest
  on `ContDiffMBOn.iteratedDMB_dMB`) and the interchange of a derivative in the first variable
  with derivatives in the second one (`hasDirDerivAt_iteratedDMB_right_of`, from
  `hasDirDerivAt_comm`). The chain rules, and the statements on products, then follow by
  induction from the chain rule for `C^k` maps (Proposition 1.4.10, `ContDiffLC.comp_one`): for
  instance `d^(1,0) (g ∘ (f₁ × f₂))((x, a), y) = d^(1,0) g((f₁ x, df₁(x, a)), f₂ y)`. We do not
  claim these arguments are new.
* As in `LocallyConvexAnalysis.Calculus.CklMaps`, only finite `k`, `ℓ` are treated. The chain rules
  ask the target sets `V₁`, `V₂`, `W` (and, in chain rule 2, also `U` and `V`) to be locally convex,
  as in Glöckner–Neeb; all spaces are real locally convex Hausdorff spaces in one universe.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### Partial differentials on open sets -/

section OpenPartials

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

/-- The first partial differential `((x, a), y) ↦ d^(1,0) f(x, y, a)`. -/
def partialD₁ (f : E₁ × E₂ → F) (p : (E₁ × E₁) × E₂) : F :=
  iteratedDMB₂ 1 0 f ((p.1.1, p.2), fun _ ↦ p.1.2, Fin.elim0)

/-- The second partial differential `(x, (y, b)) ↦ d^(0,1) f(x, y, b)`. -/
def partialD₂ (f : E₁ × E₂ → F) (p : E₁ × (E₂ × E₂)) : F :=
  iteratedDMB₂ 0 1 f ((p.1, p.2.1), Fin.elim0, fun _ ↦ p.2.2)

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The differentials of `partialD₁ f` in the second variable. -/
theorem iteratedDMB_partialD₁_right (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) ℓ f U V) {j : ℕ} (hj : j ≤ ℓ) {xa : E₁ × E₁}
    (hxa : xa.1 ∈ U) {y : E₂} (hy : y ∈ V) (w : Fin j → E₂) :
    iteratedDMB j (fun y' ↦ partialD₁ f (xa, y')) (y, w) =
      dMB (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w)) xa :=
  hf.iteratedDMB_right hU hV (i := 1) (by omega) hxa (fun _ ↦ xa.2) j hj y hy w

omit [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The mixed differentials of `partialD₁ f`. -/
theorem iteratedDMB₂_partialD₁ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) ℓ f U V) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ) {x a : E₁} {y : E₂}
    (hx : x ∈ U) (hy : y ∈ V) (vv : Fin i → E₁ × E₁) (w : Fin j → E₂) :
    iteratedDMB₂ i j (partialD₁ f) (((x, a), y), vv, w) =
      iteratedDMB₂ (i + 1) j f ((x, y), Fin.cons a fun s ↦ (vv s).1, w) +
        ∑ s, iteratedDMB₂ i j f ((x, y), update (fun s ↦ (vv s).1) s (vv s).2, w) := by
  have hφ := hf.contDiffMBOn_left j hj y hy w
  change iteratedDMB i (fun xa ↦ iteratedDMB j (fun y' ↦ partialD₁ f (xa, y')) (y, w))
    ((x, a), vv) = _
  rw [iteratedDMB_congr_of_eventuallyEq i (Filter.eventually_of_mem
    ((hU.prod isOpen_univ).mem_nhds (show (x, a) ∈ U ×ˢ (univ : Set E₁) from ⟨hx, mem_univ a⟩))
    fun xa hxa ↦ iteratedDMB_partialD₁_right hU hV hf hj hxa.1 hy w)]
  exact hφ.iteratedDMB_dMB hU i hi x hx a (fun s ↦ (vv s).1) fun s ↦ (vv s).2

/-- `partialD₁ f` is `C^{k,ℓ}` on `(U × E₁) × V` if `f` is `C^{k+1,ℓ}` on `U × V`. -/
theorem contDiffMBOn₂_partialD₁ (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ (k + 1) ℓ f U V) :
    ContDiffMBOn₂ k ℓ (partialD₁ f) (U ×ˢ univ) V where
  contDiffMBOn_right xa hxa :=
    hf.contDiffMBOn_right_iteratedDMB₂ hU hV (i := 1) (by omega) hxa.1 (fun _ ↦ xa.2)
  contDiffMBOn_left j hj y hy w :=
    ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ)
      (fun xa hxa ↦ (iteratedDMB_partialD₁_right hU hV hf hj hxa.1 hy w).symm)
      (hf.contDiffMBOn_left j hj y hy w).2.2
  continuousOn i hi j hj := by
    have h₁ := hf.continuousOn_comp (i := i + 1) (j := j) (by omega) hj
      (S := ((U ×ˢ (univ : Set E₁)) ×ˢ V) ×ˢ univ)
      (σ := fun p : ((E₁ × E₁) × E₂) × (Fin i → E₁ × E₁) × (Fin j → E₂) ↦
        ((p.1.1.1, p.1.2), Fin.cons p.1.1.2 fun s ↦ (p.2.1 s).1, p.2.2))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1.1, hp.1.2⟩, mem_univ _⟩
    have h₂ := continuousOn_finsetSum (Finset.univ : Finset (Fin i)) fun s _ ↦
      hf.continuousOn_comp (i := i) (j := j) (by omega) hj
      (S := ((U ×ˢ (univ : Set E₁)) ×ˢ V) ×ˢ univ)
      (σ := fun p : ((E₁ × E₁) × E₂) × (Fin i → E₁ × E₁) × (Fin j → E₂) ↦
        ((p.1.1.1, p.1.2), update (fun s ↦ (p.2.1 s).1) s (p.2.1 s).2, p.2.2))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1.1, hp.1.2⟩, mem_univ _⟩
    refine (h₁.add h₂).congr fun p hp ↦ ?_
    exact iteratedDMB₂_partialD₁ hU hV hf hi hj hp.1.1.1 hp.1.2 p.2.1 p.2.2

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- The differentials of `partialD₂ f` in the second variable. -/
theorem iteratedDMB_partialD₂_right (hV : IsOpen V) (hf : ContDiffMBOn₂ 0 (ℓ + 1) f U V)
    {j : ℕ} (hj : j ≤ ℓ) {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V) (b : E₂)
    (ww : Fin j → E₂ × E₂) :
    iteratedDMB j (fun yb ↦ partialD₂ f (x, yb)) ((y, b), ww) =
      iteratedDMB (j + 1) (fun y' ↦ f (x, y')) (y, Fin.cons b fun t ↦ (ww t).1) +
        ∑ t, iteratedDMB j (fun y' ↦ f (x, y')) (y, update (fun t ↦ (ww t).1) t (ww t).2) :=
  (hf.contDiffMBOn_right x hx).iteratedDMB_dMB hV j hj y hy b (fun t ↦ (ww t).1)
    fun t ↦ (ww t).2

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- `partialD₂ f` is `C^{0,ℓ}` on `U × (V × E₂)` if `f` is `C^{0,ℓ+1}` on `U × V`. -/
theorem contDiffMBOn₂_partialD₂ (hV : IsOpen V) (hf : ContDiffMBOn₂ 0 (ℓ + 1) f U V) :
    ContDiffMBOn₂ 0 ℓ (partialD₂ f) U (V ×ˢ univ) where
  contDiffMBOn_right x hx :=
    ContDiffMBOn.congr_of_isOpen (hV.prod isOpen_univ) (fun _ _ ↦ rfl)
      (hf.contDiffMBOn_right x hx).2.2
  contDiffMBOn_left j hj yb hyb ww := by
    have h₁ : ContinuousOn (fun x' ↦
        iteratedDMB (j + 1) (fun y' ↦ f (x', y')) (yb.1, Fin.cons yb.2 fun t ↦ (ww t).1) +
          ∑ t, iteratedDMB j (fun y' ↦ f (x', y'))
            (yb.1, update (fun t ↦ (ww t).1) t (ww t).2)) U :=
      ContinuousOn.add (hf.contDiffMBOn_left (j + 1) (by omega) yb.1 hyb.1 _)
        (continuousOn_finsetSum _ fun t _ ↦ hf.contDiffMBOn_left j (by omega) yb.1 hyb.1 _)
    exact h₁.congr fun x hx ↦ iteratedDMB_partialD₂_right hV hf hj hx hyb.1 yb.2 ww
  continuousOn i hi j hj := by
    obtain rfl : i = 0 := by omega
    have h₁ := hf.continuousOn_comp (i := 0) (j := j + 1) le_rfl (by omega)
      (S := (U ×ˢ (V ×ˢ (univ : Set E₂))) ×ˢ univ)
      (σ := fun p : (E₁ × (E₂ × E₂)) × (Fin 0 → E₁) × (Fin j → E₂ × E₂) ↦
        ((p.1.1, p.1.2.1), p.2.1, Fin.cons p.1.2.2 fun t ↦ (p.2.2 t).1))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.1⟩, mem_univ _⟩
    have h₂ := continuousOn_finsetSum (Finset.univ : Finset (Fin j)) fun t _ ↦
      hf.continuousOn_comp (i := 0) (j := j) le_rfl (by omega)
      (S := (U ×ˢ (V ×ˢ (univ : Set E₂))) ×ˢ univ)
      (σ := fun p : (E₁ × (E₂ × E₂)) × (Fin 0 → E₁) × (Fin j → E₂ × E₂) ↦
        ((p.1.1, p.1.2.1), p.2.1, update (fun t ↦ (p.2.2 t).1) t (p.2.2 t).2))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1, hp.1.2.1⟩, mem_univ _⟩
    refine (h₁.add h₂).congr fun p hp ↦ ?_
    exact iteratedDMB_partialD₂_right hV hf hj hp.1.1 hp.1.2.1 p.1.2.2 p.2.2

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- Derivatives in the first variable of the differentials in the second one, for a map whose
first partial derivative `G` is `C^{0,ℓ}` (an instance of Schwarz's theorem, compare
[GN26, Proposition 1.7.21]). -/
theorem hasDirDerivAt_iteratedDMB_right_of (hU : IsOpen U) (hV : IsOpen V)
    (hf0 : ContDiffMBOn₂ 0 ℓ f U V) {G : (E₁ × E₁) × E₂ → F}
    (hG : ∀ x ∈ U, ∀ y ∈ V, ∀ a, HasDirDerivAt (fun x' ↦ f (x', y)) x a (G ((x, a), y)))
    (hGc : ContDiffMBOn₂ k ℓ G (U ×ˢ univ) V) :
    ∀ j ≤ ℓ, ∀ x ∈ U, ∀ y ∈ V, ∀ (a : E₁) (w : Fin j → E₂),
      HasDirDerivAt (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w)) x a
        (iteratedDMB j (fun y' ↦ G ((x, a), y')) (y, w))
  | 0, _, x, hx, y, hy, a, _ => hG x hx y hy a
  | j + 1, hj, x, hx, y, hy, a, w => by
    have hUV : IsOpen (U ×ˢ V) := hU.prod hV
    have h := hasDirDerivAt_comm (E := E₁ × E₂) hUV (a := (0, w (Fin.last j))) (b := (a, 0))
      (g := fun p ↦ iteratedDMB j (fun y' ↦ f (p.1, y')) (p.2, Fin.init w))
      (A := fun p ↦ iteratedDMB (j + 1) (fun y' ↦ f (p.1, y')) (p.2, w))
      (B := fun p ↦ iteratedDMB j (fun y' ↦ G ((p.1, a), y')) (p.2, Fin.init w))
      (M := fun p ↦ iteratedDMB (j + 1) (fun y' ↦ G ((p.1, a), y')) (p.2, w))
      (fun p hp ↦ hasDirDerivAt_slice₂.2
        ((hf0.contDiffMBOn_right p.1 hp.1).hasContIterDerivOn.1 j (by omega) p.2 hp.2 w))
      (fun p hp ↦ hasDirDerivAt_slice.2 (hasDirDerivAt_iteratedDMB_right_of hU hV hf0 hG hGc j
        (by omega) p.1 hp.1 p.2 hp.2 a _))
      ((hGc.continuousOn 0 (Nat.zero_le k) j (by omega)).comp
        (f := fun p : E₁ × E₂ ↦ (((p.1, a), p.2), (Fin.elim0 : Fin 0 → E₁ × E₁), Fin.init w))
        (by fun_prop) fun p hp ↦ ⟨⟨⟨hp.1, mem_univ _⟩, hp.2⟩, mem_univ _⟩)
      (fun p hp ↦ hasDirDerivAt_slice₂.2 ((hGc.contDiffMBOn_right (p.1, a)
        ⟨hp.1, mem_univ _⟩).hasContIterDerivOn.1 j (by omega) p.2 hp.2 w))
      ((hGc.continuousOn 0 (Nat.zero_le k) (j + 1) hj).comp
        (f := fun p : E₁ × E₂ ↦ (((p.1, a), p.2), (Fin.elim0 : Fin 0 → E₁ × E₁), w))
        (by fun_prop) fun p hp ↦ ⟨⟨⟨hp.1, mem_univ _⟩, hp.2⟩, mem_univ _⟩)
      (show (x, y) ∈ U ×ˢ V from ⟨hx, hy⟩)
    exact hasDirDerivAt_slice.1 h

omit [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **Recursion in the first variable, on open sets**: if `f` is `C^{0,ℓ}`, with first partial
derivative `d^(1,0) f(x, y, a) = G((x, a), y)` for a `C^{k,ℓ}` map `G`, then `f` is `C^{k+1,ℓ}`,
and `d^(i+1,j) f(x, y, v, w) = d^(i,j) G((x, v₀), y, (v₁, 0), …, (vᵢ, 0), w)`. -/
theorem ContDiffMBOn₂.succ_of (hU : IsOpen U) (hV : IsOpen V) (hf0 : ContDiffMBOn₂ 0 ℓ f U V)
    {G : (E₁ × E₁) × E₂ → F}
    (hG : ∀ x ∈ U, ∀ y ∈ V, ∀ a, HasDirDerivAt (fun x' ↦ f (x', y)) x a (G ((x, a), y)))
    (hGc : ContDiffMBOn₂ k ℓ G (U ×ˢ univ) V) :
    ContDiffMBOn₂ (k + 1) ℓ f U V ∧ ∀ i j, j ≤ ℓ → ∀ x ∈ U, ∀ y ∈ V,
      ∀ (v : Fin (i + 1) → E₁) (w : Fin j → E₂), iteratedDMB₂ (i + 1) j f ((x, y), v, w) =
        iteratedDMB₂ i j G (((x, v 0), y), fun s ↦ (v s.succ, 0), w) := by
  have hd := hasDirDerivAt_iteratedDMB_right_of hU hV hf0 hG hGc
  have hdφ : ∀ j ≤ ℓ, ∀ y ∈ V, ∀ w : Fin j → E₂, ∀ x ∈ U, ∀ a : E₁,
      dMB (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w)) (x, a) =
        iteratedDMB j (fun y' ↦ G ((x, a), y')) (y, w) :=
    fun j hj y hy w x hx a ↦ (hd j hj x hx y hy a w).dMB_eq
  have hform : ∀ i j, j ≤ ℓ → ∀ x ∈ U, ∀ y ∈ V,
      ∀ (v : Fin (i + 1) → E₁) (w : Fin j → E₂), iteratedDMB₂ (i + 1) j f ((x, y), v, w) =
        iteratedDMB₂ i j G (((x, v 0), y), fun s ↦ (v s.succ, 0), w) := by
    intro i j hj x hx y hy v w
    change iteratedDMB (i + 1) (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w)) (x, v) =
      iteratedDMB i (fun xa ↦ iteratedDMB j (fun y' ↦ G (xa, y')) (y, w))
        ((x, v 0), fun s ↦ (v s.succ, 0))
    rw [iteratedDMB_succ_eq_dMB]
    exact iteratedDMB_congr_of_eventuallyEq i (Filter.eventually_of_mem
      ((hU.prod isOpen_univ).mem_nhds (show (x, v 0) ∈ U ×ˢ (univ : Set E₁) from
        ⟨hx, mem_univ _⟩)) fun xa hxa ↦ hdφ j hj y hy w xa.1 hxa.1 xa.2) _
  refine ⟨⟨hf0.contDiffMBOn_right, fun j hj y hy w ↦ ⟨hf0.contDiffMBOn_left j hj y hy w,
    fun x hx a ↦ ?_, ?_⟩, fun i hi j hj ↦ ?_⟩, hform⟩
  · rw [hdφ j hj y hy w x hx a]
    exact hd j hj x hx y hy a w
  · exact ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ)
      (fun xa hxa ↦ (hdφ j hj y hy w xa.1 hxa.1 xa.2).symm) (hGc.contDiffMBOn_left j hj y hy w)
  · cases i with
    | zero => exact hf0.continuousOn 0 le_rfl j hj
    | succ i =>
      refine ((hGc.continuousOn i (by omega) j hj).comp
        (f := fun p : (E₁ × E₂) × (Fin (i + 1) → E₁) × (Fin j → E₂) ↦
          (((p.1.1, p.2.1 0), p.1.2), (fun s ↦ (p.2.1 s.succ, 0) : Fin i → E₁ × E₁), p.2.2))
        (by fun_prop) fun p (hp : p ∈ ((U ×ˢ V : Set (E₁ × E₂)) ×ˢ
          (univ : Set ((Fin (i + 1) → E₁) × (Fin j → E₂))))) ↦
          ⟨⟨⟨hp.1.1, mem_univ _⟩, hp.1.2⟩, mem_univ _⟩).congr
        fun p hp ↦ ?_
      exact hform i j hj p.1.1 hp.1.1 p.1.2 hp.1.2 p.2.1 p.2.2

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- **Recursion in the second variable, on open sets** (for `k = 0`): if `f` is continuous, with
second partial derivative `d^(0,1) f(x, y, b) = H(x, (y, b))` for a `C^{0,ℓ}` map `H`, then `f`
is `C^{0,ℓ+1}`, and `d^(0,j+1) f(x, y, w) = d^(0,j) H(x, (y, w₀), (w₁, 0), …, (wⱼ, 0))`. -/
theorem ContDiffMBOn₂.zero_succ_of (hV : IsOpen V) (hf0 : ContDiffMBOn₂ 0 0 f U V)
    {H : E₁ × (E₂ × E₂) → F}
    (hH : ∀ x ∈ U, ∀ y ∈ V, ∀ b, HasDirDerivAt (fun y' ↦ f (x, y')) y b (H (x, (y, b))))
    (hHc : ContDiffMBOn₂ 0 ℓ H U (V ×ˢ univ)) :
    ContDiffMBOn₂ 0 (ℓ + 1) f U V ∧ ∀ j, j ≤ ℓ → ∀ x ∈ U, ∀ y ∈ V, ∀ w : Fin (j + 1) → E₂,
      iteratedDMB (j + 1) (fun y' ↦ f (x, y')) (y, w) =
        iteratedDMB j (fun yb ↦ H (x, yb)) ((y, w 0), fun t ↦ (w t.succ, 0)) := by
  have hdH : ∀ x ∈ U, ∀ y ∈ V, ∀ b, dMB (fun y' ↦ f (x, y')) (y, b) = H (x, (y, b)) :=
    fun x hx y hy b ↦ (hH x hx y hy b).dMB_eq
  have hform : ∀ j, j ≤ ℓ → ∀ x ∈ U, ∀ y ∈ V, ∀ w : Fin (j + 1) → E₂,
      iteratedDMB (j + 1) (fun y' ↦ f (x, y')) (y, w) =
        iteratedDMB j (fun yb ↦ H (x, yb)) ((y, w 0), fun t ↦ (w t.succ, 0)) := by
    intro j hj x hx y hy w
    rw [iteratedDMB_succ_eq_dMB]
    exact iteratedDMB_congr_of_eventuallyEq j (Filter.eventually_of_mem
      ((hV.prod isOpen_univ).mem_nhds (show (y, w 0) ∈ V ×ˢ (univ : Set E₂) from
        ⟨hy, mem_univ _⟩)) fun yb hyb ↦ hdH x hx yb.1 hyb.1 yb.2) _
  refine ⟨⟨fun x hx ↦ ⟨hf0.contDiffMBOn_right x hx, fun y hy b ↦ ?_, ?_⟩,
    fun j hj y hy w ↦ ?_, fun i hi j hj ↦ ?_⟩, hform⟩
  · rw [hdH x hx y hy b]
    exact hH x hx y hy b
  · exact ContDiffMBOn.congr_of_isOpen (hV.prod isOpen_univ)
      (fun yb hyb ↦ (hdH x hx yb.1 hyb.1 yb.2).symm) (hHc.contDiffMBOn_right x hx)
  · cases j with
    | zero => exact hf0.contDiffMBOn_left 0 le_rfl y hy w
    | succ j =>
      exact ContinuousOn.congr (hHc.contDiffMBOn_left j (by omega) (y, w 0) ⟨hy, mem_univ _⟩
        fun t ↦ (w t.succ, 0)) fun x hx ↦ hform j (by omega) x hx y hy w
  · obtain rfl : i = 0 := by omega
    cases j with
    | zero => exact hf0.continuousOn 0 le_rfl 0 le_rfl
    | succ j =>
      refine ((hHc.continuousOn 0 le_rfl j (by omega)).comp
        (f := fun p : (E₁ × E₂) × (Fin 0 → E₁) × (Fin (j + 1) → E₂) ↦
          ((p.1.1, (p.1.2, p.2.2 0)), p.2.1, (fun t ↦ (p.2.2 t.succ, 0) : Fin j → E₂ × E₂)))
        (by fun_prop) fun p (hp : p ∈ ((U ×ˢ V : Set (E₁ × E₂)) ×ˢ
          (univ : Set ((Fin 0 → E₁) × (Fin (j + 1) → E₂))))) ↦
          ⟨⟨hp.1.1, ⟨hp.1.2, mem_univ _⟩⟩, mem_univ _⟩).congr
        fun p hp ↦ ?_
      exact hform j (by omega) p.1.1 hp.1.1 p.1.2 hp.1.2 p.2.2

end OpenPartials

/-! ### Recursive characterization on sets with dense interior -/

section DensePartials

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

/-- The first partial differential `((x, a), y) ↦ d^(1,0) f(x, y, a)` on `(U × E₁) × V`. -/
def partialDLC₁ (f : E₁ × E₂ → F) (U : Set E₁) (V : Set E₂) (p : (E₁ × E₁) × E₂) : F :=
  iteratedDLC₂ 1 0 f U V ((p.1.1, p.2), fun _ ↦ p.1.2, Fin.elim0)

/-- The second partial differential `(x, (y, b)) ↦ d^(0,1) f(x, y, b)` on `U × (V × E₂)`. -/
def partialDLC₂ (f : E₁ × E₂ → F) (U : Set E₁) (V : Set E₂) (p : E₁ × (E₂ × E₂)) : F :=
  iteratedDLC₂ 0 1 f U V ((p.1, p.2.1), Fin.elim0, fun _ ↦ p.2.2)

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- On `U⁰ × V⁰`, `partialDLC₁ f U V` is `d^(1,0) f`. -/
theorem partialDLC₁_eqOn_interior :
    EqOn (partialDLC₁ f U V) (partialD₁ f) ((interior U ×ˢ univ) ×ˢ interior V) :=
  fun p hp ↦ iteratedDLC₂_eqOn_interior 1 0 f U V (x := ((p.1.1, p.2), _, _))
    ⟨⟨hp.1.1, hp.2⟩, mem_univ _⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- On `U⁰ × V⁰`, `partialDLC₂ f U V` is `d^(0,1) f`. -/
theorem partialDLC₂_eqOn_interior :
    EqOn (partialDLC₂ f U V) (partialD₂ f) (interior U ×ˢ (interior V ×ˢ univ)) :=
  fun p hp ↦ iteratedDLC₂_eqOn_interior 0 1 f U V (x := ((p.1, p.2.1), _, _))
    ⟨⟨hp.1, hp.2.1⟩, mem_univ _⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `partialDLC₁ f U V` is the derivative of `f` in the first variable on `U⁰ × V⁰`. -/
theorem ContDiffLC₂.hasDirDerivAt_partialDLC₁ (hf : ContDiffLC₂ (k + 1) ℓ f U V) {x : E₁}
    (hx : x ∈ interior U) {y : E₂} (hy : y ∈ interior V) (a : E₁) :
    HasDirDerivAt (fun x' ↦ f (x', y)) x a (partialDLC₁ f U V ((x, a), y)) := by
  rw [partialDLC₁_eqOn_interior ⟨⟨hx, mem_univ _⟩, hy⟩]
  exact hf.2.1.hasDirDerivAt_left (i := 0) (j := 0) (Nat.succ_pos k) (Nat.zero_le ℓ) hx hy
    (fun _ ↦ a) Fin.elim0

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `partialDLC₂ f U V` is the derivative of `f` in the second variable on `U⁰ × V⁰`. -/
theorem ContDiffLC₂.hasDirDerivAt_partialDLC₂ (hf : ContDiffLC₂ k (ℓ + 1) f U V) {x : E₁}
    (hx : x ∈ interior U) {y : E₂} (hy : y ∈ interior V) (b : E₂) :
    HasDirDerivAt (fun y' ↦ f (x, y')) y b (partialDLC₂ f U V (x, (y, b))) := by
  rw [partialDLC₂_eqOn_interior ⟨hx, ⟨hy, mem_univ _⟩⟩]
  exact (hf.2.1.contDiffMBOn_right x hx).2.1 y hy b

/-- **Recursion in the first variable** (`→`): if `f` is `C^{k+1,ℓ}` on `U × V`, then its first
partial differential `((x, a), y) ↦ d^(1,0) f(x, y, a)` is `C^{k,ℓ}` on `(U × E₁) × V`. -/
theorem ContDiffLC₂.contDiffLC₂_partialDLC₁ (hf : ContDiffLC₂ (k + 1) ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) :
    ContDiffLC₂ k ℓ (partialDLC₁ f U V) (U ×ˢ univ) V := by
  have hint : interior (U ×ˢ (univ : Set E₁)) = interior U ×ˢ univ := by
    rw [interior_prod_eq, interior_univ]
  have hO := contDiffMBOn₂_partialD₁ isOpen_interior isOpen_interior hf.2.1
  have hc := fun i (hi : i ≤ k + 1) j (hj : j ≤ ℓ) ↦ hf.continuousOn_iteratedDLC₂ hU hV hi hj
  refine ⟨?_, ?_, fun i hi j hj ↦ ⟨fun q ↦ iteratedDLC₂ (i + 1) j f U V
    ((q.1.1.1, q.1.2), Fin.cons q.1.1.2 fun s ↦ (q.2.1 s).1, q.2.2) +
      ∑ s, iteratedDLC₂ i j f U V
        ((q.1.1.1, q.1.2), update (fun s ↦ (q.2.1 s).1) s (q.2.1 s).2, q.2.2), ?_, ?_⟩⟩
  · exact (hc 1 (by omega) 0 (Nat.zero_le ℓ)).comp
      (f := fun p : (E₁ × E₁) × E₂ ↦ ((p.1.1, p.2), (fun _ ↦ p.1.2 : Fin 1 → E₁),
        (Fin.elim0 : Fin 0 → E₂))) (by fun_prop) fun p hp ↦ ⟨⟨hp.1.1, hp.2⟩, mem_univ _⟩
  · rw [hint]
    exact hO.congr (isOpen_interior.prod isOpen_univ) isOpen_interior
      fun p hp ↦ (partialDLC₁_eqOn_interior hp).symm
  · refine ContinuousOn.add ((hc (i + 1) (by omega) j hj).comp (by fun_prop)
      fun q hq ↦ ⟨⟨hq.1.1.1, hq.1.2⟩, mem_univ _⟩)
      (continuousOn_finsetSum _ fun s _ ↦ (hc i (by omega) j hj).comp (by fun_prop)
        fun q hq ↦ ⟨⟨hq.1.1.1, hq.1.2⟩, mem_univ _⟩)
  · rintro ⟨⟨⟨x, a⟩, y⟩, vv, w⟩ ⟨⟨hxa, hy⟩, -⟩
    rw [hint] at hxa
    rw [iteratedDMB₂_congr (isOpen_interior.prod isOpen_univ) isOpen_interior
      (fun p hp ↦ partialDLC₁_eqOn_interior hp) i j hxa hy vv w,
      iteratedDMB₂_partialD₁ isOpen_interior isOpen_interior hf.2.1 hi hj hxa.1 hy vv w]
    simp only
    rw [iteratedDLC₂_eqOn_interior _ _ _ _ _ (show ((x, y), _, w) ∈ _ from
      ⟨⟨hxa.1, hy⟩, mem_univ _⟩)]
    congr 1
    exact Finset.sum_congr rfl fun s _ ↦ iteratedDLC₂_eqOn_interior _ _ _ _ _
      (show ((x, y), _, w) ∈ _ from ⟨⟨hxa.1, hy⟩, mem_univ _⟩)

omit [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The mixed differentials of the first partial differential `d^(1,0) f`, on all of
`(U × E₁) × V`: `d^(i,j)(d^(1,0) f)((x, a), y, (v, b), w)` equals
`d^(i+1,j) f(x, y, (a, v), w) + ∑ₛ d^(i,j) f(x, y, v with bₛ in place of vₛ, w)`. -/
theorem ContDiffLC₂.iteratedDLC₂_partialDLC₁ (hf : ContDiffLC₂ (k + 1) ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ) :
    EqOn (iteratedDLC₂ i j (partialDLC₁ f U V) (U ×ˢ univ) V) (fun q ↦ iteratedDLC₂ (i + 1) j f U V
      ((q.1.1.1, q.1.2), Fin.cons q.1.1.2 fun s ↦ (q.2.1 s).1, q.2.2) +
        ∑ s, iteratedDLC₂ i j f U V
          ((q.1.1.1, q.1.2), update (fun s ↦ (q.2.1 s).1) s (q.2.1 s).2, q.2.2))
      (((U ×ˢ univ) ×ˢ V) ×ˢ univ) := by
  have hint : interior (U ×ˢ (univ : Set E₁)) = interior U ×ˢ univ := by
    rw [interior_prod_eq, interior_univ]
  have hc := fun i (hi : i ≤ k + 1) j (hj : j ≤ ℓ) ↦ hf.continuousOn_iteratedDLC₂ hU hV hi hj
  refine iteratedDLC₂_eqOn_of_continuousOn hU.prod_univ hV ?_ ?_
  · exact ContinuousOn.add ((hc (i + 1) (by omega) j hj).comp (by fun_prop)
      fun q hq ↦ ⟨⟨hq.1.1.1, hq.1.2⟩, mem_univ _⟩)
      (continuousOn_finsetSum _ fun s _ ↦ (hc i (by omega) j hj).comp (by fun_prop)
        fun q hq ↦ ⟨⟨hq.1.1.1, hq.1.2⟩, mem_univ _⟩)
  · rintro ⟨⟨⟨x, a⟩, y⟩, vv, w⟩ ⟨⟨hxa, hy⟩, -⟩
    rw [hint] at hxa
    rw [iteratedDMB₂_congr (isOpen_interior.prod isOpen_univ) isOpen_interior
      (fun p hp ↦ partialDLC₁_eqOn_interior hp) i j hxa hy vv w,
      iteratedDMB₂_partialD₁ isOpen_interior isOpen_interior hf.2.1 hi hj hxa.1 hy vv w]
    simp only
    rw [iteratedDLC₂_eqOn_interior _ _ _ _ _ (show ((x, y), _, w) ∈ _ from
      ⟨⟨hxa.1, hy⟩, mem_univ _⟩)]
    congr 1
    exact Finset.sum_congr rfl fun s _ ↦ iteratedDLC₂_eqOn_interior _ _ _ _ _
      (show ((x, y), _, w) ∈ _ from ⟨⟨hxa.1, hy⟩, mem_univ _⟩)

omit [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- `d^(0,j)(d^(1,0) f)((x, a), y, w) = d^(1,j) f(x, y, a, w)` on `(U × E₁) × V × E₂^j`. -/
theorem ContDiffLC₂.iteratedDLC₂_zero_partialDLC₁ (hf : ContDiffLC₂ (k + 1) ℓ f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) {j : ℕ} (hj : j ≤ ℓ) {x a : E₁}
    (hx : x ∈ U) {y : E₂} (hy : y ∈ V) (v : Fin 0 → E₁ × E₁) (w : Fin j → E₂) :
    iteratedDLC₂ 0 j (partialDLC₁ f U V) (U ×ˢ univ) V (((x, a), y), v, w) =
      iteratedDLC₂ 1 j f U V ((x, y), fun _ ↦ a, w) := by
  rw [hf.iteratedDLC₂_partialDLC₁ hU hV (Nat.zero_le k) hj
    (show (((x, a), y), v, w) ∈ _ from ⟨⟨⟨hx, mem_univ _⟩, hy⟩, mem_univ _⟩)]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  congr 3
  funext s
  exact Fin.cases rfl (fun i ↦ i.elim0) s

/-- **Recursion in the second variable** (`→`, for `k = 0`): if `f` is `C^{0,ℓ+1}` on `U × V`,
then its second partial differential `(x, (y, b)) ↦ d^(0,1) f(x, y, b)` is `C^{0,ℓ}` on
`U × (V × E₂)`. -/
theorem ContDiffLC₂.contDiffLC₂_partialDLC₂ (hf : ContDiffLC₂ 0 (ℓ + 1) f U V)
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) :
    ContDiffLC₂ 0 ℓ (partialDLC₂ f U V) U (V ×ˢ univ) := by
  have hint : interior (V ×ˢ (univ : Set E₂)) = interior V ×ˢ univ := by
    rw [interior_prod_eq, interior_univ]
  have hO := contDiffMBOn₂_partialD₂ isOpen_interior hf.2.1
  have hc := fun i (hi : i ≤ 0) j (hj : j ≤ ℓ + 1) ↦ hf.continuousOn_iteratedDLC₂ hU hV hi hj
  refine ⟨?_, ?_, fun i hi j hj ↦ ?_⟩
  · exact (hc 0 le_rfl 1 (by omega)).comp
      (f := fun p : E₁ × (E₂ × E₂) ↦ ((p.1, p.2.1), (Fin.elim0 : Fin 0 → E₁),
        (fun _ ↦ p.2.2 : Fin 1 → E₂))) (by fun_prop) fun p hp ↦ ⟨⟨hp.1, hp.2.1⟩, mem_univ _⟩
  · rw [hint]
    exact hO.congr isOpen_interior (isOpen_interior.prod isOpen_univ)
      fun p hp ↦ (partialDLC₂_eqOn_interior hp).symm
  obtain rfl : i = 0 := by omega
  refine ⟨fun q ↦ iteratedDLC₂ 0 (j + 1) f U V
    ((q.1.1, q.1.2.1), q.2.1, Fin.cons q.1.2.2 fun t ↦ (q.2.2 t).1) +
      ∑ t, iteratedDLC₂ 0 j f U V
        ((q.1.1, q.1.2.1), q.2.1, update (fun t ↦ (q.2.2 t).1) t (q.2.2 t).2), ?_, ?_⟩
  · refine ContinuousOn.add ((hc 0 le_rfl (j + 1) (by omega)).comp (by fun_prop)
      fun q hq ↦ ⟨⟨hq.1.1, hq.1.2.1⟩, mem_univ _⟩)
      (continuousOn_finsetSum _ fun t _ ↦ (hc 0 le_rfl j (by omega)).comp (by fun_prop)
        fun q hq ↦ ⟨⟨hq.1.1, hq.1.2.1⟩, mem_univ _⟩)
  · rintro ⟨⟨x, ⟨y, b⟩⟩, v, ww⟩ ⟨⟨hx, hyb⟩, -⟩
    rw [hint] at hyb
    rw [iteratedDMB₂_congr isOpen_interior (isOpen_interior.prod isOpen_univ)
      (fun p hp ↦ partialDLC₂_eqOn_interior hp) 0 j hx hyb v ww]
    change _ = iteratedDMB j (fun yb ↦ partialD₂ f (x, yb)) ((y, b), ww)
    rw [iteratedDMB_partialD₂_right isOpen_interior hf.2.1 hj hx hyb.1 b ww]
    simp only
    rw [iteratedDLC₂_eqOn_interior _ _ _ _ _ (show ((x, y), v, _) ∈ _ from
      ⟨⟨hx, hyb.1⟩, mem_univ _⟩)]
    congr 1
    exact Finset.sum_congr rfl fun t _ ↦ iteratedDLC₂_eqOn_interior _ _ _ _ _
      (show ((x, y), v, _) ∈ _ from ⟨⟨hx, hyb.1⟩, mem_univ _⟩)

omit [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **Recursion in the first variable** (`←`): if `f` is `C^{0,ℓ}` on `U × V` and its derivative
in the first variable on `U⁰ × V⁰` is given by a map `G` that is `C^{k,ℓ}` on `(U × E₁) × V`,
then `f` is `C^{k+1,ℓ}`. -/
theorem ContDiffLC₂.succ_of (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf0 : ContDiffLC₂ 0 ℓ f U V) {G : (E₁ × E₁) × E₂ → F}
    (hG : ∀ x ∈ interior U, ∀ y ∈ interior V, ∀ a,
      HasDirDerivAt (fun x' ↦ f (x', y)) x a (G ((x, a), y)))
    (hGc : ContDiffLC₂ k ℓ G (U ×ˢ univ) V) : ContDiffLC₂ (k + 1) ℓ f U V := by
  have hint : interior (U ×ˢ (univ : Set E₁)) = interior U ×ˢ univ := by
    rw [interior_prod_eq, interior_univ]
  have hGc' := hGc.2.1
  rw [hint] at hGc'
  obtain ⟨hO, hform⟩ := ContDiffMBOn₂.succ_of isOpen_interior isOpen_interior hf0.2.1 hG hGc'
  refine ContDiffLC₂.of_continuousOn_iteratedDLC₂ hf0.1 hO fun i hi j hj ↦ ?_
  cases i with
  | zero => exact hf0.continuousOn_iteratedDLC₂ hU hV le_rfl hj
  | succ i =>
    have hc : ContinuousOn (fun p : (E₁ × E₂) × (Fin (i + 1) → E₁) × (Fin j → E₂) ↦
        iteratedDLC₂ i j G (U ×ˢ univ) V (((p.1.1, p.2.1 0), p.1.2),
          (fun s ↦ (p.2.1 s.succ, 0) : Fin i → E₁ × E₁), p.2.2)) ((U ×ˢ V) ×ˢ univ) :=
      (hGc.continuousOn_iteratedDLC₂ hU.prod_univ hV (by omega) hj).comp (by fun_prop)
        fun p hp ↦ ⟨⟨⟨hp.1.1, mem_univ _⟩, hp.1.2⟩, mem_univ _⟩
    refine hc.congr (iteratedDLC₂_eqOn_of_continuousOn hU hV hc ?_)
    rintro ⟨⟨x, y⟩, v, w⟩ ⟨⟨hx, hy⟩, -⟩
    rw [hform i j hj x hx y hy v w]
    exact iteratedDLC₂_eqOn_interior _ _ _ _ _
      ⟨⟨by rw [hint]; exact ⟨hx, mem_univ _⟩, hy⟩, mem_univ _⟩

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- **Recursion in the second variable** (`←`, for `k = 0`): if `f` is continuous on `U × V` and
its derivative in the second variable on `U⁰ × V⁰` is given by a map `H` that is `C^{0,ℓ}` on
`U × (V × E₂)`, then `f` is `C^{0,ℓ+1}`. -/
theorem ContDiffLC₂.zero_succ_of (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf0 : ContDiffLC₂ 0 0 f U V) {H : E₁ × (E₂ × E₂) → F}
    (hH : ∀ x ∈ interior U, ∀ y ∈ interior V, ∀ b,
      HasDirDerivAt (fun y' ↦ f (x, y')) y b (H (x, (y, b))))
    (hHc : ContDiffLC₂ 0 ℓ H U (V ×ˢ univ)) : ContDiffLC₂ 0 (ℓ + 1) f U V := by
  have hint : interior (V ×ˢ (univ : Set E₂)) = interior V ×ˢ univ := by
    rw [interior_prod_eq, interior_univ]
  have hHc' := hHc.2.1
  rw [hint] at hHc'
  obtain ⟨hO, hform⟩ := ContDiffMBOn₂.zero_succ_of isOpen_interior hf0.2.1 hH hHc'
  refine ContDiffLC₂.of_continuousOn_iteratedDLC₂ hf0.1 hO fun i hi j hj ↦ ?_
  obtain rfl : i = 0 := by omega
  cases j with
  | zero => exact hf0.continuousOn_iteratedDLC₂ hU hV le_rfl le_rfl
  | succ j =>
    have hc : ContinuousOn (fun p : (E₁ × E₂) × (Fin 0 → E₁) × (Fin (j + 1) → E₂) ↦
        iteratedDLC₂ 0 j H U (V ×ˢ univ) ((p.1.1, (p.1.2, p.2.2 0)), p.2.1,
          (fun t ↦ (p.2.2 t.succ, 0) : Fin j → E₂ × E₂))) ((U ×ˢ V) ×ˢ univ) :=
      (hHc.continuousOn_iteratedDLC₂ hU hV.prod_univ le_rfl (by omega)).comp (by fun_prop)
        fun p hp ↦ ⟨⟨hp.1.1, ⟨hp.1.2, mem_univ _⟩⟩, mem_univ _⟩
    refine hc.congr (iteratedDLC₂_eqOn_of_continuousOn hU hV hc ?_)
    rintro ⟨⟨x, y⟩, v, w⟩ ⟨⟨hx, hy⟩, -⟩
    change _ = iteratedDMB (j + 1) (fun y' ↦ f (x, y')) (y, w)
    rw [hform j (by omega) x hx y hy w]
    exact iteratedDLC₂_eqOn_interior _ _ _ _ _
      ⟨⟨hx, by rw [hint]; exact ⟨hy, mem_univ _⟩⟩, mem_univ _⟩

end DensePartials

/-! ### Monotonicity, congruence, linear maps and products -/

section Rules

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `C^{k,ℓ}` maps are `C^{k',ℓ'}` for `k' ≤ k`, `ℓ' ≤ ℓ`. -/
theorem ContDiffLC₂.of_le {k' ℓ' : ℕ} (hf : ContDiffLC₂ k ℓ f U V) (hk : k' ≤ k)
    (hl : ℓ' ≤ ℓ) : ContDiffLC₂ k' ℓ' f U V :=
  ⟨hf.1, ⟨fun x hx ↦ (hf.2.1.contDiffMBOn_right x hx).of_le hl,
    fun j hj y hy w ↦ (hf.2.1.contDiffMBOn_left j (hj.trans hl) y hy w).of_le hk,
    fun i hi j hj ↦ hf.2.1.continuousOn i (hi.trans hk) j (hj.trans hl)⟩,
    fun i hi j hj ↦ hf.2.2 i (hi.trans hk) j (hj.trans hl)⟩

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- `C^{k,ℓ}` only depends on the values on `U × V`. -/
theorem ContDiffLC₂.congr {g : E₁ × E₂ → F} (hf : ContDiffLC₂ k ℓ f U V)
    (h : EqOn f g (U ×ˢ V)) : ContDiffLC₂ k ℓ g U V := by
  have h' : EqOn f g (interior U ×ˢ interior V) :=
    h.mono (prod_mono interior_subset interior_subset)
  refine ⟨hf.1.congr h.symm, hf.2.1.congr isOpen_interior isOpen_interior h',
    fun i hi j hj ↦ ?_⟩
  obtain ⟨D, hDc, hDe⟩ := hf.2.2 i hi j hj
  exact ⟨D, hDc, fun p hp ↦ (hDe hp).trans
    (iteratedDMB₂_congr isOpen_interior isOpen_interior h' i j hp.1.1 hp.1.2 p.2.1 p.2.2)⟩

omit [IsTopologicalAddGroup G] [LocallyConvexSpace ℝ G] in
/-- Composition with a continuous linear map, in the case `k = 0`. -/
theorem ContDiffLC₂.clm_comp_zero (L : F →L[ℝ] G) {ℓ : ℕ} {f : E₁ × E₂ → F}
    {V : Set E₂} (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    (hf : ContDiffLC₂ 0 ℓ f U V) : ContDiffLC₂ 0 ℓ (fun p ↦ L (f p)) U V := by
  induction ℓ generalizing E₂ f V with
  | zero => exact contDiffLC₂_zero_zero_iff.2 (L.continuous.comp_continuousOn hf.1)
  | succ ℓ ih =>
    exact ContDiffLC₂.zero_succ_of hU hV
      (contDiffLC₂_zero_zero_iff.2 (L.continuous.comp_continuousOn hf.1))
      (H := fun q ↦ L (partialDLC₂ f U V q))
      (fun x hx y hy b ↦ (hf.hasDirDerivAt_partialDLC₂ hx hy b).clm_comp_real L)
      (ih hV.prod_univ (hf.contDiffLC₂_partialDLC₂ hU hV))

/-- Composition with a continuous linear map preserves `C^{k,ℓ}`. -/
theorem ContDiffLC₂.clm_comp (L : F →L[ℝ] G) {k : ℕ} {f : E₁ × E₂ → F} {U : Set E₁}
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) (hf : ContDiffLC₂ k ℓ f U V) :
    ContDiffLC₂ k ℓ (fun p ↦ L (f p)) U V := by
  induction k generalizing E₁ f U with
  | zero => exact hf.clm_comp_zero L hU hV
  | succ k ih =>
    exact ContDiffLC₂.succ_of hU hV
      ((hf.of_le (Nat.zero_le _) le_rfl).clm_comp_zero L hU hV)
      (G := fun q ↦ L (partialDLC₁ f U V q))
      (fun x hx y hy a ↦ (hf.hasDirDerivAt_partialDLC₁ hx hy a).clm_comp_real L)
      (ih hU.prod_univ (hf.contDiffLC₂_partialDLC₁ hU hV))

/-- Pairs of `C^{0,ℓ}` maps. -/
theorem ContDiffLC₂.prodMk_zero {ℓ : ℕ} {f : E₁ × E₂ → F} {g : E₁ × E₂ → G} {V : Set E₂}
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) (hf : ContDiffLC₂ 0 ℓ f U V)
    (hg : ContDiffLC₂ 0 ℓ g U V) : ContDiffLC₂ 0 ℓ (fun p ↦ (f p, g p)) U V := by
  induction ℓ generalizing E₂ f g V with
  | zero => exact contDiffLC₂_zero_zero_iff.2 (hf.1.prodMk hg.1)
  | succ ℓ ih =>
    exact ContDiffLC₂.zero_succ_of hU hV (contDiffLC₂_zero_zero_iff.2 (hf.1.prodMk hg.1))
      (H := fun q ↦ (partialDLC₂ f U V q, partialDLC₂ g U V q))
      (fun x hx y hy b ↦ (hf.hasDirDerivAt_partialDLC₂ hx hy b).prodMk
        (hg.hasDirDerivAt_partialDLC₂ hx hy b))
      (ih hV.prod_univ (hf.contDiffLC₂_partialDLC₂ hU hV) (hg.contDiffLC₂_partialDLC₂ hU hV))

/-- Pairs of `C^{k,ℓ}` maps are `C^{k,ℓ}` ([GN26, Proposition 1.7.20]). -/
theorem ContDiffLC₂.prodMk {k : ℕ} {f : E₁ × E₂ → F} {g : E₁ × E₂ → G} {U : Set E₁}
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) (hf : ContDiffLC₂ k ℓ f U V)
    (hg : ContDiffLC₂ k ℓ g U V) : ContDiffLC₂ k ℓ (fun p ↦ (f p, g p)) U V := by
  induction k generalizing E₁ f g U with
  | zero => exact hf.prodMk_zero hU hV hg
  | succ k ih =>
    exact ContDiffLC₂.succ_of hU hV
      ((hf.of_le (Nat.zero_le _) le_rfl).prodMk_zero hU hV (hg.of_le (Nat.zero_le _) le_rfl))
      (G := fun q ↦ (partialDLC₁ f U V q, partialDLC₁ g U V q))
      (fun x hx y hy a ↦ (hf.hasDirDerivAt_partialDLC₁ hx hy a).prodMk
        (hg.hasDirDerivAt_partialDLC₁ hx hy a))
      (ih hU.prod_univ (hf.contDiffLC₂_partialDLC₁ hU hV) (hg.contDiffLC₂_partialDLC₁ hU hV))

/-- **[GN26, Proposition 1.7.20]** (p. 95), for two factors: a map into `F × G` is
`C^{k,ℓ}` if and only if both components are. -/
theorem contDiffLC₂_prodMk_iff {g : E₁ × E₂ → G} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) :
    ContDiffLC₂ k ℓ (fun p ↦ (f p, g p)) U V ↔ ContDiffLC₂ k ℓ f U V ∧ ContDiffLC₂ k ℓ g U V :=
  ⟨fun h ↦ ⟨(h.clm_comp (ContinuousLinearMap.fst ℝ F G) hU hV).congr fun _ _ ↦ rfl,
    (h.clm_comp (ContinuousLinearMap.snd ℝ F G) hU hV).congr fun _ _ ↦ rfl⟩,
    fun h ↦ h.1.prodMk hU hV h.2⟩

end Rules

/-! ### The chain rules -/

section Chain

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F₁ : Type u} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [LocallyConvexSpace ℝ F₁] [T2Space F₁]
  {F₂ : Type u} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [LocallyConvexSpace ℝ F₂] [T2Space F₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- `(x, a) ↦ f x` is `C^k` on `U × E` if `f` is `C^k` on `U`. -/
theorem ContDiffLC.comp_fst {k : ℕ} {f : E₁ → F} {U : Set E₁} (hU : HasDenseInterior U)
    (hf : ContDiffLC k f U) : ContDiffLC k (fun q : E₁ × E₁ ↦ f q.1) (U ×ˢ univ) := by
  have h := ContDiffLC.comp_clm_of_isOpenMap (ContinuousLinearMap.fst ℝ E₁ E₁)
    (by rw [ContinuousLinearMap.coe_fst']; exact isOpenMap_fst) hU hf
  rwa [show (ContinuousLinearMap.fst ℝ E₁ E₁) ⁻¹' U = U ×ˢ univ by ext; simp] at h

omit [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- The partial map `x ↦ f(x, y)` of a `C^{k+1,ℓ}` map, also for `y` on the boundary, is
`C^{k+1}`, with differential `d^(1,0) f(·, y, ·)` ([GN26, Remark 1.7.19(b)]). -/
theorem ContDiffLC₂.dLC_left {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}
    (hf : ContDiffLC₂ (k + 1) ℓ f U V) (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    {y : E₂} (hy : y ∈ V) : ContDiffLC (k + 1) (fun x ↦ f (x, y)) U ∧
      EqOn (dLC (fun x ↦ f (x, y)) U) (fun q ↦ partialDLC₁ f U V (q, y)) (U ×ˢ univ) := by
  have hD0 : EqOn (iteratedDLC₂ 0 0 f U V) (fun p ↦ f p.1) ((U ×ˢ V) ×ˢ univ) :=
    iteratedDLC₂_eqOn_of_continuousOn hU hV (hf.1.comp continuous_fst.continuousOn
      fun p hp ↦ hp.1) fun _ _ ↦ rfl
  obtain ⟨h1, h2⟩ := hf.contDiffLC_left hU hV (Nat.zero_le ℓ) hy Fin.elim0
    (hf.continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) (Nat.zero_le _))
    (iteratedDLC₂_eqOn_interior 0 0 f U V)
  have heq : EqOn (fun x ↦ iteratedDLC₂ 0 0 f U V ((x, y), Fin.elim0, Fin.elim0))
      (fun x ↦ f (x, y)) U := fun x hx ↦ hD0 (show ((x, y), _, _) ∈ _ from ⟨⟨hx, hy⟩, mem_univ _⟩)
  refine ⟨h1.congr heq, fun q hq ↦ ?_⟩
  rw [← dLC_congr (heq.mono interior_subset)]
  exact h2 1 (by omega) _ (hf.continuousOn_iteratedDLC₂ hU hV (by omega) (Nat.zero_le _))
    (iteratedDLC₂_eqOn_interior 1 0 f U V) (show (q.1, fun _ ↦ q.2) ∈ _ from ⟨hq.1, mem_univ _⟩)

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- The partial map `y ↦ f(x, y)` of a `C^{k,ℓ+1}` map is `C^{ℓ+1}`, with differential
`d^(0,1) f(x, ·, ·)` ([GN26, Lemma 1.7.18]). -/
theorem ContDiffLC₂.dLC_right {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}
    (hf : ContDiffLC₂ k (ℓ + 1) f U V) (hU : HasDenseInterior U) (hV : HasDenseInterior V)
    {x : E₁} (hx : x ∈ U) : ContDiffLC (ℓ + 1) (fun y ↦ f (x, y)) V ∧
      EqOn (dLC (fun y ↦ f (x, y)) V) (fun q ↦ partialDLC₂ f U V (x, q)) (V ×ˢ univ) := by
  obtain ⟨h1, h2⟩ := hf.contDiffLC_right hU hV hx
  refine ⟨h1, fun q hq ↦ ?_⟩
  exact h2 1 (by omega) _ (hf.continuousOn_iteratedDLC₂ hU hV (Nat.zero_le _) (by omega))
    (iteratedDLC₂_eqOn_interior 0 1 f U V) (show (q.1, fun _ ↦ q.2) ∈ _ from ⟨hq.1, mem_univ _⟩)

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- Chain rule 1 for `C^{0,s}` maps. -/
theorem ContDiffLC₂.comp_prodMap_zero {s : ℕ} {g : F₁ × F₂ → F} {f₁ : E₁ → F₁} {f₂ : E₂ → F₂}
    {U₁ : Set E₁} {U₂ : Set E₂} {V₁ : Set F₁} {V₂ : Set F₂} (hU₁ : HasDenseInterior U₁)
    (hU₂ : HasDenseInterior U₂) (hV₁ : HasDenseInterior V₁) (hV₂c : IsLocallyConvexSubset V₂)
    (hV₂ : HasDenseInterior V₂) (hg : ContDiffLC₂ 0 s g V₁ V₂) (hf₁ : ContinuousOn f₁ U₁)
    (hf₂ : ContDiffLC s f₂ U₂) (h₁ : MapsTo f₁ U₁ V₁) (h₂ : MapsTo f₂ U₂ V₂) :
    ContDiffLC₂ 0 s (fun p ↦ g (f₁ p.1, f₂ p.2)) U₁ U₂ := by
  have hc : ContinuousOn (fun p : E₁ × E₂ ↦ g (f₁ p.1, f₂ p.2)) (U₁ ×ˢ U₂) :=
    hg.1.comp ((hf₁.comp continuousOn_fst fun (p : E₁ × E₂) (hp : p ∈ U₁ ×ˢ U₂) ↦ hp.1).prodMk
      (hf₂.continuousOn.comp continuousOn_snd fun (p : E₁ × E₂) (hp : p ∈ U₁ ×ˢ U₂) ↦ hp.2))
      fun p hp ↦ ⟨h₁ hp.1, h₂ hp.2⟩
  induction s generalizing E₂ F₂ g f₂ U₂ V₂ with
  | zero => exact contDiffLC₂_zero_zero_iff.2 hc
  | succ s ih =>
    refine ContDiffLC₂.zero_succ_of hU₁ hU₂ (contDiffLC₂_zero_zero_iff.2 hc)
      (H := fun q ↦ partialDLC₂ g V₁ V₂ (f₁ q.1, (f₂ q.2.1, dLC f₂ U₂ q.2)))
      (fun x hx y hy b ↦ ?_) ?_
    · obtain ⟨hgz, hdgz⟩ := hg.dLC_right hV₁ hV₂ (h₁ (interior_subset hx))
      obtain ⟨hcomp, hdcomp⟩ := ContDiffLC.comp_one hU₂ hV₂c hV₂ (hgz.of_le (by omega))
        (hf₂.of_le (by omega)) h₂
      have hd := hcomp.2.1 y hy b
      rw [← dLC_of_mem_interior _ (p := (y, b)) hy, hdcomp ⟨interior_subset hy, mem_univ _⟩]
        at hd
      beta_reduce at hd
      rw [hdgz (show (f₂ y, dLC f₂ U₂ (y, b)) ∈ V₂ ×ˢ univ from
        ⟨h₂ (interior_subset hy), mem_univ _⟩)] at hd
      exact hd
    · have hf₂' : ContDiffLC s (fun q : E₂ × E₂ ↦ (f₂ q.1, dLC f₂ U₂ q)) (U₂ ×ˢ univ) :=
        ContDiffLC.prodMk hU₂.prod_univ ((hf₂.of_le (by omega)).comp_fst hU₂) hf₂.contDiffLC_dLC
      have hc' : ContinuousOn (fun p : E₁ × (E₂ × E₂) ↦
          partialDLC₂ g V₁ V₂ (f₁ p.1, (f₂ p.2.1, dLC f₂ U₂ p.2))) (U₁ ×ˢ (U₂ ×ˢ univ)) :=
        (hg.contDiffLC₂_partialDLC₂ hV₁ hV₂).1.comp ((hf₁.comp continuousOn_fst
          fun (p : E₁ × (E₂ × E₂)) (hp : p ∈ U₁ ×ˢ (U₂ ×ˢ univ)) ↦ hp.1).prodMk
          (hf₂'.continuousOn.comp continuousOn_snd
            fun (p : E₁ × (E₂ × E₂)) (hp : p ∈ U₁ ×ˢ (U₂ ×ˢ univ)) ↦ hp.2))
          fun p hp ↦ ⟨h₁ hp.1, h₂ hp.2.1, mem_univ _⟩
      exact ih hU₂.prod_univ (hV₂c.prod isLocallyConvexSubset_univ) hV₂.prod_univ
        (hg.contDiffLC₂_partialDLC₂ hV₁ hV₂) hf₂' (fun q hq ↦ ⟨h₂ hq.1, mem_univ _⟩) hc'

/-- **Chain rule 1 for `C^{r,s}` maps** ([GN26, Proposition 1.7.26, p. 99]): if `g` is
`C^{r,s}` on `V₁ × V₂`, `f₁` is `C^r` on `U₁` and `f₂` is `C^s` on `U₂`, with `f₁(U₁) ⊆ V₁` and
`f₂(U₂) ⊆ V₂`, then `(x, y) ↦ g(f₁ x, f₂ y)` is `C^{r,s}` on `U₁ × U₂`. -/
theorem ContDiffLC₂.comp_prodMap {r s : ℕ} {g : F₁ × F₂ → F} {f₁ : E₁ → F₁} {f₂ : E₂ → F₂}
    {U₁ : Set E₁} {U₂ : Set E₂} {V₁ : Set F₁} {V₂ : Set F₂} (hU₁ : HasDenseInterior U₁)
    (hU₂ : HasDenseInterior U₂) (hV₁c : IsLocallyConvexSubset V₁) (hV₁ : HasDenseInterior V₁)
    (hV₂c : IsLocallyConvexSubset V₂) (hV₂ : HasDenseInterior V₂) (hg : ContDiffLC₂ r s g V₁ V₂)
    (hf₁ : ContDiffLC r f₁ U₁) (hf₂ : ContDiffLC s f₂ U₂) (h₁ : MapsTo f₁ U₁ V₁)
    (h₂ : MapsTo f₂ U₂ V₂) : ContDiffLC₂ r s (fun p ↦ g (f₁ p.1, f₂ p.2)) U₁ U₂ := by
  induction r generalizing E₁ F₁ g f₁ U₁ V₁ with
  | zero => exact hg.comp_prodMap_zero hU₁ hU₂ hV₁ hV₂c hV₂ hf₁.continuousOn hf₂ h₁ h₂
  | succ r ih =>
    refine ContDiffLC₂.succ_of hU₁ hU₂ ((hg.of_le (Nat.zero_le _) le_rfl).comp_prodMap_zero
      hU₁ hU₂ hV₁ hV₂c hV₂ hf₁.continuousOn hf₂ h₁ h₂)
      (G := fun q ↦ partialDLC₁ g V₁ V₂ ((f₁ q.1.1, dLC f₁ U₁ q.1), f₂ q.2))
      (fun x hx y hy a ↦ ?_) ?_
    · obtain ⟨hgz, hdgz⟩ := hg.dLC_left hV₁ hV₂ (h₂ (interior_subset hy))
      obtain ⟨hcomp, hdcomp⟩ := ContDiffLC.comp_one hU₁ hV₁c hV₁ (hgz.of_le (by omega))
        (hf₁.of_le (by omega)) h₁
      have hd := hcomp.2.1 x hx a
      rw [← dLC_of_mem_interior _ (p := (x, a)) hx, hdcomp ⟨interior_subset hx, mem_univ _⟩]
        at hd
      beta_reduce at hd
      rw [hdgz (show (f₁ x, dLC f₁ U₁ (x, a)) ∈ V₁ ×ˢ univ from
        ⟨h₁ (interior_subset hx), mem_univ _⟩)] at hd
      exact hd
    · have hf₁' : ContDiffLC r (fun q : E₁ × E₁ ↦ (f₁ q.1, dLC f₁ U₁ q)) (U₁ ×ˢ univ) :=
        ContDiffLC.prodMk hU₁.prod_univ ((hf₁.of_le (by omega)).comp_fst hU₁) hf₁.contDiffLC_dLC
      exact ih hU₁.prod_univ (hV₁c.prod isLocallyConvexSubset_univ) hV₁.prod_univ
        (hg.contDiffLC₂_partialDLC₁ hV₁ hV₂) hf₁' (fun q hq ↦ ⟨h₁ hq.1, mem_univ _⟩)

/-- Chain rule 2 for `C^{0,s}` maps. -/
theorem ContDiffLC₂.comp_left_zero {s : ℕ} {f : E₁ × E₂ → F₁} {g : F₁ → F} {U : Set E₁}
    {V : Set E₂} {W : Set F₁} (hU : HasDenseInterior U) (hVc : IsLocallyConvexSubset V)
    (hV : HasDenseInterior V) (hWc : IsLocallyConvexSubset W) (hW : HasDenseInterior W)
    (hf : ContDiffLC₂ 0 s f U V) (hg : ContDiffLC s g W) (hfW : MapsTo f (U ×ˢ V) W) :
    ContDiffLC₂ 0 s (fun p ↦ g (f p)) U V := by
  induction s generalizing E₂ F₁ f g V W with
  | zero => exact contDiffLC₂_zero_zero_iff.2 (hg.continuousOn.comp hf.1 hfW)
  | succ s ih =>
    refine ContDiffLC₂.zero_succ_of hU hV
      (contDiffLC₂_zero_zero_iff.2 (hg.continuousOn.comp hf.1 hfW))
      (H := fun q ↦ dLC g W (f (q.1, q.2.1), partialDLC₂ f U V q)) (fun x hx y hy b ↦ ?_) ?_
    · obtain ⟨hfx, hdfx⟩ := hf.dLC_right hU hV (interior_subset hx)
      have hmx : MapsTo (fun y ↦ f (x, y)) V W := fun y hy ↦ hfW ⟨interior_subset hx, hy⟩
      obtain ⟨hcomp, hdcomp⟩ := ContDiffLC.comp_one hV hWc hW (hg.of_le (by omega))
        (hfx.of_le (by omega)) hmx
      have hd := hcomp.2.1 y hy b
      rw [← dLC_of_mem_interior _ (p := (y, b)) hy, hdcomp ⟨interior_subset hy, mem_univ _⟩]
        at hd
      beta_reduce at hd
      rw [hdfx (show (y, b) ∈ V ×ˢ univ from ⟨interior_subset hy, mem_univ _⟩)] at hd
      exact hd
    · have hA : ContDiffLC₂ 0 s (fun q : E₁ × (E₂ × E₂) ↦ f (q.1, q.2.1)) U (V ×ˢ univ) :=
        ((hf.of_le le_rfl (by omega)).comp_prodMap_zero (f₁ := id)
          (f₂ := ⇑(ContinuousLinearMap.fst ℝ E₂ E₂)) hU hV.prod_univ hU hVc hV continuousOn_id
          ((ContinuousLinearMap.fst ℝ E₂ E₂).contDiffLC s hV.prod_univ) (mapsTo_id _)
          fun q hq ↦ hq.1).congr fun _ _ ↦ rfl
      have hP := hA.prodMk hU hV.prod_univ (hf.contDiffLC₂_partialDLC₂ hU hV)
      exact ih (hVc.prod isLocallyConvexSubset_univ) hV.prod_univ
        (hWc.prod isLocallyConvexSubset_univ) hW.prod_univ hP hg.contDiffLC_dLC
        fun q hq ↦ ⟨hfW ⟨hq.1, hq.2.1⟩, mem_univ _⟩

/-- **Chain rule 2 for `C^{r,s}` maps** ([GN26, Proposition 1.7.28, p. 100]): if `f` is
`C^{r,s}` on `U × V` with `f(U × V) ⊆ W` and `g` is `C^{r+s}` on `W`, then `g ∘ f` is `C^{r,s}`
on `U × V`. -/
theorem ContDiffLC₂.comp_left {r s : ℕ} {f : E₁ × E₂ → F₁} {g : F₁ → F} {U : Set E₁}
    {V : Set E₂} {W : Set F₁} (hUc : IsLocallyConvexSubset U) (hU : HasDenseInterior U)
    (hVc : IsLocallyConvexSubset V) (hV : HasDenseInterior V) (hWc : IsLocallyConvexSubset W)
    (hW : HasDenseInterior W) (hf : ContDiffLC₂ r s f U V) (hg : ContDiffLC (r + s) g W)
    (hfW : MapsTo f (U ×ˢ V) W) : ContDiffLC₂ r s (fun p ↦ g (f p)) U V := by
  induction r generalizing E₁ F₁ f g U W with
  | zero => exact hf.comp_left_zero hU hVc hV hWc hW (by simpa using hg) hfW
  | succ r ih =>
    refine ContDiffLC₂.succ_of hU hV ((hf.of_le (Nat.zero_le _) le_rfl).comp_left_zero hU hVc hV
      hWc hW (hg.of_le (by omega)) hfW)
      (G := fun q ↦ dLC g W (f (q.1.1, q.2), partialDLC₁ f U V q)) (fun x hx y hy a ↦ ?_) ?_
    · obtain ⟨hfy, hdfy⟩ := hf.dLC_left hU hV (interior_subset hy)
      have hmy : MapsTo (fun x ↦ f (x, y)) U W := fun x hx ↦ hfW ⟨hx, interior_subset hy⟩
      obtain ⟨hcomp, hdcomp⟩ := ContDiffLC.comp_one hU hWc hW (hg.of_le (by omega))
        (hfy.of_le (by omega)) hmy
      have hd := hcomp.2.1 x hx a
      rw [← dLC_of_mem_interior _ (p := (x, a)) hx, hdcomp ⟨interior_subset hx, mem_univ _⟩]
        at hd
      beta_reduce at hd
      rw [hdfy (show (x, a) ∈ U ×ˢ univ from ⟨interior_subset hx, mem_univ _⟩)] at hd
      exact hd
    · have hA : ContDiffLC₂ r s (fun q : (E₁ × E₁) × E₂ ↦ f (q.1.1, q.2)) (U ×ˢ univ) V :=
        ((hf.of_le (by omega) le_rfl).comp_prodMap
          (f₁ := ⇑(ContinuousLinearMap.fst ℝ E₁ E₁)) (f₂ := id) hU.prod_univ hV hUc hU hVc hV
          ((ContinuousLinearMap.fst ℝ E₁ E₁).contDiffLC r hU.prod_univ) (contDiffLC_id s hV)
          (fun q hq ↦ hq.1) (mapsTo_id _)).congr fun _ _ ↦ rfl
      have hP := hA.prodMk hU.prod_univ hV (hf.contDiffLC₂_partialDLC₁ hU hV)
      have hg' : ContDiffLC (r + s) (dLC g W) (W ×ˢ univ) := by
        have : ContDiffLC (r + s + 1) g W := by rwa [show r + s + 1 = r + 1 + s by omega]
        exact this.contDiffLC_dLC
      exact ih (hUc.prod isLocallyConvexSubset_univ) hU.prod_univ
        (hWc.prod isLocallyConvexSubset_univ) hW.prod_univ hP hg'
        fun q hq ↦ ⟨hfW ⟨hq.1.1, hq.2⟩, mem_univ _⟩

end Chain

/-! ### Mappings to products of families -/

section Pi

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {ι : Type w} {Fi : ι → Type v} [∀ a, AddCommGroup (Fi a)] [∀ a, Module ℝ (Fi a)]
  [∀ a, TopologicalSpace (Fi a)] [∀ a, IsTopologicalAddGroup (Fi a)]
  [∀ a, ContinuousSMul ℝ (Fi a)] [∀ a, LocallyConvexSpace ℝ (Fi a)] [∀ a, T2Space (Fi a)]
  {k ℓ : ℕ} {U : Set E₁} {V : Set E₂}

omit [∀ a, IsTopologicalAddGroup (Fi a)] [∀ a, ContinuousSMul ℝ (Fi a)]
  [∀ a, LocallyConvexSpace ℝ (Fi a)] [∀ a, T2Space (Fi a)] in
/-- Directional derivatives of maps into products are taken componentwise. -/
theorem HasDirDerivAt.pi {E : Type*} [AddCommGroup E] [Module ℝ E] {φ : ∀ a, E → Fi a}
    {x h : E} {y : ∀ a, Fi a} (hφ : ∀ a, HasDirDerivAt (φ a) x h (y a)) :
    HasDirDerivAt (fun z a ↦ φ a z) x h y :=
  tendsto_pi_nhds.2 hφ

/-- Families of `C^{0,ℓ}` maps. -/
theorem ContDiffLC₂.pi_zero {ℓ : ℕ} {f : ∀ a, E₁ × E₂ → Fi a} {V : Set E₂}
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) (hf : ∀ a, ContDiffLC₂ 0 ℓ (f a) U V) :
    ContDiffLC₂ 0 ℓ (fun p a ↦ f a p) U V := by
  induction ℓ generalizing E₂ f V with
  | zero => exact contDiffLC₂_zero_zero_iff.2 (continuousOn_pi.2 fun a ↦ (hf a).1)
  | succ ℓ ih =>
    exact ContDiffLC₂.zero_succ_of hU hV
      (contDiffLC₂_zero_zero_iff.2 (continuousOn_pi.2 fun a ↦ (hf a).1))
      (H := fun q a ↦ partialDLC₂ (f a) U V q)
      (fun x hx y hy b ↦ HasDirDerivAt.pi fun a ↦ (hf a).hasDirDerivAt_partialDLC₂ hx hy b)
      (ih hV.prod_univ fun a ↦ (hf a).contDiffLC₂_partialDLC₂ hU hV)

/-- Families of `C^{k,ℓ}` maps are `C^{k,ℓ}` as maps into the product. -/
theorem ContDiffLC₂.pi {k : ℕ} {f : ∀ a, E₁ × E₂ → Fi a} {U : Set E₁}
    (hU : HasDenseInterior U) (hV : HasDenseInterior V) (hf : ∀ a, ContDiffLC₂ k ℓ (f a) U V) :
    ContDiffLC₂ k ℓ (fun p a ↦ f a p) U V := by
  induction k generalizing E₁ f U with
  | zero => exact ContDiffLC₂.pi_zero hU hV hf
  | succ k ih =>
    exact ContDiffLC₂.succ_of hU hV
      (ContDiffLC₂.pi_zero hU hV fun a ↦ (hf a).of_le (Nat.zero_le _) le_rfl)
      (G := fun q a ↦ partialDLC₁ (f a) U V q)
      (fun x hx y hy b ↦ HasDirDerivAt.pi fun a ↦ (hf a).hasDirDerivAt_partialDLC₁ hx hy b)
      (ih hU.prod_univ fun a ↦ (hf a).contDiffLC₂_partialDLC₁ hU hV)

/-- **[GN26, Proposition 1.7.20]** (p. 95): a map into a product `∏ₐ Fₐ` of locally
convex spaces is `C^{k,ℓ}` if and only if each component is. -/
theorem contDiffLC₂_pi_iff {f : ∀ a, E₁ × E₂ → Fi a} (hU : HasDenseInterior U)
    (hV : HasDenseInterior V) :
    ContDiffLC₂ k ℓ (fun p a ↦ f a p) U V ↔ ∀ a, ContDiffLC₂ k ℓ (f a) U V :=
  ⟨fun h a ↦ (h.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := Fi) a) hU hV).congr
    fun _ _ ↦ rfl, fun h ↦ ContDiffLC₂.pi hU hV h⟩

end Pi

end LocallyConvex.Analysis

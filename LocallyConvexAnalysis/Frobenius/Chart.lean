/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Frobenius.Basic
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Involutive distributions and rectifying charts on Banach spaces

Near a point of `E × F`, a distribution whose subspaces are complements of `0 × F` is the field
of graphs `q ↦ graph f(q)` of a map `f : O → L(E, F)`. This file shows that, for this
distribution:

* **Involutivity is Penot's integrability condition.** The Lie bracket of two vector fields
  tangent to the graphs lies in `graph f(q)` if and only if
  `Df(q)(X q)((Y q).1) = Df(q)(Y q)((X q).1)` (`lieBracket_mem_graph_iff`). Hence
  `f` satisfies (Frob) at `q` if and only if the distribution is involutive at `q`
  (`frob_iff_involutive`). No completeness is needed here.
* **Frobenius theorem in chart form.** If `E` and `F` are Banach spaces and `f` is `C^n`,
  `1 ≤ n`, and satisfies (Frob), then around every point of `O` there is a `C^n` diffeomorphism
  `Φ(x, y) = (x, α(x, y))` whose derivative carries `E × 0` onto the distribution
  (`exists_frobenius_chart`). Its inverse is a chart that rectifies the distribution: its
  derivative carries `graph f(z)` onto `E × 0`. The leaves `x ↦ Φ(x, y)` are the integral
  manifolds. In the holomorphic case `Φ` and `Φ⁻¹` are complex analytic
  (`exists_frobenius_chart_holomorphic`).

The chart is built from the solution `α` of `D₁α = f(x, α)`, `α(x₀, y) = y`, given by
`exists_frobenius` ([Pen70, Théorème 1.1, p. 48]), and the inverse function theorem. The local
analysis of involutivity follows [Lan99, Chapter VI, §1] (condition FR 1 in local form, p. 157;
Theorems 1.1 and 1.2, pp. 156 and 158), where the integrability of the local equation is derived
from FR 1.

## Main results

* `lieBracket_mem_graph_iff`, `frob_iff_involutive`
* `map_range_inl_eq_graph`
* `exists_frobenius_chart`, `exists_frobenius_chart_holomorphic`

## References

* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
* [J.-P. Penot, *Sur le théorème de Frobenius*][Pen70]
-/

@[expose] public section

open Set Filter Metric VectorField
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

section Involutive

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A field tangent to the graphs of `f` has `F`-component of its derivative determined by `f`:
`D(X₂)(q) v = Df(q)(v)(X₁ q) + f(q)(DX₁(q) v)`. -/
theorem fderiv_snd_of_mem_graph {f : E × F → E →L[𝕜] F} {X : E × F → E × F} {q : E × F}
    (hf : DifferentiableAt 𝕜 f q) (hX : DifferentiableAt 𝕜 X q)
    (hXf : ∀ᶠ p in 𝓝 q, X p ∈ (f p : E →ₗ[𝕜] F).graph) (v : E × F) :
    (fderiv 𝕜 X q v).2 = fderiv 𝕜 f q v (X q).1 + f q (fderiv 𝕜 X q v).1 := by
  have hXf' : (fun p ↦ (X p).2) =ᶠ[𝓝 q] fun p ↦ f p (X p).1 :=
    hXf.mono fun p hp ↦ (LinearMap.mem_graph_iff _ _).1 hp
  have h1 := hX.hasFDerivAt.snd
  have h2 := (hf.hasFDerivAt.clm_apply hX.hasFDerivAt.fst).congr_of_eventuallyEq hXf'
  have := congrArg (fun L : E × F →L[𝕜] F ↦ L v) (h1.unique h2)
  simpa [add_comm] using this

/-- **Involutivity of a field of graphs.** For vector fields `X`, `Y` tangent near `q` to the
distribution `p ↦ graph f(p)`, the bracket `[X, Y](q)` lies in `graph f(q)` if and only if
`Df(q)(X q)((Y q).1) = Df(q)(Y q)((X q).1)`. -/
theorem lieBracket_mem_graph_iff {f : E × F → E →L[𝕜] F} {X Y : E × F → E × F} {q : E × F}
    (hf : DifferentiableAt 𝕜 f q) (hX : DifferentiableAt 𝕜 X q) (hY : DifferentiableAt 𝕜 Y q)
    (hXf : ∀ᶠ p in 𝓝 q, X p ∈ (f p : E →ₗ[𝕜] F).graph)
    (hYf : ∀ᶠ p in 𝓝 q, Y p ∈ (f p : E →ₗ[𝕜] F).graph) :
    lieBracket 𝕜 X Y q ∈ (f q : E →ₗ[𝕜] F).graph ↔
      fderiv 𝕜 f q (X q) (Y q).1 = fderiv 𝕜 f q (Y q) (X q).1 := by
  rw [LinearMap.mem_graph_iff, lieBracket_eq]
  simp only [Prod.snd_sub, Prod.fst_sub, ContinuousLinearMap.coe_coe, map_sub,
    fderiv_snd_of_mem_graph hf hY hYf, fderiv_snd_of_mem_graph hf hX hXf]
  rw [← sub_eq_zero, ← sub_eq_zero (a := fderiv 𝕜 f q (X q) (Y q).1)]
  constructor <;> intro h <;> [rw [← h]; rw [← h]] <;> abel

/-- **Penot's integrability condition is involutivity.** For `f` differentiable at `q`, the
condition (Frob) at `q` holds if and only if the Lie bracket of any two vector fields tangent to
the distribution `p ↦ graph f(p)` near `q`, differentiable at `q`, lies in `graph f(q)`. -/
theorem frob_iff_involutive {f : E × F → E →L[𝕜] F} {q : E × F}
    (hf : DifferentiableAt 𝕜 f q) :
    (∀ a b : E, fderiv 𝕜 f q (a, f q a) b = fderiv 𝕜 f q (b, f q b) a) ↔
      ∀ X Y : E × F → E × F, DifferentiableAt 𝕜 X q → DifferentiableAt 𝕜 Y q →
        (∀ᶠ p in 𝓝 q, X p ∈ (f p : E →ₗ[𝕜] F).graph) →
        (∀ᶠ p in 𝓝 q, Y p ∈ (f p : E →ₗ[𝕜] F).graph) →
        lieBracket 𝕜 X Y q ∈ (f q : E →ₗ[𝕜] F).graph := by
  constructor
  · intro h X Y hX hY hXf hYf
    rw [lieBracket_mem_graph_iff hf hX hY hXf hYf]
    have hXq : X q = ((X q).1, f q (X q).1) :=
      Prod.ext rfl ((LinearMap.mem_graph_iff _ _).1 hXf.self_of_nhds)
    have hYq : Y q = ((Y q).1, f q (Y q).1) :=
      Prod.ext rfl ((LinearMap.mem_graph_iff _ _).1 hYf.self_of_nhds)
    rw [hXq, hYq]
    exact h _ _
  · intro h a b
    have hS : ∀ c : E, DifferentiableAt 𝕜 (fun p : E × F ↦ (c, f p c)) q := fun c ↦
      (differentiableAt_const c).prodMk (hf.clm_apply (differentiableAt_const c))
    have hSf : ∀ c : E, ∀ᶠ p in 𝓝 q,
        ((fun p : E × F ↦ (c, f p c)) p) ∈ (f p : E →ₗ[𝕜] F).graph := fun c ↦
      Eventually.of_forall fun p ↦ (LinearMap.mem_graph_iff _ _).2 rfl
    exact (lieBracket_mem_graph_iff hf (hS a) (hS b) (hSf a) (hSf b)).1
      (h _ _ (hS a) (hS b) (hSf a) (hSf b))

/-- A linear map with `L(a, 0) = (a, g a)` carries `E × 0` onto `graph g`. -/
theorem map_range_inl_eq_graph {L : E × F →L[𝕜] E × F} {g : E →L[𝕜] F}
    (hL : ∀ a : E, L (a, 0) = (a, g a)) :
    Submodule.map (L : E × F →ₗ[𝕜] E × F) (LinearMap.range (LinearMap.inl 𝕜 E F)) =
      (g : E →ₗ[𝕜] F).graph := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.mem_graph_iff,
    ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, h⟩
    rw [LinearMap.inl_apply, hL] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl
  · intro h
    refine ⟨(a, 0), ⟨a, rfl⟩, ?_⟩
    rw [hL, h]

end Involutive

section Chart

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]

/-- **The Frobenius theorem in chart form on Banach spaces.** Let `O ⊆ E × F` be open and
`f : O → L(E, F)` of class `C^n`, `1 ≤ n`, satisfying (Frob). Then every `(x₀, y₀) ∈ O` is fixed
by a `C^n` diffeomorphism `Φ` between open subsets of `O`, of the form `Φ(x, y) = (x, α(x, y))`,
whose derivative carries `(a, 0)` to `(a, f(Φ p) a)`. Thus `Φ` carries the foliation by the
slices `E × {y}` to the distribution `z ↦ graph f(z)`, and the chart `Φ⁻¹` rectifies it:
`DΦ⁻¹(z)` maps `graph f(z)` onto `E × 0`. -/
theorem exists_frobenius_chart {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    {n : ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn 𝕜 n f O)
    (hfrob : ∀ q ∈ O, ∀ a b : E, fderiv 𝕜 f q (a, f q a) b = fderiv 𝕜 f q (b, f q b) a)
    {x₀ : E} {y₀ : F} (h₀ : (x₀, y₀) ∈ O) :
    ∃ Φ : OpenPartialHomeomorph (E × F) (E × F), (x₀, y₀) ∈ Φ.source ∧ Φ (x₀, y₀) = (x₀, y₀) ∧
      Φ.source ⊆ O ∧ Φ.target ⊆ O ∧
      ContDiffOn 𝕜 n Φ Φ.source ∧ ContDiffOn 𝕜 n Φ.symm Φ.target ∧
      (∀ p ∈ Φ.source, (Φ p).1 = p.1) ∧
      (∀ p ∈ Φ.source, ∀ a : E, fderiv 𝕜 Φ p (a, 0) = (a, f (Φ p) a)) ∧
      ∀ z ∈ Φ.target, Submodule.map (fderiv 𝕜 Φ.symm z : E × F →ₗ[𝕜] E × F)
        (f z : E →ₗ[𝕜] F).graph = LinearMap.range (LinearMap.inl 𝕜 E F) := by
  have hn0 : (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hn
  have hnz : (n : WithTop ℕ∞) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn0)
  obtain ⟨r, hr, hBO, α, hα, hα0, hαD⟩ := exists_frobenius hO hn hf hfrob h₀
  set B := ball x₀ r ×ˢ ball y₀ r
  have hB : IsOpen B := isOpen_ball.prod isOpen_ball
  have hp₀B : (x₀, y₀) ∈ B := ⟨mem_ball_self hr, mem_ball_self hr⟩
  set Φ₀ : E × F → E × F := fun p ↦ (p.1, α p) with hΦ₀def
  have hΦ₀ : ContDiffOn 𝕜 n Φ₀ B := contDiffOn_fst.prodMk hα
  have hdα : ∀ p ∈ B, HasFDerivAt α (fderiv 𝕜 α p) p := fun p hp ↦
    (((hα.differentiableOn hnz) p hp).differentiableAt (hB.mem_nhds hp)).hasFDerivAt
  have hdΦ₀ : ∀ p ∈ B, HasFDerivAt Φ₀ ((ContinuousLinearMap.fst 𝕜 E F).prod (fderiv 𝕜 α p)) p :=
    fun p hp ↦ hasFDerivAt_fst.prodMk (hdα p hp)
  -- the first partial derivative of `α` is `f`
  have hD₁ : ∀ p ∈ B, ∀ a : E, fderiv 𝕜 α p (a, 0) = f (Φ₀ p) a := by
    intro p hp a
    have h1 := (hdα p hp).comp p.1 (hasFDerivAt_prodMk_left (𝕜 := 𝕜) p.1 p.2)
    have h2 := (hαD p.1 hp.1 p.2 hp.2).2
    have := congrArg (fun L : E →L[𝕜] F ↦ L a) (h1.unique h2)
    simpa using this
  -- the second partial derivative of `α` at `(x₀, y₀)` is the identity
  have hD₂ : ∀ b : F, fderiv 𝕜 α (x₀, y₀) (0, b) = b := by
    intro b
    have h1 := (hdα _ hp₀B).comp y₀ (hasFDerivAt_prodMk_right (𝕜 := 𝕜) x₀ y₀)
    have h2 : HasFDerivAt (fun y ↦ α (x₀, y)) (ContinuousLinearMap.id 𝕜 F) y₀ :=
      (hasFDerivAt_id y₀).congr_of_eventuallyEq
        (eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) hα0)
    have := congrArg (fun L : F →L[𝕜] F ↦ L b) (h1.unique h2)
    simpa using this
  have hαp₀ : α (x₀, y₀) = y₀ := hα0 y₀ (mem_ball_self hr)
  -- the derivative at `(x₀, y₀)` is the shear `(a, b) ↦ (a, f(x₀, y₀) a + b)`
  set g := f (x₀, y₀)
  let L : (E × F) ≃L[𝕜] (E × F) :=
    ContinuousLinearEquiv.equivOfInverse
      ((ContinuousLinearMap.fst 𝕜 E F).prod
        (g.comp (ContinuousLinearMap.fst 𝕜 E F) + ContinuousLinearMap.snd 𝕜 E F))
      ((ContinuousLinearMap.fst 𝕜 E F).prod
        (ContinuousLinearMap.snd 𝕜 E F - g.comp (ContinuousLinearMap.fst 𝕜 E F)))
      (fun v ↦ by simp) (fun v ↦ by simp)
  have hder : HasFDerivAt Φ₀ (L : E × F →L[𝕜] E × F) (x₀, y₀) := by
    convert hdΦ₀ _ hp₀B using 1
    refine ContinuousLinearMap.ext fun v ↦ Prod.ext rfl ?_
    · have hv : v = (v.1, 0) + (0, v.2) := by simp
      change g v.1 + v.2 = fderiv 𝕜 α (x₀, y₀) v
      rw [hv, map_add, hD₁ _ hp₀B, hD₂]
      simp [Φ₀, hαp₀, g]
  -- the inverse function theorem
  set H := (hΦ₀.contDiffAt (hB.mem_nhds hp₀B)).toOpenPartialHomeomorph Φ₀ hder hnz
  have hH : ∀ p, H p = Φ₀ p := fun _ ↦ rfl
  set S := B ∩ fderiv 𝕜 Φ₀ ⁻¹' range ((↑) : ((E × F) ≃L[𝕜] (E × F)) → _ →L[𝕜] _)
  have hS : IsOpen S := (hΦ₀.continuousOn_fderiv_of_isOpen hB hn0).isOpen_inter_preimage hB
    ContinuousLinearEquiv.isOpen
  have hp₀S : (x₀, y₀) ∈ S := ⟨hp₀B, _, hder.fderiv.symm⟩
  set Φ := H.restrOpen S hS
  have hΦ : ∀ p, Φ p = Φ₀ p := fun _ ↦ rfl
  have hsrc : Φ.source ⊆ S := fun p hp ↦ by
    rw [OpenPartialHomeomorph.restrOpen_source] at hp; exact hp.2
  have hsrcB : Φ.source ⊆ B := fun p hp ↦ (hsrc hp).1
  have hp₀src : (x₀, y₀) ∈ Φ.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hder hnz, hp₀S⟩
  have hΦfd : ∀ p ∈ Φ.source, fderiv 𝕜 Φ p = fderiv 𝕜 Φ₀ p := fun p _ ↦ rfl
  have hΦ₀O : ∀ p ∈ B, Φ₀ p ∈ O := fun p hp ↦ (hαD p.1 hp.1 p.2 hp.2).1
  have hfd : ∀ p ∈ Φ.source, ∀ a : E, fderiv 𝕜 Φ p (a, 0) = (a, f (Φ p) a) := by
    intro p hp a
    rw [hΦfd p hp, (hdΦ₀ p (hsrcB hp)).fderiv]
    simp [hD₁ p (hsrcB hp)]
    rfl
  refine ⟨Φ, hp₀src, by simp [hΦ, Φ₀, hαp₀], fun p hp ↦ hBO (hsrcB hp), ?_,
    hΦ₀.mono hsrcB, ?_, fun p _ ↦ rfl, hfd, ?_⟩
  · intro z hz
    rw [← Φ.right_inv hz]
    exact hΦ₀O _ (hsrcB (Φ.map_target hz))
  · intro z hz
    obtain ⟨hpB, e, he⟩ := hsrc (Φ.map_target hz)
    have hd : HasFDerivAt Φ (e : _ →L[𝕜] _) (Φ.symm z) := by
      rw [he]; exact hdΦ₀ _ hpB |>.fderiv ▸ hdΦ₀ _ hpB
    exact (Φ.contDiffAt_symm hz hd (hΦ₀.contDiffAt (hB.mem_nhds hpB))).contDiffWithinAt
  · intro z hz
    have hp := Φ.map_target hz
    obtain ⟨hpB, e, he⟩ := hsrc hp
    have hd : HasFDerivAt Φ (e : _ →L[𝕜] _) (Φ.symm z) := by
      rw [he]; exact hdΦ₀ _ hpB |>.fderiv ▸ hdΦ₀ _ hpB
    rw [(Φ.hasFDerivAt_symm hz hd).fderiv]
    have hmap := map_range_inl_eq_graph (L := (e : E × F →L[𝕜] E × F))
      (g := f z) fun a ↦ by rw [he, ← hΦfd _ hp, hfd _ hp, Φ.right_inv hz]
    have hid : ((e.symm : E × F →L[𝕜] E × F) : E × F →ₗ[𝕜] E × F) ∘ₗ
        ((e : E × F →L[𝕜] E × F) : E × F →ₗ[𝕜] E × F) = LinearMap.id :=
      LinearMap.ext fun v ↦ e.symm_apply_apply v
    rw [← hmap, ← Submodule.map_comp, hid, Submodule.map_id]

end Chart

section Holomorphic

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **The holomorphic Frobenius theorem in chart form.** If `f : O → L(E, F)` is holomorphic on
complex Banach spaces and satisfies (Frob), the chart of `exists_frobenius_chart` and its inverse
are complex analytic. -/
theorem exists_frobenius_chart_holomorphic {f : E × F → E →L[ℂ] F} {O : Set (E × F)}
    (hO : IsOpen O) (hf : DifferentiableOn ℂ f O)
    (hfrob : ∀ q ∈ O, ∀ a b : E, fderiv ℂ f q (a, f q a) b = fderiv ℂ f q (b, f q b) a)
    {x₀ : E} {y₀ : F} (h₀ : (x₀, y₀) ∈ O) :
    ∃ Φ : OpenPartialHomeomorph (E × F) (E × F), (x₀, y₀) ∈ Φ.source ∧ Φ (x₀, y₀) = (x₀, y₀) ∧
      Φ.source ⊆ O ∧ Φ.target ⊆ O ∧
      ComplexAnalyticOn Φ Φ.source ∧ ComplexAnalyticOn Φ.symm Φ.target ∧
      (∀ p ∈ Φ.source, (Φ p).1 = p.1) ∧
      (∀ p ∈ Φ.source, ∀ a : E, fderiv ℂ Φ p (a, 0) = (a, f (Φ p) a)) ∧
      ∀ z ∈ Φ.target, Submodule.map (fderiv ℂ Φ.symm z : E × F →ₗ[ℂ] E × F)
        (f z : E →ₗ[ℂ] F).graph = LinearMap.range (LinearMap.inl ℂ E F) := by
  obtain ⟨Φ, h1, h2, h3, h4, hΦ, hΦs, h5, h6, h7⟩ :=
    exists_frobenius_chart (𝕜 := ℂ) hO (n := 1) le_rfl
      (by exact_mod_cast hf.contDiffOn_one_complex hO) hfrob h₀
  exact ⟨Φ, h1, h2, h3, h4,
    (hΦ.differentiableOn one_ne_zero).complexAnalyticOn Φ.open_source,
    (hΦs.differentiableOn one_ne_zero).complexAnalyticOn Φ.open_target, h5, h6, h7⟩

end Holomorphic

end LocallyConvex.Analysis

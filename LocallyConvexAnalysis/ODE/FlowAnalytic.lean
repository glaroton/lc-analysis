/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.Flow
public import LocallyConvexAnalysis.Analytic.BanachHolomorphic
public import LocallyConvexAnalysis.Complex.NormedComplexification
public import LocallyConvexAnalysis.Analytic.Operations

/-!
# Holomorphic and real analytic dependence of local flows on Banach spaces

We show that local flows of holomorphic vector fields on complex Banach spaces are holomorphic in
complex time and initial value, and that local flows of real analytic vector fields on real
Banach spaces are real analytic. This is the real analytic case of [GN26, Theorem 2.4.34]
(p. 203; the real analytic case is proved on p. 206). The time-dependent case with parameters is
reduced to the autonomous one through the field `(s, x, λ) ↦ (1, f(s, x, λ), 0)`, as usual.

## Main definitions

* `prodToNormed`: the complex linear homeomorphism `(ℝ × E)_ℂ → ℂ × E_ℂ`, with the normed
  complexification `E_ℂ` of `E`.

## Main results

* `exists_differentiableOn_flow_complex`: if `f` is complex differentiable on an open subset `U`
  of a complex Banach space, the local flows of `c' = f ∘ c` are holomorphic in **complex time**
  and initial value: `Fl : B_ℂ(0, ε) × V → U` is complex differentiable, hence complex analytic
  in the sense of Glöckner–Neeb (`DifferentiableOn.complexAnalyticOn`), and its restriction to
  real times solves the equation.
* `exists_realAnalyticOn_flow`: if `f` is **real analytic** (in the sense of Milnor:
  `RealAnalyticOn`, [GN26, Definition 2.2.2]) on an open subset `U` of a real Banach space
  `E`, then its local flows `Fl : (-ε, ε) × V → U` are real analytic in `(t, x)`
  ([GN26, Theorem 2.4.34], real analytic case).
* `exists_realAnalyticOn_flow_param`: the same for time-dependent equations with parameters,
  `c'(t) = f(t, c(t), λ)` with `f` real analytic on an open subset of `ℝ × E × Λ`: the solution
  is real analytic in time, initial time, initial value and parameter
  ([GN26, Theorem 2.4.34(b)], real analytic case).

## Implementation notes

* **Method.** We follow Glöckner–Neeb. A real analytic `f` has a complex analytic extension `g`
  to an open set `W ⊆ E_ℂ`; on the complex Banach space `E_ℂ` with a complex norm defining the
  product topology (`NormedComplexification`), `g` is complex differentiable
  (`ComplexAnalyticOn.differentiableOn`) and `C¹` over `ℂ`
  (`DifferentiableOn.contDiffOn_one_complex`). The flow theorem over `𝕜 = ℂ`,
  `exists_contDiffOn_flow_rclike`, gives a flow `Φ` of `g`, complex differentiable in complex
  time and initial value. For real `t` and `x ∈ E`, the curves `t ↦ Φ(t, x)` and `t ↦ Fl(t, x)`
  (the real flow of `f`, viewed in `E_ℂ`) both solve `c' = g ∘ c` with `c(0) = x`, since `g`
  extends `f`; by uniqueness they agree. Hence `Φ`, composed with the complex linear
  homeomorphism `(ℝ × E)_ℂ ≅ ℂ × E_ℂ`, is a complex analytic extension of `Fl`.
  GN obtain the identification `Φ(t, x) ∈ E` from their Lemma 2.4.30 (complex solutions with real
  data stay real); here it follows from uniqueness, since the real flow is already available.
* `E` is a Banach space: completeness is needed for the inverse function theorem on which the
  flows rest. On Fréchet spaces even linear equations need neither have solutions nor unique
  ones ([GN26, Examples 2.4.2] and 2.4.3).
* In `exists_realAnalyticOn_flow_param` the parameter space `Λ` is a Banach space, since the
  parameter becomes a coordinate of the autonomous equation; Glöckner and Neeb allow any locally
  convex parameter space, which is treated in `ODE/FlowParamReal.lean`.
* Only the time of existence `ε` of the local flow is shrunk; GN's Remark 2.4.35 (real analytic
  dependence on the whole quantitative domain of existence) needs the identity theorem and is not
  formalized here.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

universe u

/-! ### Holomorphic flows -/

section Holomorphic

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Local flows of holomorphic vector fields are holomorphic in complex time and initial
value.** Let `f` be complex differentiable on an open set `U` of a complex Banach space `E`, and
`x₀ ∈ U`. There are `ε > 0`, an open neighbourhood `V` of `x₀` and `Fl : ℂ × E → E`, complex
differentiable on `B_ℂ(0, ε) × V` with values in `U` and `Fl(0, x) = x`, such that for every
`x ∈ V` the curve of real time `t ↦ Fl(t, x)`, `|t| < ε`, solves `c' = f ∘ c`. -/
theorem exists_differentiableOn_flow_complex {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ Fl : ℂ × E → E,
      DifferentiableOn ℂ Fl (ball (0 : ℂ) ε ×ˢ V) ∧ ∀ x ∈ V, Fl (0, x) = x ∧
        (∀ t ∈ ball (0 : ℂ) ε, Fl (t, x) ∈ U) ∧
        ∀ t : ℝ, |t| < ε → HasDerivAt (fun s : ℝ ↦ Fl ((s : ℂ), x)) (f (Fl ((t : ℂ), x))) t := by
  obtain ⟨ε, hε, V, hV, hx₀V, Fl, hFl, H⟩ := exists_contDiffOn_flow_rclike (𝕜 := ℂ) hU
    (n := 1) le_rfl (hf.contDiffOn_one_complex hU) hx₀
  exact ⟨ε, hε, V, hV, hx₀V, Fl, hFl.differentiableOn one_ne_zero, H⟩

end Holomorphic

/-! ### Real analytic flows -/

section RealAnalytic

open Complexification NormedComplexification

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complex linear homeomorphism `(ℝ × E)_ℂ → ℂ × E_ℂ`, with the normed complexification
`E_ℂ` of `E`. -/
def prodToNormed : Complexification (ℝ × E) →L[ℂ] ℂ × NormedComplexification E :=
  (toComplexCLM.prodMap toNormed).comp prodCLM

@[simp] theorem prodToNormed_ofReal (t : ℝ) (x : E) :
    prodToNormed (ofReal (t, x)) = ((t : ℂ), ofRealCLM x) := by
  simp [prodToNormed]

/-- **Local flows of real analytic vector fields are real analytic.** Let `f` be real analytic
(in the sense of Milnor, `RealAnalyticOn`) on an open set `U` of a real Banach space `E`, and
`x₀ ∈ U`. There are `ε > 0`, an open neighbourhood `V` of `x₀` and `Fl : ℝ × E → E`, real
analytic on `(-ε, ε) × V`, such that for every `x ∈ V` the curve `t ↦ Fl(t, x)` is a solution of
`c' = f ∘ c` on `(-ε, ε)` with values in `U` and `c(0) = x` ([GN26, Theorem 2.4.34],
real analytic case). By `eqOn_Ioo_of_contDiffOn` these curves are the only solutions. -/
theorem exists_realAnalyticOn_flow [CompleteSpace E] {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : RealAnalyticOn f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ Fl : ℝ × E → E,
      RealAnalyticOn Fl (Ioo (-ε) ε ×ˢ V) ∧ ∀ x ∈ V, Fl (0, x) = x ∧
        ∀ t ∈ Ioo (-ε) ε, Fl (t, x) ∈ U ∧ HasDerivAt (fun s ↦ Fl (s, x)) (f (Fl (t, x))) t := by
  have hfs : ContDiffOn ℝ ∞ f U := (smoothMBOn_iff_contDiffOn hU).1 (hf.smoothMBOn hU)
  obtain ⟨W, hW, g, hg, hext⟩ := hf
  -- the complex analytic extension, on the normed complexification
  set W' : Set (NormedComplexification E) := ofNormed ⁻¹' W
  have hW' : IsOpen W' := hW.preimage ofNormed.continuous
  set g' : NormedComplexification E → NormedComplexification E := toNormed ∘ g ∘ ofNormed
  have hg'a : ComplexAnalyticOn g' W' :=
    (toNormed.complexAnalyticOn isOpen_univ).comp
      (hg.comp (ofNormed.complexAnalyticOn hW') hW' hW fun _ hz ↦ hz) hW' isOpen_univ
      (mapsTo_univ _ _)
  have hg'1 : ContDiffOn ℂ 1 g' W' := (hg'a.differentiableOn hW').contDiffOn_one_complex hW'
  have hextW : ∀ y ∈ U, ofRealCLM y ∈ W' := fun y hy ↦ (hext y hy).1
  have hextg : ∀ y ∈ U, g' (ofRealCLM y) = ofRealCLM (f y) := fun y hy ↦ by
    change toNormed (g (ofReal y)) = _
    rw [(hext y hy).2]
    rfl
  -- the real flow of `f` and the complex flow of its extension
  obtain ⟨ε₁, hε₁, V₁, hV₁, hx₀V₁, Fl, -, H₁⟩ :=
    exists_contDiffOn_flow hU (n := 1) le_rfl (hfs.of_le (by norm_cast)) hx₀
  obtain ⟨ε₂, hε₂, V₂, hV₂, hx₀V₂, Φ, hΦ, H₂⟩ :=
    exists_contDiffOn_flow_rclike (𝕜 := ℂ) hW' (n := 1) le_rfl hg'1 (hextW x₀ hx₀)
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  set V := V₁ ∩ ofRealCLM ⁻¹' V₂
  have hV : IsOpen V := hV₁.inter (hV₂.preimage ofRealCLM.continuous)
  have hI₁ : Ioo (-ε) ε ⊆ Ioo (-ε₁) ε₁ :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have habs : ∀ t ∈ Ioo (-ε) ε, |t| < ε₂ := fun t ht ↦
    (abs_lt.2 ht).trans_le (min_le_right _ _)
  -- the complexified real flow is the complex flow at real times
  have hid : ∀ x ∈ V, ∀ t ∈ Ioo (-ε) ε, ofRealCLM (Fl (t, x)) = Φ ((t : ℂ), ofRealCLM x) := by
    intro x hx
    refine eqOn_Ioo_of_contDiffOn hW' (hg'1.restrict_scalars ℝ)
      (c₁ := fun s ↦ ofRealCLM (Fl (s, x))) (c₂ := fun s ↦ Φ ((s : ℂ), ofRealCLM x))
      (fun t ht ↦ ?_) (fun t ht ↦ ?_) ⟨neg_lt_zero.2 hε, hε⟩ ?_
    · obtain ⟨hU', hd⟩ := (H₁ x hx.1).2 t (hI₁ ht)
      refine ⟨?_, hextW _ hU'⟩
      rw [hextg _ hU']
      exact ofRealCLM.hasFDerivAt.comp_hasDerivAt t hd
    · refine ⟨(H₂ _ hx.2).2.2 t (habs t ht), (H₂ _ hx.2).2.1 _ ?_⟩
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact habs t ht
    · simp only [Complex.ofReal_zero, (H₁ x hx.1).1, (H₂ _ hx.2).1]
  -- the complex analytic extension of the real flow
  set P : Complexification (ℝ × E) →L[ℂ] ℂ × NormedComplexification E := prodToNormed
  set B : Set (ℂ × NormedComplexification E) := ball (0 : ℂ) ε ×ˢ V₂
  have hB : IsOpen B := isOpen_ball.prod hV₂
  have hBsub : B ⊆ ball (0 : ℂ) ε₂ ×ˢ V₂ :=
    prod_mono (ball_subset_ball (min_le_right _ _)) le_rfl
  have hΦa : ComplexAnalyticOn Φ B :=
    ((hΦ.differentiableOn one_ne_zero).mono hBsub).complexAnalyticOn hB
  set W₀ := P ⁻¹' B
  have hW₀ : IsOpen W₀ := hB.preimage P.continuous
  refine ⟨ε, hε, V, hV, ⟨hx₀V₁, hx₀V₂⟩, Fl, ⟨W₀, hW₀, ofNormed ∘ Φ ∘ P, ?_, fun p hp ↦ ?_⟩,
    fun x hx ↦ ⟨(H₁ x hx.1).1, fun t ht ↦ (H₁ x hx.1).2 t (hI₁ ht)⟩⟩
  · exact (ofNormed.complexAnalyticOn isOpen_univ).comp
      (hΦa.comp (P.complexAnalyticOn hW₀) hW₀ hB fun _ hz ↦ hz) hW₀ isOpen_univ
      (mapsTo_univ _ _)
  · obtain ⟨t, x⟩ := p
    obtain ⟨ht, hx⟩ := hp
    have hP : P (ofReal (t, x)) = ((t : ℂ), ofRealCLM x) := prodToNormed_ofReal t x
    refine ⟨?_, ?_⟩
    · change P (ofReal (t, x)) ∈ B
      rw [hP]
      refine ⟨?_, hx.2⟩
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.2 ht
    · change ofNormed (Φ (P (ofReal (t, x)))) = _
      rw [hP, ← hid x hx t ht]
      rfl

end RealAnalytic

/-! ### Time-dependent equations with parameters -/

section Parameters

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {Λ : Type u} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [CompleteSpace Λ]

/-- **Real analytic dependence on time, initial value and parameters.** Let `f(t, x, λ)` be real
analytic (in the sense of Milnor) on an open set `U ⊆ ℝ × E × Λ`, with `E`, `Λ` real Banach
spaces, and `p₀ ∈ U`. There are `ε > 0`, an open neighbourhood `V` of `p₀` and
`φ : ℝ × (ℝ × E × Λ) → E`, real analytic on `(-ε, ε) × V`, such that for `p = (t₀, x, λ) ∈ V`
the curve `t ↦ φ(t, p)` solves `c'(t) = f(t₀ + t, c(t), λ)` on `(-ε, ε)` with `c(0) = x`; that
is, `φ(t, p)` is the value at time `t₀ + t` of the solution with `c(t₀) = x`
([GN26, Theorem 2.4.34(b)], real analytic case, p. 203). The proof applies
`exists_realAnalyticOn_flow` to the autonomous field `(s, x, λ) ↦ (1, f(s, x, λ), 0)`. Glöckner and
Neeb allow any locally convex parameter space; here `Λ` is a Banach space, since the parameter
becomes a coordinate of the autonomous equation. Locally convex parameters are treated in
`ODE/FlowParamReal.lean` (`exists_realAnalyticOn_flow_lcParam`). -/
theorem exists_realAnalyticOn_flow_param {f : ℝ × E × Λ → E} {U : Set (ℝ × E × Λ)}
    (hU : IsOpen U) (hf : RealAnalyticOn f U) {p₀ : ℝ × E × Λ} (hp₀ : p₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set (ℝ × E × Λ), IsOpen V ∧ p₀ ∈ V ∧ ∃ φ : ℝ × (ℝ × E × Λ) → E,
      RealAnalyticOn φ (Ioo (-ε) ε ×ˢ V) ∧ ∀ p ∈ V, φ (0, p) = p.2.1 ∧
        ∀ t ∈ Ioo (-ε) ε, (p.1 + t, φ (t, p), p.2.2) ∈ U ∧
          HasDerivAt (fun s ↦ φ (s, p)) (f (p.1 + t, φ (t, p), p.2.2)) t := by
  -- the autonomous field
  set X : ℝ × E × Λ → ℝ × E × Λ := fun q ↦ (1, f q, 0)
  have hX : RealAnalyticOn X U :=
    ((realAnalyticOn_const ((1 : ℝ), (0 : E), (0 : Λ)) U).add (hf.clm_comp
      (ContinuousLinearMap.inr ℝ ℝ (E × Λ) ∘L ContinuousLinearMap.inl ℝ E Λ))).congr
      fun q _ ↦ by simp [X]
  obtain ⟨ε, hε, V, hV, hp₀V, Fl, hFl, H⟩ := exists_realAnalyticOn_flow hU hX hp₀
  set L : ℝ × E × Λ →L[ℝ] E := ContinuousLinearMap.fst ℝ E Λ ∘L ContinuousLinearMap.snd ℝ ℝ (E × Λ)
  refine ⟨ε, hε, V, hV, hp₀V, fun q ↦ L (Fl q), hFl.clm_comp L, fun p hp ↦ ⟨?_, ?_⟩⟩
  · simp [L, (H p hp).1]
  -- the time and parameter components of the flow
  have hI : IsOpen (Ioo (-ε) ε) := isOpen_Ioo
  have hIc : IsPreconnected (Ioo (-ε) ε) := isPreconnected_Ioo
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.2 hε, hε⟩
  have hD := fun t (ht : t ∈ Ioo (-ε) ε) ↦ ((H p hp).2 t ht).2
  have hD₁ : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s ↦ (Fl (s, p)).1) 1 t := fun t ht ↦
    (ContinuousLinearMap.fst ℝ ℝ (E × Λ)).hasFDerivAt.comp_hasDerivAt t (hD t ht)
  have hD₃ : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s ↦ (Fl (s, p)).2.2) 0 t := fun t ht ↦
    ((ContinuousLinearMap.snd ℝ E Λ ∘L
      ContinuousLinearMap.snd ℝ ℝ (E × Λ)).hasFDerivAt).comp_hasDerivAt t (hD t ht)
  have hfst : ∀ t ∈ Ioo (-ε) ε, (Fl (t, p)).1 = p.1 + t := by
    refine hI.eqOn_of_deriv_eq hIc (f := fun s ↦ (Fl (s, p)).1) (g := fun s ↦ p.1 + s)
      (fun t ht ↦ (hD₁ t ht).differentiableAt.differentiableWithinAt)
      (differentiable_id.const_add _).differentiableOn (fun t ht ↦ ?_) h0 (by simp [(H p hp).1])
    rw [(hD₁ t ht).deriv, ((hasDerivAt_id' t).const_add p.1).deriv]
  have hthd : ∀ t ∈ Ioo (-ε) ε, (Fl (t, p)).2.2 = p.2.2 := by
    refine hI.eqOn_of_deriv_eq hIc (f := fun s ↦ (Fl (s, p)).2.2) (g := fun _ ↦ p.2.2)
      (fun t ht ↦ (hD₃ t ht).differentiableAt.differentiableWithinAt)
      (differentiable_const _).differentiableOn (fun t ht ↦ ?_) h0 (by simp [(H p hp).1])
    rw [(hD₃ t ht).deriv, (hasDerivAt_const t p.2.2).deriv]
  intro t ht
  have hFl_eq : Fl (t, p) = (p.1 + t, L (Fl (t, p)), p.2.2) :=
    Prod.ext (hfst t ht) (Prod.ext rfl (hthd t ht))
  rw [← hFl_eq]
  exact ⟨((H p hp).2 t ht).1, L.hasFDerivAt.comp_hasDerivAt t (hD t ht)⟩

end Parameters

end LocallyConvex.Analysis

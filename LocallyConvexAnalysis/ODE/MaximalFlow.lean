/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.FlowParamReal
public import LocallyConvexAnalysis.ODE.FlowParam

/-!
# Maximal flows of differential equations with parameters

Reference: [GN26, Definition 2.4.28, Theorem 2.4.29] (p. 200), Lemma 2.5.7, Theorem 2.5.18 and
Corollary 2.5.20 (pp. 214–222), Remark 2.4.35 (p. 206).

Let `E` be a real Banach space, `W` a topological space of parameters and `f : ℝ × E × W → E`
defined on `U ⊆ ℝ × E × W`. For `(t₀, y₀, p) ∈ U`, solutions of `y' = f(t, y, p)`, `y(t₀) = y₀`,
on open intervals glue to a maximal solution; `dom f U` is the set of `(t, t₀, y₀, p)` with `t` in
its interval, and `flow f U (t, t₀, y₀, p)` its value at `t` (Definition 2.4.28).

## Main results

* `MaximalFlow.IsSol.eqOn`: uniqueness of solutions on open intervals, under a local Lipschitz
  condition in `y` (`LocallyLipschitzY`).
* `MaximalFlow.flow_eq`, `MaximalFlow.isSol_flow`: the flow is the maximal solution.
* `MaximalFlow.flow_concat`: the flow property (Lemma 2.5.7).
* `MaximalFlow.isOpen_dom_and`: **globalization** (Theorem 2.5.18): if the equation admits local
  flows with a regularity `R` (`HasLocalFlows`, `FlowRegularity`), then `dom f U` is open and the
  flow has regularity `R` on it.
* `MaximalFlow.isOpen_dom_and_continuousOn_flow`, `MaximalFlow.isOpen_dom_and_contDiffMBOn_flow`,
  `MaximalFlow.isOpen_dom_and_smoothMBOn_flow`, `MaximalFlow.isOpen_dom_and_realAnalyticOn_flow`:
  **continuous, `C^k`, smooth and real analytic dependence of the maximal flow on time, initial
  time, initial value and a locally convex parameter** (Theorem 2.4.29), for `f` of the same
  class on an open set (for `k = 0`, with a local Lipschitz condition, `LocallyLipschitzYParam`).
* `MaximalFlow.realAnalyticOn_flow_of_forall_isSol`: if solutions exist on a whole interval `J`
  for all initial data in `J × S`, the flow is real analytic on `J × J × S` (the real analytic
  part of Remark 2.4.35).

## Implementation notes

* Time runs over `ℝ`; an open interval `J` of Glöckner–Neeb is encoded in `U ⊆ J × E × W`.
* The local Lipschitz condition is derived from `C^1`
  (`MaximalFlow.locallyLipschitzY_of_contDiffMBOn`) or from real analyticity
  (`MaximalFlow.locallyLipschitzY_of_realAnalyticOn`), and the local flows come from
  `exists_contDiffMBOn_flow_lcParam` and `exists_realAnalyticOn_flow_lcParam`.
* As in Glöckner–Neeb, the globalization is abstract: it only uses local flows and the
  composition `Fl(t, t₁, y₁, q) = Φ(t, t₂, Fl(t₂, t₁, y₁, q), q)` of a local flow with the flow
  near an earlier time. We state it for a regularity predicate `R` with the properties used
  (`FlowRegularity`), so that it serves the continuous, `C^k` and real analytic cases.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology NNReal

noncomputable section

namespace LocallyConvex.Analysis

namespace MaximalFlow

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Type*}
  (f : ℝ × E × W → E) (U : Set (ℝ × E × W))

/-- `γ` solves `y' = f(t, y, p)` on `I`. -/
def IsSol (p : W) (I : Set ℝ) (γ : ℝ → E) : Prop :=
  ∀ t ∈ I, (t, γ t, p) ∈ U ∧ HasDerivAt γ (f (t, γ t, p)) t

/-- A local Lipschitz condition in the second variable ([GN26, Definition 2.5.19]). -/
def LocallyLipschitzY : Prop :=
  ∀ q ∈ U, ∃ K : ℝ≥0, ∃ δ > (0 : ℝ), ∃ r > (0 : ℝ), ∀ t ∈ ball q.1 δ,
    LipschitzOnWith K (fun y ↦ f (t, y, q.2.2)) {y | y ∈ ball q.2.1 r ∧ (t, y, q.2.2) ∈ U}

/-- The domain of the maximal flow ([GN26, Definition 2.4.28]): the `(t, t₀, y₀, p)` such
that some solution on an open interval containing `t₀` and `t` starts at `y₀` at time `t₀`. -/
def dom : Set (ℝ × ℝ × E × W) :=
  {x | ∃ I : Set ℝ, ∃ γ : ℝ → E, IsOpen I ∧ IsPreconnected I ∧ x.2.1 ∈ I ∧ x.1 ∈ I ∧
    γ x.2.1 = x.2.2.1 ∧ IsSol f U x.2.2.2 I γ}

open Classical in
/-- The maximal flow `Fl(t, t₀, y₀, p)` ([GN26, Definition 2.4.28]); `0` outside
`dom f U`. -/
def flow (x : ℝ × ℝ × E × W) : E :=
  if h : x ∈ dom f U then h.choose_spec.choose x.1 else 0

variable {f U}

theorem IsSol.mono {p : W} {I J : Set ℝ} {γ : ℝ → E} (h : IsSol f U p I γ) (hJ : J ⊆ I) :
    IsSol f U p J γ := fun t ht ↦ h t (hJ ht)

/-- Local uniqueness of solutions. -/
theorem IsSol.eventuallyEq (hL : LocallyLipschitzY f U) {p : W} {I : Set ℝ} {γ₁ γ₂ : ℝ → E}
    (hI : IsOpen I) (h₁ : IsSol f U p I γ₁) (h₂ : IsSol f U p I γ₂) {t : ℝ} (ht : t ∈ I)
    (heq : γ₁ t = γ₂ t) : γ₁ =ᶠ[𝓝 t] γ₂ := by
  obtain ⟨K, δ, hδ, r, hr, hK⟩ := hL (t, γ₁ t, p) (h₁ t ht).1
  have hb₁ : ∀ᶠ s in 𝓝 t, γ₁ s ∈ ball (γ₁ t) r :=
    (h₁ t ht).2.continuousAt (ball_mem_nhds _ hr)
  have hb₂ : ∀ᶠ s in 𝓝 t, γ₂ s ∈ ball (γ₁ t) r := by
    rw [heq]
    exact (h₂ t ht).2.continuousAt (ball_mem_nhds _ hr)
  refine ODE_solution_unique_of_eventually (v := fun s y ↦ f (s, y, p))
    (s := fun s ↦ {y | y ∈ ball (γ₁ t) r ∧ (s, y, p) ∈ U}) (K := K) ?_ ?_ ?_ heq
  · filter_upwards [ball_mem_nhds t hδ] with s hs using hK s hs
  · filter_upwards [hI.mem_nhds ht, hb₁] with s hs hb using ⟨(h₁ s hs).2, hb, (h₁ s hs).1⟩
  · filter_upwards [hI.mem_nhds ht, hb₂] with s hs hb using ⟨(h₂ s hs).2, hb, (h₂ s hs).1⟩

/-- **Uniqueness of solutions** on an open interval. -/
theorem IsSol.eqOn (hL : LocallyLipschitzY f U) {p : W} {I : Set ℝ} {γ₁ γ₂ : ℝ → E}
    (hI : IsOpen I) (hIc : IsPreconnected I) (h₁ : IsSol f U p I γ₁) (h₂ : IsSol f U p I γ₂)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) (heq : γ₁ t₀ = γ₂ t₀) : EqOn γ₁ γ₂ I := by
  set u : Set ℝ := {s | γ₁ =ᶠ[𝓝 s] γ₂}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hcl : closure u ∩ I ⊆ u := by
    rintro s ⟨hs, hsI⟩
    refine h₁.eventuallyEq hL hI h₂ hsI ?_
    have : (𝓝[u] s).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hs
    have hlim : Tendsto (fun x ↦ γ₁ x - γ₂ x) (𝓝[u] s) (𝓝 (γ₁ s - γ₂ s)) :=
      (((h₁ s hsI).2.continuousAt.sub (h₂ s hsI).2.continuousAt).tendsto).mono_left
        nhdsWithin_le_nhds
    have h0 : ∀ᶠ x in 𝓝[u] s, (0 : E) = γ₁ x - γ₂ x :=
      eventually_nhdsWithin_of_forall fun x hx ↦ by rw [eq_comm, sub_eq_zero]; exact hx.self_of_nhds
    exact sub_eq_zero.1 (tendsto_nhds_unique (tendsto_const_nhds.congr' h0) hlim).symm
  exact fun s hs ↦
    (hIc.subset_of_closure_inter_subset hu ⟨t₀, ht₀, h₁.eventuallyEq hL hI h₂ ht₀ heq⟩ hcl
      hs).self_of_nhds

theorem isPreconnected_inter {I J : Set ℝ} (hI : IsPreconnected I) (hJ : IsPreconnected J) :
    IsPreconnected (I ∩ J) :=
  isPreconnected_iff_ordConnected.2
    ((isPreconnected_iff_ordConnected.1 hI).inter (isPreconnected_iff_ordConnected.1 hJ))

open Classical in
/-- **Gluing** two solutions that agree at a common point. -/
theorem IsSol.glue (hL : LocallyLipschitzY f U) {p : W} {I₁ I₂ : Set ℝ} {γ₁ γ₂ : ℝ → E}
    (hI₁ : IsOpen I₁) (hI₁c : IsPreconnected I₁) (hI₂ : IsOpen I₂) (hI₂c : IsPreconnected I₂)
    (h₁ : IsSol f U p I₁ γ₁) (h₂ : IsSol f U p I₂ γ₂) {c : ℝ} (hc₁ : c ∈ I₁) (hc₂ : c ∈ I₂)
    (heq : γ₁ c = γ₂ c) :
    IsSol f U p (I₁ ∪ I₂) (I₁.piecewise γ₁ γ₂) ∧ EqOn (I₁.piecewise γ₁ γ₂) γ₁ I₁ ∧
      EqOn (I₁.piecewise γ₁ γ₂) γ₂ I₂ := by
  have hagree : EqOn γ₁ γ₂ (I₁ ∩ I₂) :=
    IsSol.eqOn hL (hI₁.inter hI₂) (isPreconnected_inter hI₁c hI₂c) (h₁.mono inter_subset_left)
      (h₂.mono inter_subset_right) ⟨hc₁, hc₂⟩ heq
  have hg₁ : EqOn (I₁.piecewise γ₁ γ₂) γ₁ I₁ := piecewise_eqOn _ _ _
  have hg₂ : EqOn (I₁.piecewise γ₁ γ₂) γ₂ I₂ := fun s hs ↦ by
    by_cases h : s ∈ I₁
    · rw [piecewise_eq_of_mem _ _ _ h]
      exact hagree ⟨h, hs⟩
    · rw [piecewise_eq_of_notMem _ _ _ h]
  refine ⟨fun s hs ↦ ?_, hg₁, hg₂⟩
  rcases hs with hs | hs
  · rw [hg₁ hs]
    exact ⟨(h₁ s hs).1, (h₁ s hs).2.congr_of_eventuallyEq
      (eventuallyEq_of_mem (hI₁.mem_nhds hs) hg₁)⟩
  · rw [hg₂ hs]
    exact ⟨(h₂ s hs).1, (h₂ s hs).2.congr_of_eventuallyEq
      (eventuallyEq_of_mem (hI₂.mem_nhds hs) hg₂)⟩

theorem mem_dom {p : W} {I : Set ℝ} {γ : ℝ → E} (hI : IsOpen I) (hIc : IsPreconnected I)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (hsol : IsSol f U p I γ) :
    (t, t₀, γ t₀, p) ∈ dom f U :=
  ⟨I, γ, hI, hIc, ht₀, ht, rfl, hsol⟩

/-- **The flow is the solution**: on an open interval through `t₀`, every solution with
`γ(t₀) = y₀` is `t ↦ Fl(t, t₀, y₀, p)`. -/
theorem flow_eq (hL : LocallyLipschitzY f U) {p : W} {I : Set ℝ} {γ : ℝ → E} (hI : IsOpen I)
    (hIc : IsPreconnected I) {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (hsol : IsSol f U p I γ) :
    flow f U (t, t₀, γ t₀, p) = γ t := by
  have h := mem_dom hI hIc ht₀ ht hsol
  simp only [flow, h, ↓reduceDIte]
  obtain ⟨hI', hIc', ht₀', ht', hγ', hsol'⟩ := h.choose_spec.choose_spec
  exact IsSol.eqOn hL (hI'.inter hI) (isPreconnected_inter hIc' hIc)
    (hsol'.mono inter_subset_left) (hsol.mono inter_subset_right) ⟨ht₀', ht₀⟩ hγ' ⟨ht', ht⟩

/-- **The flow property** ([GN26, Lemma 2.5.7]): `Fl(t, t₂, Fl(t₂, t₁, y₁, q), q)` is
`Fl(t, t₁, y₁, q)`, and the latter is defined as soon as the former is. -/
theorem flow_concat (hL : LocallyLipschitzY f U) {t t₁ t₂ : ℝ} {y₁ : E} {q : W}
    (h₁ : (t₂, t₁, y₁, q) ∈ dom f U) (h₂ : (t, t₂, flow f U (t₂, t₁, y₁, q), q) ∈ dom f U) :
    (t, t₁, y₁, q) ∈ dom f U ∧
      flow f U (t, t₁, y₁, q) = flow f U (t, t₂, flow f U (t₂, t₁, y₁, q), q) := by
  obtain ⟨I₁, γ₁, hI₁, hI₁c, ht₁, ht₂, hy, hsol₁⟩ := h₁
  simp only at ht₁ ht₂ hy hsol₁
  subst hy
  have hy₂ : flow f U (t₂, t₁, γ₁ t₁, q) = γ₁ t₂ := flow_eq hL hI₁ hI₁c ht₁ ht₂ hsol₁
  rw [hy₂] at h₂ ⊢
  obtain ⟨I₂, γ₂, hI₂, hI₂c, ht₂', ht, hγ₂, hsol₂⟩ := h₂
  simp only at ht₂' ht hγ₂ hsol₂
  obtain ⟨hsol, hg₁, hg₂⟩ := IsSol.glue hL hI₁ hI₁c hI₂ hI₂c hsol₁ hsol₂ ht₂ ht₂' hγ₂.symm
  have hU := hI₁.union hI₂
  have hUc := hI₁c.union t₂ ht₂ ht₂' hI₂c
  have hmem := mem_dom hU hUc (Or.inl ht₁) (Or.inr ht) hsol
  rw [hg₁ ht₁] at hmem
  refine ⟨hmem, ?_⟩
  have e1 := flow_eq hL hU hUc (Or.inl ht₁) (Or.inr ht) hsol
  have e2 := flow_eq hL hI₂ hI₂c ht₂' ht hsol₂
  rw [hg₁ ht₁, hg₂ ht] at e1
  rw [e1, ← hγ₂, e2]

/-- The flow solves the equation on its interval: `t ↦ Fl(t, t₀, y₀, p)` is the maximal
solution. -/
theorem isSol_flow (hL : LocallyLipschitzY f U) {t₀ : ℝ} {y₀ : E} {p : W} :
    IsSol f U p {t | (t, t₀, y₀, p) ∈ dom f U} fun t ↦ flow f U (t, t₀, y₀, p) := by
  rintro t ⟨I, γ, hI, hIc, ht₀, ht, hy, hsol⟩
  simp only at ht₀ ht hy hsol
  subst hy
  have heq : EqOn (fun s ↦ flow f U (s, t₀, γ t₀, p)) γ I := fun s hs ↦
    flow_eq hL hI hIc ht₀ hs hsol
  rw [heq ht]
  exact ⟨(hsol t ht).1, (hsol t ht).2.congr_of_eventuallyEq (eventuallyEq_of_mem (hI.mem_nhds ht)
    heq)⟩

variable [TopologicalSpace W] (f U)

/-- **Local flows with a regularity `R`** ([GN26, Definition 2.5.9]): around each point of
`U` there is a solution map `φ(t, t₀, y₀, p)` with regularity `R` on a box. -/
def HasLocalFlows (R : (ℝ × ℝ × E × W → E) → Set (ℝ × ℝ × E × W) → Prop) : Prop :=
  ∀ q ∈ U, ∃ ε > (0 : ℝ), ∃ V : Set (E × W), IsOpen V ∧ q.2 ∈ V ∧ ∃ φ : ℝ × ℝ × E × W → E,
    R φ (ball q.1 ε ×ˢ (ball q.1 ε ×ˢ V)) ∧
    ∀ t₀ ∈ ball q.1 ε, ∀ v ∈ V, φ (t₀, t₀, v.1, v.2) = v.1 ∧
      ∀ t ∈ ball q.1 ε, (t, φ (t, t₀, v.1, v.2), v.2) ∈ U ∧
        HasDerivAt (fun s ↦ φ (s, t₀, v.1, v.2)) (f (t, φ (t, t₀, v.1, v.2), v.2)) t

/-- The properties of a regularity class used in the globalization of local flows. -/
structure FlowRegularity (R : (ℝ × ℝ × E × W → E) → Set (ℝ × ℝ × E × W) → Prop) : Prop where
  mono : ∀ {φ A B}, R φ A → B ⊆ A → R φ B
  congr : ∀ {φ ψ A}, IsOpen A → EqOn ψ φ A → R φ A → R ψ A
  of_local : ∀ {φ A}, IsOpen A → (∀ x ∈ A, ∃ N, IsOpen N ∧ x ∈ N ∧ R φ (A ∩ N)) → R φ A
  continuousOn : ∀ {φ A}, IsOpen A → R φ A → ContinuousOn φ A
  comp : ∀ {φ ψ : ℝ × ℝ × E × W → E} {A B D : Set (ℝ × ℝ × E × W)} (c : ℝ), IsOpen A →
    IsOpen B → IsOpen D → R φ A → R ψ B →
    (∀ x ∈ D, (c, x.2) ∈ B ∧ (x.1, c, ψ (c, x.2), x.2.2.2) ∈ A) →
    R (fun x ↦ φ (x.1, c, ψ (c, x.2), x.2.2.2)) D

variable {f U}

omit [TopologicalSpace W] in
/-- Local flows are restrictions of the maximal flow ([GN26, Remark 2.5.11]). -/
theorem mem_dom_and_flow_eq_of_local (hL : LocallyLipschitzY f U) {c ε : ℝ}
    {V : Set (E × W)} {φ : ℝ × ℝ × E × W → E}
    (hφ : ∀ t₀ ∈ ball c ε, ∀ v ∈ V, φ (t₀, t₀, v.1, v.2) = v.1 ∧
      ∀ t ∈ ball c ε, (t, φ (t, t₀, v.1, v.2), v.2) ∈ U ∧
        HasDerivAt (fun s ↦ φ (s, t₀, v.1, v.2)) (f (t, φ (t, t₀, v.1, v.2), v.2)) t)
    {x : ℝ × ℝ × E × W} (hx : x ∈ ball c ε ×ˢ (ball c ε ×ˢ V)) :
    x ∈ dom f U ∧ flow f U x = φ x := by
  obtain ⟨t, t₀, y₀, p⟩ := x
  obtain ⟨ht, ht₀, hv⟩ := hx
  obtain ⟨h0, hsol⟩ := hφ t₀ ht₀ (y₀, p) hv
  have hs : IsSol f U p (ball c ε) fun s ↦ φ (s, t₀, y₀, p) := fun s hs ↦ hsol s hs
  have hm := mem_dom isOpen_ball (convex_ball c ε).isPreconnected ht₀ ht hs
  have he := flow_eq hL isOpen_ball (convex_ball c ε).isPreconnected ht₀ ht hs
  simp only [h0] at hm he
  exact ⟨hm, he⟩

/-- **Globalization of local flows** ([GN26, Theorem 2.5.18]): if the equation satisfies a
local Lipschitz condition in `y` and admits local flows with regularity `R`, the domain of the
maximal flow is open and the flow has regularity `R` on it. Given `(τ, t₀, y₀, p)`, the set of
times `t₁` near which the flow is regular contains `t₀` and is open and closed in the interval of
the solution: near a limit point `θ`, the flow is the local flow at `θ` composed with the flow
at a nearby regular time `t₂`. -/
theorem isOpen_dom_and {R : (ℝ × ℝ × E × W → E) → Set (ℝ × ℝ × E × W) → Prop}
    (hR : FlowRegularity R) (hL : LocallyLipschitzY f U) (hloc : HasLocalFlows f U R) :
    IsOpen (dom f U) ∧ R (flow f U) (dom f U) := by
  have key : ∀ x ∈ dom f U, ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ dom f U ∧ R (flow f U) N := by
    rintro ⟨τ, t₀, y₀, p⟩ ⟨I, γ, hI, hIc, ht₀, hτ, hγ0, hsol⟩
    simp only at ht₀ hτ hγ0 hsol ⊢
    subst hγ0
    set u : Set ℝ := {t₁ | ∃ N, IsOpen N ∧ (t₁, t₀, γ t₀, p) ∈ N ∧ N ⊆ dom f U ∧ R (flow f U) N}
    have hu : IsOpen u := isOpen_iff_forall_mem_open.2 fun t₁ ⟨N, hN, hmem, hsub, hRN⟩ ↦
      ⟨(fun s ↦ (s, t₀, γ t₀, p)) ⁻¹' N, fun s hs ↦ ⟨N, hN, hs, hsub, hRN⟩,
        hN.preimage (by fun_prop), hmem⟩
    -- `t₀` is regular: a local flow
    have h0 : t₀ ∈ u := by
      obtain ⟨ε, hε, V, hV, hqV, φ, hφ, hφsol⟩ := hloc (t₀, γ t₀, p) (hsol t₀ ht₀).1
      refine ⟨ball t₀ ε ×ˢ (ball t₀ ε ×ˢ V), isOpen_ball.prod (isOpen_ball.prod hV),
        ⟨mem_ball_self hε, mem_ball_self hε, hqV⟩,
        fun x hx ↦ (mem_dom_and_flow_eq_of_local hL hφsol hx).1,
        hR.congr (isOpen_ball.prod (isOpen_ball.prod hV))
          (fun x hx ↦ (mem_dom_and_flow_eq_of_local hL hφsol hx).2) hφ⟩
    -- the regular times are closed in `I`
    have hcl : closure u ∩ I ⊆ u := by
      rintro θ ⟨hθ, hθI⟩
      obtain ⟨hθU, hθd⟩ := hsol θ hθI
      obtain ⟨ε, hε, V, hV, hθV, φ, hφ, hφsol⟩ := hloc (θ, γ θ, p) hθU
      have hG : I ∩ ball θ ε ∩ {s | (γ s, p) ∈ V} ∈ 𝓝 θ :=
        inter_mem (inter_mem (hI.mem_nhds hθI) (ball_mem_nhds θ hε))
          ((hθd.continuousAt.prodMk continuousAt_const).preimage_mem_nhds (hV.mem_nhds hθV))
      obtain ⟨t₂, ⟨⟨ht₂I, ht₂b⟩, ht₂V⟩, N₂, hN₂, ht₂N, hN₂d, hN₂R⟩ :=
        mem_closure_iff_nhds.1 hθ _ hG
      have hflowc := hR.continuousOn hN₂ hN₂R
      have hin : Continuous fun z : ℝ × E × W ↦ ((t₂, z) : ℝ × ℝ × E × W) := by fun_prop
      set Z : Set (ℝ × E × W) := {z | (t₂, z) ∈ N₂ ∧ (flow f U (t₂, z), z.2.2) ∈ V}
      have hZ : IsOpen Z := by
        have h1 : IsOpen {z : ℝ × E × W | (t₂, z) ∈ N₂} := hN₂.preimage hin
        have h2 : ContinuousOn (fun z : ℝ × E × W ↦ (flow f U (t₂, z), z.2.2))
            {z | (t₂, z) ∈ N₂} :=
          (hflowc.comp hin.continuousOn fun z hz ↦ hz).prodMk (by fun_prop)
        exact h2.isOpen_inter_preimage h1 hV
      have hZ0 : (t₀, γ t₀, p) ∈ Z := by
        refine ⟨ht₂N, ?_⟩
        rw [flow_eq hL hI hIc ht₀ ht₂I hsol]
        exact ht₂V
      -- on `ball θ ε × Z`, the flow is the local flow at `θ` after the flow up to `t₂`
      have hD : ∀ x ∈ ball θ ε ×ˢ Z,
          x ∈ dom f U ∧ flow f U x = φ (x.1, t₂, flow f U (t₂, x.2), x.2.2.2) := by
        rintro ⟨t, t₁, y₁, q⟩ ⟨ht, hz1, hz2⟩
        have hloc' := mem_dom_and_flow_eq_of_local hL hφsol
          (x := (t, t₂, flow f U (t₂, t₁, y₁, q), q)) ⟨ht, ht₂b, hz2⟩
        obtain ⟨hd, heq⟩ := flow_concat hL (hN₂d hz1) hloc'.1
        exact ⟨hd, heq.trans hloc'.2⟩
      exact ⟨ball θ ε ×ˢ Z, isOpen_ball.prod hZ, ⟨mem_ball_self hε, hZ0⟩,
        fun x hx ↦ (hD x hx).1,
        hR.congr (isOpen_ball.prod hZ) (fun x hx ↦ (hD x hx).2)
          (hR.comp t₂ (isOpen_ball.prod (isOpen_ball.prod hV))
          hN₂ (isOpen_ball.prod hZ) hφ hN₂R fun x hx ↦ ⟨hx.2.1, hx.1, ht₂b, hx.2.2⟩)⟩
    have hτu : τ ∈ u := hIc.subset_of_closure_inter_subset hu ⟨t₀, ht₀, h0⟩ hcl hτ
    obtain ⟨N, hN, hmem, hsub, hRN⟩ := hτu
    exact ⟨N, hN, hmem, hsub, hRN⟩
  have hopen : IsOpen (dom f U) := isOpen_iff_forall_mem_open.2 fun x hx ↦
    let ⟨N, hN, hmem, hsub, _⟩ := key x hx
    ⟨N, hsub, hN, hmem⟩
  refine ⟨hopen, hR.of_local hopen fun x hx ↦ ?_⟩
  obtain ⟨N, hN, hmem, hsub, hRN⟩ := key x hx
  exact ⟨N, hN, hmem, by rwa [inter_eq_right.2 hsub]⟩

end General

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Type*} [AddCommGroup W]
  [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W]

/-- Being `C^k` is a regularity class for the globalization of local flows. -/
theorem flowRegularity_contDiffMBOn (k : ℕ) :
    FlowRegularity (E := E) (W := W) fun φ A ↦ ContDiffMBOn k φ A where
  mono h hBA := h.mono hBA
  congr hA h hφ := ContDiffMBOn.congr_of_isOpen hA (fun x hx ↦ (h hx).symm) hφ
  of_local hA h := ContDiffMBOn.of_local hA h
  continuousOn _ h := h.continuousOn
  comp := by
    intro φ ψ A B D c hA hB hD hφ hψ hmaps
    set L : ℝ × ℝ × E × W →L[ℝ] ℝ × ℝ × E × W :=
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × E × W)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × E × W))
    have haff : ContDiffMBOn k (fun x : ℝ × ℝ × E × W ↦ ((c, 0) : ℝ × ℝ × E × W) + L x) D :=
      contDiffMBOn_const_add_clm _ L k D
    have hψc : ContDiffMBOn k (fun x : ℝ × ℝ × E × W ↦ ψ (c, x.2)) D := by
      have h := ContDiffMBOn.comp (g := ψ)
        (f := fun x : ℝ × ℝ × E × W ↦ ((c, 0) : ℝ × ℝ × E × W) + L x) hD hB hψ haff
        fun x hx ↦ by simpa [L] using (hmaps x hx).1
      exact h.congr_of_isOpen hD fun x _ ↦ by simp [L]
    set L₁ : ℝ × ℝ × E × W →L[ℝ] ℝ × ℝ × E × W :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × E × W)).prod
        ((0 : ℝ × ℝ × E × W →L[ℝ] ℝ).prod ((0 : ℝ × ℝ × E × W →L[ℝ] E).prod
          ((ContinuousLinearMap.snd ℝ E W).comp ((ContinuousLinearMap.snd ℝ ℝ (E × W)).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × E × W))))))
    set L₂ : E →L[ℝ] ℝ × ℝ × E × W :=
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × E × W)).comp ((ContinuousLinearMap.inr ℝ ℝ (E × W)).comp
        (ContinuousLinearMap.inl ℝ E W))
    have hg : ContDiffMBOn k (fun x : ℝ × ℝ × E × W ↦ (x.1, c, ψ (c, x.2), x.2.2.2)) D := by
      have h := ((L₁.contDiffMBOn k D).add hD
        (contDiffMBOn_const k ((0, c, 0, 0) : ℝ × ℝ × E × W) D)).add hD
        (ContDiffMBOn.clm_comp' L₂ hD hψc)
      exact h.congr_of_isOpen hD fun x _ ↦ by simp [L₁, L₂]
    exact ContDiffMBOn.comp hD hA hφ hg fun x hx ↦ (hmaps x hx).2

omit [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- A `C^1` right-hand side satisfies a local Lipschitz condition in `y` ([GN26, (2.103)]:
the derivative in `y` is bounded near each point, by continuity of `df` at `(q, 0)`). -/
theorem locallyLipschitzY_of_contDiffMBOn {f : ℝ × E × W → E} {U : Set (ℝ × E × W)}
    (hU : IsOpen U) (hf : ContDiffMBOn 1 f U) : LocallyLipschitzY f U := by
  intro q hq
  obtain ⟨r₁, hr₁, r₂, hr₂, P, -, hpP, -, -, L, hL, -, -, hlip⟩ :=
    ODEFlowParam.exists_bounds hU hf hq
  refine ⟨Real.toNNReal L, r₁, hr₁, r₂, hr₂, fun t ht ↦ LipschitzOnWith.of_dist_le_mul
    fun y hy y' hy' ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]
  exact hlip t ht q.2.2 hpP y hy.1 y' hy'.1

/-- **The maximal flow is `C^k`** ([GN26, Theorem 2.4.29 and Corollary 2.5.20], `k ≥ 1`):
let `E` be a real Banach space, `W` a real locally convex space, `k ≥ 1` and
`f : ℝ × E × W → E` a `C^k` map on an open set `U`. Then the domain of the maximal flow of
`y' = f(t, y, p)` is open in `ℝ × ℝ × E × W` and the flow `(t, t₀, y₀, p) ↦ Fl(t, t₀, y₀, p)` is
`C^k` on it. -/
theorem isOpen_dom_and_contDiffMBOn_flow [CompleteSpace E] {f : ℝ × E × W → E}
    {U : Set (ℝ × E × W)} (hU : IsOpen U) {k : ℕ} (hk : 1 ≤ k) (hf : ContDiffMBOn k f U) :
    IsOpen (dom f U) ∧ ContDiffMBOn k (flow f U) (dom f U) :=
  isOpen_dom_and (flowRegularity_contDiffMBOn k)
    (locallyLipschitzY_of_contDiffMBOn hU (hf.of_le hk))
    fun _ hq ↦ exists_contDiffMBOn_flow_lcParam hU hk hf hq

/-- **The maximal flow of a smooth equation is smooth** ([GN26, Theorem 2.4.29],
`k = ∞`). -/
theorem isOpen_dom_and_smoothMBOn_flow [CompleteSpace E] {f : ℝ × E × W → E}
    {U : Set (ℝ × E × W)} (hU : IsOpen U) (hf : SmoothMBOn f U) :
    IsOpen (dom f U) ∧ SmoothMBOn (flow f U) (dom f U) := by
  refine ⟨(isOpen_dom_and_contDiffMBOn_flow hU le_rfl (hf 1)).1, fun k ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact (isOpen_dom_and_contDiffMBOn_flow hU le_rfl (hf 1)).2.of_le (by omega)
  · exact (isOpen_dom_and_contDiffMBOn_flow hU hk (hf k)).2

/-- A **local Lipschitz condition in the second variable, with parameters**
([GN26, Definition 2.5.19]): near each point of `U`, on a box inside `U`, `f` is Lipschitz in `y`
uniformly in `t` and `p`. -/
def LocallyLipschitzYParam (f : ℝ × E × W → E) (U : Set (ℝ × E × W)) : Prop :=
  ∀ q ∈ U, ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q.2.2 ∈ P ∧ ∃ L > 0,
    ball q.1 r₁ ×ˢ (ball q.2.1 r₂ ×ˢ P) ⊆ U ∧
    ∀ t ∈ ball q.1 r₁, ∀ p ∈ P, ∀ y ∈ ball q.2.1 r₂, ∀ y' ∈ ball q.2.1 r₂,
      ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖

omit [NormedSpace ℝ E] [AddCommGroup W] [Module ℝ W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] in
theorem LocallyLipschitzYParam.locallyLipschitzY {f : ℝ × E × W → E} {U : Set (ℝ × E × W)}
    (h : LocallyLipschitzYParam f U) : LocallyLipschitzY f U := by
  intro q hq
  obtain ⟨r₁, hr₁, r₂, hr₂, P, -, hpP, L, hL, -, hlip⟩ := h q hq
  refine ⟨Real.toNNReal L, r₁, hr₁, r₂, hr₂, fun t ht ↦ LipschitzOnWith.of_dist_le_mul
    fun y hy y' hy' ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]
  exact hlip t ht q.2.2 hpP y hy.1 y' hy'.1

omit [NormedSpace ℝ E] [AddCommGroup W] [Module ℝ W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] in
/-- Continuity is a regularity class for the globalization of local flows. -/
theorem flowRegularity_continuousOn :
    FlowRegularity (E := E) (W := W) fun φ A ↦ ContinuousOn φ A where
  mono h hBA := h.mono hBA
  congr _ h hφ := hφ.congr h
  of_local hA h := fun x hx ↦ by
    obtain ⟨N, hN, hxN, hφN⟩ := h x hx
    exact ((hφN x ⟨hx, hxN⟩).continuousAt ((hA.inter hN).mem_nhds ⟨hx, hxN⟩)).continuousWithinAt
  continuousOn _ h := h
  comp := by
    intro φ ψ A B D c _ _ _ hφ hψ hmaps
    have hψc : ContinuousOn (fun x : ℝ × ℝ × E × W ↦ ψ (c, x.2)) D :=
      hψ.comp (continuous_const.prodMk continuous_snd).continuousOn fun x hx ↦ (hmaps x hx).1
    have hg : ContinuousOn (fun x : ℝ × ℝ × E × W ↦ (x.1, c, ψ (c, x.2), x.2.2.2)) D :=
      continuous_fst.continuousOn.prodMk (continuousOn_const.prodMk (hψc.prodMk
        (by fun_prop : Continuous fun x : ℝ × ℝ × E × W ↦ x.2.2.2).continuousOn))
    exact hφ.comp hg fun x hx ↦ (hmaps x hx).2

omit [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
omit [Module ℝ W] in
omit [AddCommGroup W] in
/-- **The maximal flow is continuous** ([GN26, Theorem 2.4.29 and Corollary 2.5.20],
`k = 0`): let `E` be a real Banach space, `W` a topological space and
`f : ℝ × E × W → E` continuous on an open set `U` and locally Lipschitz in the second variable,
with parameters. Then the domain of the maximal flow of `y' = f(t, y, p)` is open in
`ℝ × ℝ × E × W` and the flow is continuous on it. -/
theorem isOpen_dom_and_continuousOn_flow [CompleteSpace E] {f : ℝ × E × W → E}
    {U : Set (ℝ × E × W)} (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hlip : LocallyLipschitzYParam f U) :
    IsOpen (dom f U) ∧ ContinuousOn (flow f U) (dom f U) :=
  isOpen_dom_and flowRegularity_continuousOn hlip.locallyLipschitzY fun q hq ↦ by
    obtain ⟨r₁, hr₁, r₂, hr₂, P, hP, hpP, L, hL, -, hl⟩ := hlip q hq
    exact exists_continuousOn_flow_lcParam hU hfc hq ⟨r₁, hr₁, r₂, hr₂, P, hP, hpP, L, hL, hl⟩

end Smooth

section RealAnalytic

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {W : Type u} [AddCommGroup W]
  [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W]

/-- Real analyticity is a regularity class for the globalization of local flows. -/
theorem flowRegularity_realAnalyticOn :
    FlowRegularity (E := E) (W := W) fun φ A ↦ RealAnalyticOn φ A where
  mono h hBA := h.mono hBA
  congr _ h hφ := hφ.congr h
  of_local hA h := RealAnalyticOn.of_local hA h
  continuousOn hA h := (h.smoothMBOn hA 0).continuousOn
  comp := by
    intro φ ψ A B D c _ _ _ hφ hψ hmaps
    set L : ℝ × ℝ × E × W →L[ℝ] ℝ × ℝ × E × W :=
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × E × W)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × E × W))
    have haff : RealAnalyticOn (fun x : ℝ × ℝ × E × W ↦ ((c, x.2) : ℝ × ℝ × E × W)) D :=
      ((realAnalyticOn_const ((c, 0) : ℝ × ℝ × E × W) D).add (L.realAnalyticOn D)).congr
        fun x _ ↦ Prod.ext (by simp [L]) (by simp [L])
    have hψc : RealAnalyticOn (fun x : ℝ × ℝ × E × W ↦ ψ (c, x.2)) D :=
      hψ.comp haff fun x hx ↦ (hmaps x hx).1
    -- `(x₁, c, ψ(c, x₂), x₂₂₂)` as a sum of maps into `ℝ × ℝ × E × W` (one universe)
    set L₁ : ℝ × ℝ × E × W →L[ℝ] ℝ × ℝ × E × W :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × E × W)).prod
        ((0 : ℝ × ℝ × E × W →L[ℝ] ℝ).prod ((0 : ℝ × ℝ × E × W →L[ℝ] E).prod
          ((ContinuousLinearMap.snd ℝ E W).comp ((ContinuousLinearMap.snd ℝ ℝ (E × W)).comp
            (ContinuousLinearMap.snd ℝ ℝ (ℝ × E × W))))))
    set L₂ : E →L[ℝ] ℝ × ℝ × E × W :=
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × E × W)).comp ((ContinuousLinearMap.inr ℝ ℝ (E × W)).comp
        (ContinuousLinearMap.inl ℝ E W))
    have hg : RealAnalyticOn (fun x : ℝ × ℝ × E × W ↦ (x.1, c, ψ (c, x.2), x.2.2.2)) D :=
      (((L₁.realAnalyticOn D).add (realAnalyticOn_const ((0, c, 0, 0) : ℝ × ℝ × E × W) D)).add
        (hψc.clm_comp L₂)).congr fun x _ ↦ by simp [L₁, L₂]
    exact hφ.comp hg fun x hx ↦ (hmaps x hx).2

/-- A real analytic right-hand side satisfies a local Lipschitz condition in `y`: for fixed `p`,
`(t, y) ↦ f(t, y, p)` is real analytic on an open subset of the Banach space `ℝ × E`, hence `C^1`
with locally bounded derivative. -/
theorem locallyLipschitzY_of_realAnalyticOn {f : ℝ × E × W → E} {U : Set (ℝ × E × W)}
    (hU : IsOpen U) (hf : RealAnalyticOn f U) : LocallyLipschitzY f U := by
  intro q hq
  set p := q.2.2
  set g : ℝ × E → E := fun z ↦ f (z.1, z.2, p)
  have hin : Continuous fun z : ℝ × E ↦ ((z.1, z.2, p) : ℝ × E × W) := by fun_prop
  set Ug : Set (ℝ × E) := {z | (z.1, z.2, p) ∈ U}
  have hUg : IsOpen Ug := hU.preimage hin
  -- `g` is real analytic, hence `C^1`
  set L : ℝ × E →L[ℝ] ℝ × E × W :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod ((ContinuousLinearMap.snd ℝ ℝ E).prod 0)
  have haff : RealAnalyticOn (fun z : ℝ × E ↦ ((z.1, z.2, p) : ℝ × E × W)) Ug :=
    ((realAnalyticOn_const ((0, 0, p) : ℝ × E × W) Ug).add (L.realAnalyticOn Ug)).congr
      fun z _ ↦ by simp [L]
  have hg : RealAnalyticOn g Ug := hf.comp haff fun z hz ↦ hz
  have hC1 : ContDiffOn ℝ 1 g Ug := ContDiffMBOn.contDiffOn_one hUg (hg.smoothMBOn hUg 2)
  set z₀ : ℝ × E := (q.1, q.2.1)
  have hz₀ : z₀ ∈ Ug := hq
  -- a ball around `z₀` on which `‖Dg‖ ≤ ‖Dg(z₀)‖ + 1`
  have hcont : ContinuousAt (fderiv ℝ g) z₀ :=
    (hC1.continuousOn_fderiv_of_isOpen hUg le_rfl).continuousAt (hUg.mem_nhds hz₀)
  obtain ⟨ρ₁, hρ₁, hb⟩ := Metric.eventually_nhds_iff.1
    (hcont.eventually (Metric.ball_mem_nhds (fderiv ℝ g z₀) one_pos))
  obtain ⟨ρ₂, hρ₂, hsub⟩ := Metric.isOpen_iff.1 hUg z₀ hz₀
  set ρ := min ρ₁ ρ₂
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  set C : ℝ≥0 := Real.toNNReal (‖fderiv ℝ g z₀‖ + 1)
  have hLip : LipschitzOnWith C g (ball z₀ ρ) := by
    refine (convex_ball z₀ ρ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun z hz ↦ ?_)
      fun z hz ↦ ?_
    · exact (hC1.differentiableOn one_ne_zero z (hsub (ball_subset_ball (min_le_right _ _) hz)))
        |>.differentiableAt (hUg.mem_nhds (hsub (ball_subset_ball (min_le_right _ _) hz)))
    · have h1 := hb (lt_of_lt_of_le hz (min_le_left _ _))
      rw [dist_eq_norm] at h1
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
      calc ‖fderiv ℝ g z‖ = ‖fderiv ℝ g z₀ + (fderiv ℝ g z - fderiv ℝ g z₀)‖ := by abel_nf
        _ ≤ ‖fderiv ℝ g z₀‖ + ‖fderiv ℝ g z - fderiv ℝ g z₀‖ := norm_add_le _ _
        _ ≤ ‖fderiv ℝ g z₀‖ + 1 := by linarith
  refine ⟨C, ρ, hρ, ρ, hρ, fun t ht ↦ ?_⟩
  have hcomp := hLip.comp (LipschitzWith.prodMk_left t).lipschitzOnWith
    (s := ball q.2.1 ρ) fun y hy ↦ by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt ht hy
  rw [mul_one] at hcomp
  exact hcomp.mono fun y hy ↦ hy.1

/-- **The maximal flow is real analytic** ([GN26, Theorem 2.4.29], real analytic case, and
Corollary 2.5.20): let `E` be a real Banach space, `W` a real locally convex space and
`f : ℝ × E × W → E` real analytic on an open set `U`. Then the domain of the maximal flow of
`y' = f(t, y, p)` is open in `ℝ × ℝ × E × W` and the flow `(t, t₀, y₀, p) ↦ Fl(t, t₀, y₀, p)` is
real analytic on it. -/
theorem isOpen_dom_and_realAnalyticOn_flow [CompleteSpace E] {f : ℝ × E × W → E}
    {U : Set (ℝ × E × W)} (hU : IsOpen U) (hf : RealAnalyticOn f U) :
    IsOpen (dom f U) ∧ RealAnalyticOn (flow f U) (dom f U) :=
  isOpen_dom_and flowRegularity_realAnalyticOn (locallyLipschitzY_of_realAnalyticOn hU hf)
    fun _ hq ↦ exists_realAnalyticOn_flow_lcParam hU hf hq

/-- **Real analytic dependence on a whole interval** (the real analytic part of
[GN26, Remark 2.4.35]): if the solutions of `y' = f(t, y, p)`, `y(t₀) = y₀`, exist on an open
interval `J` for all `t₀ ∈ J` and `(y₀, p) ∈ S`, then they are given by the maximal flow, which is
real analytic on `J × J × S`. With the quantitative existence theorem ([GN26, Theorem 2.4.23]),
this applies to `S = B_R(y) × P` for the radii of Remark 2.4.35. -/
theorem realAnalyticOn_flow_of_forall_isSol [CompleteSpace E] {f : ℝ × E × W → E}
    {U : Set (ℝ × E × W)} (hU : IsOpen U) (hf : RealAnalyticOn f U) {J : Set ℝ} (hJ : IsOpen J)
    (hJc : IsPreconnected J) {S : Set (E × W)}
    (hS : ∀ t₀ ∈ J, ∀ v ∈ S, ∃ γ : ℝ → E, γ t₀ = v.1 ∧ IsSol f U v.2 J γ) :
    J ×ˢ (J ×ˢ S) ⊆ dom f U ∧ RealAnalyticOn (flow f U) (J ×ˢ (J ×ˢ S)) := by
  have hsub : J ×ˢ (J ×ˢ S) ⊆ dom f U := by
    rintro ⟨t, t₀, y₀, p⟩ ⟨ht, ht₀, hv⟩
    obtain ⟨γ, hγ, hsol⟩ := hS t₀ ht₀ (y₀, p) hv
    simp only at hγ
    subst hγ
    exact mem_dom hJ hJc ht₀ ht hsol
  exact ⟨hsub, (isOpen_dom_and_realAnalyticOn_flow hU hf).2.mono hsub⟩

end RealAnalytic

end MaximalFlow

end LocallyConvex.Analysis

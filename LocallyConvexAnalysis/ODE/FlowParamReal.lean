/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.FlowParam
public import LocallyConvexAnalysis.Complex.NormedComplexification
public import LocallyConvexAnalysis.Analytic.Operations

/-!
# Real analytic dependence of solutions on parameters in a locally convex space

Let `E` be a real Banach space, `W` a real locally convex space and `f : ℝ × E × W → E` real
analytic (in the sense of Milnor, `RealAnalyticOn`) on an open set `U`. We show that the solution
`φ(t, t₀, y₀, p)` of `y' = f(t, y, p)`, `y(t₀) = y₀`, is real analytic in time, initial time,
initial value and parameter. This extends `exists_realAnalyticOn_flow_param`, where the parameter
space is a Banach space.

Reference: [GN26, Theorem 2.4.34], real analytic case (pp. 203–206).

## Main definitions

* `parToCx E W`, `cxToPar E W`: the complex linear homeomorphisms
  `ℂ × E_ℂ × W_ℂ → (ℝ × E × W)_ℂ` and `(ℝ × ℝ × E × W)_ℂ → ℂ × ℂ × E_ℂ × W_ℂ`.

## Main results

* `exists_realAnalyticOn_flow_lcParam`: the solution `φ(t, t₀, y₀, p)` of `y' = f(t, y, p)`,
  `y(t₀) = y₀`, is real analytic in `(t, t₀, y₀, p)` near any point of `U`
  ([GN26, Theorem 2.4.34], real analytic case).
* `NormedComplexification.isClosed_range_ofRealCLM`: `E` is closed in its normed
  complexification `E_ℂ`.

## Implementation notes

We follow Glöckner–Neeb. The complex analytic extension of `f`, transported to
`ℂ × E_ℂ × W_ℂ` with the normed complexification `E_ℂ` of `E`, has a complex analytic solution
map `Φ` (`exists_complexAnalyticOn_flow_param`). For real data, `Φ` takes values in `E`: the
fixed point problem defining it preserves the closed set of curves in `E`
(`ODEFlowParam.flowPhi_mem_of_real`; this replaces the argument of [GN26, Lemma 2.4.30],
by real local solutions and uniqueness). The real part of `Φ` at real points is the real solution,
and `Φ` composed with the complex linear homeomorphism `(ℝ × ℝ × E × W)_ℂ ≅ ℂ × ℂ × E_ℂ × W_ℂ`
is a complex analytic extension of it.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u

namespace Complexification

section Products

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The inverse of `prodCLM`: the complex linear homeomorphism `E_ℂ × F_ℂ → (E × F)_ℂ`. -/
def prodInvCLM : Complexification E × Complexification F →L[ℂ] Complexification (E × F) where
  toFun p := mk (re p.1, re p.2) (im p.1, im p.2)
  map_add' p q := by ext <;> simp
  map_smul' z p := by ext <;> simp
  cont := continuous_mk
    ((continuous_re.comp continuous_fst).prodMk (continuous_re.comp continuous_snd))
    ((continuous_im.comp continuous_fst).prodMk (continuous_im.comp continuous_snd))

@[simp] theorem prodInvCLM_ofReal (x : E) (y : F) :
    prodInvCLM (ofReal x, ofReal y) = ofReal (x, y) := by
  ext <;> rfl

end Products

/-- The complex linear homeomorphism `ℂ → ℝ_ℂ`, `u + i v ↦ u + i v`. -/
def ofComplexCLM : ℂ →L[ℂ] Complexification ℝ where
  toFun z := mk z.re z.im
  map_add' z w := by ext <;> simp
  map_smul' z w := by ext <;> simp
  cont := continuous_mk Complex.continuous_re Complex.continuous_im

@[simp] theorem ofComplexCLM_ofReal (r : ℝ) : ofComplexCLM (r : ℂ) = ofReal r := by
  ext <;> simp [ofComplexCLM]

end Complexification

namespace NormedComplexification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Complexification

/-- The real part `E_ℂ → E`, as a continuous real linear map. -/
def reL : NormedComplexification E →L[ℝ] E where
  toFun p := re (toCx p)
  map_add' p q := by simp
  map_smul' r p := by
    rw [← Complex.coe_smul, toCx_smul, ofReal_smul, re_real_smul]
    rfl
  cont := lipschitzWith_re.continuous

theorem reL_ofRealCLM (u : E) : reL (ofRealCLM u) = u := rfl

/-- The real points of `E_ℂ`, as a closed real subspace. -/
theorem isClosed_range_ofRealCLM :
    IsClosed ((LinearMap.range (ofRealCLM (E := E)).toLinearMap :
      Submodule ℝ (NormedComplexification E)) : Set (NormedComplexification E)) := by
  have h : ((LinearMap.range (ofRealCLM (E := E)).toLinearMap :
      Submodule ℝ (NormedComplexification E)) : Set (NormedComplexification E)) =
      {p | im (toCx p) = 0} := by
    ext p
    refine ⟨?_, fun hp ↦ ⟨re (toCx p), ?_⟩⟩
    · rintro ⟨u, rfl⟩
      rfl
    · change ofCx (ofReal (re (toCx p))) = p
      refine (Complexification.ext rfl ?_ : ofReal (re (toCx p)) = toCx p)
      exact (hp : im (toCx p) = 0).symm
  rw [h]
  exact isClosed_eq lipschitzWith_im.continuous continuous_const

end NormedComplexification

open Complexification NormedComplexification

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {W : Type u} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]

variable (E W) in
/-- The complex linear homeomorphism `ℂ × E_ℂ × W_ℂ → (ℝ × E × W)_ℂ`. -/
def parToCx :
    ℂ × NormedComplexification E × Complexification W →L[ℂ] Complexification (ℝ × E × W) :=
  prodInvCLM ∘L (ofComplexCLM.prodMap
    (prodInvCLM ∘L (ofNormed.prodMap (ContinuousLinearMap.id ℂ (Complexification W)))))

omit [CompleteSpace E] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] in
theorem parToCx_ofReal (r : ℝ) (y : E) (p : W) :
    parToCx E W ((r : ℂ), ofRealCLM y, ofReal p) = ofReal (r, y, p) := by
  change prodInvCLM (ofComplexCLM (r : ℂ), prodInvCLM (ofNormed (ofRealCLM y), ofReal p)) = _
  rw [ofComplexCLM_ofReal]
  exact (congrArg (fun q ↦ prodInvCLM (ofReal r, q)) (prodInvCLM_ofReal y p)).trans
    (prodInvCLM_ofReal r (y, p))

variable (E W) in
/-- The complex linear homeomorphism `(ℝ × ℝ × E × W)_ℂ → ℂ × ℂ × E_ℂ × W_ℂ`. -/
def cxToPar : Complexification (ℝ × ℝ × E × W) →L[ℂ]
    ℂ × ℂ × NormedComplexification E × Complexification W :=
  (toComplexCLM.prodMap ((toComplexCLM.prodMap
    ((toNormed.prodMap (ContinuousLinearMap.id ℂ (Complexification W))) ∘L
      Complexification.prodCLM)) ∘L Complexification.prodCLM)) ∘L Complexification.prodCLM

omit [CompleteSpace E] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] in
theorem cxToPar_ofReal (t t₀ : ℝ) (y : E) (p : W) :
    cxToPar E W (ofReal (t, t₀, y, p)) = ((t : ℂ), (t₀ : ℂ), ofRealCLM y, ofReal p) := by
  simp [cxToPar]

/-- **Real analytic dependence on time, initial time, initial value and a locally convex
parameter** ([GN26, Theorem 2.4.34], real analytic case, pp. 203–206). Let `E` be a real
Banach space, `W` a real locally convex space, and `f : ℝ × E × W → E` real analytic (in the sense
of Milnor) on an open set `U ∋ q₀`. There are `ε > 0`, an open neighbourhood `V` of
`(q₀.2.1, q₀.2.2)` in `E × W` and a map `φ`, real analytic on
`(q₀.1 - ε, q₀.1 + ε)² × V`, such that for `t₀` in the interval and `(y₀, p) ∈ V` the curve
`t ↦ φ(t, t₀, y₀, p)` solves `y' = f(t, y, p)`, `y(t₀) = y₀`, on the interval. -/
theorem exists_realAnalyticOn_flow_lcParam {f : ℝ × E × W → E} {U : Set (ℝ × E × W)}
    (hU : IsOpen U) (hf : RealAnalyticOn f U) {q₀ : ℝ × E × W} (hq₀ : q₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set (E × W), IsOpen V ∧ q₀.2 ∈ V ∧ ∃ φ : ℝ × ℝ × E × W → E,
      RealAnalyticOn φ (ball q₀.1 ε ×ˢ (ball q₀.1 ε ×ˢ V)) ∧
      ∀ t₀ ∈ ball q₀.1 ε, ∀ v ∈ V, φ (t₀, t₀, v.1, v.2) = v.1 ∧
        ∀ t ∈ ball q₀.1 ε, (t, φ (t, t₀, v.1, v.2), v.2) ∈ U ∧
          HasDerivAt (fun s ↦ φ (s, t₀, v.1, v.2)) (f (t, φ (t, t₀, v.1, v.2), v.2)) t := by
  obtain ⟨V', hV', g, hg, hext⟩ := hf
  -- the complex analytic extension on `ℂ × E_ℂ × W_ℂ`
  set Q := parToCx E W
  set O : Set (ℂ × NormedComplexification E × Complexification W) :=
    Q ⁻¹' (V' ∩ (re : Complexification (ℝ × E × W) → ℝ × E × W) ⁻¹' U)
  have hO : IsOpen O := (hV'.inter (hU.preimage continuous_re)).preimage Q.continuous
  set G := toNormed ∘ g ∘ Q
  have hG : ComplexAnalyticOn G O :=
    (toNormed.complexAnalyticOn isOpen_univ).comp
      (hg.comp (Q.complexAnalyticOn hO) hO hV' fun _ hz ↦ hz.1) hO isOpen_univ (mapsTo_univ _ _)
  have hreal : ∀ (r : ℝ) (y : E) (p : W), ((r : ℂ), ofRealCLM y, ofReal p) ∈ O →
      (r, y, p) ∈ U ∧ G ((r : ℂ), ofRealCLM y, ofReal p) = ofRealCLM (f (r, y, p)) := by
    intro r y p h
    have hQ := parToCx_ofReal r y p
    have hU' : (r, y, p) ∈ U := by
      have h2 := h.2
      rwa [mem_preimage, hQ, re_ofReal] at h2
    refine ⟨hU', ?_⟩
    change toNormed (g (Q _)) = _
    rw [hQ, (hext _ hU').2]
    rfl
  have hq₀O : ((q₀.1 : ℂ), ofRealCLM q₀.2.1, ofReal q₀.2.2) ∈ O := by
    change Q _ ∈ V' ∩ (re : Complexification (ℝ × E × W) → ℝ × E × W) ⁻¹' U
    rw [parToCx_ofReal]
    exact ⟨(hext q₀ hq₀).1, by simpa using hq₀⟩
  obtain ⟨ε, hε, VC, hVC, hq₀VC, Φ, hΦ, H, Hreal⟩ := exists_complexAnalyticOn_flow_param hO hG hq₀O
  -- real data give real solutions
  set R : Submodule ℝ (NormedComplexification E) := LinearMap.range (ofRealCLM (E := E)).toLinearMap
  set PR : Set (Complexification W) := range ofReal
  have hball : ∀ r : ℝ, r ∈ ball q₀.1 ε → (r : ℂ) ∈ ball (q₀.1 : ℂ) ε := fun r hr ↦ by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← Real.dist_eq]
    exact hr
  set V : Set (E × W) := (fun v : E × W ↦ (ofRealCLM v.1, ofReal v.2)) ⁻¹' VC
  have hV : IsOpen V := hVC.preimage
    ((ofRealCLM.continuous.comp continuous_fst).prodMk (ofReal.continuous.comp continuous_snd))
  have hR : ∀ t ∈ ball q₀.1 ε, ∀ t₀ ∈ ball q₀.1 ε, ∀ v ∈ V,
      Φ ((t : ℂ), (t₀ : ℂ), ofRealCLM v.1, ofReal v.2) =
        ofRealCLM (reL (Φ ((t : ℂ), (t₀ : ℂ), ofRealCLM v.1, ofReal v.2))) := by
    intro t ht t₀ ht₀ v hv
    obtain ⟨y, hy⟩ := Hreal R isClosed_range_ofRealCLM PR
      (fun r y p hy hp hrO ↦ by
        obtain ⟨y', rfl⟩ := hy
        obtain ⟨p', rfl⟩ := hp
        exact ⟨_, ((hreal r y' p' hrO).2).symm⟩)
      t t₀ (hball t ht) (hball t₀ ht₀) _ hv ⟨v.1, rfl⟩ ⟨v.2, rfl⟩
    rw [← hy]
    rfl
  -- the real solution map
  set φ : ℝ × ℝ × E × W → E :=
    fun x ↦ reL (Φ ((x.1 : ℂ), (x.2.1 : ℂ), ofRealCLM x.2.2.1, ofReal x.2.2.2))
  set Bℂ := ball (q₀.1 : ℂ) ε ×ˢ (ball (q₀.1 : ℂ) ε ×ˢ VC)
  have hBℂ : IsOpen Bℂ := isOpen_ball.prod (isOpen_ball.prod hVC)
  set P := cxToPar E W
  refine ⟨ε, hε, V, hV, hq₀VC, φ, ⟨P ⁻¹' Bℂ, hBℂ.preimage P.continuous, ofNormed ∘ Φ ∘ P,
    (ofNormed.complexAnalyticOn isOpen_univ).comp
      (hΦ.comp (P.complexAnalyticOn (hBℂ.preimage P.continuous)) (hBℂ.preimage P.continuous) hBℂ
        fun _ hz ↦ hz) (hBℂ.preimage P.continuous) isOpen_univ (mapsTo_univ _ _),
    fun x hx ↦ ?_⟩, fun t₀ ht₀ v hv ↦ ⟨?_, fun t ht ↦ ?_⟩⟩
  · obtain ⟨t, t₀, y, p⟩ := x
    obtain ⟨ht, ht₀, hv⟩ := hx
    have hP := cxToPar_ofReal (E := E) (W := W) t t₀ y p
    refine ⟨?_, ?_⟩
    · change P _ ∈ Bℂ
      rw [hP]
      exact ⟨hball t ht, hball t₀ ht₀, hv⟩
    · change ofNormed (Φ (P (ofReal (t, t₀, y, p)))) = _
      rw [hP, hR t ht t₀ ht₀ (y, p) hv]
      rfl
  · change reL _ = _
    rw [(H _ (hball t₀ ht₀) _ hv).1]
    rfl
  · have hz := hR t ht t₀ ht₀ v hv
    have hH := (H _ (hball t₀ ht₀) _ hv).2 _ (hball t ht)
    rw [hz] at hH
    obtain ⟨hmem, hd⟩ := hH
    obtain ⟨hU', hG'⟩ := hreal _ _ _ hmem
    refine ⟨hU', ?_⟩
    have hd' : HasDerivAt (fun s : ℝ ↦ Φ ((s : ℂ), (t₀ : ℂ), ofRealCLM v.1, ofReal v.2))
        (G ((t : ℂ), ofRealCLM (φ (t, t₀, v.1, v.2)), ofReal v.2)) t := by
      refine (hd.scomp t (Complex.ofRealCLM.hasDerivAt (x := t))).congr_deriv ?_
      simp [φ]
    have h2 := reL.hasFDerivAt.comp_hasDerivAt t hd'
    rw [hG', reL_ofRealCLM] at h2
    exact h2

end LocallyConvex.Analysis

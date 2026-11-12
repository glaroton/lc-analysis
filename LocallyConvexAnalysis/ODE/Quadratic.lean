/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MBFrechet
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The second order equation of a quadratic spray in a Banach space

Let `E` be a Banach space, `U ⊆ E` open and `Γ : E → E → E → E`, written `Γ x a b`, a map such
that `(x, a, b) ↦ Γ x a b` is `C²` in the sense of Michal–Bastiani on `U × E × E` (for instance
smooth, see `SmoothMBOn.contDiffMBOn`). We study the second order equation

  `c'' = Γ_c (c', c')`,

the local equation of the geodesics of a quadratic spray (equivalently, of a connection with
Christoffel map `Γ`) on a Banach manifold; see [Lan99, Chapter IV, §3] and [Lar, §§6.1–6.2]. It
is the first order system on `E × E` given by the vector field `sprayField Γ (x, v) = (v, Γ x v v)`.

## Main results

* `contDiffOn_sprayField`: by the bridge `ContDiffMBOn.contDiffOn` ([GN26, Proposition 2.3.17]),
  the vector field is Fréchet `C¹` on `U × E`; hence it is locally Lipschitz there
  (`exists_lipschitzOnWith_sprayField`).
* `exists_uniform_isSprayCurveOn`: **uniform local existence**. For `x₀ ∈ U` there are
  `r, δ, ε > 0` such that for all `y` with `‖y - x₀‖ ≤ r` and all `w` with `‖w‖ ≤ δ` there is a
  solution on `[-ε, ε]` with `c 0 = y`, `c' 0 = w`. The proof is the Picard–Lindelöf theorem
  (`IsPicardLindelof`) with initial conditions in a closed ball and a common time interval.
* `IsSprayCurveOn.rescale`: if `Γ x` is homogeneous in each slot, `t ↦ c (s t)` is a solution
  with initial velocity `s w` whenever `c` is a solution with initial velocity `w`.
* `exists_uniform_isSprayCurveOn_of_norm_le`: for every `K ≥ 0` the existence time can be chosen
  uniformly for `‖y - x₀‖ ≤ r`, `‖w‖ ≤ K` (rescaling trades speed for time).
* `IsSprayCurveOn.eqOn_Ioo`: **uniqueness**. Two solutions on `(a, b)` with the same position
  and velocity at some `t₀ ∈ (a, b)` agree on `(a, b)`. This rests on the general
  `eqOn_Ioo_of_locallyLipschitz` for autonomous locally Lipschitz vector fields, proved by a
  connectedness argument from Mathlib's local uniqueness `ODE_solution_unique_of_eventually`.

Smoothness of solutions and their dependence on initial conditions are not treated here: they
follow from the general results on flows applied to the vector field `sprayField Γ`, which is
`C^k` when `Γ` is (`exists_contDiffOn_flow` in `ODE/Flow.lean`, and the maximal flow
`MaximalFlow.isOpen_dom_and_contDiffMBOn_flow` in `ODE/MaximalFlow.lean`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
* [G. Larotonda, *Estructuras geométricas para las variedades de Banach*][Lar]
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

namespace LocallyConvex.Analysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The first order system -/

/-- The vector field `(x, v) ↦ (v, Γ x v v)` on `E × E` of the second order equation
`c'' = Γ_c (c', c')`. -/
def sprayField (Γ : E → E → E → E) (p : E × E) : E × E :=
  (p.2, Γ p.1 p.2 p.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem sprayField_apply (Γ : E → E → E → E) (x v : E) :
    sprayField Γ (x, v) = (v, Γ x v v) :=
  rfl

/-- `c` is a solution of `c'' = Γ_c (c', c')` on `I` with velocity `c'`, staying in `U`: for every
`t ∈ I`, `c t ∈ U`, `c` has derivative `c' t` at `t` and `c'` has derivative
`Γ (c t) (c' t) (c' t)` at `t`. Derivatives are two-sided (`HasDerivAt`), also at the endpoints of
`I` if `I` contains them. -/
def IsSprayCurveOn (U : Set E) (Γ : E → E → E → E) (I : Set ℝ) (c c' : ℝ → E) : Prop :=
  ∀ t ∈ I, c t ∈ U ∧ HasDerivAt c (c' t) t ∧ HasDerivAt c' (Γ (c t) (c' t) (c' t)) t

theorem IsSprayCurveOn.mono {U : Set E} {Γ : E → E → E → E} {I J : Set ℝ} {c c' : ℝ → E}
    (h : IsSprayCurveOn U Γ I c c') (hJ : J ⊆ I) : IsSprayCurveOn U Γ J c c' :=
  fun t ht ↦ h t (hJ ht)

/-- A solution of the second order equation is the same as an integral curve
`t ↦ (c t, c' t)` of `sprayField Γ` staying in `U × E`. -/
theorem isSprayCurveOn_iff {U : Set E} {Γ : E → E → E → E} {I : Set ℝ} {c c' : ℝ → E} :
    IsSprayCurveOn U Γ I c c' ↔ ∀ t ∈ I, (c t, c' t) ∈ U ×ˢ (univ : Set E) ∧
      HasDerivAt (fun s ↦ (c s, c' s)) (sprayField Γ (c t, c' t)) t := by
  refine forall₂_congr fun t _ ↦ ?_
  simp only [mem_prod, mem_univ, and_true, sprayField_apply]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ h.1.prodMk h.2, fun h ↦ ⟨?_, ?_⟩⟩
  · exact (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t h
  · exact (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t h

/-! ### Regularity of the vector field -/

section Regularity

variable {U : Set E} {Γ : E → E → E → E}

/-- If `(x, a, b) ↦ Γ x a b` is `C²` in the sense of Michal–Bastiani on `U × E × E`, then
`sprayField Γ` is Fréchet `C¹` on `U × E`. -/
theorem contDiffOn_sprayField (hU : IsOpen U)
    (hΓ : ContDiffMBOn 2 (fun p : E × E × E ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ)) :
    ContDiffOn ℝ 1 (sprayField Γ) (U ×ˢ (univ : Set E)) := by
  have hG : ContDiffOn ℝ 1 (fun p : E × E × E ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ) :=
    ContDiffMBOn.contDiffOn (k := 1) (hU.prod isOpen_univ) hΓ
  have hd : ContDiff ℝ 1 (fun p : E × E ↦ (p.1, p.2, p.2)) := by fun_prop
  have hcomp : ContDiffOn ℝ 1 (fun p : E × E ↦ Γ p.1 p.2 p.2) (U ×ˢ (univ : Set E)) :=
    hG.comp hd.contDiffOn fun p hp ↦ ⟨hp.1, mem_univ _⟩
  exact contDiffOn_snd.prodMk hcomp

/-- `sprayField Γ` is locally Lipschitz on `U × E`. -/
theorem exists_lipschitzOnWith_sprayField (hU : IsOpen U)
    (hΓ : ContDiffMBOn 2 (fun p : E × E × E ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ))
    {p : E × E} (hp : p ∈ U ×ˢ (univ : Set E)) :
    ∃ K, ∃ s ∈ 𝓝 p, LipschitzOnWith K (sprayField Γ) s :=
  ((contDiffOn_sprayField hU hΓ).contDiffAt
    ((hU.prod isOpen_univ).mem_nhds hp)).exists_lipschitzOnWith

end Regularity

/-! ### Picard–Lindelöf with control of the image -/

/-- Picard–Lindelöf, keeping track of the fact that the solution stays in the closed ball where
the hypotheses on the vector field hold (this is how the solution is constructed, but it is not
part of the statement of `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`). -/
theorem exists_hasDerivWithinAt_mem_closedBall {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X] {f : ℝ → X → X} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ x : X} {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → X, α t₀ = x ∧ ∀ t ∈ Icc tmin tmax,
      HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t ∧ α t ∈ closedBall x₀ a := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, by rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀],
    fun t ht ↦ ⟨?_, α.compProj_mem_closedBall hf.mul_max_le⟩⟩
  apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
    α.continuous_compProj.continuousOn (fun _ _ ↦ α.compProj_mem_closedBall hf.mul_max_le)
    x ht |>.congr_of_mem _ ht
  intro t' ht'
  nth_rw 1 [← hα]
  rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-! ### Uniform local existence -/

section Existence

variable [CompleteSpace E] {U : Set E} {Γ : E → E → E → E}

/-- **Uniform local existence** for `c'' = Γ_c (c', c')`: near each `x₀ ∈ U` there are radii
`r, δ > 0` and a time `ε > 0` such that every initial condition `c 0 = y`, `c' 0 = w` with
`‖y - x₀‖ ≤ r` and `‖w‖ ≤ δ` has a solution on `[-ε, ε]` staying in `U`. (In fact `r = δ`.) -/
theorem exists_uniform_isSprayCurveOn (hU : IsOpen U)
    (hΓ : ContDiffMBOn 2 (fun p : E × E × E ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ))
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ δ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ y, ‖y - x₀‖ ≤ r → ∀ w, ‖w‖ ≤ δ →
      ∃ c c' : ℝ → E, c 0 = y ∧ c' 0 = w ∧ IsSprayCurveOn U Γ (Icc (-ε) ε) c c' := by
  set p₀ : E × E := (x₀, 0)
  have hW : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hp₀ : p₀ ∈ U ×ˢ (univ : Set E) := ⟨hx₀, mem_univ _⟩
  obtain ⟨K, s, hs, hK⟩ := exists_lipschitzOnWith_sprayField hU hΓ hp₀
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs (hW.mem_nhds hp₀))
  -- the closed ball of radius `a / 2` lies in `s ∩ (U × E)`
  have hball : closedBall p₀ (a / 2) ⊆ s ∩ U ×ˢ (univ : Set E) :=
    (closedBall_subset_ball (half_lt_self ha)).trans has
  set L : ℝ := K * a + ‖sprayField Γ p₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb : ∀ p ∈ closedBall p₀ (a / 2), ‖sprayField Γ p‖ ≤ L := by
    intro p hp
    have hp' : ‖p - p₀‖ ≤ a := (mem_closedBall_iff_norm.mp hp).trans (half_le_self ha.le)
    calc ‖sprayField Γ p‖ ≤ ‖sprayField Γ p - sprayField Γ p₀‖ + ‖sprayField Γ p₀‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ K * ‖p - p₀‖ + ‖sprayField Γ p₀‖ := by
          gcongr
          exact hK.norm_sub_le (hball hp).1 (hball (mem_closedBall_self (by positivity))).1
      _ ≤ K * a + ‖sprayField Γ p₀‖ := by gcongr
      _ ≤ L := by linarith
  set T : ℝ := a / 4 / L with hT
  have hT0 : 0 < T := by positivity
  have hT0' : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT0.le⟩
  have hpl : IsPicardLindelof (fun _ ↦ sprayField Γ) (⟨0, hT0'⟩ : Icc (-T) T) p₀
      ⟨a / 2, by positivity⟩ ⟨a / 4, by positivity⟩ ⟨L, hL0.le⟩ K := by
    refine IsPicardLindelof.of_time_independent (fun p hp ↦ hb p hp)
      (hK.mono fun p hp ↦ (hball hp).1) ?_
    change L * max (T - 0) (0 - -T) ≤ a / 2 - a / 4
    rw [sub_zero, zero_sub, neg_neg, max_self, hT, mul_div_cancel₀ _ hL0.ne']
    linarith
  refine ⟨a / 4, by positivity, a / 4, by positivity, T / 2, by positivity, fun y hy w hw ↦ ?_⟩
  have hyw : (y, w) ∈ closedBall p₀ (⟨a / 4, by positivity⟩ : ℝ≥0) := by
    rw [mem_closedBall_iff_norm]
    exact norm_prod_le_iff.mpr ⟨by simpa [p₀] using hy, by simpa [p₀] using hw⟩
  obtain ⟨α, hα0, hα⟩ := exists_hasDerivWithinAt_mem_closedBall hpl hyw
  refine ⟨fun t ↦ (α t).1, fun t ↦ (α t).2, by simp [hα0], by simp [hα0], ?_⟩
  refine isSprayCurveOn_iff.mpr fun t ht ↦ ?_
  have htT : t ∈ Ioo (-T) T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hd, hm⟩ := hα t (Ioo_subset_Icc_self htT)
  exact ⟨(hball hm).2, hd.hasDerivAt (Icc_mem_nhds htT.1 htT.2)⟩

end Existence

/-! ### Rescaling -/

section Rescaling

variable {U : Set E} {Γ : E → E → E → E}

/-- **Rescaling.** If `Γ x` is homogeneous in each slot and `c` is a solution with velocity `c'`
on `I`, then for every `s : ℝ` the curve `t ↦ c (s t)` is a solution with velocity
`t ↦ s • c' (s t)` on `{t | s t ∈ I}`. -/
theorem IsSprayCurveOn.rescale (hΓ₁ : ∀ x a b (s : ℝ), Γ x (s • a) b = s • Γ x a b)
    (hΓ₂ : ∀ x a b (s : ℝ), Γ x a (s • b) = s • Γ x a b) {I : Set ℝ} {c c' : ℝ → E}
    (h : IsSprayCurveOn U Γ I c c') (s : ℝ) :
    IsSprayCurveOn U Γ ((fun t ↦ s * t) ⁻¹' I) (fun t ↦ c (s * t)) (fun t ↦ s • c' (s * t)) := by
  intro t ht
  obtain ⟨hU, hc, hc'⟩ := h (s * t) ht
  have hm : HasDerivAt (fun t : ℝ ↦ s * t) s t := by
    simpa using (hasDerivAt_id t).const_mul s
  refine ⟨hU, hc.scomp t hm, ?_⟩
  have := (hc'.scomp t hm).const_smul s
  convert this using 1
  all_goals first
    | (funext τ; rfl)
    | simp only [hΓ₁, hΓ₂]

/-- Rescaling on symmetric intervals: a solution on `[-ε, ε]` gives, for `s ≠ 0`, a solution
`t ↦ c (s t)` on `[-ε / |s|, ε / |s|]`. -/
theorem IsSprayCurveOn.rescale_Icc (hΓ₁ : ∀ x a b (s : ℝ), Γ x (s • a) b = s • Γ x a b)
    (hΓ₂ : ∀ x a b (s : ℝ), Γ x a (s • b) = s • Γ x a b) {ε : ℝ} {c c' : ℝ → E}
    (h : IsSprayCurveOn U Γ (Icc (-ε) ε) c c') {s : ℝ} (hs : s ≠ 0) :
    IsSprayCurveOn U Γ (Icc (-(ε / |s|)) (ε / |s|)) (fun t ↦ c (s * t))
      (fun t ↦ s • c' (s * t)) := by
  refine (h.rescale hΓ₁ hΓ₂ s).mono fun t ht ↦ ?_
  have hs' : 0 < |s| := abs_pos.mpr hs
  have ht' : |t| ≤ ε / |s| := abs_le.mpr ht
  have : |s * t| ≤ ε := by
    rw [abs_mul]
    calc |s| * |t| ≤ |s| * (ε / |s|) := by gcongr
      _ = ε := mul_div_cancel₀ _ hs'.ne'
  exact abs_le.mp this

variable [CompleteSpace E]

/-- **Uniform existence for bounded velocities.** For `x₀ ∈ U` there is `r > 0` such that for
every `K ≥ 0` there is a time `ε > 0` for which every initial condition `c 0 = y`, `c' 0 = w`
with `‖y - x₀‖ ≤ r` and `‖w‖ ≤ K` has a solution on `[-ε, ε]` staying in `U`. -/
theorem exists_uniform_isSprayCurveOn_of_norm_le (hU : IsOpen U)
    (hΓ : ContDiffMBOn 2 (fun p : E × E × E ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ))
    (hΓ₁ : ∀ x a b (s : ℝ), Γ x (s • a) b = s • Γ x a b)
    (hΓ₂ : ∀ x a b (s : ℝ), Γ x a (s • b) = s • Γ x a b) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∀ K : ℝ, 0 ≤ K → ∃ ε > (0 : ℝ), ∀ y, ‖y - x₀‖ ≤ r → ∀ w, ‖w‖ ≤ K →
      ∃ c c' : ℝ → E, c 0 = y ∧ c' 0 = w ∧ IsSprayCurveOn U Γ (Icc (-ε) ε) c c' := by
  obtain ⟨r, hr, δ, hδ, ε, hε, H⟩ := exists_uniform_isSprayCurveOn hU hΓ hx₀
  refine ⟨r, hr, fun K hK ↦ ?_⟩
  set s : ℝ := (K + δ) / δ with hs_def
  have hs : 0 < s := by positivity
  refine ⟨ε / s, by positivity, fun y hy w hw ↦ ?_⟩
  have hw' : ‖s⁻¹ • w‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, hs_def, inv_div,
      div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨c, c', hc0, hc'0, hcs⟩ := H y hy _ hw'
  refine ⟨fun t ↦ c (s * t), fun t ↦ s • c' (s * t), by simp [hc0], ?_, ?_⟩
  · simp [hc'0, smul_smul, hs.ne']
  · simpa [abs_of_pos hs] using hcs.rescale_Icc hΓ₁ hΓ₂ hs.ne'

end Rescaling

/-! ### Uniqueness -/

section Uniqueness

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Local step of the uniqueness argument: two integral curves of a locally Lipschitz autonomous
vector field, defined on `(a, b)`, that agree at `t ∈ (a, b)` agree near `t`. -/
theorem eventuallyEq_of_locallyLipschitz {F : X → X} {W : Set X}
    (hF : ∀ p ∈ W, ∃ K, ∃ s ∈ 𝓝 p, LipschitzOnWith K F s) {α β : ℝ → X} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (F (α t)) t ∧ α t ∈ W)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (F (β t)) t ∧ β t ∈ W) {t : ℝ} (ht : t ∈ Ioo a b)
    (heq : α t = β t) : α =ᶠ[𝓝 t] β := by
  obtain ⟨K, s, hs, hK⟩ := hF (α t) (hα t ht).2
  have hI : ∀ᶠ τ in 𝓝 t, τ ∈ Ioo a b := Ioo_mem_nhds ht.1 ht.2
  have hαs : ∀ᶠ τ in 𝓝 t, α τ ∈ s := (hα t ht).1.continuousAt.preimage_mem_nhds hs
  have hβs : ∀ᶠ τ in 𝓝 t, β τ ∈ s :=
    (hβ t ht).1.continuousAt.preimage_mem_nhds (heq ▸ hs)
  refine ODE_solution_unique_of_eventually (v := fun _ ↦ F) (s := fun _ ↦ s) (K := K)
    (Eventually.of_forall fun _ ↦ hK) ?_ ?_ heq
  · filter_upwards [hI, hαs] with τ hτ hτs using ⟨(hα τ hτ).1, hτs⟩
  · filter_upwards [hI, hβs] with τ hτ hτs using ⟨(hβ τ hτ).1, hτs⟩

/-- **Uniqueness of integral curves** of an autonomous vector field `F` that is locally Lipschitz
at the points of `W`: two integral curves on `(a, b)` staying in `W` and agreeing at some
`t₀ ∈ (a, b)` agree on `(a, b)`. -/
theorem eqOn_Ioo_of_locallyLipschitz {F : X → X} {W : Set X}
    (hF : ∀ p ∈ W, ∃ K, ∃ s ∈ 𝓝 p, LipschitzOnWith K F s) {α β : ℝ → X} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (F (α t)) t ∧ α t ∈ W)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (F (β t)) t ∧ β t ∈ W) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (heq : α t₀ = β t₀) : EqOn α β (Ioo a b) := by
  set u : Set ℝ := {t | α =ᶠ[𝓝 t] β}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : Ioo a b ⊆ u := by
    refine isPreconnected_Ioo.subset_of_closure_inter_subset hu
      ⟨t₀, ht₀, eventuallyEq_of_locallyLipschitz hF hα hβ ht₀ heq⟩ ?_
    rintro t ⟨htc, ht⟩
    refine eventuallyEq_of_locallyLipschitz hF hα hβ ht ?_
    by_contra hne
    have hev : ∀ᶠ τ in 𝓝 t, α τ ≠ β τ :=
      ((hα t ht).1.continuousAt.prodMk (hβ t ht).1.continuousAt).eventually
        (isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds hne)
    obtain ⟨τ, hτu, hτ⟩ := (mem_closure_iff_frequently.mp htc).and_eventually hev |>.exists
    exact hτ hτu.eq_of_nhds
  exact fun t ht ↦ (hsub ht).eq_of_nhds

variable {U : Set E} {Γ : E → E → E → E}

/-- **Uniqueness** for `c'' = Γ_c (c', c')`: two solutions on `(a, b)` (staying in `U`) with the
same position and velocity at some `t₀ ∈ (a, b)` agree on `(a, b)`, together with their
velocities. -/
theorem IsSprayCurveOn.eqOn_Ioo (hU : IsOpen U)
    (hΓ : ContDiffMBOn 2 (fun p : E × E × E ↦ Γ p.1 p.2.1 p.2.2) (U ×ˢ univ))
    {a b : ℝ} {c₁ c₁' c₂ c₂' : ℝ → E} (h₁ : IsSprayCurveOn U Γ (Ioo a b) c₁ c₁')
    (h₂ : IsSprayCurveOn U Γ (Ioo a b) c₂ c₂') {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hc : c₁ t₀ = c₂ t₀) (hv : c₁' t₀ = c₂' t₀) :
    EqOn c₁ c₂ (Ioo a b) ∧ EqOn c₁' c₂' (Ioo a b) := by
  have H := eqOn_Ioo_of_locallyLipschitz (F := sprayField Γ) (W := U ×ˢ univ)
    (fun p hp ↦ exists_lipschitzOnWith_sprayField hU hΓ hp)
    (α := fun t ↦ (c₁ t, c₁' t)) (β := fun t ↦ (c₂ t, c₂' t))
    (fun t ht ↦ ((isSprayCurveOn_iff.mp h₁) t ht).symm)
    (fun t ht ↦ ((isSprayCurveOn_iff.mp h₂) t ht).symm) ht₀ (by simp [hc, hv])
  exact ⟨fun t ht ↦ congrArg Prod.fst (H ht), fun t ht ↦ congrArg Prod.snd (H ht)⟩

end Uniqueness

end LocallyConvex.Analysis

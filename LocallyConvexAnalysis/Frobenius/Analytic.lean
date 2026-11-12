/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Frobenius.Basic
public import LocallyConvexAnalysis.ODE.FlowAnalytic

/-!
# The local Frobenius theorem, real analytic case

Let `E`, `F` be real Banach spaces, `O ⊆ E × F` open and `f : O → L(E, F)` real analytic in the
sense of Milnor (`RealAnalyticOn`, [GN26, Definition 2.2.2]), satisfying the integrability
condition (Frob) of `LocallyConvexAnalysis.Frobenius.Basic`. Then the solution `α` of
`D₁α = f(x, α)`, `α(x₀, y) = y`, is real analytic near `(x₀, y₀)`. This is the case `r = ω` of J.-P.
Penot, *Sur le théorème de Frobenius*, Bull. Soc. Math. France 98 (1970), Théorème 1.1 (p. 48).

## Main definitions

* `frobeniusRayField f x₀`: the vector field `X(s, v, c) = (1, 0, f(x₀ + s v, c) v)` on
  `ℝ × E × F`, whose integral curves through `(0, v, y)` are `t ↦ (t, v, α(x₀ + t v, y))`.

## Main results

* `realAnalyticOn_frobeniusRayField`: if `f` is real analytic on `O`, then so is
  `frobeniusRayField f x₀` where it is defined.
* `exists_frobenius_realAnalytic`: if `f` is real analytic and satisfies (Frob), then near every
  `(x₀, y₀) ∈ O` there is a real analytic `α` on `B(x₀, r) × B(y₀, r) ⊆ O` with `α(x₀, y) = y`
  and `D₁α(x, y) = f(x, α(x, y))` ([Pen70, Théorème 1.1], `r = ω`).

## Implementation notes

Penot obtains this case from a real analytic implicit function theorem. We reduce it instead to
the real analytic dependence of local flows on the initial value (`exists_realAnalyticOn_flow`,
[GN26, Theorem 2.4.34]). Along the ray `t ↦ x₀ + t v`, the curve `t ↦ α(x₀ + t v, y)`
solves `c' = f(x₀ + t v, c) v`, `c(0) = y`; hence `t ↦ (t, v, α(x₀ + t v, y))` is the integral
curve through `(0, v, y)` of the autonomous real analytic vector field

  `X(s, v, c) = (1, 0, f(x₀ + s v, c) v)` on `ℝ × E × F`,

by uniqueness of solutions (`eqOn_Ioo_of_contDiffOn`). If `Fl` is its flow on `(-ε, ε) × V`,
then `α(x, y)` is the last component of `Fl(ε/2, (0, (2/ε)(x - x₀), y))`, a real analytic
function of `(x, y)`. We do not claim this argument is new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [J.-P. Penot, *Sur le théorème de Frobenius*][Pen70]
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The vector field `X(s, v, c) = (1, 0, f(x₀ + s v, c) v)` on `ℝ × E × F`, whose integral
curves through `(0, v, y)` are `t ↦ (t, v, α(x₀ + t v, y))`. -/
def frobeniusRayField (f : E × F → E →L[ℝ] F) (x₀ : E) (p : ℝ × E × F) : ℝ × E × F :=
  (1, 0, f (x₀ + p.1 • p.2.1, p.2.2) p.2.1)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The vector field `frobeniusRayField` is real analytic where it is defined. -/
theorem realAnalyticOn_frobeniusRayField {f : E × F → E →L[ℝ] F} {O : Set (E × F)}
    (hf : RealAnalyticOn f O) (x₀ : E) :
    RealAnalyticOn (frobeniusRayField f x₀) {p | (x₀ + p.1 • p.2.1, p.2.2) ∈ O} := by
  set U := {p : ℝ × E × F | (x₀ + p.1 • p.2.1, p.2.2) ∈ O}
  -- `p ↦ p.1 • p.2.1`, as a continuous bilinear expression in `(p, p)`
  have hsmul : RealAnalyticOn (fun p : ℝ × E × F ↦ p.1 • p.2.1) U := by
    let β : (ℝ × E × F) →ₗ[ℝ] (ℝ × E × F) →ₗ[ℝ] E :=
      LinearMap.mk₂ ℝ (fun p q ↦ p.1 • q.2.1) (fun _ _ _ ↦ add_smul _ _ _)
        (fun c p q ↦ by change (c * p.1) • q.2.1 = c • p.1 • q.2.1; rw [mul_smul])
        (fun _ _ _ ↦ smul_add _ _ _)
        (fun c p q ↦ by change p.1 • c • q.2.1 = c • p.1 • q.2.1; exact smul_comm _ _ _)
    have hβ : Continuous fun pq : (ℝ × E × F) × (ℝ × E × F) ↦ β pq.1 pq.2 :=
      (continuous_fst.comp continuous_fst).smul (continuous_fst.comp (continuous_snd.comp
        continuous_snd))
    exact RealAnalyticOn.bilin β hβ ((ContinuousLinearMap.id ℝ _).realAnalyticOn U)
      ((ContinuousLinearMap.id ℝ _).realAnalyticOn U)
  have hpt : RealAnalyticOn (fun p : ℝ × E × F ↦ (x₀ + p.1 • p.2.1, p.2.2)) U :=
    ((realAnalyticOn_const x₀ U).add hsmul).prodMk
      ((ContinuousLinearMap.snd ℝ E F ∘L ContinuousLinearMap.snd ℝ ℝ (E × F)).realAnalyticOn U)
  have hfU : RealAnalyticOn (fun p : ℝ × E × F ↦ f (x₀ + p.1 • p.2.1, p.2.2)) U :=
    hf.comp hpt fun _ hp ↦ hp
  have happ : RealAnalyticOn (fun p : ℝ × E × F ↦ f (x₀ + p.1 • p.2.1, p.2.2) p.2.1) U := by
    let β : (E →L[ℝ] F) →ₗ[ℝ] E →ₗ[ℝ] F :=
      LinearMap.mk₂ ℝ (fun T v ↦ T v) (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)
        (fun T _ _ ↦ T.map_add _ _) (fun c T v ↦ T.map_smul c v)
    have hβ : Continuous fun Tv : (E →L[ℝ] F) × E ↦ β Tv.1 Tv.2 :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous
    exact RealAnalyticOn.bilin β hβ hfU
      ((ContinuousLinearMap.fst ℝ E F ∘L ContinuousLinearMap.snd ℝ ℝ (E × F)).realAnalyticOn U)
  refine ((realAnalyticOn_const ((1 : ℝ), (0 : E), (0 : F)) U).add (happ.clm_comp
    (ContinuousLinearMap.inr ℝ ℝ (E × F) ∘L ContinuousLinearMap.inr ℝ E F))).congr fun p _ ↦ ?_
  simp [frobeniusRayField]

/-- **The local Frobenius theorem, real analytic case** ([Pen70, Théorème 1.1], `r = ω`). Let
`E`, `F` be real Banach spaces, `O ⊆ E × F` open and `f : O → L(E, F)` real analytic (in the
sense of Milnor) satisfying (Frob): `Df(q)(a, f(q) a)(b) = Df(q)(b, f(q) b)(a)`. Then for every
`(x₀, y₀) ∈ O` there are `r > 0` and a real analytic map `α` on `B(x₀, r) × B(y₀, r) ⊆ O` with
`α(x₀, y) = y` and `D₁α(x, y) = f(x, α(x, y))`. -/
theorem exists_frobenius_realAnalytic {f : E × F → E →L[ℝ] F} {O : Set (E × F)} (hO : IsOpen O)
    (hf : RealAnalyticOn f O)
    (hfrob : ∀ q ∈ O, ∀ a b : E, fderiv ℝ f q (a, f q a) b = fderiv ℝ f q (b, f q b) a)
    {x₀ : E} {y₀ : F} (h₀ : (x₀, y₀) ∈ O) :
    ∃ r > (0 : ℝ), ball x₀ r ×ˢ ball y₀ r ⊆ O ∧ ∃ α : E × F → F,
      RealAnalyticOn α (ball x₀ r ×ˢ ball y₀ r) ∧ (∀ y ∈ ball y₀ r, α (x₀, y) = y) ∧
      ∀ x ∈ ball x₀ r, ∀ y ∈ ball y₀ r, (x, α (x, y)) ∈ O ∧
        HasFDerivAt (fun x' ↦ α (x', y)) (f (x, α (x, y))) x := by
  have hfs : ContDiffOn ℝ ∞ f O := (smoothMBOn_iff_contDiffOn hO).1 (hf.smoothMBOn hO)
  -- the `C¹` Frobenius theorem
  obtain ⟨r, hr, hrO, α, -, hα0, hαd⟩ :=
    exists_frobenius (𝕜 := ℝ) hO (n := 1) le_rfl (hfs.of_le (by norm_cast)) hfrob h₀
  -- the real analytic flow of the ray field
  set X := frobeniusRayField f x₀
  set U := {p : ℝ × E × F | (x₀ + p.1 • p.2.1, p.2.2) ∈ O}
  have hU : IsOpen U := hO.preimage (by fun_prop)
  have hX : RealAnalyticOn X U := realAnalyticOn_frobeniusRayField hf x₀
  have hX1 : ContDiffOn ℝ 1 X U :=
    ((smoothMBOn_iff_contDiffOn hU).1 (hX.smoothMBOn hU)).of_le (by norm_cast)
  have hp₀ : ((0 : ℝ), (0 : E), y₀) ∈ U := by simpa [U] using h₀
  obtain ⟨ε, hε, V, hV, hp₀V, Fl, hFl, H⟩ := exists_realAnalyticOn_flow hU hX hp₀
  -- along rays, `α` is read off the flow
  have hray : ∀ v : E, ∀ y ∈ ball y₀ r, ((0 : ℝ), v, y) ∈ V → ‖v‖ * ε < r →
      ∀ t ∈ Ioo (-ε) ε, Fl (t, (0, v, y)) = (t, v, α (x₀ + t • v, y)) := by
    intro v y hy hpV hvε
    have hxt : ∀ t ∈ Ioo (-ε) ε, x₀ + t • v ∈ ball x₀ r := fun t ht ↦ by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖v‖ ≤ ε * ‖v‖ := by
            gcongr; exact (abs_lt.2 ht).le
        _ = ‖v‖ * ε := mul_comm _ _
        _ < r := hvε
    refine eqOn_Ioo_of_contDiffOn hU hX1 (c₁ := fun t ↦ Fl (t, (0, v, y)))
      (c₂ := fun t ↦ (t, v, α (x₀ + t • v, y))) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
      ⟨neg_lt_zero.2 hε, hε⟩ ?_
    · obtain ⟨hU', hd⟩ := (H _ hpV).2 t ht
      exact ⟨hd, hU'⟩
    · obtain ⟨hO', hd⟩ := hαd _ (hxt t ht) y hy
      refine ⟨?_, hO'⟩
      have hline : HasDerivAt (fun s : ℝ ↦ x₀ + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add x₀
      have h3 := hd.comp_hasDerivAt t hline
      exact (hasDerivAt_id t).prodMk ((hasDerivAt_const t v).prodMk h3)
    · simp [(H _ hpV).1, hα0 y hy]
  -- the radius
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hV _ hp₀V
  set r' := min (r / 2) (min (δ * ε / 2) δ)
  have hr' : 0 < r' := lt_min (by positivity) (lt_min (by positivity) hδ)
  have hr'r : r' ≤ r := (min_le_left _ _).trans (by linarith)
  have hball : ∀ x ∈ ball x₀ r', ∀ y ∈ ball y₀ r',
      ((0 : ℝ), (2 / ε) • (x - x₀), y) ∈ V ∧ ‖(2 / ε) • (x - x₀)‖ * ε < r ∧ y ∈ ball y₀ r := by
    intro x hx y hy
    have hx' : ‖x - x₀‖ < r' := by rwa [mem_ball, dist_eq_norm] at hx
    have hy' : ‖y - y₀‖ < r' := by rwa [mem_ball, dist_eq_norm] at hy
    have hn : ‖(2 / ε) • (x - x₀)‖ = 2 / ε * ‖x - x₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    refine ⟨hδV ?_, ?_, ball_subset_ball hr'r hy⟩
    · rw [mem_ball, Prod.dist_eq, Prod.dist_eq, dist_self, dist_eq_norm, dist_eq_norm, sub_zero,
        hn]
      refine max_lt hδ (max_lt ?_ (hy'.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
      have : ‖x - x₀‖ < δ * ε / 2 := hx'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      calc 2 / ε * ‖x - x₀‖ < 2 / ε * (δ * ε / 2) := by gcongr
        _ = δ := by field_simp
    · rw [hn]
      have : ‖x - x₀‖ < r / 2 := hx'.trans_le (min_le_left _ _)
      calc 2 / ε * ‖x - x₀‖ * ε = 2 * ‖x - x₀‖ := by field_simp
        _ < r := by linarith
  have hε2 : ε / 2 ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  have hαFl : ∀ q ∈ ball x₀ r' ×ˢ ball y₀ r',
      α q = (Fl (ε / 2, (0, (2 / ε) • (q.1 - x₀), q.2))).2.2 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨hpV, hvε, hyr⟩ := hball x hx y hy
    rw [hray _ y hyr hpV hvε _ hε2, smul_smul, div_mul_div_cancel₀ (by positivity : (2 : ℝ) ≠ 0),
      div_self hε.ne', one_smul, add_sub_cancel]
  refine ⟨r', hr', (Set.prod_mono (ball_subset_ball hr'r) (ball_subset_ball hr'r)).trans hrO, α,
    ?_, fun y hy ↦ hα0 y (ball_subset_ball hr'r hy),
    fun x hx y hy ↦ hαd x (ball_subset_ball hr'r hx) y (ball_subset_ball hr'r hy)⟩
  -- `α` agrees with a real analytic function of `(x, y)`
  have hin : RealAnalyticOn (fun q : E × F ↦ (ε / 2, ((0 : ℝ), (2 / ε) • (q.1 - x₀), q.2)))
      (ball x₀ r' ×ˢ ball y₀ r') :=
    ((realAnalyticOn_const ((ε / 2 : ℝ), (0 : ℝ), -((2 / ε) • x₀), (0 : F)) _).add
      ((ContinuousLinearMap.inr ℝ ℝ (ℝ × E × F) ∘L ContinuousLinearMap.inr ℝ ℝ (E × F) ∘L
        ((2 / ε) • ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ E)
          ((ε / 2) • ContinuousLinearMap.id ℝ F))).realAnalyticOn _)).congr fun q _ ↦ by
      ext <;> simp [sub_eq_neg_add, smul_smul, hε.ne']
  have hmaps : MapsTo (fun q : E × F ↦ (ε / 2, ((0 : ℝ), (2 / ε) • (q.1 - x₀), q.2)))
      (ball x₀ r' ×ˢ ball y₀ r') (Ioo (-ε) ε ×ˢ V) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hε2, (hball x hx y hy).1⟩
  exact ((hFl.comp hin hmaps).clm_comp
    (ContinuousLinearMap.snd ℝ E F ∘L ContinuousLinearMap.snd ℝ ℝ (E × F))).congr hαFl

end LocallyConvex.Analysis

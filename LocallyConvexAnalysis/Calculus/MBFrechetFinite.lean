/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MBFrechet

/-!
# In finite dimensions, Michal–Bastiani and Fréchet `C^k` maps agree

On open subsets of a finite-dimensional normed space `E`, with values in any normed space `F`, a
map is `C^k` in the sense of Michal–Bastiani if and only if it is Fréchet `C^k`, for every
`k ∈ ℕ`. In general one derivative is lost (`ContDiffMBOn.contDiffOn`,
[GN26, Proposition 2.3.17(b)]); in finite dimensions it is not. This is a consequence of
[GN26, Proposition 2.3.17(c)] (`f` is Fréchet `C^k` iff it is `C^k` and `x ↦ d^(k) f(x, ·)` is
continuous into `L^k(E; F)` with the topology of bounded convergence): in finite dimensions that
topology is the norm topology, and the continuity follows from the joint continuity of
`d^(k) f`.

## Main results

* `continuousOn_of_unc`: if `(x, v) ↦ g x v` is continuous on `U × E^m`, then
  `g : U → L^m(E; F)` is continuous for the operator norm.
* `contDiffOn_of_unc_of_finiteDimensional`: if `(x, v) ↦ g x v` is `C^k` in the sense of
  Michal–Bastiani, then `g : U → L^m(E; F)` is Fréchet `C^k`.
* `contDiffMBOn_iff_contDiffOn`: Michal–Bastiani and Fréchet `C^k` agree.

## Implementation notes

The proof is the induction of `Calculus/MBFrechet.lean` with the base case improved: there,
continuity of `g` in the operator norm comes from a local Lipschitz bound, which needs `ĝ` of
class `C^1`; here it comes from the uniform continuity of `ĝ` on `{x} × B̄^m`, where the closed
unit ball `B̄` of `E` is compact (tube lemma), so `ĝ` continuous suffices. The inductive step is
unchanged, with the index shifted by one.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- In finite dimensions, **continuity of `ĝ` gives continuity of `g` in the operator norm**: if
`(x, v) ↦ g x v` is continuous on `U × E^m`, then `g : U → L^m(E; F)` is continuous. -/
theorem continuousOn_of_unc {m : ℕ} {g : E → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F}
    {U : Set E} (hU : IsOpen U) (hg : ContinuousOn (unc g) (U ×ˢ univ)) : ContinuousOn g U := by
  intro x hx
  refine ContinuousAt.continuousWithinAt (Metric.tendsto_nhds.2 fun ε hε ↦ ?_)
  have := FiniteDimensional.proper_real E
  set η := ε / (2 * 2 ^ m)
  have hη : 0 < η := by positivity
  have hKb : IsCompact (closedBall (0 : Fin m → E) 1) := isCompact_closedBall _ _
  have hev : ∀ᶠ y in 𝓝 x, ∀ v ∈ closedBall (0 : Fin m → E) 1, dist (g y v) (g x v) < η := by
    refine hKb.eventually_forall_of_forall_eventually fun v _ ↦ ?_
    have hc : ContinuousAt (fun q : E × (Fin m → E) ↦ dist (unc g q) (g x q.2)) (x, v) :=
      ((hg.continuousAt (prod_mem_nhds (hU.mem_nhds hx) univ_mem)).dist
        ((g x).cont.comp continuous_snd).continuousAt)
    refine hc.eventually (Iio_mem_nhds ?_)
    simpa [unc] using hη
  filter_upwards [hev] with y hy
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (ContinuousMultilinearMap.opNorm_le_bound (by positivity : 0 ≤ η * 2 ^ m)
    fun V ↦ ?_) ?_
  · refine (g y - g x).toMultilinearMap.bound_of_shell (ε := fun _ ↦ 1) (c := fun _ ↦ (2 : ℝ))
      (fun _ ↦ one_pos) (fun _ ↦ by norm_num) (fun u hlo hhi ↦ ?_) V
    have hu : u ∈ closedBall (0 : Fin m → E) 1 := by
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ (hhi i).le
    have h1 : ‖(g y - g x) u‖ < η := by
      rw [sub_apply, ← dist_eq_norm]
      exact hy u hu
    have hprod : (1 / 2 : ℝ) ^ m ≤ ∏ i, ‖u i‖ := by
      have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin m ↦ (1 / 2 : ℝ))
        (g := fun i ↦ ‖u i‖) (fun _ _ ↦ by positivity) (fun i _ ↦ by simpa using hlo i)
      simpa using this
    change ‖(g y - g x) u‖ ≤ η * 2 ^ m * ∏ i, ‖u i‖
    calc ‖(g y - g x) u‖ ≤ η := h1.le
      _ = η * 2 ^ m * (1 / 2) ^ m := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ η * 2 ^ m * ∏ i, ‖u i‖ := by gcongr
  · have : η * 2 ^ m = ε / 2 := by
      simp only [η]
      field_simp
    rw [this]
    exact half_lt_self hε

/-- The main induction in finite dimensions: if `(x, v) ↦ g x v` is `C^k` in the sense of
Michal–Bastiani, then `g : U → L^m(E; F)` is Fréchet `C^k` (no derivative is lost). -/
theorem contDiffOn_of_unc_of_finiteDimensional : ∀ (k m : ℕ)
    {g : E → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F} {U : Set E}, IsOpen U →
    ContDiffMBOn k (unc g) (U ×ˢ univ) → ContDiffOn ℝ k g U := by
  intro k
  induction k with
  | zero =>
    intro m g U hU hg
    rw [Nat.cast_zero, contDiffOn_zero]
    exact continuousOn_of_unc hU hg
  | succ k ih =>
    intro m g U hU hg
    have hg1 : ContDiffMBOn 1 (unc g) (U ×ˢ univ) := hg.of_le (by omega)
    classical
    -- the second derivative as a continuous multilinear map
    let Bc : E → ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ E) F := fun y ↦
      if hy : y ∈ U then
        (secondBML hU hg1 hy).mkContinuous (secondB_bound hU hg1 hy).choose_spec.2.choose
          fun u ↦ ((secondB_bound hU hg1 hy).choose_spec.2.choose_spec.2 y
            (by simpa using (secondB_bound hU hg1 hy).choose_spec.1)).2 u
      else 0
    have hBc : ∀ y ∈ U, ∀ u, Bc y u = secondB g y u := fun y hy u ↦ by
      simp only [Bc, hy, ↓reduceDIte]
      rfl
    -- its uncurried version is `C^k`
    have hBcMB : ContDiffMBOn k (unc Bc) (U ×ˢ univ) := by
      let P := Fin (m + 1) → E
      let Λ : E × P →L[ℝ] (E × (Fin m → E)) × (E × (Fin m → E)) :=
        ((ContinuousLinearMap.fst ℝ E P).prod
          ((ContinuousLinearMap.pi fun j : Fin m ↦ ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (m + 1) ↦ E) j.succ).comp (ContinuousLinearMap.snd ℝ E P))).prod
          (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) ↦ E) 0).comp
            (ContinuousLinearMap.snd ℝ E P)).prod 0)
      have h2 : ContDiffMBOn k (dMB (unc g)) ((U ×ˢ univ) ×ˢ univ) := hg.2.2
      have h3 := ContDiffMBOn.comp_clm Λ ((hU.prod isOpen_univ).prod isOpen_univ) h2
      have hpre : Λ ⁻¹' ((U ×ˢ univ) ×ˢ univ) = U ×ˢ univ := by ext p; simp [Λ]
      rw [hpre] at h3
      refine ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) (fun p hp ↦ ?_) h3
      simp only [Function.comp_apply, unc]
      rw [hBc p.1 hp.1]
      rfl
    have hBcC : ContDiffOn ℝ k Bc U := ih (m + 1) hU hBcMB
    -- the candidate derivative
    let D : E → E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F := fun y ↦
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F (Bc y)
    have hDapply : ∀ y w V, D y w V = Bc y (Fin.cons w V) := fun _ _ _ ↦ rfl
    have hder : ∀ y ∈ U, HasFDerivAt g (D y) y := by
      intro y hy
      refine HasFDerivAt.of_isLittleO (Asymptotics.isLittleO_iff.mpr fun c hc ↦ ?_)
      have hcont : ContinuousAt Bc y :=
        (hBcC.continuousOn.continuousAt (hU.mem_nhds hy))
      have hev : ∀ᶠ p in 𝓝 y, p ∈ U ∧ ‖Bc p - Bc y‖ ≤ c := by
        refine (hU.eventually_mem hy).and ?_
        have := Metric.continuousAt_iff.mp hcont c hc
        obtain ⟨δ, hδ, hδ'⟩ := this
        filter_upwards [Metric.ball_mem_nhds y hδ] with p hp
        exact (by simpa [dist_eq_norm] using hδ' hp : ‖Bc p - Bc y‖ < c).le
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
      filter_upwards [Metric.ball_mem_nhds y hδ] with z hz
      have hz' : ‖z - y‖ < δ := by simpa [dist_eq_norm] using hz
      have hseg : ∀ s ∈ Icc (0 : ℝ) 1, dist (y + s • (z - y)) y < δ := fun s hs ↦ by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
        calc s * ‖z - y‖ ≤ 1 * ‖z - y‖ := by gcongr; exact hs.2
          _ < δ := by simpa using hz'
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun V ↦ ?_
      let ℓ : E →L[ℝ] F := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ E) F V).comp (D y)
      have hℓ : ∀ q, ℓ q = Bc y (Fin.cons q V) := fun q ↦ rfl
      have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt (fun q ↦ g q V - ℓ q) (y + s • (z - y))
          (z - y) (secondB g (y + s • (z - y)) (Fin.cons (z - y) V) - ℓ (z - y)) :=
        fun s hs ↦ (hasDirDerivAt_unc_base hg1 (hδ' (hseg s hs)).1 V (z - y)).sub
          (ℓ.hasDirDerivAt _ _)
      have hDc : ContinuousOn (fun s : ℝ ↦
          secondB g (y + s • (z - y)) (Fin.cons (z - y) V) - ℓ (z - y)) (Icc 0 1) :=
        ((continuousOn_secondB hg1).comp
          (by fun_prop : Continuous fun s : ℝ ↦
            (y + s • (z - y), (Fin.cons (z - y) V : Fin (m + 1) → E))).continuousOn
          fun s hs ↦ ⟨(hδ' (hseg s hs)).1, mem_univ _⟩).sub continuousOn_const
      have hmem := sub_mem_of_hasDirDerivAt hd hDc
        (convex_closedBall 0 (c * ‖z - y‖ * ∏ i, ‖V i‖)) Metric.isClosed_closedBall
        (fun s hs ↦ by
          have hp := hδ' (hseg s hs)
          rw [mem_closedBall_zero_iff, hℓ, ← hBc _ hp.1, ← sub_apply]
          refine ((Bc _ - Bc y).le_opNorm _).trans ?_
          rw [norm_prod_cons]
          calc ‖Bc (y + s • (z - y)) - Bc y‖ * (‖z - y‖ * ∏ i, ‖V i‖)
              ≤ c * (‖z - y‖ * ∏ i, ‖V i‖) := by gcongr; exact hp.2
            _ = c * ‖z - y‖ * ∏ i, ‖V i‖ := by ring)
      rw [mem_closedBall_zero_iff, add_sub_cancel] at hmem
      have e : (g z - g y - D y (z - y)) V = g z V - ℓ z - (g y V - ℓ y) := by
        simp only [map_sub, sub_apply]
        change _ - _ - (ℓ z - ℓ y) = _
        abel
      calc ‖(g z - g y - D y (z - y)) V‖ = ‖g z V - ℓ z - (g y V - ℓ y)‖ := by rw [e]
        _ ≤ c * ‖z - y‖ * ∏ i, ‖V i‖ := hmem
    have hfd : EqOn (fderiv ℝ g) D U := fun y hy ↦ (hder y hy).fderiv
    have hDC : ContDiffOn ℝ k D U :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).contDiff.comp_contDiffOn
        hBcC
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨fun y hy ↦ (hder y hy).differentiableAt.differentiableWithinAt, by simp,
      hDC.congr hfd⟩

/-- **In finite dimensions, Michal–Bastiani `C^k` maps are Fréchet `C^k`**, with no loss of
derivatives. -/
theorem ContDiffMBOn.contDiffOn_of_finiteDimensional {k : ℕ} {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffMBOn k f U) : ContDiffOn ℝ k f U := by
  let g : E → ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) F := fun x ↦
    (continuousMultilinearCurryFin0 ℝ E F).symm (f x)
  have hg : ContDiffMBOn k (unc g) (U ×ˢ univ) := by
    have h := ContDiffMBOn.comp_clm (ContinuousLinearMap.fst ℝ E (Fin 0 → E)) hU hf
    have hpre : (ContinuousLinearMap.fst ℝ E (Fin 0 → E)) ⁻¹' U = U ×ˢ univ := by ext; simp
    rw [hpre] at h
    exact ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) (fun p _ ↦ rfl) h
  have := (continuousMultilinearCurryFin0 ℝ E F).contDiff.comp_contDiffOn
    (contDiffOn_of_unc_of_finiteDimensional k 0 hU hg)
  refine this.congr fun x _ ↦ ?_
  simp [g]

/-- **Michal–Bastiani and Fréchet `C^k` agree on open subsets of finite-dimensional spaces.** -/
theorem contDiffMBOn_iff_contDiffOn {k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U) :
    ContDiffMBOn k f U ↔ ContDiffOn ℝ k f U :=
  ⟨ContDiffMBOn.contDiffOn_of_finiteDimensional hU, ContDiffOn.contDiffMBOn hU⟩

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MichalBastiani

/-!
# Michal–Bastiani `C^{k+1}` maps between normed spaces are Fréchet `C^k`

This is [GN26, Proposition 2.3.17(b)]. The proof there goes through the compact-open topology on
`L(E, F)` and the exponential law (Theorem 1.7.30). Here we give a proof that stays in normed
spaces: derivatives are tracked as continuous multilinear maps with the operator norm. We show, by
induction on `k` and for all `m` simultaneously:

> if `g : U → L^m(E; F)` is such that `(x, v₁, …, vₘ) ↦ g x (v₁, …, vₘ)` is `C^{k+1}` in the
> sense of Michal–Bastiani, then `g` is Fréchet `C^k`.

The derivative of `g` is `curryLeft ∘ B`, where `B y (w, v) = d(ĝ)((y, v), (w, 0))` is
`(m + 1)`-multilinear and is handled by the case `(k, m + 1)`. For `m = 0` we get the result for
maps `f : U → F`.

## Main definitions

* `unc g`: the uncurried map `ĝ (x, v) = g x v` of `g : E → L^m(E; F)`.
* `secondB g y`: the map `B y (w, v) = d(ĝ)((y, v), (w, 0))`, the derivative of `ĝ` in the base
  direction; for `y ∈ U`, `secondBML` is the same map as an `(m + 1)`-multilinear map.

## Main results

* `contDiffOn_of_unc`: if `ĝ` is `C^{k+1}` in the sense of Michal–Bastiani on `U × E^m`, then
  `g : U → L^m(E; F)` is Fréchet `C^k`.
* `ContDiffMBOn.contDiffOn`: `C^{k+1}` maps in the sense of Michal–Bastiani between open subsets
  of normed spaces are Fréchet `C^k` ([GN26, Proposition 2.3.17(b)]).
* `smoothMBOn_iff_contDiffOn`: smoothness in the sense of Michal–Bastiani and in the sense of
  Fréchet agree on open subsets of normed spaces.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The uncurried version `(x, v) ↦ g x v` of `g : E → L^m(E; F)`. -/
def unc {m : ℕ} (g : E → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F) :
    E × (Fin m → E) → F :=
  fun p ↦ g p.1 p.2

/-- `B y u = d(ĝ)((y, tail u), (u 0, 0))`: the derivative of `ĝ` in the base direction `u 0`. -/
def secondB {m : ℕ} (g : E → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F) (y : E)
    (u : Fin (m + 1) → E) : F :=
  dMB (unc g) ((y, Fin.tail u), (u 0, 0))

section Structure

variable {m : ℕ} {g : E → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F}

theorem unc_line (y w : E) (V : Fin m → E) (t : ℝ) :
    unc g ((y, V) + t • (w, (0 : Fin m → E))) = g (y + t • w) V := by
  simp [unc]

theorem hasDirDerivAt_unc_add {y w : E} {V V₁ V₂ : Fin m → E} {a b : F}
    (h : ∀ z, g z V = g z V₁ + g z V₂) (h₁ : HasDirDerivAt (unc g) (y, V₁) (w, 0) a)
    (h₂ : HasDirDerivAt (unc g) (y, V₂) (w, 0) b) :
    HasDirDerivAt (unc g) (y, V) (w, 0) (a + b) := by
  refine (Filter.Tendsto.add h₁ h₂).congr fun t ↦ ?_
  simp only [unc_line]
  simp only [unc, h, ← smul_add]
  congr 1
  abel

theorem hasDirDerivAt_unc_smul {y w : E} {V V₁ : Fin m → E} {a : F} (c : ℝ)
    (h : ∀ z, g z V = c • g z V₁) (h₁ : HasDirDerivAt (unc g) (y, V₁) (w, 0) a) :
    HasDirDerivAt (unc g) (y, V) (w, 0) (c • a) := by
  refine (h₁.const_smul c).congr fun t ↦ ?_
  simp only [unc_line]
  simp only [unc, h, smul_sub, smul_comm c t⁻¹]

variable {U : Set E}

/-- For `y ∈ U`, `secondB g y` is `(m + 1)`-multilinear. -/
def secondBML (hU : IsOpen U) (hg : ContDiffMBOn 1 (unc g) (U ×ˢ univ)) {y : E} (hy : y ∈ U) :
    MultilinearMap ℝ (fun _ : Fin (m + 1) ↦ E) F where
  toFun := secondB g y
  map_update_add' := by
    intro inst u i a b
    obtain rfl : inst = instDecidableEqFin (m + 1) := Subsingleton.elim _ _
    have hd : ∀ (V : Fin m → E) (w : E),
        HasDirDerivAt (unc g) (y, V) (w, 0) (dMB (unc g) ((y, V), (w, 0))) :=
      fun V w ↦ hg.2.1 _ ⟨hy, mem_univ _⟩ _
    cases i using Fin.cases with
    | zero =>
      simp only [secondB, Fin.tail_update_zero, Function.update_self]
      rw [show ((a + b, 0) : E × (Fin m → E)) = (a, 0) + (b, 0) by simp]
      exact hg.dMB_add (hU.prod isOpen_univ) ⟨hy, mem_univ _⟩ _ _
    | succ j =>
      simp only [secondB, Fin.tail_update_succ,
        Function.update_of_ne (Fin.succ_ne_zero j).symm]
      exact (hasDirDerivAt_unc_add (fun z ↦ (g z).map_update_add _ _ _ _)
        (hd _ _) (hd _ _)).dMB_eq
  map_update_smul' := by
    intro inst u i c a
    obtain rfl : inst = instDecidableEqFin (m + 1) := Subsingleton.elim _ _
    cases i using Fin.cases with
    | zero =>
      simp only [secondB, Fin.tail_update_zero, Function.update_self]
      rw [show ((c • a, 0) : E × (Fin m → E)) = c • (a, 0) by simp]
      exact hg.dMB_smul ⟨hy, mem_univ _⟩ _ _
    | succ j =>
      simp only [secondB, Fin.tail_update_succ,
        Function.update_of_ne (Fin.succ_ne_zero j).symm]
      exact (hasDirDerivAt_unc_smul c (fun z ↦ (g z).map_update_smul _ _ _ _)
        (hg.2.1 _ ⟨hy, mem_univ _⟩ _)).dMB_eq

theorem secondBML_apply (hU : IsOpen U) (hg : ContDiffMBOn 1 (unc g) (U ×ˢ univ)) {y : E}
    (hy : y ∈ U) (u : Fin (m + 1) → E) : secondBML hU hg hy u = secondB g y u := rfl

theorem continuousOn_secondB (hg : ContDiffMBOn 1 (unc g) (U ×ˢ univ)) :
    ContinuousOn (fun p : E × (Fin (m + 1) → E) ↦ secondB g p.1 p.2) (U ×ˢ univ) := by
  have h0 : ContinuousOn (dMB (unc g)) ((U ×ˢ univ) ×ˢ univ) := hg.2.2
  have hΛ : Continuous fun p : E × (Fin (m + 1) → E) ↦
      ((p.1, Fin.tail p.2), (p.2 0, (0 : Fin m → E))) := by
    unfold Fin.tail; fun_prop
  exact h0.comp hΛ.continuousOn fun p hp ↦ ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩

/-- Local uniform bound for `secondB`. -/
theorem secondB_bound (hU : IsOpen U) (hg : ContDiffMBOn 1 (unc g) (U ×ˢ univ)) {x : E}
    (hx : x ∈ U) : ∃ δ > 0, ∃ C ≥ 0, ∀ y, ‖y - x‖ < δ → y ∈ U ∧
      ∀ u, ‖secondB g y u‖ ≤ C * ∏ i, ‖u i‖ := by
  have hzero : secondB g x 0 = 0 := by
    rw [← secondBML_apply hU hg hx]; exact (secondBML hU hg hx).map_zero
  have hc : ContinuousAt (fun p : E × (Fin (m + 1) → E) ↦ secondB g p.1 p.2) (x, 0) :=
    (continuousOn_secondB hg).continuousAt (prod_mem_nhds (hU.mem_nhds hx) univ_mem)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.continuousAt_iff.mp hc 1 one_pos
  obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.mp hU x hx
  set δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  refine ⟨δ, hδ, (2 / δ) ^ (m + 1), by positivity, fun y hy ↦ ?_⟩
  have hyU : y ∈ U := hδ₁U (by
    rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hy (min_le_right _ _))
  refine ⟨hyU, fun u ↦ ?_⟩
  rw [← secondBML_apply hU hg hyU]
  refine (secondBML hU hg hyU).bound_of_shell (ε := fun _ ↦ δ) (c := fun _ ↦ (2 : ℝ))
    (fun _ ↦ hδ) (fun _ ↦ by norm_num) (fun u hlo hhi ↦ ?_) u
  have hlt : ‖secondB g y u‖ < 1 := by
    have := hball (x := (y, u)) (by
      rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, sub_zero]
      refine max_lt (lt_of_lt_of_le hy (min_le_left _ _)) ?_
      refine (pi_norm_lt_iff hδ₀).mpr fun i ↦ lt_of_lt_of_le (hhi i) (min_le_left _ _))
    simpa [hzero] using this
  rw [secondBML_apply]
  have hprod : (δ / 2) ^ (m + 1) ≤ ∏ i, ‖u i‖ := by
    have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin (m + 1) ↦ δ / 2)
      (g := fun i ↦ ‖u i‖) (fun _ _ ↦ by positivity)
      (fun i _ ↦ by simpa using hlo i)
    simpa [div_pow] using this
  calc ‖secondB g y u‖ ≤ 1 := hlt.le
    _ = (2 / δ) ^ (m + 1) * (δ / 2) ^ (m + 1) := by
        rw [← mul_pow]; field_simp; simp
    _ ≤ (2 / δ) ^ (m + 1) * ∏ i, ‖u i‖ := by gcongr

theorem hasDirDerivAt_unc_base (hg : ContDiffMBOn 1 (unc g) (U ×ˢ univ)) {p : E} (hp : p ∈ U)
    (V : Fin m → E) (w : E) :
    HasDirDerivAt (fun z ↦ g z V) p w (secondB g p (Fin.cons w V)) := by
  have := hg.2.1 (p, V) ⟨hp, mem_univ _⟩ (w, 0)
  simp only [secondB, Fin.tail_cons, Fin.cons_zero]
  refine this.congr fun t ↦ ?_
  simp only [unc_line]
  rfl

omit [NormedSpace ℝ E] in
theorem norm_prod_cons (w : E) (V : Fin m → E) :
    ∏ i, ‖(Fin.cons w V : Fin (m + 1) → E) i‖ = ‖w‖ * ∏ i, ‖V i‖ := by
  rw [Fin.prod_univ_succ]
  simp

/-- `g` is locally Lipschitz in the operator norm. -/
theorem lipschitz_of_unc (hU : IsOpen U) (hg : ContDiffMBOn 1 (unc g) (U ×ˢ univ)) {x : E}
    (hx : x ∈ U) : ∃ δ > 0, ∃ C ≥ 0, ∀ y, ‖y - x‖ < δ → y ∈ U ∧ ‖g y - g x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨δ, hδ, C, hC, hb⟩ := secondB_bound hU hg hx
  refine ⟨δ, hδ, C, hC, fun y hy ↦ ⟨(hb y hy).1, ?_⟩⟩
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, ‖x + s • (y - x) - x‖ < δ := fun s hs ↦ by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
    calc s * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact hs.2
      _ < δ := by simpa using hy
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC (norm_nonneg _)) fun V ↦ ?_
  have hφ : Continuous fun s : ℝ ↦
      (x + s • (y - x), (Fin.cons (y - x) V : Fin (m + 1) → E)) := by fun_prop
  have hDc' := (continuousOn_secondB (g := g) hg).comp hφ.continuousOn
    (fun s (hs : s ∈ Icc (0 : ℝ) 1) ↦ ⟨(hb _ (hseg s hs)).1, mem_univ _⟩)
  have hDc : ContinuousOn (fun s : ℝ ↦ secondB g (x + s • (y - x)) (Fin.cons (y - x) V))
      (Icc 0 1) := hDc'
  have hmem := sub_mem_of_hasDirDerivAt (f := fun z ↦ g z V) (z := x) (w := y - x)
    (fun s hs ↦ hasDirDerivAt_unc_base hg (hb _ (hseg s hs)).1 V (y - x)) hDc
    (convex_closedBall 0 (C * ‖y - x‖ * ∏ i, ‖V i‖)) Metric.isClosed_closedBall
    (fun s hs ↦ by
      rw [mem_closedBall_zero_iff]
      refine ((hb _ (hseg s hs)).2 _).trans (le_of_eq ?_)
      rw [norm_prod_cons]; ring)
  rw [mem_closedBall_zero_iff, add_sub_cancel] at hmem
  rw [sub_apply]
  exact hmem

end Structure

/-- The main induction: if `(x, v) ↦ g x v` is `C^{k+1}` in the sense of Michal–Bastiani, then
`g : U → L^m(E; F)` is Fréchet `C^k`. -/
theorem contDiffOn_of_unc : ∀ (k m : ℕ) {g : E → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F}
    {U : Set E}, IsOpen U → ContDiffMBOn (k + 1) (unc g) (U ×ˢ univ) → ContDiffOn ℝ k g U := by
  intro k
  induction k with
  | zero =>
    intro m g U hU hg
    rw [Nat.cast_zero, contDiffOn_zero]
    intro x hx
    obtain ⟨δ, hδ, C, hC, hb⟩ := lipschitz_of_unc hU hg hx
    refine Metric.continuousWithinAt_iff.mpr fun ε hε ↦ ⟨min δ (ε / (C + 1)),
      lt_min hδ (by positivity), fun {y} _ hy ↦ ?_⟩
    rw [dist_eq_norm] at hy ⊢
    calc ‖g y - g x‖ ≤ C * ‖y - x‖ := (hb y (lt_of_lt_of_le hy (min_le_left _ _))).2
      _ ≤ (C + 1) * ‖y - x‖ := by gcongr; linarith
      _ < (C + 1) * (ε / (C + 1)) := by gcongr; exact lt_of_lt_of_le hy (min_le_right _ _)
      _ = ε := by field_simp
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
    -- its uncurried version is `C^{k+1}`
    have hBcMB : ContDiffMBOn (k + 1) (unc Bc) (U ×ˢ univ) := by
      let P := Fin (m + 1) → E
      let Λ : E × P →L[ℝ] (E × (Fin m → E)) × (E × (Fin m → E)) :=
        ((ContinuousLinearMap.fst ℝ E P).prod
          ((ContinuousLinearMap.pi fun j : Fin m ↦ ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin (m + 1) ↦ E) j.succ).comp (ContinuousLinearMap.snd ℝ E P))).prod
          (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) ↦ E) 0).comp
            (ContinuousLinearMap.snd ℝ E P)).prod 0)
      have h2 : ContDiffMBOn (k + 1) (dMB (unc g)) ((U ×ˢ univ) ×ˢ univ) := hg.2.2
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

/-- [GN26, Proposition 2.3.17(b)]: `C^{k+1}` maps in the sense of Michal–Bastiani
between open subsets of normed spaces are Fréchet `C^k`. -/
theorem ContDiffMBOn.contDiffOn {k : ℕ} {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffMBOn (k + 1) f U) : ContDiffOn ℝ k f U := by
  let g : E → ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ E) F := fun x ↦
    (continuousMultilinearCurryFin0 ℝ E F).symm (f x)
  have hg : ContDiffMBOn (k + 1) (unc g) (U ×ˢ univ) := by
    have h := ContDiffMBOn.comp_clm (ContinuousLinearMap.fst ℝ E (Fin 0 → E)) hU hf
    have hpre : (ContinuousLinearMap.fst ℝ E (Fin 0 → E)) ⁻¹' U = U ×ˢ univ := by ext; simp
    rw [hpre] at h
    exact ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ) (fun p _ ↦ rfl) h
  have := (continuousMultilinearCurryFin0 ℝ E F).contDiff.comp_contDiffOn
    (contDiffOn_of_unc k 0 hU hg)
  refine this.congr fun x _ ↦ ?_
  simp [g]

/-- Smoothness in the sense of Michal–Bastiani and Fréchet agree on normed spaces
([GN26, Proposition 2.3.17]). -/
theorem smoothMBOn_iff_contDiffOn {f : E → F} {U : Set E} (hU : IsOpen U) :
    SmoothMBOn f U ↔ ContDiffOn ℝ ∞ f U := by
  rw [contDiffOn_infty]
  exact ⟨fun h k ↦ (h (k + 1)).contDiffOn hU,
    fun h k ↦ ContDiffOn.contDiffMBOn hU (h k)⟩

end LocallyConvex.Analysis

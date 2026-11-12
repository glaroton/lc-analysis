/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MichalBastiani
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Superposition operators with parameters

Reference: [GN26, Proposition 1.7.5], in the form used in the proof of Theorem 2.4.34 (p. 204).

Let `K` be a compact metric space, `E'` and `E` normed spaces, `Z` a real topological vector
space and `Ω ⊆ E' × Z` open. For `H : K × (E' × Z) → E` continuous on `K × Ω` and with
directional derivatives `D(s, x, v)` in the second variable, `D` continuous on `K × Ω × (E' × Z)`,
the superposition operator

  `S(ψ, z) = (s ↦ H(s, ψ(s), z)) : C(K, E') × Z → C(K, E)`

is `C^1` in the sense of Michal–Bastiani on the open set of `(ψ, z)` with `(ψ(s), z) ∈ Ω` for all
`s` (`contDiffMBOn_superposeParam`), with `dS((ψ, z), (η, v)) = (s ↦ D(s, (ψ s, z), (η s, v)))`
(`hasDirDerivAt_superposeParam`).
If moreover `H(s, x) = H̃(κ(s), x)` for a continuous `κ : K → ℝ` and a `C^k` map `H̃` on an open
subset of `ℝ × (E' × Z)`, the superposition operator is `C^k`
(`contDiffMBOn_superposeParam_of_contDiffMBOn`), by induction on `k`: its derivative is again a
superposition operator, read on `C(K, E' × E') × (Z × Z)` through the pairing `pairCLM`.

## Main definitions

* `paramDomain K Ω`: the set of `(ψ, z) ∈ C(K, E') × Z` with `(ψ(s), z) ∈ Ω` for all `s ∈ K`.
* `superposeParam H`: the superposition operator `(ψ, z) ↦ (s ↦ H(s, ψ(s), z))`.
* `superposeParamDeriv D`: the candidate derivative, which sends `((ψ, z), (η, v))` to
  `s ↦ D(s, (ψ s, z), (η s, v))`.
* `pairCLM K A B`: the pairing `C(K, A) × C(K, B) → C(K, A × B)`, a continuous linear map.

## Main results

* `isOpen_paramDomain`: the domain `paramDomain K Ω` is open if `Ω` is.
* `continuousOn_superposeParam`: the superposition operator is continuous.
* `hasDirDerivAt_superposeParam`: `dS((ψ, z), (η, v)) = (s ↦ D(s, (ψ s, z), (η s, v)))`.
* `contDiffMBOn_superposeParam`: superposition operators with parameters are `C^1` (compare
  [GN26, Proposition 1.7.5]).
* `contDiffMBOn_superposeParam_of_contDiffMBOn`: if `H(s, x) = H̃(κ(s), x)` with `κ` continuous
  and `H̃` of class `C^k` on an open set containing `κ(K) × Ω`, the superposition operator is
  `C^k` (compare [GN26, Proposition 1.7.5]).

## Proof

The difference quotients converge uniformly in `s ∈ K`: by the mean value inequality, their
distance to `D(s, x_s, d_s)` (with `x_s = (ψ s, z)`, `d_s = (η s, v)`) is bounded by the
oscillation of `u ↦ D(s, x_s + u d_s, d_s)` on `[0, t]`, which is uniformly small by uniform
continuity on the compact set `K × [-δ, δ]`. Continuity of `S` and of `dS` follows from the
joint continuity of `H` and `D` and compactness of `K` (the curried map of a jointly continuous map
is continuous for the compact-open topology).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

variable {K : Type*} [MetricSpace K] [CompactSpace K]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {Z : Type*} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pairs `(ψ, z) ∈ C(K, E') × Z` with `(ψ(s), z) ∈ Ω` for all `s ∈ K`. -/
def paramDomain (K : Type*) [TopologicalSpace K] (Ω : Set (E' × Z)) : Set (C(K, E') × Z) :=
  {q | ∀ s, (q.1 s, q.2) ∈ Ω}

omit [NormedSpace ℝ E'] [AddCommGroup Z] [Module ℝ Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  in
/-- The domain of a superposition operator is open. -/
theorem isOpen_paramDomain {Ω : Set (E' × Z)} (hΩ : IsOpen Ω) : IsOpen (paramDomain K Ω) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hc : Continuous fun r : (C(K, E') × Z) × K ↦ (r.1.1 r.2, r.1.2) :=
    (ContinuousEval.continuous_eval.comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
      (continuous_snd.comp continuous_fst)
  have : ∀ s ∈ (univ : Set K), ∀ᶠ r : (C(K, E') × Z) × K in 𝓝 (q, s), (r.1.1 r.2, r.1.2) ∈ Ω :=
    fun s _ ↦ (hc.tendsto (q, s)).eventually (hΩ.mem_nhds (hq s))
  have h := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun (q' : C(K, E') × Z) (s : K) ↦ (q'.1 s, q'.2) ∈ Ω) this
  filter_upwards [h] with q' hq' s using hq' s (mem_univ s)

open Classical in
/-- The map `s ↦ G(s, a)` as an element of `C(K, E)` (`0` if it is not continuous). -/
def curryMap {A : Type*} (G : K × A → E) (a : A) : C(K, E) :=
  if h : Continuous fun s ↦ G (s, a) then ⟨fun s ↦ G (s, a), h⟩ else 0

omit [CompactSpace K] [NormedSpace ℝ E] in
theorem curryMap_apply {A : Type*} {G : K × A → E} {a : A} (h : Continuous fun s ↦ G (s, a))
    (s : K) : curryMap G a s = G (s, a) := by
  simp [curryMap, h]

omit [CompactSpace K] [NormedSpace ℝ E] in
/-- The curried map of a map continuous on `K × A'` is continuous on `A'` into `C(K, E)`. -/
theorem continuousOn_curryMap {A : Type*} [TopologicalSpace A] {G : K × A → E} {A' : Set A}
    (hG : ContinuousOn G (univ ×ˢ A')) : ContinuousOn (curryMap G) A' := by
  have hc : Continuous fun p : A' × K ↦ G (p.2, p.1) :=
    hG.comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      fun p ↦ ⟨mem_univ _, p.1.2⟩
  let G' : C(A' × K, E) := ⟨fun p ↦ G (p.2, p.1), hc⟩
  rw [continuousOn_iff_continuous_domRestrict]
  refine G'.curry.continuous.congr fun a ↦ ?_
  have ha : Continuous fun s ↦ G (s, (a : A)) := (G'.curry a).continuous
  ext s
  rw [domRestrict_apply, curryMap_apply ha]
  rfl

/-- The **superposition operator** `(ψ, z) ↦ (s ↦ H(s, ψ(s), z))`. -/
def superposeParam (H : K × (E' × Z) → E) (q : C(K, E') × Z) : C(K, E) :=
  curryMap (fun r : K × (C(K, E') × Z) ↦ H (r.1, (r.2.1 r.1, r.2.2))) q

/-- The candidate derivative `(s ↦ D(s, (ψ s, z), (η s, v)))`. -/
def superposeParamDeriv (D : K × ((E' × Z) × (E' × Z)) → E)
    (r : (C(K, E') × Z) × (C(K, E') × Z)) : C(K, E) :=
  curryMap (fun u : K × ((C(K, E') × Z) × (C(K, E') × Z)) ↦
    D (u.1, ((u.2.1.1 u.1, u.2.1.2), (u.2.2.1 u.1, u.2.2.2)))) r

variable {Ω : Set (E' × Z)} {H : K × (E' × Z) → E} {D : K × ((E' × Z) × (E' × Z)) → E}

omit [NormedSpace ℝ E'] [AddCommGroup Z] [Module ℝ Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  in
theorem continuous_paramEval : Continuous fun r : K × (C(K, E') × Z) ↦ (r.2.1 r.1, r.2.2) :=
  (ContinuousEval.continuous_eval.comp ((continuous_fst.comp continuous_snd).prodMk
    continuous_fst)).prodMk (continuous_snd.comp continuous_snd)

omit [NormedSpace ℝ E'] [AddCommGroup Z] [Module ℝ Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  [CompactSpace K] [NormedSpace ℝ E] in
theorem superposeParam_apply (hH : ContinuousOn H (univ ×ˢ Ω)) {q : C(K, E') × Z}
    (hq : q ∈ paramDomain K Ω) (s : K) : superposeParam H q s = H (s, (q.1 s, q.2)) :=
  curryMap_apply (G := fun r : K × (C(K, E') × Z) ↦ H (r.1, (r.2.1 r.1, r.2.2)))
    (hH.comp_continuous (continuous_id.prodMk (q.1.continuous.prodMk (continuous_const (y := q.2))))
      fun s ↦ ⟨mem_univ _, hq s⟩) s

omit [NormedSpace ℝ E'] [AddCommGroup Z] [Module ℝ Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  [NormedSpace ℝ E] in
/-- The superposition operator is continuous. -/
theorem continuousOn_superposeParam (hH : ContinuousOn H (univ ×ˢ Ω)) :
    ContinuousOn (superposeParam H) (paramDomain K Ω) :=
  continuousOn_curryMap (hH.comp (continuous_fst.prodMk continuous_paramEval).continuousOn
    fun r hr ↦ ⟨mem_univ _, hr.2 r.1⟩)

omit [NormedSpace ℝ E'] [AddCommGroup Z] [Module ℝ Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z]
  [CompactSpace K] [NormedSpace ℝ E] in
theorem superposeParamDeriv_apply (hD : ContinuousOn D (univ ×ˢ (Ω ×ˢ univ)))
    {q : C(K, E') × Z} (hq : q ∈ paramDomain K Ω) (w : C(K, E') × Z) (s : K) :
    superposeParamDeriv D (q, w) s = D (s, ((q.1 s, q.2), (w.1 s, w.2))) :=
  curryMap_apply (G := fun u : K × ((C(K, E') × Z) × (C(K, E') × Z)) ↦
      D (u.1, ((u.2.1.1 u.1, u.2.1.2), (u.2.2.1 u.1, u.2.2.2))))
    (hD.comp_continuous (continuous_id.prodMk ((q.1.continuous.prodMk
      (continuous_const (y := q.2))).prodMk (w.1.continuous.prodMk (continuous_const (y := w.2)))))
      fun s ↦ ⟨mem_univ _, hq s, mem_univ _⟩) s

/-- **The derivative of a superposition operator.** -/
theorem hasDirDerivAt_superposeParam (hΩ : IsOpen Ω) (hH : ContinuousOn H (univ ×ˢ Ω))
    (hd : ∀ s, ∀ x ∈ Ω, ∀ v, HasDirDerivAt (fun x ↦ H (s, x)) x v (D (s, (x, v))))
    (hD : ContinuousOn D (univ ×ˢ (Ω ×ˢ univ))) {q : C(K, E') × Z}
    (hq : q ∈ paramDomain K Ω) (w : C(K, E') × Z) :
    HasDirDerivAt (superposeParam H) q w (superposeParamDeriv D (q, w)) := by
  -- the base points and directions
  set x : K → E' × Z := fun s ↦ (q.1 s, q.2) with hx_def
  set d : K → E' × Z := fun s ↦ (w.1 s, w.2) with hd_def
  have hxd : Continuous fun r : ℝ × K ↦ x r.2 + r.1 • d r.2 := by
    have h1 : Continuous fun r : ℝ × K ↦ x r.2 :=
      (q.1.continuous.comp continuous_snd).prodMk continuous_const
    have h2 : Continuous fun r : ℝ × K ↦ d r.2 :=
      (w.1.continuous.comp continuous_snd).prodMk continuous_const
    exact h1.add (continuous_fst.smul h2)
  -- Step 1: a uniform `δ` with `x_s + u d_s ∈ Ω` for `|u| < δ`
  obtain ⟨δ, hδ, hδΩ⟩ : ∃ δ > 0, ∀ u : ℝ, |u| < δ → ∀ s, x s + u • d s ∈ Ω := by
    have : ∀ s ∈ (univ : Set K), ∀ᶠ r : ℝ × K in 𝓝 (0, s), x r.2 + r.1 • d r.2 ∈ Ω :=
      fun s _ ↦ (hxd.tendsto (0, s)).eventually (hΩ.mem_nhds (by simpa [hx_def] using hq s))
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun (u : ℝ) (s : K) ↦ x s + u • d s ∈ Ω) this
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h
    exact ⟨δ, hδ, fun u hu s ↦ hδ' (by simpa [Real.dist_eq] using hu) s (mem_univ s)⟩
  -- the derivatives along the segments
  set Δ : K × ℝ → E := fun r ↦ D (r.1, (x r.1 + r.2 • d r.1, d r.1)) with hΔ_def
  have hΔc : ContinuousOn Δ (univ ×ˢ Icc (-(δ / 2)) (δ / 2)) := by
    refine hD.comp (continuous_fst.prodMk ((hxd.comp continuous_swap).prodMk
      ((w.1.continuous.comp continuous_fst).prodMk continuous_const))).continuousOn ?_
    rintro ⟨s, u⟩ ⟨-, hu⟩
    refine ⟨mem_univ _, hδΩ u ?_ s, mem_univ _⟩
    rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
  have hderiv : ∀ s, ∀ u : ℝ, |u| < δ →
      HasDerivAt (fun u ↦ H (s, x s + u • d s)) (Δ (s, u)) u := by
    intro s u hu
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine (hd s _ (hδΩ u hu s) (d s)).congr fun t ↦ ?_
    simp only [add_smul, add_assoc]
  -- Steps 2–4: uniform convergence of the difference quotients
  rw [HasDirDerivAt, Metric.tendsto_nhds]
  intro ε hε
  have huc := (isCompact_univ.prod isCompact_Icc).uniformContinuousOn_of_continuous hΔc
  obtain ⟨η, hη, hηΔ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < min (δ / 2) η ∧ t ≠ 0 := by
    exact (((continuous_abs.tendsto' 0 0 abs_zero).eventually
      (gt_mem_nhds (by positivity))).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  filter_upwards [hev] with t ht
  obtain ⟨htδ, ht0⟩ := ht
  have htδ' : |t| < δ / 2 := htδ.trans_le (min_le_left _ _)
  have htη : |t| < η := htδ.trans_le (min_le_right _ _)
  have hqt : q + t • w ∈ paramDomain K Ω := fun s ↦ by
    simpa [hx_def, hd_def] using hδΩ t (by linarith) s
  refine lt_of_le_of_lt ((ContinuousMap.dist_le (by positivity)).2 fun s ↦ ?_) (half_lt_self hε)
  rw [ContinuousMap.smul_apply, ContinuousMap.sub_apply, superposeParam_apply hH hqt,
    superposeParam_apply hH hq, superposeParamDeriv_apply hD hq]
  have hpt : ((q + t • w).1 s, (q + t • w).2) = x s + t • d s := by
    simp [hx_def, hd_def]
  rw [hpt]
  -- the mean value inequality on `[0, t]`
  set g : ℝ → E := fun u ↦ H (s, x s + u • d s) - u • Δ (s, 0)
  have hg : ∀ u ∈ uIcc 0 t, HasDerivWithinAt g (Δ (s, u) - Δ (s, 0)) (uIcc 0 t) u := by
    intro u hu
    have hu' : |u| ≤ |t| := by simpa using abs_sub_left_of_mem_uIcc hu
    exact ((hderiv s u (by linarith)).sub
      ((hasDerivAt_id u).smul_const (Δ (s, 0)))).hasDerivWithinAt.congr_deriv (by simp)
  have hbound : ∀ u ∈ uIcc 0 t, ‖Δ (s, u) - Δ (s, 0)‖ ≤ ε / 2 := by
    intro u hu
    have hu' : |u| ≤ |t| := by simpa using abs_sub_left_of_mem_uIcc hu
    have hmem : ∀ v : ℝ, |v| < δ / 2 → (s, v) ∈ (univ : Set K) ×ˢ Icc (-(δ / 2)) (δ / 2) :=
      fun v hv ↦ ⟨mem_univ _, by rw [abs_lt] at hv; constructor <;> linarith [hv.1, hv.2]⟩
    have := hηΔ (s, u) (hmem u (by linarith)) (s, 0) (hmem 0 (by rw [abs_zero]; positivity))
      (by simpa [Prod.dist_eq, Real.dist_eq] using lt_of_le_of_lt hu' htη)
    rw [dist_eq_norm] at this
    exact this.le
  have hmv := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hg hbound
    left_mem_uIcc right_mem_uIcc
  simp only [g, zero_smul, sub_zero, add_zero] at hmv
  rw [dist_eq_norm]
  have hrew : t⁻¹ • (H (s, x s + t • d s) - H (s, x s)) - D (s, ((q.1 s, q.2), (w.1 s, w.2))) =
      t⁻¹ • (H (s, x s + t • d s) - t • Δ (s, 0) - H (s, x s)) := by
    simp only [hΔ_def, zero_smul, add_zero, smul_sub, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    abel
  rw [hrew, norm_smul, norm_inv, Real.norm_eq_abs]
  calc |t|⁻¹ * ‖H (s, x s + t • d s) - t • Δ (s, 0) - H (s, x s)‖
      ≤ |t|⁻¹ * (ε / 2 * ‖t‖) := by gcongr
    _ = ε / 2 := by
        rw [Real.norm_eq_abs]
        field_simp

/-- **Superposition operators with parameters are `C^1`** (compare
[GN26, Proposition 1.7.5]). -/
theorem contDiffMBOn_superposeParam (hΩ : IsOpen Ω) (hH : ContinuousOn H (univ ×ˢ Ω))
    (hd : ∀ s, ∀ x ∈ Ω, ∀ v, HasDirDerivAt (fun x ↦ H (s, x)) x v (D (s, (x, v))))
    (hD : ContinuousOn D (univ ×ˢ (Ω ×ˢ univ))) :
    ContDiffMBOn 1 (superposeParam H) (paramDomain K Ω) := by
  have hder := fun q (hq : q ∈ paramDomain K Ω) w ↦
    hasDirDerivAt_superposeParam hΩ hH hd hD hq w
  have hcD : ContinuousOn (superposeParamDeriv D) (paramDomain K Ω ×ˢ univ) :=
    have h1 := continuous_paramEval.comp (continuous_fst.prodMk
      (continuous_fst.comp continuous_snd) :
        Continuous fun u : K × ((C(K, E') × Z) × (C(K, E') × Z)) ↦ (u.1, u.2.1))
    have h2 := continuous_paramEval.comp (continuous_fst.prodMk
      (continuous_snd.comp continuous_snd) :
        Continuous fun u : K × ((C(K, E') × Z) × (C(K, E') × Z)) ↦ (u.1, u.2.2))
    continuousOn_curryMap (hD.comp (continuous_fst.prodMk (h1.prodMk h2)).continuousOn
      fun r hr ↦ ⟨mem_univ _, hr.2.1 r.1, mem_univ _⟩)
  refine ⟨continuousOn_superposeParam hH, fun q hq w ↦ ?_, ?_⟩
  · rw [(hder q hq w).dMB_eq]
    exact hder q hq w
  · exact hcD.congr fun r hr ↦ (hder r.1 hr.1 r.2).dMB_eq


/-! ### `C^k` superposition operators -/

section Ck

universe u w

/-- The pairing `C(K, A) × C(K, B) → C(K, A × B)`, a continuous linear map. -/
def pairCLM (K : Type*) [MetricSpace K] [CompactSpace K] (A B : Type*) [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] :
    C(K, A) × C(K, B) →L[ℝ] C(K, A × B) :=
  LinearMap.mkContinuous
    { toFun := fun r ↦ r.1.prodMk r.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl } 1 fun r ↦ by
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s ↦ ?_
    simp only [Prod.norm_def]
    exact max_le_max (r.1.norm_coe_le_norm s) (r.2.norm_coe_le_norm s)

@[simp] theorem pairCLM_apply {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (r : C(K, A) × C(K, B)) (s : K) :
    pairCLM K A B r s = (r.1 s, r.2 s) := rfl

/-- **Superposition operators with parameters are `C^k`** (compare
[GN26, Proposition 1.7.5]): if `H(s, x) = H̃(κ(s), x)` for a continuous `κ : K → ℝ` and a map `H̃`
which is `C^k` on an open set `O ⊆ ℝ × (E' × Z)` containing `κ(K) × Ω`, the superposition operator
`(ψ, z) ↦ (s ↦ H(s, ψ(s), z))` is `C^k` on the open set of `(ψ, z)` with `(ψ(s), z) ∈ Ω`. By
induction on `k`: its derivative is the superposition operator of `dH̃(·, (0, ·))`, read on
`C(K, E' × E') × (Z × Z)` through the pairing `pairCLM`. -/
theorem contDiffMBOn_superposeParam_of_contDiffMBOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (κ : K → ℝ) (hκ : Continuous κ) :
    ∀ (k : ℕ) {E' : Type u} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Z : Type w}
    [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
    [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z] [T2Space Z] {H : ℝ × (E' × Z) → E}
    {O : Set (ℝ × (E' × Z))} {Ω : Set (E' × Z)}, IsOpen O → IsOpen Ω →
    (∀ s, ∀ x ∈ Ω, (κ s, x) ∈ O) → ContDiffMBOn k H O →
    ContDiffMBOn k (superposeParam fun r : K × (E' × Z) ↦ H (κ r.1, r.2)) (paramDomain K Ω) := by
  intro k
  induction k with
  | zero =>
    intro E' _ _ Z _ _ _ _ _ _ _ H O Ω hO hΩ hκO hH
    exact continuousOn_superposeParam (ContinuousOn.comp (g := H) hH
      ((hκ.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun r (hr : r ∈ (univ : Set K) ×ˢ Ω) ↦ hκO r.1 r.2 hr.2)
  | succ k ih =>
    intro E' _ _ Z _ _ _ _ _ _ _ H O Ω hO hΩ hκO hH
    set H₁ : K × (E' × Z) → E := fun r ↦ H (κ r.1, r.2)
    set D : K × ((E' × Z) × (E' × Z)) → E := fun r ↦ dMB H ((κ r.1, r.2.1), (0, r.2.2))
    have hH₁ : ContinuousOn H₁ (univ ×ˢ Ω) :=
      hH.continuousOn.comp ((hκ.comp continuous_fst).prodMk continuous_snd).continuousOn
        fun r hr ↦ hκO r.1 r.2 hr.2
    have hdH : ContinuousOn (dMB H) (O ×ˢ univ) := hH.2.2.continuousOn
    have hD : ContinuousOn D (univ ×ˢ (Ω ×ˢ univ)) :=
      hdH.comp (((hκ.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)).prodMk
        (continuous_const.prodMk (continuous_snd.comp continuous_snd))).continuousOn
        fun r hr ↦ ⟨hκO r.1 r.2.1 hr.2.1, mem_univ _⟩
    have hd : ∀ s, ∀ x ∈ Ω, ∀ v, HasDirDerivAt (fun x ↦ H₁ (s, x)) x v (D (s, (x, v))) := by
      intro s x hx v
      have := hH.hasDirDerivAt (hκO s x hx) (0, v)
      unfold HasDirDerivAt at this ⊢
      refine this.congr fun t ↦ ?_
      simp only [H₁, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
    have hS1 : ContDiffMBOn 1 (superposeParam H₁) (paramDomain K Ω) :=
      contDiffMBOn_superposeParam (K := K) (H := H₁) (D := D) hΩ hH₁ hd hD
    -- the derivative, as a superposition operator on `C(K, E' × E') × (Z × Z)`
    set H₂ : ℝ × ((E' × E') × (Z × Z)) → E := fun r ↦ dMB H ((r.1, (r.2.1.1, r.2.2.1)),
      (0, (r.2.1.2, r.2.2.2)))
    set O₂ : Set (ℝ × ((E' × E') × (Z × Z))) := {r | (r.1, (r.2.1.1, r.2.2.1)) ∈ O}
    set Ω₂ : Set ((E' × E') × (Z × Z)) := {x | (x.1.1, x.2.1) ∈ Ω}
    set L₂ : ℝ × ((E' × E') × (Z × Z)) →L[ℝ] (ℝ × (E' × Z)) × (ℝ × (E' × Z)) :=
      ((ContinuousLinearMap.fst ℝ ℝ _).prod
        (((ContinuousLinearMap.fst ℝ E' E') ∘L (ContinuousLinearMap.fst ℝ _ _) ∘L
          (ContinuousLinearMap.snd ℝ ℝ _)).prod
        ((ContinuousLinearMap.fst ℝ Z Z) ∘L (ContinuousLinearMap.snd ℝ _ _) ∘L
          (ContinuousLinearMap.snd ℝ ℝ _)))).prod
      ((0 : ℝ × ((E' × E') × (Z × Z)) →L[ℝ] ℝ).prod
        (((ContinuousLinearMap.snd ℝ E' E') ∘L (ContinuousLinearMap.fst ℝ _ _) ∘L
          (ContinuousLinearMap.snd ℝ ℝ _)).prod
        ((ContinuousLinearMap.snd ℝ Z Z) ∘L (ContinuousLinearMap.snd ℝ _ _) ∘L
          (ContinuousLinearMap.snd ℝ ℝ _))))
    have hL₂ : O₂ = L₂ ⁻¹' (O ×ˢ univ) := by ext; simp [O₂, L₂]
    have hO₂ : IsOpen O₂ := by
      rw [hL₂]
      exact (hO.prod isOpen_univ).preimage L₂.continuous
    have hH₂ : ContDiffMBOn k H₂ O₂ := by
      rw [hL₂]
      exact ContDiffMBOn.comp_clm L₂ (hO.prod isOpen_univ) hH.2.2
    have hΩ₂ : IsOpen Ω₂ :=
      hΩ.preimage ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
    have hS₂ := ih (H := H₂) (O := O₂) (Ω := Ω₂) hO₂ hΩ₂ (fun s x hx ↦ hκO s _ hx) hH₂
    -- compose with the pairing
    set L : (C(K, E') × Z) × (C(K, E') × Z) →L[ℝ] C(K, E' × E') × (Z × Z) :=
      ((pairCLM K E' E') ∘L ((ContinuousLinearMap.fst ℝ _ _).prodMap
        (ContinuousLinearMap.fst ℝ _ _))).prod
      ((ContinuousLinearMap.snd ℝ _ _).prodMap (ContinuousLinearMap.snd ℝ _ _))
    have hLpre : L ⁻¹' paramDomain K Ω₂ = paramDomain K Ω ×ˢ univ := by
      ext r
      simp [L, paramDomain, Ω₂]
    have hcomp := ContDiffMBOn.comp_clm L (isOpen_paramDomain hΩ₂) hS₂
    rw [hLpre] at hcomp
    refine ⟨hS1.continuousOn, hS1.2.1, ContDiffMBOn.congr_of_isOpen
      ((isOpen_paramDomain hΩ).prod isOpen_univ) (fun r hr ↦ ?_) hcomp⟩
    have hdS := hasDirDerivAt_superposeParam (K := K) (H := H₁) (D := D)
      hΩ hH₁ hd hD hr.1 r.2
    rw [hdS.dMB_eq]
    ext s
    have hH₂c : ContinuousOn (fun r : K × ((E' × E') × (Z × Z)) ↦ H₂ (κ r.1, r.2))
        (univ ×ˢ Ω₂) :=
      ContinuousOn.comp (g := H₂) hH₂.continuousOn
        ((hκ.comp continuous_fst).prodMk continuous_snd).continuousOn
        fun r (hr : r ∈ (univ : Set K) ×ˢ Ω₂) ↦ hκO r.1 _ hr.2
    have hLr : L r ∈ paramDomain K Ω₂ := by
      rw [← mem_preimage, hLpre]
      exact hr
    rw [Function.comp_apply, superposeParam_apply hH₂c hLr s, superposeParamDeriv_apply hD hr.1]
    rfl

end Ck

end LocallyConvex.Analysis

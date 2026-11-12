/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.ComplexC1

/-!
# The complex Michal–Bastiani calculus

Reference: [GN26, Definitions 1.2.1] and 1.3.1 over `ℂ` (pp. 30, 37), Lemma 1.4.17 (p. 58) and
Theorem 2.1.12 (p. 134).

## Main definitions

* `HasCDirDerivAt`, `dCMB`, `ContDiffCMBOn`, `SmoothCMBOn`: complex directional derivatives
  `t⁻¹ (f(x + t h) - f(x)) → df(x, h)` as `t → 0` in `ℂ`, and the classes `C^k_ℂ`, `C^∞_ℂ`.

## Main results

* `ContDiffCMBOn.contDiffMBOn`, `ContDiffCMBOn.dMB_smul`: a `C^k_ℂ` map is `C^k_ℝ`, with complex
  linear differentials if `k ≥ 1` (GN 2.1.12, (a) ⇒ (b), (e) ⇒ (f)).
* `ComplexAnalyticOn.contDiffCMBOn`: complex analytic maps are `C^k_ℂ` for every `k`
  (GN 2.1.12, (d) ⇒ (a)).
* `complexAnalyticOn_of_contDiffMBOn_one_of_mackey`: for a Mackey complete target, a real `C^1`
  map with complex linear differentials is complex analytic (GN 2.1.12, (f) ⇒ (d)).
* `contDiffCMBOn_iff`, `smoothCMBOn_iff_holomorphicOn`: for `1 ≤ k ≤ ∞`, `C^k_ℂ` iff `C^k_ℝ`
  with complex linear differentials, without completeness (GN Lemma 1.4.17).
* `tfae_complexAnalyticOn_smoothCMBOn`: (a) ⇔ (b) ⇔ (c) ⇔ (d) for an arbitrary target, and
  `tfae_complexAnalyticOn_of_mackey`: (a)–(f) for a Mackey complete target.

## Method

The complex difference quotients restrict to the real ones, so `dCMB f = dMB f` wherever the
complex derivatives exist, and their complex homogeneity follows by substituting `t ↦ c t`. For
(d) ⇒ (a), the complex derivative of the line map `z ↦ f(x + z h)` at `0` is a complex
directional derivative, and `df` is again complex analytic (`ComplexAnalyticOn.dMB`). For
(f) ⇒ (d), as in `Analytic/ComplexC1.lean`: the line maps are weakly holomorphic, since `ℓ ∘ f` is a
Fréchet differentiable map on an open subset of `ℂ` with complex linear derivative, for every
continuous linear functional `ℓ`; then `CAnalyticOn.of_weak` uses the Mackey completeness.

The converse of Lemma 1.4.17 (`contDiffCMBOn_of_contDiffMBOn`, `contDiffCMBOn_iff`), for every
`k` and without completeness of `F`, rests on `ContDiffMBOn.hasCDirDerivAt`: writing `t = s u`
with `s = |t|`, `|u| = 1`, the real difference quotients converge to `df(x, u h)` uniformly on the
unit circle (Glöckner's lemma and the tube lemma), and multiplication by `u⁻¹` preserves balanced
`0`-neighbourhoods. GN use the mean value theorem instead; we do not claim this argument is new.
The second differential is complex linear in the direction by symmetry
(`ContDiffMBOn.dMB_dMB_smul`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

/-! ### Definitions -/

section Definitions

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- `f` has complex derivative `y` at `x` in the direction `h`:
`t⁻¹ • (f (x + t • h) - f x) → y` as `t → 0` in `ℂ`, `t ≠ 0`. -/
def HasCDirDerivAt (f : E → F) (x h : E) (y : F) : Prop :=
  Tendsto (fun t : ℂ ↦ t⁻¹ • (f (x + t • h) - f x)) (𝓝[≠] 0) (𝓝 y)

/-- The complex directional derivative `df(x)(h)`, as a function on `E × E` (junk value where it
does not exist). -/
def dCMB (f : E → F) (p : E × E) : F :=
  limUnder (𝓝[≠] (0 : ℂ)) fun t : ℂ ↦ t⁻¹ • (f (p.1 + t • p.2) - f p.1)

/-- `C^k_ℂ` maps in the sense of Michal–Bastiani on a set `U` (meant to be open), `k ∈ ℕ`
([GN26, Definitions 1.2.1] and 1.3.1, over `ℂ`). -/
def ContDiffCMBOn : ℕ → ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E],
    (E → F) → Set E → Prop
  | 0, _, _, _, _, f, U => ContinuousOn f U
  | k + 1, _, _, _, _, f, U =>
      ContinuousOn f U ∧ (∀ x ∈ U, ∀ h, HasCDirDerivAt f x h (dCMB f (x, h))) ∧
        ContDiffCMBOn k (dCMB f) (U ×ˢ univ)

/-- `C^∞_ℂ` maps in the sense of Michal–Bastiani. -/
def SmoothCMBOn (f : E → F) (U : Set E) : Prop := ∀ k, ContDiffCMBOn k f U

theorem ContDiffCMBOn.continuousOn {k : ℕ} {f : E → F} {U : Set E} (hf : ContDiffCMBOn k f U) :
    ContinuousOn f U := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

variable [T2Space F]

omit [TopologicalSpace E] in
/-- The complex directional derivative is unique (`F` Hausdorff). -/
theorem HasCDirDerivAt.dCMB_eq {f : E → F} {x h : E} {y : F} (hd : HasCDirDerivAt f x h y) :
    dCMB f (x, h) = y :=
  hd.limUnder_eq

end Definitions

/-! ### Complex derivatives are real derivatives -/

section Real

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F]

omit [TopologicalSpace E] in
/-- A complex directional derivative is a real one. -/
theorem HasCDirDerivAt.hasDirDerivAt {f : E → F} {x h : E} {y : F} (hd : HasCDirDerivAt f x h y) :
    HasDirDerivAt f x h y := by
  have hc : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto' _ _ Complex.ofReal_zero).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun t ht ↦ Complex.ofReal_ne_zero.2 ht⟩
  refine (hd.comp hc).congr fun t ↦ ?_
  simp only [Function.comp_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t⁻¹, RCLike.real_smul_eq_coe_smul (K := ℂ) t h]
  simp

variable [ContinuousSMul ℂ F]

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [Module ℝ F]
  [IsScalarTower ℝ ℂ F] in
/-- **Complex homogeneity** of complex directional derivatives. -/
theorem HasCDirDerivAt.smul_dir {f : E → F} {x h : E} {y : F} (hd : HasCDirDerivAt f x h y)
    (c : ℂ) : HasCDirDerivAt f x (c • h) (c • y) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [HasCDirDerivAt, zero_smul, smul_zero, add_zero, sub_self]
    exact tendsto_const_nhds
  · have hm : Tendsto (fun t : ℂ ↦ t * c) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦
        mul_ne_zero ht hc⟩
      have : Continuous fun t : ℂ ↦ t * c := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ((hd.comp hm).const_smul c).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    rw [Function.comp_apply, smul_smul, mul_smul t c h]
    congr 1
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]

variable [ContinuousSMul ℝ F] [T2Space F]

omit [TopologicalSpace E] [ContinuousSMul ℂ F] [ContinuousSMul ℝ F] in
/-- Where the complex directional derivative exists, it is the real one. -/
theorem HasCDirDerivAt.dMB_eq {f : E → F} {x h : E} {y : F} (hd : HasCDirDerivAt f x h y) :
    dMB f (x, h) = y :=
  hd.hasDirDerivAt.dMB_eq

omit [ContinuousSMul ℂ F] [ContinuousSMul ℝ F] in
/-- **[GN26, Lemma 1.4.17]** (easy direction) **and Theorem 2.1.12, (a) ⇒ (b) and
(e) ⇒ (f)**, the smoothness part: a `C^k_ℂ` map is `C^k_ℝ`, with the same differentials. By
induction on `k`, over all domains. -/
theorem ContDiffCMBOn.contDiffMBOn : ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] {f : E → F} {U : Set E}, IsOpen U →
    ContDiffCMBOn k f U →
    ContDiffMBOn k f U := by
  intro k
  induction k with
  | zero => intro E _ _ _ _ _ _ _ _ _ f U _ hf; exact hf
  | succ k ih =>
    intro E _ _ _ _ _ _ _ _ _ f U hU hf
    have heq : ∀ x ∈ U, ∀ h, dMB f (x, h) = dCMB f (x, h) := fun x hx h ↦
      (hf.2.1 x hx h).dMB_eq
    refine ⟨hf.1, fun x hx h ↦ ?_, ?_⟩
    · rw [heq x hx h]
      exact (hf.2.1 x hx h).hasDirDerivAt
    · exact ContDiffMBOn.congr_of_isOpen (hU.prod isOpen_univ)
        (fun p hp ↦ (heq p.1 hp.1 p.2).symm) (ih (hU.prod isOpen_univ) hf.2.2)

omit [ContinuousSMul ℝ F] in
/-- **[GN26, Theorem 2.1.12], (e) ⇒ (f)**, the linearity part: the differentials of a
`C^1_ℂ` map are complex linear. -/
theorem ContDiffCMBOn.dMB_smul {k : ℕ} {f : E → F} {U : Set E} (hf : ContDiffCMBOn (k + 1) f U)
    {x : E} (hx : x ∈ U) (c : ℂ) (h : E) : dMB f (x, c • h) = c • dMB f (x, h) := by
  have hd := hf.2.1 x hx h
  rw [hd.dMB_eq, (hd.smul_dir c).dMB_eq]

end Real

/-! ### Theorem 2.1.12 -/

section Main

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] continuousSMul_real_of_complex polynormableSpace_complex

/-- The complex derivative of a complex analytic map along a line is its real differential. -/
theorem ComplexAnalyticOn.hasCDirDerivAt {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {f : E → F} {U : Set E} (hf : ComplexAnalyticOn f U)
    (hU : IsOpen U) {x : E} (hx : x ∈ U) (h : E) :
    HasCDirDerivAt f x h (LocallyConvex.Analysis.dMB f (x, h)) := by
  have hg := hf.gateauxAnalyticOn hU x hx h
  have h0 : (0 : ℂ) ∈ {z : ℂ | x + z • h ∈ U} := by simpa using hx
  have hd : HasCDirDerivAt f x h (cDeriv (fun z : ℂ ↦ f (x + z • h)) 0) := by
    refine (hg.hasCDerivAt h0).congr fun t ↦ ?_
    simp
  rwa [hd.dMB_eq]

/-- **[GN26, Theorem 2.1.12], (d) ⇒ (a)**: complex analytic maps are `C^k_ℂ` for every
`k`, without completeness of `F`. By induction on `k`, over all domains, since `df` is again
complex analytic (`ComplexAnalyticOn.dMB`). -/
theorem ComplexAnalyticOn.contDiffCMBOn : ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E]
    [Module ℂ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [T2Space E] {f : E → F} {U : Set E},
    IsOpen U → ComplexAnalyticOn f U → ContDiffCMBOn k f U := by
  intro k
  induction k with
  | zero => intro E _ _ _ _ _ _ _ _ _ f U _ hf; exact hf.1
  | succ k ih =>
    intro E _ _ _ _ _ _ _ _ _ f U hU hf
    have heq : ∀ x ∈ U, ∀ h, dCMB f (x, h) = LocallyConvex.Analysis.dMB f (x, h) := fun x hx h ↦
      (hf.hasCDirDerivAt hU hx h).dCMB_eq
    refine ⟨hf.1, fun x hx h ↦ ?_, ih (hU.prod isOpen_univ)
      ((hf.dMB hU).congr (hU.prod isOpen_univ) fun p hp ↦ (heq p.1 hp.1 p.2).symm)⟩
    rw [heq x hx h]
    exact hf.hasCDirDerivAt hU hx h

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E] {f : E → F} {U : Set E}

omit [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- **[GN26, Theorem 2.1.12], (a) ⇒ (b)**: a `C^∞_ℂ` map is `C^∞_ℝ` with complex linear
differentials. -/
theorem SmoothCMBOn.holomorphicOn (hU : IsOpen U) (hf : SmoothCMBOn f U) : HolomorphicOn f U :=
  ⟨fun k ↦ ContDiffCMBOn.contDiffMBOn k hU (hf k), fun _ hx c h ↦ (hf 1).dMB_smul hx c h⟩

/-- **[GN26, Theorem 2.1.12], (a) ⇔ (b) ⇔ (c) ⇔ (d)**, for an arbitrary (not necessarily
complete) complex locally convex space `F`. -/
theorem tfae_complexAnalyticOn_smoothCMBOn (hU : IsOpen U) :
    List.TFAE [SmoothCMBOn f U, HolomorphicOn f U, ContinuousOn f U ∧ GateauxAnalyticOn f U,
      ComplexAnalyticOn f U] := by
  tfae_have 1 → 2 := SmoothCMBOn.holomorphicOn hU
  tfae_have 2 ↔ 4 := (complexAnalyticOn_iff_holomorphicOn hU).symm
  tfae_have 3 ↔ 4 := (complexAnalyticOn_iff_gateauxAnalyticOn hU).symm
  tfae_have 4 → 1 := fun h k ↦ ComplexAnalyticOn.contDiffCMBOn k hU h
  tfae_finish

/-! ### The converse of Lemma 1.4.17 -/

omit [Module ℝ F] [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] in
/-- `C^k_ℂ` only depends on the values on the open set. -/
theorem ContDiffCMBOn.congr_of_isOpen : ∀ {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {f₁ f₂ : E → F}
    {U : Set E}, IsOpen U → EqOn f₁ f₂ U → ContDiffCMBOn k f₁ U → ContDiffCMBOn k f₂ U := by
  intro k
  induction k with
  | zero => intro E _ _ _ _ _ f₁ f₂ U _ heq hf; exact ContinuousOn.congr hf heq.symm
  | succ k ih =>
    intro E _ _ _ _ _ f₁ f₂ U hU heq hf
    have hd : ∀ x ∈ U, ∀ h, HasCDirDerivAt f₂ x h (dCMB f₁ (x, h)) := by
      intro x hx h
      have hev : ∀ᶠ t : ℂ in 𝓝[≠] 0, x + t • h ∈ U :=
        (((continuous_const.add (continuous_id.smul continuous_const)).tendsto' (0 : ℂ) x
          (by simp)).eventually (hU.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
      refine (hf.2.1 x hx h).congr' ?_
      filter_upwards [hev] with t ht
      rw [heq ht, heq hx]
    have hdeq : EqOn (dCMB f₁) (dCMB f₂) (U ×ˢ univ) := fun p hp ↦
      ((hd p.1 hp.1 p.2).dCMB_eq).symm
    refine ⟨ContinuousOn.congr hf.1 heq.symm, fun x hx h ↦ ?_,
      ih (hU.prod isOpen_univ) hdeq hf.2.2⟩
    rw [← hdeq ⟨hx, mem_univ h⟩]
    exact hd x hx h

/-- **Complex directional derivatives of `C^1_ℝ` maps with complex linear differentials**
([GN26, Lemma 1.4.17], the case `k = 1`). Writing `t = s u` with `s = |t|` and `|u| = 1`,
`t⁻¹ (f(x + t h) - f(x)) - df(x, h) = u⁻¹ (s⁻¹ (f(x + s u h) - f(x)) - df(x, u h))`; the real
difference quotients converge to `df(x, u h)` uniformly in `u` on the compact unit circle
(Glöckner's lemma `ContDiffMBOn.tendsto_quotient` and the tube lemma), and multiplication by `u⁻¹`
preserves balanced `0`-neighbourhoods. GN argue with the mean value theorem instead; we do not
claim this argument is new. -/
theorem ContDiffMBOn.hasCDirDerivAt {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffMBOn 1 f U)
    (hI : ∀ x ∈ U, ∀ (c : ℂ) (h : E), dMB f (x, c • h) = c • dMB f (x, h)) {x : E} (hx : x ∈ U)
    (h : E) : HasCDirDerivAt f x h (dMB f (x, h)) := by
  -- uniform convergence on the unit circle
  have hunif : ∀ V ∈ 𝓝 (0 : F), ∀ᶠ s : ℝ in 𝓝 0, ∀ u ∈ Metric.sphere (0 : ℂ) 1,
      s ≠ 0 → s⁻¹ • (f (x + s • (u • h)) - f x) - dMB f (x, u • h) ∈ V := by
    intro V hV
    refine (isCompact_sphere (0 : ℂ) 1).eventually_forall_of_forall_eventually fun u₀ _ ↦ ?_
    have hφ : Tendsto (fun z : ℝ × ℂ ↦ ((x, z.2 • h, z.1) : E × E × ℝ))
        (𝓝[{z | z.1 ≠ 0}] (0, u₀)) (𝓝[{p | p.2.2 ≠ 0}] (x, u₀ • h, 0)) :=
      tendsto_nhdsWithin_iff.2 ⟨((by fun_prop : Continuous fun z : ℝ × ℂ ↦
        ((x, z.2 • h, z.1) : E × E × ℝ)).tendsto _).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun z hz ↦ hz⟩
    have h1 : Tendsto (fun z : ℝ × ℂ ↦ z.1⁻¹ • (f (x + z.1 • (z.2 • h)) - f x))
        (𝓝[{z | z.1 ≠ 0}] (0, u₀)) (𝓝 (dMB f (x, u₀ • h))) := by
      have hq := ContDiffMBOn.tendsto_quotient (E := E) (F := F) (g := f) (U := U) (y := x)
        (v := u₀ • h) hU hf hx
      exact hq.comp hφ
    have h2 : Tendsto (fun z : ℝ × ℂ ↦ dMB f (x, z.2 • h)) (𝓝[{z | z.1 ≠ 0}] (0, u₀))
        (𝓝 (dMB f (x, u₀ • h))) := by
      have hc : Continuous fun z : ℝ × ℂ ↦ dMB f (x, z.2 • h) :=
        (hf.continuous_dMB hx).comp (continuous_snd.smul continuous_const)
      exact (hc.tendsto ((0 : ℝ), u₀)).mono_left nhdsWithin_le_nhds
    have h3 := (h1.sub h2).eventually (by rwa [sub_self])
    rwa [eventually_nhdsWithin_iff] at h3
  -- conclusion
  rw [HasCDirDerivAt, ← tendsto_sub_nhds_zero_iff]
  intro V₀ hV₀
  rw [mem_map]
  set V := balancedCore ℂ V₀
  have hV : V ∈ 𝓝 (0 : F) := balancedCore_mem_nhds_zero hV₀
  have hnorm : Tendsto (fun t : ℂ ↦ ‖t‖) (𝓝[≠] 0) (𝓝 0) :=
    (continuous_norm.tendsto' _ _ norm_zero).mono_left nhdsWithin_le_nhds
  filter_upwards [hnorm.eventually (hunif V hV), self_mem_nhdsWithin] with t ht (ht0 : t ≠ 0)
  have hs : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht0
  set u : ℂ := t / (‖t‖ : ℂ)
  have hsC : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hu : u ∈ Metric.sphere (0 : ℂ) 1 := by
    simp [u, hs]
  have hu0 : u ≠ 0 := div_ne_zero ht0 hsC
  have htu : t = (‖t‖ : ℂ) * u := by simp only [u]; field_simp
  have key : t⁻¹ • (f (x + t • h) - f x) - dMB f (x, h) =
      u⁻¹ • ((‖t‖)⁻¹ • (f (x + ‖t‖ • (u • h)) - f x) - dMB f (x, u • h)) := by
    have e1 : x + ‖t‖ • (u • h) = x + t • h := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      congr 2
      exact htu.symm
    have hinv : u⁻¹ * ((‖t‖⁻¹ : ℝ) : ℂ) = t⁻¹ :=
      calc _ = ((‖t‖ : ℂ) * u)⁻¹ := by push_cast; rw [mul_inv, mul_comm]
        _ = t⁻¹ := congrArg Inv.inv htu.symm
    have e2 : u⁻¹ • ((‖t‖)⁻¹ • (f (x + t • h) - f x)) = t⁻¹ • (f (x + t • h) - f x) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      congr 1
    rw [hI x hx u h, e1, smul_sub u⁻¹ _ (u • dMB f (x, h)), smul_smul u⁻¹ u, inv_mul_cancel₀ hu0,
      one_smul, e2]
  rw [mem_preimage, key]
  refine balancedCore_subset V₀ ((balancedCore.balanced V₀).smul_mem ?_ (ht u hu hs))
  rw [norm_inv, mem_sphere_zero_iff_norm.1 hu, inv_one]

/-- The second differential of a `C^2_ℝ` map with complex linear differentials is complex linear in
the direction ([GN26, proof of Lemma 1.4.17]): `d²f(x)(h, ·)` is complex linear in `h`,
hence in the other variable by symmetry. -/
theorem ContDiffMBOn.dMB_dMB_smul {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffMBOn 2 f U)
    (hI : ∀ x ∈ U, ∀ (c : ℂ) (h : E), dMB f (x, c • h) = c • dMB f (x, h)) {p : E × E}
    (hp : p ∈ U ×ˢ univ) (c : ℂ) (v : E × E) :
    dMB (dMB f) (p, c • v) = c • dMB (dMB f) (p, v) := by
  obtain ⟨x, h⟩ := p
  obtain ⟨y, k⟩ := v
  have hx : x ∈ U := hp.1
  have hf1 : ContDiffMBOn 1 f U := hf.of_le (by norm_num)
  have hdf1 : ContDiffMBOn 1 (dMB f) (U ×ˢ univ) := hf.2.2
  -- the derivative in the direction `(0, w)` is `df(x, w)`
  have hsplit : ∀ y' w : E, dMB (dMB f) ((x, h), (y', w)) =
      dMB (dMB f) ((x, h), (y', 0)) + dMB f (x, w) := by
    intro y' w
    have h0 : HasDirDerivAt (dMB f) (x, h) (0, w) (dMB f (x, w)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
      simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
      rw [hf1.dMB_add hU hx, hf1.dMB_smul hx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht,
        one_smul]
    rw [show ((y', w) : E × E) = (y', 0) + (0, w) by simp,
      hdf1.dMB_add (hU.prod isOpen_univ) hp, h0.dMB_eq]
  -- complex homogeneity of `df(·, y)` passes to its derivative in the first variable
  have hhom : ∀ y' : E, dMB (dMB f) ((x, c • y'), (h, 0)) = c • dMB (dMB f) ((x, y'), (h, 0)) := by
    intro y'
    have hd := hdf1.2.1 (x, y') ⟨hx, mem_univ _⟩ (h, 0)
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, x + t • h ∈ U :=
      (((continuous_const.add (continuous_id.smul continuous_const)).tendsto' (0 : ℝ) x
        (by simp)).eventually (hU.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
    refine HasDirDerivAt.dMB_eq ((Filter.Tendsto.const_smul hd c).congr' ?_)
    filter_upwards [hev] with t ht
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero]
    rw [hI _ ht, hI _ hx, ← smul_sub, smul_comm]
  rw [Prod.smul_mk, hsplit (c • y) (c • k), hsplit y k, hf.dMB_dMB_symm hU hx, hhom,
    ← hf.dMB_dMB_symm hU hx, hI x hx,
    smul_add]

/-- **[GN26, Lemma 1.4.17]**, the converse direction, for every `k` and without
completeness of `F`: a `C^k_ℝ` map whose differentials are complex linear is `C^k_ℂ`. By induction
on `k`, over all domains; the differential `df` again has complex linear differentials
(`ContDiffMBOn.dMB_dMB_smul`). -/
theorem contDiffCMBOn_of_contDiffMBOn : ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E]
    [Module ℂ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E] [T2Space E] {f : E → F} {U : Set E},
    IsOpen U → ContDiffMBOn k f U →
    (1 ≤ k → ∀ x ∈ U, ∀ (c : ℂ) (h : E), dMB f (x, c • h) = c • dMB f (x, h)) →
    ContDiffCMBOn k f U := by
  intro k
  induction k with
  | zero => intro E _ _ _ _ _ _ _ _ _ f U _ hf _; exact hf
  | succ k ih =>
    intro E _ _ _ _ _ _ _ _ _ f U hU hf hI
    have hI' := hI (by omega)
    have hf1 : ContDiffMBOn 1 f U := hf.of_le (by omega)
    have heq : ∀ x ∈ U, ∀ h, dCMB f (x, h) = dMB f (x, h) := fun x hx h ↦
      (hf1.hasCDirDerivAt hU hI' hx h).dCMB_eq
    refine ⟨hf.1, fun x hx h ↦ ?_, ?_⟩
    · rw [heq x hx h]
      exact hf1.hasCDirDerivAt hU hI' hx h
    · refine ContDiffCMBOn.congr_of_isOpen (hU.prod isOpen_univ)
        (fun p hp ↦ (heq p.1 hp.1 p.2).symm) (ih (hU.prod isOpen_univ) hf.2.2 fun hk p hp c v ↦ ?_)
      exact (hf.of_le (by omega) : ContDiffMBOn 2 f U).dMB_dMB_smul hU hI' hp c v

/-- **[GN26, Lemma 1.4.17]**, for open domains, `k ≥ 1` and arbitrary `F`: a map is
`C^k_ℂ` iff it is `C^k_ℝ` with complex linear differentials. -/
theorem contDiffCMBOn_iff {k : ℕ} (hk : 1 ≤ k) (hU : IsOpen U) :
    ContDiffCMBOn k f U ↔
      ContDiffMBOn k f U ∧ ∀ x ∈ U, ∀ (c : ℂ) (h : E), dMB f (x, c • h) = c • dMB f (x, h) := by
  refine ⟨fun h ↦ ⟨ContDiffCMBOn.contDiffMBOn k hU h, fun x hx c v ↦ ?_⟩,
    fun h ↦ contDiffCMBOn_of_contDiffMBOn k hU h.1 fun _ ↦ h.2⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  exact h.dMB_smul hx c v

/-- **[GN26, Lemma 1.4.17]** for `k = ∞`: `C^∞_ℂ` maps are exactly the `C^∞_ℝ` maps with
complex linear differentials, without completeness of `F`. -/
theorem smoothCMBOn_iff_holomorphicOn (hU : IsOpen U) : SmoothCMBOn f U ↔ HolomorphicOn f U :=
  ⟨SmoothCMBOn.holomorphicOn hU, fun h k ↦ contDiffCMBOn_of_contDiffMBOn k hU (h.1 k) fun _ ↦ h.2⟩

/-- **[GN26, Theorem 2.1.12], (f) ⇒ (d)**: a map into a Mackey complete space which is
real `C^1` (Michal–Bastiani) with complex linear differentials is complex analytic. -/
theorem complexAnalyticOn_of_contDiffMBOn_one_of_mackey [MackeyComplete F] (hU : IsOpen U)
    (hf : ContDiffMBOn 1 f U)
    (hI : ∀ x ∈ U, ∀ h, dMB f (x, Complex.I • h) = Complex.I • dMB f (x, h)) :
    ComplexAnalyticOn f U := by
  refine (complexAnalyticOn_iff_gateauxAnalyticOn hU).2 ⟨hf.continuousOn, fun x _ y ↦ ?_⟩
  set V : Set ℂ := {z | x + z • y ∈ U}
  have hcont : Continuous fun z : ℂ ↦ x + z • y := by fun_prop
  have hV : IsOpen V := hU.preimage hcont
  set ℓ : ℂ → F := fun z ↦ f (x + z • y)
  have hℓc : ContinuousOn ℓ V := hf.continuousOn.comp hcont.continuousOn fun z hz ↦ hz
  -- the line map has directional derivatives
  have hd : ∀ z ∈ V, ∀ w : ℂ, HasDirDerivAt ℓ z w (dMB f (x + z • y, w • y)) := by
    intro z hz w
    refine (hf.hasDirDerivAt hz (w • y)).congr fun t ↦ ?_
    simp only [ℓ, add_smul, smul_assoc, add_assoc]
  have hdc : ContinuousOn (fun p : ℂ × ℂ ↦ dMB f (x + p.1 • y, p.2 • y)) (V ×ˢ univ) :=
    hf.2.2.continuousOn.comp (by fun_prop) fun p hp ↦ ⟨hp.1, mem_univ _⟩
  -- its compositions with continuous linear functionals are complex differentiable
  have hdiff : ∀ φ : F →L[ℂ] ℂ, DifferentiableOn ℂ (φ ∘ ℓ) V := by
    intro φ
    have hdφ : ∀ z ∈ V, ∀ w : ℂ, HasDirDerivAt (φ ∘ ℓ) z w (φ (dMB f (x + z • y, w • y))) :=
      fun z hz w ↦ (hd z hz w).clm_comp φ
    have hφ : ContDiffMBOn 1 (φ ∘ ℓ) V := by
      refine ⟨φ.continuous.comp_continuousOn hℓc, fun z hz w ↦ ?_, ?_⟩
      · rw [(hdφ z hz w).dMB_eq]; exact hdφ z hz w
      · exact (φ.continuous.comp_continuousOn hdc).congr fun p hp ↦ (hdφ p.1 hp.1 p.2).dMB_eq
    intro z hz
    have hF := hφ.hasFDerivAt_of_finiteDimensional hV hz
    have hlin : ∀ (c : ℂ) (w : ℂ), dMBCLM hV hφ hz (c • w) = c • dMBCLM hV hφ hz w := by
      refine map_smul_of_map_I_smul (T := dMBCLM hV hφ hz) (fun v w ↦ map_add _ v w)
        (fun r w ↦ ?_) (fun w ↦ ?_)
      · exact map_smul _ r w
      · simp only [dMBCLM_apply, (hdφ z hz _).dMB_eq, smul_assoc, hI _ hz, map_smul]
    let L : ℂ →L[ℂ] ℂ := (1 : ℂ →L[ℂ] ℂ).smulRight (dMBCLM hV hφ hz 1)
    refine (hasFDerivAt_of_restrictScalars ℝ hF (f' := L) ?_).differentiableAt
      |>.differentiableWithinAt
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply, L]
    rw [← hlin]
    change dMBCLM hV hφ hz (w * 1) = dMBCLM hV hφ hz w
    rw [mul_one]
  exact CAnalyticOn.of_weak hV hℓc hdiff

/-- **[GN26, Theorem 2.1.12]**, all six conditions, for a Mackey complete complex locally
convex space `F`: (a) `C^∞_ℂ`, (b) `C^∞_ℝ` with complex linear differentials, (c) continuous and
Gâteaux analytic, (d) complex analytic, (e) `C^1_ℂ`, (f) `C^1_ℝ` with complex linear
differentials. -/
theorem tfae_complexAnalyticOn_of_mackey [MackeyComplete F] (hU : IsOpen U) :
    List.TFAE [SmoothCMBOn f U, HolomorphicOn f U, ContinuousOn f U ∧ GateauxAnalyticOn f U,
      ComplexAnalyticOn f U, ContDiffCMBOn 1 f U,
      ContDiffMBOn 1 f U ∧ ∀ x ∈ U, ∀ (c : ℂ) (h : E), dMB f (x, c • h) = c • dMB f (x, h)] := by
  tfae_have 1 → 2 := SmoothCMBOn.holomorphicOn hU
  tfae_have 4 → 1 := fun h k ↦ ComplexAnalyticOn.contDiffCMBOn k hU h
  tfae_have 2 ↔ 4 := (complexAnalyticOn_iff_holomorphicOn hU).symm
  tfae_have 3 ↔ 4 := (complexAnalyticOn_iff_gateauxAnalyticOn hU).symm
  tfae_have 1 → 5 := fun h ↦ h 1
  tfae_have 5 → 6 := fun h ↦ ⟨ContDiffCMBOn.contDiffMBOn 1 hU h, fun _ hx c v ↦ h.dMB_smul hx c v⟩
  tfae_have 6 → 4 := fun h ↦
    complexAnalyticOn_of_contDiffMBOn_one_of_mackey hU h.1 fun x hx v ↦ h.2 x hx Complex.I v
  tfae_finish

end Main

end LocallyConvex.Analysis

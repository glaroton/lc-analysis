/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Real
public import LocallyConvexAnalysis.Analytic.HomogeneousSeries

/-! # Identity theorems for analytic maps

The identity theorems of [GN26, Theorems 2.1.16] and
2.2.8, and Proposition 2.2.12, for complex and real analytic maps between locally convex spaces,
without completeness of the target.

## Main results

* `eqOn_of_hasLocalTaylor`: on a connected open set, two smooth maps which are the sums of their
  Taylor series near each point, and whose differentials of all orders agree at one point, agree.
* `ComplexAnalyticOn.eqOn_of_iteratedDMB`, `ComplexAnalyticOn.eqOn_of_eqOn_open`,
  `ComplexAnalyticOn.eqOn_of_eqOn_real`: GN Theorem 2.1.16 (b), (a), (c).
* `RealAnalyticOn.eqOn_of_iteratedDMB`, `RealAnalyticOn.eqOn_of_eqOn_open`: GN Theorem 2.2.8.
* `ComplexAnalyticOn.eqOn_of_eqOn_ofReal`: complex analytic extensions of real analytic maps are
  unique on connected domains.
* `RealAnalyticOn.exists_complexAnalytic_extension`: GN Proposition 2.2.12.

## Implementation notes

* GN prove 2.2.8 through a complex analytic extension, on its connected component; here the
  real Taylor expansion (`RealAnalyticOn.exists_taylor`) is used directly, as in the complex
  case, through `eqOn_of_hasLocalTaylor`.
* For 2.1.16 (c), equality of the derivatives along `H` comes from the one-variable identity
  theorem in Mathlib on the complex lines `z ↦ x + z y`, `y ∈ H`; the passage from the diagonal
  on `H` to all of `E` uses the real polarization formula (`MultilinearMap.eq_polarization`) and
  complex multilinearity (`HolomorphicOn.exists_multilinear`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

/-! ### A generic identity theorem -/

section Generic

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]

/-- `f` is the sum of its Taylor series near each point of `U`. -/
def HasLocalTaylor (f : E → F) (U : Set E) : Prop :=
  ∀ x ∈ U, ∃ Y ∈ 𝓝 (0 : E), ∀ y ∈ Y, Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
    (n.factorial : ℝ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y)) atTop (𝓝 (f (x + y)))

omit [ContinuousSMul ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
/-- Two maps with local Taylor expansions whose differentials agree at `x` agree near `x`. -/
theorem eventuallyEq_of_hasLocalTaylor {f g : E → F} {U : Set E} (htf : HasLocalTaylor f U)
    (htg : HasLocalTaylor g U) {x : E} (hx : x ∈ U)
    (hd : ∀ n y, iteratedDMB n f (x, fun _ ↦ y) = iteratedDMB n g (x, fun _ ↦ y)) :
    f =ᶠ[𝓝 x] g := by
  obtain ⟨Y₁, hY₁, h₁⟩ := htf x hx
  obtain ⟨Y₂, hY₂, h₂⟩ := htg x hx
  have hnb : (fun z ↦ z - x) ⁻¹' (Y₁ ∩ Y₂) ∈ 𝓝 x :=
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using inter_mem hY₁ hY₂)
  filter_upwards [hnb] with z hz
  have e : x + (z - x) = z := add_sub_cancel x z
  have h := h₁ _ hz.1
  simp only [hd] at h
  rw [← e]
  exact tendsto_nhds_unique h (h₂ _ hz.2)

omit [ContinuousSMul ℝ F] in
/-- **Identity theorem, generic form** (the proof of [GN26, Theorem 2.1.16], (b)): on a
connected open set, two smooth maps with local Taylor expansions whose differentials of all
orders agree at one point agree everywhere. The set of points near which `f = g` is open,
nonempty, and relatively closed in `U` by continuity of the differentials. -/
theorem eqOn_of_hasLocalTaylor {f g : E → F} {U : Set E} (hU : IsOpen U)
    (hpc : IsPreconnected U) (hf : SmoothMBOn f U) (hg : SmoothMBOn g U)
    (htf : HasLocalTaylor f U) (htg : HasLocalTaylor g U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hd : ∀ n y, iteratedDMB n f (x₀, fun _ ↦ y) = iteratedDMB n g (x₀, fun _ ↦ y)) :
    EqOn f g U := by
  set u := {x : E | f =ᶠ[𝓝 x] g}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ u := by
    refine hpc.subset_of_closure_inter_subset hu
      ⟨x₀, hx₀, eventuallyEq_of_hasLocalTaylor htf htg hx₀ hd⟩ fun x ⟨hxc, hxU⟩ ↦ ?_
    refine eventuallyEq_of_hasLocalTaylor htf htg hxU fun n y ↦ ?_
    set φ : E → F := fun z ↦ iteratedDMB n f (z, fun _ ↦ y) - iteratedDMB n g (z, fun _ ↦ y)
    have hcon : ∀ {h : E → F}, SmoothMBOn h U →
        ContinuousOn (fun z ↦ iteratedDMB n h (z, fun _ ↦ y)) U := fun {h} hh ↦
      ((hh n).hasContIterDerivOn.2 n le_rfl).comp
        (by fun_prop : Continuous fun z : E ↦ (z, fun _ : Fin n ↦ y)).continuousOn
        fun z hz ↦ ⟨hz, mem_univ _⟩
    have hc : ContinuousAt φ x :=
      ((hcon hf).sub (hcon hg)).continuousAt (hU.mem_nhds hxU)
    have h0 : ∀ z ∈ u, φ z = 0 := fun z hz ↦ by
      simp only [φ, iteratedDMB_congr_of_eventuallyEq n hz, sub_self]
    have hmem := hc.continuousWithinAt.mem_closure_image hxc
    have himg : φ '' u ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩; exact h0 z hz
    have := closure_mono himg hmem
    rw [closure_singleton] at this
    exact sub_eq_zero.1 this
  exact fun x hx ↦ (hsub hx).eq_of_nhds

end Generic

/-! ### Complex analytic maps -/

section Complex

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] continuousSMul_real_of_complex polynormableSpace_complex

/-- Complex analytic maps are the sums of their Taylor series near each point. -/
theorem ComplexAnalyticOn.hasLocalTaylor {f : E → F} {U : Set E} (hf : ComplexAnalyticOn f U)
    (hU : IsOpen U) : HasLocalTaylor f U := by
  intro x hx
  obtain ⟨Y, hY, -, hsum⟩ :=
    ((complexAnalyticOn_iff_holomorphicOn hU).1 hf).exists_taylor hU hx
  refine ⟨Y, hY, fun y hy ↦ (hsum y hy).congr fun N ↦ ?_⟩
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [show ((n.factorial : ℂ))⁻¹ = (((n.factorial : ℝ))⁻¹ : ℝ) by push_cast; rfl,
    ofReal_smul_eq]

/-- **Identity theorem** ([GN26, Theorem 2.1.16] (b)): two complex analytic maps on a
connected open set whose differentials of all orders agree at one point agree everywhere. No
completeness of `F` is used. -/
theorem ComplexAnalyticOn.eqOn_of_iteratedDMB {f g : E → F} {U : Set E} (hU : IsOpen U)
    (hpc : IsPreconnected U) (hf : ComplexAnalyticOn f U) (hg : ComplexAnalyticOn g U)
    {x₀ : E} (hx₀ : x₀ ∈ U)
    (hd : ∀ n y, iteratedDMB n f (x₀, fun _ ↦ y) = iteratedDMB n g (x₀, fun _ ↦ y)) :
    EqOn f g U :=
  eqOn_of_hasLocalTaylor hU hpc (hf.smoothMBOn hU) (hg.smoothMBOn hU) (hf.hasLocalTaylor hU)
    (hg.hasLocalTaylor hU) hx₀ hd

/-- **Identity theorem** ([GN26, Theorem 2.1.16] (a)): two complex analytic maps on a
connected open set which agree on a nonempty open subset agree everywhere. -/
theorem ComplexAnalyticOn.eqOn_of_eqOn_open {f g : E → F} {U V : Set E} (hU : IsOpen U)
    (hpc : IsPreconnected U) (hf : ComplexAnalyticOn f U) (hg : ComplexAnalyticOn g U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hne : V.Nonempty) (hfg : EqOn f g V) : EqOn f g U := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine hf.eqOn_of_iteratedDMB hU hpc hg (hVU hx₀) fun n y ↦ ?_
  exact iteratedDMB_congr_of_eventuallyEq n
    (Filter.eventually_of_mem (hV.mem_nhds hx₀) hfg) _

/-- **Identity theorem** ([GN26, Theorem 2.1.16] (c)): let `H ⊆ E` be a real subspace with
`H + i H = E`. Two complex analytic maps on a connected open set which agree on `(x + H) ∩ U`
for some `x ∈ U` agree everywhere. Along each real line `x + ℝ y`, `y ∈ H`, the one-variable
identity theorem gives `δⁿₓf(y) = δⁿₓg(y)`; real polarization extends this to the multilinear
differentials on `Hⁿ`, and complex multilinearity to `Eⁿ`. -/
theorem ComplexAnalyticOn.eqOn_of_eqOn_real {f g : E → F} {U : Set E} (hU : IsOpen U)
    (hpc : IsPreconnected U) (hf : ComplexAnalyticOn f U) (hg : ComplexAnalyticOn g U)
    (H : Submodule ℝ E) (hH : ∀ w : E, ∃ a ∈ H, ∃ b ∈ H, w = a + Complex.I • b) {x : E}
    (hx : x ∈ U) (hfg : ∀ h ∈ H, x + h ∈ U → f (x + h) = g (x + h)) : EqOn f g U := by
  have hhf := (complexAnalyticOn_iff_holomorphicOn hU).1 hf
  have hhg := (complexAnalyticOn_iff_holomorphicOn hU).1 hg
  -- Step 1: the differentials agree on the diagonal of `Hⁿ`
  have hline : ∀ n, ∀ y ∈ H, iteratedDMB n f (x, fun _ ↦ y) = iteratedDMB n g (x, fun _ ↦ y) := by
    intro n y hy
    set D := {z : ℂ | x + z • y ∈ U}
    have hlc : Continuous fun z : ℂ ↦ x + z • y :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hD : IsOpen D := hU.preimage hlc
    have h0D : (0 : ℂ) ∈ D := by simpa [D] using hx
    obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD 0 h0D
    have hlf := (hf.gateauxAnalyticOn hU) x hx y
    have hlg := (hg.gateauxAnalyticOn hU) x hx y
    refine eq_of_forall_clm_eq fun ℓ ↦ ?_
    have hA : ∀ {φ : E → F}, CAnalyticOn (fun z : ℂ ↦ φ (x + z • y)) D →
        AnalyticOnNhd ℂ (fun z : ℂ ↦ ℓ (φ (x + z • y))) (Metric.ball 0 r) := fun hφ ↦
      ((hφ.differentiableOn_clm ℓ).mono hrD).analyticOnNhd Metric.isOpen_ball
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), ℓ (f (x + z • y)) = ℓ (g (x + z • y)) := by
      have hev : ∀ᶠ t : ℝ in 𝓝 0, (t : ℂ) ∈ D :=
        Complex.continuous_ofReal.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds h0D)
      have hev' : ∀ᶠ t : ℝ in 𝓝[≠] 0, ℓ (f (x + (t : ℂ) • y)) = ℓ (g (x + (t : ℂ) • y)) := by
        refine (hev.filter_mono nhdsWithin_le_nhds).mono fun t ht ↦ ?_
        rw [ofReal_smul_eq, hfg _ (H.smul_mem t hy) (by rw [← ofReal_smul_eq]; exact ht)]
      have hT : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
        have := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
          (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0) fun t ht ↦ by simpa using ht
        simpa using this
      exact hT.frequently hev'.frequently
    have heq := (hA hlf).eqOn_of_preconnected_of_frequently_eq (hA hlg)
      (convex_ball (0 : ℂ) r).isPreconnected (Metric.mem_ball_self hr) hfreq
    have hev : (fun z : ℂ ↦ ℓ (f (x + z • y))) =ᶠ[𝓝 0] fun z ↦ ℓ (g (x + z • y)) :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) heq
    have hcf : ContDiffMBOn n (fun z : ℂ ↦ f (x + z • y)) D :=
      (hlf.hasContIterDerivOn n).contDiffMBOn hD
    have hcg : ContDiffMBOn n (fun z : ℂ ↦ g (x + z • y)) D :=
      (hlg.hasContIterDerivOn n).contDiffMBOn hD
    have h1 := iteratedDMB_congr_of_eventuallyEq n hev (fun _ ↦ (1 : ℂ))
    change iteratedDMB n (fun z ↦ (ℓ.restrictScalars ℝ) (f (x + z • y))) (0, fun _ ↦ 1) =
      iteratedDMB n (fun z ↦ (ℓ.restrictScalars ℝ) (g (x + z • y))) (0, fun _ ↦ 1) at h1
    rw [iteratedDMB_clm_comp hD hcf (ℓ.restrictScalars ℝ) n le_rfl 0 h0D,
      iteratedDMB_clm_comp hD hcg (ℓ.restrictScalars ℝ) n le_rfl 0 h0D,
      iteratedDMB_comp_line, iteratedDMB_comp_line] at h1
    simpa using h1
  -- Step 2: the multilinear differentials agree on `Hⁿ`
  refine hf.eqOn_of_iteratedDMB hU hpc hg hx fun n w ↦ ?_
  obtain ⟨Af, hAf⟩ := hhf.exists_multilinear hU hx n
  obtain ⟨Ag, hAg⟩ := hhg.exists_multilinear hU hx n
  set Dm := Af - Ag
  have hsymm : (Dm.restrictScalars ℝ).IsSymm := by
    intro σ v
    simp only [Dm, MultilinearMap.coe_restrictScalars, sub_apply, hAf, hAg,
      (hf.smoothMBOn hU n).iteratedDMB_perm hU le_rfl hx,
      (hg.smoothMBOn hU n).iteratedDMB_perm hU le_rfl hx]
  have hHn : ∀ v : Fin n → E, (∀ i, v i ∈ H) → Dm v = 0 := by
    intro v hv
    have := MultilinearMap.eq_polarization hsymm v
    simp only [MultilinearMap.coe_restrictScalars] at this
    rw [this]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun ε _ ↦ smul_eq_zero_of_right _ ?_)
    have hmem : ∑ j, ε j • v j ∈ H := H.sum_mem fun j _ ↦ H.smul_of_tower_mem (ε j) (hv j)
    simp only [MultilinearMap.diag, MultilinearMap.coe_restrictScalars, Dm,
      sub_apply, hAf, hAg, hline n _ hmem, sub_self]
  -- Step 3: complex multilinearity
  obtain ⟨a, ha, b, hb, rfl⟩ := hH w
  have hexp := apply_add_smul_eq_sum Dm a b Complex.I
  have hzero : Dm (fun _ ↦ a + Complex.I • b) = 0 := by
    rw [hexp]
    refine Finset.sum_eq_zero fun k _ ↦ smul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun S _ ↦ hHn _ fun i ↦ ?_
    by_cases hi : i ∈ S <;> simp [hi, ha, hb]
  have := hzero
  simp only [Dm, sub_apply, hAf, hAg] at this
  exact sub_eq_zero.1 this

end Complex

/-! ### Real analytic maps -/

section Real

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Identity theorem** ([GN26, Theorem 2.2.8]): two real analytic maps on a connected
open set whose differentials of all orders agree at one point agree everywhere. Glöckner and
Neeb pass to a complex analytic extension; here the Taylor expansion of real analytic maps
(`RealAnalyticOn.exists_taylor`) suffices. -/
theorem RealAnalyticOn.eqOn_of_iteratedDMB {f g : E → F} {U : Set E} (hU : IsOpen U)
    (hpc : IsPreconnected U) (hf : RealAnalyticOn f U) (hg : RealAnalyticOn g U)
    {x₀ : E} (hx₀ : x₀ ∈ U)
    (hd : ∀ n y, iteratedDMB n f (x₀, fun _ ↦ y) = iteratedDMB n g (x₀, fun _ ↦ y)) :
    EqOn f g U :=
  eqOn_of_hasLocalTaylor hU hpc (hf.smoothMBOn hU) (hg.smoothMBOn hU)
    (fun x hx ↦ by obtain ⟨Y, hY, -, h⟩ := hf.exists_taylor hU hx; exact ⟨Y, hY, h⟩)
    (fun x hx ↦ by obtain ⟨Y, hY, -, h⟩ := hg.exists_taylor hU hx; exact ⟨Y, hY, h⟩) hx₀ hd

/-- **Identity theorem** ([GN26, Theorem 2.2.8]): two real analytic maps on a connected
open set which agree on a nonempty open subset agree everywhere. -/
theorem RealAnalyticOn.eqOn_of_eqOn_open {f g : E → F} {U V : Set E} (hU : IsOpen U)
    (hpc : IsPreconnected U) (hf : RealAnalyticOn f U) (hg : RealAnalyticOn g U)
    (hV : IsOpen V) (hVU : V ⊆ U) (hne : V.Nonempty) (hfg : EqOn f g V) : EqOn f g U := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine hf.eqOn_of_iteratedDMB hU hpc hg (hVU hx₀) fun n y ↦ ?_
  exact iteratedDMB_congr_of_eventuallyEq n
    (Filter.eventually_of_mem (hV.mem_nhds hx₀) hfg) _

open Complexification

/-- **Uniqueness of complex analytic extensions**: two complex analytic maps on a connected open
set `V ⊆ E_ℂ` which agree at the real points of `V` agree on `V` ([GN26, Theorem 2.1.16]
(c), with `H = E ⊆ E_ℂ`). -/
theorem ComplexAnalyticOn.eqOn_of_eqOn_ofReal {g₁ g₂ : Complexification E → Complexification F}
    {V : Set (Complexification E)} (hV : IsOpen V) (hpc : IsPreconnected V)
    (h₁ : ComplexAnalyticOn g₁ V) (h₂ : ComplexAnalyticOn g₂ V) {x₀ : E} (hx₀ : ofReal x₀ ∈ V)
    (h : ∀ y : E, ofReal y ∈ V → g₁ (ofReal y) = g₂ (ofReal y)) : EqOn g₁ g₂ V := by
  refine h₁.eqOn_of_eqOn_real hV hpc h₂ (LinearMap.range ofRealₗ) (fun w ↦ ?_) hx₀ ?_
  · exact ⟨ofRealₗ (re w), ⟨_, rfl⟩, ofRealₗ (im w), ⟨_, rfl⟩, by
      rw [← mk_eq_add_I_smul, mk_re_im]⟩
  · rintro _ ⟨y, rfl⟩ hy
    have e : ofReal x₀ + ofRealₗ y = ofReal (x₀ + y) := by
      rw [map_add]; rfl
    rw [e] at hy ⊢
    exact h _ hy

end Real

/-! ### Real analytic maps into complex spaces -/

section ComplexTarget

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

open Complexification

attribute [local instance] continuousSMul_real_of_complex

/-- The complex linear map `F_ℂ → F`, `v + i w ↦ v + i w`, for a complex space `F`. -/
def complexifyFold : Complexification F →L[ℂ] F where
  toFun p := re p + Complex.I • im p
  map_add' p p' := by simp only [re_add, im_add, smul_add]; abel
  map_smul' c p := by
    refine map_smul_of_map_I_smul (T := fun p : Complexification F ↦ re p + Complex.I • im p)
      (fun p p' ↦ by simp only [re_add, im_add, smul_add]; abel)
      (fun r p ↦ by
        simp only [re_real_smul, im_real_smul, smul_add, smul_comm Complex.I r])
      (fun p ↦ ?_) c p
    simp only [re_smul, im_smul, Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_sub,
      zero_add, smul_add, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  cont := continuous_re.add (continuous_const.smul continuous_im)

omit [LocallyConvexSpace ℝ F] [T2Space F] in
@[simp] theorem complexifyFold_ofReal (v : F) : complexifyFold (ofReal v) = v := by
  simp [complexifyFold]

/-- **Real analytic maps into complex spaces** ([GN26, Proposition 2.2.12]): a real
analytic map `f : U → F` with values in a complex locally convex space extends to a complex
analytic map `V → F` on an open set `V ⊆ E_ℂ` containing `U`: compose an extension
`V → F_ℂ` with `complexifyFold : F_ℂ → F`. -/
theorem RealAnalyticOn.exists_complexAnalytic_extension {f : E → F} {U : Set E}
    (hf : RealAnalyticOn f U) :
    ∃ V : Set (Complexification E), IsOpen V ∧ ∃ g : Complexification E → F,
      ComplexAnalyticOn g V ∧ ∀ x ∈ U, ofReal x ∈ V ∧ g (ofReal x) = f x := by
  obtain ⟨V, hV, h, hh, hext⟩ := hf
  refine ⟨V, hV, complexifyFold ∘ h,
    (complexifyFold.complexAnalyticOn isOpen_univ).comp hh hV isOpen_univ (mapsTo_univ _ _),
    fun x hx ↦ ⟨(hext x hx).1, ?_⟩⟩
  simp [(hext x hx).2]

end ComplexTarget

end LocallyConvex.Analysis

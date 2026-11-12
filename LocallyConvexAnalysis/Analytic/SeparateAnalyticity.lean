/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Hartogs

/-! # Separately analytic maps on products of locally convex spaces

Hartogs' theorem in `ℂ²` (`LocallyConvexAnalysis.Analytic.Hartogs`) extends to maps on open subsets
of products `E₁ × E₂` of complex locally convex spaces (compare Mujica, *Complex Analysis in Banach
Spaces*, North-Holland Math. Studies 120 (1986), Theorems 36.5 and 36.8, for Banach spaces).

## Main results

* `GateauxAnalyticOn.continuousOn_of_locallyBoundedOn`,
  `GateauxAnalyticOn.complexAnalyticOn_of_locallyBoundedOn`: a Gâteaux analytic map which is
  locally bounded (for every continuous seminorm) is continuous, hence complex analytic. No
  completeness is used.
* `gateauxAnalyticOn_of_separately`: a separately complex analytic map on an open subset of
  `E₁ × E₂` is Gâteaux analytic, for `F` Mackey complete.
* `complexAnalyticOn_of_separately_of_locallyBoundedOn`: separately analytic and locally
  bounded maps are complex analytic.

## Implementation notes

* Mujica removes the local boundedness assumption for Banach spaces: Baire's theorem gives
  boundedness on a product of open sets (his Lemma 36.2), and his Theorem 36.5 propagates local
  boundedness of a Gâteaux holomorphic map over a connected domain, through Cauchy–Hadamard and
  another use of Baire's theorem (his Proposition 36.7). The locally convex version, one seminorm
  at a time, is in `LocallyConvexAnalysis.Analytic.Zorn` (`complexAnalyticOn_of_separately_prod`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [J. Mujica, *Complex Analysis in Banach Spaces*][Muj86]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology Pointwise

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### Gâteaux analytic maps which are locally bounded -/

section LocallyBounded

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] polynormableSpace_complex

/-- `f` is *locally bounded* on `U`: for every continuous seminorm `q` on `F`, `q ∘ f` is
bounded on a neighbourhood of each point of `U`. -/
def LocallyBoundedOn (f : E → F) (U : Set E) : Prop :=
  ∀ a ∈ U, ∀ q : Seminorm ℂ F, Continuous q → ∃ W ∈ 𝓝 a, ∃ M, ∀ x ∈ W, q (f x) ≤ M

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] in
/-- **Gâteaux analytic and locally bounded maps are continuous** (compare
[Muj86, Theorem 36.5 and Proposition 36.7] for Banach
spaces). No completeness of `F` is used: along the complex lines through `a`, the Cauchy estimates
make `f` uniformly `q`-Lipschitz (`seminorm_sub_le_of_dominated`). -/
theorem GateauxAnalyticOn.continuousOn_of_locallyBoundedOn {f : E → F} {U : Set E}
    (hU : IsOpen U) (hg : GateauxAnalyticOn f U) (hb : LocallyBoundedOn f U) :
    ContinuousOn f U := by
  intro a ha
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, tendsto_nhds_iff_seminorm]
  intro q hq ε hε
  obtain ⟨W, hW, M, hM⟩ := hb a ha q hq
  -- a balanced neighbourhood `V` with `a + λ h ∈ W ∩ U` for `h ∈ V`, `|λ| ≤ 2`
  set N : Set E := {h | a + h ∈ W ∩ U}
  have hN : N ∈ 𝓝 (0 : E) := by
    have hc : Continuous fun h : E ↦ a + h := continuous_const.add continuous_id
    exact hc.continuousAt.preimage_mem_nhds (by simpa using inter_mem hW (hU.mem_nhds ha))
  set V₀ := balancedCore ℂ N
  have hV₀ : V₀ ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hN
  have hline : ∀ h, (3 : ℂ) • h ∈ V₀ → ∀ l : ℂ, ‖l‖ ≤ 3 → a + l • h ∈ W ∩ U := by
    intro h hh l hl
    have : (l / 3) • ((3 : ℂ) • h) ∈ V₀ :=
      (balancedCore.balanced N).smul_mem (by rw [norm_div]; simp; linarith) hh
    rw [smul_smul, div_mul_cancel₀ _ (by norm_num)] at this
    exact balancedCore_subset N this
  set δ : ℝ := min 1 (ε / (|M| + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hnb : {x : E | (3 : ℂ) • ((δ : ℂ)⁻¹ • (x - a)) ∈ V₀} ∈ 𝓝 a := by
    have hc : Continuous fun x : E ↦ (3 : ℂ) • ((δ : ℂ)⁻¹ • (x - a)) :=
      continuous_const.smul (continuous_const.smul (continuous_id.sub continuous_const))
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hV₀)
  filter_upwards [hnb] with x hx
  set h := (δ : ℂ)⁻¹ • (x - a)
  have hxa : x = a + (δ : ℂ) • h := by
    simp only [h, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hδ.ne' : (δ : ℂ) ≠ 0),
      one_smul]; abel
  set φ : ℂ → F := fun l ↦ f (a + l • h)
  have hφ := hg a ha h
  have hball : ball (0 : ℂ) (3 * 1) ⊆ {l : ℂ | a + l • h ∈ U} := fun l hl ↦
    (hline h hx l (by rw [mem_ball_zero_iff] at hl; linarith)).2
  have hlip := seminorm_sub_le_of_dominated (g := φ) hq (c := 0) (r := 1) (M := M) one_pos
    (fun ℓ _ ↦ (hφ.differentiableOn_clm ℓ).mono hball)
    (fun l hl ↦ hM _ (hline h hx l (by rw [mem_ball_zero_iff] at hl; linarith)).1)
    (z := (δ : ℂ)) (w := 0)
    (by rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
        exact min_le_left _ _)
    (mem_closedBall_self zero_le_one)
  have hφx : φ (δ : ℂ) = f x := by simp only [φ]; rw [← hxa]
  have hφa : φ 0 = f a := by simp [φ]
  rw [hφx, hφa, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ, div_one] at hlip
  calc q (f x - f a) ≤ M * δ := hlip
    _ ≤ |M| * δ := by gcongr; exact le_abs_self M
    _ ≤ |M| * (ε / (|M| + 1)) := by gcongr; exact min_le_right _ _
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg M]

variable [LocallyConvexSpace ℝ E] [T2Space E]

/-- **Gâteaux analytic and locally bounded maps are complex analytic**, without completeness
(`GateauxAnalyticOn.continuousOn_of_locallyBoundedOn` and [GN26, Theorem 2.1.12]). -/
theorem GateauxAnalyticOn.complexAnalyticOn_of_locallyBoundedOn {f : E → F} {U : Set E}
    (hU : IsOpen U) (hg : GateauxAnalyticOn f U) (hb : LocallyBoundedOn f U) :
    ComplexAnalyticOn f U :=
  (complexAnalyticOn_iff_gateauxAnalyticOn hU).2 ⟨hg.continuousOn_of_locallyBoundedOn hU hb, hg⟩

end LocallyBounded

/-- Gâteaux analyticity along lines whose base point is not in `U`. -/
theorem GateauxAnalyticOn.cAnalyticOn_line {E : Type u} [AddCommGroup E] [Module ℂ E]
    {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    {f : E → F} {V : Set E} (hg : GateauxAnalyticOn f V) (x y : E) :
    CAnalyticOn (fun z : ℂ ↦ f (x + z • y)) {z : ℂ | x + z • y ∈ V} := by
  intro z₀ hz₀
  obtain ⟨r, hr, hsub, a, ha⟩ := hg (x + z₀ • y) hz₀ y 0 (by simpa using hz₀)
  have e : ∀ t : ℂ, x + z₀ • y + t • y = x + (z₀ + t) • y := fun t ↦ by
    rw [add_smul, add_assoc]
  refine ⟨r, hr, fun z hz ↦ ?_, a, fun t ht ↦ ?_⟩
  · have h := hsub (show z - z₀ ∈ ball (0 : ℂ) r by
      rw [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]; exact hz)
    simp only [mem_ofPred_eq, e, add_sub_cancel] at h ⊢
    exact h
  · have h := ha t ht
    simp only [zero_add, e] at h
    exact h

/-! ### Products -/

section Product

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [Module ℂ E₁] [IsScalarTower ℝ ℂ E₁]
  [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℂ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [Module ℂ E₂] [IsScalarTower ℝ ℂ E₂]
  [TopologicalSpace E₂] [IsTopologicalAddGroup E₂] [ContinuousSMul ℂ E₂]
  [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] polynormableSpace_complex

omit [Module ℝ E₁] [IsScalarTower ℝ ℂ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁] [Module ℝ E₂]
  [IsScalarTower ℝ ℂ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **Separately analytic maps are Gâteaux analytic** (compare [Muj86, proof of Theorem 36.8]),
for a Mackey complete `F`: along a complex line through `p ∈ U` in the direction `(u, v)`,
`(ζ, σ) ↦ f (p₁ + ζ u, p₂ + σ v)` is separately analytic on an open subset of `ℂ²`, hence
complex analytic (`complexAnalyticOn_of_separately`), and the line is its diagonal. -/
theorem gateauxAnalyticOn_of_separately [MackeyComplete F] {f : E₁ × E₂ → F}
    {U : Set (E₁ × E₂)} (hU : IsOpen U)
    (h₁ : ∀ y, ComplexAnalyticOn (fun x ↦ f (x, y)) {x | (x, y) ∈ U})
    (h₂ : ∀ x, ComplexAnalyticOn (fun y ↦ f (x, y)) {y | (x, y) ∈ U}) :
    GateauxAnalyticOn f U := by
  intro p hp w
  set h : ℂ → ℂ → F := fun ζ σ ↦ f (p.1 + ζ • w.1, p.2 + σ • w.2)
  set Wset : Set (ℂ × ℂ) := {z | (p.1 + z.1 • w.1, p.2 + z.2 • w.2) ∈ U}
  have hc : Continuous fun z : ℂ × ℂ ↦ ((p.1 + z.1 • w.1, p.2 + z.2 • w.2) : E₁ × E₂) :=
    (continuous_const.add (continuous_fst.smul continuous_const)).prodMk
      (continuous_const.add (continuous_snd.smul continuous_const))
  have hW : IsOpen Wset := hU.preimage hc
  have hs₁ : ∀ σ, CAnalyticOn (fun ζ ↦ h ζ σ) {ζ | (ζ, σ) ∈ Wset} := fun σ ↦ by
    have hU₁ : IsOpen {x | (x, p.2 + σ • w.2) ∈ U} :=
      hU.preimage (continuous_id.prodMk continuous_const)
    exact ((h₁ (p.2 + σ • w.2)).gateauxAnalyticOn hU₁).cAnalyticOn_line p.1 w.1
  have hs₂ : ∀ ζ, CAnalyticOn (h ζ) {σ | (ζ, σ) ∈ Wset} := fun ζ ↦ by
    have hU₂ : IsOpen {y | (p.1 + ζ • w.1, y) ∈ U} :=
      hU.preimage (continuous_const.prodMk continuous_id)
    exact ((h₂ (p.1 + ζ • w.1)).gateauxAnalyticOn hU₂).cAnalyticOn_line p.2 w.2
  have hh := complexAnalyticOn_of_separately hW hs₁ hs₂
  have := (hh.gateauxAnalyticOn hW).cAnalyticOn_line (0, 0) (1, 1)
  have e : ∀ z : ℂ, p + z • w = (p.1 + z • w.1, p.2 + z • w.2) := fun z ↦ rfl
  simp only [e]
  simpa [h, Wset, uncurry] using this

/-- **Separately analytic, locally bounded maps on products are complex analytic** (compare
[Muj86, Theorem 36.8], for Banach spaces, where local boundedness at one point is derived from
Baire's theorem). `F` is Mackey complete; for a non Mackey complete `F` the conclusion fails
already for `E₁ = E₂ = ℂ` (`not_complexAnalyticOn_sepG`). -/
theorem complexAnalyticOn_of_separately_of_locallyBoundedOn [MackeyComplete F]
    {f : E₁ × E₂ → F} {U : Set (E₁ × E₂)} (hU : IsOpen U)
    (h₁ : ∀ y, ComplexAnalyticOn (fun x ↦ f (x, y)) {x | (x, y) ∈ U})
    (h₂ : ∀ x, ComplexAnalyticOn (fun y ↦ f (x, y)) {y | (x, y) ∈ U})
    (hb : LocallyBoundedOn f U) : ComplexAnalyticOn f U :=
  (gateauxAnalyticOn_of_separately hU h₁ h₂).complexAnalyticOn_of_locallyBoundedOn hU hb

end Product

end LocallyConvex.Analysis

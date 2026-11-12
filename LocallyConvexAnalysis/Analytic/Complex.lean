/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.OneVariable
public import LocallyConvexAnalysis.Analytic.Polynomial
public import LocallyConvexAnalysis.Calculus.Higher
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Complex analytic maps between locally convex spaces

[GN26, §2.1]: Definitions 2.1.2
and 2.1.11 and Theorem 2.1.12, equivalence of (b), (c) and (d), for maps `f : E → F` on an open
set `U ⊆ E`, where `E` and `F` are complex locally convex spaces and `F` is **not assumed to be
complete in any sense** (sequentially, Mackey, …). As in
`LocallyConvexAnalysis.Analytic.OneVariable`, no completion of `F` is used: every series or limit is
*given* as an element of `F`, convergence is checked seminorm by seminorm, and scalar estimates are
transported through Hahn–Banach (`seminorm_le_of_forall_clm`).

## Main definitions

* `ComplexAnalyticOn f U`: `f` is continuous and locally `f (x + y) = ∑ₖ pₖ(y)` with continuous
  complex homogeneous polynomials `pₖ` (GN Definition 2.1.2, condition (d)).
* `GateauxAnalyticOn f U`: `z ↦ f (x + z y)` is complex analytic on `{z | x + z y ∈ U}`
  (GN Definition 2.1.11; condition (c) is `ContinuousOn f U ∧ GateauxAnalyticOn f U`).
* `HolomorphicOn f U`: `f` is smooth in the real Michal–Bastiani sense and every `df(x, ·)` is
  complex linear (GN Theorem 2.1.12, condition (b)).

## Main results (no completeness of `F`)

* `tfae_complexAnalyticOn`: (b) ⇔ (c) ⇔ (d) (GN Theorem 2.1.12), with the separate
  implications `HolomorphicOn.gateauxAnalyticOn` ((b) ⇒ (c)),
  `GateauxAnalyticOn.holomorphicOn` ((c) ⇒ (b)), `HolomorphicOn.complexAnalyticOn` ((b) ⇒ (d))
  and `ComplexAnalyticOn.gateauxAnalyticOn` ((d) ⇒ (c)).
* `HolomorphicOn.exists_taylor`: the Taylor expansion
  `f (x + y) = ∑ₙ d⁽ⁿ⁾f(x, y, …, y)/n!` on a `0`-neighbourhood (GN Corollary 2.1.14),
  and `HolomorphicOn.isContHomPoly`: the Taylor polynomials are continuous complex homogeneous
  polynomials.
* `ComplexAnalyticOn.smoothMBOn`: complex analytic maps are smooth (Glöckner, *Infinite-dimensional
  Lie groups without completeness restrictions*, Banach Center Publ. 55 (2002), Proposition
  2.4, complex case); `ComplexAnalyticOn.dMB`: their differentials are complex analytic (loc. cit.,
  Lemma 2.6).
* Intermediate results of independent interest: `GateauxAnalyticOn.continuousOn_dMB` (the
  differential of a continuous Gâteaux analytic map is continuous),
  `GateauxAnalyticOn.gateauxAnalyticOn_dMB` (and Gâteaux analytic), the scalar Osgood lemma
  `OsgoodHyp.differentiableOn_coeff`, `OsgoodHyp.hasSum_line`, and the formula
  `iteratedDMB_comp_line` for iterated differentials along complex lines.

## Proof of (c) ⇒ (b) without completion

GN prove (c) ⇒ (a) by writing `df(x, y) = (2πi)⁻¹ ∮ f(x + ζy) ζ⁻² dζ` (GN (2.13)), using the
continuity and differentiability of parameter-dependent integrals (GN Lemma 1.1.11 and
Proposition 1.3.23) with values in a completion `F̃`, and returning to `F` by polarization (GN
Corollary 1.6.20). Here:

* **continuity of `df`**: `df` is a locally uniform limit of the continuous difference quotients
  `s⁻¹ (f (x + s v) - f x)`, by the Taylor remainder estimate along complex lines, which is
  uniform near each point because `f` is locally bounded (`exists_nhds_bound_line`);
  `df` is then real linear in `v` by `ContDiffMBOn.dMB_add`, and complex homogeneous by
  one-variable theory;
* **Gâteaux analyticity of `df`**: for a continuous functional `ℓ`,
  `(ζ, σ) ↦ ℓ (f (u + ζ y + σ v))` is continuous and separately holomorphic, hence has a double
  power series (Osgood's lemma, proved here from Mathlib's one-variable theory and its
  Weierstrass theorem on locally uniform limits). The Taylor coefficients of
  `z ↦ df(u + z y, v)` are double coefficients, and a discrete polarization over roots of unity
  (`sum_rootsOfUnity_extract`) expresses them through coefficients of `f` along the lines
  `t ↦ u + t (y + λ v)`, which lie in `F`. Then `WeakTaylorOn.hasPowerSeriesOnDisc` gives
  the expansion in `F` (`GateauxAnalyticOn.cAnalyticOn_dMB_line`);
* **induction**: since `df : U × E → F` is again continuous and Gâteaux analytic, induction over
  all complex domains gives `Cᵏ` for every `k` (`contDiffMBOn_of_gateauxAnalyticOn`).

For (b) ⇒ (d), the complex multilinearity of `d⁽ⁿ⁾f(x, ·)` follows from the complex linearity
of `df(z, ·)` for `z` near `x` in the first argument and from Schwarz's theorem (GN
Proposition 1.3.17, `ContDiffMBOn.iteratedDMB_perm`) in the others.

## Implementation notes

* GN's series (2.6) is a pointwise limit of partial sums; `ComplexAnalyticOn` follows this.
  The series produced by `HolomorphicOn.complexAnalyticOn` are even unconditionally summable.
* `E` and `F` carry both a real and a complex structure linked by `IsScalarTower ℝ ℂ _`, as in
  `LocallyConvexAnalysis.Analytic.OneVariable`; local convexity is stated over `ℝ` and the complex
  polynormability is derived (`polynormableSpace_complex`). The implications (c) ⇒ (b) and
  (d) ⇒ (c) do not use local convexity of `E`.
* Condition (a) of GN Theorem 2.1.12 (`C^∞_ℂ`, the complex Michal–Bastiani calculus) and
  conditions (e) and (f), which require `F` Mackey complete, are in `Analytic/ComplexMB.lean`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology Real

noncomputable section

namespace LocallyConvex.Analysis

universe u v

/-! ### Definitions -/

section Definitions

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- `f` is *complex analytic* on `U` ([GN26, Definition 2.1.2]): `f` is continuous on `U`
and, around each `x ∈ U`, it is the pointwise limit of a series of continuous homogeneous
polynomials, `f (x + y) = ∑ₖ pₖ (y)` for `y` in a `0`-neighbourhood `Y` with `x + Y ⊆ U`.
As in GN, the series is a limit of partial sums, and its value is required to lie in `F`;
no completeness of `F` is assumed. -/
def ComplexAnalyticOn (f : E → F) (U : Set E) : Prop :=
  ContinuousOn f U ∧ ∀ x ∈ U, ∃ p : ℕ → E → F, (∀ n, IsContHomPoly ℂ n (p n)) ∧
    ∃ Y ∈ 𝓝 (0 : E), (∀ y ∈ Y, x + y ∈ U) ∧
      ∀ y ∈ Y, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, p n y) atTop (𝓝 (f (x + y)))

/-- `f` is *Gâteaux analytic* on `U` ([GN26, Definition 2.1.11]): it is complex analytic
along each affine line, i.e. for `x ∈ U` and `y ∈ E` the map `z ↦ f (x + z • y)` is complex
analytic (`CAnalyticOn`) on the open set `{z ∈ ℂ | x + z • y ∈ U}`. -/
def GateauxAnalyticOn (f : E → F) (U : Set E) : Prop :=
  ∀ x ∈ U, ∀ y : E, CAnalyticOn (fun z : ℂ ↦ f (x + z • y)) {z : ℂ | x + z • y ∈ U}

variable [Module ℝ E] [Module ℝ F]

/-- `f` is smooth in the real Michal–Bastiani sense on `U` and its differentials
`df(x, ·) : E → F` are complex linear (condition (b) of [GN26, Theorem 2.1.12]). Real
linearity of `df(x, ·)` is automatic for `C¹` maps (`ContDiffMBOn.dMB_add`,
`ContDiffMBOn.dMB_smul`); the condition is the complex homogeneity. -/
def HolomorphicOn (f : E → F) (U : Set E) : Prop :=
  SmoothMBOn f U ∧ ∀ x ∈ U, ∀ (c : ℂ) (h : E), dMB f (x, c • h) = c • dMB f (x, h)

end Definitions

/-! ### Differentials along complex lines -/

section Line

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The real directional derivative of `f` along the complex line `z ↦ x + z • y`:
`d(f(x + · y))(z, w) = df(x + z y, w y)`. This is an identity between limits of the same
difference quotients and needs no hypothesis on `f`. -/
theorem dMB_comp_line (f : E → F) (x y : E) (z w : ℂ) :
    dMB (fun z : ℂ ↦ f (x + z • y)) (z, w) = dMB f (x + z • y, w • y) := by
  unfold dMB
  congr 1
  funext t
  simp only [add_smul, smul_assoc, add_assoc]

/-- The iterated differentials of `f` along the complex line `z ↦ x + z • y`:
`d⁽ⁿ⁾(f(x + · y))(z, w₁, …, wₙ) = d⁽ⁿ⁾f(x + z y, w₁ y, …, wₙ y)`, with no hypothesis on `f`. -/
theorem iteratedDMB_comp_line (f : E → F) (x y : E) : ∀ (n : ℕ) (z : ℂ) (w : Fin n → ℂ),
    iteratedDMB n (fun z : ℂ ↦ f (x + z • y)) (z, w) =
      iteratedDMB n f (x + z • y, fun i ↦ w i • y)
  | 0, _, _ => rfl
  | n + 1, z, w => by
    rw [iteratedDMB_succ, iteratedDMB_succ]
    have e : (fun z' : ℂ ↦ iteratedDMB n (fun z : ℂ ↦ f (x + z • y)) (z', Fin.init w)) =
        fun z' ↦ iteratedDMB n f (x + z' • y, fun i ↦ Fin.init w i • y) :=
      funext fun z' ↦ iteratedDMB_comp_line f x y n z' _
    rw [e]
    exact dMB_comp_line (fun p ↦ iteratedDMB n f (p, fun i ↦ Fin.init w i • y)) x y z _

end Line

/-! ### Easy implications -/

section Easy

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] continuousSMul_real_of_complex polynormableSpace_complex

variable {f : E → F} {U : Set E}

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [LocallyConvexSpace ℝ E] [T2Space E] [T2Space F] in
/-- **(d) ⇒ (c)** in [GN26, Theorem 2.1.12]: complex analytic maps are Gâteaux
analytic. Along a line, a homogeneous polynomial of degree `n` becomes `zⁿ • pₙ(y)`. -/
theorem ComplexAnalyticOn.gateauxAnalyticOn (hf : ComplexAnalyticOn f U) (hU : IsOpen U) :
    GateauxAnalyticOn f U := by
  intro x _ y z₀ hz₀
  obtain ⟨p, hp, Y, hY, -, hsum⟩ := hf.2 _ hz₀
  have hl : Continuous fun ζ : ℂ ↦ ζ • y := continuous_id.smul continuous_const
  have hZ : IsOpen {z : ℂ | x + z • y ∈ U} := hU.preimage (continuous_const.add hl)
  obtain ⟨r₁, hr₁, hr₁Z⟩ := Metric.isOpen_iff.1 hZ z₀ hz₀
  have hY' : (fun ζ : ℂ ↦ ζ • y) ⁻¹' Y ∈ 𝓝 (0 : ℂ) :=
    hl.continuousAt.preimage_mem_nhds (by simpa using hY)
  obtain ⟨r₂, hr₂, hr₂Y⟩ := Metric.mem_nhds_iff.1 hY'
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁Z,
    fun n ↦ p n y, hasPowerSeriesOnDisc_of_tendsto fun ζ hζ ↦ ?_⟩
  have hζY : ζ • y ∈ Y := hr₂Y (by simpa using hζ.trans_le (min_le_right _ _))
  have e : x + (z₀ + ζ) • y = x + z₀ • y + ζ • y := by rw [add_smul, add_assoc]
  change Tendsto _ atTop (𝓝 (f (x + (z₀ + ζ) • y)))
  rw [e]
  exact (hsum _ hζY).congr fun N ↦ Finset.sum_congr rfl fun n _ ↦ (hp n).map_smul ζ y

/-- **(b) ⇒ (c)** in [GN26, Theorem 2.1.12], without completeness: the restriction of a
real smooth map with complex linear differentials to a complex line is smooth with complex
linear differentials (chain rule), hence complex analytic by `cAnalyticOn_iff_smoothMBOn`
(GN, Corollary 2.1.9). -/
theorem HolomorphicOn.gateauxAnalyticOn (hf : HolomorphicOn f U) (hU : IsOpen U) :
    GateauxAnalyticOn f U := by
  intro x _ y
  have hA : Continuous fun z : ℂ ↦ x + z • y := by fun_prop
  have hZ : IsOpen {z : ℂ | x + z • y ∈ U} := hU.preimage hA
  refine (cAnalyticOn_iff_smoothMBOn hZ).2 ⟨fun k ↦ ?_, fun z hz w ↦ ?_⟩
  · let L : ℂ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℂ).smulRight y
    have hAk : ContDiffMBOn k (fun z : ℂ ↦ x + L z) {z : ℂ | x + z • y ∈ U} :=
      ContDiffMBOn.add hZ (contDiffMBOn_const k x _) (L.contDiffMBOn k _)
    exact ContDiffMBOn.comp hZ hU (hf.1 k) hAk fun z hz ↦ hz
  · rw [dMB_comp_line, dMB_comp_line, one_smul, hf.2 _ hz]

/-! ### (b) ⇒ (d): the Taylor series -/

/-- Under (b), `d⁽ʲ⁺¹⁾f(x, ·)` is complex homogeneous in its first argument: the first
derivative is taken in a direction in which `df(z, ·)` is complex linear for all `z` near `x`. -/
theorem HolomorphicOn.iteratedDMB_cons_smul (hf : HolomorphicOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) (j : ℕ) (c : ℂ) (a : E) (v : Fin j → E) :
    iteratedDMB (j + 1) f (x, Fin.cons (c • a) v) =
      c • iteratedDMB (j + 1) f (x, Fin.cons a v) := by
  rw [iteratedDMB_cons, iteratedDMB_cons]
  let L : F →L[ℝ] F := (c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
  have hg : ContDiffMBOn j (fun z ↦ dMB f (z, a)) U :=
    (hf.1 (1 + j)).contDiffMBOn_iteratedDMB_slice (k := 1) (r := j) hU fun _ ↦ a
  have hev : (fun z ↦ dMB f (z, c • a)) =ᶠ[𝓝 x] fun z ↦ L (dMB f (z, a)) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun z hz ↦ hf.2 z hz c a
  rw [iteratedDMB_congr_of_eventuallyEq j hev, iteratedDMB_clm_comp hU hg L j le_rfl x hx]
  rfl

/-- Under (b), `d⁽ⁿ⁾f(x, ·)` is complex homogeneous in each argument (by symmetry,
[GN26, Proposition 1.3.17], it suffices to treat the first one). -/
theorem HolomorphicOn.iteratedDMB_update_smul (hf : HolomorphicOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) {n : ℕ} (v : Fin n → E) (i : Fin n) (c : ℂ) (a : E) :
    iteratedDMB n f (x, update v i (c • a)) = c • iteratedDMB n f (x, update v i a) := by
  cases n with
  | zero => exact i.elim0
  | succ j =>
    have key : ∀ b, iteratedDMB (j + 1) f (x, update v i b) =
        iteratedDMB (j + 1) f (x, Fin.cons b (Fin.tail (v ∘ Equiv.swap 0 i))) := by
      intro b
      rw [← (hf.1 (j + 1)).iteratedDMB_perm hU le_rfl hx (update v i b) (Equiv.swap 0 i),
        Function.update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_right]
      conv_lhs => rw [← Fin.cons_self_tail (v ∘ Equiv.swap 0 i), Fin.update_cons_zero]
    rw [key, key, hf.iteratedDMB_cons_smul hU hx]

/-- Under (b), `d⁽ⁿ⁾f(x, ·)` is complex `n`-linear. -/
theorem HolomorphicOn.exists_multilinear (hf : HolomorphicOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) (n : ℕ) :
    ∃ A : MultilinearMap ℂ (fun _ : Fin n ↦ E) F, ∀ v, A v = iteratedDMB n f (x, v) := by
  obtain ⟨M, hM, -⟩ := (hf.1 n).exists_iteratedDMB_multilinear hU hx
  refine ⟨{ toFun := fun v ↦ iteratedDMB n f (x, v)
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun v ↦ rfl⟩
  · intro inst v i a b
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    simp only [← hM]
    exact M.map_update_add v i a b
  · intro inst v i c a
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hf.iteratedDMB_update_smul hU hx v i c a

/-- Under (b), the Taylor polynomials `y ↦ δⁿₓf(y)/n! = d⁽ⁿ⁾f(x, y, …, y)/n!` are continuous
complex homogeneous polynomials ([GN26, Lemma 1.6.9], plus complex linearity). -/
theorem HolomorphicOn.isContHomPoly (hf : HolomorphicOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) (n : ℕ) :
    IsContHomPoly ℂ n fun y ↦ (n.factorial : ℂ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y) := by
  obtain ⟨A, hA⟩ := hf.exists_multilinear hU hx n
  refine isContHomPoly_iff_continuous.2 ⟨?_, (n.factorial : ℂ)⁻¹ • A, funext fun y ↦ ?_⟩
  · have hc := ((hf.1 n).hasContIterDerivOn.2 n le_rfl).comp_continuous
      (by fun_prop : Continuous fun y : E ↦ (x, fun _ : Fin n ↦ y)) fun y ↦ ⟨hx, mem_univ _⟩
    exact hc.const_smul _
  · simp [MultilinearMap.diag, hA]

/-- **Taylor expansion** ([GN26, Corollary 2.1.14], for some `0`-neighbourhood), without
completeness: under (b), `f (x + y) = ∑ₙ d⁽ⁿ⁾f(x, y, …, y)/n!` on a `0`-neighbourhood `Y` with
`x + Y ⊆ U` (any balanced `Y` with `x + 2 Y ⊆ U` will do). Along the line `z ↦ x + z y` this is
the one-variable Taylor expansion (`CAnalyticOn.hasPowerSeriesOnDisc`, GN Corollary 2.1.8 (b)),
whose coefficients are `d⁽ⁿ⁾f(x, y, …, y)/n! ∈ F`. -/
theorem HolomorphicOn.exists_taylor (hf : HolomorphicOn f U) (hU : IsOpen U) {x : E}
    (hx : x ∈ U) : ∃ Y ∈ 𝓝 (0 : E), (∀ y ∈ Y, x + y ∈ U) ∧ ∀ y ∈ Y,
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
        (n.factorial : ℂ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y)) atTop (𝓝 (f (x + y))) := by
  have hN : (fun y ↦ x + y) ⁻¹' U ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hU.mem_nhds hx)
  set B := balancedCore ℂ ((fun y ↦ x + y) ⁻¹' U)
  have hB : B ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hN
  set Y := (fun y : E ↦ (2 : ℂ) • y) ⁻¹' B
  have hY : Y ∈ 𝓝 (0 : E) :=
    (continuous_const_smul (2 : ℂ)).continuousAt.preimage_mem_nhds (by simpa using hB)
  have hline : ∀ y ∈ Y, closedBall (0 : ℂ) 2 ⊆ {z : ℂ | x + z • y ∈ U} := by
    intro y hy z hz
    have hz' : ‖z / 2‖ ≤ 1 := by
      rw [norm_div, Complex.norm_two, div_le_one two_pos]; simpa using hz
    have h := (balancedCore.balanced _).smul_mem hz' hy
    have e : (z / 2) • (2 : ℂ) • y = z • y := by
      rw [smul_smul, div_mul_cancel₀ _ two_ne_zero]
    rw [e] at h
    have h2 : z • y ∈ (fun y ↦ x + y) ⁻¹' U := balancedCore_subset _ h
    exact h2
  have h1 : (1 : ℂ) ∈ closedBall (0 : ℂ) 2 := by norm_num
  refine ⟨Y, hY, fun y hy ↦ by simpa using hline y hy h1, fun y hy ↦ ?_⟩
  have hA := hf.gateauxAnalyticOn hU x hx y
  have hcoef : ∀ n, (n.factorial : ℂ)⁻¹ • cDeriv^[n] (fun z : ℂ ↦ f (x + z • y)) 0 =
      (n.factorial : ℂ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y) := by
    intro n
    have e1 := hA.iteratedDMB_eq n (x := 0) (by simpa using hx) (fun _ ↦ 1)
    rw [iteratedDMB_comp_line] at e1
    simp only [zero_smul, add_zero, one_smul, Finset.prod_const_one] at e1
    rw [e1]
  have hs := hA.hasPowerSeriesOnDisc (x := 0) two_pos (hline y hy) 1 (by norm_num)
  simp only [one_pow, one_smul, zero_add, hcoef] at hs
  exact hs.tendsto_sum_nat

/-- **(b) ⇒ (d)** in [GN26, Theorem 2.1.12], without completeness: a real smooth map with
complex linear differentials is complex analytic, the polynomials being the Taylor polynomials
(`HolomorphicOn.exists_taylor`, `HolomorphicOn.isContHomPoly`). -/
theorem HolomorphicOn.complexAnalyticOn (hf : HolomorphicOn f U) (hU : IsOpen U) :
    ComplexAnalyticOn f U := by
  refine ⟨hf.1 0, fun x hx ↦ ?_⟩
  obtain ⟨Y, hY, hYU, hsum⟩ := hf.exists_taylor hU hx
  exact ⟨fun n y ↦ (n.factorial : ℂ)⁻¹ • iteratedDMB n f (x, fun _ ↦ y),
    fun n ↦ hf.isContHomPoly hU hx n, Y, hY, hYU, hsum⟩

/-! ### (c) ⇒ `C¹`: the first differential -/

/-- Taylor remainder estimate in `F` for a complex analytic map of one variable, seminorm by
seminorm (from the scalar estimate through Hahn–Banach, as in
`WeakTaylorOn.hasPowerSeriesOnDisc`). -/
theorem CAnalyticOn.seminorm_sub_taylor_le {h : ℂ → F} {V : Set ℂ} (hh : CAnalyticOn h V)
    {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hsub : closedBall z₀ R ⊆ V) {q : Seminorm ℂ F}
    (hq : Continuous q) (hM : ∀ ζ ∈ sphere z₀ R, q (h ζ) ≤ M) {z : ℂ} (hz : ‖z‖ < R) (N : ℕ) :
    q (h (z₀ + z) - ∑ n ∈ Finset.range N, z ^ n • ((n.factorial : ℂ)⁻¹ • cDeriv^[n] h z₀)) ≤
      M * (‖z‖ / R) ^ N / (1 - ‖z‖ / R) := by
  refine seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_
  obtain ⟨hd, hc⟩ := hh.weakTaylorOn hR.le hsub ℓ
  have hC : ∀ ζ ∈ sphere z₀ R, ‖(ℓ ∘ h) ζ‖ ≤ M := fun ζ hζ ↦ (hℓ _).trans (hM ζ hζ)
  have := norm_sub_taylor_le hR hd hC hz N
  rw [map_sub, map_sum]
  simpa only [map_smul, smul_eq_mul, hc, Function.comp_apply] using this

variable {f : E → F} {U : Set E}

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
/-- Directional derivatives of a Gâteaux analytic map: `df(x, c y) = c f_y'(0)`, where
`f_y(z) = f (x + z y)` (GN, proof of Theorem 2.1.12, "(c) ⇒ (a)", before (2.13)). -/
theorem GateauxAnalyticOn.hasDirDerivAt (hg : GateauxAnalyticOn f U) {x : E} (hx : x ∈ U)
    (y : E) (c : ℂ) :
    HasDirDerivAt f x (c • y) (c • cDeriv (fun z : ℂ ↦ f (x + z • y)) 0) := by
  have h := ((hg x hx y).hasCDerivAt (x := 0) (by simpa using hx)).hasDirDerivAt c
  refine h.congr fun t ↦ ?_
  simp only [zero_add, zero_smul, add_zero, smul_assoc]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
/-- `df(x, y) = f_y'(0)` for a Gâteaux analytic map. -/
theorem GateauxAnalyticOn.dMB_eq (hg : GateauxAnalyticOn f U) {x : E} (hx : x ∈ U) (y : E) :
    dMB f (x, y) = cDeriv (fun z : ℂ ↦ f (x + z • y)) 0 := by
  simpa using (hg.hasDirDerivAt hx y 1).dMB_eq

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E] in
/-- The differential of a Gâteaux analytic map is complex homogeneous. -/
theorem GateauxAnalyticOn.dMB_smul (hg : GateauxAnalyticOn f U) {x : E} (hx : x ∈ U) (c : ℂ)
    (y : E) : dMB f (x, c • y) = c • dMB f (x, y) := by
  rw [(hg.hasDirDerivAt hx y c).dMB_eq, hg.dMB_eq hx]

omit [Module ℝ E] [IsScalarTower ℝ ℂ E] [LocallyConvexSpace ℝ E] [T2Space E] [Module ℝ F]
  [IsScalarTower ℝ ℂ F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- A uniform bound for a continuous map near `(x₀, v₀)`: there are a neighbourhood `W` of
`(x₀, v₀)`, `R > 0` and `M` with `x + ζ v ∈ U` and `q (f (x + ζ v)) ≤ M` for `(x, v) ∈ W` and
`|ζ| ≤ R`. -/
theorem exists_nhds_bound_line (hU : IsOpen U) (hc : ContinuousOn f U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (v₀ : E) {q : Seminorm ℂ F} (hq : Continuous q) :
    ∃ W ∈ 𝓝 (x₀, v₀), ∃ R > 0, ∃ M, ∀ p ∈ W, ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      p.1 + ζ • p.2 ∈ U ∧ q (f (p.1 + ζ • p.2)) ≤ M := by
  have hcx : ContinuousAt f x₀ := hc.continuousAt (hU.mem_nhds hx₀)
  set N₀ := {e : E | x₀ + e ∈ U ∧ q (f (x₀ + e) - f x₀) < 1}
  have hN₀ : N₀ ∈ 𝓝 (0 : E) := by
    have h1 : Tendsto (fun e : E ↦ x₀ + e) (𝓝 0) (𝓝 x₀) := by
      simpa using (tendsto_const_nhds (x := x₀)).add (tendsto_id (x := 𝓝 (0 : E)))
    have h2' : Tendsto (fun e ↦ f (x₀ + e) - f x₀) (𝓝 0) (𝓝 0) := by
      simpa using (hcx.tendsto.comp h1).sub_const (f x₀)
    have h2 := (hq.tendsto 0).comp h2'
    simp only [map_zero] at h2
    exact (h1.eventually (hU.mem_nhds hx₀)).and (h2.eventually (gt_mem_nhds one_pos))
  obtain ⟨V, hV, hV4⟩ := exists_nhds_zero_quarter hN₀
  set B := balancedCore ℂ V
  have hB : B ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hV
  have hB3 : ∀ a b c, a ∈ B → b ∈ B → c ∈ B → a + b + c ∈ N₀ := fun a b c ha hb hc ↦ by
    simpa using hV4 (balancedCore_subset V ha) (balancedCore_subset V hb)
      (balancedCore_subset V hc) (mem_of_mem_nhds hV)
  have hl : Continuous fun ζ : ℂ ↦ ζ • v₀ := continuous_id.smul continuous_const
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1
    (hl.continuousAt.preimage_mem_nhds (by simpa using hB) : (fun ζ : ℂ ↦ ζ • v₀) ⁻¹' B ∈ 𝓝 0)
  set R := δ / 2 with hRdef
  have hR : 0 < R := half_pos hδ
  have hW : (fun p : E × E ↦ (p.1 - x₀, (R : ℂ) • (p.2 - v₀))) ⁻¹' (B ×ˢ B) ∈ 𝓝 (x₀, v₀) := by
    have hcont : Continuous fun p : E × E ↦ (p.1 - x₀, (R : ℂ) • (p.2 - v₀)) := by fun_prop
    refine hcont.continuousAt.preimage_mem_nhds ?_
    simpa using prod_mem_nhds hB hB
  refine ⟨_, hW, R, hR, q (f x₀) + 1, fun p hp ζ hζ ↦ ?_⟩
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have h1 : ζ • v₀ ∈ B := hδB (by rw [mem_ball_zero_iff]; linarith)
  have h2 : (ζ / R) • ((R : ℂ) • (p.2 - v₀)) ∈ B := by
    refine (balancedCore.balanced V).smul_mem ?_ hp.2
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
    exact div_le_one_of_le₀ hζ hR.le
  have he : x₀ + (p.1 - x₀ + ζ • v₀ + (ζ / R) • ((R : ℂ) • (p.2 - v₀))) ∈ U ∧
      q (f (x₀ + (p.1 - x₀ + ζ • v₀ + (ζ / R) • ((R : ℂ) • (p.2 - v₀)))) - f x₀) < 1 :=
    hB3 _ _ _ (hp.1 : p.1 - x₀ ∈ B) h1 h2
  have e : x₀ + (p.1 - x₀ + ζ • v₀ + (ζ / R) • ((R : ℂ) • (p.2 - v₀))) = p.1 + ζ • p.2 := by
    rw [smul_smul, div_mul_cancel₀ _ hR0, smul_sub]; abel
  rw [e] at he
  refine ⟨he.1, ?_⟩
  calc q (f (p.1 + ζ • p.2)) ≤ q (f (p.1 + ζ • p.2) - f x₀) + q (f x₀) := by
        simpa using map_add_le_add q (f (p.1 + ζ • p.2) - f x₀) (f x₀)
    _ ≤ q (f x₀) + 1 := by linarith [he.2]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **Continuity of `df`** for a continuous Gâteaux analytic map (GN, proof of Theorem 2.1.12,
"(c) ⇒ (a)"). GN use the Cauchy integral (2.13) and the continuity of parameter-dependent
integrals (GN Lemma 1.1.11); here `df` is exhibited as a locally uniform limit of the continuous
difference quotients `s⁻¹ (f (x + s v) - f x)`, the uniformity coming from the Taylor
remainder estimate along complex lines (`CAnalyticOn.seminorm_sub_taylor_le`). -/
theorem GateauxAnalyticOn.continuousOn_dMB (hU : IsOpen U) (hc : ContinuousOn f U)
    (hg : GateauxAnalyticOn f U) : ContinuousOn (dMB f) (U ×ˢ univ) := by
  rintro ⟨x₀, v₀⟩ ⟨hx₀ : x₀ ∈ U, -⟩
  refine ContinuousAt.continuousWithinAt (tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_)
  obtain ⟨W, hW, R, hR, M, hM⟩ := exists_nhds_bound_line hU hc hx₀ v₀ hq
  have hM0 : 0 ≤ M :=
    (apply_nonneg q _).trans (hM _ (mem_of_mem_nhds hW) 0 (by simpa using hR.le)).2
  -- the difference quotients are uniformly close to `df` on `W`
  have hunif : ∀ p ∈ W, ∀ s : ℝ, 0 < s → s ≤ R / 2 →
      q ((s : ℂ)⁻¹ • (f (p.1 + (s : ℂ) • p.2) - f p.1) - dMB f p) ≤ 2 * M * s / R ^ 2 := by
    intro p hp s hs hsR
    have hpU : p.1 ∈ U := by simpa using (hM p hp 0 (by simpa using hR.le)).1
    have hsub : closedBall (0 : ℂ) R ⊆ {z : ℂ | p.1 + z • p.2 ∈ U} := fun z hz ↦
      (hM p hp z (by simpa using hz)).1
    have hsz : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_of_nonneg hs.le]
    have hT := (hg p.1 hpU p.2).seminorm_sub_taylor_le hR hsub hq
      (fun ζ hζ ↦ (hM p hp ζ (by simp at hζ; linarith)).2) (z := s) (by rw [hsz]; linarith) 2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, one_smul,
      Nat.factorial, Nat.cast_one, inv_one, Function.iterate_zero, id, zero_add, pow_one,
      Function.iterate_one, zero_smul, add_zero, Nat.mul_one] at hT
    rw [← hg.dMB_eq hpU, hsz] at hT
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : (s : ℂ)⁻¹ • (f (p.1 + (s : ℂ) • p.2) - f p.1) - dMB f p =
        (s : ℂ)⁻¹ • (f (p.1 + (s : ℂ) • p.2) - (f p.1 + (s : ℂ) • dMB f p)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hs0, one_smul]; abel
    rw [e, map_smul_eq_mul, norm_inv, hsz]
    have hsR' : s / R ≤ 1 / 2 := by rw [div_le_iff₀ hR]; linarith
    calc s⁻¹ * q (f (p.1 + (s : ℂ) • p.2) - (f p.1 + (s : ℂ) • dMB f p))
        ≤ s⁻¹ * (M * (s / R) ^ 2 / (1 - s / R)) := by gcongr
      _ ≤ s⁻¹ * (M * (s / R) ^ 2 / (1 / 2)) := by gcongr; linarith
      _ = 2 * M * s / R ^ 2 := by field_simp
  -- choose `s`
  set s := min (R / 2) (ε * R ^ 2 / (8 * (M + 1))) with hsdef
  have hs : 0 < s := lt_min (half_pos hR) (by positivity)
  have hsε : 2 * M * s / R ^ 2 < ε / 3 := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : s ≤ ε * R ^ 2 / (8 * (M + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [sq_nonneg R, mul_pos hε (pow_pos hR 2)]
  -- continuity of the difference quotient at `(x₀, v₀)`
  have hsR : s ≤ R / 2 := min_le_left _ _
  set D : E × E → F := fun p ↦ (s : ℂ)⁻¹ • (f (p.1 + (s : ℂ) • p.2) - f p.1)
  have hD : ContinuousAt D (x₀, v₀) := by
    have hsn : ‖(s : ℂ)‖ ≤ R := by
      rw [Complex.norm_real, Real.norm_of_nonneg hs.le]; linarith
    have h1 : x₀ + (s : ℂ) • v₀ ∈ U := (hM _ (mem_of_mem_nhds hW) s hsn).1
    have hf1 : ContinuousAt (fun p : E × E ↦ f (p.1 + (s : ℂ) • p.2)) (x₀, v₀) :=
      ContinuousAt.comp (f := fun p : E × E ↦ p.1 + (s : ℂ) • p.2)
        (hc.continuousAt (hU.mem_nhds h1)) (by fun_prop)
    have hf2 : ContinuousAt (fun p : E × E ↦ f p.1) (x₀, v₀) :=
      ContinuousAt.comp (f := Prod.fst) (hc.continuousAt (hU.mem_nhds hx₀)) continuousAt_fst
    exact (hf1.sub hf2).const_smul _
  have hD' := (tendsto_nhds_iff_seminorm.1 hD) q hq (ε / 3) (by positivity)
  filter_upwards [hW, hD'] with p hp hpD
  have e : dMB f p - dMB f (x₀, v₀) = -(D p - dMB f p) + (D p - D (x₀, v₀)) +
      (D (x₀, v₀) - dMB f (x₀, v₀)) := by abel
  rw [e]
  calc q (-(D p - dMB f p) + (D p - D (x₀, v₀)) + (D (x₀, v₀) - dMB f (x₀, v₀)))
      ≤ q (D p - dMB f p) + q (D p - D (x₀, v₀)) + q (D (x₀, v₀) - dMB f (x₀, v₀)) := by
        refine (map_add_le_add q _ _).trans ?_
        gcongr
        exact (map_add_le_add q _ _).trans (by rw [map_neg_eq_map])
    _ < ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (hunif p hp s hs hsR).trans_lt hsε
        · exact (hunif _ (mem_of_mem_nhds hW) s hs hsR).trans_lt hsε
    _ = ε := by ring

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- A continuous Gâteaux analytic map is `C¹` in the Michal–Bastiani sense. -/
theorem GateauxAnalyticOn.contDiffMBOn_one (hU : IsOpen U) (hc : ContinuousOn f U)
    (hg : GateauxAnalyticOn f U) : ContDiffMBOn 1 f U :=
  ⟨hc, fun x hx h ↦ by simpa [hg.dMB_eq hx] using hg.hasDirDerivAt hx h 1,
    hg.continuousOn_dMB hU hc⟩

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The differential of a continuous Gâteaux analytic map is complex linear. -/
theorem GateauxAnalyticOn.dMB_add_smul (hU : IsOpen U) (hc : ContinuousOn f U)
    (hg : GateauxAnalyticOn f U) {x : E} (hx : x ∈ U) (v w : E) (c : ℂ) :
    dMB f (x, v + c • w) = dMB f (x, v) + c • dMB f (x, w) := by
  rw [(hg.contDiffMBOn_one hU hc).dMB_add hU hx, hg.dMB_smul hx]

end Easy

/-! ### Scalar functions of two complex variables (Osgood's lemma) -/

section Osgood

variable {g : ℂ → ℂ → ℂ} {R M : ℝ}

/-- The Taylor coefficients of `g` in the second variable: `∂_σᵏ g(ζ, 0) / k!`. -/
def osgoodCoeff (g : ℂ → ℂ → ℂ) (k : ℕ) (ζ : ℂ) : ℂ :=
  iteratedDeriv k (g ζ) 0 / k.factorial

/-- The Taylor coefficients `∂_ζʲ (∂_σᵏ g(·, 0) / k!)(0) / j!` of the coefficients. -/
def osgoodCoeff₂ (g : ℂ → ℂ → ℂ) (k j : ℕ) : ℂ :=
  iteratedDeriv j (osgoodCoeff g k) 0 / j.factorial

/-- The hypotheses of Osgood's lemma on the closed bidisc of radius `R`: `g` is holomorphic in
`σ` for `|ζ| ≤ R` (continuously up to the boundary), holomorphic in `ζ` for `|σ| < R`, and
bounded by `M` for `|ζ| ≤ R`, `|σ| = R`. -/
structure OsgoodHyp (g : ℂ → ℂ → ℂ) (R M : ℝ) : Prop where
  pos : 0 < R
  diff₂ : ∀ ζ ∈ closedBall (0 : ℂ) R, DiffContOnCl ℂ (g ζ) (ball 0 R)
  diff₁ : ∀ σ ∈ ball (0 : ℂ) R, DifferentiableOn ℂ (fun ζ ↦ g ζ σ) (ball 0 R)
  bound : ∀ ζ ∈ closedBall (0 : ℂ) R, ∀ σ ∈ sphere (0 : ℂ) R, ‖g ζ σ‖ ≤ M

namespace OsgoodHyp

/-- The bound `M` is nonnegative. -/
theorem bound_nonneg (h : OsgoodHyp g R M) : 0 ≤ M :=
  (norm_nonneg _).trans (h.bound 0 (by simp [h.pos.le]) R (by simp [abs_of_pos h.pos]))

/-- Cauchy estimate for the coefficients in the second variable. -/
theorem norm_coeff_le (h : OsgoodHyp g R M) {ζ : ℂ} (hζ : ζ ∈ closedBall (0 : ℂ) R) (k : ℕ) :
    ‖osgoodCoeff g k ζ‖ ≤ M / R ^ k := by
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k h.pos (h.diff₂ ζ hζ)
    (h.bound ζ hζ)
  have hfac : (0 : ℝ) < k.factorial := by positivity
  rw [osgoodCoeff, norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖iteratedDeriv k (g ζ) 0‖ ≤ k.factorial * M / R ^ k := this
    _ = M / R ^ k * k.factorial := by ring

/-- Taylor expansion in the second variable. -/
theorem hasSum_coeff (h : OsgoodHyp g R M) {ζ : ℂ} (hζ : ζ ∈ closedBall (0 : ℂ) R) {σ : ℂ}
    (hσ : ‖σ‖ < R) : HasSum (fun k ↦ σ ^ k * osgoodCoeff g k ζ) (g ζ σ) := by
  have := Complex.hasSum_taylorSeries_on_ball (h.diff₂ ζ hζ).differentiableOn
    (by simpa using hσ : σ ∈ ball (0 : ℂ) R)
  convert this using 1
  funext k
  rw [osgoodCoeff, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

/-- **Osgood's lemma**, the key step: the Taylor coefficients `∂_σᵏ g(ζ, 0) / k!` are
holomorphic in `ζ`. They are locally uniform limits of the holomorphic functions
`ζ ↦ h⁻ᵏ (g(ζ, h) - ∑_{i < k} hⁱ ∂_σⁱ g(ζ, 0) / i!)` as `h → 0`, by the uniform Taylor
remainder estimate in `σ`; Mathlib's Weierstrass theorem
(`TendstoLocallyUniformlyOn.differentiableOn`) concludes. -/
theorem differentiableOn_coeff (h : OsgoodHyp g R M) (k : ℕ) :
    DifferentiableOn ℂ (osgoodCoeff g k) (ball 0 R) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hR := h.pos
  have hM0 := h.bound_nonneg
  set Fh : ℂ → ℂ → ℂ := fun t ζ ↦
    (t ^ k)⁻¹ * (g ζ t - ∑ i ∈ Finset.range k, t ^ i * osgoodCoeff g i ζ) with hFh
  refine TendstoLocallyUniformlyOn.differentiableOn (φ := 𝓝[≠] (0 : ℂ)) (F := Fh) ?_ ?_
    isOpen_ball
  · refine TendstoUniformlyOn.tendstoLocallyUniformlyOn ?_
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set δ := min (R / 2) (ε * R ^ (k + 1) / (2 * (M + 1))) with hδdef
    have hδ : 0 < δ := lt_min (half_pos hR) (by positivity)
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hδ), self_mem_nhdsWithin]
      with t ht (ht0 : t ≠ 0) ζ hζ
    rw [mem_ball_zero_iff] at ht
    have htR : ‖t‖ < R := ht.trans_le ((min_le_left _ _).trans (half_le_self hR.le))
    have ht2 : ‖t‖ / R ≤ 1 / 2 := by
      rw [div_le_iff₀ hR]; linarith [min_le_left (R / 2) (ε * R ^ (k + 1) / (2 * (M + 1)))]
    have hT := norm_sub_taylor_le hR (h.diff₂ ζ (ball_subset_closedBall hζ))
      (h.bound ζ (ball_subset_closedBall hζ)) htR (k + 1)
    rw [zero_add] at hT
    have htn : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht0
    have e : Fh t ζ - osgoodCoeff g k ζ = (t ^ k)⁻¹ * (g ζ t - ∑ n ∈ Finset.range (k + 1),
        t ^ n * (iteratedDeriv n (g ζ) 0 / n.factorial)) := by
      simp only [hFh, Finset.sum_range_succ, osgoodCoeff]
      field_simp
      ring
    rw [dist_comm, dist_eq_norm, e, norm_mul, norm_inv, norm_pow]
    calc (‖t‖ ^ k)⁻¹ * ‖g ζ t - ∑ n ∈ Finset.range (k + 1),
          t ^ n * (iteratedDeriv n (g ζ) 0 / n.factorial)‖
        ≤ (‖t‖ ^ k)⁻¹ * (M * (‖t‖ / R) ^ (k + 1) / (1 - ‖t‖ / R)) := by gcongr
      _ ≤ (‖t‖ ^ k)⁻¹ * (M * (‖t‖ / R) ^ (k + 1) / (1 / 2)) := by gcongr; linarith
      _ = 2 * M * ‖t‖ / R ^ (k + 1) := by
          have := hR.ne'; rw [div_pow, pow_succ, pow_succ]; field_simp
      _ ≤ 2 * (M + 1) * ‖t‖ / R ^ (k + 1) := by gcongr; linarith
      _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          have h1 : ‖t‖ < ε * R ^ (k + 1) / (2 * (M + 1)) := ht.trans_le (min_le_right _ _)
          rw [lt_div_iff₀ (by positivity)] at h1
          linarith
  · filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hR)] with t ht
    refine DifferentiableOn.const_mul (DifferentiableOn.sub (h.diff₁ t ht) ?_) _
    have := DifferentiableOn.sum (u := Finset.range k)
      (A := fun i ζ ↦ t ^ i * osgoodCoeff g i ζ) fun i hi ↦
        (ih i (Finset.mem_range.1 hi)).const_mul _
    convert this using 1
    funext ζ
    simp

/-- Cauchy estimate for the double coefficients on the disc of radius `R / 2`. -/
theorem norm_coeff₂_le (h : OsgoodHyp g R M) (k j : ℕ) :
    ‖osgoodCoeff₂ g k j‖ ≤ M / R ^ k / (R / 2) ^ j := by
  have hR := h.pos
  have hd : DiffContOnCl ℂ (osgoodCoeff g k) (ball 0 (R / 2)) :=
    ((h.differentiableOn_coeff k).mono ((closure_ball_subset_closedBall).trans
      (closedBall_subset_ball (half_lt_self hR)))).diffContOnCl
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (half_pos hR) hd
    fun ζ hζ ↦ h.norm_coeff_le (sphere_subset_closedBall.trans
      (closedBall_subset_closedBall (half_le_self hR.le)) hζ) k
  have hfac : (0 : ℝ) < j.factorial := by positivity
  rw [osgoodCoeff₂, norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖iteratedDeriv j (osgoodCoeff g k) 0‖ ≤ j.factorial * (M / R ^ k) / (R / 2) ^ j := this
    _ = M / R ^ k / (R / 2) ^ j * j.factorial := by ring

/-- Taylor expansion of the coefficients in the first variable. -/
theorem hasSum_coeff₂ (h : OsgoodHyp g R M) (k : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ < R) :
    HasSum (fun j ↦ ζ ^ j * osgoodCoeff₂ g k j) (osgoodCoeff g k ζ) := by
  have := Complex.hasSum_taylorSeries_on_ball (h.differentiableOn_coeff k)
    (by simpa using hζ : ζ ∈ ball (0 : ℂ) R)
  convert this using 1
  funext j
  rw [osgoodCoeff₂, sub_zero, smul_eq_mul, smul_eq_mul]
  ring

end OsgoodHyp

/-- Regrouping a summable double series along the antidiagonals. -/
theorem hasSum_antidiagonal_of_hasSum {f : ℕ × ℕ → ℂ} {a : ℂ} (h : HasSum f a) :
    HasSum (fun m ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, f p) a := by
  have h' : HasSum (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) a :=
    (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).hasSum_iff.2 h
  refine h'.sigma fun m ↦ ?_
  have := hasSum_fintype
    (fun c : (Finset.HasAntidiagonal.antidiagonal m : Finset (ℕ × ℕ)) ↦ f c.1)
  rw [Finset.sum_coe_sort] at this
  exact this

namespace OsgoodHyp

/-- **Restriction to the lines `σ = λ ζ`**: for `|λ| ≤ 1` and `|t| < R / 2`,
`g(t, λ t) = ∑ₘ tᵐ ∑_{k + j = m} c_{k j} λᵏ`, where `c_{k j}` are the double Taylor
coefficients. -/
theorem hasSum_line (h : OsgoodHyp g R M) {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {t : ℂ}
    (ht : ‖t‖ < R / 2) :
    HasSum (fun m ↦ t ^ m *
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, osgoodCoeff₂ g p.1 p.2 * lam ^ p.1)
      (g t (lam * t)) := by
  have hR := h.pos
  have hM0 := h.bound_nonneg
  have htR : ‖t‖ < R := ht.trans (half_lt_self hR)
  set T : ℕ × ℕ → ℂ := fun p ↦ (lam * t) ^ p.1 * (t ^ p.2 * osgoodCoeff₂ g p.1 p.2) with hT
  -- summability by comparison with a product of geometric series
  have hs1 : ‖t‖ / R < 1 := (div_lt_one hR).2 htR
  have hs2 : ‖t‖ / (R / 2) < 1 := (div_lt_one (half_pos hR)).2 ht
  have hsum : Summable T := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (by positivity) hs1).mul_left M |>.mul_of_nonneg
        (summable_geometric_of_lt_one (by positivity) hs2) (fun _ ↦ by positivity)
        (fun _ ↦ by positivity)) fun p ↦ ?_
    simp only [hT, norm_mul, norm_pow]
    have hc := h.norm_coeff₂_le p.1 p.2
    calc (‖lam‖ * ‖t‖) ^ p.1 * (‖t‖ ^ p.2 * ‖osgoodCoeff₂ g p.1 p.2‖)
        ≤ (1 * ‖t‖) ^ p.1 * (‖t‖ ^ p.2 * (M / R ^ p.1 / (R / 2) ^ p.2)) := by gcongr
      _ = M * (‖t‖ / R) ^ p.1 * (‖t‖ / (R / 2)) ^ p.2 := by
          have := hR.ne'; simp only [one_mul, div_pow]; field_simp
  -- identification of the sum
  have hrow : ∀ k, HasSum (fun j ↦ T (k, j)) ((lam * t) ^ k * osgoodCoeff g k t) := fun k ↦
    (h.hasSum_coeff₂ k htR).mul_left _
  have hcol : HasSum (fun k ↦ (lam * t) ^ k * osgoodCoeff g k t) (g t (lam * t)) :=
    h.hasSum_coeff (ball_subset_closedBall (by simpa using htR)) (by
      rw [norm_mul]; nlinarith [norm_nonneg t, norm_nonneg lam])
  have hT' : HasSum T (g t (lam * t)) := by
    have h1 := hsum.hasSum
    rwa [(h1.prod_fiberwise hrow).unique hcol] at h1
  refine (hasSum_antidiagonal_of_hasSum hT').congr_fun fun m ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  simp only [hT, ← hp, mul_pow, pow_add]
  ring

end OsgoodHyp

/-- Discrete Fourier extraction: with `N = n + 2` and `ω = e^{2πi/N}`, the coefficient of `λ`
in a polynomial `∑_{k ≤ n + 1} c_k λᵏ` is `N⁻¹ ∑_{i < N} ω^{(N-1) i} P(ωⁱ)`. -/
theorem sum_rootsOfUnity_extract (n : ℕ) (c : ℕ × ℕ → ℂ) :
    ((n + 2 : ℕ) : ℂ)⁻¹ * ∑ i ∈ Finset.range (n + 2),
      Complex.exp (2 * π * Complex.I / (n + 2 : ℕ)) ^ ((n + 1) * i) *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c p *
          (Complex.exp (2 * π * Complex.I / (n + 2 : ℕ)) ^ i) ^ p.1 = c (1, n) := by
  set N := n + 2 with hN
  set ω := Complex.exp (2 * π * Complex.I / (N : ℕ))
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N (by omega)
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have key : ∀ k ≤ n + 1, ∑ i ∈ Finset.range N, ω ^ ((n + 1) * i) * (ω ^ i) ^ k =
      if k = 1 then (N : ℂ) else 0 := by
    intro k hk
    have e : ∀ i, ω ^ ((n + 1) * i) * (ω ^ i) ^ k = (ω ^ (n + 1 + k)) ^ i := fun i ↦ by
      rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
    simp only [e]
    split_ifs with hk1
    · subst hk1
      rw [show n + 1 + 1 = N by omega, hω.pow_eq_one]
      simp
    · have hne : ω ^ (n + 1 + k) ≠ 1 := by
        rw [Ne, hω.pow_eq_one_iff_dvd]
        rintro ⟨c, hc⟩
        rcases c with _ | _ | c
        · omega
        · omega
        · rw [show N * (c + 1 + 1) = N * c + 2 * N by ring] at hc
          omega
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
        zero_div]
  calc (N : ℂ)⁻¹ * ∑ i ∈ Finset.range N, ω ^ ((n + 1) * i) *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c p * (ω ^ i) ^ p.1
      = (N : ℂ)⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), c p *
          ∑ i ∈ Finset.range N, ω ^ ((n + 1) * i) * (ω ^ i) ^ p.1 := by
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
    _ = (N : ℂ)⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (n + 1),
          if p = (1, n) then c p * N else 0 := by
        congr 1
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [key p.1 (by omega)]
        by_cases h1 : p.1 = 1
        · have : p = (1, n) := Prod.ext h1 (by omega)
          simp [this]
        · have : p ≠ (1, n) := fun h ↦ h1 (by rw [h])
          simp [h1, this]
    _ = c (1, n) := by
        rw [Finset.sum_ite_eq' (Finset.HasAntidiagonal.antidiagonal (n + 1)) (1, n)]
        rw [ite_eq_left_iff.2 ?_]
        swap; · intro h; exact absurd (by simp [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
        field_simp

end Osgood

/-! ### Algebra of complex analytic maps of one variable -/

section OneVariable

variable {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] {V : Set ℂ}

omit [ContinuousSMul ℂ F] in
/-- Sums of complex analytic maps are complex analytic. -/
theorem CAnalyticOn.add {f g : ℂ → F} (hf : CAnalyticOn f V) (hg : CAnalyticOn g V) :
    CAnalyticOn (fun z ↦ f z + g z) V := by
  intro z₀ hz₀
  obtain ⟨r₁, hr₁, hV₁, a, ha⟩ := hf z₀ hz₀
  obtain ⟨r₂, hr₂, -, b, hb⟩ := hg z₀ hz₀
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hV₁,
    fun n ↦ a n + b n, fun z hz ↦ ?_⟩
  have := (ha z (hz.trans_le (min_le_left _ _))).add (hb z (hz.trans_le (min_le_right _ _)))
  simpa [smul_add] using this

/-- If `f` is complex analytic, so is `z ↦ z • f z`. -/
theorem CAnalyticOn.smul_id {f : ℂ → F} (hf : CAnalyticOn f V) :
    CAnalyticOn (fun z ↦ z • f z) V := by
  intro z₀ hz₀
  obtain ⟨r, hr, hV, a, ha⟩ := hf z₀ hz₀
  refine ⟨r, hr, hV, fun n ↦ z₀ • a n + (if n = 0 then 0 else a (n - 1)), fun z hz ↦ ?_⟩
  have h1 : HasSum (fun n ↦ z ^ n • (z₀ • a n)) (z₀ • f (z₀ + z)) := by
    simpa [smul_comm z₀] using (ha z hz).const_smul z₀
  have h2 : HasSum (fun n ↦ z ^ n • (if n = 0 then (0 : F) else a (n - 1))) (z • f (z₀ + z)) := by
    refine (hasSum_nat_add_iff' 1).1 ?_
    simpa [pow_succ, mul_smul, smul_comm z] using (ha z hz).const_smul z
  convert h1.add h2 using 1
  · funext n; rw [smul_add]
  · change (z₀ + z) • f (z₀ + z) = _
    rw [add_smul]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- Complex analyticity only depends on the values on the (open) domain. -/
theorem CAnalyticOn.congr {f g : ℂ → F} (hf : CAnalyticOn f V) (h : EqOn f g V) :
    CAnalyticOn g V := by
  intro z₀ hz₀
  obtain ⟨r, hr, hV, a, ha⟩ := hf z₀ hz₀
  exact ⟨r, hr, hV, a, fun z hz ↦ h (hV (mem_ball_add hz)) ▸ ha z hz⟩

end OneVariable

/-! ### The differential of a continuous Gâteaux analytic map is Gâteaux analytic -/

section Differential

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] continuousSMul_real_of_complex polynormableSpace_complex

variable {f : E → F} {U : Set E}

/-- The Taylor coefficients of `f` along the line through `u` in the direction `y + λ v`, used
to name the coefficients of `z ↦ df(u + z y, v)` as elements of `F`. -/
def lineCoeff (f : E → F) (u y v : E) (m : ℕ) (lam : ℂ) : F :=
  (m.factorial : ℂ)⁻¹ • cDeriv^[m] (fun t : ℂ ↦ f (u + t • (y + lam • v))) 0

/-- The candidate `n`-th Taylor coefficient of `z ↦ df(u + z y, v)` at `0`, a finite linear
combination of coefficients along lines (a discrete polarization):
`N⁻¹ ∑_{i < N} ω^{(N-1) i} • lineCoeff (n + 1) (ωⁱ)`, `N = n + 2`, `ω = e^{2πi/N}`. -/
def mixedCoeff (f : E → F) (u y v : E) (n : ℕ) : F :=
  ((n + 2 : ℕ) : ℂ)⁻¹ • ∑ i ∈ Finset.range (n + 2),
    Complex.exp (2 * π * Complex.I / (n + 2 : ℕ)) ^ ((n + 1) * i) •
      lineCoeff f u y v (n + 1) (Complex.exp (2 * π * Complex.I / (n + 2 : ℕ)) ^ i)

/-- **The differential of a continuous Gâteaux analytic map is complex analytic in the base
point along complex lines**: `z ↦ df(x + z y, v)` is complex analytic, without completeness of
`F`. For each continuous functional `ℓ`, `(ζ, σ) ↦ ℓ (f (x + (z₀ + ζ) y + σ v))` is a continuous,
separately holomorphic function of two variables, hence has a double power series
(`OsgoodHyp.hasSum_line`); the Taylor coefficients of `ℓ (df(x + (z₀ + ζ) y, v))` are double
coefficients, which are extracted from coefficients along lines through `x + z₀ y` by
`sum_rootsOfUnity_extract`. Hence the coefficients `mixedCoeff` lie in `F`, and
`WeakTaylorOn.hasPowerSeriesOnDisc` gives the convergence in `F`. This replaces GN's
differentiation of parameter-dependent integrals in a completion (proof of Theorem 2.1.12,
"(c) ⇒ (a)", via GN Proposition 1.3.23). -/
theorem GateauxAnalyticOn.cAnalyticOn_dMB_line (hU : IsOpen U) (hc : ContinuousOn f U)
    (hg : GateauxAnalyticOn f U) (x y v : E) :
    CAnalyticOn (fun z : ℂ ↦ dMB f (x + z • y, v)) {z : ℂ | x + z • y ∈ U} := by
  intro z₀ hz₀
  set u₀ := x + z₀ • y with hu₀
  have hshift : ∀ ζ : ℂ, x + (z₀ + ζ) • y = u₀ + ζ • y := fun ζ ↦ by
    rw [hu₀, add_smul, add_assoc]
  -- a closed bidisc of radius `R` around `0` is mapped into `U`
  set A : ℂ × ℂ → E := fun p ↦ u₀ + p.1 • y + p.2 • v with hA
  have hAc : Continuous A := by fun_prop
  have hAU : A ⁻¹' U ∈ 𝓝 ((0 : ℂ), (0 : ℂ)) :=
    hAc.continuousAt.preimage_mem_nhds (by simpa [hA] using hU.mem_nhds hz₀)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hAU
  set R := δ / 2 with hRdef
  have hR : 0 < R := half_pos hδ
  have hbi : ∀ ζ σ : ℂ, ‖ζ‖ ≤ R → ‖σ‖ ≤ R → u₀ + ζ • y + σ • v ∈ U := by
    intro ζ σ hζ hσ
    have : ((ζ, σ) : ℂ × ℂ) ∈ ball ((0 : ℂ), (0 : ℂ)) δ := by
      rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]
      exact max_lt (by linarith) (by linarith)
    exact hδU this
  have hbase : ∀ ζ : ℂ, ‖ζ‖ ≤ R → u₀ + ζ • y ∈ U := fun ζ hζ ↦ by
    simpa using hbi ζ 0 hζ (by simp [hR.le])
  -- the scalar functions satisfy the hypotheses of Osgood's lemma
  have hosg : ∀ ℓ : F →L[ℂ] ℂ, ∃ M, OsgoodHyp (fun ζ σ ↦ ℓ (f (u₀ + ζ • y + σ • v))) R M := by
    intro ℓ
    have hK : IsCompact (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    have hcont : ContinuousOn (fun p : ℂ × ℂ ↦ ℓ (f (A p)))
        (closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R) :=
      ℓ.continuous.comp_continuousOn (hc.comp hAc.continuousOn fun p hp ↦
        hbi p.1 p.2 (by simpa using hp.1) (by simpa using hp.2))
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
    refine ⟨M, hR, fun ζ hζ ↦ ?_, fun σ hσ ↦ ?_, fun ζ hζ σ hσ ↦ ?_⟩
    · rw [mem_closedBall_zero_iff] at hζ
      have hd := (hg _ (hbase ζ hζ) v).differentiableOn_clm ℓ
      refine (hd.mono fun σ hσ ↦ ?_).diffContOnCl
      have hσ' := closure_ball_subset_closedBall hσ
      rw [mem_closedBall_zero_iff] at hσ'
      exact hbi ζ σ hζ hσ'
    · rw [mem_ball_zero_iff] at hσ
      have hd := (hg _ (by simpa using hbi 0 σ (by simp [hR.le]) hσ.le) y).differentiableOn_clm ℓ
      have e : (fun ζ ↦ ℓ (f (u₀ + ζ • y + σ • v))) =
          ℓ ∘ fun ζ : ℂ ↦ f (u₀ + σ • v + ζ • y) := by
        funext ζ; simp only [Function.comp_apply, add_right_comm]
      rw [e]
      refine hd.mono fun ζ hζ ↦ ?_
      rw [mem_ball_zero_iff] at hζ
      change u₀ + σ • v + ζ • y ∈ U
      rw [add_right_comm]
      exact hbi ζ σ hζ.le hσ.le
    · exact hM (ζ, σ) ⟨hζ, sphere_subset_closedBall hσ⟩
  -- the candidate coefficients satisfy the scalar identities
  have hweak : ∀ ℓ : F →L[ℂ] ℂ,
      DifferentiableOn ℂ (ℓ ∘ fun z : ℂ ↦ dMB f (x + z • y, v)) (ball z₀ R) ∧
      ∀ n, ℓ (mixedCoeff f u₀ y v n) =
        iteratedDeriv n (ℓ ∘ fun z : ℂ ↦ dMB f (x + z • y, v)) z₀ / n.factorial := by
    intro ℓ
    obtain ⟨M, hM⟩ := hosg ℓ
    set g : ℂ → ℂ → ℂ := fun ζ σ ↦ ℓ (f (u₀ + ζ • y + σ • v)) with hg_def
    -- `ℓ (df(x + (z₀ + ζ) y, v))` is the first coefficient in `σ`
    have hd1 : ∀ ζ : ℂ, ‖ζ‖ < R →
        (ℓ ∘ fun z : ℂ ↦ dMB f (x + z • y, v)) (z₀ + ζ) = osgoodCoeff g 1 ζ := by
      intro ζ hζ
      have hb := hbase ζ hζ.le
      have hcd := ((hg _ hb v).hasCDerivAt (x := 0) (by simpa using hb)).hasDerivAt_clm ℓ
      simp only [Function.comp_apply, hshift, hg.dMB_eq hb, osgoodCoeff, iteratedDeriv_one,
        Nat.factorial_one, Nat.cast_one, div_one]
      exact hcd.deriv.symm
    have hser : ∀ ζ : ℂ, ‖ζ‖ < R → HasSum (fun n ↦ ζ ^ n • osgoodCoeff₂ g 1 n)
        ((ℓ ∘ fun z : ℂ ↦ dMB f (x + z • y, v)) (z₀ + ζ)) := fun ζ hζ ↦ by
      rw [hd1 ζ hζ]; simpa only [smul_eq_mul] using hM.hasSum_coeff₂ 1 hζ
    refine ⟨differentiableOn_of_hasSum hR hser, fun n ↦ ?_⟩
    rw [← coeff_eq_iteratedDeriv_of_hasSum hR hser n]
    -- coefficients along lines
    have hline : ∀ (m : ℕ) (lam : ℂ), ‖lam‖ ≤ 1 → ℓ (lineCoeff f u₀ y v m lam) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, osgoodCoeff₂ g p.1 p.2 * lam ^ p.1 := by
      intro m lam hlam
      have hsub : closedBall (0 : ℂ) (R / 2) ⊆ {t : ℂ | u₀ + t • (y + lam • v) ∈ U} := by
        intro t ht
        rw [mem_closedBall_zero_iff] at ht
        change u₀ + t • (y + lam • v) ∈ U
        rw [smul_add, smul_smul, ← add_assoc]
        refine hbi t (t * lam) (by linarith) ?_
        rw [norm_mul]; nlinarith [norm_nonneg t, norm_nonneg lam]
      have hps := (hg u₀ (by simpa using hbase 0 (by simp [hR.le])) (y + lam • v)
        ).hasPowerSeriesOnDisc (x := 0) (half_pos hR) hsub
      rw [lineCoeff, hps.clm_apply (half_pos hR) ℓ m]
      refine (coeff_eq_iteratedDeriv_of_hasSum (x := 0)
        (g := ℓ ∘ fun t : ℂ ↦ f (u₀ + t • (y + lam • v)))
        (c := fun m ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          osgoodCoeff₂ g p.1 p.2 * lam ^ p.1) (half_pos hR) (fun t ht ↦ ?_) m).symm
      have := hM.hasSum_line hlam ht
      simp only [smul_eq_mul, zero_add, Function.comp_apply]
      convert this using 2
      rw [smul_add, smul_smul, ← add_assoc, mul_comm]
    -- discrete polarization
    have hω : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / (n + 2 : ℕ))) (n + 2) :=
      Complex.isPrimitiveRoot_exp (n + 2) (by omega)
    have hωn : ∀ i : ℕ, ‖Complex.exp (2 * π * Complex.I / (n + 2 : ℕ)) ^ i‖ ≤ 1 := fun i ↦ by
      rw [norm_pow, hω.norm'_eq_one (by omega), one_pow]
    rw [mixedCoeff, map_smul, map_sum, smul_eq_mul]
    simp only [map_smul, smul_eq_mul, hline _ _ (hωn _)]
    exact sum_rootsOfUnity_extract n fun p ↦ osgoodCoeff₂ g p.1 p.2
  -- conclusion
  have hR2 : 0 < R / 2 := half_pos hR
  have hball : ∀ z ∈ closedBall z₀ (R / 2), x + z • y ∈ U := fun z hz ↦ by
    have : z = z₀ + (z - z₀) := by ring
    rw [this, hshift]
    exact hbase _ (by rw [← dist_eq_norm]; exact (mem_closedBall.1 hz).trans (by linarith))
  refine ⟨R / 2, hR2, fun z hz ↦ hball z (ball_subset_closedBall hz), mixedCoeff f u₀ y v,
    WeakTaylorOn.hasPowerSeriesOnDisc (fun ℓ ↦ ⟨?_, (hweak ℓ).2⟩) hR2 ?_⟩
  · exact ((hweak ℓ).1.mono (closure_ball_subset_closedBall.trans
      (closedBall_subset_ball (half_lt_self hR)))).diffContOnCl
  · refine (hg.continuousOn_dMB hU hc).comp (by fun_prop : Continuous fun z : ℂ ↦
      (x + z • y, v)).continuousOn fun z hz ↦ ⟨hball z (sphere_subset_closedBall hz), mem_univ _⟩

/-- **The differential of a continuous Gâteaux analytic map is Gâteaux analytic** on `U × E`:
`z ↦ df(x + z y, v + z w) = df(x + z y, v) + z df(x + z y, w)` is complex analytic. -/
theorem GateauxAnalyticOn.gateauxAnalyticOn_dMB (hU : IsOpen U) (hc : ContinuousOn f U)
    (hg : GateauxAnalyticOn f U) : GateauxAnalyticOn (dMB f) (U ×ˢ univ) := by
  rintro ⟨x, v⟩ ⟨hx, -⟩ ⟨y, w⟩
  have hset : {z : ℂ | (x, v) + z • (y, w) ∈ U ×ˢ (univ : Set E)} = {z : ℂ | x + z • y ∈ U} := by
    ext z; simp
  rw [hset]
  refine ((hg.cAnalyticOn_dMB_line hU hc x y v).add
    (hg.cAnalyticOn_dMB_line hU hc x y w).smul_id).congr fun z hz ↦ ?_
  simp only [Prod.smul_mk, Prod.mk_add_mk]
  exact (hg.dMB_add_smul hU hc hz v w z).symm

end Differential

/-! ### Theorem 2.1.12 -/

section Main

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] continuousSMul_real_of_complex polynormableSpace_complex

/-- **(c) ⇒ `Cᵏ`** ([GN26, proof of Theorem 2.1.12], "(c) ⇒ (a)", induction on `k`):
a continuous Gâteaux analytic map is `Cᵏ` in the real Michal–Bastiani sense for every `k`.
The induction runs over all complex locally convex domains, since the differential
`df : U × E → F` is again continuous and Gâteaux analytic
(`GateauxAnalyticOn.continuousOn_dMB`, `GateauxAnalyticOn.gateauxAnalyticOn_dMB`).
No completeness of `F` is used. -/
theorem contDiffMBOn_of_gateauxAnalyticOn : ∀ (k : ℕ) {E : Type u} [AddCommGroup E]
    [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {f : E → F} {U : Set E}, IsOpen U →
    ContinuousOn f U → GateauxAnalyticOn f U → ContDiffMBOn k f U := by
  intro k
  induction k with
  | zero => intro E _ _ _ _ _ _ _ f U hU hc hg; exact hc
  | succ k ih =>
    intro E _ _ _ _ _ _ _ f U hU hc hg
    exact ⟨hc, (hg.contDiffMBOn_one hU hc).2.1,
      ih (hU.prod isOpen_univ) (hg.continuousOn_dMB hU hc) (hg.gateauxAnalyticOn_dMB hU hc)⟩

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  {f : E → F} {U : Set E}

/-- **(c) ⇒ (b)** in [GN26, Theorem 2.1.12], without completeness of `F`: a continuous
Gâteaux analytic map is smooth in the real Michal–Bastiani sense, with complex linear
differentials. -/
theorem GateauxAnalyticOn.holomorphicOn (hU : IsOpen U) (hc : ContinuousOn f U)
    (hg : GateauxAnalyticOn f U) : HolomorphicOn f U :=
  ⟨fun k ↦ contDiffMBOn_of_gateauxAnalyticOn k hU hc hg, fun _ hx c h ↦ hg.dMB_smul hx c h⟩

variable [LocallyConvexSpace ℝ E] [T2Space E]

/-- **[GN26, Theorem 2.1.12], (b) ⇔ (c)**, for complex locally convex spaces `E`, `F`
with `F` not necessarily complete in any sense. -/
theorem holomorphicOn_iff_gateauxAnalyticOn (hU : IsOpen U) :
    HolomorphicOn f U ↔ ContinuousOn f U ∧ GateauxAnalyticOn f U :=
  ⟨fun h ↦ ⟨h.1 0, h.gateauxAnalyticOn hU⟩, fun h ↦ h.2.holomorphicOn hU h.1⟩

/-- **[GN26, Theorem 2.1.12], (c) ⇔ (d)**, without completeness of `F`. -/
theorem complexAnalyticOn_iff_gateauxAnalyticOn (hU : IsOpen U) :
    ComplexAnalyticOn f U ↔ ContinuousOn f U ∧ GateauxAnalyticOn f U :=
  ⟨fun h ↦ ⟨h.1, h.gateauxAnalyticOn hU⟩,
    fun h ↦ (h.2.holomorphicOn hU h.1).complexAnalyticOn hU⟩

/-- **[GN26, Theorem 2.1.12], (b) ⇔ (d)**, without completeness of `F`: a map is
complex analytic iff it is smooth in the real Michal–Bastiani sense with complex linear
differentials (Glöckner, Banach Center Publ. 55 (2002), Lemma 2.5, where the proof passes
through the completion of `F`). -/
theorem complexAnalyticOn_iff_holomorphicOn (hU : IsOpen U) :
    ComplexAnalyticOn f U ↔ HolomorphicOn f U := by
  rw [complexAnalyticOn_iff_gateauxAnalyticOn hU, holomorphicOn_iff_gateauxAnalyticOn hU]

/-- **[GN26, Theorem 2.1.12], (b) ⇔ (c) ⇔ (d)**, for an arbitrary (not necessarily
complete) complex locally convex space `F`. -/
theorem tfae_complexAnalyticOn (hU : IsOpen U) :
    List.TFAE [HolomorphicOn f U, ContinuousOn f U ∧ GateauxAnalyticOn f U,
      ComplexAnalyticOn f U] := by
  tfae_have 1 ↔ 2 := holomorphicOn_iff_gateauxAnalyticOn hU
  tfae_have 3 ↔ 2 := complexAnalyticOn_iff_gateauxAnalyticOn hU
  tfae_finish

/-- **Complex analytic maps are smooth** (Glöckner, Banach Center Publ. 55 (2002),
Proposition 2.4, complex case), without completeness of `F`. -/
theorem ComplexAnalyticOn.smoothMBOn (hf : ComplexAnalyticOn f U) (hU : IsOpen U) :
    SmoothMBOn f U :=
  ((complexAnalyticOn_iff_holomorphicOn hU).1 hf).1

/-- The differential of a complex analytic map is complex analytic on `U × E` (Glöckner,
Banach Center Publ. 55 (2002), Lemma 2.6), without completeness of `F`. -/
theorem ComplexAnalyticOn.dMB (hf : ComplexAnalyticOn f U) (hU : IsOpen U) :
    ComplexAnalyticOn (dMB f) (U ×ˢ univ) :=
  (complexAnalyticOn_iff_gateauxAnalyticOn (hU.prod isOpen_univ)).2
    ⟨hf.gateauxAnalyticOn hU |>.continuousOn_dMB hU hf.1,
      hf.gateauxAnalyticOn hU |>.gateauxAnalyticOn_dMB hU hf.1⟩

end Main

end LocallyConvex.Analysis

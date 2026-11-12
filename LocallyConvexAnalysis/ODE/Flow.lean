/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.Quadratic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Local flows of vector fields on Banach spaces, with smooth dependence on initial data

Let `E` be a Banach space, `U ⊆ E` open and `f : U → E` of class `C^n` in the Fréchet sense,
`1 ≤ n ≤ ∞`. We prove that the solutions of `c' = f ∘ c`, `c(0) = x`, depend in a `C^n` way on
`(t, x)` (`exists_contDiffOn_flow`): near each `x₀ ∈ U` there are `ε > 0`, an open `V ∋ x₀` and
`Fl : (-ε, ε) × V → U`, jointly `C^n`, with `Fl(0, x) = x` and `∂ₜ Fl(t, x) = f(Fl(t, x))`. The
curves `t ↦ Fl(t, x)` are the only solutions (`eqOn_Ioo_of_contDiffOn`, from Mathlib's
`ODE_solution_unique_of_eventually` through `eqOn_Ioo_of_locallyLipschitz`). The smooth case in
the sense of Michal–Bastiani is `exists_smoothMBOn_flow`.

**Complex time.** The proof works verbatim over `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`): for `E` a Banach
space over `𝕜` and `f` of class `C^n` over `𝕜`, `exists_contDiffOn_flow_rclike` gives a flow
`Fl : B_𝕜(0, ε) × V → U` which is `C^n` over `𝕜` in `(t, x)`, with time `t` in the ball of `𝕜`,
and whose restriction to real times solves `c' = f ∘ c`. For `𝕜 = ℂ` this is the holomorphic
dependence of the solutions of holomorphic equations on complex time and initial value, used in
`LocallyConvexAnalysis.ODE.FlowAnalytic` for the real analytic case.

References: [Lan99, Chapter IV, §1] (Theorem 1.11, and the second proof through Lemmas 1.12,
1.13 and Theorem 1.14); [GN26, Theorem 2.4.34 and Corollary 2.4.37], which cover time-dependent
equations with parameters.

## Main definitions

* `mapsInto K U`: the open set of continuous curves `K → E` with values in `U`.
* `superpose f`: the superposition operator `γ ↦ f ∘ γ` on `C(K, E)`.
* `pointwiseApply`: pointwise application `(A, γ) ↦ (s ↦ A s (γ s))`, as a continuous bilinear
  map `C(K, L(E, F)) × C(K, E) → C(K, F)`.
* `primitiveCLM`: the primitive operator `J γ = (s ↦ ∫₀ˢ γ)` on `C([-1, 1], E)`.
* `flowEqMap f`: the map `Ψ(λ, x, γ) = (λ, x, γ - x - λ J(f ∘ γ))` on `𝕜 × E × C([-1, 1], E)`,
  whose zeros in the last component are the solutions of `γ' = λ f ∘ γ`, `γ(0) = x`.

## Main results

* `hasFDerivAt_superpose`, `contDiffOn_superpose`: for `f` of class `C^n` on `U` and `K`
  compact, `γ ↦ f ∘ γ` is Fréchet `C^n` on `mapsInto K U`, with derivative
  `η ↦ (s ↦ f'(γ s) (η s))` ([Lan99, Chapter IV, Lemma 1.12]).
* `exists_contDiffOn_flow_rclike`: over `𝕜 = ℝ` or `ℂ`, a `C^n` vector field on an open subset of
  a Banach space has a local flow `Fl : B_𝕜(0, ε) × V → U`, `C^n` over `𝕜` in `(t, x)`, whose
  restriction to real times solves `c' = f ∘ c`.
* `exists_contDiffOn_flow`: the case `𝕜 = ℝ`; near each `x₀ ∈ U` there are `ε > 0`, an open
  `V ∋ x₀` and `Fl : (-ε, ε) × V → U`, jointly `C^n`, with `Fl(0, x) = x` and
  `∂ₜ Fl(t, x) = f(Fl(t, x))` ([Lan99, Chapter IV, Theorem 1.14]; [GN26, Theorem 2.4.34 and
  Corollary 2.4.37] cover time-dependent equations with parameters).
* `exists_smoothMBOn_flow`: the local flows of a vector field that is smooth in the sense of
  Michal–Bastiani are jointly smooth in the sense of Michal–Bastiani.
* `eqOn_Ioo_of_contDiffOn`: two solutions of `c' = f ∘ c`, `f` of class `C¹`, with values in `U`
  that agree at one instant agree on their common interval.

## Method

We follow the implicit function approach of [Lan99, Chapter IV, Theorem 1.14], on the Banach
space `C([-1, 1], E)` of continuous curves with the sup norm.

* **Superposition operators** (`contDiffOn_superpose`). For `f` of class `C^n` on `U` and `K`
  compact, `γ ↦ f ∘ γ` is Fréchet `C^n` on the open set `mapsInto K U` of curves with values in
  `U`, with derivative `η ↦ (s ↦ f'(γ s) (η s))` (`hasFDerivAt_superpose`,
  [Lan99, Chapter IV, Lemma 1.12]).
  The estimate rests on the uniform continuity of `f'` near the compact set `γ(K)`
  (`exists_forall_dist_lt_of_isCompact`); the higher derivatives follow by induction, since the
  derivative is again a superposition operator, composed with the continuous bilinear map
  `pointwiseApply`.
* **The fixed point problem** (`flowEqMap`). With `J γ = (s ↦ ∫₀ˢ γ)` (`primitiveCLM`), consider
  `Ψ(λ, x, γ) = (λ, x, γ - x - λ J(f ∘ γ))` on `𝕜 × E × C([-1, 1], E)`. Its zeros in the last
  component are the solutions of `γ' = λ f ∘ γ`, `γ(0) = x`, that is, the curves
  `s ↦ c_x(λ s)` for the solution `c_x` with `c_x(0) = x`. The curves are always parametrized
  by the real interval `[-1, 1]`; only the time scale `λ` lies in `𝕜`.
* **The inverse function theorem.** At `(0, x₀, x₀)` the derivative of `Ψ` is the shear
  `(a, b, c) ↦ (a, b, c - b - a J(f ∘ x₀))` (`hasFDerivAt_flowEqMap`), which is invertible, so
  Mathlib's inverse function theorem (`ContDiffAt.toOpenPartialHomeomorph`,
  `OpenPartialHomeomorph.contDiffAt_symm`) gives a `C^n` family `Γ(λ, x)` of solutions. We set
  `Fl(t, x) = Γ(t, x)(1)`.
* **Rescaling.** By injectivity of `Ψ` near `(0, x₀, x₀)`, `Γ(σ λ, x)(1) = Γ(λ, x)(σ)` for
  real `σ ∈ [-1, 1]`, since both sides solve the same fixed point problem. Hence near a real
  time `t`, `Fl(s, x) = x + λ ∫₀^{s/λ} f(Γ(λ, x)(τ)) dτ` for a fixed real `λ > |t|`, and the
  fundamental theorem of calculus gives `∂ₜ Fl(t, x) = f(Fl(t, x))`.

Lang treats the time variable separately: he applies the implicit mapping theorem to
`T(x, α) = x + ∫ f ∘ α - α` on curves over a fixed short interval, which gives smoothness in `x`,
and recovers smoothness in `t` from the equation. Here the time scale `λ` is a parameter of the
fixed point problem, so the inverse function theorem gives joint smoothness in `(t, x)` at once;
we do not claim this argument is new.

## Implementation notes

* Completeness of `E` is explicit (`[CompleteSpace E]`): it is needed for the Bochner integral in
  `J` (the fundamental theorem of calculus) and for the inverse function theorem on
  `𝕜 × E × C([-1, 1], E)`.
* Over `𝕜`, the space `E` carries both a `𝕜`- and a compatible real structure
  (`[NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E]`), the latter for the integrals.
* The real analytic case is `LocallyConvexAnalysis.ODE.FlowAnalytic`.
* Outside Banach spaces the theorem fails, even for continuous linear vector fields: on the
  locally convex direct sum `ℝ^(ℕ)` the right shift has no solution with initial value
  `(1, 0, 0, …)` ([GN26, Example 2.4.2]), and on the Fréchet space `ℝ^ℕ` the left shift
  has several solutions with initial value `0` (Example 2.4.3). This is why lc-manifolds treats
  local flows as a hypothesis outside the Banach setting.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [S. Lang, *Fundamentals of Differential Geometry*][Lan99]
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Uniform continuity near a compact set -/

/-- A map continuous on an open neighbourhood `U` of a compact set `K` is uniformly continuous
near `K`: for every `ε > 0` there is `δ > 0` such that every point at distance `< δ` from a point
`x ∈ K` lies in `U` and its image is at distance `< ε` from the image of `x`. -/
theorem exists_forall_dist_lt_of_isCompact {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {g : X → Y} (hg : ContinuousOn g U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y, dist y x < δ → y ∈ U ∧ dist (g y) (g x) < ε := by
  set c : X → Set X := fun p ↦ U ∩ g ⁻¹' ball (g p) (ε / 2)
  have hc : ∀ p, IsOpen (c p) := fun p ↦ hg.isOpen_inter_preimage hU isOpen_ball
  have hcov : K ⊆ ⋃ p, c p := fun x hx ↦
    mem_iUnion.2 ⟨x, hKU hx, mem_ball_self (half_pos hε)⟩
  obtain ⟨δ, hδ, H⟩ := lebesgue_number_lemma_of_metric hK hc hcov
  refine ⟨δ, hδ, fun x hx y hy ↦ ?_⟩
  obtain ⟨p, hp⟩ := H x hx
  have hy' := hp (mem_ball.2 hy)
  have hx' := hp (mem_ball_self hδ)
  refine ⟨hy'.1, ?_⟩
  calc dist (g y) (g x) ≤ dist (g y) (g p) + dist (g x) (g p) := dist_triangle_right _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hy'.2 hx'.2
    _ = ε := add_halves ε

/-! ### Superposition operators on `C(K, E)` with the sup norm -/

section Superposition

variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]

variable (K) in
/-- The continuous maps `K → E` with values in `U`. -/
def mapsInto (U : Set E) : Set C(K, E) :=
  {γ | ∀ s, γ s ∈ U}

open scoped Classical in
/-- The **superposition operator** `γ ↦ f ∘ γ` on `C(K, E)` (with the junk value `0` when `f ∘ γ`
is not continuous; this never happens on `mapsInto K U` if `f` is continuous on `U`). -/
def superpose (f : E → F) (γ : C(K, E)) : C(K, F) :=
  if h : Continuous (f ∘ γ) then ⟨f ∘ γ, h⟩ else 0

omit [CompactSpace K] in
/-- On curves with values in `U`, the superposition operator of a map continuous on `U` is
`γ ↦ f ∘ γ`. -/
theorem superpose_apply {f : E → F} {U : Set E} (hf : ContinuousOn f U) {γ : C(K, E)}
    (hγ : γ ∈ mapsInto K U) (s : K) : superpose f γ s = f (γ s) := by
  have h : Continuous (f ∘ γ) := hf.comp_continuous γ.continuous hγ
  simp [superpose, h]

/-- Uniform continuity of `g` near the image of `γ ∈ mapsInto K U`. -/
theorem exists_forall_dist_lt_of_mem_mapsInto {G : Type*} [PseudoMetricSpace G] {U : Set E}
    (hU : IsOpen U) {g : E → G} (hg : ContinuousOn g U) {γ : C(K, E)} (hγ : γ ∈ mapsInto K U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, ∀ y, dist y (γ s) < δ → y ∈ U ∧ dist (g y) (g (γ s)) < ε := by
  obtain ⟨δ, hδ, H⟩ := exists_forall_dist_lt_of_isCompact (isCompact_range γ.continuous) hU
    (range_subset_iff.2 hγ) hg hε
  exact ⟨δ, hδ, fun s y hy ↦ H _ (mem_range_self s) y hy⟩

/-- `mapsInto K U` is open in the sup norm if `U` is open. -/
theorem isOpen_mapsInto {U : Set E} (hU : IsOpen U) : IsOpen (mapsInto K U) := by
  refine Metric.isOpen_iff.2 fun γ hγ ↦ ?_
  obtain ⟨δ, hδ, H⟩ := exists_forall_dist_lt_of_mem_mapsInto hU continuousOn_id hγ one_pos
  exact ⟨δ, hδ, fun γ' hγ' s ↦
    (H s _ ((ContinuousMap.dist_apply_le_dist (f := γ') (g := γ) s).trans_lt (mem_ball.1 hγ'))).1⟩

/-- Superposition with a map continuous on `U` is continuous on `mapsInto K U`. -/
theorem continuousOn_superpose {g : E → F} {U : Set E} (hU : IsOpen U) (hg : ContinuousOn g U) :
    ContinuousOn (superpose g) (mapsInto K U) := by
  refine Metric.continuousOn_iff.2 fun γ hγ ε hε ↦ ?_
  obtain ⟨δ, hδ, H⟩ := exists_forall_dist_lt_of_mem_mapsInto hU hg hγ (half_pos hε)
  refine ⟨δ, hδ, fun γ' hγ' hd ↦ ?_⟩
  refine ((ContinuousMap.dist_le (half_pos hε).le).2 fun s ↦ ?_).trans_lt (half_lt_self hε)
  rw [superpose_apply hg hγ', superpose_apply hg hγ]
  exact (H s _ ((ContinuousMap.dist_apply_le_dist (f := γ') (g := γ) s).trans_lt hd)).2.le

variable (𝕜 K E F) in
/-- Pointwise application `(A, γ) ↦ (s ↦ A s (γ s))`, as a continuous bilinear map
`C(K, L(E, F)) × C(K, E) → C(K, F)`. -/
def pointwiseApply : C(K, E →L[𝕜] F) →L[𝕜] C(K, E) →L[𝕜] C(K, F) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 (fun (A : C(K, E →L[𝕜] F)) (γ : C(K, E)) ↦
      (⟨fun s ↦ A s (γ s), A.continuous.clm_apply γ.continuous⟩ : C(K, F)))
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp))
    1 fun A γ ↦ by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun s ↦ ?_
      exact ((A s).le_opNorm (γ s)).trans
        (mul_le_mul (A.norm_coe_le_norm s) (γ.norm_coe_le_norm s) (norm_nonneg _)
          (norm_nonneg A))

/-- `pointwiseApply` evaluates pointwise. -/
@[simp]
theorem pointwiseApply_apply (A : C(K, E →L[𝕜] F)) (γ : C(K, E)) (s : K) :
    pointwiseApply 𝕜 K E F A γ s = A s (γ s) :=
  rfl

/-- **The derivative of a superposition operator.** If `f` is `C¹` on the open set `U`, then
`γ ↦ f ∘ γ` is Fréchet differentiable at every `γ ∈ mapsInto K U`, with derivative
`η ↦ (s ↦ f'(γ s) (η s))`. -/
theorem hasFDerivAt_superpose {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn 𝕜 1 f U)
    {γ : C(K, E)} (hγ : γ ∈ mapsInto K U) :
    HasFDerivAt (superpose f) (pointwiseApply 𝕜 K E F (superpose (fderiv 𝕜 f) γ)) γ := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hfc : ContinuousOn f U := hf.continuousOn
  have hDc : ContinuousOn (fderiv 𝕜 f) U := hf.continuousOn_fderiv_of_isOpen hU le_rfl
  have hDf : ∀ y ∈ U, HasFDerivAt f (fderiv 𝕜 f y) y := fun y hy ↦
    ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, H⟩ := exists_forall_dist_lt_of_mem_mapsInto hU hDc hγ hc
  filter_upwards [ball_mem_nhds (0 : C(K, E)) hδ] with η hη
  have hη' : ∀ s, ‖η s‖ < δ := fun s ↦
    (η.norm_coe_le_norm s).trans_lt (mem_ball_zero_iff.1 hη)
  have hγη : γ + η ∈ mapsInto K U := fun s ↦
    (H s _ (by simpa [dist_eq_norm] using hη' s)).1
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun s ↦ ?_
  simp only [ContinuousMap.sub_apply, pointwiseApply_apply, superpose_apply hfc hγη,
    superpose_apply hfc hγ, superpose_apply hDc hγ, ContinuousMap.add_apply]
  have hB : ball (γ s) δ ⊆ U := fun y hy ↦ (H s y hy).1
  have hmv := (convex_ball (γ s) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := f) (f' := fderiv 𝕜 f) (φ := fderiv 𝕜 f (γ s)) (C := c) (y := γ s + η s)
    (fun y hy ↦ (hDf y (hB hy)).hasFDerivWithinAt)
    (fun y hy ↦ by simpa [dist_eq_norm] using (H s y hy).2.le)
    (mem_ball_self hδ) (by simpa [mem_ball, dist_eq_norm] using hη' s)
  simp only [add_sub_cancel_left] at hmv
  exact hmv.trans (mul_le_mul_of_nonneg_left (η.norm_coe_le_norm s) hc.le)

/-- **Superposition operators are `C^n`.** If `f` is `C^n` on the open set `U`, then
`γ ↦ f ∘ γ` is Fréchet `C^n` on `mapsInto K U ⊆ C(K, E)`. -/
theorem contDiffOn_superpose_nat {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F},
      ContDiffOn 𝕜 n f U → ContDiffOn 𝕜 n (superpose (K := K) f) (mapsInto K U) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero] at hf ⊢
    exact continuousOn_superpose hU hf
  | succ n ih =>
    intro F _ _ f hf
    have hf1 : ContDiffOn 𝕜 1 f U := hf.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hD : ContDiffOn 𝕜 n (fderiv 𝕜 f) U := hf.fderiv_of_isOpen hU (by simp)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_mapsInto hU)]
    refine ⟨fun γ hγ ↦ (hasFDerivAt_superpose hU hf1 hγ).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine ((pointwiseApply 𝕜 K E F).contDiff.comp_contDiffOn (ih hD)).congr fun γ hγ ↦ ?_
    exact (hasFDerivAt_superpose hU hf1 hγ).fderiv

/-- **Superposition operators are `C^n`**, for `n ∈ ℕ ∪ {∞}`. -/
theorem contDiffOn_superpose {U : Set E} (hU : IsOpen U) {n : ℕ∞} {f : E → F}
    (hf : ContDiffOn 𝕜 n f U) : ContDiffOn 𝕜 n (superpose (K := K) f) (mapsInto K U) := by
  cases n with
  | top =>
    rw [contDiffOn_infty] at hf ⊢
    exact fun m ↦ contDiffOn_superpose_nat hU m (hf m)
  | coe m => exact contDiffOn_superpose_nat hU m hf

end Superposition

/-! ### The primitive operator on `C([-1, 1], E)` -/

/-- The interval `[-1, 1]`, on which the curves of the fixed point problem are parametrized. -/
local notation "𝕀" => (Icc (-1 : ℝ) 1)

section Primitive

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E]

/-- `[-1, 1]` is closed under multiplication. -/
theorem mul_mem_Icc_neg_one_one {a b : ℝ} (ha : a ∈ 𝕀) (hb : b ∈ 𝕀) : a * b ∈ 𝕀 := by
  have ha' : |a| ≤ 1 := abs_le.2 ha
  have hb' : |b| ≤ 1 := abs_le.2 hb
  refine abs_le.1 ?_
  rw [abs_mul]
  simpa using mul_le_mul ha' hb' (abs_nonneg _) zero_le_one

/-- The reparametrization `s ↦ σ s` of `[-1, 1]`, for `σ ∈ [-1, 1]`. -/
def scaleI (σ : 𝕀) : C(𝕀, 𝕀) :=
  ⟨fun s ↦ ⟨σ * s, mul_mem_Icc_neg_one_one σ.2 s.2⟩,
    (continuous_const.mul continuous_subtype_val).subtype_mk _⟩

/-- `scaleI σ` is multiplication by `σ`. -/
@[simp]
theorem scaleI_apply (σ s : 𝕀) : (scaleI σ s : ℝ) = σ * s :=
  rfl

/-- A curve on `[-1, 1]`, extended to `ℝ` by constants. -/
def extendI (γ : C(𝕀, E)) : ℝ → E :=
  IccExtend (by norm_num : (-1 : ℝ) ≤ 1) γ

omit [NormedSpace ℝ E] in
/-- The extension of a continuous curve is continuous. -/
theorem continuous_extendI (γ : C(𝕀, E)) : Continuous (extendI γ) :=
  γ.continuous.Icc_extend'

omit [NormedSpace ℝ E] in
/-- On `[-1, 1]`, the extension of a curve is the curve. -/
theorem extendI_of_mem (γ : C(𝕀, E)) {s : ℝ} (hs : s ∈ 𝕀) : extendI γ s = γ ⟨s, hs⟩ :=
  IccExtend_of_mem _ _ hs

omit [NormedSpace ℝ E] in
/-- The extension of a curve is bounded by its sup norm. -/
theorem norm_extendI_le (γ : C(𝕀, E)) (s : ℝ) : ‖extendI γ s‖ ≤ ‖γ‖ :=
  γ.norm_coe_le_norm _

variable (𝕜) in
/-- The **primitive operator** `γ ↦ (s ↦ ∫₀ˢ γ)` on `C([-1, 1], E)`, a continuous `𝕜`-linear map
of norm at most `1`. -/
def primitiveCLM : C(𝕀, E) →L[𝕜] C(𝕀, E) :=
  LinearMap.mkContinuous
    { toFun := fun γ ↦ ⟨fun s ↦ ∫ τ in (0 : ℝ)..s, extendI γ τ,
        (intervalIntegral.continuous_primitive
          (fun a b ↦ (continuous_extendI γ).intervalIntegrable a b) 0).comp
          continuous_subtype_val⟩
      map_add' := fun γ₁ γ₂ ↦ by
        ext s
        exact intervalIntegral.integral_add ((continuous_extendI γ₁).intervalIntegrable _ _)
          ((continuous_extendI γ₂).intervalIntegrable _ _)
      map_smul' := fun c γ ↦ by
        ext s
        exact intervalIntegral.integral_smul c _ }
    1 fun γ ↦ by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s ↦ ?_
      have hs : |(s : ℝ) - 0| ≤ 1 := by simpa using abs_le.2 s.2
      calc ‖∫ τ in (0 : ℝ)..s, extendI γ τ‖ ≤ ‖γ‖ * |(s : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ ↦ norm_extendI_le γ τ
        _ ≤ ‖γ‖ * 1 := by gcongr
        _ = ‖γ‖ := mul_one _

/-- `primitiveCLM γ s = ∫₀ˢ γ`. -/
@[simp]
theorem primitiveCLM_apply (γ : C(𝕀, E)) (s : 𝕀) :
    primitiveCLM 𝕜 γ s = ∫ τ in (0 : ℝ)..s, extendI γ τ :=
  rfl

/-- The fundamental theorem of calculus for the primitive operator. -/
theorem hasDerivAt_primitive [CompleteSpace E] (γ : C(𝕀, E)) (t : ℝ) :
    HasDerivAt (fun u ↦ ∫ τ in (0 : ℝ)..u, extendI γ τ) (extendI γ t) t :=
  ((continuous_extendI γ).integral_hasStrictDerivAt 0 t).hasDerivAt

end Primitive

/-! ### The fixed point problem and its derivative -/

section FlowMap

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable (𝕜) in
/-- The constant curves, `x ↦ (s ↦ x)`, as a continuous linear map `E → C([-1, 1], E)`. -/
def constI : E →L[𝕜] C(𝕀, E) :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ContinuousMap.const 𝕀 x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun x ↦ by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun _ ↦ le_rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- `constI x` is the constant curve `x`. -/
@[simp]
theorem constI_apply (x : E) (s : 𝕀) : constI 𝕜 x s = x :=
  rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable (𝕜) in
/-- Evaluation at `s ∈ [-1, 1]`, as a continuous linear map `C([-1, 1], E) → E`. -/
def evalI (s : 𝕀) : C(𝕀, E) →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun γ ↦ γ s
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun γ ↦ by
      rw [one_mul]
      exact γ.norm_coe_le_norm s

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- `evalI s` evaluates at `s`. -/
@[simp]
theorem evalI_apply (s : 𝕀) (γ : C(𝕀, E)) : evalI 𝕜 s γ = γ s :=
  rfl

variable (𝕜) in
/-- The map `Ψ(λ, x, γ) = (λ, x, γ - x - λ ∫₀ f ∘ γ)` on `𝕜 × E × C([-1, 1], E)`. Its zeros in
the last component are the curves `γ` with `γ(s) = x + λ ∫₀ˢ f(γ(τ)) dτ`, i.e. the solutions of
`γ' = λ f ∘ γ` with `γ(0) = x`. -/
def flowEqMap (f : E → E) (p : 𝕜 × E × C(𝕀, E)) : 𝕜 × E × C(𝕀, E) :=
  (p.1, p.2.1, p.2.2 - constI 𝕜 p.2.1 - p.1 • primitiveCLM 𝕜 (superpose f p.2.2))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable (𝕜) in
/-- The shear `(a, b, c) ↦ (a, b, c + σ (b + a w))` of `𝕜 × E × C([-1, 1], E)`. -/
def shearCLM (σ : 𝕜) (w : C(𝕀, E)) : (𝕜 × E × C(𝕀, E)) →L[𝕜] (𝕜 × E × C(𝕀, E)) :=
  (ContinuousLinearMap.fst 𝕜 𝕜 (E × C(𝕀, E))).prod
    (((ContinuousLinearMap.fst 𝕜 E C(𝕀, E)).comp (ContinuousLinearMap.snd 𝕜 𝕜 (E × C(𝕀, E)))).prod
      ((ContinuousLinearMap.snd 𝕜 E C(𝕀, E)).comp (ContinuousLinearMap.snd 𝕜 𝕜 (E × C(𝕀, E))) +
        σ • ((constI 𝕜).comp ((ContinuousLinearMap.fst 𝕜 E C(𝕀, E)).comp
          (ContinuousLinearMap.snd 𝕜 𝕜 (E × C(𝕀, E)))) +
          (ContinuousLinearMap.fst 𝕜 𝕜 (E × C(𝕀, E))).smulRight w)))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- The formula for the shear. -/
@[simp]
theorem shearCLM_apply (σ : 𝕜) (w : C(𝕀, E)) (p : 𝕜 × E × C(𝕀, E)) :
    shearCLM 𝕜 σ w p = (p.1, p.2.1, p.2.2 + σ • (constI 𝕜 p.2.1 + p.1 • w)) :=
  rfl

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
variable (𝕜) in
/-- The shear `(a, b, c) ↦ (a, b, c - b - a w)` as a linear homeomorphism. -/
def shearEquiv (w : C(𝕀, E)) : (𝕜 × E × C(𝕀, E)) ≃L[𝕜] (𝕜 × E × C(𝕀, E)) :=
  ContinuousLinearEquiv.equivOfInverse (shearCLM 𝕜 (-1) w) (shearCLM 𝕜 1 w)
    (fun p ↦ Prod.ext rfl (Prod.ext rfl (by simp; abel)))
    (fun p ↦ Prod.ext rfl (Prod.ext rfl (by simp; abel)))

/-- `Ψ` is `C^n` where `γ` takes values in `U`. -/
theorem contDiffOn_flowEqMap {f : E → E} {U : Set E} (hU : IsOpen U) {n : ℕ∞}
    (hf : ContDiffOn 𝕜 n f U) :
    ContDiffOn 𝕜 n (flowEqMap 𝕜 f) {p : 𝕜 × E × C(𝕀, E) | p.2.2 ∈ mapsInto 𝕀 U} := by
  have hN : ContDiffOn 𝕜 n (fun p : 𝕜 × E × C(𝕀, E) ↦ superpose f p.2.2)
      {p : 𝕜 × E × C(𝕀, E) | p.2.2 ∈ mapsInto 𝕀 U} :=
    (contDiffOn_superpose hU hf).comp (contDiff_snd.comp contDiff_snd).contDiffOn
      fun p hp ↦ hp
  refine contDiffOn_fst.prodMk ((contDiff_fst.comp contDiff_snd).contDiffOn.prodMk ?_)
  refine ((contDiff_snd.comp contDiff_snd).contDiffOn.sub
    ((constI 𝕜 (E := E)).contDiff.comp (contDiff_fst.comp contDiff_snd)).contDiffOn).sub ?_
  exact contDiffOn_fst.smul ((primitiveCLM 𝕜 (E := E)).contDiff.comp_contDiffOn hN)

/-- At a point `(0, x, γ)`, the derivative of `Ψ` is the shear `(a, b, c) ↦ (a, b, c - b - a w)`
with `w = ∫₀ f ∘ γ`; in particular it is invertible. -/
theorem hasFDerivAt_flowEqMap {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn 𝕜 1 f U)
    {x : E} {γ : C(𝕀, E)} (hγ : γ ∈ mapsInto 𝕀 U) :
    HasFDerivAt (flowEqMap 𝕜 f)
      ((shearEquiv 𝕜 (primitiveCLM 𝕜 (superpose f γ)) : (𝕜 × E × C(𝕀, E)) →L[𝕜] _))
      (0, x, γ) := by
  set p : 𝕜 × E × C(𝕀, E) := (0, x, γ)
  have h2 : HasFDerivAt (fun q : 𝕜 × E × C(𝕀, E) ↦ q.2.2) _ p :=
    (hasFDerivAt_snd (𝕜 := 𝕜) (p := p)).snd
  have hN := (hasFDerivAt_superpose hU hf hγ).comp p h2
  have hJ := (primitiveCLM 𝕜).hasFDerivAt.comp p hN
  have hsm := (hasFDerivAt_fst (𝕜 := 𝕜) (p := p)).smul hJ
  have hc := (constI 𝕜).hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := 𝕜) (p := p)).fst
  have H := (hasFDerivAt_fst (𝕜 := 𝕜) (p := p)).prodMk
    ((hasFDerivAt_snd (𝕜 := 𝕜) (p := p)).fst.prodMk ((h2.sub hc).sub hsm))
  refine H.congr_fderiv ?_
  ext v
  all_goals simp [p, shearEquiv, sub_eq_add_neg, add_comm]

end FlowMap

/-! ### Local flows with smooth dependence on the initial condition -/

section Flow

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

/-- **Local flows with `C^n` dependence on time and initial condition, over `𝕜 = ℝ` or `ℂ`.**
Let `f` be `C^n` over `𝕜` (`1 ≤ n ≤ ∞`) on an open set `U` of a Banach space `E` over `𝕜`, and
`x₀ ∈ U`. There are `ε > 0`, an open neighbourhood `V` of `x₀` and a map `Fl : 𝕜 × E → E`,
jointly `C^n` over `𝕜` on `B_𝕜(0, ε) × V`, with values in `U` there and `Fl(0, x) = x`, such
that for every `x ∈ V` the curve of real time `t ↦ Fl(t, x)`, `|t| < ε`, is a solution of
`c' = f ∘ c`.

For `𝕜 = ℂ` the flow is holomorphic in complex time and initial value (for `t ∈ ℂ` the curve
`s ↦ Fl(s t, x)`, `s ∈ [-1, 1]`, solves `c' = t f ∘ c`). -/
theorem exists_contDiffOn_flow_rclike {f : E → E} {U : Set E} (hU : IsOpen U) {n : ℕ∞}
    (hn : 1 ≤ n) (hf : ContDiffOn 𝕜 n f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ Fl : 𝕜 × E → E,
      ContDiffOn 𝕜 n Fl (ball (0 : 𝕜) ε ×ˢ V) ∧ ∀ x ∈ V, Fl (0, x) = x ∧
        (∀ t ∈ ball (0 : 𝕜) ε, Fl (t, x) ∈ U) ∧
        ∀ t : ℝ, |t| < ε → HasDerivAt (fun s : ℝ ↦ Fl ((s : 𝕜), x)) (f (Fl ((t : 𝕜), x))) t := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le hn1).ne'
  have hf1 : ContDiffOn 𝕜 1 f U := hf.of_le hn1
  have hfc : ContinuousOn f U := hf.continuousOn
  set D : Set (𝕜 × E × C(𝕀, E)) := {p | p.2.2 ∈ mapsInto 𝕀 U}
  have hD : IsOpen D := (isOpen_mapsInto hU).preimage (continuous_snd.comp continuous_snd)
  set γ₀ : C(𝕀, E) := constI 𝕜 x₀
  set p₀ : 𝕜 × E × C(𝕀, E) := (0, x₀, γ₀)
  have hp₀ : p₀ ∈ D := fun _ ↦ hx₀
  have hΨ : ContDiffOn 𝕜 n (flowEqMap 𝕜 f) D := contDiffOn_flowEqMap hU hf
  have hder := hasFDerivAt_flowEqMap (x := x₀) hU hf1 hp₀
  -- the inverse function theorem at `p₀`
  set H := (hΨ.contDiffAt (hD.mem_nhds hp₀)).toOpenPartialHomeomorph (flowEqMap 𝕜 f) hder hn0
  have hH : ∀ p, H p = flowEqMap 𝕜 f p := fun _ ↦ rfl
  -- the open set where the derivative of `Ψ` is invertible
  set S := D ∩ fderiv 𝕜 (flowEqMap 𝕜 f) ⁻¹'
    range ((↑) : ((𝕜 × E × C(𝕀, E)) ≃L[𝕜] (𝕜 × E × C(𝕀, E))) → _ →L[𝕜] _)
  have hS : IsOpen S := (hΨ.continuousOn_fderiv_of_isOpen hD hn1).isOpen_inter_preimage hD
    ContinuousLinearEquiv.isOpen
  have hp₀S : p₀ ∈ S := ⟨hp₀, _, hder.fderiv.symm⟩
  set V₀ := H.target ∩ H.symm ⁻¹' S
  have hV₀ : IsOpen V₀ := H.continuousOn_symm.isOpen_inter_preimage H.open_target hS
  have hsymm : ContDiffOn 𝕜 n H.symm V₀ := by
    intro q hq
    obtain ⟨hqD, e, he⟩ := hq.2
    have hd : HasFDerivAt H (e : _ →L[𝕜] _) (H.symm q) := by
      rw [he]
      exact (((hΨ.differentiableOn hn0) _ hqD).differentiableAt (hD.mem_nhds hqD)).hasFDerivAt
    exact (H.contDiffAt_symm hq.1 hd (hΨ.contDiffAt (hD.mem_nhds hqD))).contDiffWithinAt
  have hq₀ : flowEqMap 𝕜 f p₀ = (0, x₀, 0) := by
    simp [flowEqMap, p₀, γ₀]
  have hp₀src : p₀ ∈ H.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ hder hn0
  have hq₀tgt : ((0 : 𝕜), x₀, (0 : C(𝕀, E))) ∈ H.target := by
    rw [← hq₀]; exact ContDiffAt.image_mem_toOpenPartialHomeomorph_target _ hder hn0
  have hsymm₀ : H.symm (0, x₀, 0) = p₀ := by rw [← hq₀, ← hH]; exact H.left_inv hp₀src
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.1
    (inter_mem (H.open_source.mem_nhds hp₀src) (hD.mem_nhds hp₀))
  have hW : V₀ ∩ H.symm ⁻¹' ball p₀ a ∈ 𝓝 ((0 : 𝕜), x₀, (0 : C(𝕀, E))) := by
    refine inter_mem (hV₀.mem_nhds ⟨hq₀tgt, ?_⟩)
      ((H.continuousAt_symm hq₀tgt).preimage_mem_nhds ?_)
    · rw [mem_preimage, hsymm₀]; exact hp₀S
    · rw [hsymm₀]; exact ball_mem_nhds _ ha
  obtain ⟨b, hb, hbW⟩ := Metric.mem_nhds_iff.1 hW
  have hqb : ∀ (t : 𝕜) x, ‖t‖ < b → x ∈ ball x₀ b →
      ((t, x, 0) : 𝕜 × E × C(𝕀, E)) ∈ ball ((0 : 𝕜), x₀, (0 : C(𝕀, E))) b := by
    intro t x ht hx
    rw [mem_ball] at hx ⊢
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_zero_right]
    exact max_lt ht (max_lt hx hb)
  -- the solutions `Γ(t, x)` of the fixed point problem
  set Γ : 𝕜 × E → C(𝕀, E) := fun q ↦ (H.symm (q.1, q.2, 0)).2.2 with hΓ_def
  have key : ∀ (t : 𝕜) x, ‖t‖ < b → x ∈ ball x₀ b →
      H.symm (t, x, 0) = (t, x, Γ (t, x)) ∧ (t, x, Γ (t, x)) ∈ ball p₀ a ∧
      Γ (t, x) ∈ mapsInto 𝕀 U ∧
      Γ (t, x) = constI 𝕜 x + t • primitiveCLM 𝕜 (superpose f (Γ (t, x))) := by
    intro t x ht hx
    obtain ⟨⟨hqV, -⟩, hqa⟩ := hbW (hqb t x ht hx)
    have hHp : flowEqMap 𝕜 f (H.symm (t, x, 0)) = (t, x, 0) := by
      rw [← hH]; exact H.right_inv hqV
    have h1 : (H.symm (t, x, 0)).1 = t := congrArg Prod.fst hHp
    have h2 : (H.symm (t, x, 0)).2.1 = x := congrArg (fun q ↦ q.2.1) hHp
    have h3 := congrArg (fun q ↦ q.2.2) hHp
    simp only [flowEqMap, h1, h2] at h3
    have hp : H.symm (t, x, 0) = (t, x, Γ (t, x)) := Prod.ext h1 (Prod.ext h2 rfl)
    refine ⟨hp, by rw [← hp]; exact hqa, (has hqa).2, ?_⟩
    rw [sub_sub] at h3
    exact sub_eq_zero.1 h3
  set one : 𝕀 := ⟨1, by norm_num⟩
  set Fl : 𝕜 × E → E := fun q ↦ Γ q one with hFl_def
  -- **rescaling**: `Fl(σ l, x) = Γ(l, x)(σ)` for real `σ`, by uniqueness in the inverse function
  -- theorem
  have hscale : ∀ (l : 𝕜) x, ‖l‖ < b → x ∈ ball x₀ b → ∀ σ : 𝕀,
      Fl (((σ : ℝ) : 𝕜) * l, x) = Γ (l, x) σ := by
    intro l x hl hx σ
    have hσ : |(σ : ℝ)| ≤ 1 := abs_le.2 σ.2
    have hσl' : ‖((σ : ℝ) : 𝕜) * l‖ ≤ ‖l‖ := by
      rw [norm_mul, RCLike.norm_ofReal]; exact mul_le_of_le_one_left (norm_nonneg l) hσ
    have hσl : ‖((σ : ℝ) : 𝕜) * l‖ < b := hσl'.trans_lt hl
    obtain ⟨-, hball, hmaps, heq⟩ := key l x hl hx
    set δ := (Γ (l, x)).comp (scaleI σ)
    have hδmaps : δ ∈ mapsInto 𝕀 U := fun s ↦ hmaps _
    have hδball : ((((σ : ℝ) : 𝕜) * l), x, δ) ∈ ball p₀ a := by
      simp only [mem_ball, Prod.dist_eq] at hball ⊢
      refine max_lt ?_ (max_lt ?_ ?_)
      · calc dist (((σ : ℝ) : 𝕜) * l) 0 ≤ dist l 0 := by simpa [dist_zero_right] using hσl'
          _ < a := (le_max_left _ _).trans_lt hball
      · exact ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hball
      · refine lt_of_le_of_lt ?_ (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hball)
        refine (ContinuousMap.dist_le dist_nonneg).2 fun s ↦ ?_
        exact ContinuousMap.dist_apply_le_dist (f := Γ (l, x)) (g := γ₀) (scaleI σ s)
    have hδeq : flowEqMap 𝕜 f ((((σ : ℝ) : 𝕜) * l), x, δ) = ((((σ : ℝ) : 𝕜) * l), x, 0) := by
      refine Prod.ext rfl (Prod.ext rfl ?_)
      ext s
      have hsI : (s : ℝ) ∈ 𝕀 := s.2
      have h1 : δ s = x + l • ∫ τ in (0 : ℝ)..(σ * s), extendI (superpose f (Γ (l, x))) τ := by
        change Γ (l, x) (scaleI σ s) = _
        conv_lhs => rw [heq]
        simp
      have h2 : ∫ τ in (0 : ℝ)..s, extendI (superpose f δ) τ =
          ∫ τ in (0 : ℝ)..s, extendI (superpose f (Γ (l, x))) (σ * τ) := by
        refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
        have hτI : τ ∈ 𝕀 := uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hsI hτ
        rw [extendI_of_mem _ hτI, extendI_of_mem _ (mul_mem_Icc_neg_one_one σ.2 hτI),
          superpose_apply hfc hδmaps, superpose_apply hfc hmaps]
        rfl
      simp only [flowEqMap, ContinuousMap.sub_apply, ContinuousMap.smul_apply, constI_apply,
        primitiveCLM_apply, ContinuousMap.zero_apply]
      rw [h2, h1, mul_comm _ l, mul_smul, ← RCLike.real_smul_eq_coe_smul (K := 𝕜),
        intervalIntegral.smul_integral_comp_mul_left, mul_zero]
      abel
    have hsrc₁ : ((((σ : ℝ) : 𝕜) * l), x, δ) ∈ H.source := (has hδball).1
    have htgt : ((((σ : ℝ) : 𝕜) * l), x, (0 : C(𝕀, E))) ∈ H.target :=
      (hbW (hqb _ x hσl hx)).1.1
    have hinj : ((((σ : ℝ) : 𝕜) * l), x, δ) = H.symm ((((σ : ℝ) : 𝕜) * l), x, 0) :=
      H.injOn hsrc₁ (H.map_target htgt) (by rw [H.right_inv htgt]; exact hδeq)
    have hδ1 : δ one = Γ (l, x) σ := congrArg (Γ (l, x)) (Subtype.ext (mul_one _))
    change (H.symm ((((σ : ℝ) : 𝕜) * l), x, 0)).2.2 one = _
    rw [← hinj]
    exact hδ1
  refine ⟨b, hb, ball x₀ b, isOpen_ball, mem_ball_self hb, Fl, ?_,
    fun x hx ↦ ⟨?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩⟩
  · -- smoothness
    have hι : ContDiff 𝕜 n (fun q : 𝕜 × E ↦ ((q.1, q.2, 0) : 𝕜 × E × C(𝕀, E))) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
    have hmaps : MapsTo (fun q : 𝕜 × E ↦ ((q.1, q.2, 0) : 𝕜 × E × C(𝕀, E)))
        (ball (0 : 𝕜) b ×ˢ ball x₀ b) V₀ := fun q hq ↦
      (hbW (hqb _ _ (mem_ball_zero_iff.1 hq.1) hq.2)).1
    exact ((evalI 𝕜 (E := E) one).contDiff.comp
      (contDiff_snd.comp contDiff_snd)).comp_contDiffOn (hsymm.comp hι.contDiffOn hmaps)
  · obtain ⟨-, -, -, heq⟩ := key 0 x (by simpa using hb) hx
    change Γ (0, x) one = x
    rw [heq]
    simp
  · exact (key t x (mem_ball_zero_iff.1 ht) hx).2.2.1 one
  · -- the derivative in real time, from the rescaling identity
    set l : ℝ := (|t| + b) / 2
    have hl0 : 0 < l := by positivity
    have htl : |t| < l := by simp only [l]; linarith
    have hl : ‖(l : 𝕜)‖ < b := by
      rw [RCLike.norm_ofReal, abs_of_pos hl0]; simp only [l]; linarith
    obtain ⟨-, -, hmaps, heq⟩ := key l x hl hx
    set g := extendI (superpose f (Γ ((l : 𝕜), x))) with hg
    have hmemI : ∀ s, |s| < l → s / l ∈ 𝕀 := fun s hs ↦ by
      have := abs_lt.1 hs
      exact ⟨by rw [le_div_iff₀ hl0]; linarith, by rw [div_le_iff₀ hl0]; linarith⟩
    have hFl : ∀ s (hs : |s| < l), Fl ((s : 𝕜), x) = Γ ((l : 𝕜), x) ⟨s / l, hmemI s hs⟩ :=
      fun s hs ↦ by
        have h' : (((s / l : ℝ) : 𝕜) * (l : 𝕜)) = (s : 𝕜) := by
          rw [← RCLike.ofReal_mul, div_mul_cancel₀ s hl0.ne']
        have := hscale (l : 𝕜) x hl hx ⟨s / l, hmemI s hs⟩
        change Fl ((((s / l : ℝ)) : 𝕜) * (l : 𝕜), x) = _ at this
        rwa [h'] at this
    have hev : (fun s : ℝ ↦ x + (l : 𝕜) • ∫ τ in (0 : ℝ)..(s / l), g τ) =ᶠ[𝓝 t]
        fun s : ℝ ↦ Fl ((s : 𝕜), x) := by
      have htl' := abs_lt.1 htl
      filter_upwards [Ioo_mem_nhds htl'.1 htl'.2] with s hs
      rw [hFl s (abs_lt.2 hs), heq]
      simp [g]
    have hd : HasDerivAt (fun s : ℝ ↦ x + (l : 𝕜) • ∫ τ in (0 : ℝ)..(s / l), g τ)
        (g (t / l)) t := by
      have h1 := (hasDerivAt_primitive (superpose f (Γ ((l : 𝕜), x))) (t / l)).scomp t
        ((hasDerivAt_id t).div_const l)
      refine ((h1.const_smul (l : 𝕜)).const_add x).congr_deriv ?_
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul, ← RCLike.ofReal_mul,
        mul_one_div_cancel hl0.ne', RCLike.ofReal_one, one_smul, hg]
    refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    rw [hg, extendI_of_mem _ (hmemI t htl), superpose_apply hfc hmaps, hFl t htl]

/-- **Local flows of `C^n` vector fields on Banach spaces, with `C^n` dependence on the initial
condition.** Let `f` be `C^n` (`1 ≤ n ≤ ∞`) on an open set `U` of a Banach space `E`, and
`x₀ ∈ U`. There are `ε > 0`, an open neighbourhood `V` of `x₀` and a map `Fl : ℝ × E → E`,
jointly `C^n` on `(-ε, ε) × V`, such that for every `x ∈ V` the curve `t ↦ Fl(t, x)` is a
solution of `c' = f ∘ c` on `(-ε, ε)` with values in `U` and `c(0) = x`. This is the case
`𝕜 = ℝ` of `exists_contDiffOn_flow_rclike`. -/
theorem exists_contDiffOn_flow {f : E → E} {U : Set E} (hU : IsOpen U) {n : ℕ∞} (hn : 1 ≤ n)
    (hf : ContDiffOn ℝ n f U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ Fl : ℝ × E → E,
      ContDiffOn ℝ n Fl (Ioo (-ε) ε ×ˢ V) ∧ ∀ x ∈ V, Fl (0, x) = x ∧
        ∀ t ∈ Ioo (-ε) ε, Fl (t, x) ∈ U ∧ HasDerivAt (fun s ↦ Fl (s, x)) (f (Fl (t, x))) t := by
  obtain ⟨ε, hε, V, hV, hx₀V, Fl, hFl, H⟩ :=
    exists_contDiffOn_flow_rclike (𝕜 := ℝ) hU hn hf hx₀
  have hball : ball (0 : ℝ) ε = Ioo (-ε) ε := by rw [Real.ball_eq_Ioo]; simp
  refine ⟨ε, hε, V, hV, hx₀V, Fl, hball ▸ hFl, fun x hx ↦ ⟨(H x hx).1, fun t ht ↦
    ⟨(H x hx).2.1 t (hball ▸ ht), ?_⟩⟩⟩
  simpa using (H x hx).2.2 t (abs_lt.2 ht)

/-- **Smooth local flows in the sense of Michal–Bastiani.** If `f` is smooth in the sense of
Michal–Bastiani on the open set `U` of a Banach space, its local flows are jointly smooth in the
sense of Michal–Bastiani. (On normed spaces this is the same as Fréchet smoothness,
`smoothMBOn_iff_contDiffOn`.) -/
theorem exists_smoothMBOn_flow {f : E → E} {U : Set E} (hU : IsOpen U) (hf : SmoothMBOn f U)
    {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ε > (0 : ℝ), ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∃ Fl : ℝ × E → E,
      SmoothMBOn Fl (Ioo (-ε) ε ×ˢ V) ∧ ∀ x ∈ V, Fl (0, x) = x ∧
        ∀ t ∈ Ioo (-ε) ε, Fl (t, x) ∈ U ∧ HasDerivAt (fun s ↦ Fl (s, x)) (f (Fl (t, x))) t := by
  obtain ⟨ε, hε, V, hV, hx₀V, Fl, hFl, H⟩ := exists_contDiffOn_flow hU (n := ⊤) le_top
    ((smoothMBOn_iff_contDiffOn hU).1 hf) hx₀
  exact ⟨ε, hε, V, hV, hx₀V, Fl, (smoothMBOn_iff_contDiffOn (isOpen_Ioo.prod hV)).2 hFl, H⟩

omit [CompleteSpace E] in
/-- **Uniqueness of solutions** of `c' = f ∘ c` for `f` of class `C¹` on an open set `U`: two
solutions on `(a, b)` with values in `U` that agree at one instant agree on `(a, b)`. This is
`eqOn_Ioo_of_locallyLipschitz`, which rests on Mathlib's `ODE_solution_unique_of_eventually`. In
particular the curves `t ↦ Fl(t, x)` of `exists_contDiffOn_flow` are the only solutions with
`c(0) = x` on `(-ε, ε)`. -/
theorem eqOn_Ioo_of_contDiffOn {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {c₁ c₂ : ℝ → E} {a b : ℝ}
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt c₁ (f (c₁ t)) t ∧ c₁ t ∈ U)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt c₂ (f (c₂ t)) t ∧ c₂ t ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (heq : c₁ t₀ = c₂ t₀) : EqOn c₁ c₂ (Ioo a b) :=
  eqOn_Ioo_of_locallyLipschitz
    (fun _ hp ↦ (hf.contDiffAt (hU.mem_nhds hp)).exists_lipschitzOnWith) h₁ h₂ ht₀ heq

end Flow

end LocallyConvex.Analysis

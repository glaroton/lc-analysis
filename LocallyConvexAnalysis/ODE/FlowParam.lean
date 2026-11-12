/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.FixedPointParam
public import LocallyConvexAnalysis.MappingSpace.SuperpositionParam
public import LocallyConvexAnalysis.Analytic.ComplexC1
public import LocallyConvexAnalysis.ODE.Flow
public import LocallyConvexAnalysis.MappingSpace.CkSuperposition
public import LocallyConvexAnalysis.Calculus.Rules

/-!
# Dependence of solutions on parameters in a locally convex space

Reference: [GN26, Theorem 2.4.34] (pp. 203–206).

Let `𝕂 ∈ {ℝ, ℂ}`, `E` a Banach space and `W` a locally convex space over `𝕂`, and
`f : 𝕂 × E × W → E` defined on an open set `O`. The solution map `Φ(t, t₀, y₀, p)` of
`y' = f(t, y, p)`, `y(t₀) = y₀`, is constructed on a neighbourhood of a given point
(`ODEFlowParam.flowPhi`), uniformly for the construction in both cases.

## Main definitions

* `ODEFlowParam.FlowData f O q₀`: radii and bounds for the fixed point problem
  ([GN26, (2.103) and (2.104)]).
* `ODEFlowParam.gMap f`: the map `g(z, η)(τ) = ∫₀^τ H(s, η(s), z) ds` on `C([-1, 1], E)`.
* `ODEFlowParam.eta D hfc z`: the fixed point `η_z ∈ C([-1, 1], E)` of `g(z, ·)`.
* `ODEFlowParam.flowPhi D hfc`: the solution map `Φ(t, t₀, y₀, p) = η_{t,t₀,y₀,p}(1) + y₀`
  ([GN26, p. 205]).

## Main results

* `ODEFlowParam.uniformContraction`: the maps `g(z, ·)` form a uniform family of
  `1/2`-contractions of the ball of radius `R` of `C([-1, 1], E)`, mapping the closed ball of
  radius `R/2` into itself.
* `ODEFlowParam.contDiffMBOn_flowPhi_of_contDiffMBOn`: the solution map is `C^k` if `f` is
  ([GN26, Theorem 2.4.34]).
* `ODEFlowParam.eta_rescale`: the rescaling identity
  `η(t₀ + σ (t - t₀), t₀, y₀, p) = η(t, t₀, y₀, p)(σ ·)` for `σ ∈ [0, 1]` ([GN26, (2.107)]).
* `ODEFlowParam.hasDerivAt_flowPhi_time_of`: the solutions solve the differential equation
  `∂ₜ Φ(t, t₀, y₀, p) = f(t, Φ(t, t₀, y₀, p), p)`, given a derivative in time continuous at `t`.
* `ODEFlowParam.complexAnalyticOn_flowPhi`: for `f` complex analytic, the solution map is complex
  analytic ([GN26, Theorem 2.4.34], case `𝕂 = ℂ`).
* `ODEFlowParam.flowPhi_mem_of_real`: real data give real solutions (cf. [GN26, Lemma 2.4.30]).
* `exists_complexAnalyticOn_flow_param` (`𝕂 = ℂ`): for `f` complex analytic, `Φ` is complex
  analytic in all variables, and real data give real solutions.
* `exists_contDiffMBOn_flow_lcParam` (`𝕂 = ℝ`): for `f` of class `C^k`, `k ≥ 1`, `Φ` is `C^k` in
  all variables.
* `exists_continuousOn_flow_lcParam` (`𝕂 = ℝ`, `k = 0`): for `f` continuous and Lipschitz in `y`
  near the point, uniformly in the other variables, `Φ` is continuous.

## Implementation notes

We follow Glöckner–Neeb. For `z = (t, t₀, y₀, p)`, the curve `η_z ∈ C([-1, 1], E)` with
`η_z(τ) = Φ(t₀ + τ (t - t₀), t₀, y₀, p) - y₀` is the fixed point of

  `g(z, η)(τ) = ∫₀^τ H(s, η(s), z) ds`,  `H(s, y, z) = (t - t₀) f(t₀ + s (t - t₀), y + y₀, p)`.

On small radii (`FlowData`, [GN26, (2.103) and (2.104)]) the maps `g(z, ·)` form a uniform
family of `1/2`-contractions of a closed ball (`uniformContraction`).

* If `f` is `C^k`, so is `g`, by the results on superposition operators with parameters
  (`contDiffMBOn_superposeParam_of_contDiffMBOn`), hence so are `z ↦ η_z`
  (`UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn`) and `Φ(z) = η_z(1) + y₀`
  (`contDiffMBOn_flowPhi_of_contDiffMBOn`).
* In the complex case, `C^1` suffices: the differential of `z ↦ η_z` is complex linear since it is
  a Neumann series of complex linear maps (`derivFixedPoint_smul`), and `Φ` is complex analytic
  (`complexAnalyticOn_of_contDiffMBOn_one`, [GN26, Theorem 2.1.12] (f) ⇒ (d)).

The rescaling identity `η_{t₀ + σ(t - t₀), t₀, y₀, p} = η_{t, t₀, y₀, p}(σ ·)`, `σ ∈ [0, 1]`
([GN26, (2.107)]), follows from the uniqueness of fixed points (`eta_rescale`). It shows
that along the segment from `t₀` to `t` the solution is a primitive, which gives the differential
equation for `t ≠ t₀`; at `t = t₀` it follows by continuity of the derivative in time
(`hasDerivAt_flowPhi_time_of`).

If `f` is real on real data (with respect to a closed real subspace of `E`), the maps `g(z, ·)`
for real `z` preserve the closed set of curves with values in that subspace, which therefore
contains the fixed point (`flowPhi_mem_of_real`). This is what the real analytic case needs
(`ODE/FlowParamReal.lean`); Glöckner–Neeb obtain it from real local solutions and uniqueness
(Lemma 2.4.30).

* The Lipschitz constant in `y` comes from the continuity of `df` at the base point, not from
  Cauchy estimates; no boundedness of `f` on a neighbourhood in `W` is required beyond the one
  given by continuity.
* The bounds of `FlowData` come from `C^1` (`exists_bounds`) or, for `k = 0`, from continuity and
  a uniform Lipschitz condition (`exists_bounds_of_lipschitz`). For `k = 0` the differential
  equation follows from the integral representation
  `Φ(r, t₀, y₀, p) = y₀ + ∫_{t₀}^r f(v, Φ(v, t₀, y₀, p), p) dv`
  (`hasDerivAt_flowPhi_time_continuous`).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology NNReal

noncomputable section

namespace LocallyConvex.Analysis

namespace ODEFlowParam

section General

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕂 E] [IsScalarTower ℝ 𝕂 E]
  [CompleteSpace E]
  {W : Type*} [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W]

/-- The parameters `z = (t, t₀, y₀, p)`. -/
abbrev Par (𝕂 E W : Type*) := 𝕂 × 𝕂 × E × W

/-- The point `(t₀ + s (t - t₀), y + y₀, p)` at which `f` is evaluated. -/
def evalPt (s : ℝ) (x : E × Par 𝕂 E W) : 𝕂 × E × W :=
  (x.2.2.1 + (s : 𝕂) * (x.2.1 - x.2.2.1), x.1 + x.2.2.2.1, x.2.2.2.2)

/-- The linear part of `evalPt s`. -/
def evalPtLin (s : ℝ) (v : E × Par 𝕂 E W) : 𝕂 × E × W :=
  (v.2.2.1 + (s : 𝕂) * (v.2.1 - v.2.2.1), v.1 + v.2.2.2.1, v.2.2.2.2)

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [NormedSpace 𝕂 E] [IsScalarTower ℝ 𝕂 E] in
theorem evalPt_add_smul (s : ℝ) (x v : E × Par 𝕂 E W) (r : ℝ) :
    evalPt s (x + r • v) = evalPt s x + r • evalPtLin s v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [evalPt, evalPtLin, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      RCLike.real_smul_eq_coe_mul]
    ring
  · simp only [evalPt, evalPtLin, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_add]
    abel
  · simp [evalPt, evalPtLin]

omit [CompleteSpace E] [Module ℝ W] [IsScalarTower ℝ 𝕂 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕂 E] in
theorem evalPtLin_smul (s : ℝ) (c : 𝕂) (v : E × Par 𝕂 E W) :
    evalPtLin s (c • v) = c • evalPtLin s v := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [evalPtLin, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  · simp [evalPtLin, smul_add]
  · simp [evalPtLin]

omit [NormedSpace 𝕂 E] [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem continuous_evalPt : Continuous fun r : ℝ × (E × Par 𝕂 E W) ↦ evalPt r.1 r.2 := by
  unfold evalPt; fun_prop

omit [NormedSpace 𝕂 E] [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem continuous_evalPtLin : Continuous fun r : ℝ × (E × Par 𝕂 E W) ↦ evalPtLin r.1 r.2 := by
  unfold evalPtLin; fun_prop

/-- The time increment `t - t₀` of the parameters. -/
def incr (x : E × Par 𝕂 E W) : 𝕂 := x.2.1 - x.2.2.1

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [NormedSpace 𝕂 E] [IsScalarTower ℝ 𝕂 E] in
theorem incr_add_smul (x v : E × Par 𝕂 E W) (r : ℝ) : incr (x + r • v) = incr x + r * incr v := by
  simp only [incr, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    RCLike.real_smul_eq_coe_mul]
  ring

variable (f : 𝕂 × E × W → E)

/-- The integrand `H(s, (y, (t, t₀, y₀, p))) = (t - t₀) f(t₀ + s (t - t₀), y + y₀, p)`. -/
def integrand (s : ℝ) (x : E × Par 𝕂 E W) : E := incr x • f (evalPt s x)

/-- Its directional derivative in the second variable. -/
def integrandDeriv (s : ℝ) (x v : E × Par 𝕂 E W) : E :=
  incr v • f (evalPt s x) + incr x • dMB f (evalPt s x, evalPtLin s v)

variable {f} {O : Set (𝕂 × E × W)}

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W]
  [LocallyConvexSpace ℝ W] [T2Space W] in
theorem hasDirDerivAt_integrand (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) (s : ℝ)
    {x : E × Par 𝕂 E W} (hx : evalPt s x ∈ O) (v : E × Par 𝕂 E W) :
    HasDirDerivAt (integrand f s) x v (integrandDeriv f s x v) := by
  have hq : Tendsto (fun r : ℝ ↦ r⁻¹ • (f (evalPt s x + r • evalPtLin s v) - f (evalPt s x)))
      (𝓝[≠] 0) (𝓝 (dMB f (evalPt s x, evalPtLin s v))) := hf.hasDirDerivAt hx (evalPtLin s v)
  have hcont : Tendsto (fun r : ℝ ↦ f (evalPt s x + r • evalPtLin s v)) (𝓝[≠] 0)
      (𝓝 (f (evalPt s x))) := by
    have h1 : Tendsto (fun r : ℝ ↦ evalPt s x + r • evalPtLin s v) (𝓝 0) (𝓝 (evalPt s x)) :=
      (by fun_prop : Continuous fun r : ℝ ↦ evalPt s x + r • evalPtLin s v).tendsto' 0 _
        (by simp)
    exact ((hf.continuousOn.continuousAt (hO.mem_nhds hx)).tendsto.comp h1).mono_left
      nhdsWithin_le_nhds
  have hlim := (hcont.const_smul (incr v)).add (hq.const_smul (incr x))
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun r (hr : r ≠ 0) ↦ ?_)
  simp only [integrand, incr_add_smul, evalPt_add_smul]
  set A := f (evalPt s x + r • evalPtLin s v)
  set B := f (evalPt s x)
  calc incr v • A + incr x • r⁻¹ • (A - B)
      = r⁻¹ • ((r : 𝕂) • incr v • A) + r⁻¹ • (incr x • (A - B)) := by
        rw [← RCLike.real_smul_eq_coe_smul (K := 𝕂), inv_smul_smul₀ hr, smul_comm (incr x)]
    _ = r⁻¹ • ((incr x + (r : 𝕂) * incr v) • A - incr x • B) := by
        rw [← smul_add, add_smul, mul_smul, smul_sub]
        congr 1
        abel

omit [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] in
theorem continuousOn_integrand (hfc : ContinuousOn f O) :
    ContinuousOn (fun r : ℝ × (E × Par 𝕂 E W) ↦ integrand f r.1 r.2) {r | evalPt r.1 r.2 ∈ O} := by
  have h1 : Continuous fun r : ℝ × (E × Par 𝕂 E W) ↦ incr r.2 := by unfold incr; fun_prop
  exact h1.continuousOn.smul (hfc.comp continuous_evalPt.continuousOn fun r hr ↦ hr)

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  [IsScalarTower ℝ 𝕂 E] in
theorem continuousOn_integrandDeriv (hd : ContinuousOn (dMB f) (O ×ˢ univ))
    (hfc : ContinuousOn f O) :
    ContinuousOn (fun r : ℝ × ((E × Par 𝕂 E W) × (E × Par 𝕂 E W)) ↦
      integrandDeriv f r.1 r.2.1 r.2.2) {r | evalPt r.1 r.2.1 ∈ O} := by
  have h1 : Continuous fun r : ℝ × ((E × Par 𝕂 E W) × (E × Par 𝕂 E W)) ↦ incr r.2.2 := by
    unfold incr; fun_prop
  have h2 : Continuous fun r : ℝ × ((E × Par 𝕂 E W) × (E × Par 𝕂 E W)) ↦ incr r.2.1 := by
    unfold incr; fun_prop
  have he : Continuous fun r : ℝ × ((E × Par 𝕂 E W) × (E × Par 𝕂 E W)) ↦ evalPt r.1 r.2.1 :=
    continuous_evalPt.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hl : Continuous fun r : ℝ × ((E × Par 𝕂 E W) × (E × Par 𝕂 E W)) ↦ evalPtLin r.1 r.2.2 :=
    continuous_evalPtLin.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  refine (h1.continuousOn.smul (hfc.comp he.continuousOn fun r hr ↦ hr)).add
    (h2.continuousOn.smul (hd.comp (he.prodMk hl).continuousOn fun r hr ↦ ⟨hr, mem_univ _⟩))

omit [CompleteSpace E] [Module ℝ W] [IsScalarTower ℝ 𝕂 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕂 E] in
theorem incr_smul (c : 𝕂) (v : E × Par 𝕂 E W) : incr (c • v) = c * incr v := by
  simp only [incr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

omit [CompleteSpace E] [IsScalarTower ℝ 𝕂 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  [IsScalarTower ℝ 𝕂 E] in
/-- The derivative of the integrand is complex linear if `f` is holomorphic. -/
theorem integrandDeriv_smul (hI : ∀ q ∈ O, ∀ (c : 𝕂) w, dMB f (q, c • w) = c • dMB f (q, w))
    {s : ℝ} {x : E × Par 𝕂 E W} (hx : evalPt s x ∈ O) (c : 𝕂) (v : E × Par 𝕂 E W) :
    integrandDeriv f s x (c • v) = c • integrandDeriv f s x v := by
  simp only [integrandDeriv, incr_smul, evalPtLin_smul, hI _ hx, smul_add, mul_smul,
    smul_comm (incr x) c]


/-! ### `C^k` dependence -/

variable (𝕂 E) in
/-- Scalar multiplication `𝕂 × E → E`, as a real bilinear map. -/
def smulBilin : 𝕂 →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ (fun a y ↦ a • y) add_smul (fun c a y ↦ smul_assoc c a y) smul_add
    (fun c a y ↦ smul_comm a c y)

omit [CompleteSpace E] in
theorem continuous_smulBilin : Continuous fun p : 𝕂 × E ↦ smulBilin 𝕂 E p.1 p.2 :=
  continuous_smul

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] in
/-- The integrand is `C^k` in all variables, the time `s` included, if `f` is `C^k`. -/
theorem contDiffMBOn_integrand (hO : IsOpen O) {k : ℕ} (hf : ContDiffMBOn k f O) :
    ContDiffMBOn k (fun r : ℝ × (E × Par 𝕂 E W) ↦ integrand f r.1 r.2)
      {r | evalPt r.1 r.2 ∈ O} := by
  -- helps instance synthesis on the products below
  have : ContinuousSMul ℝ (Par 𝕂 E W) := inferInstance
  set A : Set (ℝ × (E × Par 𝕂 E W)) := {r | evalPt r.1 r.2 ∈ O}
  have hA : IsOpen A := hO.preimage continuous_evalPt
  -- the coordinates, as continuous linear maps
  set X := ContinuousLinearMap.snd ℝ ℝ (E × Par 𝕂 E W)
  set Zp := ContinuousLinearMap.snd ℝ E (Par 𝕂 E W) ∘L X
  set Lt := ContinuousLinearMap.fst ℝ 𝕂 (𝕂 × E × W) ∘L Zp
  set Lt₀ := ContinuousLinearMap.fst ℝ 𝕂 (E × W) ∘L ContinuousLinearMap.snd ℝ 𝕂 (𝕂 × E × W) ∘L Zp
  set Ly₀ := ContinuousLinearMap.fst ℝ E W ∘L ContinuousLinearMap.snd ℝ 𝕂 (E × W) ∘L
    ContinuousLinearMap.snd ℝ 𝕂 (𝕂 × E × W) ∘L Zp
  set Lp := ContinuousLinearMap.snd ℝ E W ∘L ContinuousLinearMap.snd ℝ 𝕂 (E × W) ∘L
    ContinuousLinearMap.snd ℝ 𝕂 (𝕂 × E × W) ∘L Zp
  set Ly := ContinuousLinearMap.fst ℝ E (Par 𝕂 E W) ∘L X
  set Ls := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂) ∘L ContinuousLinearMap.fst ℝ ℝ (E × Par 𝕂 E W)
  have hincr : ContDiffMBOn k (fun r : ℝ × (E × Par 𝕂 E W) ↦ incr r.2) A :=
    (Lt - Lt₀).contDiffMBOn k A
  have hmul : ContDiffMBOn k (fun r : ℝ × (E × Par 𝕂 E W) ↦
      smulBilin 𝕂 𝕂 (Ls r) (incr r.2)) A :=
    ContDiffMBOn.bilin (smulBilin 𝕂 𝕂) continuous_smulBilin hA (Ls.contDiffMBOn k A) hincr
  have h1 : ContDiffMBOn k (fun r : ℝ × (E × Par 𝕂 E W) ↦
      Lt₀ r + smulBilin 𝕂 𝕂 (Ls r) (incr r.2)) A :=
    (Lt₀.contDiffMBOn k A).add hA hmul
  have hev : ContDiffMBOn k (fun r : ℝ × (E × Par 𝕂 E W) ↦ evalPt r.1 r.2) A :=
    h1.prodMk hA (((Ly + Ly₀).contDiffMBOn k A).prodMk hA (Lp.contDiffMBOn k A))
  have hfe : ContDiffMBOn k (fun r : ℝ × (E × Par 𝕂 E W) ↦ f (evalPt r.1 r.2)) A :=
    ContDiffMBOn.comp (g := f) (f := fun r : ℝ × (E × Par 𝕂 E W) ↦ evalPt r.1 r.2) hA hO hf hev
      fun r hr ↦ hr
  exact ContDiffMBOn.bilin (smulBilin 𝕂 E) continuous_smulBilin hA hincr hfe

/-! ### Local bounds -/

omit [NormedSpace 𝕂 E] [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
/-- A box `B(a, r₁) × B(b, r₂) × P` inside a neighbourhood of `(a, b, c)`. -/
theorem exists_box {N : Set (𝕂 × E × W)} {q₀ : 𝕂 × E × W} (hN : N ∈ 𝓝 q₀) :
    ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q₀.2.2 ∈ P ∧
      ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) ⊆ N := by
  obtain ⟨a, b, c⟩ := q₀
  rw [nhds_prod_eq, nhds_prod_eq] at hN
  obtain ⟨t₁, ht₁, t₂, ht₂, h12⟩ := Filter.mem_prod_iff.mp hN
  obtain ⟨t₃, ht₃, t₄, ht₄, h34⟩ := Filter.mem_prod_iff.mp ht₂
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.mem_nhds_iff.mp ht₁
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.mem_nhds_iff.mp ht₃
  refine ⟨r₁, hr₁, r₂, hr₂, interior t₄, isOpen_interior, mem_interior_iff_mem_nhds.2 ht₄, ?_⟩
  rintro ⟨t, y, p⟩ ⟨ht, hy, hp⟩
  exact h12 ⟨hb₁ ht, h34 ⟨hb₂ hy, interior_subset hp⟩⟩

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace 𝕂 E]
  [IsScalarTower ℝ 𝕂 E] in
/-- **Local bounds** ([GN26, (2.103)]): near `q₀`, `f` is bounded and Lipschitz in the
second variable, uniformly in the others. The Lipschitz constant comes from the continuity of
`df` at `(q₀, 0)`. -/
theorem exists_bounds (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) {q₀ : 𝕂 × E × W} (hq₀ : q₀ ∈ O) :
    ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q₀.2.2 ∈ P ∧ ∃ M > 0, ∃ L > 0,
      ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) ⊆ O ∧
      (∀ q ∈ ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P), ‖f q‖ ≤ M) ∧
      ∀ t ∈ ball q₀.1 r₁, ∀ p ∈ P, ∀ y ∈ ball q₀.2.1 r₂, ∀ y' ∈ ball q₀.2.1 r₂,
        ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖ := by
  set M := ‖f q₀‖ + 1
  have hM : ∀ᶠ q in 𝓝 q₀, ‖f q‖ ≤ M :=
    ((continuous_norm.tendsto _).comp ((hf.continuousOn.continuousAt
      (hO.mem_nhds hq₀)).tendsto)).eventually (eventually_le_nhds (by simp [M]))
  -- the derivative is small near `(q₀, 0)`
  have hd : ContinuousOn (dMB f) (O ×ˢ univ) := hf.2.2
  have hd0 : dMB f (q₀, 0) = 0 := by
    simpa using hf.dMB_smul hq₀ 0 (0 : 𝕂 × E × W)
  have hev : ∀ᶠ r in 𝓝 (q₀, (0 : 𝕂 × E × W)), ‖dMB f r‖ < 1 := by
    have := (continuous_norm.tendsto _).comp ((hd.continuousAt (x := (q₀, (0 : 𝕂 × E × W)))
      (prod_mem_nhds (hO.mem_nhds hq₀) univ_mem)).tendsto)
    rw [hd0, norm_zero] at this
    exact this.eventually (gt_mem_nhds zero_lt_one)
  rw [nhds_prod_eq] at hev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.mp hev
  obtain ⟨δ, hδ, hδb⟩ : ∃ δ > 0, ∀ v : E, ‖v‖ < δ → pb ((0 : 𝕂), v, (0 : W)) := by
    have hc : Continuous fun v : E ↦ ((0 : 𝕂), v, (0 : W)) := by fun_prop
    have := (hc.tendsto 0).eventually hpb
    obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp this
    exact ⟨δ, hδ, fun v hv ↦ h (by simpa using hv)⟩
  set L := 2 / δ
  have hL : ∀ q, pa q → q ∈ O → ∀ d : E, ‖dMB f (q, ((0 : 𝕂), d, (0 : W)))‖ ≤ L * ‖d‖ := by
    intro q hq hqO d
    rcases eq_or_ne d 0 with rfl | hd'
    · have h0 : dMB f (q, ((0 : 𝕂), (0 : E), (0 : W))) = 0 := by
        have := hf.dMB_smul hqO 0 ((0 : 𝕂), (0 : E), (0 : W))
        rw [zero_smul, zero_smul] at this
        exact this
      rw [h0]; simp
    have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd'
    set c : ℝ := δ / (2 * ‖d‖)
    have hc : 0 < c := by positivity
    have hcd : ‖c • d‖ < δ := by
      have : c * ‖d‖ = δ / 2 := by simp only [c]; field_simp
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, this]
      linarith
    have h1 := hab hq (hδb _ hcd)
    have h2 : ((0 : 𝕂), c • d, (0 : W)) = c • ((0 : 𝕂), d, (0 : W)) := by simp
    rw [h2, hf.dMB_smul hqO, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at h1
    have : ‖dMB f (q, ((0 : 𝕂), d, (0 : W)))‖ < 1 / c := by
      rw [lt_div_iff₀ hc]; linarith
    calc _ ≤ 1 / c := this.le
      _ = L * ‖d‖ := by simp only [c, L]; field_simp
  -- the box
  obtain ⟨r₁, hr₁, r₂, hr₂, P, hP, hpP, hbox⟩ :=
    exists_box (Filter.inter_mem (Filter.inter_mem (hO.mem_nhds hq₀) hM) hpa)
  refine ⟨r₁, hr₁, r₂, hr₂, P, hP, hpP, M, by positivity, L, by positivity,
    fun q hq ↦ (hbox hq).1.1, fun q hq ↦ (hbox hq).1.2, ?_⟩
  intro t ht p hp y hy y' hy'
  -- the mean value inequality along the segment from `y'` to `y`
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1,
      (t, y' + u • (y - y'), p) ∈ ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) :=
    fun u hu ↦ ⟨ht, (convex_ball _ _).add_smul_sub_mem hy' hy hu, hp⟩
  have hder : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun u ↦ f (t, y' + u • (y - y'), p))
      (dMB f ((t, y' + u • (y - y'), p), ((0 : 𝕂), y - y', (0 : W)))) (Icc 0 1) u := by
    intro u hu
    have hq := (hbox (hseg u hu)).1.1
    refine HasDerivAt.hasDerivWithinAt ?_
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine (hf.hasDirDerivAt hq _).congr fun r ↦ ?_
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, add_smul, add_assoc]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hder (C := L * ‖y - y'‖)
    (fun u hu ↦ hL _ (hbox (hseg u (Ico_subset_Icc_self hu))).2 (hbox (hseg u
      (Ico_subset_Icc_self hu))).1.1 _) 1 (right_mem_Icc.2 zero_le_one)
  simpa using hmv

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace 𝕂 E]
  [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] [AddCommGroup W] [Module ℝ W] in
/-- **Local bounds without differentiability** ([GN26, (2.103)], case `k = 0`): if `f` is
continuous and Lipschitz in the second variable, uniformly near `q₀`, then near `q₀` it is bounded
and Lipschitz on a box inside `O`. -/
theorem exists_bounds_of_lipschitz (hO : IsOpen O) (hfc : ContinuousOn f O) {q₀ : 𝕂 × E × W}
    (hq₀ : q₀ ∈ O)
    (hlip : ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q₀.2.2 ∈ P ∧ ∃ L > 0,
      ∀ t ∈ ball q₀.1 r₁, ∀ p ∈ P, ∀ y ∈ ball q₀.2.1 r₂, ∀ y' ∈ ball q₀.2.1 r₂,
        ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖) :
    ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q₀.2.2 ∈ P ∧ ∃ M > 0, ∃ L > 0,
      ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) ⊆ O ∧
      (∀ q ∈ ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P), ‖f q‖ ≤ M) ∧
      ∀ t ∈ ball q₀.1 r₁, ∀ p ∈ P, ∀ y ∈ ball q₀.2.1 r₂, ∀ y' ∈ ball q₀.2.1 r₂,
        ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖ := by
  obtain ⟨r₁, hr₁, r₂, hr₂, P, hP, hpP, L, hL, hlip⟩ := hlip
  set M := ‖f q₀‖ + 1
  have hM : ∀ᶠ q in 𝓝 q₀, ‖f q‖ ≤ M :=
    ((continuous_norm.tendsto _).comp ((hfc.continuousAt
      (hO.mem_nhds hq₀)).tendsto)).eventually (eventually_le_nhds (by simp [M]))
  have hbig : ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) ∈ 𝓝 q₀ :=
    (isOpen_ball.prod (isOpen_ball.prod hP)).mem_nhds
      ⟨mem_ball_self hr₁, mem_ball_self hr₂, hpP⟩
  obtain ⟨a, ha, b, hb, P', hP', hpP', hbox⟩ :=
    exists_box (Filter.inter_mem (Filter.inter_mem (hO.mem_nhds hq₀) hM) hbig)
  refine ⟨a, ha, b, hb, P', hP', hpP', M, by positivity, L, hL, fun q hq ↦ (hbox hq).1.1,
    fun q hq ↦ (hbox hq).1.2, fun t ht p hp y hy y' hy' ↦ ?_⟩
  have h1 := (hbox (show ((t, y, p) : 𝕂 × E × W) ∈ _ from ⟨ht, hy, hp⟩)).2
  have h2 := (hbox (show ((t, y', p) : 𝕂 × E × W) ∈ _ from ⟨ht, hy', hp⟩)).2
  exact hlip t h1.1 p h1.2.2 y h1.2.1 y' h2.2.1

/-! ### The data of the fixed point problem -/

/-- Radii and bounds for the fixed point problem ([GN26, (2.103) and (2.104)]): on the box
`B(t̄, 3ρ) × B(ȳ, 2R) × P ⊆ O`, `‖f‖ ≤ M` and `f` is `L`-Lipschitz in `y`, with
`2ρM ≤ R/2` and `2ρL ≤ 1/2`. -/
structure FlowData (f : 𝕂 × E × W → E) (O : Set (𝕂 × E × W)) (q₀ : 𝕂 × E × W) where
  /-- The radius of the time ball `B(t̄, 3ρ)`. -/
  ρ : ℝ
  /-- The radius of the space ball `B(ȳ, 2R)`. -/
  R : ℝ
  /-- The bound `‖f‖ ≤ M` on the box. -/
  M : ℝ
  /-- The Lipschitz constant of `f` in `y` on the box. -/
  L : ℝ
  /-- The open set of parameters. -/
  P : Set W
  ρ_pos : 0 < ρ
  R_pos : 0 < R
  M_nonneg : 0 ≤ M
  L_nonneg : 0 ≤ L
  isOpen_P : IsOpen P
  mem_P : q₀.2.2 ∈ P
  box_subset : ball q₀.1 (3 * ρ) ×ˢ (ball q₀.2.1 (2 * R) ×ˢ P) ⊆ O
  bound : ∀ q ∈ ball q₀.1 (3 * ρ) ×ˢ (ball q₀.2.1 (2 * R) ×ˢ P), ‖f q‖ ≤ M
  lipschitz : ∀ t ∈ ball q₀.1 (3 * ρ), ∀ p ∈ P, ∀ y ∈ ball q₀.2.1 (2 * R),
    ∀ y' ∈ ball q₀.2.1 (2 * R), ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖
  small_M : 2 * ρ * M ≤ R / 2
  small_L : 2 * ρ * L ≤ 1 / 2

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace 𝕂 E]
  [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] [AddCommGroup W] [Module ℝ W] in
/-- Radii for the fixed point problem, from local bounds. -/
theorem exists_flowData_of_bounds {q₀ : 𝕂 × E × W}
    (h : ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q₀.2.2 ∈ P ∧ ∃ M > 0, ∃ L > 0,
      ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) ⊆ O ∧
      (∀ q ∈ ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P), ‖f q‖ ≤ M) ∧
      ∀ t ∈ ball q₀.1 r₁, ∀ p ∈ P, ∀ y ∈ ball q₀.2.1 r₂, ∀ y' ∈ ball q₀.2.1 r₂,
        ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖) : Nonempty (FlowData f O q₀) := by
  obtain ⟨r₁, hr₁, r₂, hr₂, P, hP, hpP, M, hM, L, hL, hbox, hbd, hlip⟩ := h
  set R := r₂ / 2
  set ρ := min (r₁ / 3) (min (R / (4 * M)) (1 / (4 * L)))
  have hρ : 0 < ρ := by positivity
  have hρ1 : 3 * ρ ≤ r₁ := by
    have := min_le_left (r₁ / 3) (min (R / (4 * M)) (1 / (4 * L))); linarith
  have hρ2 : ρ ≤ R / (4 * M) := (min_le_right _ _).trans (min_le_left _ _)
  have hρ3 : ρ ≤ 1 / (4 * L) := (min_le_right _ _).trans (min_le_right _ _)
  have h2R : 2 * R = r₂ := by simp only [R]; ring
  have hsub : ball q₀.1 (3 * ρ) ×ˢ (ball q₀.2.1 (2 * R) ×ˢ P) ⊆
      ball q₀.1 r₁ ×ˢ (ball q₀.2.1 r₂ ×ˢ P) := by
    rw [h2R]; exact prod_mono (ball_subset_ball hρ1) subset_rfl
  refine ⟨⟨ρ, R, M, L, P, hρ, by positivity, hM.le, hL.le, hP, hpP, hsub.trans hbox,
    fun q hq ↦ hbd q (hsub hq), fun t ht p hp y hy y' hy' ↦ ?_, ?_, ?_⟩⟩
  · rw [h2R] at hy hy'
    exact hlip t (ball_subset_ball hρ1 ht) p hp y hy y' hy'
  · have := mul_le_mul_of_nonneg_right hρ2 hM.le
    rw [div_mul_eq_mul_div, mul_comm 4 M, ← div_div, mul_div_assoc, div_self hM.ne',
      mul_one] at this
    nlinarith
  · have := mul_le_mul_of_nonneg_right hρ3 hL.le
    rw [div_mul_eq_mul_div, one_mul, mul_comm 4 L, ← div_div, div_self hL.ne'] at this
    nlinarith

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace 𝕂 E]
  [IsScalarTower ℝ 𝕂 E] in
theorem exists_flowData (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) {q₀ : 𝕂 × E × W}
    (hq₀ : q₀ ∈ O) : Nonempty (FlowData f O q₀) :=
  exists_flowData_of_bounds (exists_bounds hO hf hq₀)

/-! ### The fixed point problem -/

/-- The interval `[-1, 1]` on which the curves are parametrized. -/
local notation "𝕀" => (Icc (-1 : ℝ) 1)

omit [CompleteSpace E] in
/-- The primitive operator has norm at most `1`. -/
theorem norm_primitive_le (γ : C(𝕀, E)) : ‖primitiveCLM 𝕂 γ‖ ≤ ‖γ‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s ↦ ?_
  rw [primitiveCLM_apply]
  have hs : |(s : ℝ) - 0| ≤ 1 := by simpa using abs_le.2 s.2
  calc ‖∫ τ in (0 : ℝ)..s, extendI γ τ‖ ≤ ‖γ‖ * |(s : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ ↦ norm_extendI_le γ τ
    _ ≤ ‖γ‖ * 1 := by gcongr
    _ = ‖γ‖ := mul_one _

variable {q₀ : 𝕂 × E × W} (D : FlowData f O q₀)

/-- The parameters `(t, t₀, y₀, p) ∈ B(t̄, ρ) × B(t̄, ρ) × B(ȳ, R) × P`. -/
def parSet : Set (Par 𝕂 E W) := ball q₀.1 D.ρ ×ˢ (ball q₀.1 D.ρ ×ˢ (ball q₀.2.1 D.R ×ˢ D.P))

/-- The domain `B(0, R) × parSet` of the integrand. -/
def dom : Set (E × Par 𝕂 E W) := ball 0 D.R ×ˢ parSet D

include D in
omit [CompleteSpace E] [NormedSpace 𝕂 E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem isOpen_parSet : IsOpen (parSet D) :=
  isOpen_ball.prod (isOpen_ball.prod (isOpen_ball.prod D.isOpen_P))

omit [CompleteSpace E] [NormedSpace 𝕂 E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem isOpen_dom : IsOpen (dom D) := isOpen_ball.prod (isOpen_parSet D)

omit [NormedSpace 𝕂 E] [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem norm_incr_lt {x : E × Par 𝕂 E W} (hx : x ∈ dom D) : ‖incr x‖ < 2 * D.ρ := by
  obtain ⟨-, ht, ht₀, -⟩ := hx
  have h1 := mem_ball_iff_norm.1 ht
  have h2 := mem_ball_iff_norm'.1 ht₀
  calc ‖incr x‖ = ‖(x.2.1 - q₀.1) + (q₀.1 - x.2.2.1)‖ := by simp [incr]
    _ ≤ ‖x.2.1 - q₀.1‖ + ‖q₀.1 - x.2.2.1‖ := norm_add_le _ _
    _ < D.ρ + D.ρ := add_lt_add h1 h2
    _ = 2 * D.ρ := by ring

omit [NormedSpace 𝕂 E] [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem evalPt_mem_box {s : ℝ} (hs : s ∈ 𝕀) {x : E × Par 𝕂 E W} (hx : x ∈ dom D) :
    evalPt s x ∈ ball q₀.1 (3 * D.ρ) ×ˢ (ball q₀.2.1 (2 * D.R) ×ˢ D.P) := by
  have hincr := norm_incr_lt D hx
  obtain ⟨hy, -, ht₀, hy₀, hp⟩ := hx
  have hs1 : ‖(s : 𝕂)‖ ≤ 1 := by simpa [RCLike.norm_ofReal] using abs_le.2 hs
  refine ⟨?_, ?_, hp⟩
  · rw [mem_ball_iff_norm]
    calc ‖x.2.2.1 + (s : 𝕂) * (x.2.1 - x.2.2.1) - q₀.1‖
        ≤ ‖x.2.2.1 - q₀.1‖ + ‖(s : 𝕂)‖ * ‖incr x‖ := by
          rw [show x.2.2.1 + (s : 𝕂) * (x.2.1 - x.2.2.1) - q₀.1 =
            (x.2.2.1 - q₀.1) + (s : 𝕂) * incr x by simp [incr]; ring, ← norm_mul]
          exact norm_add_le _ _
      _ < D.ρ + 1 * (2 * D.ρ) :=
          add_lt_add_of_lt_of_le (mem_ball_iff_norm.1 ht₀)
            (mul_le_mul hs1 hincr.le (norm_nonneg _) zero_le_one)
      _ = 3 * D.ρ := by ring
  · rw [mem_ball_iff_norm]
    calc ‖x.1 + x.2.2.2.1 - q₀.2.1‖ ≤ ‖x.1‖ + ‖x.2.2.2.1 - q₀.2.1‖ := by
          rw [add_sub_assoc]; exact norm_add_le _ _
      _ < D.R + D.R := add_lt_add (mem_ball_zero_iff.1 hy) (mem_ball_iff_norm.1 hy₀)
      _ = 2 * D.R := by ring

variable (f) in
/-- The integrand on `[-1, 1]`. -/
def intH (r : 𝕀 × (E × Par 𝕂 E W)) : E := integrand f r.1 r.2

variable (f) in
/-- Its derivative. -/
def intDH (r : 𝕀 × ((E × Par 𝕂 E W) × (E × Par 𝕂 E W))) : E := integrandDeriv f r.1 r.2.1 r.2.2

variable (f) in
/-- The map `g(z, ψ) = ∫₀ H(·, ψ(·), z)` of the fixed point problem ([GN26, (2.106)]). -/
def gMap (q : Par 𝕂 E W × C(𝕀, E)) : C(𝕀, E) :=
  primitiveCLM 𝕂 (superposeParam (intH f) (q.2, q.1))

omit [NormedSpace 𝕂 E] [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W]
  [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] [NormedSpace ℝ E] in
theorem mem_paramDomain {z : Par 𝕂 E W} (hz : z ∈ parSet D) {ψ : C(𝕀, E)}
    (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R) : (ψ, z) ∈ paramDomain 𝕀 (dom D) := fun s ↦
  ⟨mem_ball_zero_iff.2 ((ψ.norm_coe_le_norm s).trans_lt (mem_ball_zero_iff.1 hψ)), hz⟩

omit [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] in
theorem continuousOn_intH (hfc : ContinuousOn f O) :
    ContinuousOn (intH f) (univ ×ˢ dom D) :=
  (continuousOn_integrand hfc).comp (continuous_subtype_val.prodMap continuous_id).continuousOn
    fun r hr ↦ D.box_subset (evalPt_mem_box D r.1.2 hr.2)

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  [IsScalarTower ℝ 𝕂 E] in
theorem continuousOn_intDH (hf : ContDiffMBOn 1 f O) :
    ContinuousOn (intDH f) (univ ×ˢ (dom D ×ˢ univ)) :=
  (continuousOn_integrandDeriv hf.2.2 hf.continuousOn).comp
    (continuous_subtype_val.prodMap continuous_id).continuousOn
    fun r hr ↦ D.box_subset (evalPt_mem_box D r.1.2 hr.2.1)

omit [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] in
theorem superposeParam_intH_apply (hfc : ContinuousOn f O) {z : Par 𝕂 E W} (hz : z ∈ parSet D)
    {ψ : C(𝕀, E)} (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R) (s : 𝕀) :
    superposeParam (intH f) (ψ, z) s = integrand f s (ψ s, z) :=
  superposeParam_apply (continuousOn_intH D hfc) (mem_paramDomain D hz hψ) s

omit [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] in
theorem norm_superposeParam_le (hfc : ContinuousOn f O) {z : Par 𝕂 E W} (hz : z ∈ parSet D)
    {ψ : C(𝕀, E)} (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R) :
    ‖superposeParam (intH f) (ψ, z)‖ ≤ 2 * D.ρ * D.M := by
  refine (ContinuousMap.norm_le _ (by have := D.ρ_pos; have := D.M_nonneg; positivity)).2
    fun s ↦ ?_
  rw [superposeParam_intH_apply D hfc hz hψ, integrand, norm_smul]
  have hx := mem_paramDomain D hz hψ s
  exact mul_le_mul (norm_incr_lt D hx).le (D.bound _ (evalPt_mem_box D s.2 hx)) (norm_nonneg _)
    (by have := D.ρ_pos; positivity)

omit [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] in
theorem norm_superposeParam_sub_le (hfc : ContinuousOn f O) {z : Par 𝕂 E W} (hz : z ∈ parSet D)
    {ψ ψ' : C(𝕀, E)} (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R) (hψ' : ψ' ∈ ball (0 : C(𝕀, E)) D.R) :
    ‖superposeParam (intH f) (ψ, z) - superposeParam (intH f) (ψ', z)‖ ≤
      2 * D.ρ * D.L * ‖ψ - ψ'‖ := by
  refine (ContinuousMap.norm_le _ (by have := D.ρ_pos; have := D.L_nonneg; positivity)).2
    fun s ↦ ?_
  rw [ContinuousMap.sub_apply, superposeParam_intH_apply D hfc hz hψ,
    superposeParam_intH_apply D hfc hz hψ', integrand, integrand,
    show incr ((ψ' s, z) : E × Par 𝕂 E W) = incr ((ψ s, z) : E × Par 𝕂 E W) from rfl, ← smul_sub,
    norm_smul]
  have hx := mem_paramDomain D hz hψ s
  have hx' := mem_paramDomain D hz hψ' s
  have hb := evalPt_mem_box D s.2 hx
  have hb' := evalPt_mem_box D s.2 hx'
  have hincr : incr ((ψ s, z) : E × Par 𝕂 E W) = incr ((ψ' s, z) : E × Par 𝕂 E W) := rfl
  have hlip := D.lipschitz _ hb.1 _ hb.2.2 _ hb.2.1 _ hb'.2.1
  simp only [evalPt] at hlip
  rw [show ψ s + z.2.2.1 - (ψ' s + z.2.2.1) = ψ s - ψ' s by abel] at hlip
  calc ‖incr ((ψ s, z) : E × Par 𝕂 E W)‖ * ‖f (evalPt s (ψ s, z)) - f (evalPt s (ψ' s, z))‖
      ≤ (2 * D.ρ) * (D.L * ‖ψ s - ψ' s‖) :=
        mul_le_mul (norm_incr_lt D hx).le hlip (norm_nonneg _) (by have := D.ρ_pos; positivity)
    _ ≤ (2 * D.ρ) * (D.L * ‖ψ - ψ'‖) := by
        have := D.ρ_pos; have := D.L_nonneg
        gcongr
        exact (ψ - ψ').norm_coe_le_norm s
    _ = 2 * D.ρ * D.L * ‖ψ - ψ'‖ := by ring

omit [CompleteSpace E] [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  [T2Space W] in
/-- **The uniform family of contractions** of Glöckner–Neeb's proof, with constant `1/2`, on the
ball of radius `R` of `C([-1, 1], E)`, mapping the closed ball of radius `R/2` into itself. -/
theorem uniformContraction (hfc : ContinuousOn f O) :
    UniformContraction (gMap f) (parSet D) (ball 0 D.R) (closedBall 0 (D.R / 2)) (1 / 2) where
  isOpen_param := isOpen_parSet D
  isOpen := isOpen_ball
  isClosed := isClosed_closedBall
  nonempty := ⟨0, mem_closedBall_self (by linarith [D.R_pos])⟩
  subset := closedBall_subset_ball (by linarith [D.R_pos])
  lt_one := by norm_num
  mapsTo z hz ψ hψ := mem_closedBall_zero_iff.2 ((norm_primitive_le _).trans
    ((norm_superposeParam_le D hfc hz (closedBall_subset_ball (by linarith [D.R_pos]) hψ)).trans
      D.small_M))
  lipschitz z hz ψ hψ ψ' hψ' := by
    simp only [gMap]
    rw [← map_sub]
    calc _ ≤ ‖superposeParam (intH f) (ψ, z) - superposeParam (intH f) (ψ', z)‖ :=
          norm_primitive_le _
      _ ≤ 2 * D.ρ * D.L * ‖ψ - ψ'‖ := norm_superposeParam_sub_le D hfc hz hψ hψ'
      _ ≤ ((1 / 2 : ℝ≥0) : ℝ) * ‖ψ - ψ'‖ := by
          gcongr
          simpa using D.small_L

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W]
  [LocallyConvexSpace ℝ W] [T2Space W] in
theorem hasDirDerivAt_gMap (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) {z : Par 𝕂 E W}
    (hz : z ∈ parSet D) {ψ : C(𝕀, E)} (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R)
    (w : Par 𝕂 E W × C(𝕀, E)) :
    HasDirDerivAt (gMap f) (z, ψ) w
      (primitiveCLM 𝕂 (superposeParamDeriv (intDH f) ((ψ, z), (w.2, w.1)))) := by
  have hd : ∀ s : 𝕀, ∀ x ∈ dom D, ∀ v, HasDirDerivAt (fun x ↦ intH f (s, x)) x v
      (intDH f (s, (x, v))) := fun s x hx v ↦
    hasDirDerivAt_integrand hO hf s (D.box_subset (evalPt_mem_box D s.2 hx)) v
  have h := (hasDirDerivAt_superposeParam (isOpen_dom D) (continuousOn_intH D hf.continuousOn)
    hd (continuousOn_intDH D hf) (mem_paramDomain D hz hψ) (w.2, w.1)).clm_comp_real
    ((primitiveCLM 𝕂).restrictScalars ℝ)
  refine h.congr fun t ↦ ?_
  rfl

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] in
theorem contDiffMBOn_gMap (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) :
    ContDiffMBOn 1 (gMap f) (parSet D ×ˢ ball (0 : C(𝕀, E)) D.R) := by
  have hd : ∀ s : 𝕀, ∀ x ∈ dom D, ∀ v, HasDirDerivAt (fun x ↦ intH f (s, x)) x v
      (intDH f (s, (x, v))) := fun s x hx v ↦
    hasDirDerivAt_integrand hO hf s (D.box_subset (evalPt_mem_box D s.2 hx)) v
  have hS := contDiffMBOn_superposeParam (isOpen_dom D) (continuousOn_intH D hf.continuousOn) hd
    (continuousOn_intDH D hf)
  have hswap : ContDiffMBOn 1 (fun q : Par 𝕂 E W × C(𝕀, E) ↦ (q.2, q.1)) univ :=
    (ContinuousLinearEquiv.prodComm ℝ (Par 𝕂 E W) C(𝕀, E)).toContinuousLinearMap.contDiffMBOn 1 univ
  have hc := ContDiffMBOn.comp ((isOpen_parSet D).prod isOpen_ball)
    (isOpen_paramDomain (isOpen_dom D)) hS (hswap.mono (subset_univ _))
    fun q hq ↦ mem_paramDomain D hq.1 hq.2
  exact hc.clm_comp' ((primitiveCLM 𝕂).restrictScalars ℝ)
    ((isOpen_parSet D).prod isOpen_ball)

omit [CompleteSpace E] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] [LocallyConvexSpace ℝ W]
  [T2Space W] in
/-- `dg` is complex linear when `f` is holomorphic. -/
theorem dMB_gMap_smul (hO : IsOpen O) (hf : ContDiffMBOn 1 f O)
    (hI : ∀ q ∈ O, ∀ (c : 𝕂) w, dMB f (q, c • w) = c • dMB f (q, w)) {z : Par 𝕂 E W}
    (hz : z ∈ parSet D) {ψ : C(𝕀, E)} (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R) (c : 𝕂)
    (w : Par 𝕂 E W × C(𝕀, E)) :
    dMB (gMap f) ((z, ψ), c • w) = c • dMB (gMap f) ((z, ψ), w) := by
  rw [(hasDirDerivAt_gMap D hO hf hz hψ (c • w)).dMB_eq,
    (hasDirDerivAt_gMap D hO hf hz hψ w).dMB_eq, ← map_smul]
  congr 1
  ext s
  have hD := continuousOn_intDH D hf
  have hm := mem_paramDomain D hz hψ
  rw [ContinuousMap.smul_apply, superposeParamDeriv_apply hD hm, superposeParamDeriv_apply hD hm]
  simp only [intDH, Prod.smul_fst, Prod.smul_snd, ContinuousMap.smul_apply]
  rw [← integrandDeriv_smul hI (D.box_subset (evalPt_mem_box D s.2 (hm s)))]
  rfl

variable (hfc : ContinuousOn f O)

/-- The fixed point `η(z) ∈ C([-1, 1], E)` (Glöckner–Neeb, `η_{t,t₀,y₀,p}`). -/
def eta (z : Par 𝕂 E W) : C(𝕀, E) := (uniformContraction D hfc).fixedPoint z

/-- The point `1 ∈ [-1, 1]`. -/
def oneI : 𝕀 := ⟨1, by norm_num, le_rfl⟩

/-- **The solution map** `Φ(t, t₀, y₀, p) = η_{t,t₀,y₀,p}(1) + y₀` ([GN26, p. 205]). -/
def flowPhi (z : Par 𝕂 E W) : E := eta D hfc z oneI + z.2.2.1

omit [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] in
theorem derivFixedPoint_smul (hO : IsOpen O) (hf : ContDiffMBOn 1 f O)
    (hI : ∀ q ∈ O, ∀ (c : 𝕂) w, dMB f (q, c • w) = c • dMB f (q, w)) {z : Par 𝕂 E W}
    (hz : z ∈ parSet D) (c : 𝕂) (w : Par 𝕂 E W) :
    (uniformContraction D hfc).derivFixedPoint z (c • w) =
      c • (uniformContraction D hfc).derivFixedPoint z w := by
  set hU := uniformContraction D hfc
  have hg := contDiffMBOn_gMap D hO hf
  have hψ : hU.fixedPoint z ∈ ball (0 : C(𝕀, E)) D.R :=
    hU.subset (hU.fixedPoint_mem hz)
  have hA : ∀ v, hU.opA z (c • v) = c • hU.opA z v := fun v ↦ by
    simp only [UniformContraction.opA]
    rw [show ((0 : Par 𝕂 E W), c • v) = c • ((0 : Par 𝕂 E W), v) by simp]
    exact dMB_gMap_smul D hO hf hI hz hψ c _
  have hb : hU.vecB z (c • w) = c • hU.vecB z w := by
    simp only [UniformContraction.vecB]
    rw [show (c • w, (0 : C(𝕀, E))) = c • (w, (0 : C(𝕀, E))) by simp]
    exact dMB_gMap_smul D hO hf hI hz hψ c _
  have hiter : ∀ n v, (hU.opA z)^[n] (c • v) = c • (hU.opA z)^[n] v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro v; rw [iterate_succ_apply', iterate_succ_apply', ih, hA]
  have hsum : Summable fun n ↦ (hU.opA z)^[n] (hU.vecB z w) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity)
      (by norm_num : ((1 / 2 : ℝ≥0) : ℝ) < 1)).mul_right ‖hU.vecB z w‖)
      fun n ↦ hU.norm_iterate_opA_le hg hz _ n
  simp only [UniformContraction.derivFixedPoint, hb, hiter]
  exact hsum.tsum_const_smul c

omit [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] in
theorem hasDirDerivAt_flowPhi (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) {z : Par 𝕂 E W}
    (hz : z ∈ parSet D) (w : Par 𝕂 E W) :
    HasDirDerivAt (flowPhi D hfc) z w
      ((uniformContraction D hfc).derivFixedPoint z w oneI + w.2.2.1) := by
  have h1 := ((uniformContraction D hfc).hasDirDerivAt_fixedPoint (contDiffMBOn_gMap D hO hf) hz
    w).clm_comp_real ((evalI 𝕂 oneI).restrictScalars ℝ)
  have h2 : HasDirDerivAt (fun z : Par 𝕂 E W ↦ z.2.2.1) z w w.2.2.1 :=
    (ContinuousLinearMap.fst ℝ E W ∘L ContinuousLinearMap.snd ℝ 𝕂 (E × W) ∘L
      ContinuousLinearMap.snd ℝ 𝕂 (𝕂 × E × W)).hasDirDerivAt z w
  exact h1.add h2

omit [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] in
theorem contDiffMBOn_flowPhi (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) :
    ContDiffMBOn 1 (flowPhi D hfc) (parSet D) := by
  have hη := (uniformContraction D hfc).contDiffMBOn_fixedPoint (contDiffMBOn_gMap D hO hf)
  have h1 := ContDiffMBOn.clm_comp' ((evalI 𝕂 oneI).restrictScalars ℝ) (isOpen_parSet D) hη
  have h2 : ContDiffMBOn 1 (fun z : Par 𝕂 E W ↦ z.2.2.1) (parSet D) :=
    (ContinuousLinearMap.fst ℝ E W ∘L ContinuousLinearMap.snd ℝ 𝕂 (E × W) ∘L
      ContinuousLinearMap.snd ℝ 𝕂 (𝕂 × E × W)).contDiffMBOn 1 _
  exact h1.add (isOpen_parSet D) h2

omit [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] [CompleteSpace E] in
/-- `g` is `C^k` if `f` is (compare [GN26, proof of Theorem 2.4.34]): the superposition
operator of the integrand is `C^k` (`contDiffMBOn_superposeParam_of_contDiffMBOn`). -/
theorem contDiffMBOn_gMap_of_contDiffMBOn (hO : IsOpen O) {k : ℕ} (hf : ContDiffMBOn k f O) :
    ContDiffMBOn k (gMap f) (parSet D ×ˢ ball (0 : C(𝕀, E)) D.R) := by
  have : ContinuousSMul ℝ (Par 𝕂 E W) := inferInstance
  have hS := contDiffMBOn_superposeParam_of_contDiffMBOn (K := 𝕀) (E := E) Subtype.val
    continuous_subtype_val k (E' := E) (Z := Par 𝕂 E W)
    (H := fun r : ℝ × (E × Par 𝕂 E W) ↦ integrand f r.1 r.2)
    (O := {r | evalPt r.1 r.2 ∈ O}) (Ω := dom D) (hO.preimage continuous_evalPt) (isOpen_dom D)
    (fun s x hx ↦ D.box_subset (evalPt_mem_box D s.2 hx)) (contDiffMBOn_integrand hO hf)
  have hswap : ContDiffMBOn k (fun q : Par 𝕂 E W × C(𝕀, E) ↦ (q.2, q.1)) univ :=
    (ContinuousLinearEquiv.prodComm ℝ (Par 𝕂 E W) C(𝕀, E)).toContinuousLinearMap.contDiffMBOn k
      univ
  have hc := ContDiffMBOn.comp ((isOpen_parSet D).prod isOpen_ball)
    (isOpen_paramDomain (isOpen_dom D)) hS (hswap.mono (subset_univ _))
    fun q hq ↦ mem_paramDomain D hq.1 hq.2
  exact hc.clm_comp' ((primitiveCLM 𝕂).restrictScalars ℝ) ((isOpen_parSet D).prod isOpen_ball)

omit [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] in
/-- **The solution map is `C^k`** if `f` is ([GN26, Theorem 2.4.34]): the fixed point of a
`C^k` uniform family of contractions is `C^k`
(`UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn`). -/
theorem contDiffMBOn_flowPhi_of_contDiffMBOn (hO : IsOpen O) {k : ℕ} (hf : ContDiffMBOn k f O) :
    ContDiffMBOn k (flowPhi D hfc) (parSet D) := by
  have : ContinuousSMul ℝ (Par 𝕂 E W) := inferInstance
  have hη := (uniformContraction D hfc).contDiffMBOn_fixedPoint_of_contDiffMBOn k
    (contDiffMBOn_gMap_of_contDiffMBOn D hO hf)
  have h1 := ContDiffMBOn.clm_comp' ((evalI 𝕂 oneI).restrictScalars ℝ) (isOpen_parSet D) hη
  have h2 : ContDiffMBOn k (fun z : Par 𝕂 E W ↦ z.2.2.1) (parSet D) :=
    (ContinuousLinearMap.fst ℝ E W ∘L ContinuousLinearMap.snd ℝ 𝕂 (E × W) ∘L
      ContinuousLinearMap.snd ℝ 𝕂 (𝕂 × E × W)).contDiffMBOn k _
  exact h1.add (isOpen_parSet D) h2

include hfc in
omit [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] [CompleteSpace E] [AddCommGroup W]
  [Module ℝ W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  in
/-- `g` is continuous if `f` is. -/
theorem continuousOn_gMap : ContinuousOn (gMap f) (parSet D ×ˢ ball (0 : C(𝕀, E)) D.R) :=
  ((primitiveCLM 𝕂).continuous.comp_continuousOn
    ((continuousOn_superposeParam (continuousOn_intH D hfc)).comp
      (continuous_snd.prodMk continuous_fst).continuousOn fun _ hq ↦ mem_paramDomain D hq.1 hq.2))

omit [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] [AddCommGroup W] [Module ℝ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **The solution map is continuous** if `f` is ([GN26, Theorem 2.4.34], `k = 0`). -/
theorem continuousOn_flowPhi : ContinuousOn (flowPhi D hfc) (parSet D) := by
  have hη := (uniformContraction D hfc).continuousOn_fixedPoint (continuousOn_gMap D hfc)
  have hp : Continuous fun z : Par 𝕂 E W ↦ z.2.2.1 := by fun_prop
  exact ((evalI 𝕂 oneI).continuous.comp_continuousOn hη).add hp.continuousOn

/-! ### The solutions -/

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
theorem eta_mem {z : Par 𝕂 E W} (hz : z ∈ parSet D) : eta D hfc z ∈ closedBall 0 (D.R / 2) :=
  (uniformContraction D hfc).fixedPoint_mem hz

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
theorem eta_mem_ball {z : Par 𝕂 E W} (hz : z ∈ parSet D) : eta D hfc z ∈ ball 0 D.R :=
  (uniformContraction D hfc).subset (eta_mem D hfc hz)

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- `η(z)(τ) = ∫₀^τ H(s, η(z)(s), z) ds`. -/
theorem eta_apply {z : Par 𝕂 E W} (hz : z ∈ parSet D) (τ : 𝕀) :
    eta D hfc z τ = ∫ v in (0 : ℝ)..τ, extendI (superposeParam (intH f) (eta D hfc z, z)) v := by
  have h := (uniformContraction D hfc).apply_fixedPoint hz
  rw [← primitiveCLM_apply (𝕜 := 𝕂)]
  exact (congrArg (fun γ : C(𝕀, E) ↦ γ τ) h).symm

omit [CompleteSpace E] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [ContinuousSMul 𝕂 W] [AddCommGroup W]
  [Module ℝ W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W]
  [IsScalarTower ℝ 𝕂 E] [NormedSpace ℝ E] in
include hfc in
theorem superposeParam_intH_apply' {z : Par 𝕂 E W} (hz : z ∈ parSet D) {ψ : C(𝕀, E)}
    (hψ : ψ ∈ ball (0 : C(𝕀, E)) D.R) (u : 𝕀) :
    superposeParam (intH f) (ψ, z) u =
      (z.1 - z.2.1) • f (z.2.1 + (u : 𝕂) * (z.1 - z.2.1), ψ u + z.2.2.1, z.2.2.2) :=
  superposeParam_intH_apply D hfc hz hψ u

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **The rescaling identity** ([GN26, (2.107)]): for `σ ∈ [0, 1]`,
`η(t₀ + σ (t - t₀), t₀, y₀, p) = η(t, t₀, y₀, p)(σ ·)`. -/
theorem eta_rescale {t t₀ : 𝕂} {y₀ : E} {p : W} (hz : (t, t₀, y₀, p) ∈ parSet D) (σ : 𝕀)
    (hσ : 0 ≤ (σ : ℝ)) :
    eta D hfc (t₀ + (σ : 𝕂) * (t - t₀), t₀, y₀, p) =
      (eta D hfc (t, t₀, y₀, p)).comp (scaleI σ) := by
  set z : Par 𝕂 E W := (t, t₀, y₀, p)
  set t' := t₀ + (σ : 𝕂) * (t - t₀)
  have ht' : t' ∈ ball q₀.1 D.ρ := by
    have := (convex_ball q₀.1 D.ρ).add_smul_sub_mem hz.2.1 hz.1 ⟨hσ, σ.2.2⟩
    simpa [t', RCLike.real_smul_eq_coe_mul] using this
  have hz' : ((t', t₀, y₀, p) : Par 𝕂 E W) ∈ parSet D := ⟨ht', hz.2⟩
  set η := eta D hfc z
  have hη := eta_mem_ball D hfc hz
  set ζ := η.comp (scaleI σ)
  have hζ : ζ ∈ closedBall (0 : C(𝕀, E)) (D.R / 2) := by
    rw [mem_closedBall_zero_iff]
    refine (ContinuousMap.norm_le ζ (by linarith [D.R_pos])).2 fun τ ↦ ?_
    exact (η.norm_coe_le_norm _).trans (mem_closedBall_zero_iff.1 (eta_mem D hfc hz))
  have hζb : ζ ∈ ball (0 : C(𝕀, E)) D.R :=
    closedBall_subset_ball (by linarith [D.R_pos]) hζ
  symm
  refine (uniformContraction D hfc).eq_fixedPoint hz' hζ ?_
  ext τ
  simp only [gMap, primitiveCLM_apply]
  set g : ℝ → E := extendI (superposeParam (intH f) (η, z))
  have hsc : ((σ : ℝ) • ∫ v in (0 : ℝ)..τ, g ((σ : ℝ) * v)) =
      ∫ v in (σ : ℝ) * 0..(σ : ℝ) * τ, g v :=
    intervalIntegral.smul_integral_comp_mul_left _ _
  rw [mul_zero] at hsc
  change _ = η (scaleI σ τ)
  rw [eta_apply D hfc hz (scaleI σ τ), scaleI_apply, ← hsc, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun v hv ↦ ?_
  have hvI : v ∈ 𝕀 := uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ τ.2 hv
  have hσv : (σ : ℝ) * v ∈ 𝕀 := mul_mem_Icc_neg_one_one σ.2 hvI
  simp only [g]
  rw [extendI_of_mem _ hvI, extendI_of_mem _ hσv,
    superposeParam_intH_apply' D hfc hz' hζb, superposeParam_intH_apply' D hfc hz hη,
    RCLike.real_smul_eq_coe_smul (K := 𝕂), smul_smul]
  have hζv : ζ ⟨v, hvI⟩ = η ⟨(σ : ℝ) * v, hσv⟩ := rfl
  rw [hζv]
  congr 1
  · simp only [t']; ring
  · congr 1
    refine Prod.ext ?_ rfl
    simp only [t', z]; push_cast; ring

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- `Φ(t₀ + σ (t - t₀), t₀, y₀, p) = η(t, t₀, y₀, p)(σ) + y₀` for `σ ∈ [0, 1]`. -/
theorem flowPhi_rescale {t t₀ : 𝕂} {y₀ : E} {p : W} (hz : (t, t₀, y₀, p) ∈ parSet D) (σ : 𝕀)
    (hσ : 0 ≤ (σ : ℝ)) :
    flowPhi D hfc (t₀ + (σ : 𝕂) * (t - t₀), t₀, y₀, p) = eta D hfc (t, t₀, y₀, p) σ + y₀ := by
  simp only [flowPhi, eta_rescale D hfc hz σ hσ, ContinuousMap.comp_apply]
  congr 2
  exact Subtype.ext (by simp [oneI])

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- `Φ(t₀, t₀, y₀, p) = y₀`. -/
theorem flowPhi_self {t₀ : 𝕂} {y₀ : E} {p : W} (hz : (t₀, t₀, y₀, p) ∈ parSet D) :
    flowPhi D hfc (t₀, t₀, y₀, p) = y₀ := by
  have h := flowPhi_rescale D hfc hz ⟨0, by norm_num, by norm_num⟩ le_rfl
  simp only [RCLike.ofReal_zero, zero_mul, add_zero] at h
  rw [h, eta_apply D hfc hz, intervalIntegral.integral_same, zero_add]

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- The solutions stay in the domain of `f`. -/
theorem mem_O_flowPhi {t t₀ : 𝕂} {y₀ : E} {p : W} (hz : (t, t₀, y₀, p) ∈ parSet D) :
    (t, flowPhi D hfc (t, t₀, y₀, p), p) ∈ O := by
  refine D.box_subset ⟨ball_subset_ball (by linarith [D.ρ_pos]) hz.1, ?_, hz.2.2.2⟩
  rw [mem_ball_iff_norm]
  have h1 : ‖eta D hfc (t, t₀, y₀, p) oneI‖ ≤ D.R / 2 :=
    ((eta D hfc _).norm_coe_le_norm _).trans (mem_closedBall_zero_iff.1 (eta_mem D hfc hz))
  have h2 := mem_ball_iff_norm.1 hz.2.2.1
  calc ‖flowPhi D hfc (t, t₀, y₀, p) - q₀.2.1‖
      ≤ ‖eta D hfc (t, t₀, y₀, p) oneI‖ + ‖y₀ - q₀.2.1‖ := by
        simp only [flowPhi]; rw [add_sub_assoc]; exact norm_add_le _ _
    _ < D.R / 2 + D.R := by linarith
    _ ≤ 2 * D.R := by linarith [D.R_pos]

omit [AddCommGroup W] [Module ℝ W] [Module 𝕂 W] [IsScalarTower ℝ 𝕂 W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕂 W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **The solutions solve the differential equation**:
`∂ₜ Φ(t, t₀, y₀, p) = f(t, Φ(t, t₀, y₀, p), p)`, as soon as `t ↦ Φ(t, t₀, y₀, p)` has derivatives
`g'(s)` on the ball and `g'` is continuous at `t`. Away from `t₀`, the rescaling identity shows
that along the segment from `t₀` to `s` the solution is a primitive; at `t₀`, by continuity. -/
theorem hasDerivAt_flowPhi_time_of (hO : IsOpen O) {t t₀ : 𝕂} {y₀ : E} {p : W}
    (hz : (t, t₀, y₀, p) ∈ parSet D) {g' : 𝕂 → E}
    (hdiff : ∀ s ∈ ball q₀.1 D.ρ, HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p)) (g' s) s)
    (hcont : ContinuousAt g' t) :
    HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p))
      (f (t, flowPhi D hfc (t, t₀, y₀, p), p)) t := by
  set g : 𝕂 → E := fun s ↦ flowPhi D hfc (s, t₀, y₀, p)
  have hmem : ∀ s ∈ ball q₀.1 D.ρ, ((s, t₀, y₀, p) : Par 𝕂 E W) ∈ parSet D :=
    fun s hs ↦ ⟨hs, hz.2⟩
  -- away from `t₀`: compare with the primitive along the segment from `t₀` to `s`
  have hoff : ∀ s ∈ ball q₀.1 D.ρ, s ≠ t₀ → g' s = f (s, g s, p) := by
    intro s hs hne
    have hzs := hmem s hs
    set η := eta D hfc (s, t₀, y₀, p)
    set S := superposeParam (intH f) (η, ((s, t₀, y₀, p) : Par 𝕂 E W))
    have hh : HasDerivAt (fun w : ℝ ↦ t₀ + (w : 𝕂) * (s - t₀)) (s - t₀) 1 := by
      simpa using (((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕂).hasDerivAt (x := (1 : ℝ))).mul_const
        (s - t₀)).const_add t₀
    have h1 : HasDerivAt (g ∘ fun w : ℝ ↦ t₀ + (w : 𝕂) * (s - t₀)) ((s - t₀) • g' s) 1 := by
      refine HasDerivAt.scomp (1 : ℝ) ?_ hh
      simpa using hdiff s hs
    have h2 : HasDerivAt (fun u : ℝ ↦ (∫ τ in (0 : ℝ)..u, extendI S τ) + y₀) (extendI S 1) 1 :=
      (hasDerivAt_primitive S 1).add_const y₀
    have hI : EqOn (g ∘ fun w : ℝ ↦ t₀ + (w : 𝕂) * (s - t₀))
        (fun u ↦ (∫ τ in (0 : ℝ)..u, extendI S τ) + y₀) (Icc 0 1) := by
      intro w hw
      have hwI : w ∈ 𝕀 := ⟨by linarith [hw.1], hw.2⟩
      have h := flowPhi_rescale D hfc hzs ⟨w, hwI⟩ hw.1
      simp only [Function.comp_apply, g]
      exact h.trans (by rw [eta_apply D hfc hzs])
    have h01 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have huniq := (uniqueDiffOn_Icc zero_lt_one 1 h01).eq_deriv _ h1.hasDerivWithinAt
      (h2.hasDerivWithinAt.congr_of_mem (fun w hw ↦ hI hw) h01)
    have hS1 : extendI S 1 = (s - t₀) • f (s, g s, p) := by
      rw [extendI_of_mem _ ⟨by norm_num, le_rfl⟩,
        superposeParam_intH_apply' D hfc hzs (eta_mem_ball D hfc hzs)]
      simp only [RCLike.ofReal_one, one_mul, add_sub_cancel]
      rfl
    rw [hS1] at huniq
    exact smul_right_injective E (sub_ne_zero.2 hne) huniq
  by_cases hne : t = t₀
  · -- at `t₀`: by continuity of both sides
    have hcF : ContinuousAt (fun s ↦ f (s, g s, p)) t := by
      have hgc : ContinuousAt g t := (hdiff t hz.1).continuousAt
      have hc : ContinuousAt (fun s ↦ ((s, g s, p) : 𝕂 × E × W)) t :=
        continuousAt_id.prodMk (hgc.prodMk continuousAt_const)
      exact ContinuousAt.comp (g := f)
        (hfc.continuousAt (hO.mem_nhds (mem_O_flowPhi D hfc hz))) hc
    have hev : (fun s ↦ f (s, g s, p)) =ᶠ[𝓝[≠] t] g' := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz.1)]
        with s hs hsb
      exact (hoff s hsb (hne ▸ hs)).symm
    have hlim := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      ((hcF.tendsto.mono_left nhdsWithin_le_nhds).congr' hev)
    rw [← hlim]
    exact hdiff t hz.1
  · rw [← hoff t hz.1 hne]
    exact hdiff t hz.1

end General

/-! ### The complex case -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {W : Type*} [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] {f : ℂ × E × W → E} {O : Set (ℂ × E × W)}
  {q₀ : ℂ × E × W} (D : FlowData f O q₀) (hfc : ContinuousOn f O)

/-- The interval `[-1, 1]` on which the curves are parametrized. -/
local notation "𝕀" => (Icc (-1 : ℝ) 1)

/-- **The solution map is complex analytic** ([GN26, Theorem 2.4.34], case `𝕂 = ℂ`). -/
theorem complexAnalyticOn_flowPhi (hO : IsOpen O) (hf : ComplexAnalyticOn f O) :
    ComplexAnalyticOn (flowPhi D hfc) (parSet D) := by
  have hhol := (complexAnalyticOn_iff_holomorphicOn hO).1 hf
  have hf1 : ContDiffMBOn 1 f O := hhol.1 1
  refine complexAnalyticOn_of_contDiffMBOn_one (isOpen_parSet D)
    (contDiffMBOn_flowPhi D hfc hO hf1) fun z hz w ↦ ?_
  rw [(hasDirDerivAt_flowPhi D hfc hO hf1 hz _).dMB_eq,
    (hasDirDerivAt_flowPhi D hfc hO hf1 hz _).dMB_eq,
    derivFixedPoint_smul D hfc hO hf1 hhol.2 hz]
  simp [smul_add]

/-- The solutions are complex differentiable in time. -/
theorem exists_hasDerivAt_flowPhi (hO : IsOpen O) (hf : ComplexAnalyticOn f O) {t t₀ : ℂ}
    {y₀ : E} {p : W} (hz : (t, t₀, y₀, p) ∈ parSet D) :
    ∃ d, HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p)) d t := by
  have hG := (complexAnalyticOn_flowPhi D hfc hO hf).gateauxAnalyticOn (isOpen_parSet D) _ hz
    ((1, 0, 0, 0) : Par ℂ E W)
  have hline : ∀ w : ℂ, ((t, t₀, y₀, p) : Par ℂ E W) + w • ((1, 0, 0, 0) : Par ℂ E W) =
      (t + w, t₀, y₀, p) := fun w ↦ by simp
  have h0 : (0 : ℂ) ∈ {w : ℂ | ((t, t₀, y₀, p) : Par ℂ E W) + w • ((1, 0, 0, 0) : Par ℂ E W) ∈
      parSet D} := by
    simpa only [mem_ofPred_eq, hline, add_zero] using hz
  have hd := hG.hasCDerivAt h0
  refine ⟨_, hasDerivAt_iff_tendsto_slope_zero.2 (hd.congr fun w ↦ ?_)⟩
  simp only [hline, zero_add, add_zero]

/-- **The solutions solve the differential equation**:
`∂ₜ Φ(t, t₀, y₀, p) = f(t, Φ(t, t₀, y₀, p), p)`. -/
theorem hasDerivAt_flowPhi_time (hO : IsOpen O) (hf : ComplexAnalyticOn f O) {t t₀ : ℂ}
    {y₀ : E} {p : W} (hz : (t, t₀, y₀, p) ∈ parSet D) :
    HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p))
      (f (t, flowPhi D hfc (t, t₀, y₀, p), p)) t := by
  set g : ℂ → E := fun s ↦ flowPhi D hfc (s, t₀, y₀, p)
  have hdiff : ∀ s ∈ ball q₀.1 D.ρ, HasDerivAt g (deriv g s) s := fun s hs ↦ by
    obtain ⟨d, hd⟩ := exists_hasDerivAt_flowPhi D hfc hO hf (t := s) ⟨hs, hz.2⟩
    exact hd.differentiableAt.hasDerivAt
  have hdo : DifferentiableOn ℂ g (ball q₀.1 D.ρ) := fun s hs ↦
    (hdiff s hs).differentiableAt.differentiableWithinAt
  exact hasDerivAt_flowPhi_time_of D hfc hO hz hdiff
    ((hdo.analyticOnNhd isOpen_ball).deriv t hz.1).continuousAt

/-! ### Real solutions for real data -/

omit [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℂ W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **Real data give real solutions** (cf. [GN26, Lemma 2.4.30]). Let `R ⊆ E` be a closed
real subspace and `P_R ⊆ W` a set of parameters such that `f(r, y, p) ∈ R` for real `r`, `y ∈ R`
and `p ∈ P_R`. Then `Φ(t, t₀, y₀, p) ∈ R` for real `t, t₀`, `y₀ ∈ R` and `p ∈ P_R`: the maps
`g(z, ·)` preserve the closed set of curves with values in `R`, which therefore contains the
fixed point. -/
theorem flowPhi_mem_of_real (R : Submodule ℝ E) (hR : IsClosed (R : Set E)) (PR : Set W)
    (hfR : ∀ (r : ℝ) (y : E) (p : W), y ∈ R → p ∈ PR → ((r : ℂ), y, p) ∈ O →
      f ((r : ℂ), y, p) ∈ R)
    {t t₀ : ℝ} {y₀ : E} {p : W} (hy₀ : y₀ ∈ R) (hp : p ∈ PR)
    (hz : ((t : ℂ), (t₀ : ℂ), y₀, p) ∈ parSet D) :
    flowPhi D hfc ((t : ℂ), (t₀ : ℂ), y₀, p) ∈ R := by
  set z : Par ℂ E W := ((t : ℂ), (t₀ : ℂ), y₀, p)
  set hU := uniformContraction D hfc
  set K : Set C(𝕀, E) := {η | ∀ s, η s ∈ R}
  have hK : IsClosed K := by
    simp only [K, ofPred_forall]
    exact isClosed_iInter fun s ↦ hR.preimage (continuous_eval_const s)
  -- `g(z, ·)` preserves `K`
  have hmaps : ∀ η ∈ K, η ∈ closedBall (0 : C(𝕀, E)) (D.R / 2) → gMap f (z, η) ∈ K := by
    intro η hηK hηb
    have hηb' : η ∈ ball (0 : C(𝕀, E)) D.R := closedBall_subset_ball (by linarith [D.R_pos]) hηb
    set S := superposeParam (intH f) (η, z)
    have hS : ∀ u : 𝕀, S u ∈ R := by
      intro u
      rw [superposeParam_intH_apply' D hfc hz hηb' u]
      have hpt : ((t₀ + (u : ℝ) * (t - t₀) : ℝ) : ℂ) = (t₀ : ℂ) + (u : ℂ) * ((t : ℂ) - t₀) := by
        push_cast; ring
      have hO' := D.box_subset (evalPt_mem_box D u.2 (mem_paramDomain D hz hηb' u))
      have hy : η u + y₀ ∈ R := R.add_mem (hηK u) hy₀
      have hf' := hfR (t₀ + (u : ℝ) * (t - t₀)) _ _ hy hp (by rw [hpt]; exact hO')
      rw [hpt] at hf'
      have hc : ∀ x ∈ R, ((t : ℂ) - t₀) • x ∈ R := fun x hx ↦ by
        rw [show ((t : ℂ) - t₀) = ((t - t₀ : ℝ) : ℂ) by push_cast; ring, Complex.coe_smul]
        exact R.smul_mem _ hx
      exact hc _ hf'
    intro τ
    simp only [gMap, primitiveCLM_apply]
    have hcont : Continuous fun v ↦ (⟨extendI S v, by
        simp only [extendI, IccExtend]; exact hS _⟩ : R) :=
      (continuous_extendI S).subtype_mk _
    have h := R.subtypeL.intervalIntegral_comp_comm (a := 0) (b := (τ : ℝ))
      (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 τ)
    rw [show (fun v ↦ R.subtypeL (⟨extendI S v, _⟩ : R)) = extendI S from rfl] at h
    rw [h]
    exact Subtype.mem _
  -- hence so does the fixed point
  have hiter : ∀ n, (fun ψ ↦ gMap f (z, ψ))^[n] 0 ∈ K := by
    intro n
    induction n with
    | zero => intro s; exact R.zero_mem
    | succ n ih =>
      rw [iterate_succ_apply']
      exact hmaps _ ih (hU.iterate_mem hz (by simpa using (half_pos D.R_pos).le) n)
  have hη : eta D hfc z ∈ K :=
    hK.mem_of_tendsto (hU.tendsto_iterate hz (by simpa using (half_pos D.R_pos).le))
      (Eventually.of_forall hiter)
  exact R.add_mem (hη oneI) hy₀

/-- **Holomorphic dependence on time, initial time, initial value and a locally convex parameter**
([GN26, Theorem 2.4.34], case `𝕂 = ℂ`, pp. 203–206). Let `E` be a complex Banach space,
`W` a complex locally convex space, and `f : ℂ × E × W → E` complex analytic on an open set
`O ∋ q₀`. There are `ε > 0`, an open neighbourhood `V` of `(q₀.2.1, q₀.2.2)` in `E × W` and a
map `Φ`, complex analytic on `B(q₀.1, ε) × B(q₀.1, ε) × V`, such that for `t₀` in the disc and
`(y₀, p) ∈ V` the map `t ↦ Φ(t, t₀, y₀, p)` solves `y' = f(t, y, p)`, `y(t₀) = y₀`, on the
disc `B(q₀.1, ε)` (in complex time). Moreover, real data give real solutions: if `f` maps real
times, points of a closed real subspace `R ⊆ E` and parameters in `P_R` into `R`, then
`Φ(t, t₀, y₀, p) ∈ R` for real `t, t₀`, `y₀ ∈ R` and `p ∈ P_R`. -/
theorem _root_.LocallyConvex.Analysis.exists_complexAnalyticOn_flow_param {f : ℂ × E × W → E}
    {O : Set (ℂ × E × W)} (hO : IsOpen O) (hf : ComplexAnalyticOn f O) {q₀ : ℂ × E × W}
    (hq₀ : q₀ ∈ O) :
    ∃ ε > (0 : ℝ), ∃ V : Set (E × W), IsOpen V ∧ q₀.2 ∈ V ∧ ∃ Φ : ℂ × ℂ × E × W → E,
      ComplexAnalyticOn Φ (ball q₀.1 ε ×ˢ (ball q₀.1 ε ×ˢ V)) ∧
      (∀ t₀ ∈ ball q₀.1 ε, ∀ v ∈ V, Φ (t₀, t₀, v.1, v.2) = v.1 ∧
        ∀ t ∈ ball q₀.1 ε, (t, Φ (t, t₀, v.1, v.2), v.2) ∈ O ∧
          HasDerivAt (fun s ↦ Φ (s, t₀, v.1, v.2)) (f (t, Φ (t, t₀, v.1, v.2), v.2)) t) ∧
      ∀ (R : Submodule ℝ E), IsClosed (R : Set E) → ∀ PR : Set W,
        (∀ (r : ℝ) (y : E) (p : W), y ∈ R → p ∈ PR → ((r : ℂ), y, p) ∈ O →
          f ((r : ℂ), y, p) ∈ R) →
        ∀ t t₀ : ℝ, (t : ℂ) ∈ ball q₀.1 ε → (t₀ : ℂ) ∈ ball q₀.1 ε → ∀ v ∈ V, v.1 ∈ R → v.2 ∈ PR →
          Φ ((t : ℂ), (t₀ : ℂ), v.1, v.2) ∈ R := by
  have hf1 : ContDiffMBOn 1 f O := ((complexAnalyticOn_iff_holomorphicOn hO).1 hf).1 1
  obtain ⟨D⟩ := exists_flowData hO hf1 hq₀
  have hfc : ContinuousOn f O := hf.1
  refine ⟨D.ρ, D.ρ_pos, ball q₀.2.1 D.R ×ˢ D.P, isOpen_ball.prod D.isOpen_P,
    ⟨mem_ball_self D.R_pos, D.mem_P⟩, flowPhi D hfc, complexAnalyticOn_flowPhi D hfc hO hf,
    fun t₀ ht₀ v hv ↦ ⟨flowPhi_self D hfc ⟨ht₀, ht₀, hv⟩, fun t ht ↦
      ⟨mem_O_flowPhi D hfc ⟨ht, ht₀, hv⟩, hasDerivAt_flowPhi_time D hfc hO hf ⟨ht, ht₀, hv⟩⟩⟩,
    fun R hR PR hfR t t₀ ht ht₀ v hv hy hp ↦
      flowPhi_mem_of_real D hfc R hR PR hfR hy hp ⟨ht, ht₀, hv⟩⟩

end Complex

/-! ### The real case -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] [T2Space W] {f : ℝ × E × W → E}
  {O : Set (ℝ × E × W)} {q₀ : ℝ × E × W} (D : FlowData f O q₀) (hfc : ContinuousOn f O)

/-- The interval `[-1, 1]` on which the curves are parametrized. -/
local notation "𝕀" => (Icc (-1 : ℝ) 1)

/-- **The real solutions solve the differential equation**: for real time, the derivative of
`t ↦ Φ(t, t₀, y₀, p)` is the directional derivative of the `C^1` map `Φ` in the time direction. -/
theorem hasDerivAt_flowPhi_time_real (hO : IsOpen O) (hf : ContDiffMBOn 1 f O) {t t₀ : ℝ}
    {y₀ : E} {p : W} (hz : (t, t₀, y₀, p) ∈ parSet D) :
    HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p))
      (f (t, flowPhi D hfc (t, t₀, y₀, p), p)) t := by
  have hΦ := contDiffMBOn_flowPhi D hfc hO hf
  set e₁ : Par ℝ E W := (1, 0, 0, 0)
  set g' : ℝ → E := fun s ↦ dMB (flowPhi D hfc) ((s, t₀, y₀, p), e₁)
  have hmem : ∀ s ∈ ball q₀.1 D.ρ, ((s, t₀, y₀, p) : Par ℝ E W) ∈ parSet D :=
    fun s hs ↦ ⟨hs, hz.2⟩
  have hdiff : ∀ s ∈ ball q₀.1 D.ρ, HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p)) (g' s) s := by
    intro s hs
    rw [hasDerivAt_iff_tendsto_slope_zero]
    refine (hΦ.hasDirDerivAt (hmem s hs) e₁).congr fun u ↦ ?_
    simp [e₁, Prod.smul_mk]
  have hline : Continuous fun s : ℝ ↦ (((s, t₀, y₀, p) : Par ℝ E W), e₁) := by fun_prop
  have hcont : ContinuousAt g' t :=
    ContinuousAt.comp (g := dMB (flowPhi D hfc))
      (f := fun s : ℝ ↦ (((s, t₀, y₀, p) : Par ℝ E W), e₁))
      ((hΦ.2.2 : ContinuousOn (dMB (flowPhi D hfc)) (parSet D ×ˢ univ)).continuousAt
        (x := (((t, t₀, y₀, p) : Par ℝ E W), e₁))
        (prod_mem_nhds ((isOpen_parSet D).mem_nhds hz) univ_mem)) hline.continuousAt
  exact hasDerivAt_flowPhi_time_of D hfc hO hz hdiff hcont

omit [AddCommGroup W] [Module ℝ W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [LocallyConvexSpace ℝ W] [T2Space W] in
/-- **The real solutions solve the differential equation**, for continuous `f`: by the rescaling
identity, `Φ(r, t₀, y₀, p) = y₀ + ∫_{t₀}^r f(v, Φ(v, t₀, y₀, p), p) dv`, and the integrand is
continuous. -/
theorem hasDerivAt_flowPhi_time_continuous (hO : IsOpen O) {t t₀ : ℝ} {y₀ : E} {p : W}
    (hz : (t, t₀, y₀, p) ∈ parSet D) :
    HasDerivAt (fun s ↦ flowPhi D hfc (s, t₀, y₀, p))
      (f (t, flowPhi D hfc (t, t₀, y₀, p), p)) t := by
  set Φ : ℝ → E := fun s ↦ flowPhi D hfc (s, t₀, y₀, p)
  set F : ℝ → E := fun v ↦ f (v, Φ v, p)
  have hmem : ∀ s ∈ ball q₀.1 D.ρ, ((s, t₀, y₀, p) : Par ℝ E W) ∈ parSet D :=
    fun s hs ↦ ⟨hs, hz.2⟩
  have hΦc : ContinuousOn Φ (ball q₀.1 D.ρ) :=
    (continuousOn_flowPhi D hfc).comp
      (by fun_prop : Continuous fun s : ℝ ↦ ((s, t₀, y₀, p) : Par ℝ E W)).continuousOn hmem
  have hFc : ContinuousOn F (ball q₀.1 D.ρ) := fun v hv ↦
    ContinuousAt.comp_continuousWithinAt (g := f)
      (hfc.continuousAt (hO.mem_nhds (mem_O_flowPhi D hfc (hmem v hv))))
      (continuousWithinAt_id.prodMk ((hΦc v hv).prodMk continuousWithinAt_const))
  -- the integral representation
  have hrep : ∀ r ∈ ball q₀.1 D.ρ, Φ r = y₀ + ∫ v in t₀..r, F v := by
    intro r hr
    have hzr := hmem r hr
    have hcongr : ∫ u in (0 : ℝ)..1,
          extendI (superposeParam (intH f) (eta D hfc (r, t₀, y₀, p), (r, t₀, y₀, p))) u =
        ∫ u in (0 : ℝ)..1, (r - t₀) • F (t₀ + (r - t₀) * u) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu01 : u ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hu
      have huI : u ∈ 𝕀 := ⟨by linarith [hu01.1], hu01.2⟩
      have hres := flowPhi_rescale D hfc hzr ⟨u, huI⟩ hu01.1
      simp only [RCLike.ofReal_real_eq_id, id] at hres
      rw [extendI_of_mem _ huI, superposeParam_intH_apply' D hfc hzr (eta_mem_ball D hfc hzr)]
      simp only [F, Φ, RCLike.ofReal_real_eq_id, id, show t₀ + (r - t₀) * u = t₀ + u * (r - t₀)
        by ring, hres]
    have hsub : ∫ u in (0 : ℝ)..1, (r - t₀) • F (t₀ + (r - t₀) * u) = ∫ v in t₀..r, F v := by
      rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_add_mul]
      simp
    simp only [Φ, flowPhi]
    rw [add_comm, eta_apply D hfc hzr, show ((oneI : 𝕀) : ℝ) = 1 from rfl, hcongr, hsub]
  have hseg : uIcc t₀ t ⊆ ball q₀.1 D.ρ := (convex_ball _ _).ordConnected.uIcc_subset hz.2.1 hz.1
  have hderiv : HasDerivAt (fun r ↦ y₀ + ∫ v in t₀..r, F v) (F t) t :=
    (intervalIntegral.integral_hasDerivAt_right ((hFc.mono hseg).intervalIntegrable)
      (hFc.stronglyMeasurableAtFilter isOpen_ball t hz.1)
      (hFc.continuousAt (isOpen_ball.mem_nhds hz.1))).const_add y₀
  exact hderiv.congr_of_eventuallyEq
    (eventually_of_mem (isOpen_ball.mem_nhds hz.1) fun r hr ↦ hrep r hr)

end Real

/-- **`C^k` dependence on time, initial time, initial value and a locally convex parameter**
([GN26, Theorem 2.4.34], case `𝕂 = ℝ`, pp. 203–206). Let `E` be a real Banach space, `W` a
real locally convex space, `k ≥ 1`, and `f : ℝ × E × W → E` a `C^k` map on an open set `O ∋ q₀`.
There are `ε > 0`, an open neighbourhood `V` of `(q₀.2.1, q₀.2.2)` in `E × W` and a map `Φ`,
`C^k` on `(q₀.1 - ε, q₀.1 + ε)² × V`, such that for `t₀` in the interval and `(y₀, p) ∈ V` the
curve `t ↦ Φ(t, t₀, y₀, p)` solves `y' = f(t, y, p)`, `y(t₀) = y₀`, on the interval. -/
theorem _root_.LocallyConvex.Analysis.exists_contDiffMBOn_flow_lcParam {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {W : Type*} [AddCommGroup W]
    [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
    [LocallyConvexSpace ℝ W] [T2Space W] {f : ℝ × E × W → E} {O : Set (ℝ × E × W)}
    (hO : IsOpen O) {k : ℕ} (hk : 1 ≤ k) (hf : ContDiffMBOn k f O) {q₀ : ℝ × E × W}
    (hq₀ : q₀ ∈ O) :
    ∃ ε > (0 : ℝ), ∃ V : Set (E × W), IsOpen V ∧ q₀.2 ∈ V ∧ ∃ φ : ℝ × ℝ × E × W → E,
      ContDiffMBOn k φ (ball q₀.1 ε ×ˢ (ball q₀.1 ε ×ˢ V)) ∧
      ∀ t₀ ∈ ball q₀.1 ε, ∀ v ∈ V, φ (t₀, t₀, v.1, v.2) = v.1 ∧
        ∀ t ∈ ball q₀.1 ε, (t, φ (t, t₀, v.1, v.2), v.2) ∈ O ∧
          HasDerivAt (fun s ↦ φ (s, t₀, v.1, v.2)) (f (t, φ (t, t₀, v.1, v.2), v.2)) t := by
  have hf1 : ContDiffMBOn 1 f O := hf.of_le hk
  obtain ⟨D⟩ := exists_flowData hO hf1 hq₀
  have hfc : ContinuousOn f O := hf.continuousOn
  exact ⟨D.ρ, D.ρ_pos, ball q₀.2.1 D.R ×ˢ D.P, isOpen_ball.prod D.isOpen_P,
    ⟨mem_ball_self D.R_pos, D.mem_P⟩, flowPhi D hfc,
    contDiffMBOn_flowPhi_of_contDiffMBOn D hfc hO hf,
    fun t₀ ht₀ v hv ↦ ⟨flowPhi_self D hfc ⟨ht₀, ht₀, hv⟩, fun t ht ↦
      ⟨mem_O_flowPhi D hfc ⟨ht, ht₀, hv⟩,
        hasDerivAt_flowPhi_time_real D hfc hO hf1 ⟨ht, ht₀, hv⟩⟩⟩⟩

/-- **Continuous dependence on time, initial time, initial value and a parameter**
([GN26, Theorem 2.4.34], `k = 0`). Let `E` be a real Banach space, `W` a topological space
(for instance a real locally convex space) and `f : ℝ × E × W → E` continuous on an open set
`O ∋ q₀` and Lipschitz in the second variable near `q₀`, uniformly in the others. There are
`ε > 0`, an open neighbourhood `V` of `(q₀.2.1, q₀.2.2)` in `E × W` and a map `Φ`, continuous on
`(q₀.1 - ε, q₀.1 + ε)² × V`, such that for `t₀` in the interval and `(y₀, p) ∈ V` the curve
`t ↦ Φ(t, t₀, y₀, p)` solves `y' = f(t, y, p)`, `y(t₀) = y₀`, on the interval. -/
theorem _root_.LocallyConvex.Analysis.exists_continuousOn_flow_lcParam {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {W : Type*} [TopologicalSpace W]
    {f : ℝ × E × W → E} {O : Set (ℝ × E × W)}
    (hO : IsOpen O) (hfc : ContinuousOn f O) {q₀ : ℝ × E × W} (hq₀ : q₀ ∈ O)
    (hlip : ∃ r₁ > 0, ∃ r₂ > 0, ∃ P : Set W, IsOpen P ∧ q₀.2.2 ∈ P ∧ ∃ L > 0,
      ∀ t ∈ ball q₀.1 r₁, ∀ p ∈ P, ∀ y ∈ ball q₀.2.1 r₂, ∀ y' ∈ ball q₀.2.1 r₂,
        ‖f (t, y, p) - f (t, y', p)‖ ≤ L * ‖y - y'‖) :
    ∃ ε > (0 : ℝ), ∃ V : Set (E × W), IsOpen V ∧ q₀.2 ∈ V ∧ ∃ φ : ℝ × ℝ × E × W → E,
      ContinuousOn φ (ball q₀.1 ε ×ˢ (ball q₀.1 ε ×ˢ V)) ∧
      ∀ t₀ ∈ ball q₀.1 ε, ∀ v ∈ V, φ (t₀, t₀, v.1, v.2) = v.1 ∧
        ∀ t ∈ ball q₀.1 ε, (t, φ (t, t₀, v.1, v.2), v.2) ∈ O ∧
          HasDerivAt (fun s ↦ φ (s, t₀, v.1, v.2)) (f (t, φ (t, t₀, v.1, v.2), v.2)) t := by
  obtain ⟨D⟩ := exists_flowData_of_bounds (exists_bounds_of_lipschitz hO hfc hq₀ hlip)
  exact ⟨D.ρ, D.ρ_pos, ball q₀.2.1 D.R ×ˢ D.P, isOpen_ball.prod D.isOpen_P,
    ⟨mem_ball_self D.R_pos, D.mem_P⟩, flowPhi D hfc, continuousOn_flowPhi D hfc,
    fun t₀ ht₀ v hv ↦ ⟨flowPhi_self D hfc ⟨ht₀, ht₀, hv⟩, fun t ht ↦
      ⟨mem_O_flowPhi D hfc ⟨ht, ht₀, hv⟩,
        hasDerivAt_flowPhi_time_continuous D hfc hO ⟨ht, ht₀, hv⟩⟩⟩⟩

end ODEFlowParam

end LocallyConvex.Analysis

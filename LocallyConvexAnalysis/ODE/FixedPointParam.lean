/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MichalBastiani
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fixed points of contractions depending on a parameter in a locally convex space

Reference: [GN26, Propositions 2.3.26(a)] and 2.3.27(a), pp. 163–166.

Let `E` be a real topological vector space, `P ⊆ E` open, `F` a Banach space, `U ⊆ F` open and
`C ⊆ U` closed and nonempty. Let `f : E × F → F` be such that each `f_p = f(p, ·)`, `p ∈ P`, maps
`C` into `C` and is a contraction on `U` with a common constant `θ < 1`. Let `φ(p)` be the fixed
point of `f_p` in `C`. We show that `φ` is continuous, resp. `C^k` in the sense of
Michal–Bastiani, if `f` is.

## Main definitions

* `UniformContraction f P U C θ`: the family `f(p, ·)`, `p ∈ P`, maps `C` into `C` and consists
  of contractions on `U` with a common constant `θ < 1`.
* `UniformContraction.fixedPoint`: the fixed point `φ(p) ∈ C` of `f(p, ·)`.
* `UniformContraction.derivFixedPoint`: the candidate derivative `dφ(p, q) = ∑ₙ Aₚⁿ bₚ(q)`, where
  `Aₚ v = df((p, φ p), (0, v))` (`UniformContraction.opA`) and `bₚ(q) = df((p, φ p), (q, 0))`
  (`UniformContraction.vecB`).

## Main results

* `UniformContraction.continuousOn_fixedPoint` ([GN26, Proposition 2.3.26(a)]): if `f` is
  continuous on `P × U`, then `φ` is continuous on `P`.
* `UniformContraction.contDiffMBOn_fixedPoint` ([GN26, Proposition 2.3.27(a)] for `k = 1`):
  if `f` is `C^1` on `P × U` in the sense of Michal–Bastiani, then so is `φ` on `P`, with
  `dφ(p, q) = ∑ₙ Aₚⁿ bₚ(q)` (`UniformContraction.hasDirDerivAt_fixedPoint`): the Neumann series
  of `(1 - Aₚ)⁻¹ bₚ(q)`.
* `UniformContraction.dMB_fixedPoint_eq`: `dφ(p, q)` is the fixed point of
  `w ↦ df((p, φ p), (q, w))`.
* `UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn` ([GN26, Proposition 2.3.27(a)]):
  if `f` is `C^k` on `P × U`, then `φ` is `C^k` on `P`, by induction on `k`.

## Implementation notes

* We follow Glöckner–Neeb. For `t ≠ 0` small, with `f_t = f(p + t q, ·)` and `wₙ(t) = f_tⁿ(φ p)`,

    `t⁻¹ (φ(p + t q) - φ(p)) = ∑ₙ hₙ(t)`, `hₙ(t) = t⁻¹ (w_{n+1}(t) - wₙ(t))`,

  since `wₙ(t) → φ(p + t q)` as `n → ∞`. The contraction property gives
  `‖hₙ(t)‖ ≤ θⁿ ‖h₀(t)‖`. Glöckner–Neeb show that the `hₙ` extend continuously to `t = 0` and
  sum them uniformly; here we only need the limits `hₙ(t) → Aₚⁿ bₚ(q)` as `t → 0`, which follow
  by induction on `n` from Glöckner's lemma on difference quotients
  (`ContDiffMBOn.tendsto_quotient`), since `h_{n+1}(t) = t⁻¹ (f(Y_t + t V_t) - f(Y_t))` with
  `Y_t = (p + t q, wₙ(t))`, `V_t = (0, hₙ(t))`; then Tannery's theorem (dominated convergence
  for series) gives the limit of the sum.
* Glöckner–Neeb state the result for a locally convex subset `P` with dense interior of a locally
  convex space `E`, and `C = U` closed convex with dense interior. We take `P` and `U` open and a
  closed invariant set `C ⊆ U` (in the application, a closed ball inside an open ball). For
  `k = 1` neither local convexity nor the Hausdorff property of `E` is needed; the induction for
  higher `k` (`UniformContraction.dMB_fixedPoint_eq` and the next result) assumes both.
* `UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn` gives Proposition 2.3.27(a) for all
  `k`, by induction: `dφ(p, q)` is the fixed point of `w ↦ df((p, φ p), (q, w))`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology NNReal

noncomputable section

namespace LocallyConvex.Analysis

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A family `f(p, ·)`, `p ∈ P`, of self-maps of a closed nonempty set `C ⊆ U` which are
contractions on the open set `U` with a common constant `θ < 1` ([GN26, before Proposition 2.3.26]:
a *uniform family of contractions*). -/
structure UniformContraction (f : E × F → F) (P : Set E) (U C : Set F) (θ : ℝ≥0) : Prop where
  isOpen_param : IsOpen P
  isOpen : IsOpen U
  isClosed : IsClosed C
  nonempty : C.Nonempty
  subset : C ⊆ U
  lt_one : θ < 1
  mapsTo : ∀ p ∈ P, MapsTo (fun x ↦ f (p, x)) C C
  lipschitz : ∀ p ∈ P, ∀ x ∈ U, ∀ y ∈ U, ‖f (p, x) - f (p, y)‖ ≤ θ * ‖x - y‖

namespace UniformContraction

variable {f : E × F → F} {P : Set E} {U C : Set F} {θ : ℝ≥0}

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  [CompleteSpace F] in
theorem contractingWith (h : UniformContraction f P U C θ) {p : E} (hp : p ∈ P) :
    ContractingWith θ ((h.mapsTo p hp).restrict _ C C) :=
  ⟨h.lt_one, LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa [Subtype.dist_eq, dist_eq_norm] using
      h.lipschitz p hp x (h.subset x.2) y (h.subset y.2)⟩

open Classical in
/-- The fixed point `φ(p) ∈ C` of `f(p, ·)` (and `0` for `p ∉ P`). -/
def fixedPoint (h : UniformContraction f P U C θ) (p : E) : F :=
  if hp : p ∈ P then
    haveI : Nonempty C := h.nonempty.to_subtype
    haveI : CompleteSpace C := h.isClosed.completeSpace_coe
    ((h.contractingWith hp).fixedPoint _ : C)
  else 0

variable (h : UniformContraction f P U C θ)
include h

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
theorem fixedPoint_spec {p : E} (hp : p ∈ P) : h.fixedPoint p ∈ C ∧ f (p, h.fixedPoint p) =
    h.fixedPoint p := by
  have : Nonempty C := h.nonempty.to_subtype
  have : CompleteSpace C := h.isClosed.completeSpace_coe
  have hfix := (h.contractingWith hp).fixedPoint_isFixedPt
  have heq : h.fixedPoint p = ((h.contractingWith hp).fixedPoint _ : C) := by
    simp only [fixedPoint, hp, dite_true]
  rw [heq]
  exact ⟨Subtype.prop _, congrArg Subtype.val hfix⟩

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
theorem fixedPoint_mem {p : E} (hp : p ∈ P) : h.fixedPoint p ∈ C :=
  (h.fixedPoint_spec hp).1

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
theorem apply_fixedPoint {p : E} (hp : p ∈ P) : f (p, h.fixedPoint p) = h.fixedPoint p :=
  (h.fixedPoint_spec hp).2

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
/-- The fixed point is the only fixed point in `C`. -/
theorem eq_fixedPoint {p : E} (hp : p ∈ P) {x : F} (hx : x ∈ C) (hfx : f (p, x) = x) :
    x = h.fixedPoint p := by
  have hθ : (θ : ℝ) < 1 := h.lt_one
  have h1 : ‖x - h.fixedPoint p‖ ≤ θ * ‖x - h.fixedPoint p‖ := by
    have := h.lipschitz p hp x (h.subset hx) _ (h.subset (h.fixedPoint_mem hp))
    rwa [hfx, h.apply_fixedPoint hp] at this
  have h2 : ‖x - h.fixedPoint p‖ = 0 := by
    have := norm_nonneg (x - h.fixedPoint p)
    nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 h2)

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  [CompleteSpace F] in
theorem iterate_mem {p : E} (hp : p ∈ P) {x : F} (hx : x ∈ C) (n : ℕ) :
    (fun y ↦ f (p, y))^[n] x ∈ C :=
  ((h.mapsTo p hp).iterate n) hx

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
/-- The iterates converge to the fixed point. -/
theorem tendsto_iterate {p : E} (hp : p ∈ P) {x : F} (hx : x ∈ C) :
    Tendsto (fun n ↦ (fun y ↦ f (p, y))^[n] x) atTop (𝓝 (h.fixedPoint p)) := by
  have : Nonempty C := h.nonempty.to_subtype
  have : CompleteSpace C := h.isClosed.completeSpace_coe
  have ht := (continuous_subtype_val.tendsto _).comp
    ((h.contractingWith hp).tendsto_iterate_fixedPoint ⟨x, hx⟩)
  have heq : h.fixedPoint p = ((h.contractingWith hp).fixedPoint _ : C) := by
    simp only [fixedPoint, hp, dite_true]
  rw [heq]
  refine ht.congr fun n ↦ ?_
  simp only [comp_apply]
  rw [(h.mapsTo p hp).iterate_restrict]
  rfl

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  [CompleteSpace F] in
/-- The `n`-th iterate is a `θⁿ`-contraction on `C`. -/
theorem norm_iterate_sub_le {p : E} (hp : p ∈ P) {x y : F} (hx : x ∈ C) (hy : y ∈ C) (n : ℕ) :
    ‖(fun z ↦ f (p, z))^[n] x - (fun z ↦ f (p, z))^[n] y‖ ≤ θ ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    calc _ ≤ θ * ‖(fun z ↦ f (p, z))^[n] x - (fun z ↦ f (p, z))^[n] y‖ :=
          h.lipschitz p hp _ (h.subset (h.iterate_mem hp hx n)) _
            (h.subset (h.iterate_mem hp hy n))
      _ ≤ θ * (θ ^ n * ‖x - y‖) := by gcongr
      _ = θ ^ (n + 1) * ‖x - y‖ := by rw [pow_succ]; ring

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
/-- `‖φ(q) - φ(p)‖ ≤ (1 - θ)⁻¹ ‖f(q, φ p) - φ p‖` ([GN26, (2.48)]). -/
theorem norm_fixedPoint_sub_le {p q : E} (hp : p ∈ P) (hq : q ∈ P) :
    ‖h.fixedPoint q - h.fixedPoint p‖ ≤
      (1 - θ : ℝ)⁻¹ * ‖f (q, h.fixedPoint p) - h.fixedPoint p‖ := by
  have hθ : (θ : ℝ) < 1 := h.lt_one
  have h1 : ‖h.fixedPoint q - h.fixedPoint p‖ ≤
      θ * ‖h.fixedPoint q - h.fixedPoint p‖ + ‖f (q, h.fixedPoint p) - h.fixedPoint p‖ := by
    calc ‖h.fixedPoint q - h.fixedPoint p‖
        = ‖(f (q, h.fixedPoint q) - f (q, h.fixedPoint p)) +
            (f (q, h.fixedPoint p) - h.fixedPoint p)‖ := by
          rw [h.apply_fixedPoint hq]; congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (by
          gcongr
          exact h.lipschitz q hq _ (h.subset (h.fixedPoint_mem hq)) _
            (h.subset (h.fixedPoint_mem hp)))
  rw [le_inv_mul_iff₀ (by linarith)]
  nlinarith

omit [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NormedSpace ℝ F]
  in
/-- **[GN26, Proposition 2.3.26(a)]**: the fixed point depends continuously on the
parameter. -/
theorem continuousOn_fixedPoint (hf : ContinuousOn f (P ×ˢ U)) : ContinuousOn h.fixedPoint P := by
  intro p hp
  have hP := h.isOpen_param
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hcont : Tendsto (fun q ↦ f (q, h.fixedPoint p)) (𝓝[P] p) (𝓝 (h.fixedPoint p)) := by
    have := (hf (p, h.fixedPoint p) ⟨hp, h.subset (h.fixedPoint_mem hp)⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨(continuous_id.prodMk continuous_const).continuousWithinAt.tendsto,
        eventually_nhdsWithin_of_forall fun q hq ↦ ⟨hq, h.subset (h.fixedPoint_mem hp)⟩⟩)
    rwa [comp_def, h.apply_fixedPoint hp] at this
  have h0 := (tendsto_iff_norm_sub_tendsto_zero.1 hcont).const_mul ((1 - θ : ℝ)⁻¹)
  rw [mul_zero] at h0
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ h0
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact h.norm_fixedPoint_sub_le hp hq

/-! ### Differentiability -/

/-- `Aₚ v = df((p, φ p), (0, v))`. -/
def opA (p : E) (v : F) : F := dMB f ((p, h.fixedPoint p), (0, v))

/-- `bₚ(q) = df((p, φ p), (q, 0))`. -/
def vecB (p q : E) : F := dMB f ((p, h.fixedPoint p), (q, 0))

/-- The derivative `dφ(p, q) = ∑ₙ Aₚⁿ bₚ(q)`. -/
def derivFixedPoint (p q : E) : F := ∑' n, (h.opA p)^[n] (h.vecB p q)

variable (hf : ContDiffMBOn 1 f (P ×ˢ U))
include hf

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- `‖Aₚ v‖ ≤ θ ‖v‖`. -/
theorem norm_opA_le {p : E} (hp : p ∈ P) (v : F) : ‖h.opA p v‖ ≤ θ * ‖v‖ := by
  have hx := h.subset (h.fixedPoint_mem hp)
  have hd := hf.hasDirDerivAt (x := (p, h.fixedPoint p)) ⟨hp, hx⟩ (0, v)
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), h.fixedPoint p + t • v ∈ U :=
    nhdsWithin_le_nhds (((continuous_const.add (continuous_id.smul continuous_const)).tendsto
      (0 : ℝ)).eventually (by simpa using h.isOpen.mem_nhds hx))
  refine le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hd) ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
  have ht0 : t ≠ 0 := ht0
  simp only [comp_apply, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, norm_smul,
    norm_inv, Real.norm_eq_abs]
  calc |t|⁻¹ * ‖f (p, h.fixedPoint p + t • v) - f (p, h.fixedPoint p)‖
      ≤ |t|⁻¹ * (θ * ‖h.fixedPoint p + t • v - h.fixedPoint p‖) := by
        gcongr; exact h.lipschitz p hp _ ht _ hx
    _ = θ * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        field_simp

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem norm_iterate_opA_le {p : E} (hp : p ∈ P) (v : F) (n : ℕ) :
    ‖(h.opA p)^[n] v‖ ≤ θ ^ n * ‖v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    calc _ ≤ θ * ‖(h.opA p)^[n] v‖ := h.norm_opA_le hf hp _
      _ ≤ θ * (θ ^ n * ‖v‖) := by gcongr
      _ = θ ^ (n + 1) * ‖v‖ := by rw [pow_succ]; ring

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- The terms `Aₚⁿ bₚ(q)` are continuous in `(p, q)`. -/
theorem continuousOn_iterate_opA (n : ℕ) :
    ContinuousOn (fun z : E × E ↦ (h.opA z.1)^[n] (h.vecB z.1 z.2)) (P ×ˢ univ) := by
  have hφ := h.continuousOn_fixedPoint hf.continuousOn
  have hdf : ContinuousOn (dMB f) ((P ×ˢ U) ×ˢ univ) := hf.2.2
  have hmem : ∀ z ∈ P ×ˢ (univ : Set E), (z.1, h.fixedPoint z.1) ∈ P ×ˢ U := fun z hz ↦
    ⟨hz.1, h.subset (h.fixedPoint_mem hz.1)⟩
  have hbase : ContinuousOn (fun z : E × E ↦ (z.1, h.fixedPoint z.1)) (P ×ˢ univ) :=
    continuousOn_fst.prodMk (hφ.comp continuousOn_fst fun z hz ↦ hz.1)
  induction n with
  | zero =>
    exact hdf.comp (hbase.prodMk (continuousOn_snd.prodMk continuousOn_const))
      fun z hz ↦ ⟨hmem z hz, mem_univ _⟩
  | succ n ih =>
    simp only [iterate_succ_apply']
    exact hdf.comp (hbase.prodMk (continuousOn_const.prodMk ih)) fun z hz ↦ ⟨hmem z hz, mem_univ _⟩

/-- **[GN26, Proposition 2.3.27(a)]**, `k = 1`: the fixed point has directional
derivatives `dφ(p, q) = ∑ₙ Aₚⁿ bₚ(q)`. -/
theorem hasDirDerivAt_fixedPoint {p : E} (hp : p ∈ P) (q : E) :
    HasDirDerivAt h.fixedPoint p q (h.derivFixedPoint p q) := by
  set x := h.fixedPoint p with hx_def
  have hxC : x ∈ C := h.fixedPoint_mem hp
  have hxU : x ∈ U := h.subset hxC
  have hfx : f (p, x) = x := h.apply_fixedPoint hp
  have hPU : IsOpen (P ×ˢ U) := h.isOpen_param.prod h.isOpen
  -- `p + t q ∈ P` for small `t`
  have hPev : ∀ᶠ t in 𝓝 (0 : ℝ), p + t • q ∈ P :=
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto (0 : ℝ)).eventually
      (by simpa using h.isOpen_param.mem_nhds hp)
  -- the iterates `wₙ(t) = f_tⁿ(x)` and the quotients `hₙ(t)`
  set w : ℕ → ℝ → F := fun n t ↦ (fun y ↦ f (p + t • q, y))^[n] x with hw_def
  set hq : ℕ → ℝ → F := fun n t ↦ t⁻¹ • (w (n + 1) t - w n t) with hq_def
  have hw_succ : ∀ n t, w (n + 1) t = f (p + t • q, w n t) := fun n t ↦ by
    simp only [hw_def, iterate_succ_apply']
  have hwC : ∀ n, ∀ᶠ t in 𝓝 (0 : ℝ), w n t ∈ C := fun n ↦
    hPev.mono fun t ht ↦ h.iterate_mem ht hxC n
  -- `wₙ(t) → x`
  have hw_lim : ∀ n, Tendsto (w n) (𝓝 0) (𝓝 x) := by
    intro n
    induction n with
    | zero => simp [hw_def]
    | succ n ih =>
      have hlin : Tendsto (fun t : ℝ ↦ p + t • q) (𝓝 0) (𝓝 p) :=
        (by fun_prop : Continuous fun t : ℝ ↦ p + t • q).tendsto' 0 p (by simp)
      have h1 : Tendsto (fun t ↦ (p + t • q, w n t)) (𝓝 0) (𝓝[P ×ˢ U] (p, x)) :=
        tendsto_nhdsWithin_iff.2 ⟨hlin.prodMk_nhds ih, (hPev.and (hwC n)).mono fun t ht ↦
          ⟨ht.1, h.subset ht.2⟩⟩
      have h2 := (hf.continuousOn (p, x) ⟨hp, hxU⟩).tendsto.comp h1
      rw [hfx] at h2
      exact h2.congr fun t ↦ (hw_succ n t).symm
  -- `hₙ(t) → Aₚⁿ bₚ(q)`
  have hq_lim : ∀ n, Tendsto (hq n) (𝓝[≠] 0) (𝓝 ((h.opA p)^[n] (h.vecB p q))) := by
    intro n
    induction n with
    | zero =>
      have hd := hf.hasDirDerivAt (x := (p, x)) ⟨hp, hxU⟩ (q, 0)
      refine hd.congr fun t ↦ ?_
      simp only [hq_def, hw_def, zero_add, iterate_zero, id_eq, iterate_one, Prod.smul_mk,
        smul_zero, Prod.mk_add_mk, add_zero, hfx]
    | succ n ih =>
      have hlin : Tendsto (fun t : ℝ ↦ p + t • q) (𝓝 0) (𝓝 p) :=
        (by fun_prop : Continuous fun t : ℝ ↦ p + t • q).tendsto' 0 p (by simp)
      have hquot := hf.tendsto_quotient hPU (y := (p, x))
        (v := ((0 : E), (h.opA p)^[n] (h.vecB p q))) ⟨hp, hxU⟩
      have hg : Tendsto (fun t : ℝ ↦ (((p + t • q, w n t) : E × F),
          (((0 : E), hq n t) : E × F), t)) (𝓝[≠] 0)
          (𝓝[{r : (E × F) × (E × F) × ℝ | r.2.2 ≠ 0}]
            (((p, x) : E × F), (((0 : E), (h.opA p)^[n] (h.vecB p q)) : E × F), (0 : ℝ))) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦ ht⟩
        exact ((hlin.prodMk_nhds (hw_lim n)).mono_left nhdsWithin_le_nhds).prodMk_nhds
          ((tendsto_const_nhds.prodMk_nhds ih).prodMk_nhds
            (tendsto_id.mono_left nhdsWithin_le_nhds))
      have := hquot.comp hg
      rw [iterate_succ_apply']
      refine this.congr' (eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) ↦ ?_)
      simp only [comp_apply, Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, hq_def,
        smul_smul, mul_inv_cancel₀ ht, one_smul, add_sub_cancel, ← hw_succ]
  -- the bound `‖hₙ(t)‖ ≤ θⁿ M`
  set M : ℝ := ‖h.vecB p q‖ + 1
  have hM : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖hq 0 t‖ ≤ M := by
    have := (continuous_norm.tendsto _).comp (hq_lim 0)
    simp only [iterate_zero, id_eq] at this
    exact this.eventually (eventually_le_nhds (by simp [M]))
  have hbound : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ n, ‖hq n t‖ ≤ θ ^ n * M := by
    filter_upwards [hM, nhdsWithin_le_nhds hPev] with t ht hpt n
    have hiter := h.norm_iterate_sub_le hpt (h.mapsTo _ hpt hxC) hxC n
    have hw1 : ∀ m, w (m + 1) t = (fun y ↦ f (p + t • q, y))^[m] (f (p + t • q, x)) :=
      fun m ↦ by simp only [hw_def, iterate_succ_apply]
    calc ‖hq n t‖ = |t|⁻¹ * ‖w (n + 1) t - w n t‖ := by
          simp [hq_def, norm_smul]
      _ ≤ |t|⁻¹ * (θ ^ n * ‖f (p + t • q, x) - x‖) := by
          gcongr; rw [hw1]; exact hiter
      _ = θ ^ n * ‖hq 0 t‖ := by
          simp only [hq_def, hw_def, zero_add, iterate_one, iterate_zero, id_eq, norm_smul,
            norm_inv, Real.norm_eq_abs]
          ring
      _ ≤ θ ^ n * M := by gcongr
  have hsum : Summable fun n ↦ (θ : ℝ) ^ n * M :=
    (summable_geometric_of_lt_one θ.2 h.lt_one).mul_right M
  -- the series of the `hₙ(t)` is the difference quotient of `φ`
  have htsum : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      ∑' n, hq n t = t⁻¹ • (h.fixedPoint (p + t • q) - h.fixedPoint p) := by
    filter_upwards [hbound, nhdsWithin_le_nhds hPev] with t hb hpt
    have hs : Summable fun n ↦ ‖hq n t‖ := hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
    have hpartial : ∀ N, ∑ n ∈ Finset.range N, hq n t = t⁻¹ • (w N t - x) := fun N ↦ by
      simp only [hq_def, ← Finset.smul_sum, Finset.sum_range_sub (fun n ↦ w n t)]
      simp [hw_def]
    have hlimN : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, hq n t) atTop
        (𝓝 (t⁻¹ • (h.fixedPoint (p + t • q) - x))) := by
      simp only [hpartial]
      exact ((h.tendsto_iterate hpt hxC).sub_const x).const_smul _
    exact ((hasSum_iff_tendsto_nat_of_summable_norm hs).2 hlimN).tsum_eq
  -- Tannery's theorem
  have hT := tendsto_tsum_of_dominated_convergence hsum hq_lim hbound
  exact hT.congr' htsum

/-- **[GN26, Proposition 2.3.27(a)]**, `k = 1`: the fixed point is `C^1`. -/
theorem contDiffMBOn_fixedPoint : ContDiffMBOn 1 h.fixedPoint P := by
  have hφ := h.continuousOn_fixedPoint hf.continuousOn
  have hD : ContinuousOn (fun z : E × E ↦ h.derivFixedPoint z.1 z.2) (P ×ˢ univ) := by
    intro z hz
    obtain ⟨p, q⟩ := z
    have hp : p ∈ P := hz.1
    -- a neighbourhood where `‖bₚ(q)‖ ≤ M`
    have hb := h.continuousOn_iterate_opA hf 0 (p, q) hz
    simp only [iterate_zero, id_eq] at hb
    set M : ℝ := ‖h.vecB p q‖ + 1
    obtain ⟨N, hN, hNb⟩ : ∃ N ∈ 𝓝[P ×ˢ univ] (p, q), ∀ z ∈ N, ‖h.vecB z.1 z.2‖ ≤ M :=
      ⟨_, ((continuous_norm.tendsto _).comp hb).eventually (eventually_le_nhds (by simp [M])),
        fun _ hz ↦ hz⟩
    have hsum : Summable fun n ↦ (θ : ℝ) ^ n * M :=
      (summable_geometric_of_lt_one θ.2 h.lt_one).mul_right M
    have hcont : ContinuousOn (fun z : E × E ↦ h.derivFixedPoint z.1 z.2)
        ((P ×ˢ univ) ∩ N) := by
      refine continuousOn_tsum (fun n ↦ (h.continuousOn_iterate_opA hf n).mono
        inter_subset_left) hsum fun n z hz ↦ ?_
      calc _ ≤ θ ^ n * ‖h.vecB z.1 z.2‖ := h.norm_iterate_opA_le hf hz.1.1 _ n
        _ ≤ θ ^ n * M := by gcongr; exact hNb z hz.2
    exact (hcont (p, q) ⟨hz, mem_of_mem_nhdsWithin hz hN⟩).mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin hN)
  have hd : ∀ p ∈ P, ∀ q, HasDirDerivAt h.fixedPoint p q (h.derivFixedPoint p q) :=
    fun p hp q ↦ h.hasDirDerivAt_fixedPoint hf hp q
  refine ⟨hφ, fun p hp q ↦ ?_, ?_⟩
  · rw [(hd p hp q).dMB_eq]
    exact hd p hp q
  · exact hD.congr fun z hz ↦ (hd z.1 hz.1 z.2).dMB_eq

end UniformContraction

/-! ### `C^k` dependence of fixed points -/

section Ck

universe u

/-- The derivative `dφ(p, q)` is the fixed point of `w ↦ df((p, φ p), (q, w))`: differentiate
`φ(p) = f(p, φ(p))` by the chain rule. -/
theorem UniformContraction.dMB_fixedPoint_eq {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {f : E × F → F} {P : Set E} {U C : Set F} {θ : ℝ≥0}
    (h : UniformContraction f P U C θ) (hf : ContDiffMBOn 1 f (P ×ˢ U)) {p : E} (hp : p ∈ P)
    (q : E) :
    dMB h.fixedPoint (p, q) = dMB f ((p, h.fixedPoint p), (q, dMB h.fixedPoint (p, q))) := by
  have h1 := h.contDiffMBOn_fixedPoint hf
  set g : E → E × F := fun p ↦ (p, h.fixedPoint p)
  have hg : ContDiffMBOn 1 g P := ((ContinuousLinearMap.id ℝ E).contDiffMBOn 1 P).prodMk
    h.isOpen_param h1
  have hgP : MapsTo g P (P ×ˢ U) := fun p hp ↦ ⟨hp, h.subset (h.fixedPoint_mem hp)⟩
  obtain ⟨-, hcomp⟩ := hf.comp_one (h.isOpen_param.prod h.isOpen) hg hgP
  -- `φ = f ∘ g` near `p`
  have hev : h.fixedPoint =ᶠ[𝓝 p] f ∘ g :=
    eventually_of_mem (h.isOpen_param.mem_nhds hp) fun p hp ↦ (h.apply_fixedPoint hp).symm
  have hd1 : HasDirDerivAt (f ∘ g) p q (dMB h.fixedPoint (p, q)) :=
    (h1.hasDirDerivAt hp q).congr_of_eventuallyEq hev
  have hdg : dMB g (p, q) = (q, dMB h.fixedPoint (p, q)) :=
    (((ContinuousLinearMap.id ℝ E).hasDirDerivAt p q).prodMk (h1.hasDirDerivAt hp q)).dMB_eq
  calc dMB h.fixedPoint (p, q) = dMB (f ∘ g) (p, q) := hd1.dMB_eq.symm
    _ = dMB f (g p, dMB g (p, q)) := hcomp p hp q
    _ = _ := by rw [hdg]

/-- **[GN26, Proposition 2.3.27(a)]**: if a uniform family of contractions is `C^k` on
`P × U`, its fixed point is `C^k` on `P`. By induction on `k`: the derivative `dφ` is the fixed
point of the uniform family of contractions `w ↦ df((p, φ p), (q, w))` with parameter
`(p, q) ∈ P × E` (`dMB_fixedPoint_eq`), which is `C^(k-1)` since `φ` is. -/
theorem UniformContraction.contDiffMBOn_fixedPoint_of_contDiffMBOn :
    ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    {f : E × F → F} {P : Set E} {U C : Set F} {θ : ℝ≥0} (h : UniformContraction f P U C θ),
    ContDiffMBOn k f (P ×ˢ U) → ContDiffMBOn k h.fixedPoint P := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ _ _ _ f P U C θ h hf
    exact h.continuousOn_fixedPoint hf
  | succ k ih =>
    intro E _ _ _ _ _ _ _ f P U C θ h hf
    have hf1 : ContDiffMBOn 1 f (P ×ˢ U) := hf.of_le (by omega)
    have h1 := h.contDiffMBOn_fixedPoint hf1
    have hφk : ContDiffMBOn k h.fixedPoint P := ih h hf.of_succ
    set φ := h.fixedPoint
    -- the family `G((p, q), w) = df((p, φ p), (q, w))`
    set G : (E × E) × F → F := fun x ↦ dMB f ((x.1.1, φ x.1.1), (x.1.2, x.2))
    have hmem : ∀ p ∈ P, (p, φ p) ∈ P ×ˢ U := fun p hp ↦ ⟨hp, h.subset (h.fixedPoint_mem hp)⟩
    have hPo : IsOpen P := h.isOpen_param
    have hθ : θ < 1 := h.lt_one
    have hG : UniformContraction G (P ×ˢ univ) univ univ θ := {
      isOpen_param := hPo.prod isOpen_univ
      isOpen := isOpen_univ
      isClosed := isClosed_univ
      nonempty := univ_nonempty
      subset := subset_rfl
      lt_one := hθ
      mapsTo := fun _ _ ↦ mapsTo_univ _ _
      lipschitz := by
        rintro ⟨p, q⟩ ⟨hp, -⟩ w - w' -
        have hsplit : ((q, w) : E × F) = (q, w') + (0, w - w') := by simp
        simp only [G]
        rw [hsplit, hf1.dMB_add (h.isOpen_param.prod h.isOpen) (hmem p hp), add_sub_cancel_left]
        exact h.norm_opA_le hf1 hp _ }
    -- `G` is `C^k`
    set O : Set ((E × E) × F) := (P ×ˢ univ) ×ˢ univ
    have hO : IsOpen O := (hPo.prod isOpen_univ).prod isOpen_univ
    have hpre :
        O = (ContinuousLinearMap.fst ℝ E E ∘L ContinuousLinearMap.fst ℝ (E × E) F) ⁻¹' P := by
      ext; simp [O]
    have a1 : ContDiffMBOn k (fun x : (E × E) × F ↦ x.1.1) O :=
      (ContinuousLinearMap.fst ℝ E E ∘L ContinuousLinearMap.fst ℝ (E × E) F).contDiffMBOn k O
    have a2 : ContDiffMBOn k (fun x : (E × E) × F ↦ φ x.1.1) O := by
      rw [hpre]
      exact ContDiffMBOn.comp_clm
        (ContinuousLinearMap.fst ℝ E E ∘L ContinuousLinearMap.fst ℝ (E × E) F) hPo hφk
    have a3 : ContDiffMBOn k (fun x : (E × E) × F ↦ x.1.2) O :=
      (ContinuousLinearMap.snd ℝ E E ∘L ContinuousLinearMap.fst ℝ (E × E) F).contDiffMBOn k O
    have a4 : ContDiffMBOn k (fun x : (E × E) × F ↦ x.2) O :=
      (ContinuousLinearMap.snd ℝ (E × E) F).contDiffMBOn k O
    have hΨ : ContDiffMBOn k (fun x : (E × E) × F ↦ (((x.1.1, φ x.1.1), (x.1.2, x.2)) :
        (E × F) × (E × F))) O := (a1.prodMk hO a2).prodMk hO (a3.prodMk hO a4)
    have hGk' := ContDiffMBOn.comp (g := dMB f)
      (f := fun x : (E × E) × F ↦ (((x.1.1, φ x.1.1), (x.1.2, x.2)) : (E × F) × (E × F)))
      hO ((hPo.prod h.isOpen).prod isOpen_univ) hf.2.2 hΨ
      fun x hx ↦ ⟨hmem x.1.1 hx.1.1, mem_univ _⟩
    have hGk : ContDiffMBOn k G O := hGk'
    have hfix := ih hG hGk
    refine ⟨h1.continuousOn, h1.2.1, ContDiffMBOn.congr_of_isOpen
      (hPo.prod isOpen_univ) (fun z hz ↦ ?_) hfix⟩
    exact (hG.eq_fixedPoint hz (mem_univ _) (h.dMB_fixedPoint_eq hf1 hz.1 z.2).symm).symm

end Ck

end LocallyConvex.Analysis

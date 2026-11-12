/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.OperatorValued
public import LocallyConvexAnalysis.Calculus.Rules
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Lower bounds for families of operators: stable in normed spaces, not in Fréchet spaces

A continuous linear map `A` between normed spaces is a topological embedding if and only if it is
bounded below, `m ‖v‖ ≤ ‖A v‖` for some `m > 0` (`exists_boundedBelow_of_isEmbedding` in
`Calculus/BoundedBelow.lean`). In a locally convex space the analogue of "bounded below" is
"topological embedding", and the question is whether this property is stable, and locally uniform,
along a smooth family of operators. In normed spaces this stability is the key step in the proof
that maps with bounded below derivative reflect smoothness
(`LocallyConvexAnalysis/Calculus/BoundedBelow.lean`); the counterexample below shows that this step
cannot be carried over verbatim to Fréchet spaces.

**In normed spaces** (`exists_uniform_boundedBelow`): let `E`, `F` be normed spaces (no
completeness is needed) and `L : ℝ → L(E, F)` a family such that `(t, v) ↦ L t v` is `C¹` in the
sense of Michal–Bastiani near `t = 0`. If `L 0` is a topological embedding, then the lower bound
is locally uniform: there are `δ, m > 0` with `m ‖v‖ ≤ ‖L t v‖` for `|t| < δ` and all `v`;
equivalently, the inverses of the `L t` on their ranges are equicontinuous for `t` near `0`. The
reason is that `C¹` already gives continuity of `t ↦ L t` in the operator norm
(`continuousOn_of_unc_clm`), and the lower bound survives small perturbations in
norm. The parameter may run over any locally convex space (`eventually_boundedBelow`).

**The locally convex counterexample** (`RapidDecay.counterexample`): let `s` be the Fréchet space
of rapidly decreasing real sequences, with the seminorms `p_k(x) = sup_n (n + 1)^k |x n|`
(`RapidDecay.withSeminorms`); we prove that it is complete (`RapidDecay.completeSpace`), so
the example does not exploit incompleteness. Let `ψ` be a smooth bump with `0 ≤ ψ ≤ 1`,
`ψ(1) = 1`, `ψ(u) = 0` for `|u - 1| ≥ 1/2`, and set
`aₙ(t) = 1 - (1 - e^{-(n+1)}) ψ((n + 1) t)` and `L t x = (aₙ(t) xₙ)ₙ`. Then

* every `L t` is a continuous linear automorphism of `s`, and `L 0 = id`
  (`RapidDecay.L`, `RapidDecay.L_zero`): for fixed `t ≠ 0` only the `n` with
  `(n + 1) |t| < 3/2` see the bump, so `1 / aₙ(t) ≤ e^{3/(2|t|)}`;
* `(t, x) ↦ L t x` is smooth in the sense of Michal–Bastiani on `ℝ × s` (`RapidDecay.smoothMBOn_L`):
  the `j`-th derivative of `aₙ` is bounded by `C_j (n + 1)^j`, uniformly in `t`, so all the
  differentials are continuous into `s` (`RapidDecay.contDiffMBOn_fam`);
* the lower bound is not locally uniform (`RapidDecay.not_uniform_boundedBelow`): for every
  continuous seminorm `q` and all `C`, `δ > 0` there are `|t| < δ` and `v` with
  `C q (L t v) < p₀(v)`. Take `t = 1/(n + 1)` and `v = eₙ`: then `L t eₙ = e^{-(n+1)} eₙ`, while
  `q ≤ C' p_K` for some `K` and `p_K(eₙ) = (n + 1)^K`. Equivalently, the inverses `(L t)⁻¹`
  are not equicontinuous on any neighborhood of `t = 0` (`RapidDecay.not_equicontinuousAt_L_symm`),
  although every `L t` is an isomorphism.

**Source.** We found no source for this counterexample; the construction was made for this
library. We do not claim it is new. It is in the spirit of R. S. Hamilton, *The inverse
function theorem of Nash and Moser*, Bull. Amer. Math. Soc. 7 (1982), Part I, Counterexample 5.3.3
(p. 103): on the Fréchet space of smooth `2π`-periodic functions, the smooth family of averaging
operators `L(t)` has `L(0) = id` but `L(2π/n)` is not invertible, against Theorem 5.3.2, which
says that in Banach spaces invertibility of a smooth family of linear maps is an open condition.
Here every `L t` is invertible, and what fails is the uniformity of the lower bound.

## Main definitions

* `RapidDecay`: the space `s` of rapidly decreasing real sequences, with the seminorms
  `RapidDecay.seminorm k`, `p_k(x) = sup_n (n + 1)^k |x n|`.
* `RapidDecay.mulCLM b hb`: multiplication by a polynomially bounded sequence `b`, a continuous
  linear map of `s`.
* `RapidDecay.Admissible D`, `RapidDecay.fam`: families of multipliers `aₙ(t)` whose
  `t`-derivatives are polynomially bounded in `n`, uniformly in `t`, and the map
  `(t, x) ↦ (aₙ(t) xₙ)ₙ`.
* `RapidDecay.L t`: the continuous linear automorphism `x ↦ (aₙ(t) xₙ)ₙ` of `s`.

## Main results

* `eventually_boundedBelow`, `exists_uniform_boundedBelow`: in normed spaces, if
  `(y, v) ↦ L y v` is `C¹` and `L y₀` is a topological embedding, then the `L y` are bounded
  below, with a common constant, for `y` near `y₀`.
* `RapidDecay.withSeminorms`, `RapidDecay.completeSpace`: the seminorms `p_k` define the topology
  of `s`, and `s` is complete.
* `RapidDecay.contDiffMBOn_fam`: `(t, x) ↦ (aₙ(t) xₙ)ₙ` is smooth on `ℝ × s` for an admissible
  family `aₙ`.
* `RapidDecay.smoothMBOn_L`, `RapidDecay.L_zero`: `(t, x) ↦ L t x` is smooth and `L 0 = id`.
* `RapidDecay.not_uniform_boundedBelow`, `RapidDecay.not_equicontinuousAt_L_symm`: the lower
  bound of the `L t` is not locally uniform near `t = 0`, and the inverses `(L t)⁻¹` are not
  equicontinuous on any neighborhood of `t = 0`.
* `RapidDecay.counterexample`: the combined statement: `L` is a smooth family of isomorphisms of
  `s` with `L 0 = id` whose lower bound is not locally uniform.
-/

@[expose] public section

open Set Filter
open scoped Topology NNReal ENNReal lp

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

section Normed

variable {P : Type*} [AddCommGroup P] [Module ℝ P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [ContinuousSMul ℝ P] [LocallyConvexSpace ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [AddCommGroup P] [Module ℝ P] [IsTopologicalAddGroup P] [ContinuousSMul ℝ P]
    [LocallyConvexSpace ℝ P] in
/-- If `y ↦ L y` is continuous in the operator norm at `y₀` and `L y₀` is an embedding, then the
operators `L y` are bounded below, with a common constant, for `y` near `y₀`. -/
theorem eventually_boundedBelow_of_continuousAt {L : P → E →L[ℝ] F} {y₀ : P}
    (hL : ContinuousAt L y₀) (h₀ : Topology.IsEmbedding (L y₀)) :
    ∃ m > 0, ∀ᶠ y in 𝓝 y₀, ∀ v, m * ‖v‖ ≤ ‖L y v‖ := by
  obtain ⟨m, hm, hbd⟩ := exists_boundedBelow_of_isEmbedding h₀
  refine ⟨m / 2, half_pos hm, ?_⟩
  filter_upwards [hL (Metric.ball_mem_nhds (L y₀) (half_pos hm))] with y hy v
  rw [mem_preimage, Metric.mem_ball, dist_eq_norm] at hy
  have h1 : ‖(L y - L y₀) v‖ ≤ m / 2 * ‖v‖ :=
    ((L y - L y₀).le_opNorm v).trans (by gcongr)
  have h2 : ‖L y₀ v‖ ≤ ‖L y v‖ + ‖(L y - L y₀) v‖ := by
    calc ‖L y₀ v‖ = ‖L y v - (L y - L y₀) v‖ := by
          rw [sub_apply, sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  linarith [hbd v]

/-- **Lower bounds are locally uniform in normed spaces.** Let the parameter space `P` be locally
convex, `E`, `F` normed and `L : P → L(E, F)` with `(y, v) ↦ L y v` of class `C¹` in the sense of
Michal–Bastiani on `U × E`. If `L y₀` is a topological embedding, then the `L y` are bounded
below, with a common constant, for `y` near `y₀`. -/
theorem eventually_boundedBelow {L : P → E →L[ℝ] F} {U : Set P} (hU : IsOpen U)
    (hL : ContDiffMBOn 1 (fun p : P × E ↦ L p.1 p.2) (U ×ˢ univ)) {y₀ : P} (hy₀ : y₀ ∈ U)
    (h₀ : Topology.IsEmbedding (L y₀)) :
    ∃ m > 0, ∀ᶠ y in 𝓝 y₀, ∀ v, m * ‖v‖ ≤ ‖L y v‖ :=
  eventually_boundedBelow_of_continuousAt
    ((continuousOn_of_unc_clm hU hL).continuousAt (hU.mem_nhds hy₀)) h₀

/-- **Lower bounds are locally uniform in normed spaces**, for a one-parameter family: if
`(t, v) ↦ L t v` is `C¹` in the sense of Michal–Bastiani near `t = 0` and `L 0` is a topological
embedding, then `m ‖v‖ ≤ ‖L t v‖` for `|t| < δ` and all `v`. -/
theorem exists_uniform_boundedBelow {L : ℝ → E →L[ℝ] F} {U : Set ℝ} (hU : IsOpen U)
    (hL : ContDiffMBOn 1 (fun p : ℝ × E ↦ L p.1 p.2) (U ×ˢ univ)) (h0 : (0 : ℝ) ∈ U)
    (hemb : Topology.IsEmbedding (L 0)) :
    ∃ δ > 0, ∃ m > 0, ∀ t, |t| < δ → ∀ v, m * ‖v‖ ≤ ‖L t v‖ := by
  obtain ⟨m, hm, hev⟩ := eventually_boundedBelow hU hL h0 hemb
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨δ, hδ, m, hm, fun t ht ↦ hball (by simpa [Real.dist_eq] using ht)⟩

end Normed


/-! ### The space of rapidly decreasing sequences -/

/-- The weight `(n + 1) ^ k`. -/
abbrev wt (k n : ℕ) : ℝ := ((n : ℝ) + 1) ^ k

/-- The weights are positive. -/
theorem wt_pos (k n : ℕ) : 0 < wt k n := by positivity

/-- The weights are at least `1`. -/
theorem one_le_wt (k n : ℕ) : 1 ≤ wt k n := one_le_pow₀ (by simp)

/-- `(n + 1)^(k + l) = (n + 1)^k (n + 1)^l`. -/
theorem wt_add (k l n : ℕ) : wt (k + l) n = wt k n * wt l n := pow_add _ _ _

/-- The weights increase with the exponent. -/
theorem wt_mono {k l : ℕ} (h : k ≤ l) (n : ℕ) : wt k n ≤ wt l n :=
  pow_le_pow_right₀ (by simp) h

/-- Rapidly decreasing sequences, as a subspace of `ℝ^ℕ`. -/
def rapidDecaySubmodule : Submodule ℝ (ℕ → ℝ) where
  carrier := {x | ∀ k, ∃ C, ∀ n, wt k n * |x n| ≤ C}
  add_mem' {x y} hx hy k := by
    obtain ⟨C, hC⟩ := hx k
    obtain ⟨D, hD⟩ := hy k
    refine ⟨C + D, fun n ↦ ?_⟩
    calc wt k n * |(x + y) n| ≤ wt k n * |x n| + wt k n * |y n| := by
          rw [← mul_add]; gcongr; exact abs_add_le _ _
      _ ≤ C + D := add_le_add (hC n) (hD n)
  zero_mem' k := ⟨0, fun n ↦ by simp⟩
  smul_mem' c x hx k := by
    obtain ⟨C, hC⟩ := hx k
    refine ⟨|c| * C, fun n ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, mul_left_comm]
    gcongr
    exact hC n

/-- The space `s` of rapidly decreasing real sequences. Its topology is defined below by the
seminorms `p_k(x) = sup_n (n + 1)^k |x n|`. -/
def RapidDecay : Type := rapidDecaySubmodule

namespace RapidDecay

/-- `s` is a vector space. -/
instance : AddCommGroup RapidDecay := inferInstanceAs (AddCommGroup rapidDecaySubmodule)
instance : Module ℝ RapidDecay := inferInstanceAs (Module ℝ rapidDecaySubmodule)

/-- The underlying sequence. -/
def toFun (x : RapidDecay) : ℕ → ℝ := (x : rapidDecaySubmodule).1

instance : CoeFun RapidDecay (fun _ ↦ ℕ → ℝ) := ⟨toFun⟩

/-- Two elements of `s` with the same terms are equal. -/
@[ext] theorem ext {x y : RapidDecay} (h : ∀ n, x n = y n) : x = y :=
  Subtype.ext (funext h)

@[simp] theorem add_apply (x y : RapidDecay) (n : ℕ) : (x + y) n = x n + y n := rfl
@[simp] theorem sub_apply (x y : RapidDecay) (n : ℕ) : (x - y) n = x n - y n := rfl
@[simp] theorem neg_apply (x : RapidDecay) (n : ℕ) : (-x) n = -x n := rfl
@[simp] theorem zero_apply (n : ℕ) : (0 : RapidDecay) n = 0 := rfl
@[simp] theorem smul_apply (c : ℝ) (x : RapidDecay) (n : ℕ) : (c • x) n = c * x n := rfl

/-- The defining property of rapidly decreasing sequences. -/
theorem bound (x : RapidDecay) (k : ℕ) : ∃ C, ∀ n, wt k n * |x n| ≤ C := x.2 k

/-- A sequence with `(n + 1)^k |x n|` bounded for every `k`, as an element of `s`. -/
def mk (x : ℕ → ℝ) (hx : ∀ k, ∃ C, ∀ n, wt k n * |x n| ≤ C) : RapidDecay := ⟨x, hx⟩

@[simp] theorem mk_apply (x : ℕ → ℝ) (hx) (n : ℕ) : mk x hx n = x n := rfl

/-- The sequences `(n + 1)^k x n`, in `ℓ^∞`. -/
def weight (k : ℕ) : RapidDecay →ₗ[ℝ] ℓ^∞(ℕ, ℝ) where
  toFun x := ⟨fun n ↦ wt k n * x n, by
    change Memℓp _ ∞
    rw [memℓp_infty_iff]
    obtain ⟨C, hC⟩ := x.bound k
    refine ⟨C, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos k n)]
    exact hC n⟩
  map_add' x y := lp.ext (funext fun n ↦ by
    change wt k n * (x n + y n) = wt k n * x n + wt k n * y n; ring)
  map_smul' c x := lp.ext (funext fun n ↦ by
    change wt k n * (c * x n) = c * (wt k n * x n); ring)

@[simp] theorem weight_apply (k : ℕ) (x : RapidDecay) (n : ℕ) :
    weight k x n = wt k n * x n := rfl

/-- All the weighted sequences at once. -/
def weights : RapidDecay →ₗ[ℝ] (ℕ → ℓ^∞(ℕ, ℝ)) := LinearMap.pi weight

/-- The uniform structure of `s`, induced from the product `(ℓ^∞)^ℕ` by the weights. -/
instance : UniformSpace RapidDecay := UniformSpace.comap weights inferInstance

/-- The uniform structure is translation invariant. -/
instance : IsUniformAddGroup RapidDecay := IsUniformAddGroup.comap weights

/-- The seminorm `p_k(x) = sup_n (n + 1)^k |x n|`. -/
def seminorm (k : ℕ) : Seminorm ℝ RapidDecay := (normSeminorm ℝ ℓ^∞(ℕ, ℝ)).comp (weight k)

/-- The family of seminorms `p_k`. -/
abbrev seminormFamily : SeminormFamily ℝ RapidDecay ℕ := seminorm

/-- `p_k(x)` is the `ℓ^∞` norm of `((n + 1)^k x n)_n`. -/
theorem seminorm_apply (k : ℕ) (x : RapidDecay) : seminorm k x = ‖weight k x‖ := rfl

/-- Each term is controlled by the seminorm: `(n + 1)^k |x n| ≤ p_k(x)`. -/
theorem le_seminorm (k : ℕ) (x : RapidDecay) (n : ℕ) : wt k n * |x n| ≤ seminorm k x := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero (weight k x) n
  rw [weight_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos k n)] at this
  exact this

/-- A uniform bound for the terms bounds the seminorm. -/
theorem seminorm_le {k : ℕ} {x : RapidDecay} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, wt k n * |x n| ≤ C) : seminorm k x ≤ C := by
  refine lp.norm_le_of_forall_le hC fun n ↦ ?_
  rw [weight_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos k n)]
  exact h n

/-- The seminorms increase with `k`. -/
theorem seminorm_mono {k l : ℕ} (h : k ≤ l) (x : RapidDecay) : seminorm k x ≤ seminorm l x :=
  seminorm_le (by positivity) fun n ↦
    (mul_le_mul_of_nonneg_right (wt_mono h n) (abs_nonneg _)).trans (le_seminorm l x n)

/-- **The seminorms `p_k` define the topology of `s`.** -/
theorem withSeminorms : WithSeminorms seminormFamily := by
  have h := weights.withSeminorms_induced
    (withSeminorms_pi fun _ : ℕ ↦ norm_withSeminorms ℝ ℓ^∞(ℕ, ℝ))
  refine h.congr (fun k ↦ ⟨{⟨k, 0⟩}, 1, fun x ↦ ?_⟩)
    (fun i ↦ ⟨{i.1}, 1, fun x ↦ ?_⟩)
  · simp only [Finset.sup_singleton, one_smul]
    rfl
  · simp only [Finset.sup_singleton, one_smul]
    rfl

/-- `s` is locally convex. -/
instance : LocallyConvexSpace ℝ RapidDecay := withSeminorms.toLocallyConvexSpace
instance : ContinuousSMul ℝ RapidDecay := withSeminorms.continuousSMul

/-- `s` is Hausdorff. -/
instance : T2Space RapidDecay := by
  have : T1Space RapidDecay := withSeminorms.T1_of_separating fun x hx ↦ by
    by_contra! h
    exact hx (ext fun n ↦ by
      have := le_seminorm 0 x n
      rw [h 0] at this
      simpa [wt] using this)
  infer_instance


/-! ### Completeness -/

/-- The evaluations on `ℓ^∞` are continuous. -/
theorem continuous_lp_apply (n : ℕ) : Continuous fun f : ℓ^∞(ℕ, ℝ) ↦ f n :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun f g ↦ by
    simpa [dist_eq_norm] using lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) n).continuous

/-- The uniform structure of `s` is induced by the weights. -/
theorem isUniformInducing_weights : IsUniformInducing weights :=
  isUniformInducing_iff_uniformSpace.mpr rfl

/-- The image of `s` in `(ℓ^∞)^ℕ` is cut out by the relations `y_k = (n + 1)^k y_0`. -/
theorem range_weights : range weights = {y | ∀ k n, y k n = wt k n * y 0 n} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ k n
    change weight k x n = wt k n * weight 0 x n
    simp [wt]
  · intro hy
    refine ⟨mk (fun n ↦ y 0 n) fun k ↦ ⟨‖y k‖, fun n ↦ ?_⟩, ?_⟩
    · have := lp.norm_apply_le_norm ENNReal.top_ne_zero (y k) n
      rwa [hy k n, Real.norm_eq_abs, abs_mul, abs_of_pos (wt_pos k n)] at this
    · funext k
      exact lp.ext (funext fun n ↦ (hy k n).symm)

/-- The image of `s` in `(ℓ^∞)^ℕ` is closed. -/
theorem isClosed_range_weights : IsClosed (range weights) := by
  rw [range_weights, ofPred_forall]
  refine isClosed_iInter fun k ↦ ?_
  rw [ofPred_forall]
  refine isClosed_iInter fun n ↦ isClosed_eq ?_ ?_
  · exact (continuous_lp_apply n).comp (continuous_apply k)
  · exact continuous_const.mul ((continuous_lp_apply n).comp (continuous_apply 0))

/-- **`s` is complete**: it is a Fréchet space. -/
instance completeSpace : CompleteSpace RapidDecay :=
  (completeSpace_iff_isComplete_range isUniformInducing_weights).mpr
    isClosed_range_weights.isComplete

/-! ### Multipliers -/

/-- Polynomially bounded sequences. -/
def PolyBdd (b : ℕ → ℝ) : Prop := ∃ C, 0 ≤ C ∧ ∃ N, ∀ n, |b n| ≤ C * wt N n

/-- A pointwise bound by a weighted sequence gives a bound for the seminorms. -/
theorem seminorm_le_of_le {x y : RapidDecay} {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (h : ∀ n, |y n| ≤ C * wt N n * |x n|) (k : ℕ) :
    seminorm k y ≤ C * seminorm (k + N) x := by
  refine seminorm_le (by have := apply_nonneg (seminorm (k + N)) x; positivity) fun n ↦ ?_
  calc wt k n * |y n| ≤ wt k n * (C * wt N n * |x n|) := by gcongr; exact h n
    _ = C * (wt (k + N) n * |x n|) := by rw [wt_add]; ring
    _ ≤ C * seminorm (k + N) x := by gcongr; exact le_seminorm _ _ _

/-- A polynomially bounded multiplier maps `s` into `s`. -/
theorem PolyBdd.mem {b : ℕ → ℝ} (hb : PolyBdd b) (x : RapidDecay) :
    ∀ k, ∃ C, ∀ n, wt k n * |b n * x n| ≤ C := by
  obtain ⟨C, hC, N, hN⟩ := hb
  intro k
  obtain ⟨D, hD⟩ := x.bound (k + N)
  refine ⟨C * D, fun n ↦ ?_⟩
  calc wt k n * |b n * x n| ≤ wt k n * (C * wt N n * |x n|) := by
        rw [abs_mul]; gcongr; exact hN n
    _ = C * (wt (k + N) n * |x n|) := by rw [wt_add]; ring
    _ ≤ C * D := by gcongr; exact hD n

open Classical in
/-- The multiplication operator `x ↦ (b n * x n)`, for `b` polynomially bounded (and `0`
otherwise). -/
def mulSeq (b : ℕ → ℝ) (x : RapidDecay) : RapidDecay :=
  if hb : PolyBdd b then mk (fun n ↦ b n * x n) (hb.mem x) else 0

/-- The terms of `b x`. -/
theorem mulSeq_apply {b : ℕ → ℝ} (hb : PolyBdd b) (x : RapidDecay) (n : ℕ) :
    mulSeq b x n = b n * x n := by
  simp only [mulSeq, hb, ↓reduceDIte, mk_apply]

/-- A linear map on `s` is continuous if each `p_k ∘ f` is bounded by a multiple of some `p_l`. -/
theorem continuous_of_bound (f : RapidDecay →ₗ[ℝ] RapidDecay)
    (h : ∀ k, ∃ C l, ∀ x, seminorm k (f x) ≤ C * seminorm l x) : Continuous f :=
  withSeminorms.continuous_of_isBounded withSeminorms f (.of_real fun k ↦ by
    obtain ⟨C, l, h⟩ := h k
    exact ⟨{l}, C, fun x ↦ by simpa using h x⟩)

/-- The multiplication operator by a polynomially bounded sequence, as a linear map. -/
def mulLM (b : ℕ → ℝ) (hb : PolyBdd b) : RapidDecay →ₗ[ℝ] RapidDecay where
  toFun := mulSeq b
  map_add' x y := ext fun n ↦ by simp only [mulSeq_apply hb, add_apply]; ring
  map_smul' c x := ext fun n ↦ by
    simp only [mulSeq_apply hb, smul_apply, RingHom.id_apply]; ring

/-- The multiplication operator by a polynomially bounded sequence, as a continuous linear map. -/
def mulCLM (b : ℕ → ℝ) (hb : PolyBdd b) : RapidDecay →L[ℝ] RapidDecay :=
  ⟨mulLM b hb, by
    obtain ⟨C, hC, N, hN⟩ := id hb
    refine continuous_of_bound _ fun k ↦ ⟨C, k + N, fun x ↦ seminorm_le_of_le hC (fun n ↦ ?_) k⟩
    change |mulSeq b x n| ≤ _
    rw [mulSeq_apply hb, abs_mul]
    gcongr
    exact hN n⟩

/-- The terms of `b x`. -/
@[simp] theorem mulCLM_apply {b : ℕ → ℝ} (hb : PolyBdd b) (x : RapidDecay) (n : ℕ) :
    mulCLM b hb x n = b n * x n :=
  mulSeq_apply hb x n


/-! ### Smooth families of multipliers -/

/-- Mean value inequality on `ℝ`. -/
theorem abs_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} {B : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hB : ∀ t, |f' t| ≤ B) (s t : ℝ) : |f t - f s| ≤ B * |t - s| := by
  simpa [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ ↦ (hf x).hasDerivWithinAt) (fun x _ ↦ by simpa using hB x) convex_univ
    (mem_univ s) (mem_univ t)

/-- Taylor's inequality of order two on `ℝ`. -/
theorem abs_taylor_le {f f' f'' : ℝ → ℝ} {B : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hB : ∀ t, |f'' t| ≤ B) (t u : ℝ) :
    |f (t + u) - f t - u * f' t| ≤ B * u ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  let g : ℝ → ℝ := fun v ↦ f (t + v) - v * f' t
  have hg : ∀ v, HasDerivAt g (f' (t + v) - f' t) v := fun v ↦ by
    have h1 : HasDerivAt (fun v ↦ f (t + v)) (f' (t + v)) v :=
      (hf (t + v)).comp_const_add t v
    have h2 := h1.sub ((hasDerivAt_id v).mul_const (f' t))
    simp only [id, one_mul] at h2
    exact h2
  have hbd : ∀ v ∈ Metric.closedBall (0 : ℝ) |u|, ‖f' (t + v) - f' t‖ ≤ B * |u| := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hv
    rw [Real.norm_eq_abs]
    calc |f' (t + v) - f' t| ≤ B * |t + v - t| := abs_sub_le_of_hasDerivAt hf' hB t (t + v)
      _ ≤ B * |u| := by rw [add_sub_cancel_left]; gcongr
  have hu : u ∈ Metric.closedBall (0 : ℝ) |u| := by simp
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (x := 0) (y := u)
    (fun v _ ↦ (hg v).hasDerivWithinAt) hbd (convex_closedBall 0 |u|)
    (Metric.mem_closedBall_self (abs_nonneg u)) hu
  simp only [g, add_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  calc |f (t + u) - f t - u * f' t| = |f (t + u) - u * f' t - f t| := by ring_nf
    _ ≤ B * |u| * |u| := this
    _ = B * u ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- A family of sequences `D 0 n t` with derivatives `D j n t` in `t`, polynomially bounded in
`n` uniformly in `t`. -/
structure Admissible (D : ℕ → ℕ → ℝ → ℝ) : Prop where
  hasDerivAt : ∀ j n t, HasDerivAt (D j n) (D (j + 1) n t) t
  bound : ∀ j, ∃ C, 0 ≤ C ∧ ∃ N, ∀ n t, |D j n t| ≤ C * wt N n

/-- The derivatives of an admissible family form an admissible family. -/
theorem Admissible.shift {D : ℕ → ℕ → ℝ → ℝ} (hD : Admissible D) :
    Admissible fun j ↦ D (j + 1) :=
  ⟨fun j ↦ hD.hasDerivAt (j + 1), fun j ↦ hD.bound (j + 1)⟩

/-- Each member of an admissible family is a polynomially bounded multiplier. -/
theorem Admissible.polyBdd {D : ℕ → ℕ → ℝ → ℝ} (hD : Admissible D) (j : ℕ) (t : ℝ) :
    PolyBdd fun n ↦ D j n t := by
  obtain ⟨C, hC, N, h⟩ := hD.bound j
  exact ⟨C, hC, N, fun n ↦ h n t⟩

/-- The map `(t, x) ↦ (a n t * x n)_n`. -/
def fam (a : ℕ → ℝ → ℝ) (p : ℝ × RapidDecay) : RapidDecay := mulSeq (fun n ↦ a n p.1) p.2

/-- The terms of `fam`. -/
theorem fam_apply {D : ℕ → ℕ → ℝ → ℝ} (hD : Admissible D) (j : ℕ) (p : ℝ × RapidDecay)
    (n : ℕ) : fam (D j) p n = D j n p.1 * p.2 n :=
  mulSeq_apply (hD.polyBdd j p.1) p.2 n

/-- Near `(t₀, x₀)` in `ℝ × s`, the second component is close to `x₀` for `p_l`. -/
theorem eventually_seminorm_snd_lt (x₀ : RapidDecay) (t₀ : ℝ) (l : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℝ × RapidDecay in 𝓝 (t₀, x₀), seminorm l (q.2 - x₀) < η :=
  (withSeminorms.tendsto_nhds Prod.snd x₀).mp (continuous_snd.tendsto (t₀, x₀)) l η hη

/-- `(t, x) ↦ (aₙ(t) xₙ)ₙ` is jointly continuous: split
`a(t) x - a(t₀) x₀ = a(t) (x - x₀) + (a(t) - a(t₀)) x₀` and use the bounds on `a` and `a'`. -/
theorem continuous_fam {D : ℕ → ℕ → ℝ → ℝ} (hD : Admissible D) : Continuous (fam (D 0)) := by
  refine continuous_iff_continuousAt.mpr fun p₀ ↦ ?_
  obtain ⟨t₀, x₀⟩ := p₀
  obtain ⟨C₀, hC₀, N₀, h₀⟩ := hD.bound 0
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := hD.bound 1
  refine (withSeminorms.tendsto_nhds _ _).mpr fun k ε hε ↦ ?_
  set A := seminorm (k + N₁) x₀
  have hA : 0 ≤ A := apply_nonneg _ _
  have hη₀ : 0 < ε / (2 * (C₀ + 1)) := by positivity
  have hη₁ : 0 < ε / (2 * (C₁ + 1) * (A + 1)) := by positivity
  have ht : ∀ᶠ q : ℝ × RapidDecay in 𝓝 (t₀, x₀), |q.1 - t₀| < ε / (2 * (C₁ + 1) * (A + 1)) :=
    (continuous_fst.tendsto (t₀, x₀)).eventually (Metric.ball_mem_nhds t₀ hη₁)
  filter_upwards [ht, eventually_seminorm_snd_lt x₀ t₀ (k + N₀) hη₀] with q hq₁ hq₂
  obtain ⟨t, x⟩ := q
  simp only at hq₁ hq₂
  -- split `a(t) x - a(t₀) x₀ = a(t) (x - x₀) + (a(t) - a(t₀)) x₀`
  set y₁ : RapidDecay := fam (D 0) (t, x - x₀)
  have e : fam (D 0) (t, x) - fam (D 0) (t₀, x₀) =
      y₁ + (fam (D 0) (t, x₀) - fam (D 0) (t₀, x₀)) := by
    ext n
    simp only [y₁, sub_apply, add_apply, fam_apply hD]
    ring
  have h1 : seminorm k y₁ ≤ C₀ * seminorm (k + N₀) (x - x₀) :=
    seminorm_le_of_le hC₀ (fun n ↦ by
      rw [fam_apply hD, abs_mul]; gcongr; exact h₀ n t) k
  have h2 : seminorm k (fam (D 0) (t, x₀) - fam (D 0) (t₀, x₀)) ≤
      (C₁ * |t - t₀|) * seminorm (k + N₁) x₀ :=
    seminorm_le_of_le (by positivity) (fun n ↦ by
      simp only [sub_apply, fam_apply hD]
      rw [← sub_mul, abs_mul]
      gcongr
      calc |D 0 n t - D 0 n t₀| ≤ (C₁ * wt N₁ n) * |t - t₀| :=
            abs_sub_le_of_hasDerivAt (hD.hasDerivAt 0 n) (fun s ↦ h₁ n s) t₀ t
        _ = C₁ * |t - t₀| * wt N₁ n := by ring) k
  rw [e]
  calc seminorm k (y₁ + (fam (D 0) (t, x₀) - fam (D 0) (t₀, x₀)))
      ≤ seminorm k y₁ + seminorm k (fam (D 0) (t, x₀) - fam (D 0) (t₀, x₀)) :=
        map_add_le_add _ _ _
    _ ≤ C₀ * seminorm (k + N₀) (x - x₀) + (C₁ * |t - t₀|) * A := add_le_add h1 h2
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_lt_of_le ?_ ?_
        · calc C₀ * seminorm (k + N₀) (x - x₀) ≤ C₀ * (ε / (2 * (C₀ + 1))) := by gcongr
            _ < (C₀ + 1) * (ε / (2 * (C₀ + 1))) := by nlinarith
            _ = ε / 2 := by field_simp
        · calc C₁ * |t - t₀| * A ≤ (C₁ + 1) * (ε / (2 * (C₁ + 1) * (A + 1))) * (A + 1) := by
                gcongr
                · linarith
                · linarith
            _ = ε / 2 := by field_simp
    _ = ε := by ring


/-- The directional derivative of `(t, x) ↦ (aₙ(t) xₙ)ₙ` in the direction `(τ, h)` is
`τ (aₙ'(t) xₙ)ₙ + (aₙ(t) hₙ)ₙ`, by Taylor's inequality for `aₙ` with the bound on `aₙ''`. -/
theorem hasDirDerivAt_fam {D : ℕ → ℕ → ℝ → ℝ} (hD : Admissible D) (p q : ℝ × RapidDecay) :
    HasDirDerivAt (fam (D 0)) p q (q.1 • fam (D 1) p + fam (D 0) (p.1, q.2)) := by
  obtain ⟨t, x⟩ := p
  obtain ⟨τ, h⟩ := q
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := hD.bound 1
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := hD.bound 2
  refine (withSeminorms.tendsto_nhds _ _).mpr fun k ε hε ↦ ?_
  set K := C₂ * τ ^ 2 * seminorm (k + N₂) x + C₁ * |τ| * seminorm (k + N₁) h
  have hK : 0 ≤ K := by
    have := apply_nonneg (seminorm (k + N₂)) x
    have := apply_nonneg (seminorm (k + N₁)) h
    positivity
  have hball : ∀ᶠ σ : ℝ in 𝓝[≠] 0, |σ| < ε / (K + 1) :=
    (eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < ε / (K + 1)))).mono
      fun σ hσ ↦ by simpa [Real.dist_eq] using hσ
  filter_upwards [hball, self_mem_nhdsWithin] with σ hσ (hσ0 : σ ≠ 0)
  -- the pointwise estimate
  have hpt : ∀ n, |(σ⁻¹ • (fam (D 0) ((t, x) + σ • (τ, h)) - fam (D 0) (t, x)) -
      ((τ, h).1 • fam (D 1) (t, x) + fam (D 0) ((t, x).1, (τ, h).2))) n| ≤
      |σ| * (C₂ * τ ^ 2 * wt N₂ n * |x n| + C₁ * |τ| * wt N₁ n * |h n|) := by
    intro n
    simp only [sub_apply, add_apply, smul_apply, fam_apply hD, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have e : σ⁻¹ * (D 0 n (t + σ * τ) * (x n + σ * h n) - D 0 n t * x n) -
        (τ * (D 1 n t * x n) + D 0 n t * h n) =
        σ⁻¹ * (D 0 n (t + σ * τ) - D 0 n t - σ * τ * D 1 n t) * x n +
          (D 0 n (t + σ * τ) - D 0 n t) * h n := by
      field_simp
      ring
    rw [e]
    have hT := abs_taylor_le (hD.hasDerivAt 0 n) (hD.hasDerivAt 1 n) (fun s ↦ h₂ n s) t (σ * τ)
    have hL := abs_sub_le_of_hasDerivAt (hD.hasDerivAt 0 n) (fun s ↦ h₁ n s) t (t + σ * τ)
    rw [add_sub_cancel_left] at hL
    calc _ ≤ |σ⁻¹ * (D 0 n (t + σ * τ) - D 0 n t - σ * τ * D 1 n t) * x n| +
          |(D 0 n (t + σ * τ) - D 0 n t) * h n| := abs_add_le _ _
      _ = |σ|⁻¹ * |D 0 n (t + σ * τ) - D 0 n t - σ * τ * D 1 n t| * |x n| +
          |D 0 n (t + σ * τ) - D 0 n t| * |h n| := by rw [abs_mul, abs_mul, abs_mul, abs_inv]
      _ ≤ |σ|⁻¹ * (C₂ * wt N₂ n * (σ * τ) ^ 2) * |x n| +
          (C₁ * wt N₁ n * |σ * τ|) * |h n| := by gcongr
      _ = |σ| * (C₂ * τ ^ 2 * wt N₂ n * |x n| + C₁ * |τ| * wt N₁ n * |h n|) := by
        have : |σ| ≠ 0 := abs_ne_zero.mpr hσ0
        rw [mul_pow, ← sq_abs σ, abs_mul]
        field_simp
  calc seminorm k _ ≤ |σ| * K := by
        refine seminorm_le (by positivity) fun n ↦ ?_
        calc wt k n * |_| ≤ wt k n * (|σ| * (C₂ * τ ^ 2 * wt N₂ n * |x n| +
              C₁ * |τ| * wt N₁ n * |h n|)) := by gcongr; exact hpt n
          _ = |σ| * (C₂ * τ ^ 2 * (wt (k + N₂) n * |x n|) +
              C₁ * |τ| * (wt (k + N₁) n * |h n|)) := by rw [wt_add, wt_add]; ring
          _ ≤ |σ| * K := by
              gcongr
              exact add_le_add (by gcongr; exact le_seminorm _ _ _)
                (by gcongr; exact le_seminorm _ _ _)
    _ ≤ ε / (K + 1) * K := by gcongr
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Smoothness of multiplier families**: `(t, x) ↦ (a n t * x n)_n` is smooth in the sense of
Michal–Bastiani on `ℝ × s` when all `t`-derivatives of `a n` are polynomially bounded in `n`,
uniformly in `t`. -/
theorem contDiffMBOn_fam : ∀ (k : ℕ) {D : ℕ → ℕ → ℝ → ℝ}, Admissible D →
    ContDiffMBOn k (fam (D 0)) univ := by
  intro k
  induction k with
  | zero => intro D hD; exact (continuous_fam hD).continuousOn
  | succ k ih =>
    intro D hD
    have heq : dMB (fam (D 0)) = fun r ↦ r.2.1 • fam (D 1) r.1 + fam (D 0) (r.1.1, r.2.2) :=
      funext fun r ↦ (hasDirDerivAt_fam hD r.1 r.2).dMB_eq
    refine ⟨(continuous_fam hD).continuousOn, fun p _ q ↦ ?_, ?_⟩
    · rw [heq]; exact hasDirDerivAt_fam hD p q
    rw [heq, univ_prod_univ]
    let L₁ : (ℝ × RapidDecay) × (ℝ × RapidDecay) →L[ℝ] ℝ × RapidDecay :=
      ContinuousLinearMap.fst ℝ _ _
    let L₂ : (ℝ × RapidDecay) × (ℝ × RapidDecay) →L[ℝ] ℝ × RapidDecay :=
      ((ContinuousLinearMap.fst ℝ ℝ RapidDecay).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        ((ContinuousLinearMap.snd ℝ ℝ RapidDecay).comp (ContinuousLinearMap.snd ℝ _ _))
    let L₃ : (ℝ × RapidDecay) × (ℝ × RapidDecay) →L[ℝ] ℝ :=
      (ContinuousLinearMap.fst ℝ ℝ RapidDecay).comp (ContinuousLinearMap.snd ℝ _ _)
    have h₁ := ContDiffMBOn.comp_clm L₁ isOpen_univ (ih hD.shift)
    have h₂ := ContDiffMBOn.comp_clm L₂ isOpen_univ (ih hD)
    have h₃ := L₃.contDiffMBOn k univ
    rw [preimage_univ] at h₁ h₂
    have hβ : Continuous fun p : ℝ × RapidDecay ↦ LinearMap.lsmul ℝ RapidDecay p.1 p.2 :=
      continuous_smul
    have h₄ := ContDiffMBOn.bilin (LinearMap.lsmul ℝ RapidDecay) hβ isOpen_univ h₃ h₁
    exact h₄.add isOpen_univ h₂


/-! ### The counterexample -/

/-- A smooth bump `ψ` with `0 ≤ ψ ≤ 1`, `ψ = 1` near `1` and `ψ u = 0` for `|u - 1| ≥ 1/2`. -/
def bump : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- `ψ ≥ 0`. -/
theorem bump_nonneg (u : ℝ) : 0 ≤ bump u := bump.nonneg

/-- `ψ ≤ 1`. -/
theorem bump_le_one (u : ℝ) : bump u ≤ 1 := bump.le_one

/-- `ψ(1) = 1`. -/
theorem bump_one : bump 1 = 1 := bump.one_of_mem_closedBall (by simp [bump])

/-- `ψ(u) = 0` for `|u - 1| ≥ 1/2`. -/
theorem bump_eq_zero {u : ℝ} (hu : 1 / 2 ≤ |u - 1|) : bump u = 0 :=
  bump.zero_of_le_dist (by simpa [bump, Real.dist_eq] using hu)

/-- `ψ(0) = 0`. -/
theorem bump_zero : bump 0 = 0 := bump_eq_zero (by norm_num)

/-- The derivatives of `ψ`. -/
theorem hasDerivAt_iteratedDeriv_bump (j : ℕ) (u : ℝ) :
    HasDerivAt (iteratedDeriv j bump) (iteratedDeriv (j + 1) bump u) u := by
  rw [iteratedDeriv_succ]
  exact ((bump.contDiff (n := ⊤)).differentiable_iteratedDeriv j
    (by exact_mod_cast WithTop.coe_lt_top j) u).hasDerivAt

/-- Each derivative of `ψ` is bounded. -/
theorem exists_bound_iteratedDeriv_bump (j : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ u, |iteratedDeriv j bump u| ≤ B := by
  have hc : Continuous (iteratedFDeriv ℝ j bump) :=
    (bump.contDiff (n := ⊤)).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (bump.hasCompactSupport.iteratedFDeriv j)
  refine ⟨max B 0, le_max_right _ _, fun u ↦ ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hB u).trans (le_max_left _ _)

/-- The constants `cₙ = 1 - e^{-(n+1)} ∈ [0, 1)`. -/
def cf (n : ℕ) : ℝ := 1 - Real.exp (-((n : ℝ) + 1))

/-- `cₙ ≥ 0`. -/
theorem cf_nonneg (n : ℕ) : 0 ≤ cf n := by
  rw [cf, sub_nonneg]
  exact Real.exp_le_one_iff.mpr (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

/-- `cₙ ≤ 1`. -/
theorem cf_le_one (n : ℕ) : cf n ≤ 1 := by
  rw [cf]; linarith [Real.exp_pos (-((n : ℝ) + 1))]

/-- The multipliers `aₙ(t) = 1 - cₙ ψ((n + 1) t)`. -/
def a (n : ℕ) (t : ℝ) : ℝ := 1 - cf n * bump (((n : ℝ) + 1) * t)

/-- `aₙ` and its derivatives: `D j n t = ∂ᵗʲ aₙ(t)`. -/
def Dfam (j n : ℕ) (t : ℝ) : ℝ :=
  (if j = 0 then 1 else 0) - cf n * (wt j n * iteratedDeriv j bump (((n : ℝ) + 1) * t))

/-- `D 0 = a`. -/
theorem Dfam_zero : Dfam 0 = a := by
  funext n t
  simp [Dfam, a, wt]

/-- The derivatives of `aₙ` are bounded by `C_j (n + 1)^j`, uniformly in `t`. -/
theorem admissible_Dfam : Admissible Dfam where
  hasDerivAt j n t := by
    have h1 : HasDerivAt (fun t ↦ iteratedDeriv j bump (((n : ℝ) + 1) * t))
        (iteratedDeriv (j + 1) bump (((n : ℝ) + 1) * t) * (((n : ℝ) + 1) * 1)) t :=
      (hasDerivAt_iteratedDeriv_bump j _).comp t ((hasDerivAt_id t).const_mul _)
    have h2 := (h1.const_mul (cf n * wt j n)).const_sub (if j = 0 then (1 : ℝ) else 0)
    convert h2 using 1
    · funext s
      simp only [Dfam]
      ring
    · simp only [Dfam, wt, pow_succ, Nat.add_one_ne_zero, ↓reduceIte]
      ring
  bound j := by
    obtain ⟨B, hB0, hB⟩ := exists_bound_iteratedDeriv_bump j
    refine ⟨1 + B, by positivity, j, fun n t ↦ ?_⟩
    have h1 : |(if j = 0 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have h2 : |cf n * (wt j n * iteratedDeriv j bump (((n : ℝ) + 1) * t))| ≤ wt j n * B := by
      rw [abs_mul, abs_mul, abs_of_nonneg (cf_nonneg n), abs_of_pos (wt_pos j n)]
      calc cf n * (wt j n * |iteratedDeriv j bump (((n : ℝ) + 1) * t)|) ≤ 1 * (wt j n * B) := by
            gcongr
            · exact cf_le_one n
            · exact hB _
        _ = wt j n * B := one_mul _
    calc |Dfam j n t| ≤ 1 + wt j n * B := (abs_sub _ _).trans (add_le_add h1 h2)
      _ ≤ wt j n + wt j n * B := by gcongr; exact one_le_wt j n
      _ = (1 + B) * wt j n := by ring

/-- For fixed `t`, `(aₙ(t))ₙ` is a bounded multiplier. -/
theorem polyBdd_a (t : ℝ) : PolyBdd fun n ↦ a n t := by
  simpa [Dfam_zero] using admissible_Dfam.polyBdd 0 t

/-- `aₙ(t) ≥ e^{-(n+1)}`. -/
theorem exp_neg_le_a (n : ℕ) (t : ℝ) : Real.exp (-((n : ℝ) + 1)) ≤ a n t := by
  have := mul_le_mul_of_nonneg_left (bump_le_one (((n : ℝ) + 1) * t)) (cf_nonneg n)
  rw [a, cf] at *
  linarith

/-- `aₙ(t) > 0`. -/
theorem a_pos (n : ℕ) (t : ℝ) : 0 < a n t := (Real.exp_pos _).trans_le (exp_neg_le_a n t)

/-- `aₙ(0) = 1`. -/
theorem a_zero (n : ℕ) : a n 0 = 1 := by simp [a, bump_zero]

/-- For fixed `t`, `(1 / aₙ(t))ₙ` is bounded by `e^{3/(2|t|)}`: if `ψ((n + 1) t) ≠ 0` then
`(n + 1) t < 3/2`, and `1 / aₙ(t) ≤ e^{n+1}`. -/
theorem polyBdd_inv_a (t : ℝ) : PolyBdd fun n ↦ (a n t)⁻¹ := by
  refine ⟨Real.exp (3 / (2 * |t|)), (Real.exp_pos _).le, 0, fun n ↦ ?_⟩
  rw [wt, pow_zero, mul_one, abs_inv, abs_of_pos (a_pos n t)]
  by_cases h : bump (((n : ℝ) + 1) * t) = 0
  · rw [a, h, mul_zero, sub_zero, inv_one]
    exact Real.one_le_exp (by positivity)
  · have hd : |((n : ℝ) + 1) * t - 1| < 1 / 2 := by
      by_contra! h'
      exact h (bump_eq_zero h')
    rw [abs_lt] at hd
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht : 0 < t := by
      by_contra! ht
      nlinarith
    rw [abs_of_pos ht]
    calc (a n t)⁻¹ ≤ (Real.exp (-((n : ℝ) + 1)))⁻¹ :=
          inv_anti₀ (Real.exp_pos _) (exp_neg_le_a n t)
      _ = Real.exp ((n : ℝ) + 1) := by rw [Real.exp_neg, inv_inv]
      _ ≤ Real.exp (3 / (2 * t)) := by
          gcongr
          rw [le_div_iff₀ (by positivity)]
          nlinarith

/-- **The operators `L t x = (aₙ(t) xₙ)ₙ`**, continuous linear automorphisms of `s`. -/
def L (t : ℝ) : RapidDecay ≃L[ℝ] RapidDecay :=
  ContinuousLinearEquiv.equivOfInverse (mulCLM _ (polyBdd_a t)) (mulCLM _ (polyBdd_inv_a t))
    (fun x ↦ ext fun n ↦ by
      simp only [mulCLM_apply]
      rw [← mul_assoc, inv_mul_cancel₀ (a_pos n t).ne', one_mul])
    (fun x ↦ ext fun n ↦ by
      simp only [mulCLM_apply]
      rw [← mul_assoc, mul_inv_cancel₀ (a_pos n t).ne', one_mul])

/-- The terms of `L t x`. -/
@[simp] theorem L_apply (t : ℝ) (x : RapidDecay) (n : ℕ) : L t x n = a n t * x n :=
  mulCLM_apply (polyBdd_a t) x n

/-- `L 0` is the identity. -/
theorem L_zero : L 0 = ContinuousLinearEquiv.refl ℝ RapidDecay :=
  ContinuousLinearEquiv.ext (funext fun x ↦ ext fun n ↦ by simp [a_zero])

/-- **Smoothness**: `(t, x) ↦ L t x` is smooth in the sense of Michal–Bastiani on `ℝ × s`. -/
theorem smoothMBOn_L : SmoothMBOn (fun p : ℝ × RapidDecay ↦ L p.1 p.2) univ := by
  have e : (fun p : ℝ × RapidDecay ↦ L p.1 p.2) = fam (Dfam 0) := by
    funext p
    ext n
    rw [L_apply, fam_apply admissible_Dfam, Dfam_zero]
  rw [e]
  exact fun k ↦ contDiffMBOn_fam k admissible_Dfam

/-- The unit vector `eₘ`. -/
def unit (m : ℕ) : RapidDecay :=
  mk (fun n ↦ if n = m then 1 else 0) fun k ↦ ⟨wt k m, fun n ↦ by
    split_ifs with h
    · simp [h]
    · simpa [h] using (wt_pos k m).le⟩

/-- The terms of `eₘ`. -/
theorem unit_apply (m n : ℕ) : unit m n = if n = m then 1 else 0 := rfl

/-- `p₀(eₘ) ≥ 1`. -/
theorem one_le_seminorm_unit (m : ℕ) : 1 ≤ seminorm 0 (unit m) := by
  simpa [unit, wt] using le_seminorm 0 (unit m) m

/-- `L(1/(m + 1)) eₘ = e^{-(m+1)} eₘ`, so `p_K(L(1/(m + 1)) eₘ) ≤ (m + 1)^K e^{-(m+1)}`. -/
theorem seminorm_L_unit_le (K m : ℕ) :
    seminorm K (L (1 / ((m : ℝ) + 1)) (unit m)) ≤ wt K m * Real.exp (-((m : ℝ) + 1)) := by
  refine seminorm_le (by positivity) fun n ↦ ?_
  rw [L_apply]
  by_cases h : n = m
  · subst h
    have : a n (1 / ((n : ℝ) + 1)) = Real.exp (-((n : ℝ) + 1)) := by
      rw [a, mul_one_div_cancel (by positivity), bump_one, cf]
      ring
    rw [this, unit_apply]
    simp only [↓reduceIte, mul_one, abs_of_pos (Real.exp_pos _), le_refl]
  · rw [unit_apply]
    simp only [h, ↓reduceIte, mul_zero, abs_zero]
    positivity

/-- The seminorm `p₀` is not controlled by any continuous seminorm on the family `L t`, `t` near
`0`. -/
theorem exists_lt_seminorm_zero (q : Seminorm ℝ RapidDecay) (hq : Continuous q) (C δ : ℝ)
    (hδ : 0 < δ) : ∃ t, |t| < δ ∧ ∃ v, C * q (L t v) < seminorm 0 v := by
  obtain ⟨S, C', -, hqS⟩ := Seminorm.bound_of_continuous withSeminorms q hq
  set K := S.sup id
  have hqK : ∀ y, q y ≤ C' * seminorm K y := fun y ↦ by
    refine (hqS y).trans ?_
    rw [_root_.smul_apply, NNReal.smul_def, smul_eq_mul]
    gcongr
    exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi ↦
      seminorm_mono (Finset.le_sup (f := id) hi) y
  -- `(m + 1)^K e^{-(m+1)} → 0` and `1 / (m + 1) → 0`
  have h1 : Tendsto (fun m : ℕ ↦ wt K m * Real.exp (-((m : ℝ) + 1))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hM : 0 < |C| * C' + 1 := by positivity
  obtain ⟨m, hm1, hm2⟩ := ((h1.eventually (gt_mem_nhds (inv_pos.mpr hM))).and
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hδ))).exists
  refine ⟨1 / ((m : ℝ) + 1), by rwa [abs_of_pos (by positivity)], unit m, ?_⟩
  calc C * q (L (1 / ((m : ℝ) + 1)) (unit m)) ≤ |C| * q (L (1 / ((m : ℝ) + 1)) (unit m)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (apply_nonneg _ _)
    _ ≤ |C| * (C' * (wt K m * Real.exp (-((m : ℝ) + 1)))) := by
        gcongr
        exact (hqK _).trans (by gcongr; exact seminorm_L_unit_le K m)
    _ = (|C| * C') * (wt K m * Real.exp (-((m : ℝ) + 1))) := by ring
    _ ≤ (|C| * C' + 1) * (wt K m * Real.exp (-((m : ℝ) + 1))) := by gcongr; linarith
    _ < (|C| * C' + 1) * (|C| * C' + 1)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hM.ne'
    _ ≤ seminorm 0 (unit m) := one_le_seminorm_unit m

/-- **The lower bound is not locally uniform in `s`.** There is a continuous seminorm `p` such
that no continuous seminorm `q` controls `p` on the family `L t`, `t` near `0`: for all `C` and
`δ > 0` there are `|t| < δ` and `v` with `C q (L t v) < p v`. -/
theorem not_uniform_boundedBelow :
    ∃ p : Seminorm ℝ RapidDecay, Continuous p ∧ ∀ q : Seminorm ℝ RapidDecay, Continuous q →
      ∀ C δ : ℝ, 0 < δ → ∃ t, |t| < δ ∧ ∃ v, C * q (L t v) < p v :=
  ⟨seminorm 0, withSeminorms.continuous_seminorm 0, exists_lt_seminorm_zero⟩

/-- **The inverses are not equicontinuous near `0`**: for no `δ > 0` is the family
`(L t)⁻¹`, `|t| < δ`, equicontinuous. -/
theorem not_equicontinuousAt_L_symm {δ : ℝ} (hδ : 0 < δ) :
    ¬ EquicontinuousAt (fun t : Ioo (-δ) δ ↦ ⇑(L t).symm) 0 := by
  intro h
  have hT := (withSeminorms.equicontinuous_TFAE
    (fun t : Ioo (-δ) δ ↦ ((L t).symm : RapidDecay →L[ℝ] RapidDecay).toLinearMap)).out 1 4
  obtain ⟨P, hPc, hP⟩ := hT.mp h 0
  obtain ⟨t, ht, v, hv⟩ := exists_lt_seminorm_zero P hPc 1 δ hδ
  have h1 := hP ⟨t, abs_lt.mp ht⟩ (L t v)
  have h2 : seminorm 0 ((L t).symm (L t v)) ≤ P (L t v) := h1
  rw [ContinuousLinearEquiv.symm_apply_apply] at h2
  linarith


/-- Every `L t` is a topological embedding (indeed an isomorphism). -/
theorem isEmbedding_L (t : ℝ) : Topology.IsEmbedding (L t) :=
  (L t).toHomeomorph.isEmbedding

/-- **The counterexample.** On the Fréchet space `s`, the family `L t` is smooth in the sense of
Michal–Bastiani, `L 0 = id`, and every `L t` is an isomorphism (in particular an embedding); but
the lower bound is not locally uniform: it is false that for every continuous seminorm `p` there
are a continuous seminorm `q` and `C, δ > 0` with `p v ≤ C q (L t v)` for all `|t| < δ` and all
`v`. Compare `exists_uniform_boundedBelow`. -/
theorem counterexample :
    SmoothMBOn (fun p : ℝ × RapidDecay ↦ L p.1 p.2) univ ∧
      L 0 = ContinuousLinearEquiv.refl ℝ RapidDecay ∧ (∀ t, Topology.IsEmbedding (L t)) ∧
      ¬ ∀ p : Seminorm ℝ RapidDecay, Continuous p → ∃ q : Seminorm ℝ RapidDecay, Continuous q ∧
        ∃ C δ : ℝ, 0 < δ ∧ ∀ t, |t| < δ → ∀ v, p v ≤ C * q (L t v) := by
  refine ⟨smoothMBOn_L, L_zero, isEmbedding_L, fun h ↦ ?_⟩
  obtain ⟨q, hq, C, δ, hδ, hbd⟩ := h (seminorm 0) (withSeminorms.continuous_seminorm 0)
  obtain ⟨t, ht, v, hv⟩ := exists_lt_seminorm_zero q hq C δ hδ
  exact (hbd t ht v).not_gt hv

end RapidDecay

end LocallyConvex.Analysis.Counterexamples

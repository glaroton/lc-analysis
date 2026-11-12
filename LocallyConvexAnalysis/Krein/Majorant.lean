/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Krein.OrthoComplemented
public import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Decomposition majorants of Krein spaces

Reference: J. Bognár, *Indefinite Inner Product Spaces*, Springer (1974), Chapter IV, §1 (p. 77,
majorants), §6 (pp. 90–93, decomposition majorants: Theorems 6.1, 6.2, 6.4, Corollary 6.3) and
§7 (pp. 93–95, Theorem 7.2), and §V.1 (p. 100, Krein spaces).

Let `B` be a Hermitian form on a vector space `E` and `E = E₊ ⊕ E₋` a fundamental decomposition
(`AlgFundamentalDecomposition B ⊤`), with projections `P₊`, `P₋` and fundamental symmetry
`J = P₊ - P₋`. The **`J`-inner product** `[x, y]_J = B(J x, y) = B(P₊ x, P₊ y) - B(P₋ x, P₋ y)`
is positive definite (`AlgFundamentalDecomposition.jInner`), and its norm `‖x‖_J` defines the
**decomposition majorant** of the decomposition ([Bog74, §IV.5–6]).

## Main results

For a Krein space `(E, B)` in Bognár's algebraic sense (`KreinDecomposition`: a fundamental
decomposition with intrinsically complete components, no topology given):

* `KreinDecomposition.completeSpace`: the space `JSpace` of its decomposition majorant is a
  Hilbert space, on which `B(x, y) = [J₀ x, y]` (`KreinDecomposition.gram_inner`).
* `KreinDecomposition.exists_jInner_bounds`: **all decomposition majorants coincide**
  ([Bog74, Theorem 6.4 and Corollary 6.3]): every fundamental decomposition `D` of `(E, B)` has a
  `J`-norm equivalent to that of `K`. So the **majorant topology** of a Krein space is well defined.
* `KreinDecomposition.ofAlg`: **every fundamental decomposition of a Krein space is a Krein
  decomposition** ([Bog74, Theorem 7.2]).

On a Hilbert space `H` with `B(x, y) = ⟪G x, y⟫` for an invertible self-adjoint Gram operator `G`:

* `AlgFundamentalDecomposition.exists_jInner_bounds`: every fundamental decomposition has its
  `J`-norm equivalent to the norm of `H`: `c ‖x‖² ≤ [x, x]_J ≤ C ‖x‖²`. Its components are
  closed (`isClosed_pos_of_gram`, `isClosed_neg_of_gram`) and its fundamental symmetry is
  continuous (`continuous_sym`); it is a Krein decomposition (`toKreinDecomposition`).

## Method

Bognár proves Theorem 6.4 for a Hilbert majorant by an iteration (`‖T x‖_J ≤ ‖T‖ ‖x‖_J` for the
`J`-symmetric `T = J₁ J₂`). For Krein spaces (`G` invertible) we argue instead with
`U = G J`, which is continuous (the components `E_± = E_∓^[⊥]` are closed, and the closed graph
theorem applies), self-adjoint, positive (`⟪U x, x⟫ = [x, x]_J`) and invertible, hence bounded
below as a quadratic form: `‖U x‖² ≤ ‖U‖ ⟪U x, x⟫` by the Cauchy–Schwarz inequality for the
positive form `⟪U ·, ·⟫`. We do not claim this argument is new.

## References

* [J. Bognár, *Indefinite Inner Product Spaces*][Bog74]
-/

@[expose] public section

open Filter RCLike
open scoped Topology InnerProductSpace ComplexConjugate

noncomputable section

namespace LocallyConvex.Analysis

/-! ### The `J`-inner product of a fundamental decomposition -/

namespace AlgFundamentalDecomposition

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} (D : AlgFundamentalDecomposition B ⊤)

theorem isCompl : IsCompl D.pos D.neg := ⟨D.disjoint, codisjoint_iff.2 D.sup_eq⟩

/-- The fundamental projection `P₊` onto `E₊` along `E₋`. -/
def projPos : E →ₗ[𝕜] E := D.pos.projection D.neg D.isCompl

/-- The fundamental projection `P₋` onto `E₋` along `E₊`. -/
def projNeg : E →ₗ[𝕜] E := D.neg.projection D.pos D.isCompl.symm

/-- The fundamental symmetry `J = P₊ - P₋`. -/
def sym : E →ₗ[𝕜] E := D.projPos - D.projNeg

theorem projPos_mem (x : E) : D.projPos x ∈ D.pos := Submodule.projection_apply_mem _ _

theorem projNeg_mem (x : E) : D.projNeg x ∈ D.neg := Submodule.projection_apply_mem _ _

theorem projPos_add_projNeg (x : E) : D.projPos x + D.projNeg x = x :=
  Submodule.projection_add_projection_eq_self D.isCompl x

theorem projPos_of_mem_pos {x : E} (hx : x ∈ D.pos) : D.projPos x = x :=
  Submodule.projection_apply_of_mem_left _ hx

theorem projNeg_of_mem_pos {x : E} (hx : x ∈ D.pos) : D.projNeg x = 0 :=
  Submodule.projection_apply_of_mem_right _ hx

theorem projPos_of_mem_neg {x : E} (hx : x ∈ D.neg) : D.projPos x = 0 :=
  Submodule.projection_apply_of_mem_right _ hx

theorem projNeg_of_mem_neg {x : E} (hx : x ∈ D.neg) : D.projNeg x = x :=
  Submodule.projection_apply_of_mem_left _ hx

theorem sym_apply (x : E) : D.sym x = D.projPos x - D.projNeg x := rfl

theorem sym_sym (x : E) : D.sym (D.sym x) = x := by
  simp only [sym_apply, map_sub, projPos_of_mem_pos _ (D.projPos_mem x),
    projNeg_of_mem_pos _ (D.projPos_mem x), projPos_of_mem_neg _ (D.projNeg_mem x),
    projNeg_of_mem_neg _ (D.projNeg_mem x)]
  rw [sub_zero, zero_sub, sub_neg_eq_add, projPos_add_projNeg]

/-- The `J`-inner product `[x, y]_J = B(J x, y)`. -/
def jInner (x y : E) : 𝕜 := B (D.sym x) y

variable (hB : ∀ x y, conj (B y x) = B x y)

include hB in
theorem B_neg_pos {x y : E} (hx : x ∈ D.neg) (hy : y ∈ D.pos) : B x y = 0 := by
  rw [← hB, D.orth y hy x hx, map_zero]

include hB in
/-- `[x, y]_J = B(P₊ x, P₊ y) - B(P₋ x, P₋ y)`. -/
theorem jInner_eq (x y : E) :
    D.jInner x y = B (D.projPos x) (D.projPos y) - B (D.projNeg x) (D.projNeg y) := by
  have hy : y = D.projPos y + D.projNeg y := (D.projPos_add_projNeg y).symm
  conv_lhs => rw [jInner, hy]
  rw [sym_apply, map_sub, LinearMap.sub_apply, map_add, map_add,
    D.orth _ (D.projPos_mem x) _ (D.projNeg_mem y),
    D.B_neg_pos hB (D.projNeg_mem x) (D.projPos_mem y)]
  ring

include hB in
theorem conj_jInner (x y : E) : conj (D.jInner y x) = D.jInner x y := by
  rw [D.jInner_eq hB, D.jInner_eq hB, map_sub, hB, hB]

theorem re_B_nonneg_pos {x : E} (hx : x ∈ D.pos) : 0 ≤ re (B x x) := by
  by_cases h : x = 0
  · simp [h]
  · exact (D.pos_def x hx h).le

theorem re_B_nonpos_neg {x : E} (hx : x ∈ D.neg) : re (B x x) ≤ 0 := by
  by_cases h : x = 0
  · simp [h]
  · exact (D.neg_def x hx h).le

include hB in
theorem re_jInner_self_nonneg (x : E) : 0 ≤ re (D.jInner x x) := by
  rw [D.jInner_eq hB, map_sub]
  linarith [D.re_B_nonneg_pos (D.projPos_mem x), D.re_B_nonpos_neg (D.projNeg_mem x)]

include hB in
theorem eq_zero_of_re_jInner_self {x : E} (h : re (D.jInner x x) = 0) : x = 0 := by
  rw [D.jInner_eq hB, map_sub] at h
  have h1 := D.re_B_nonneg_pos (D.projPos_mem x)
  have h2 := D.re_B_nonpos_neg (D.projNeg_mem x)
  have hp : D.projPos x = 0 := by
    by_contra hne
    have := D.pos_def _ (D.projPos_mem x) hne
    linarith
  have hn : D.projNeg x = 0 := by
    by_contra hne
    have := D.neg_def _ (D.projNeg_mem x) hne
    linarith
  rw [← D.projPos_add_projNeg x, hp, hn, add_zero]

include hB in
theorem jInner_of_mem_pos {x y : E} (hx : x ∈ D.pos) (hy : y ∈ D.pos) :
    D.jInner x y = B x y := by
  rw [D.jInner_eq hB, D.projPos_of_mem_pos hx, D.projPos_of_mem_pos hy, D.projNeg_of_mem_pos hx]
  simp

include hB in
theorem jInner_of_mem_neg {x y : E} (hx : x ∈ D.neg) (hy : y ∈ D.neg) :
    D.jInner x y = -B x y := by
  rw [D.jInner_eq hB, D.projPos_of_mem_neg hx, D.projNeg_of_mem_neg hx, D.projNeg_of_mem_neg hy]
  simp

/-- The `J`-inner product as a pre-inner product structure (positive semidefinite Hermitian). -/
@[instance_reducible]
def jCore : PreInnerProductSpace.Core 𝕜 E where
  inner := D.jInner
  conj_inner_symm x y := D.conj_jInner hB x y
  re_inner_nonneg x := D.re_jInner_self_nonneg hB x
  add_left x y z := by simp only [jInner, map_add, LinearMap.add_apply]
  smul_left x y r := by
    simp only [jInner, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

include hB in
/-- **The Cauchy–Schwarz inequality** for the `J`-inner product. -/
theorem norm_jInner_sq_le (x y : E) :
    ‖D.jInner x y‖ ^ 2 ≤ re (D.jInner x x) * re (D.jInner y y) := by
  let _ := D.jCore hB
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := 𝕜) x y
  have hs : ‖D.jInner y x‖ = ‖D.jInner x y‖ := by rw [← D.conj_jInner hB, RCLike.norm_conj]
  change ‖D.jInner x y‖ * ‖D.jInner y x‖ ≤ re (D.jInner x x) * re (D.jInner y y) at h
  rw [hs] at h
  nlinarith [h]

end AlgFundamentalDecomposition

/-! ### Krein spaces with a Hilbert topology -/

section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The form `⟪G x, y⟫` of an operator `G` (its **Gram operator**). -/
def gramForm (G : H →L[𝕜] H) : H →ₗ⋆[𝕜] H →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜).comp G.toLinearMap

omit [CompleteSpace H] in
@[simp] theorem gramForm_apply (G : H →L[𝕜] H) (x y : H) : gramForm G x y = ⟪G x, y⟫_𝕜 := rfl

theorem conj_gramForm {G : H →L[𝕜] H} (hG : IsSelfAdjoint G) (x y : H) :
    conj (gramForm G y x) = gramForm G x y := by
  simp only [gramForm_apply, inner_conj_symm]
  rw [← ContinuousLinearMap.adjoint_inner_left, hG.adjoint_eq]

namespace AlgFundamentalDecomposition

variable {G : H →L[𝕜] H} (D : AlgFundamentalDecomposition (gramForm G) ⊤)

omit [CompleteSpace H] in
/-- `E₊ = E₋^[⊥]` is closed ([Bog74, Corollary III.2.6]). -/
theorem isClosed_pos_of_gram : IsClosed (D.pos : Set H) := by
  have h : (D.pos : Set H) = ⋂ y ∈ D.neg, {x | ⟪G x, y⟫_𝕜 = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    refine ⟨fun hx y hy ↦ D.orth x hx y hy, fun h ↦ ?_⟩
    have hb : gramForm G (D.projNeg x) (D.projNeg x) = 0 := by
      have e := D.projPos_add_projNeg x
      have h1 := h _ (D.projNeg_mem x)
      have h2 : gramForm G (D.projPos x) (D.projNeg x) = 0 :=
        D.orth _ (D.projPos_mem x) _ (D.projNeg_mem x)
      have hs : gramForm G (D.projPos x + D.projNeg x) (D.projNeg x) =
          gramForm G (D.projPos x) (D.projNeg x) + gramForm G (D.projNeg x) (D.projNeg x) := by
        rw [map_add, LinearMap.add_apply]
      rw [e, gramForm_apply, h1, h2, zero_add] at hs
      exact hs.symm
    have hn : D.projNeg x = 0 := by
      by_contra hne
      have := D.neg_def _ (D.projNeg_mem x) hne
      rw [hb, map_zero] at this
      exact lt_irrefl _ this
    rw [← D.projPos_add_projNeg x, hn, add_zero]
    exact D.projPos_mem x
  rw [h]
  exact isClosed_biInter fun y _ ↦
    isClosed_eq ((continuous_inner.comp (G.continuous.prodMk continuous_const))) continuous_const

theorem isClosed_neg_of_gram (hG : IsSelfAdjoint G) : IsClosed (D.neg : Set H) := by
  have h : (D.neg : Set H) = ⋂ y ∈ D.pos, {x | ⟪G x, y⟫_𝕜 = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    refine ⟨fun hx y hy ↦ D.B_neg_pos (conj_gramForm hG) hx hy, fun h ↦ ?_⟩
    have ha : gramForm G (D.projPos x) (D.projPos x) = 0 := by
      have e := D.projPos_add_projNeg x
      have h1 := h _ (D.projPos_mem x)
      have h2 : gramForm G (D.projNeg x) (D.projPos x) = 0 :=
        D.B_neg_pos (conj_gramForm hG) (D.projNeg_mem x) (D.projPos_mem x)
      have hs : gramForm G (D.projPos x + D.projNeg x) (D.projPos x) =
          gramForm G (D.projPos x) (D.projPos x) + gramForm G (D.projNeg x) (D.projPos x) := by
        rw [map_add, LinearMap.add_apply]
      rw [e, gramForm_apply, h1, h2, add_zero] at hs
      exact hs.symm
    have hp : D.projPos x = 0 := by
      by_contra hne
      have := D.pos_def _ (D.projPos_mem x) hne
      rw [ha, map_zero] at this
      exact lt_irrefl _ this
    rw [← D.projPos_add_projNeg x, hp, zero_add]
    exact D.projNeg_mem x
  rw [h]
  exact isClosed_biInter fun y _ ↦
    isClosed_eq ((continuous_inner.comp (G.continuous.prodMk continuous_const))) continuous_const

/-- The fundamental symmetry of a fundamental decomposition is continuous (closed graph
theorem; [Bog74, proof of Theorem 6.4]). -/
theorem continuous_sym (hG : IsSelfAdjoint G) : Continuous D.sym := by
  have h1 := (Submodule.IsCompl.isTopCompl_of_isClosed D.isCompl D.isClosed_pos_of_gram
    (D.isClosed_neg_of_gram hG)).continuous_projection
  have h2 := (Submodule.IsCompl.isTopCompl_of_isClosed D.isCompl.symm (D.isClosed_neg_of_gram hG)
    D.isClosed_pos_of_gram).continuous_projection
  exact h1.sub h2

/-- The fundamental symmetry, as a continuous linear map. -/
def symL (hG : IsSelfAdjoint G) : H →L[𝕜] H := ⟨D.sym, D.continuous_sym hG⟩

@[simp] theorem symL_apply (hG : IsSelfAdjoint G) (x : H) : D.symL hG x = D.sym x := rfl

/-- **The `J`-norm of any fundamental decomposition of a Krein space is equivalent to the norm**
([Bog74, Theorems 6.1] and 6.4, for an invertible Gram operator): there are `c, C > 0` with
`c ‖x‖² ≤ [x, x]_J ≤ C ‖x‖²`. -/
theorem exists_jInner_bounds (hG : IsSelfAdjoint G) (hGu : IsUnit G) :
    ∃ c > 0, ∃ C > 0, ∀ x, c * ‖x‖ ^ 2 ≤ re (D.jInner x x) ∧ re (D.jInner x x) ≤ C * ‖x‖ ^ 2 := by
  have hB := conj_gramForm hG
  set U : H →L[𝕜] H := G * D.symL hG
  have hU : ∀ x y, ⟪U x, y⟫_𝕜 = D.jInner x y := fun x y ↦ rfl
  have hJ : D.symL hG * D.symL hG = 1 := ContinuousLinearMap.ext fun x ↦ D.sym_sym x
  have hUu : IsUnit U := hGu.mul ⟨⟨_, _, hJ, hJ⟩, rfl⟩
  set V : H →L[𝕜] H := ↑hUu.unit⁻¹
  have hVU : ∀ x, V (U x) = x := fun x ↦ by
    change (↑hUu.unit⁻¹ * ↑hUu.unit : H →L[𝕜] H) x = x
    rw [Units.inv_mul]
    rfl
  -- upper bound
  have hup : ∀ x, re (D.jInner x x) ≤ ‖U‖ * ‖x‖ ^ 2 := fun x ↦ by
    rw [← hU]
    calc re ⟪U x, x⟫_𝕜 ≤ ‖⟪U x, x⟫_𝕜‖ := re_le_norm _
      _ ≤ ‖U x‖ * ‖x‖ := norm_inner_le_norm _ _
      _ ≤ ‖U‖ * ‖x‖ * ‖x‖ := by gcongr; exact U.le_opNorm x
      _ = ‖U‖ * ‖x‖ ^ 2 := by ring
  -- `‖U x‖² ≤ ‖U‖ ⟪U x, x⟫`
  have hUx : ∀ x, ‖U x‖ ^ 2 ≤ ‖U‖ * re (D.jInner x x) := fun x ↦ by
    have hcs := D.norm_jInner_sq_le hB x (U x)
    have h1 : D.jInner x (U x) = ⟪U x, U x⟫_𝕜 := (hU x (U x)).symm
    rw [h1, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hcs
    have h2 := hup (U x)
    have hn := D.re_jInner_self_nonneg hB x
    rcases eq_or_lt_of_le (sq_nonneg ‖U x‖) with h0 | hpos
    · rw [← h0]
      positivity
    · have : (‖U x‖ ^ 2) ^ 2 ≤ re (D.jInner x x) * (‖U‖ * ‖U x‖ ^ 2) :=
        hcs.trans (mul_le_mul_of_nonneg_left h2 hn)
      nlinarith
  refine ⟨1 / ((‖V‖ ^ 2 + 1) * (‖U‖ + 1)), by positivity, ‖U‖ + 1, by positivity,
    fun x ↦ ⟨?_, (hup x).trans (by gcongr; linarith)⟩⟩
  have hn := D.re_jInner_self_nonneg hB x
  have hx : ‖x‖ ≤ ‖V‖ * ‖U x‖ := by
    calc ‖x‖ = ‖V (U x)‖ := by rw [hVU]
      _ ≤ ‖V‖ * ‖U x‖ := V.le_opNorm _
  have hx2 : ‖x‖ ^ 2 ≤ (‖V‖ ^ 2 + 1) * ‖U x‖ ^ 2 := by
    calc ‖x‖ ^ 2 ≤ (‖V‖ * ‖U x‖) ^ 2 := by gcongr
      _ = ‖V‖ ^ 2 * ‖U x‖ ^ 2 := by ring
      _ ≤ (‖V‖ ^ 2 + 1) * ‖U x‖ ^ 2 := by nlinarith [sq_nonneg ‖U x‖]
  have hUx' : ‖U x‖ ^ 2 ≤ (‖U‖ + 1) * re (D.jInner x x) := (hUx x).trans (by nlinarith)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  calc ‖x‖ ^ 2 ≤ (‖V‖ ^ 2 + 1) * ‖U x‖ ^ 2 := hx2
    _ ≤ (‖V‖ ^ 2 + 1) * ((‖U‖ + 1) * re (D.jInner x x)) := by gcongr
    _ = re (D.jInner x x) * ((‖V‖ ^ 2 + 1) * (‖U‖ + 1)) := by ring

/-- **All decomposition majorants of a Krein space coincide**
([Bog74, Theorem 6.4 and Corollary 6.3]): the `J`-norms of two fundamental decompositions are
equivalent. -/
theorem exists_jInner_le (hG : IsSelfAdjoint G) (hGu : IsUnit G)
    (D' : AlgFundamentalDecomposition (gramForm G) ⊤) :
    ∃ C > 0, ∀ x, re (D'.jInner x x) ≤ C * re (D.jInner x x) := by
  obtain ⟨c, hc, C, hC, h⟩ := D.exists_jInner_bounds hG hGu
  obtain ⟨c', hc', C', hC', h'⟩ := D'.exists_jInner_bounds hG hGu
  refine ⟨C' / c, by positivity, fun x ↦ ?_⟩
  calc re (D'.jInner x x) ≤ C' * ‖x‖ ^ 2 := (h' x).2
    _ = C' / c * (c * ‖x‖ ^ 2) := by field_simp
    _ ≤ C' / c * re (D.jInner x x) := by gcongr; exact (h x).1

/-- The components of a fundamental decomposition of a Krein space are complete for their
intrinsic norms. -/
theorem intrinsicallyComplete_pos (hG : IsSelfAdjoint G) (hGu : IsUnit G) :
    IntrinsicallyComplete (gramForm G) D.pos := by
  have hB := conj_gramForm hG
  obtain ⟨c, hc, C, hC, h⟩ := D.exists_jInner_bounds hG hGu
  have hj : ∀ v ∈ D.pos, re (gramForm G v v) = re (D.jInner v v) := fun v hv ↦ by
    rw [D.jInner_of_mem_pos hB hv hv]
  intro u hu hcau
  have hcau' : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (c * ε ^ 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hmem : u n - u N ∈ D.pos := D.pos.sub_mem (hu n) (hu N)
    have h1 := hN n hn N le_rfl
    rw [hj _ hmem] at h1
    have h2 := (h (u n - u N)).1
    rw [dist_eq_norm]
    have h3 : ‖u n - u N‖ ^ 2 < ε ^ 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau'
  have hxmem : x ∈ D.pos := D.isClosed_pos_of_gram.mem_of_tendsto hx (Eventually.of_forall hu)
  refine ⟨x, hxmem, ?_⟩
  have ht : Tendsto (fun n ↦ C * ‖u n - x‖ ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hx).pow 2).const_mul C
    simpa using this
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) ht
  · rw [hj _ (D.pos.sub_mem (hu n) hxmem)]
    exact D.re_jInner_self_nonneg hB _
  · rw [hj _ (D.pos.sub_mem (hu n) hxmem)]
    exact (h _).2

theorem intrinsicallyComplete_neg (hG : IsSelfAdjoint G) (hGu : IsUnit G) :
    IntrinsicallyComplete (-gramForm G) D.neg := by
  have hB := conj_gramForm hG
  obtain ⟨c, hc, C, hC, h⟩ := D.exists_jInner_bounds hG hGu
  have hj : ∀ v ∈ D.neg, re ((-gramForm G) v v) = re (D.jInner v v) := fun v hv ↦ by
    rw [D.jInner_of_mem_neg hB hv hv]
    simp
  intro u hu hcau
  have hcau' : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (c * ε ^ 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hmem : u n - u N ∈ D.neg := D.neg.sub_mem (hu n) (hu N)
    have h1 := hN n hn N le_rfl
    rw [hj _ hmem] at h1
    have h2 := (h (u n - u N)).1
    rw [dist_eq_norm]
    have h3 : ‖u n - u N‖ ^ 2 < ε ^ 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau'
  have hxmem : x ∈ D.neg := (D.isClosed_neg_of_gram hG).mem_of_tendsto hx (Eventually.of_forall hu)
  refine ⟨x, hxmem, ?_⟩
  have ht : Tendsto (fun n ↦ C * ‖u n - x‖ ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hx).pow 2).const_mul C
    simpa using this
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) ht
  · rw [hj _ (D.neg.sub_mem (hu n) hxmem)]
    exact D.re_jInner_self_nonneg hB _
  · rw [hj _ (D.neg.sub_mem (hu n) hxmem)]
    exact (h _).2

/-- **Every fundamental decomposition of a Krein space is a Krein decomposition**
([Bog74, Theorem 7.2]): its components are intrinsically complete. -/
def toKreinDecomposition (hG : IsSelfAdjoint G) (hGu : IsUnit G) :
    KreinDecomposition (gramForm G) ⊤ where
  toAlgFundamentalDecomposition := D
  pos_complete := D.intrinsicallyComplete_pos hG hGu
  neg_complete := D.intrinsicallyComplete_neg hG hGu

end AlgFundamentalDecomposition

end Hilbert

/-! ### Algebraic Krein spaces -/

section Algebraic

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜}

namespace AlgFundamentalDecomposition

set_option linter.unusedVariables false in
/-- `E` with the `J`-inner product of a fundamental decomposition: a pre-Hilbert space, the
space of the decomposition majorant ([Bog74, §IV.5]). A type synonym of `E`. -/
@[nolint unusedArguments]
def JSpace (D : AlgFundamentalDecomposition B ⊤) (_hB : ∀ x y, conj (B y x) = B x y) :
    Type _ := E

namespace JSpace

variable {D : AlgFundamentalDecomposition B ⊤} {hB : ∀ x y, conj (B y x) = B x y}

instance : AddCommGroup (JSpace D hB) := inferInstanceAs (AddCommGroup E)

instance : Module 𝕜 (JSpace D hB) := inferInstanceAs (Module 𝕜 E)

/-- The `J`-inner product as an inner product. -/
@[instance_reducible]
def core : InnerProductSpace.Core 𝕜 (JSpace D hB) where
  inner x y := D.jInner (show E from x) (show E from y)
  conj_inner_symm x y := D.conj_jInner hB _ _
  re_inner_nonneg x := D.re_jInner_self_nonneg hB _
  add_left x y z := (D.jCore hB).add_left (show E from x) (show E from y) (show E from z)
  smul_left x y r := (D.jCore hB).smul_left (show E from x) (show E from y) r
  definite x hx := D.eq_zero_of_re_jInner_self hB (by
    rw [show D.jInner (show E from x) (show E from x) = 0 from hx, map_zero])

instance : NormedAddCommGroup (JSpace D hB) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 _ _ _ _ core

instance : InnerProductSpace 𝕜 (JSpace D hB) :=
  InnerProductSpace.ofCore (core (D := D) (hB := hB)).toCore

theorem inner_eq (x y : JSpace D hB) :
    ⟪x, y⟫_𝕜 = D.jInner (show E from x) (show E from y) := rfl

theorem norm_sq_eq (x : JSpace D hB) : ‖x‖ ^ 2 = re (D.jInner (show E from x) (show E from x)) := by
  rw [@norm_sq_eq_re_inner 𝕜]
  rfl

end JSpace

end AlgFundamentalDecomposition

namespace KreinDecomposition

variable (K : KreinDecomposition B ⊤) (hB : ∀ x y, conj (B y x) = B x y)

include hB in
theorem re_B_projPos_le (v : E) :
    re (B (K.projPos v) (K.projPos v)) ≤ re (K.jInner v v) := by
  rw [K.jInner_eq hB, map_sub]
  linarith [K.re_B_nonpos_neg (K.projNeg_mem v)]

include hB in
theorem re_negB_projNeg_le (v : E) :
    re ((-B) (K.projNeg v) (K.projNeg v)) ≤ re (K.jInner v v) := by
  rw [K.jInner_eq hB, map_sub]
  simp only [LinearMap.neg_apply, map_neg]
  linarith [K.re_B_nonneg_pos (K.projPos_mem v)]

/-- **The space of the decomposition majorant of a Krein decomposition is a Hilbert space.** -/
theorem completeSpace : CompleteSpace (K.JSpace hB) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  let v : ℕ → E := fun n ↦ show E from u n
  have hdist : ∀ m n, re (K.jInner (v m - v n) (v m - v n)) = dist (u m) (u n) ^ 2 := by
    intro m n
    rw [dist_eq_norm, AlgFundamentalDecomposition.JSpace.norm_sq_eq]
    rfl
  have hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, re (K.jInner (v m - v n) (v m - v n)) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (√ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [hdist]
    have h := hN m hm n hn
    calc dist (u m) (u n) ^ 2 < √ε ^ 2 := by gcongr
      _ = ε := Real.sq_sqrt hε.le
  obtain ⟨a, ha, hta⟩ := K.pos_complete (fun n ↦ K.projPos (v n)) (fun n ↦ K.projPos_mem _)
    fun ε hε ↦ by
      obtain ⟨N, hN⟩ := hcau ε hε
      exact ⟨N, fun m hm n hn ↦ by
        rw [← map_sub]
        exact (K.re_B_projPos_le hB _).trans_lt (hN m hm n hn)⟩
  obtain ⟨b, hb, htb⟩ := K.neg_complete (fun n ↦ K.projNeg (v n)) (fun n ↦ K.projNeg_mem _)
    fun ε hε ↦ by
      obtain ⟨N, hN⟩ := hcau ε hε
      exact ⟨N, fun m hm n hn ↦ by
        rw [← map_sub]
        exact (K.re_negB_projNeg_le hB _).trans_lt (hN m hm n hn)⟩
  refine ⟨show K.JSpace hB from a + b, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun n ↦ ‖u n - (show K.JSpace hB from a + b)‖ ^ 2) atTop (𝓝 0) := by
    have he : ∀ n, ‖u n - (show K.JSpace hB from a + b)‖ ^ 2 =
        re (B (K.projPos (v n) - a) (K.projPos (v n) - a)) +
          re ((-B) (K.projNeg (v n) - b) (K.projNeg (v n) - b)) := by
      intro n
      rw [AlgFundamentalDecomposition.JSpace.norm_sq_eq]
      change re (K.jInner (v n - (a + b)) (v n - (a + b))) = _
      have hp : K.projPos (v n - (a + b)) = K.projPos (v n) - a := by
        rw [map_sub, map_add, K.projPos_of_mem_pos ha, K.projPos_of_mem_neg hb, add_zero]
      have hn : K.projNeg (v n - (a + b)) = K.projNeg (v n) - b := by
        rw [map_sub, map_add, K.projNeg_of_mem_pos ha, K.projNeg_of_mem_neg hb, zero_add]
      rw [K.jInner_eq hB, hp, hn, map_sub]
      simp only [LinearMap.neg_apply, map_neg]
      ring
    simp_rw [he]
    simpa using hta.add htb
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

include hB in
theorem jInner_sym_sym (x y : E) : K.jInner (K.sym x) (K.sym y) = K.jInner x y := by
  have hp : ∀ z, K.projPos (K.sym z) = K.projPos z := fun z ↦ by
    rw [K.sym_apply, map_sub, K.projPos_of_mem_pos (K.projPos_mem z),
      K.projPos_of_mem_neg (K.projNeg_mem z), sub_zero]
  have hn : ∀ z, K.projNeg (K.sym z) = -K.projNeg z := fun z ↦ by
    rw [K.sym_apply, map_sub, K.projNeg_of_mem_pos (K.projPos_mem z),
      K.projNeg_of_mem_neg (K.projNeg_mem z), zero_sub]
  rw [K.jInner_eq hB, K.jInner_eq hB, hp, hp, hn, hn]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

instance : CompleteSpace (K.JSpace hB) := K.completeSpace hB

/-- The fundamental symmetry `J₀` of `K`, the Gram operator of `B` on the Hilbert space of the
decomposition majorant: `B(x, y) = [J₀ x, y]_{J₀}`. -/
def gram : K.JSpace hB →L[𝕜] K.JSpace hB :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ show K.JSpace hB from K.sym (show E from x)
      map_add' := fun x y ↦ map_add K.sym (show E from x) (show E from y)
      map_smul' := fun c x ↦ map_smul K.sym c (show E from x) } 1 fun x ↦ by
    rw [one_mul]
    refine le_of_eq ?_
    have h1 := AlgFundamentalDecomposition.JSpace.norm_sq_eq
      (D := K.toAlgFundamentalDecomposition) (hB := hB) (show K.JSpace hB from K.sym x)
    have h2 := AlgFundamentalDecomposition.JSpace.norm_sq_eq
      (D := K.toAlgFundamentalDecomposition) (hB := hB) x
    change ‖(show K.JSpace hB from K.sym x)‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), h1, h2]
    exact congrArg re (K.jInner_sym_sym hB _ _)

theorem gram_apply (x : K.JSpace hB) : K.gram hB x = (K.sym x : E) := by
  rw [gram, LinearMap.mkContinuous_apply]
  rfl

theorem gram_inner (x y : K.JSpace hB) : ⟪K.gram hB x, y⟫_𝕜 = B x y := by
  rw [AlgFundamentalDecomposition.JSpace.inner_eq, gram_apply]
  exact congrArg (fun z ↦ B z y) (K.sym_sym x)

theorem isSelfAdjoint_gram : IsSelfAdjoint (K.gram hB) := by
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y ↦ ?_
  change ⟪K.gram hB x, y⟫_𝕜 = ⟪x, K.gram hB y⟫_𝕜
  rw [← inner_conj_symm x, K.gram_inner, K.gram_inner]
  exact (hB x y).symm

theorem isUnit_gram : IsUnit (K.gram hB) := by
  have h : K.gram hB * K.gram hB = 1 := ContinuousLinearMap.ext fun x ↦ K.sym_sym _
  exact ⟨⟨_, _, h, h⟩, rfl⟩

/-- A fundamental decomposition of `(E, B)`, seen in the Hilbert space of `K`. -/
def transfer (D : AlgFundamentalDecomposition B ⊤) :
    AlgFundamentalDecomposition (gramForm (K.gram hB)) ⊤ where
  pos := D.pos
  neg := D.neg
  sup_eq := D.sup_eq
  disjoint := D.disjoint
  orth x hx y hy := by
    rw [gramForm_apply, K.gram_inner]
    exact D.orth x hx y hy
  pos_def x hx h0 := by
    rw [gramForm_apply, K.gram_inner]
    exact D.pos_def x hx h0
  neg_def x hx h0 := by
    rw [gramForm_apply, K.gram_inner]
    exact D.neg_def x hx h0

theorem transfer_jInner (D : AlgFundamentalDecomposition B ⊤) (x y : K.JSpace hB) :
    (K.transfer hB D).jInner x y = D.jInner (show E from x) (show E from y) := by
  change ⟪K.gram hB _, y⟫_𝕜 = _
  rw [K.gram_inner]
  rfl

include hB in
/-- **All decomposition majorants of a Krein space coincide**
([Bog74, Corollary 6.3 and Theorem 6.4]): if `K` is a Krein decomposition of `(E, B)`, every
fundamental decomposition `D` of `(E, B)` has a `J`-norm equivalent to that of `K`. -/
theorem exists_jInner_bounds (D : AlgFundamentalDecomposition B ⊤) :
    ∃ c > 0, ∃ C > 0, ∀ x, c * re (K.jInner x x) ≤ re (D.jInner x x) ∧
      re (D.jInner x x) ≤ C * re (K.jInner x x) := by
  obtain ⟨c, hc, C, hC, h⟩ :=
    (K.transfer hB D).exists_jInner_bounds (K.isSelfAdjoint_gram hB) (K.isUnit_gram hB)
  refine ⟨c, hc, C, hC, fun x ↦ ?_⟩
  have hx := h (show K.JSpace hB from x)
  rw [AlgFundamentalDecomposition.JSpace.norm_sq_eq, K.transfer_jInner] at hx
  exact hx

include hB in
/-- **Intrinsic completeness does not depend on the fundamental decomposition**
([Bog74, Theorem 7.2]): every fundamental decomposition of a Krein space is a Krein decomposition.
-/
def ofAlg (D : AlgFundamentalDecomposition B ⊤) : KreinDecomposition B ⊤ where
  toAlgFundamentalDecomposition := D
  pos_complete := by
    intro u hu hcau
    have h := ((K.transfer hB D).intrinsicallyComplete_pos (K.isSelfAdjoint_gram hB)
      (K.isUnit_gram hB)) u hu (by simp only [gramForm_apply, K.gram_inner]; exact hcau)
    simp only [gramForm_apply, K.gram_inner] at h
    exact h
  neg_complete := by
    intro u hu hcau
    have h := ((K.transfer hB D).intrinsicallyComplete_neg (K.isSelfAdjoint_gram hB)
      (K.isUnit_gram hB)) u hu (by
        simp only [LinearMap.neg_apply, gramForm_apply, K.gram_inner]; exact hcau)
    simp only [LinearMap.neg_apply, gramForm_apply, K.gram_inner] at h
    exact h

end KreinDecomposition

end Algebraic

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Krein.IntrinsicDimension
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Continuous families of Krein spaces

Let `G : X → L(H)` be a norm-continuous family of invertible self-adjoint operators on a real or
complex Hilbert space `H`, so that `(H, ⟪G(x) ·, ·⟫)` is a Krein space for every `x`.

## Main results

* `exists_continuous_spectral_projection`: the spectral projections `P(x)` of `G(x)` onto the
  positive part depend continuously on `x`; they give fundamental decompositions
  `H = ran P(x) ⊕ ker P(x)` chosen continuously in `x`, with `±⟪G(x) v, v⟫ ≥ c ‖v‖²` on the two
  components.
* `continuousLinearEquiv_ker_of_norm_sub_lt_one`: kernels of orthogonal projections at distance
  `< 1` are isomorphic topological vector spaces.
* `isLocallyConstant_index`: **the index is locally constant**: for any choice of fundamental
  decompositions `D(x)` of `(H, ⟪G(x) ·, ·⟫)`, the intrinsic dimension of the negative component
  (the rank of negativity, [Bog74, §IV.7]) is a locally constant function of `x`.

## Method

Over `ℂ` the spectral projection is `χ_{(0, ∞)}(G(x))`, given by the continuous functional
calculus; since `0` is not in the spectra and the spectrum is upper hemicontinuous, it depends
continuously on `x` (`ContinuousOn.cfc_of_mem_nhdsSet`). Over `ℝ` it is the restriction of the
complex one for the complexification. Close orthogonal projections have isomorphic kernels
(`v ↦ v - Q v` maps `ker P` onto `ker Q` when `‖P - Q‖ < 1`), and by [Bog74, Corollary 7.4], the
index can be read off any fundamental decomposition.

## References

* [J. Bognár, *Indefinite Inner Product Spaces*][Bog74]
-/

@[expose] public section

open Filter RCLike
open scoped Topology InnerProductSpace ComplexConjugate

noncomputable section

namespace LocallyConvex.Analysis

universe u

/-! ### Continuity of the complexification of operators -/

namespace HilbertComplexification

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem norm_cx_le (T : E →L[𝕜] E) : ‖cx T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

theorem cx_sub (S T : E →L[𝕜] E) : cx (S - T) = cx S - cx T := by
  ext z <;> simp

theorem lipschitzWith_cx : LipschitzWith 1 (cx : (E →L[𝕜] E) → _) :=
  LipschitzWith.of_dist_le_mul fun S T ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← cx_sub, NNReal.coe_one, one_mul]
    exact norm_cx_le _

theorem real_sub (x y : E) :
    (real (x - y) : HilbertComplexification 𝕜 E) = real x - real y := by
  ext <;> simp [real]

end HilbertComplexification

open HilbertComplexification

/-! ### Continuity of the spectral projections -/

/-- The indicator function of `(0, ∞)`. -/
def posInd (t : ℝ) : ℝ := if 0 < t then 1 else 0

theorem continuousOn_posInd : ContinuousOn posInd {t : ℝ | t ≠ 0} := fun t ht ↦ by
  refine ContinuousAt.continuousWithinAt ?_
  rcases (show t ≠ 0 from ht).lt_or_gt with h | h
  · exact (continuousAt_const (y := (0 : ℝ))).congr (by
      filter_upwards [eventually_lt_nhds h] with s hs
      simp [posInd, hs.le.not_gt])
  · exact (continuousAt_const (y := (1 : ℝ))).congr (by
      filter_upwards [eventually_gt_nhds h] with s hs
      simp [posInd, hs])

/-- **The spectral projections of a continuous family of invertible self-adjoint operators on a
complex Hilbert space are continuous.** -/
theorem continuous_cfc_posInd {X : Type*} [TopologicalSpace X] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {A : X → F →L[ℂ] F}
    (hA : Continuous A) (hsa : ∀ x, IsSelfAdjoint (A x)) (hu : ∀ x, IsUnit (A x)) :
    Continuous fun x ↦ cfc posInd (A x) := by
  rw [← continuousOn_univ]
  refine ContinuousOn.cfc_of_mem_nhdsSet (s := {t : ℝ | t ≠ 0}) posInd ?_ hA.continuousOn
    (fun x _ ↦ hsa x) continuousOn_posInd
  refine isOpen_ne.mem_nhdsSet.2 fun t ht ↦ ?_
  simp only [Set.mem_iUnion] at ht
  obtain ⟨x, -, hx⟩ := ht
  rintro rfl
  exact (spectrum.zero_notMem_iff ℝ).2 (hu x) hx

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

theorem isSelfAdjoint_cx {G : E →L[𝕜] E} (hG : ∀ x y, ⟪G x, y⟫_𝕜 = ⟪x, G y⟫_𝕜) :
    IsSelfAdjoint (cx G) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro z w
  simp only [ContinuousLinearMap.coe_coe]
  exact inner_cx G G hG z w

theorem isUnit_cx {G : E →L[𝕜] E} (hG : Function.Bijective G) : IsUnit (cx G) := by
  let e := ContinuousLinearEquiv.ofBijective G (LinearMap.ker_eq_bot.2 hG.1)
    (LinearMap.range_eq_top.2 hG.2)
  have h1 : G * (e.symm : E →L[𝕜] E) = 1 :=
    ContinuousLinearMap.ext fun x ↦ show G (e.symm x) = x from e.apply_symm_apply x
  have h2 : (e.symm : E →L[𝕜] E) * G = 1 :=
    ContinuousLinearMap.ext fun x ↦ show e.symm (G x) = x from e.symm_apply_apply x
  exact ⟨⟨cx G, cx (e.symm : E →L[𝕜] E), by rw [← cx_mul, h1, cx_one],
    by rw [← cx_mul, h2, cx_one]⟩, rfl⟩

/-- **Spectral projections chosen continuously.** For a norm-continuous family `G` of invertible
self-adjoint operators on a real or complex Hilbert space, the spectral projections `P(x)` of
`G(x)` onto the positive part form a continuous family; each `P(x)` is an orthogonal projection
commuting with `G(x)`, with `⟪G(x) v, v⟫ ≥ c ‖v‖²` on its range and `≤ -c ‖v‖²` on its kernel. -/
theorem exists_continuous_spectral_projection {X : Type*} [TopologicalSpace X]
    {G : X → E →L[𝕜] E} (hG : Continuous G) (hsa : ∀ x v w, ⟪G x v, w⟫_𝕜 = ⟪v, G x w⟫_𝕜)
    (hbij : ∀ x, Function.Bijective (G x)) :
    ∃ P : X → E →L[𝕜] E, Continuous P ∧ ∀ x, ∃ c > 0, (∀ v, P x (P x v) = P x v) ∧
      (∀ v w, ⟪P x v, w⟫_𝕜 = ⟪v, P x w⟫_𝕜) ∧ (∀ v, G x (P x v) = P x (G x v)) ∧
      (∀ v, P x v = v → c * ‖v‖ ^ 2 ≤ re ⟪G x v, v⟫_𝕜) ∧
      (∀ v, P x v = 0 → c * ‖v‖ ^ 2 ≤ -re ⟪G x v, v⟫_𝕜) := by
  choose P c hc hPP hPsa hGP hpos hneg hreal using fun x ↦
    FundamentalSymmetry.exists_spectral_projection (hsa x) (hbij x)
  refine ⟨P, ?_, fun x ↦ ⟨c x, hc x, hPP x, hPsa x, hGP x, hpos x, hneg x⟩⟩
  -- the complex spectral projections are continuous
  have hC : Continuous fun x ↦ cfc posInd (cx (G x)) :=
    continuous_cfc_posInd (lipschitzWith_cx.continuous.comp hG)
      (fun x ↦ isSelfAdjoint_cx (hsa x)) fun x ↦ isUnit_cx (hbij x)
  have hle : ∀ x y, ‖P x - P y‖ ≤ ‖cfc posInd (cx (G x)) - cfc posInd (cx (G y))‖ := by
    intro x y
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
    have e : real ((P x - P y) v) =
        (cfc posInd (cx (G x)) - cfc posInd (cx (G y))) (real v) := by
      rw [sub_apply, sub_apply, real_sub]
      exact (congrArg₂ (· - ·) (hreal x v) (hreal y v)).symm
    rw [← norm_real (𝕜 := 𝕜) ((P x - P y) v), e, ← norm_real (𝕜 := 𝕜) v]
    exact ContinuousLinearMap.le_opNorm _ _
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun x ↦ ?_)
    (tendsto_iff_dist_tendsto_zero.1 (hC.tendsto x₀))
  rw [dist_eq_norm, dist_eq_norm]
  exact hle x x₀

/-! ### Close projections have isomorphic kernels -/

section Kernels

variable {P Q : E →L[𝕜] E}

/-- `v ↦ v - Q v`, from `ker P` to `ker Q`. -/
def kerMap (hQ : ∀ v, Q (Q v) = Q v) :
    LinearMap.ker (P : E →ₗ[𝕜] E) →ₗ[𝕜] LinearMap.ker (Q : E →ₗ[𝕜] E) where
  toFun v := ⟨(v : E) - Q v, by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hQ, sub_self]⟩
  map_add' v w := Subtype.ext (by simp only [Submodule.coe_add, map_add]; abel)
  map_smul' c v := Subtype.ext (by simp [smul_sub])

omit [CompleteSpace E] in
theorem norm_le_kerMap (hQ : ∀ v, Q (Q v) = Q v) (v : LinearMap.ker (P : E →ₗ[𝕜] E)) :
    (1 - ‖P - Q‖) * ‖v‖ ≤ ‖kerMap hQ v‖ := by
  have hPv : P v = 0 := v.2
  have hQv : ‖Q v‖ ≤ ‖P - Q‖ * ‖(v : E)‖ := by
    have : Q v = -((P - Q) v) := by
      rw [sub_apply, hPv, zero_sub, neg_neg]
    rw [this, norm_neg]
    exact (P - Q).le_opNorm _
  have h1 : ‖(v : E)‖ ≤ ‖(v : E) - Q v‖ + ‖Q v‖ := by
    simpa using norm_add_le ((v : E) - Q v) (Q v)
  change (1 - ‖P - Q‖) * ‖(v : E)‖ ≤ ‖(v : E) - Q v‖
  linarith

omit [CompleteSpace E] in
theorem norm_kerMap_le (hQ : ∀ v, Q (Q v) = Q v) (v : LinearMap.ker (P : E →ₗ[𝕜] E)) :
    ‖kerMap hQ v‖ ≤ (1 + ‖Q‖) * ‖v‖ := by
  change ‖(v : E) - Q v‖ ≤ (1 + ‖Q‖) * ‖(v : E)‖
  calc ‖(v : E) - Q v‖ ≤ ‖(v : E)‖ + ‖Q v‖ := norm_sub_le _ _
    _ ≤ ‖(v : E)‖ + ‖Q‖ * ‖(v : E)‖ := by gcongr; exact Q.le_opNorm _
    _ = (1 + ‖Q‖) * ‖(v : E)‖ := by ring

/-- **Kernels of close orthogonal projections are isomorphic**: if `P`, `Q` are orthogonal
projections with `‖P - Q‖ < 1`, then `v ↦ v - Q v` is an isomorphism of topological vector spaces
`ker P ≅ ker Q`. -/
theorem continuousLinearEquiv_ker_of_norm_sub_lt_one (hP : ∀ v, P (P v) = P v)
    (hPsa : ∀ v w, ⟪P v, w⟫_𝕜 = ⟪v, P w⟫_𝕜) (hQ : ∀ v, Q (Q v) = Q v)
    (hQsa : ∀ v w, ⟪Q v, w⟫_𝕜 = ⟪v, Q w⟫_𝕜) (h : ‖P - Q‖ < 1) :
    Nonempty (LinearMap.ker (P : E →ₗ[𝕜] E) ≃L[𝕜] LinearMap.ker (Q : E →ₗ[𝕜] E)) := by
  set δ := ‖P - Q‖
  have hδ : 0 < 1 - δ := by linarith
  have : CompleteSpace (LinearMap.ker (P : E →ₗ[𝕜] E)) :=
    (ContinuousLinearMap.isClosed_ker P).completeSpace_coe
  have : CompleteSpace (LinearMap.ker (Q : E →ₗ[𝕜] E)) :=
    (ContinuousLinearMap.isClosed_ker Q).completeSpace_coe
  set T := kerMap (P := P) hQ
  have hlow : ∀ v, ‖v‖ ≤ (1 - δ)⁻¹ * ‖T v‖ := fun v ↦ by
    rw [le_inv_mul_iff₀ hδ]
    exact norm_le_kerMap hQ v
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).2 fun v hv ↦ by
    have := hlow v
    rw [hv, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hsurj : Function.Surjective T := by
    have hanti : AntilipschitzWith ⟨(1 - δ)⁻¹, by positivity⟩ T :=
      AntilipschitzWith.of_le_mul_dist fun v w ↦ by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact hlow (v - w)
    have hcomplete : IsComplete (Set.range T) := hanti.isComplete_range
      (AddMonoidHomClass.uniformContinuous_of_bound T _ (norm_kerMap_le hQ))
    set R := LinearMap.range T
    have : CompleteSpace R := hcomplete.completeSpace_coe
    have hperp : Rᗮ = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun w hw ↦ ?_
      have hQw : Q w = 0 := w.2
      -- `w` is orthogonal to `ker P`
      have horth : ∀ v ∈ LinearMap.ker (P : E →ₗ[𝕜] E), ⟪v, (w : E)⟫_𝕜 = 0 := fun v hv ↦ by
        have h1 := Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self T ⟨v, hv⟩) hw
        rw [Submodule.coe_inner] at h1
        change ⟪v - Q v, (w : E)⟫_𝕜 = 0 at h1
        rwa [inner_sub_left, hQsa, hQw, inner_zero_right, sub_zero] at h1
      -- hence `w ∈ ran P`
      have hmem : (w : E) - P w ∈ LinearMap.ker (P : E →ₗ[𝕜] E) := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hP, sub_self]
      have hwP : (w : E) = P w := by
        have h1 := horth _ hmem
        have h2 : ⟪(w : E) - P w, P w⟫_𝕜 = 0 := by
          rw [← hPsa, map_sub, hP, sub_self, inner_zero_left]
        have h3 : ⟪(w : E) - P w, (w : E) - P w⟫_𝕜 = 0 := by
          rw [inner_sub_right, h1, h2, sub_zero]
        exact (sub_eq_zero.1 (inner_self_eq_zero.1 h3))
      have hw0 : (w : E) = 0 := by
        have hle : ‖(w : E)‖ ≤ δ * ‖(w : E)‖ := by
          calc ‖(w : E)‖ = ‖(P - Q) w‖ := by
                rw [sub_apply, hQw, sub_zero, ← hwP]
            _ ≤ δ * ‖(w : E)‖ := (P - Q).le_opNorm _
        have : (1 - δ) * ‖(w : E)‖ ≤ 0 := by linarith
        exact norm_le_zero_iff.1 (le_of_mul_le_mul_left (by simpa using this) hδ)
      exact Subtype.ext hw0
    have htop : R = ⊤ := Submodule.orthogonal_eq_bot_iff.1 hperp
    intro w
    have hw : w ∈ R := htop ▸ Submodule.mem_top
    exact hw
  let e := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  exact ⟨e.toContinuousLinearEquivOfBounds (1 + ‖Q‖) (1 - δ)⁻¹ (norm_kerMap_le hQ)
    fun w ↦ by
      have := hlow (e.symm w)
      rwa [show T (e.symm w) = w from e.apply_symm_apply w] at this⟩

end Kernels

/-! ### The index -/

section Index

theorem isSelfAdjoint_of_symm {G : E →L[𝕜] E} (hsa : ∀ v w, ⟪G v, w⟫_𝕜 = ⟪v, G w⟫_𝕜) :
    IsSelfAdjoint G :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 hsa

theorem isUnit_of_bijective {G : E →L[𝕜] E} (hG : Function.Bijective G) : IsUnit G := by
  let e := ContinuousLinearEquiv.ofBijective G (LinearMap.ker_eq_bot.2 hG.1)
    (LinearMap.range_eq_top.2 hG.2)
  refine ⟨⟨G, e.symm, ?_, ?_⟩, rfl⟩
  · exact ContinuousLinearMap.ext fun x ↦ show G (e.symm x) = x from e.apply_symm_apply x
  · exact ContinuousLinearMap.ext fun x ↦ show e.symm (G x) = x from e.symm_apply_apply x

/-- The **index** of a fundamental decomposition of `(H, ⟪G ·, ·⟫)`: the intrinsic dimension of its
negative component (the rank of negativity, [Bog74, §IV.7]). -/
def index {G : E →L[𝕜] E} (hG : IsSelfAdjoint G) (D : AlgFundamentalDecomposition (gramForm G) ⊤) :
    Cardinal.{u} :=
  intrinsicDim (-gramForm G) D.neg (KreinDecomposition.conj_neg (conj_gramForm hG))
    fun v hv h0 ↦ by simpa using D.neg_def v hv h0

/-- The index does not depend on the fundamental decomposition ([Bog74, Corollary 7.4]). -/
theorem index_eq {G : E →L[𝕜] E} (hG : IsSelfAdjoint G) (hu : IsUnit G)
    (D D' : AlgFundamentalDecomposition (gramForm G) ⊤) : index hG D = index hG D' :=
  KreinDecomposition.intrinsicDim_neg_eq (conj_gramForm hG) (D.toKreinDecomposition hG hu)
    (D'.toKreinDecomposition hG hu)

variable {G P : E →L[𝕜] E} {c : ℝ}

/-- The **spectral decomposition** `H = ran P ⊕ ker P` given by a spectral projection `P`
of `G`. -/
def spectralDecomposition (hc : 0 < c) (hPP : ∀ v, P (P v) = P v)
    (hPsa : ∀ v w, ⟪P v, w⟫_𝕜 = ⟪v, P w⟫_𝕜) (hGP : ∀ v, G (P v) = P (G v))
    (hpos : ∀ v, P v = v → c * ‖v‖ ^ 2 ≤ re ⟪G v, v⟫_𝕜)
    (hneg : ∀ v, P v = 0 → c * ‖v‖ ^ 2 ≤ -re ⟪G v, v⟫_𝕜) :
    AlgFundamentalDecomposition (gramForm G) ⊤ where
  pos := LinearMap.ker (((1 : E →L[𝕜] E) - P : E →L[𝕜] E) : E →ₗ[𝕜] E)
  neg := LinearMap.ker (P : E →ₗ[𝕜] E)
  sup_eq := by
    refine eq_top_iff.2 fun v _ ↦ Submodule.mem_sup.2 ⟨P v, ?_, v - P v, ?_, by abel⟩
    · simp [LinearMap.mem_ker, hPP]
    · simp [LinearMap.mem_ker, hPP]
  disjoint := by
    rw [Submodule.disjoint_def]
    intro v h1 h2
    have h1' : v - P v = 0 := by simpa using h1
    have h2' : P v = 0 := h2
    rw [h2', sub_zero] at h1'
    exact h1'
  orth v hv w hw := by
    have hv' : P v = v := by
      have : v - P v = 0 := by simpa using hv
      exact (sub_eq_zero.1 this).symm
    have hw' : P w = 0 := hw
    rw [gramForm_apply, ← hv', hGP, hPsa, hw', inner_zero_right]
  pos_def v hv h0 := by
    have hv' : P v = v := by
      have : v - P v = 0 := by simpa using hv
      exact (sub_eq_zero.1 this).symm
    have := hpos v hv'
    have : 0 < c * ‖v‖ ^ 2 := by positivity
    rw [gramForm_apply]
    linarith
  neg_def v hv h0 := by
    have := hneg v hv
    have : 0 < c * ‖v‖ ^ 2 := by positivity
    rw [gramForm_apply]
    linarith

/-- The index of the spectral decomposition is the dense-span dimension of `ker P`. -/
theorem index_spectralDecomposition (hG : IsSelfAdjoint G) (hc : 0 < c)
    (hPP : ∀ v, P (P v) = P v) (hPsa : ∀ v w, ⟪P v, w⟫_𝕜 = ⟪v, P w⟫_𝕜)
    (hGP : ∀ v, G (P v) = P (G v)) (hpos : ∀ v, P v = v → c * ‖v‖ ^ 2 ≤ re ⟪G v, v⟫_𝕜)
    (hneg : ∀ v, P v = 0 → c * ‖v‖ ^ 2 ≤ -re ⟪G v, v⟫_𝕜) :
    index hG (spectralDecomposition hc hPP hPsa hGP hpos hneg) =
      denseSpanDim 𝕜 (LinearMap.ker (P : E →ₗ[𝕜] E)) := by
  set D := spectralDecomposition hc hPP hPsa hGP hpos hneg
  set I := IntrinsicSpace (-gramForm G) D.neg (KreinDecomposition.conj_neg (conj_gramForm hG))
    fun v hv h0 ↦ by simpa using D.neg_def v hv h0
  have hnormI : ∀ x : I, ‖x‖ ^ 2 = -re ⟪G x.val, x.val⟫_𝕜 := fun x ↦ by
    rw [KreinDecomposition.norm_sq_intrinsic]
    simp
  let e₀ : I ≃ₗ[𝕜] LinearMap.ker (P : E →ₗ[𝕜] E) := LinearEquiv.refl 𝕜 _
  have he₀ : ∀ x : I, ((e₀ x : LinearMap.ker (P : E →ₗ[𝕜] E)) : E) = x.val := fun _ ↦ rfl
  have hto : ∀ x : I, ‖e₀ x‖ ≤ (√c)⁻¹ * ‖x‖ := fun x ↦ by
    have h1 := hneg x.val x.val_mem
    rw [← hnormI] at h1
    rw [le_inv_mul_iff₀ (Real.sqrt_pos.2 hc), ← sq_le_sq₀ (by positivity) (norm_nonneg _),
      mul_pow, Real.sq_sqrt hc.le]
    rw [← Submodule.norm_coe, he₀]
    exact h1
  have hinv : ∀ y, ‖e₀.symm y‖ ≤ √‖G‖ * ‖y‖ := fun y ↦ by
    rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (norm_nonneg _),
      hnormI]
    change -re ⟪G (y : E), (y : E)⟫_𝕜 ≤ ‖G‖ * ‖(y : E)‖ ^ 2
    calc -re ⟪G (y : E), (y : E)⟫_𝕜 ≤ ‖⟪G (y : E), (y : E)⟫_𝕜‖ := (neg_le_abs _).trans
          (abs_re_le_norm _)
      _ ≤ ‖G (y : E)‖ * ‖(y : E)‖ := norm_inner_le_norm _ _
      _ ≤ ‖G‖ * ‖(y : E)‖ * ‖(y : E)‖ := by gcongr; exact G.le_opNorm _
      _ = ‖G‖ * ‖(y : E)‖ ^ 2 := by ring
  exact (e₀.toContinuousLinearEquivOfBounds _ _ hto hinv).denseSpanDim_eq

/-- **The index of a continuous family of Krein spaces is locally constant.** Let `G` be a
norm-continuous family of invertible self-adjoint operators on a real or complex Hilbert space,
and `D(x)` any fundamental decomposition of `(H, ⟪G(x) ·, ·⟫)` for each `x`. Then the index
(the intrinsic dimension of the negative component of `D(x)`) is a locally constant function of
`x`. -/
theorem isLocallyConstant_index {X : Type*} [TopologicalSpace X] {G : X → E →L[𝕜] E}
    (hG : Continuous G) (hsa : ∀ x v w, ⟪G x v, w⟫_𝕜 = ⟪v, G x w⟫_𝕜)
    (hbij : ∀ x, Function.Bijective (G x))
    (D : ∀ x, AlgFundamentalDecomposition (gramForm (G x)) ⊤) :
    IsLocallyConstant fun x ↦ index (isSelfAdjoint_of_symm (hsa x)) (D x) := by
  obtain ⟨P, hPc, hprops⟩ := exists_continuous_spectral_projection hG hsa hbij
  choose c hc hPP hPsa hGP hpos hneg using hprops
  have hidx : ∀ x, index (isSelfAdjoint_of_symm (hsa x)) (D x) =
      denseSpanDim 𝕜 (LinearMap.ker (P x : E →ₗ[𝕜] E)) := fun x ↦
    (index_eq _ (isUnit_of_bijective (hbij x)) (D x)
      (spectralDecomposition (hc x) (hPP x) (hPsa x) (hGP x) (hpos x) (hneg x))).trans
      (index_spectralDecomposition _ (hc x) (hPP x) (hPsa x) (hGP x) (hpos x) (hneg x))
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖P x - P x₀‖ < 1 := by
    filter_upwards [(hPc.tendsto x₀).eventually (Metric.ball_mem_nhds (P x₀) one_pos)] with x hx
    rwa [dist_eq_norm] at hx
  filter_upwards [hnear] with x hx
  rw [hidx, hidx]
  obtain ⟨e⟩ := continuousLinearEquiv_ker_of_norm_sub_lt_one (hPP x) (hPsa x) (hPP x₀)
    (hPsa x₀) hx
  exact e.denseSpanDim_eq

end Index

end LocallyConvex.Analysis

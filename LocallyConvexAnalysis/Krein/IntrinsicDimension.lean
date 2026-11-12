/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Krein.Majorant
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The intrinsic dimension of the components of a Krein space

Reference: J. Bognár, *Indefinite Inner Product Spaces*, Springer (1974), §IV.7, pp. 93–95:
Lemma 7.1, Lemma 7.3 and Corollary 7.4.

The **dense-span dimension** of a topological vector space `X` (`denseSpanDim`) is the least
cardinality of a subset whose span is dense; Bognár uses it in the proof of Lemma 7.3 (the
"`τ`-dimension"). The **intrinsic dimension** of a definite subspace (`intrinsicDim`) is the
dense-span dimension of the subspace with its intrinsic norm `√B(x, x)` ([Bog74, §IV.7], "intrinsic
dimension"). It is invariant under isomorphisms of topological vector spaces
(`ContinuousLinearEquiv.denseSpanDim_eq`), and for an inner product space it is the Hilbert
dimension: the cardinality of any orthonormal family with dense span (`Orthonormal.denseSpanDim_eq`,
`HilbertBasis.denseSpanDim_eq`).

## Main results

* `KreinDecomposition.posEquiv` ([Bog74, Lemma 7.1]): if `K₁`, `K₂` are fundamental decompositions
  of a Krein space, `P₁₊` restricted to `E₂₊` is an isomorphism of topological vector spaces
  `E₂₊ ≅ E₁₊` for the intrinsic norms, with `‖x‖ ≤ ‖P₁₊ x‖`.
* `KreinDecomposition.intrinsicDim_pos_eq`, `KreinDecomposition.intrinsicDim_neg_eq` (**
  [Bog74, Corollary 7.4]**): the intrinsic dimensions of `E₊` and of `E₋` do not depend on the
  fundamental decomposition. They are the **rank of positivity** and the **rank of negativity** of
  the Krein space ([Bog74, p. 95]); the latter is the index of a Krein space.
* `KreinDecomposition.intrinsicDim_pos_eq_card`, `KreinDecomposition.intrinsicDim_neg_eq_card`:
  these ranks are the Hilbert dimensions of `E₊` and `E₋`.
* `Orthonormal.cardinal_le_denseSpanDim`, `HilbertBasis.denseSpanDim_eq`: no orthonormal family is
  larger than a set with dense span, so all Hilbert bases of a Hilbert space have the cardinality
  `denseSpanDim`.

## Method

Bognár derives Corollary 7.4 from Lemma 7.3 (`dim Q ≤ dim E₊` for a positive definite `Q`). For
Krein spaces we show instead that `P₁₊ : E₂₊ → E₁₊` is onto: its range is closed (it is bounded
below and `E₂₊` is complete) and its `B`-orthogonal in `E₁₊` lies in `E₂₊^[⊥] = E₂₋`, hence is
zero. We do not claim this argument is new.

## References

* [J. Bognár, *Indefinite Inner Product Spaces*][Bog74]
-/

@[expose] public section

open Filter RCLike
open scoped Topology InnerProductSpace ComplexConjugate Cardinal

noncomputable section

namespace LocallyConvex.Analysis

universe u

/-! ### The dense-span dimension -/

section DenseSpanDim

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (X : Type u) [AddCommGroup X] [Module 𝕜 X]
  [TopologicalSpace X]

/-- The **dense-span dimension**: the least cardinality of a subset whose span is dense
([Bog74, proof of Lemma IV.7.3]). -/
def denseSpanDim : Cardinal.{u} :=
  sInf {c | ∃ s : Set X, #s = c ∧ Dense (Submodule.span 𝕜 s : Set X)}

variable {𝕜 X}

theorem denseSpanDim_le {s : Set X} (hs : Dense (Submodule.span 𝕜 s : Set X)) :
    denseSpanDim 𝕜 X ≤ #s :=
  csInf_le' ⟨s, rfl, hs⟩

variable (𝕜 X) in
theorem exists_denseSpanDim :
    ∃ s : Set X, #s = denseSpanDim 𝕜 X ∧ Dense (Submodule.span 𝕜 s : Set X) :=
  csInf_mem (s := {c | ∃ s : Set X, #s = c ∧ Dense (Submodule.span 𝕜 s : Set X)})
    ⟨_, Set.univ, rfl, by simp⟩

/-- The dense-span dimension is invariant under isomorphisms of topological vector spaces. -/
theorem _root_.ContinuousLinearEquiv.denseSpanDim_eq {Y : Type u} [AddCommGroup Y] [Module 𝕜 Y]
    [TopologicalSpace Y] (e : X ≃L[𝕜] Y) : denseSpanDim 𝕜 X = denseSpanDim 𝕜 Y := by
  have key : ∀ {X Y : Type u} [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [AddCommGroup Y]
      [Module 𝕜 Y] [TopologicalSpace Y] (e : X ≃L[𝕜] Y), denseSpanDim 𝕜 X ≤ denseSpanDim 𝕜 Y := by
    intro X Y _ _ _ _ _ _ e
    obtain ⟨s, hs, hd⟩ := exists_denseSpanDim 𝕜 Y
    have hd' : Dense (Submodule.span 𝕜 (e.symm '' s) : Set X) :=
      (e.symm.surjective.denseRange.dense_image e.symm.continuous hd).mono
        (Submodule.image_span_subset_span (e.symm : Y →L[𝕜] X).toLinearMap s)
    exact (denseSpanDim_le hd').trans ((Cardinal.mk_image_le).trans hs.le)
  exact le_antisymm (key e) (key e.symm)

end DenseSpanDim

/-! ### The Hilbert dimension -/

section HilbertDim

open Submodule

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type u} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- An orthonormal family is no larger than any set with dense span: the dense-span dimension
bounds the cardinality of orthonormal families. For an infinite set `s` with dense span, every
`v i` has a nonzero inner product with some element of `s`, and each element of `s` has nonzero
inner products with only countably many `v i` (Bessel's inequality); for a finite `s`, the span of
`s` is the whole space and `v` is linearly independent. -/
theorem _root_.Orthonormal.cardinal_le_denseSpanDim {ι : Type u} {v : ι → X}
    (hv : Orthonormal 𝕜 v) : #ι ≤ denseSpanDim 𝕜 X := by
  obtain ⟨s, hs, hd⟩ := exists_denseSpanDim 𝕜 X
  rw [← hs]
  -- every `v i` sees some element of `s`
  have hkey : ∀ i, ∃ x ∈ s, ⟪v i, x⟫_𝕜 ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    have hle : span 𝕜 s ≤ LinearMap.ker (innerₛₗ 𝕜 (v i)) :=
      span_le.2 fun x hx ↦ by simpa using h x hx
    have hcl : closure (span 𝕜 s : Set X) ⊆ {y | ⟪v i, y⟫_𝕜 = 0} :=
      closure_minimal (fun y hy ↦ by simpa using hle hy)
        (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    have hvi : ⟪v i, v i⟫_𝕜 = 0 := hcl (hd.closure_eq ▸ Set.mem_univ (v i))
    rw [inner_self_eq_zero] at hvi
    simpa [hvi] using hv.1 i
  rcases s.finite_or_infinite with hfin | hinf
  · -- the span of `s` is closed, hence everything
    have : FiniteDimensional 𝕜 (span 𝕜 s) := FiniteDimensional.span_of_finite 𝕜 hfin
    have htop : span 𝕜 s = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hc : IsClosed (span 𝕜 s : Set X) := (span 𝕜 s).closed_of_finiteDimensional
      have : x ∈ closure (span 𝕜 s : Set X) := hd.closure_eq ▸ Set.mem_univ x
      rwa [hc.closure_eq] at this
    calc #ι ≤ Module.rank 𝕜 X := hv.linearIndependent.cardinal_le_rank
      _ = Module.rank 𝕜 (span 𝕜 s) := by rw [htop, rank_top]
      _ ≤ #s := rank_span_le s
  · -- countable supports
    have hsupp : ∀ x : X, {i | ⟪v i, x⟫_𝕜 ≠ 0}.Countable := fun x ↦ by
      have := (hv.inner_products_summable (x := x)).countable_support
      refine this.mono fun i hi ↦ ?_
      simpa [Function.mem_support] using hi
    have hcov : (Set.univ : Set ι) = ⋃ x ∈ s, {i | ⟪v i, x⟫_𝕜 ≠ 0} := by
      ext i
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, true_iff]
      exact hkey i
    have : Infinite s := hinf.to_subtype
    calc #ι = #(Set.univ : Set ι) := Cardinal.mk_univ.symm
      _ = #(⋃ x ∈ s, {i | ⟪v i, x⟫_𝕜 ≠ 0}) := by rw [hcov]
      _ ≤ #s * ⨆ x : s, #({i | ⟪v i, (x : X)⟫_𝕜 ≠ 0}) := Cardinal.mk_biUnion_le _ _
      _ ≤ #s * Cardinal.aleph0 := by
        gcongr
        exact ciSup_le' fun x ↦ Cardinal.mk_le_aleph0_iff.2 (hsupp x).to_subtype
      _ = #s := Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk s)

/-- **The dense-span dimension of an inner product space is its Hilbert dimension**: the
cardinality of any orthonormal family with dense span. -/
theorem _root_.Orthonormal.denseSpanDim_eq {ι : Type u} {v : ι → X} (hv : Orthonormal 𝕜 v)
    (hd : Dense (span 𝕜 (Set.range v) : Set X)) : denseSpanDim 𝕜 X = #ι :=
  le_antisymm ((denseSpanDim_le hd).trans Cardinal.mk_range_le) hv.cardinal_le_denseSpanDim

/-- **The dense-span dimension of a Hilbert space is its Hilbert dimension**: the cardinality of
any Hilbert basis. In particular, all Hilbert bases have the same cardinality. -/
theorem _root_.HilbertBasis.denseSpanDim_eq {ι : Type u}
    (b : HilbertBasis ι 𝕜 X) : denseSpanDim 𝕜 X = #ι :=
  b.orthonormal.denseSpanDim_eq (dense_iff_topologicalClosure_eq_top.2 b.dense_span)

end HilbertDim

/-! ### Intrinsic dimension -/

section Intrinsic

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-- The **intrinsic dimension** of a definite subspace: the dense-span dimension of the subspace
with its intrinsic norm ([Bog74, §IV.7]). -/
def intrinsicDim (B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜) (S : Submodule 𝕜 E)
    (hB : ∀ x y, conj (B y x) = B x y) (hpos : ∀ x ∈ S, x ≠ 0 → 0 < re (B x x)) : Cardinal.{u} :=
  denseSpanDim 𝕜 (IntrinsicSpace B S hB hpos)

variable {B : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜} (hB : ∀ x y, conj (B y x) = B x y)

namespace KreinDecomposition

variable (K₁ K₂ : KreinDecomposition B ⊤)

/-- The restriction `P₁₊ : E₂₊ → E₁₊` of the fundamental projection of `K₁`
([Bog74, Lemma 7.1]). -/
def posMap : IntrinsicSpace B K₂.pos hB K₂.pos_def →ₗ[𝕜] IntrinsicSpace B K₁.pos hB K₁.pos_def where
  toFun x := IntrinsicSpace.mk (K₁.projPos x.val) (K₁.projPos_mem _)
  map_add' x y := IntrinsicSpace.val_injective (by simp [map_add])
  map_smul' c x := IntrinsicSpace.val_injective (by simp [map_smul])

@[simp] theorem val_posMap (x : IntrinsicSpace B K₂.pos hB K₂.pos_def) :
    (K₁.posMap hB K₂ x).val = K₁.projPos x.val := rfl

theorem norm_sq_intrinsic {S : Submodule 𝕜 E} {hpos : ∀ x ∈ S, x ≠ 0 → 0 < re (B x x)}
    (x : IntrinsicSpace B S hB hpos) : ‖x‖ ^ 2 = re (B x.val x.val) := by
  rw [IntrinsicSpace.norm_eq, Real.sq_sqrt]
  by_cases h : x.val = 0
  · simp [h]
  · exact (hpos _ x.val_mem h).le

include hB in
/-- `B(x, x) = B(P₊ x, P₊ x) + B(P₋ x, P₋ x)`. -/
theorem re_B_eq (K : KreinDecomposition B ⊤) (x : E) :
    re (B x x) = re (B (K.projPos x) (K.projPos x)) + re (B (K.projNeg x) (K.projNeg x)) := by
  have h : B (K.projPos x + K.projNeg x) (K.projPos x + K.projNeg x) =
      B (K.projPos x) (K.projPos x) + B (K.projPos x) (K.projNeg x) +
        B (K.projNeg x) (K.projPos x) + B (K.projNeg x) (K.projNeg x) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [K.projPos_add_projNeg, K.orth _ (K.projPos_mem x) _ (K.projNeg_mem x),
    K.B_neg_pos hB (K.projNeg_mem x) (K.projPos_mem x), add_zero, add_zero] at h
  rw [h, map_add]

/-- **Lemma 7.1**: `P₁₊` is bounded below on the positive subspace `E₂₊`, `‖x‖ ≤ ‖P₁₊ x‖`. -/
theorem norm_le_norm_posMap (x : IntrinsicSpace B K₂.pos hB K₂.pos_def) :
    ‖x‖ ≤ ‖K₁.posMap hB K₂ x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_intrinsic hB, norm_sq_intrinsic hB,
    val_posMap, re_B_eq hB K₁]
  linarith [K₁.re_B_nonpos_neg (K₁.projNeg_mem x.val)]

/-- `P₁₊` is bounded on `E₂₊`, by the equivalence of the decomposition majorants. -/
theorem exists_norm_posMap_le :
    ∃ C > 0, ∀ x, ‖K₁.posMap hB K₂ x‖ ≤ C * ‖x‖ := by
  obtain ⟨c, hc, C, hC, h⟩ := K₂.exists_jInner_bounds hB K₁.toAlgFundamentalDecomposition
  refine ⟨√C, Real.sqrt_pos.2 hC, fun x ↦ ?_⟩
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt hC.le,
    norm_sq_intrinsic hB, norm_sq_intrinsic hB, val_posMap]
  have h1 : re (B (K₁.projPos x.val) (K₁.projPos x.val)) ≤ re (K₁.jInner x.val x.val) := by
    rw [K₁.jInner_eq hB, map_sub]
    linarith [K₁.re_B_nonpos_neg (K₁.projNeg_mem x.val)]
  have h2 := (h x.val).2
  rw [K₂.jInner_of_mem_pos hB x.val_mem x.val_mem] at h2
  exact h1.trans h2

theorem injective_posMap : Function.Injective (K₁.posMap hB K₂) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have h := K₁.norm_le_norm_posMap hB K₂ x
  rw [hx, norm_zero] at h
  exact norm_le_zero_iff.1 h

/-- `P₁₊ : E₂₊ → E₁₊` is onto: its range is closed, and its orthogonal in `E₁₊` lies in
`E₂₊^[⊥] = E₂₋`. -/
theorem surjective_posMap : Function.Surjective (K₁.posMap hB K₂) := by
  have := IntrinsicSpace.completeSpace (hB := hB) (hpos := K₁.pos_def) K₁.pos_complete
  have := IntrinsicSpace.completeSpace (hB := hB) (hpos := K₂.pos_def) K₂.pos_complete
  obtain ⟨C, hC, hbd⟩ := K₁.exists_norm_posMap_le hB K₂
  set T := K₁.posMap hB K₂
  have hcont : Continuous T := AddMonoidHomClass.continuous_of_bound T C hbd
  have hanti : AntilipschitzWith 1 T := AntilipschitzWith.of_le_mul_dist fun x y ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact K₁.norm_le_norm_posMap hB K₂ (x - y)
  have hclosed : IsComplete (Set.range T) := hanti.isComplete_range
    (AddMonoidHomClass.uniformContinuous_of_bound T C hbd)
  set R := LinearMap.range T
  have : CompleteSpace R := hclosed.completeSpace_coe
  have hperp : Rᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun z hz ↦ ?_
    -- `z ∈ E₁₊` is `B`-orthogonal to `E₂₊`
    have hz2 : ∀ x ∈ K₂.pos, B z.val x = 0 := fun x hx ↦ by
      have h1 : ⟪T (IntrinsicSpace.mk x hx), z⟫_𝕜 = 0 :=
        Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self T _) hz
      rw [IntrinsicSpace.inner_eq, val_posMap, IntrinsicSpace.val_mk] at h1
      have h2 : B (K₁.projNeg x) z.val = 0 :=
        K₁.B_neg_pos hB (K₁.projNeg_mem x) z.val_mem
      have h3 : B x z.val = 0 := by
        rw [← K₁.projPos_add_projNeg x, map_add, LinearMap.add_apply, h1, h2, add_zero]
      rw [← hB, h3, map_zero]
    -- hence `z ∈ E₂₋`
    have hP : K₂.projPos z.val = 0 := by
      have h0 : B (K₂.projPos z.val) (K₂.projPos z.val) = 0 := by
        have e := hz2 _ (K₂.projPos_mem z.val)
        have hs : B (K₂.projPos z.val + K₂.projNeg z.val) (K₂.projPos z.val) =
            B (K₂.projPos z.val) (K₂.projPos z.val) +
              B (K₂.projNeg z.val) (K₂.projPos z.val) := by
          rw [map_add, LinearMap.add_apply]
        rw [K₂.projPos_add_projNeg, e, K₂.B_neg_pos hB (K₂.projNeg_mem _) (K₂.projPos_mem _),
          add_zero] at hs
        exact hs.symm
      by_contra hne
      have := K₂.pos_def _ (K₂.projPos_mem z.val) hne
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
    have hneg : z.val ∈ K₂.neg := by
      rw [← K₂.projPos_add_projNeg z.val, hP, zero_add]
      exact K₂.projNeg_mem _
    have hle := K₂.re_B_nonpos_neg hneg
    have hz0 : z.val = 0 := by
      by_contra hne
      have := K₁.pos_def _ z.val_mem hne
      linarith
    exact IntrinsicSpace.val_injective (by rw [hz0]; rfl)
  have htop : R = ⊤ := Submodule.orthogonal_eq_bot_iff.1 hperp
  intro y
  have hy : y ∈ R := htop ▸ Submodule.mem_top
  exact hy

/-- **Lemma 7.1**: `P₁₊ : E₂₊ ≅ E₁₊`, an isomorphism of topological vector spaces for the
intrinsic norms. -/
def posEquiv : IntrinsicSpace B K₂.pos hB K₂.pos_def ≃L[𝕜] IntrinsicSpace B K₁.pos hB K₁.pos_def :=
  (LinearEquiv.ofBijective (K₁.posMap hB K₂)
    ⟨K₁.injective_posMap hB K₂, K₁.surjective_posMap hB K₂⟩).toContinuousLinearEquivOfBounds
    (K₁.exists_norm_posMap_le hB K₂).choose 1
    (K₁.exists_norm_posMap_le hB K₂).choose_spec.2 fun y ↦ by
      rw [one_mul]
      conv_rhs => rw [← (LinearEquiv.ofBijective (K₁.posMap hB K₂)
        ⟨K₁.injective_posMap hB K₂, K₁.surjective_posMap hB K₂⟩).apply_symm_apply y]
      exact K₁.norm_le_norm_posMap hB K₂ _

/-- **The rank of positivity is well defined** ([Bog74, Corollary 7.4]): the intrinsic dimension of
the positive component does not depend on the fundamental decomposition. -/
theorem intrinsicDim_pos_eq :
    intrinsicDim B K₁.pos hB K₁.pos_def = intrinsicDim B K₂.pos hB K₂.pos_def :=
  (K₁.posEquiv hB K₂).denseSpanDim_eq.symm

/-- The decomposition `E = E₋ ⊕ E₊` for `-B`. -/
def swap (K : KreinDecomposition B ⊤) : KreinDecomposition (-B) ⊤ where
  pos := K.neg
  neg := K.pos
  sup_eq := by rw [sup_comm]; exact K.sup_eq
  disjoint := K.disjoint.symm
  orth x hx y hy := by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, K.B_neg_pos hB hx hy, neg_zero]
  pos_def x hx h0 := by
    have := K.neg_def x hx h0
    simpa using this
  neg_def x hx h0 := by
    have := K.pos_def x hx h0
    simpa using this
  pos_complete := K.neg_complete
  neg_complete := by
    convert K.pos_complete using 1
    exact neg_neg B

include hB in
theorem conj_neg (x y : E) : conj ((-B) y x) = (-B) x y := by
  simp only [LinearMap.neg_apply, map_neg, hB]

/-- **The rank of negativity is well defined** ([Bog74, Corollary 7.4]): the intrinsic dimension of
the negative component (for `-B`) does not depend on the fundamental decomposition. This is the
index of the Krein space. -/
theorem intrinsicDim_neg_eq :
    intrinsicDim (-B) K₁.neg (conj_neg hB) (K₁.swap hB).pos_def =
      intrinsicDim (-B) K₂.neg (conj_neg hB) (K₂.swap hB).pos_def :=
  intrinsicDim_pos_eq (conj_neg hB) (K₁.swap hB) (K₂.swap hB)

/-- **The rank of positivity is the Hilbert dimension of `E₊`** ([Bog74, p. 95]): the intrinsic
dimension of the positive component is the cardinality of any Hilbert basis of it. -/
theorem intrinsicDim_pos_eq_card (K : KreinDecomposition B ⊤) {ι : Type u}
    (b : HilbertBasis ι 𝕜 (IntrinsicSpace B K.pos hB K.pos_def)) :
    intrinsicDim B K.pos hB K.pos_def = #ι :=
  b.denseSpanDim_eq

/-- The positive component of a fundamental decomposition has a Hilbert basis, whose cardinality
is the rank of positivity. -/
theorem exists_hilbertBasis_pos (K : KreinDecomposition B ⊤) :
    ∃ (w : Set (IntrinsicSpace B K.pos hB K.pos_def))
      (b : HilbertBasis w 𝕜 (IntrinsicSpace B K.pos hB K.pos_def)),
      intrinsicDim B K.pos hB K.pos_def = #w ∧ ⇑b = ((↑) : w → _) := by
  have := IntrinsicSpace.completeSpace (hB := hB) (hpos := K.pos_def) K.pos_complete
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 (IntrinsicSpace B K.pos hB K.pos_def)
  exact ⟨w, b, b.denseSpanDim_eq, hb⟩

/-- **The rank of negativity is the Hilbert dimension of `E₋`** ([Bog74, p. 95]), for the inner
product `-B` (`(K.swap hB).pos` is `K.neg`). -/
theorem intrinsicDim_neg_eq_card (K : KreinDecomposition B ⊤) {ι : Type u}
    (b : HilbertBasis ι 𝕜
      (IntrinsicSpace (-B) (K.swap hB).pos (conj_neg hB) (K.swap hB).pos_def)) :
    intrinsicDim (-B) K.neg (conj_neg hB) (K.swap hB).pos_def = #ι :=
  (K.swap hB).intrinsicDim_pos_eq_card (conj_neg hB) b

end KreinDecomposition

end Intrinsic

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Spaces.Silva
public import LocallyConvexAnalysis.Topology.DirectLimit
public import LocallyConvexAnalysis.Spaces.DirectCompleteness

/-!
# Duality for Silva spaces

Reference: [GN26, Proposition B.13.13(e)–(g)] (pp. 951–952), with Propositions B.9.16 and B.10.7
(pp. 926, 929).

For a locally convex space `E` (real scalars), `StrongDual ℝ E` carries the topology of uniform
convergence on bounded sets. We first prove semi-reflexivity and reflexivity criteria for general
locally convex spaces. Then we let `E = lim Eₙ` be a Silva space (`LCDirectLimit.IsSilva`), with
`T₁` sequential steps having bounded `0`-neighbourhoods (for instance Banach spaces), and show
that `E` is a `k_ω`-space, that its strong dual is a Fréchet space, and that `E` is reflexive and
complete.

## Main definitions

* `evalStrongDual x`: the evaluation at `x`, a continuous linear functional on the strong dual.

## Main results

* `exists_evalStrongDual_eq`: if every bounded subset of `E` has compact closure, every continuous
  linear functional on the strong dual is an evaluation (semi-reflexivity; compare
  [GN26, Proposition B.10.7]).
* `continuous_evalStrongDual`: for barrelled `E`, the evaluation map into the strong bidual is
  continuous (Banach–Steinhaus).
* `exists_continuousLinearEquiv_strongBidual`: if moreover `E` is barrelled and Hausdorff, the
  evaluation map is a continuous linear isomorphism onto the strong bidual (reflexivity; compare
  Proposition B.10.7).
* `LCDirectLimit.IsSilva.isKOmegaSpace`: `E` is a `k_ω`-space (Proposition B.13.13(g)); only the
  `T₁` sequential steps are used.
* `LCDirectLimit.IsSilva.exists_isCompact_absorbing`: some sequence of compact subsets of `E`
  absorbs every bounded set.
* `LCDirectLimit.IsSilva.metrizableSpace_strongDual`,
  `LCDirectLimit.IsSilva.completeSpace_strongDual`: the strong dual of `E` is metrizable and
  complete, hence a Fréchet space (Proposition B.13.13(f)).
* `LCDirectLimit.IsSilva.exists_continuousLinearEquiv_strongBidual`: `E` is reflexive, for barrelled
  steps (Proposition B.13.13(e)).
* `LCDirectLimit.IsSilva.completeSpace`: `E` is complete (Proposition B.13.13(f)).

## Implementation notes

* Glöckner–Neeb obtain reflexivity from Proposition B.10.7 (barrelled spaces whose closed bounded
  absolutely convex sets are weakly compact). We argue directly. For semi-reflexivity, a functional
  `φ` on the strong dual is controlled by a compact absolutely convex set `C`; if `φ` did not agree
  on finitely many functionals `f₁, …, f_k` with an evaluation at a point of `C`, a functional on
  `ℝᵏ` would separate `(φ fᵢ)ᵢ` from the image of `C`, and compactness of `C` gives one point for
  all functionals. The evaluation map is continuous by Banach–Steinhaus and open since the polar of
  a closed absolutely convex `0`-neighbourhood is bounded in the strong dual and its own polar is
  the neighbourhood (Hahn–Banach). We do not claim this argument is new.
* The completeness of the strong dual comes from Mathlib's `ContinuousLinearMap.completeSpace`,
  since a `k`-space has a topology coherent with its bounded sets; Glöckner–Neeb pass through the
  topology of compact convergence (Proposition B.9.16). Its metrizability comes from a sequence of
  compact sets absorbing the bounded sets, as in Glöckner–Neeb.
* The Banach steps of Glöckner–Neeb are replaced by the properties used: `T₁`, sequential,
  barrelled, with a bounded `0`-neighbourhood.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology Bornology
open scoped Topology Pointwise Uniformity

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Semi-reflexivity and reflexivity -/

section Reflexive

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

omit [IsTopologicalAddGroup E] in
/-- The absolutely convex hull of a bounded set is bounded. -/
theorem isVonNBounded_absConvexHull {B : Set E} (hB : IsVonNBounded ℝ B) :
    IsVonNBounded ℝ (absConvexHull ℝ B) := by
  intro U hU
  obtain ⟨W, ⟨hW, hWac⟩, hWU⟩ := (nhds_hasBasis_absConvex ℝ E).mem_iff.1 hU
  filter_upwards [hB hW, eventually_ne_cobounded (0 : ℝ)] with c hc hc0
  exact (absConvexHull_min hc ⟨hWac.1.smul c, hWac.2.smul c⟩).trans (smul_set_mono hWU)

/-- The evaluation at `x`, a continuous linear functional on the strong dual. -/
def evalStrongDual (x : E) : StrongDual ℝ (StrongDual ℝ E) where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const x

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] in
@[simp] theorem evalStrongDual_apply (x : E) (f : StrongDual ℝ E) : evalStrongDual x f = f x :=
  rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The finite-dimensional step of semi-reflexivity: if `|φ f| ≤ 1` whenever `|f| ≤ 1` on a compact
absolutely convex set `C`, then `φ` agrees on any finite set of functionals with an evaluation at
a point of `C`. Otherwise a functional on `ℝᵘ` separates `(φ f)_{f ∈ u}` from the image of `C`. -/
theorem exists_mem_eq_on_finset {C : Set E} (hCc : IsCompact C) (hCac : AbsConvex ℝ C)
    (hC0 : (0 : E) ∈ C) (φ : StrongDual ℝ (StrongDual ℝ E))
    (hφ : ∀ f : StrongDual ℝ E, (∀ x ∈ C, |f x| ≤ 1) → |φ f| ≤ 1) (u : Finset (StrongDual ℝ E)) :
    ∃ x ∈ C, ∀ f ∈ u, f x = φ f := by
  classical
  let Φ : E →L[ℝ] (u → ℝ) := ContinuousLinearMap.pi fun i : u ↦ (i : StrongDual ℝ E)
  set v : u → ℝ := fun i ↦ φ i
  by_cases hv : v ∈ Φ '' C
  · obtain ⟨x, hx, hxv⟩ := hv
    exact ⟨x, hx, fun f hf ↦ congrFun hxv ⟨f, hf⟩⟩
  exfalso
  have hconv : Convex ℝ (Φ '' C) := hCac.2.linear_image Φ.toLinearMap
  have hclosed : IsClosed (Φ '' C) := (hCc.image Φ.continuous).isClosed
  obtain ⟨l, w, hlC, hlv⟩ := geometric_hahn_banach_closed_point hconv hclosed hv
  set g : StrongDual ℝ E := l.comp Φ
  have hw0 : 0 < w := by simpa using hlC _ ⟨0, hC0, map_zero Φ⟩
  have hgC : ∀ x ∈ C, |g x| ≤ w := fun x hx ↦ by
    have h1 := hlC _ ⟨x, hx, rfl⟩
    have h2 := hlC _ ⟨-x, hCac.1.neg_mem_iff.2 hx, rfl⟩
    simp only [map_neg] at h2
    exact abs_le.2 ⟨by change -w ≤ l (Φ x); linarith, h1.le⟩
  have hφg : φ g ≤ w := by
    have := hφ (w⁻¹ • g) fun x hx ↦ by
      rw [smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hw0]
      exact (inv_mul_le_one₀ hw0).2 (hgC x hx)
    rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hw0] at this
    exact (le_abs_self _).trans ((inv_mul_le_one₀ hw0).1 this)
  -- `φ g = l v`
  set e : u → (u → ℝ) := fun i j ↦ if i = j then 1 else 0
  have hl : ∀ y : u → ℝ, l y = ∑ i, y i * l (e i) := fun y ↦ by
    conv_lhs => rw [pi_eq_sum_univ y]
    simp only [map_sum, map_smul, smul_eq_mul, e]
  have hg : g = ∑ i, l (e i) • (i : StrongDual ℝ E) := by
    ext x
    change l (Φ x) = (∑ i, l (e i) • (i : StrongDual ℝ E)) x
    rw [hl, sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hφl : φ g = l v := by
    rw [hg, hl, map_sum]
    simp only [map_smul, smul_eq_mul, v, mul_comm]
  linarith

/-- **Semi-reflexivity** (compare [GN26, Proposition B.10.7]): if every bounded subset of
`E` has compact closure, every continuous linear functional on the strong dual is an evaluation.
A bounded set `B` controls `φ` (by continuity), the closed absolutely convex hull `C` of
`ε⁻¹ B ∪ {0}` is compact, and the sets `{x ∈ C : f x = φ f}` have the finite intersection property
(`exists_mem_eq_on_finset`). We do not claim this argument is new. -/
theorem exists_evalStrongDual_eq (hK : ∀ B : Set E, IsVonNBounded ℝ B → IsCompact (closure B))
    (φ : StrongDual ℝ (StrongDual ℝ E)) : ∃ x : E, evalStrongDual x = φ := by
  -- a bounded set controlling `φ`
  have h0 : Metric.ball (φ 0) 1 ∈ 𝓝 (φ 0) := Metric.ball_mem_nhds _ one_pos
  rw [map_zero] at h0
  have hφ : φ ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : StrongDual ℝ E) :=
    φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact h0)
  obtain ⟨⟨B, ε⟩, ⟨hB, hε⟩, hsub⟩ := (ContinuousLinearMap.hasBasis_nhds_zero_of_basis
    (E := E) (σ := RingHom.id ℝ) (Metric.nhds_basis_ball (x := (0 : ℝ)))).mem_iff.1 hφ
  have key : ∀ f : StrongDual ℝ E, (∀ x ∈ B, |f x| ≤ ε) → |φ f| ≤ 1 := by
    intro f hf
    by_contra hlt
    push Not at hlt
    have hpos : 0 < |φ f| := one_pos.trans hlt
    set δ := |φ f|⁻¹
    have hδ1 : δ < 1 := inv_lt_one_of_one_lt₀ hlt
    have hδ0 : 0 < δ := inv_pos.2 hpos
    have hmem : δ • f ∈ φ ⁻¹' Metric.ball 0 1 := hsub fun x hx ↦ by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, smul_apply,
        smul_eq_mul, abs_mul, abs_of_pos hδ0]
      calc δ * |f x| ≤ δ * ε := mul_le_mul_of_nonneg_left (hf x hx) hδ0.le
        _ < ε := by nlinarith
    rw [mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, map_smul, smul_eq_mul,
      abs_mul, abs_of_pos hδ0, inv_mul_cancel₀ hpos.ne'] at hmem
    exact lt_irrefl _ hmem
  -- the compact absolutely convex set `C`
  set C := closure (absConvexHull ℝ (insert 0 (ε⁻¹ • B)))
  have hCc : IsCompact C := hK _ (isVonNBounded_absConvexHull
    ((isVonNBounded_smul_set hB ε⁻¹).insert 0))
  have hCac : AbsConvex ℝ C := (absConvex_absConvexHull).closure
  have hC0 : (0 : E) ∈ C := subset_closure (subset_absConvexHull (mem_insert _ _))
  have hφC : ∀ f : StrongDual ℝ E, (∀ x ∈ C, |f x| ≤ 1) → |φ f| ≤ 1 := fun f hf ↦ key f
    fun x hx ↦ by
      have := hf (ε⁻¹ • x) (subset_closure (subset_absConvexHull
        (mem_insert_of_mem _ (smul_mem_smul_set hx))))
      rw [map_smul, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε] at this
      exact (inv_mul_le_one₀ hε).1 this
  -- the finite intersection property
  obtain ⟨x, -, hx⟩ := hCc.inter_iInter_nonempty (fun f : StrongDual ℝ E ↦ {x | f x = φ f})
    (fun f ↦ isClosed_eq f.continuous continuous_const) fun u ↦ by
      obtain ⟨x, hxC, hx⟩ := exists_mem_eq_on_finset hCc hCac hC0 φ hφC u
      exact ⟨x, hxC, mem_iInter₂.2 hx⟩
  exact ⟨x, ContinuousLinearMap.ext fun f ↦ mem_iInter.1 hx f⟩

/-- **Separation from closed absolutely convex sets**: a point outside a closed absolutely convex
set `U ∋ 0` is separated from it by a functional bounded by `1` on `U`. -/
theorem exists_abs_le_one_lt {U : Set E} (hUc : IsClosed U) (hUac : AbsConvex ℝ U)
    (hU0 : (0 : E) ∈ U) {x : E} (hx : x ∉ U) :
    ∃ f : StrongDual ℝ E, (∀ y ∈ U, |f y| ≤ 1) ∧ 1 < f x := by
  obtain ⟨g, u, hgU, hgx⟩ := geometric_hahn_banach_closed_point hUac.2 hUc hx
  have hu : 0 < u := by simpa using hgU 0 hU0
  refine ⟨u⁻¹ • g, fun y hy ↦ ?_, ?_⟩
  · have h1 := hgU y hy
    have h2 := hgU (-y) (hUac.1.neg_mem_iff.2 hy)
    rw [map_neg] at h2
    rw [smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hu]
    exact (inv_mul_le_one₀ hu).2 (abs_le.2 ⟨by linarith, h1.le⟩)
  · rw [smul_apply, smul_eq_mul]
    exact (one_lt_inv_mul₀ hu).2 hgx

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- The polar `{f : |f| ≤ 1 on U}` of a `0`-neighbourhood is bounded in the strong dual. -/
theorem isVonNBounded_polar {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    IsVonNBounded ℝ {f : StrongDual ℝ E | ∀ y ∈ U, |f y| ≤ 1} := by
  refine ContinuousLinearMap.isVonNBounded_iff.2 fun s hs ↦ ?_
  obtain ⟨r, hr, hrs⟩ := (hs hU).exists_pos
  refine (NormedSpace.isVonNBounded_iff ℝ).2 ((Metric.isBounded_closedBall (x := (0 : ℝ))
    (r := r)).subset ?_)
  rintro _ ⟨f, hf, y, hy, rfl⟩
  obtain ⟨u, hu, rfl⟩ := hrs r (by rw [Real.norm_eq_abs, abs_of_pos hr]) hy
  change f (r • u) ∈ Metric.closedBall 0 r
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, map_smul, smul_eq_mul, abs_mul,
    abs_of_pos hr]
  exact mul_le_of_le_one_right hr.le (hf u hu)

omit [LocallyConvexSpace ℝ E] in
/-- **The evaluation map into the strong bidual of a barrelled space is continuous**: a bounded
subset of the strong dual is pointwise bounded, hence equicontinuous (Banach–Steinhaus). -/
theorem continuous_evalStrongDual [BarrelledSpace ℝ E] :
    Continuous (evalStrongDual : E → StrongDual ℝ (StrongDual ℝ E)) := by
  have hG : IsTopologicalAddGroup (StrongDual ℝ (StrongDual ℝ E)) := inferInstance
  have : ContinuousAdd (StrongDual ℝ (StrongDual ℝ E)) := hG.toContinuousAdd
  let η : E →+ StrongDual ℝ (StrongDual ℝ E) :=
    { toFun := evalStrongDual, map_zero' := by ext; simp, map_add' := fun _ _ ↦ by ext; simp }
  refine continuous_of_continuousAt_zero η ?_
  rw [ContinuousAt, map_zero]
  refine ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis (E := StrongDual ℝ E)
    (σ := RingHom.id ℝ) (Metric.nhds_basis_ball (x := (0 : ℝ)))).tendsto_right_iff).2
    fun ⟨𝔅, ε⟩ ⟨h𝔅, hε⟩ ↦ ?_
  let p : 𝔅 → Seminorm ℝ E := fun f ↦ (normSeminorm ℝ ℝ).comp (f : StrongDual ℝ E).toLinearMap
  have hp : ∀ f, Continuous (p f) := fun f ↦ continuous_norm.comp (f : StrongDual ℝ E).continuous
  have hbdd : BddAbove (range p) := by
    refine Seminorm.bddAbove_range_iff.2 fun x ↦ ?_
    have hx := ContinuousLinearMap.isVonNBounded_iff.1 h𝔅 {x} (isVonNBounded_singleton x)
    obtain ⟨r, hr⟩ := ((NormedSpace.isVonNBounded_iff ℝ).1 hx).subset_closedBall 0
    refine ⟨r, ?_⟩
    rintro _ ⟨f, rfl⟩
    have := hr ⟨f, f.2, x, rfl, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this
  -- the supremum `q = ⨆ f, p f` is a continuous seminorm
  set q : Seminorm ℝ E := ⨆ f, p f
  have hq : Continuous q := by
    have := Seminorm.continuous_iSup p hp hbdd
    rwa [← Seminorm.coe_iSup_eq hbdd] at this
  have hqx : ∀ x, ∀ f : 𝔅, p f x ≤ q x := fun x f ↦ by
    rw [Seminorm.iSup_apply hbdd]
    exact le_ciSup (Seminorm.bddAbove_range_iff.1 hbdd x) f
  have hq0 : {x | q x < ε} ∈ 𝓝 (0 : E) :=
    (isOpen_lt hq continuous_const).mem_nhds (by simp only [mem_ofPred_eq, map_zero]; exact hε)
  filter_upwards [hq0] with x hx f hf
  rw [Metric.mem_ball, dist_zero_right]
  exact (hqx x ⟨f, hf⟩).trans_lt hx

/-- **Barrelled spaces whose bounded sets are relatively compact are reflexive** (compare
[GN26, Proposition B.10.7]): the evaluation map is a continuous linear isomorphism onto the
strong bidual. It is onto by `exists_evalStrongDual_eq`, continuous by Banach–Steinhaus
(`continuous_evalStrongDual`), and open since the polar of a closed absolutely convex
`0`-neighbourhood is bounded and its own polar is the neighbourhood (`exists_abs_le_one_lt`). -/
theorem exists_continuousLinearEquiv_strongBidual [T2Space E] [BarrelledSpace ℝ E]
    (hK : ∀ B : Set E, IsVonNBounded ℝ B → IsCompact (closure B)) :
    ∃ e : E ≃L[ℝ] StrongDual ℝ (StrongDual ℝ E), ∀ x, e x = evalStrongDual x := by
  let η : E →ₗ[ℝ] StrongDual ℝ (StrongDual ℝ E) :=
    { toFun := evalStrongDual
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp }
  have hinj : Injective η := fun x y hxy ↦ by
    by_contra hne
    obtain ⟨f, hf⟩ := geometric_hahn_banach_point_point hne
    have := congrArg (fun φ : StrongDual ℝ (StrongDual ℝ E) ↦ φ f) hxy
    simp only [η, LinearMap.coe_mk, AddHom.coe_mk, evalStrongDual_apply] at this
    exact hf.ne this
  have hsurj : Surjective η := fun φ ↦ exists_evalStrongDual_eq hK φ
  let e₀ := LinearEquiv.ofBijective η ⟨hinj, hsurj⟩
  have hG : IsTopologicalAddGroup (StrongDual ℝ (StrongDual ℝ E)) := inferInstance
  have : ContinuousAdd (StrongDual ℝ (StrongDual ℝ E)) := hG.toContinuousAdd
  have hinv : Continuous e₀.symm := by
    refine continuous_of_continuousAt_zero e₀.symm.toLinearMap ?_
    rw [ContinuousAt, map_zero]
    intro U hU
    rw [Filter.mem_map]
    -- a closed absolutely convex `0`-neighbourhood inside `U`
    obtain ⟨V, ⟨hV, hVc⟩, hVU⟩ := (closed_nhds_basis (0 : E)).mem_iff.1 hU
    obtain ⟨W, ⟨hW, hWac⟩, hWV⟩ := (nhds_hasBasis_absConvex ℝ E).mem_iff.1 hV
    set U' := closure W
    have hU'n : U' ∈ 𝓝 (0 : E) := mem_of_superset hW subset_closure
    have hU'U : U' ⊆ U := (closure_minimal hWV hVc).trans hVU
    refine mem_of_superset ((ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (E := StrongDual ℝ E) (σ := RingHom.id ℝ)
      (Metric.nhds_basis_ball (x := (0 : ℝ)))).mem_of_mem
      (i := ({f | ∀ y ∈ U', |f y| ≤ 1}, 1)) ⟨isVonNBounded_polar hU'n, one_pos⟩) ?_
    intro φ hφ
    refine hU'U (by_contra fun hx ↦ ?_)
    obtain ⟨f, hfU, hfx⟩ := exists_abs_le_one_lt isClosed_closure hWac.closure
      (mem_of_mem_nhds hU'n) hx
    have h1 := hφ f hfU
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h1
    have h2 : φ f = f (e₀.symm φ) := by
      conv_lhs => rw [← e₀.apply_symm_apply φ]
      rfl
    rw [h2] at h1
    exact absurd (hfx.trans_le (le_abs_self _)) (not_lt.2 h1.le)
  exact ⟨{ e₀ with
    continuous_toFun := continuous_evalStrongDual
    continuous_invFun := hinv }, fun _ ↦ rfl⟩

end Reflexive

namespace LCDirectLimit

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {S : ℕ → Submodule ℝ V}
  [∀ n, TopologicalSpace (S n)] [∀ n, IsTopologicalAddGroup (S n)] [∀ n, ContinuousSMul ℝ (S n)]
  [∀ n, LocallyConvexSpace ℝ (S n)]

/-- **Silva spaces are `k_ω`-spaces** ([GN26, Proposition B.13.13(g)]), for `T₁`
sequential steps: the compact sets `k Lₚ` (with `Lₚ ⊆ S (p + 1)` witnessing the compactness of
`S p → S (p + 1)`) detect closed sets (`IsSilva.isClosed_of_isClosed_inter`), and their finite
unions absorb every compact set, which is bounded in some step (compact regularity). -/
theorem IsSilva.isKOmegaSpace [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    (hS : IsSilva S) : IsKOmegaSpace (LCDirectLimit S) := by
  have : T2Space (LCDirectLimit S) := hS.t2Space
  choose L hL hLn using hS.isCompactOperator_succ
  set C : ℕ → ℕ → Set (LCDirectLimit S) := fun p k ↦ incl S (p + 1) '' ((k : ℝ) • L p)
  have hCc : ∀ p k, IsCompact (C p k) := fun p k ↦
    ((hL p).smul _).image (continuous_incl S (p + 1))
  refine ⟨compactlyGeneratedSpace_of_isClosed_of_t2 fun F hF ↦
    hS.isClosed_of_isClosed_inter L hLn fun p k ↦ hF _ (hCc p k), ?_⟩
  -- the finite unions `D N` of the `C p k`
  set D : ℕ → Set (LCDirectLimit S) := fun N ↦ ⋃ p ∈ Iic N, ⋃ k ∈ Iic N, C p k
  refine ⟨D, fun N ↦ (finite_Iic N).isCompact_biUnion fun p _ ↦
    (finite_Iic N).isCompact_biUnion fun k _ ↦ hCc p k, fun K hK ↦ ?_⟩
  obtain ⟨n, hn, hKn⟩ := hS.exists_subset_isCompact hK
  -- `K` is absorbed in `S n` by the `0`-neighbourhood witnessing compactness
  obtain ⟨r, hr⟩ := absorbs_iff_norm.1 ((hKn.isVonNBounded ℝ) (hLn n))
  set k : ℕ := ⌈r⌉₊ + 1
  have hk : r ≤ ‖(k : ℝ)‖ := by
    rw [Real.norm_natCast]
    exact (Nat.le_ceil r).trans (by exact_mod_cast Nat.le_succ _)
  refine ⟨max n k, fun x hx ↦ ?_⟩
  obtain ⟨w, hw, hwx⟩ := hr _ hk (show (⟨x, hn x hx⟩ : S n) ∈ incl S n ⁻¹' K from hx)
  refine mem_iUnion₂.2 ⟨n, mem_Iic.2 (le_max_left _ _), mem_iUnion₂.2 ⟨k,
    mem_Iic.2 (le_max_right _ _), (k : ℝ) • Submodule.inclusion (hS.mono (Nat.le_succ n)) w,
    smul_mem_smul_set hw, ?_⟩⟩
  exact congrArg Subtype.val hwx

/-- **Hemicompactness for bounded sets**: in a Silva space with `T₁` sequential steps having
bounded `0`-neighbourhoods, some sequence of compact sets absorbs every bounded set (bounded sets
are relatively compact, Proposition B.13.13(d)). -/
theorem IsSilva.exists_isCompact_absorbing [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    (hS : IsSilva S) (hbdd : ∀ n, ∃ U ∈ 𝓝 (0 : S n), IsVonNBounded ℝ U) :
    ∃ K : ℕ → Set (LCDirectLimit S), (∀ N, IsCompact (K N)) ∧
      ∀ B, IsVonNBounded ℝ B → ∃ N, B ⊆ K N := by
  obtain ⟨K, hKc, hK⟩ := hS.isKOmegaSpace.2
  refine ⟨K, hKc, fun B hB ↦ ?_⟩
  obtain ⟨N, hN⟩ := hK _ (hS.isCompact_closure_of_isVonNBounded hbdd hB)
  exact ⟨N, subset_closure.trans hN⟩

/-- **The strong dual of a Silva space is metrizable** ([GN26, Proposition B.13.13(f)]):
the sets `{f : |f| < 1/(m+1) on K N}`, for a sequence `K N` of compact sets absorbing the bounded
sets, form a countable basis of `0`-neighbourhoods. -/
theorem IsSilva.metrizableSpace_strongDual [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    (hS : IsSilva S) (hbdd : ∀ n, ∃ U ∈ 𝓝 (0 : S n), IsVonNBounded ℝ U) :
    TopologicalSpace.MetrizableSpace (StrongDual ℝ (LCDirectLimit S)) := by
  obtain ⟨K, hKc, hK⟩ := hS.exists_isCompact_absorbing hbdd
  have hb := ContinuousLinearMap.hasBasis_nhds_zero_of_basis (E := LCDirectLimit S)
    (σ := RingHom.id ℝ) (Metric.nhds_basis_ball (x := (0 : ℝ)))
  have hb' : (𝓝 (0 : StrongDual ℝ (LCDirectLimit S))).HasBasis (fun _ : ℕ × ℕ ↦ True)
      fun Nm ↦ {f : StrongDual ℝ (LCDirectLimit S) |
        ∀ x ∈ K Nm.1, f x ∈ Metric.ball (0 : ℝ) (1 / ((Nm.2 : ℝ) + 1))} := by
    refine hb.to_hasBasis (fun Bε ⟨hB, hε⟩ ↦ ?_) fun Nm _ ↦
      ⟨(K Nm.1, 1 / ((Nm.2 : ℝ) + 1)), ⟨(hKc Nm.1).isVonNBounded ℝ, by positivity⟩, subset_rfl⟩
    obtain ⟨N, hN⟩ := hK _ hB
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    exact ⟨(N, m), trivial, fun f hf x hx ↦
      Metric.ball_subset_ball hm.le (hf x (hN hx))⟩
  have : (𝓝 (0 : StrongDual ℝ (LCDirectLimit S))).IsCountablyGenerated := hb'.isCountablyGenerated
  have : (𝓤 (StrongDual ℝ (LCDirectLimit S))).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  have : T2Space (LCDirectLimit S) := hS.t2Space
  exact UniformSpace.metrizableSpace

/-- **The strong dual of a Silva space is complete** ([GN26, Proposition B.13.13(f)]), for
`T₁` sequential steps: a Silva space is a `k`-space (Proposition B.13.13(g)), so its topology is
coherent with the bounded sets and uniform limits on bounded sets of continuous linear functionals
are continuous. -/
theorem IsSilva.completeSpace_strongDual [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    (hS : IsSilva S) : CompleteSpace (StrongDual ℝ (LCDirectLimit S)) := by
  have := hS.isKOmegaSpace.1
  exact ContinuousLinearMap.completeSpace
    (CompactlyCoherentSpace.isCoherentWith.mono fun K (hK : IsCompact K) ↦ hK.isVonNBounded ℝ)

/-- **Silva spaces are reflexive** ([GN26, Proposition B.13.13(e)]), for `T₁` sequential
barrelled steps having bounded `0`-neighbourhoods (for instance Banach spaces): a Silva space is
barrelled (Lemma B.13.6(e)) and its bounded sets are relatively compact (Proposition
B.13.13(d)). -/
theorem IsSilva.exists_continuousLinearEquiv_strongBidual [∀ n, T1Space (S n)]
    [∀ n, SequentialSpace (S n)] [∀ n, BarrelledSpace ℝ (S n)] (hS : IsSilva S)
    (hbdd : ∀ n, ∃ U ∈ 𝓝 (0 : S n), IsVonNBounded ℝ U) :
    ∃ e : LCDirectLimit S ≃L[ℝ] StrongDual ℝ (StrongDual ℝ (LCDirectLimit S)),
      ∀ x, e x = evalStrongDual x := by
  have : T2Space (LCDirectLimit S) := hS.t2Space
  have : BarrelledSpace ℝ (LCDirectLimit S) := barrelledSpace S
  exact LocallyConvex.Analysis.exists_continuousLinearEquiv_strongBidual
    fun _ hB ↦ hS.isCompact_closure_of_isVonNBounded hbdd hB

/-- **Silva spaces are complete** ([GN26, Proposition B.13.13(f)]), under the hypotheses of
`exists_continuousLinearEquiv_strongBidual`: the strong dual is metrizable, so the strong bidual
is complete, and the Silva space is isomorphic to it. -/
theorem IsSilva.completeSpace [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    [∀ n, BarrelledSpace ℝ (S n)] (hS : IsSilva S)
    (hbdd : ∀ n, ∃ U ∈ 𝓝 (0 : S n), IsVonNBounded ℝ U) : CompleteSpace (LCDirectLimit S) := by
  have := hS.metrizableSpace_strongDual hbdd
  obtain ⟨e, -⟩ := hS.exists_continuousLinearEquiv_strongBidual hbdd
  have h1 : UniformContinuous e := uniformContinuous_addMonoidHom_of_continuous e.continuous
  have h2 : UniformContinuous e.symm :=
    uniformContinuous_addMonoidHom_of_continuous e.symm.continuous
  have hu : IsUniformInducing e := (UniformEquiv.mk e.toEquiv h1 h2).isUniformInducing
  exact (hu.completeSpace_congr e.surjective).2 inferInstance

end LCDirectLimit

end LocallyConvex.Analysis

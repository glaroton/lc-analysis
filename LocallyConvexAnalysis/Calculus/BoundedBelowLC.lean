/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.BoundedBelow
public import LocallyConvexAnalysis.Calculus.Integral.Existence

/-!
# Maps with uniformly injective derivative reflect smoothness: the locally convex case

This file is a locally convex version of `LocallyConvexAnalysis.Calculus.BoundedBelow`, where a
smooth map `j : E → F` between normed spaces (`E` complete) whose derivative is bounded below is
shown to reflect smoothness of continuous maps: if `γ` is continuous and `j ∘ γ` is `C^k`, then `γ`
is `C^k`.

For locally convex `E` and `F` the analogue of "bounded below" for a single continuous linear
map is "topological embedding": for every continuous seminorm `p` on `E` there are a continuous
seminorm `q` on `F` and `C ≥ 0` with `p w ≤ C q(L w)`. The proof needs this uniformly near each
point, and also for convex combinations of derivatives, which is our hypothesis:

**(H)** `EquiEmbeddingNear j x₀`: there is a neighborhood `V` of `x₀` such that for every
continuous seminorm `p` on `E` there are a continuous seminorm `q` on `F` and `C ≥ 0` with
`p w ≤ C q(z)` for every `w` and every `z` in the closed convex hull of `{dj(y)(w) : y ∈ V}`
(`EquiEmbeddingOn`). Equivalently, `p w ≤ C q(∑ λᵢ dj(yᵢ)(w))` for all finite convex
combinations with `yᵢ ∈ V`.

## Main results

* `ContDiffMBOn.of_comp_of_equiEmbedding`: let `E`, `F` be Hausdorff locally convex spaces,
  `E` sequentially complete, `U ⊆ E` open, `j` of class `C^2` and `C^k` on `U` with (H) at every
  point of `U`. If `γ : W → U` is continuous on an open subset `W` of a locally convex space and
  `j ∘ γ` is `C^k`, then `γ` is `C^k`. `ContDiffMBOn.of_comp_of_equiEmbedding_of_smooth` is the
  version for smooth `j`, with the shape of `ContDiffMBOn.of_comp_of_boundedBelow`.
* `ContDiffMBOn.of_dMB_eq_of_equiEmbedding`: the linear bootstrap, if `dj(γ q)(z q) = w q` with
  `γ, w` of class `C^k`, `z` continuous and `j` of class `C^{k+1}`, then `z` is `C^k`.
* `equiEmbeddingNear_of_boundedBelow`: in normed spaces (H) is automatic at every point where
  `dj` is bounded below, by continuity of `x ↦ dj(x)` in the operator norm. Hence
  `ContDiffMBOn.of_comp_of_boundedBelow_pointwise`, the Banach theorem with a lower bound that
  may depend on the point, which contains `ContDiffMBOn.of_comp_of_boundedBelow`.

## Implementation notes

The proof follows the Banach one, with three changes.

1. *Bounded difference quotients.* For `g_t = t⁻¹ (γ(s + t h) - γ(s))`, the mean value
   inclusion (`ContDiffMBOn.quotient_mem_closure_convexHull`) puts the difference quotient of
   `j ∘ γ` in the closed convex hull of `{dj(y)(g_t) : y ∈ [γ(s), γ(s + t h)]}`; for small `t`
   the segment lies in `V`, and (H) bounds `p(g_t)` by `C q` of a convergent quantity. This is
   where convex combinations enter (`ContDiffMBOn.exists_tendsto_of_equiEmbedding`).
2. *Second order term.* The Banach proof uses strict Fréchet differentiability. Here joint
   continuity of `d²j` at `(x, 0, 0)` and homogeneity give a bilinear bound
   `q(d²j(z)(u, v)) ≤ r(u) r(v)` near `x` (`ContDiffMBOn.exists_d2_seminorm_bound`), so the
   difference between the quotient of `j ∘ γ` and `dj(γ s)(g_t)` is at most
   `r(γ(s + t h) - γ(s)) r(g_t) → 0`. This is why `j` is assumed `C^2` (the Banach theorem
   assumes `j` smooth).
3. *Limits.* `dj(γ s)(g_t)` converges and `dj(γ s)` is an embedding, so `g_t` is Cauchy along a
   sequence `t_n → 0`; it converges because `E` is sequentially complete (`SeqComplete`), and
   then along the whole filter (`exists_tendsto_of_seminorm_le`). Continuity of the derivative
   uses (H) only at single points, with joint continuity of `dj`
   (`ContDiffMBOn.continuousOn_of_dMB_eq`).

The induction on `k` mirrors the Banach file: the derivative `dγ` solves
`dj(γ p₁)(dγ p) = d(j ∘ γ) p`, and the derivative of a solution `z` of
`dj(γ q)(z q) = w q` solves an equation of the same form with right-hand side
`dw - d²j(γ)(dγ, z)`.

**Subtleties.**

* (H) is not a consequence of each `dj(x)` being an embedding. In the Fréchet space of rapidly
  decreasing sequences there is a smooth family of linear automorphisms `L(t)` with
  `L(0) = id` whose lower bounds are not locally uniform (the inverses are not equicontinuous
  near `t = 0`): see `Counterexamples.RapidDecay.counterexample`
  (`LocallyConvexAnalysis/Counterexamples/BoundedBelowStability.lean`). So in Fréchet spaces the
  pointwise lower bound does not propagate to a neighborhood, and the uniformity has to be
  assumed. Pointwise embeddings (without (H)) do not suffice for the conclusion: on
  `ℝ × s` the map `j(t, x) = (t, L(t) x)`, for a variant of that family, is a smooth bijection
  whose derivative is a linear automorphism at every point, and there is a continuous curve `γ`
  with `j ∘ γ` affine and `γ` not `C¹` (`Counterexamples.RapidDecay.not_reflect_smoothness`,
  `LocallyConvexAnalysis/Counterexamples/ReflectSmoothness.lean`).
* In normed spaces the convex combinations come for free: if `‖dj(y) - dj(x₀)‖ < m / 2` on `V`,
  then every closed convex combination of the `dj(y)(w)` is within `m / 2 ‖w‖` of `dj(x₀)(w)`.
* Sequential completeness of `E` is used only to produce the limits of difference quotients;
  the filter `𝓝[≠] 0` on `ℝ` is countably generated, so sequences suffice.

**Source.** We found no source for this locally convex statement; it was written for this
repository by adapting the Banach proof. We do not claim it is new.
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### Continuous seminorms on a locally convex space -/

section Seminorms

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Every neighborhood of `0` in a locally convex space contains the open unit ball of a
continuous seminorm. -/
theorem exists_continuous_seminorm_lt_one_subset {N : Set E} (hN : N ∈ 𝓝 (0 : E)) :
    ∃ p : Seminorm ℝ E, Continuous p ∧ ∀ v, p v < 1 → v ∈ N := by
  obtain ⟨s, ⟨hs0, hso, hsa⟩, hsN⟩ := (nhds_hasBasis_absConvex_open ℝ E).mem_iff.mp hN
  let S : AbsConvexOpenSets ℝ E := ⟨s, hs0, hso, hsa⟩
  refine ⟨gaugeSeminormFamily ℝ E S, with_gaugeSeminormFamily.continuous_seminorm S,
    fun v hv ↦ hsN ?_⟩
  have hball : v ∈ (gaugeSeminormFamily ℝ E S).ball 0 1 := by
    rwa [Seminorm.mem_ball, sub_zero]
  rw [gaugeSeminormFamily_ball] at hball
  exact hball

/-- Convergence in a locally convex space can be tested on continuous seminorms. -/
theorem tendsto_of_forall_seminorm {ι : Type*} {l : Filter ι} {g : ι → E} {y : E}
    (h : ∀ p : Seminorm ℝ E, Continuous p → ∀ ε > 0, ∀ᶠ i in l, p (g i - y) < ε) :
    Tendsto g l (𝓝 y) := by
  rw [tendsto_def]
  intro N hN
  have hN0 : (fun v ↦ y + v) ⁻¹' N ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
  obtain ⟨p, hp, hpN⟩ := exists_continuous_seminorm_lt_one_subset hN0
  filter_upwards [h p hp 1 one_pos] with i hi
  simpa using hpN _ hi

omit [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
/-- Conversely, continuous seminorms detect convergence. -/
theorem eventually_seminorm_sub_lt {ι : Type*} {l : Filter ι} {g : ι → E} {y : E}
    (hg : Tendsto g l (𝓝 y)) {p : Seminorm ℝ E} (hp : Continuous p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, p (g i - y) < ε := by
  have : Tendsto (fun i ↦ p (g i - y)) l (𝓝 (p (y - y))) :=
    (hp.tendsto _).comp (hg.sub_const y)
  rw [sub_self, map_zero] at this
  exact this.eventually (gt_mem_nhds hε)

end Seminorms

/-! ### The hypothesis -/

section Hypothesis

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type w} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The derivatives `dj(y)`, `y ∈ V`, are *uniformly injective on closed convex combinations*:
for every continuous seminorm `p` on `E` there are a continuous seminorm `q` on `F` and `C ≥ 0`
such that `p w ≤ C q(z)` for every `w` and every `z` in the closed convex hull of
`{dj(y)(w) : y ∈ V}`. In particular (taking `z = dj(y)(w)`) each `dj(y)`, `y ∈ V`, is a
topological embedding, with constants independent of `y`. -/
def EquiEmbeddingOn (j : E → F) (V : Set E) : Prop :=
  ∀ p : Seminorm ℝ E, Continuous p → ∃ q : Seminorm ℝ F, Continuous q ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : E, ∀ z ∈ closure (convexHull ℝ ((fun y ↦ dMB j (y, w)) '' V)), p w ≤ C * q z

/-- `EquiEmbeddingOn j V` for some neighborhood `V` of `x`. -/
def EquiEmbeddingNear (j : E → F) (x : E) : Prop :=
  ∃ V ∈ 𝓝 x, EquiEmbeddingOn j V

variable {j : E → F} {V V' : Set E}

theorem EquiEmbeddingOn.mono (h : EquiEmbeddingOn j V) (hV : V' ⊆ V) : EquiEmbeddingOn j V' := by
  intro p hp
  obtain ⟨q, hq, C, hC, hpq⟩ := h p hp
  exact ⟨q, hq, C, hC, fun w z hz ↦
    hpq w z (closure_mono (convexHull_mono (image_mono hV)) hz)⟩

/-- The lower bound at the points of `V`, uniformly in the point. -/
theorem EquiEmbeddingOn.exists_bound (h : EquiEmbeddingOn j V) {p : Seminorm ℝ E}
    (hp : Continuous p) : ∃ q : Seminorm ℝ F, Continuous q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ V, ∀ w, p w ≤ C * q (dMB j (y, w)) := by
  obtain ⟨q, hq, C, hC, hpq⟩ := h p hp
  exact ⟨q, hq, C, hC, fun y hy w ↦
    hpq w _ (subset_closure (subset_convexHull ℝ _ ⟨y, hy, rfl⟩))⟩

end Hypothesis

/-! ### Linear preliminaries -/

section Linear

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {F : Type w} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- If `L` is a topological embedding with seminorm estimates and `L z_i → R`, then `z_i`
converges to a solution of `L D = R`, provided `E` is sequentially complete and the filter is
countably generated. This replaces `exists_tendsto_of_boundedBelow`. -/
theorem exists_tendsto_of_seminorm_le [SeqComplete E] {L : E →L[ℝ] F}
    (hL : ∀ p : Seminorm ℝ E, Continuous p → ∃ q : Seminorm ℝ F, Continuous q ∧ ∃ C : ℝ,
      0 ≤ C ∧ ∀ w, p w ≤ C * q (L w))
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {g : ι → E} {R : F}
    (h : Tendsto (fun i ↦ L (g i)) l (𝓝 R)) : ∃ D, Tendsto g l (𝓝 D) ∧ L D = R := by
  -- the key estimate `p (g i - g i') ≤ C (q (L g i - R) + q (L g i' - R))`
  have key : ∀ p : Seminorm ℝ E, Continuous p → ∃ q : Seminorm ℝ F, Continuous q ∧ ∃ C : ℝ,
      0 ≤ C ∧ ∀ a b : E, p (a - b) ≤ C * (q (L a - R) + q (L b - R)) := by
    intro p hp
    obtain ⟨q, hq, C, hC, hpq⟩ := hL p hp
    refine ⟨q, hq, C, hC, fun a b ↦ (hpq _).trans ?_⟩
    gcongr
    calc q (L (a - b)) = q ((L a - R) - (L b - R)) := by rw [map_sub]; congr 1; abel
      _ ≤ _ := map_sub_le_add q _ _
  obtain ⟨s, hs⟩ := l.exists_seq_tendsto
  have hLs : Tendsto (fun n ↦ L (g (s n))) atTop (𝓝 R) := h.comp hs
  obtain ⟨D, hD⟩ : ∃ D, Tendsto (fun n ↦ g (s n)) atTop (𝓝 D) := by
    refine SeqComplete.exists_tendsto _ fun N hN ↦ ?_
    obtain ⟨p, hp, hpN⟩ := exists_continuous_seminorm_lt_one_subset hN
    obtain ⟨q, hq, C, hC, hpq⟩ := key p hp
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp
      (eventually_seminorm_sub_lt hLs hq (show (0 : ℝ) < 1 / (2 * (C + 1)) by positivity))
    refine ⟨n₀, fun m hm n hn ↦ hpN _ ((hpq _ _).trans_lt ?_)⟩
    have h1 := hn₀ n hn
    have h2 := hn₀ m hm
    calc C * (q (L (g (s n)) - R) + q (L (g (s m)) - R))
        ≤ C * (1 / (2 * (C + 1)) + 1 / (2 * (C + 1))) := by gcongr
      _ = C / (C + 1) := by field_simp; ring
      _ < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hLD : L D = R := tendsto_nhds_unique ((L.continuous.tendsto D).comp hD) hLs
  refine ⟨D, tendsto_of_forall_seminorm fun p hp ε hε ↦ ?_, hLD⟩
  obtain ⟨q, hq, C, hC, hpq⟩ := hL p hp
  filter_upwards [eventually_seminorm_sub_lt h hq (show 0 < ε / (C + 1) by positivity)]
    with i hi
  calc p (g i - D) ≤ C * q (L (g i - D)) := hpq _
    _ = C * q (L (g i) - R) := by rw [map_sub, hLD]
    _ ≤ C * (ε / (C + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] [IsTopologicalAddGroup F] in
/-- Sublevel sets of a continuous seminorm are closed and convex. -/
theorem Seminorm.isClosed_convex_setOf_le {q : Seminorm ℝ F} (hq : Continuous q) (c : ℝ) :
    IsClosed {v | q v ≤ c} ∧ Convex ℝ {v | q v ≤ c} :=
  ⟨isClosed_le hq continuous_const, by
    simpa only [Seminorm.closedBall_zero_eq] using q.convex_closedBall 0 c⟩

end Linear

/-! ### First-order estimates -/

section Main

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type w} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {j : E → F} {U : Set E}

omit [LocallyConvexSpace ℝ E] [T2Space E] in
theorem ContDiffMBOn.dMB_sub_right (hU : IsOpen U) (hj : ContDiffMBOn 1 j U) {y : E}
    (hy : y ∈ U) (a b : E) : dMB j (y, a - b) = dMB j (y, a) - dMB j (y, b) := by
  obtain ⟨L, hL⟩ := hj.exists_clm hU hy
  rw [← hL, ← hL, ← hL, map_sub]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- Under the hypothesis, `dj(x)` is a continuous linear map with seminorm lower bounds. -/
theorem EquiEmbeddingNear.exists_clm (hU : IsOpen U) (hj : ContDiffMBOn 1 j U) {x : E}
    (hx : x ∈ U) (hH : EquiEmbeddingNear j x) :
    ∃ L : E →L[ℝ] F, (∀ w, L w = dMB j (x, w)) ∧ ∀ p : Seminorm ℝ E, Continuous p →
      ∃ q : Seminorm ℝ F, Continuous q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, p w ≤ C * q (L w) := by
  obtain ⟨L, hL⟩ := hj.exists_clm hU hx
  obtain ⟨V, hV, hHV⟩ := hH
  refine ⟨L, hL, fun p hp ↦ ?_⟩
  obtain ⟨q, hq, C, hC, hpq⟩ := hHV.exists_bound hp
  exact ⟨q, hq, C, hC, fun w ↦ by rw [hL]; exact hpq x (mem_of_mem_nhds hV) w⟩

omit [T2Space E] in
/-- **Continuity of solutions.** If `dj(γ a)(z a) = r a` on `W`, with `γ` and `r` continuous,
then `z` is continuous. This replaces `continuousOn_of_boundedBelow`, which needs continuity of
`x ↦ dj(x)` in the operator norm. -/
theorem ContDiffMBOn.continuousOn_of_dMB_eq (hU : IsOpen U) (hj : ContDiffMBOn 1 j U)
    (hH : ∀ x ∈ U, EquiEmbeddingNear j x) {X : Type*} [TopologicalSpace X] {W : Set X}
    {γ z : X → E} {r : X → F} (hγ : ContinuousOn γ W) (hγU : MapsTo γ W U)
    (hr : ContinuousOn r W) (heq : ∀ a ∈ W, dMB j (γ a, z a) = r a) : ContinuousOn z W := by
  intro a ha
  refine tendsto_of_forall_seminorm fun p hp ε hε ↦ ?_
  obtain ⟨V, hV, hHV⟩ := hH _ (hγU ha)
  obtain ⟨q, hq, C, hC, hpq⟩ := hHV.exists_bound hp
  have hdc : ContinuousAt (dMB j) (γ a, z a) :=
    (hj.2.2 : ContinuousOn (dMB j) (U ×ˢ univ)).continuousAt
      (prod_mem_nhds (hU.mem_nhds (hγU ha)) univ_mem)
  have hlim : Tendsto (fun a' ↦ r a' - dMB j (γ a', z a)) (𝓝[W] a) (𝓝 0) := by
    have h1 : Tendsto (fun a' ↦ dMB j (γ a', z a)) (𝓝[W] a) (𝓝 (r a)) := by
      rw [← heq a ha]
      exact hdc.tendsto.comp ((hγ a ha).prodMk_nhds tendsto_const_nhds)
    simpa using (hr a ha).tendsto.sub h1
  filter_upwards [self_mem_nhdsWithin, hγ a ha hV,
    eventually_seminorm_sub_lt hlim hq (show 0 < ε / (C + 1) by positivity)] with a' ha' hV' hlt
  rw [sub_zero] at hlt
  calc p (z a' - z a) ≤ C * q (dMB j (γ a', z a' - z a)) := hpq _ hV' _
    _ = C * q (r a' - dMB j (γ a', z a)) := by
        rw [hj.dMB_sub_right hU (hγU ha'), heq a' ha']
    _ ≤ C * (ε / (C + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

/-! ### Second-order estimates -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Homogeneity of `d²j(y)(u, v) = dMB (dMB j) ((y, v), (u, 0))` in `u`. -/
theorem ContDiffMBOn.d2_smul_dir (hj : ContDiffMBOn 2 j U) {y : E} (hy : y ∈ U) (v u : E)
    (c : ℝ) : dMB (dMB j) ((y, v), (c • u, 0)) = c • dMB (dMB j) ((y, v), (u, 0)) := by
  have hdf : ContDiffMBOn 1 (dMB j) (U ×ˢ univ) := hj.2.2
  have := hdf.dMB_smul (x := (y, v)) ⟨hy, mem_univ _⟩ c (u, 0)
  simpa [Prod.smul_mk] using this

omit [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- Homogeneity of `d²j(y)(u, v) = dMB (dMB j) ((y, v), (u, 0))` in `v`. -/
theorem ContDiffMBOn.d2_smul_vec (hU : IsOpen U) (hj : ContDiffMBOn 2 j U) {y : E}
    (hy : y ∈ U) (v u : E) (c : ℝ) :
    dMB (dMB j) ((y, c • v), (u, 0)) = c • dMB (dMB j) ((y, v), (u, 0)) := by
  have hj1 : ContDiffMBOn 1 j U := hj.of_le (by omega)
  have hdf : ContDiffMBOn 1 (dMB j) (U ×ˢ univ) := hj.2.2
  have hline : ∀ᶠ t in 𝓝[≠] (0 : ℝ), y + t • u ∈ U := by
    have : Tendsto (fun t : ℝ ↦ y + t • u) (𝓝 0) (𝓝 y) := by
      have hc : Continuous fun t : ℝ ↦ y + t • u := by fun_prop
      simpa using hc.tendsto 0
    exact nhdsWithin_le_nhds (this.eventually (hU.mem_nhds hy))
  have h1 : HasDirDerivAt (dMB j) (y, c • v) (u, 0) (c • dMB (dMB j) ((y, v), (u, 0))) := by
    refine ((hdf.2.1 (y, v) ⟨hy, mem_univ _⟩ (u, 0)).const_smul c).congr' ?_
    filter_upwards [hline] with t ht
    simp only [Prod.mk_add_mk, Prod.smul_mk, smul_zero, add_zero, smul_sub]
    rw [← hj1.dMB_smul ht, ← hj1.dMB_smul hy]
  exact h1.dMB_eq

omit [T2Space E] [IsTopologicalAddGroup F] [LocallyConvexSpace ℝ F] in
/-- **Local bilinear bound for the second derivative.** For every continuous seminorm `q` on
`F` there are a neighborhood `N ⊆ U` of `x` and a continuous seminorm `r` on `E` with
`q (d²j(z)(u, v)) ≤ r u * r v` for `z ∈ N`. Only joint continuity of `d²j` at `(x, 0, 0)` and
homogeneity are used. -/
theorem ContDiffMBOn.exists_d2_seminorm_bound (hU : IsOpen U) (hj : ContDiffMBOn 2 j U)
    {x : E} (hx : x ∈ U) {q : Seminorm ℝ F} (hq : Continuous q) :
    ∃ N ∈ 𝓝 x, N ⊆ U ∧ ∃ r : Seminorm ℝ E, Continuous r ∧
      ∀ z ∈ N, ∀ u v, q (dMB (dMB j) ((z, v), (u, 0))) ≤ r u * r v := by
  have hdf : ContDiffMBOn 1 (dMB j) (U ×ˢ univ) := hj.2.2
  set B : E × E × E → F := fun a ↦ dMB (dMB j) ((a.1, a.2.2), (a.2.1, 0)) with hB
  have hB0 : B (x, 0, 0) = 0 := by
    have := hj.d2_smul_dir hx 0 0 0
    simpa [hB] using this
  have hBc : ContinuousAt B (x, 0, 0) := by
    have h0 : ContinuousOn (dMB (dMB j)) ((U ×ˢ univ) ×ˢ univ) := hdf.2.2
    have h1 : ContinuousAt (dMB (dMB j)) ((x, (0 : E)), ((0 : E), (0 : E))) :=
      h0.continuousAt (prod_mem_nhds (prod_mem_nhds (hU.mem_nhds hx) univ_mem) univ_mem)
    have hφ : Continuous fun a : E × E × E ↦ ((a.1, a.2.2), (a.2.1, (0 : E))) := by fun_prop
    exact ContinuousAt.comp (g := dMB (dMB j))
      (f := fun a : E × E × E ↦ ((a.1, a.2.2), (a.2.1, (0 : E)))) (x := (x, (0 : E), (0 : E)))
      h1 hφ.continuousAt
  have hpre : B ⁻¹' {v | q v < 1} ∈ 𝓝 (x, (0 : E), (0 : E)) :=
    hBc.preimage_mem_nhds (by
      rw [hB0]; exact (isOpen_lt hq continuous_const).mem_nhds (by simp))
  obtain ⟨N, hN, M, hM, hNM⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨M₁, hM₁, M₂, hM₂, hM12⟩ := mem_nhds_prod_iff.mp hM
  obtain ⟨r, hr, hrM⟩ := exists_continuous_seminorm_lt_one_subset (inter_mem hM₁ hM₂)
  refine ⟨N ∩ U, inter_mem hN (hU.mem_nhds hx), inter_subset_right, r, hr, fun z hz u v ↦ ?_⟩
  have hε' : ∀ ε > 0, q (dMB (dMB j) ((z, v), (u, 0))) ≤ (r u + ε) * (r v + ε) := by
    intro ε hε
    have ha : 0 < r u + ε := by positivity
    have hb : 0 < r v + ε := by positivity
    have hu' : r ((r u + ε)⁻¹ • u) < 1 := by
      rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.2 ha.le), inv_mul_lt_iff₀ ha]
      linarith
    have hv' : r ((r v + ε)⁻¹ • v) < 1 := by
      rw [map_smul_eq_mul, Real.norm_of_nonneg (inv_nonneg.2 hb.le), inv_mul_lt_iff₀ hb]
      linarith
    have hmem := hNM (mk_mem_prod hz.1 (hM12 (mk_mem_prod (hrM _ hu').1 (hrM _ hv').2)))
    simp only [mem_preimage, mem_ofPred_eq, hB] at hmem
    rw [hj.d2_smul_dir hz.2, hj.d2_smul_vec hU hz.2, smul_smul, map_smul_eq_mul,
      Real.norm_of_nonneg (by positivity), ← mul_inv, inv_mul_lt_iff₀ (by positivity),
      mul_one] at hmem
    exact hmem.le
  have ht : Tendsto (fun ε : ℝ ↦ (r u + ε) * (r v + ε)) (𝓝[>] 0) (𝓝 (r u * r v)) := by
    have hc : Continuous fun ε : ℝ ↦ (r u + ε) * (r v + ε) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ hε' ε hε)

omit [LocallyConvexSpace ℝ E] [T2Space E] [T2Space F] in
/-- Lipschitz estimate for `y ↦ dj(y)(v)` on a convex set where the bilinear bound holds. -/
theorem ContDiffMBOn.seminorm_dMB_sub_le (hj : ContDiffMBOn 2 j U) {N : Set E} (hNU : N ⊆ U)
    (hNc : Convex ℝ N) {q : Seminorm ℝ F} (hq : Continuous q) {r : Seminorm ℝ E}
    (hb : ∀ z ∈ N, ∀ u v, q (dMB (dMB j) ((z, v), (u, 0))) ≤ r u * r v) {x y : E}
    (hx : x ∈ N) (hy : y ∈ N) (v : E) :
    q (dMB j (y, v) - dMB j (x, v)) ≤ r (y - x) * r v := by
  have hdf : ContDiffMBOn 1 (dMB j) (U ×ˢ univ) := hj.2.2
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • (y - x) ∈ N := fun s hs ↦
    hNc.add_smul_mem hx (by simpa using hy) hs
  have hd : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt (fun y' ↦ dMB j (y', v)) (x + s • (y - x))
      (y - x) (dMB (dMB j) ((x + s • (y - x), v), (y - x, 0))) := fun s hs ↦ by
    refine (hdf.2.1 _ ⟨hNU (hseg s hs), mem_univ _⟩ (y - x, 0)).congr fun t ↦ ?_
    simp
  have hDc : ContinuousOn (fun s : ℝ ↦ dMB (dMB j) ((x + s • (y - x), v), (y - x, (0 : E))))
      (Icc 0 1) := by
    have h0 : ContinuousOn (dMB (dMB j)) ((U ×ˢ univ) ×ˢ univ) := hdf.2.2
    exact h0.comp (by fun_prop : Continuous fun s : ℝ ↦
      ((x + s • (y - x), v), (y - x, (0 : E)))).continuousOn
      fun s hs ↦ ⟨⟨hNU (hseg s hs), mem_univ _⟩, mem_univ _⟩
  obtain ⟨hcl, hcv⟩ := Seminorm.isClosed_convex_setOf_le hq (r (y - x) * r v)
  have hmem := sub_mem_of_hasDirDerivAt hd hDc hcv hcl (fun s hs ↦ hb _ (hseg s hs) _ _)
  simpa using hmem

omit [T2Space E] in
/-- **Difference quotients.** Let `j` be `C^2` near `x` with the hypothesis at `x`, and let
`d i → 0` and `τ i ≠ 0` be such that `(τ i)⁻¹ • (j (x + d i) - j x) → R`. Then the quotients
`(τ i)⁻¹ • d i` converge to a solution `D` of `dj(x)(D) = R`.

Proof: by the mean value inclusion the quotients of `j` lie in the closed convex hulls of
`{dj(y)((τ i)⁻¹ • d i) : y ∈ V}`, so the hypothesis bounds `(τ i)⁻¹ • d i`; the bilinear bound
on `d²j` then gives `(τ i)⁻¹ • (j (x + d i) - j x) - dj(x)((τ i)⁻¹ • d i) → 0`; finally
`dj(x)` is an embedding and `E` is sequentially complete. -/
theorem ContDiffMBOn.exists_tendsto_of_equiEmbedding [SeqComplete E] (hU : IsOpen U)
    (hj : ContDiffMBOn 2 j U) {x : E} (hx : x ∈ U) (hH : EquiEmbeddingNear j x)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {d : ι → E} {τ : ι → ℝ}
    (hd : Tendsto d l (𝓝 0)) (hτ : ∀ᶠ i in l, τ i ≠ 0) {R : F}
    (hR : Tendsto (fun i ↦ (τ i)⁻¹ • (j (x + d i) - j x)) l (𝓝 R)) :
    ∃ D, Tendsto (fun i ↦ (τ i)⁻¹ • d i) l (𝓝 D) ∧ dMB j (x, D) = R := by
  have hj1 : ContDiffMBOn 1 j U := hj.of_le (by omega)
  obtain ⟨L, hL, hLemb⟩ := hH.exists_clm hU hj1 hx
  obtain ⟨V, hV, hHV⟩ := hH
  have hxd : Tendsto (fun i ↦ x + d i) l (𝓝 x) := by simpa using hd.const_add x
  -- a convex neighborhood `S ⊆ V ∩ U` of `x`; eventually the segments `[x, x + d i]` lie in `S`
  obtain ⟨S, ⟨hS, hSc⟩, hSsub⟩ := (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x).mem_iff.mp
    (inter_mem hV (hU.mem_nhds hx))
  have hseg : ∀ᶠ i in l, ∀ s ∈ Icc (0 : ℝ) 1, x + s • d i ∈ S := by
    filter_upwards [hxd hS] with i hi s hs
    exact hSc.add_smul_mem (mem_of_mem_nhds hS) hi hs
  set g : ι → E := fun i ↦ (τ i)⁻¹ • d i with hg
  set Δ : ι → F := fun i ↦ (τ i)⁻¹ • (j (x + d i) - j x) with hΔ
  -- Step 1: the quotients `g i` are eventually bounded for every continuous seminorm
  have hbdd : ∀ p : Seminorm ℝ E, Continuous p → ∃ M, 0 ≤ M ∧ ∀ᶠ i in l, p (g i) ≤ M := by
    intro p hp
    obtain ⟨q, hq, C, hC, hpq⟩ := hHV p hp
    refine ⟨C * (q R + 1), by positivity, ?_⟩
    filter_upwards [hτ, hseg, eventually_seminorm_sub_lt hR hq one_pos] with i hτi hsegi hRi
    have htg : τ i • g i = d i := smul_inv_smul₀ hτi _
    have hmem := hj1.quotient_mem_closure_convexHull (y := x) (v := g i) hτi
      (fun s hs ↦ by rw [htg]; exact (hSsub (hsegi s hs)).2)
    rw [htg] at hmem
    have hmem' : Δ i ∈ closure (convexHull ℝ ((fun y ↦ dMB j (y, g i)) '' V)) := by
      refine closure_mono (convexHull_mono ?_) hmem
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨_, (hSsub (hsegi s hs)).1, rfl⟩
    calc p (g i) ≤ C * q (Δ i) := hpq _ _ hmem'
      _ ≤ C * (q R + 1) := by
        gcongr
        calc q (Δ i) = q ((Δ i - R) + R) := by rw [sub_add_cancel]
          _ ≤ q (Δ i - R) + q R := map_add_le_add q _ _
          _ ≤ q R + 1 := by linarith
  -- Step 2: `Δ i - dj(x)(g i) → 0`, by the bilinear bound on `d²j`
  have hsmall : ∀ q : Seminorm ℝ F, Continuous q → ∀ ε > 0,
      ∀ᶠ i in l, q ((Δ i - L (g i)) - 0) < ε := by
    intro q hq ε hε
    obtain ⟨N, hN, hNU, r, hr, hb⟩ := hj.exists_d2_seminorm_bound hU hx hq
    obtain ⟨S', ⟨hS', hS'c⟩, hS'sub⟩ :=
      (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x).mem_iff.mp hN
    have hxS' : x ∈ S' := mem_of_mem_nhds hS'
    obtain ⟨M, hM, hMev⟩ := hbdd r hr
    filter_upwards [hτ, hxd hS', hMev,
      eventually_seminorm_sub_lt hd hr (show 0 < ε / (M + 1) by positivity)]
      with i hτi hi hMi hdi
    rw [sub_zero] at hdi ⊢
    have hsegN : ∀ s ∈ Icc (0 : ℝ) 1, x + s • d i ∈ S' := fun s hs ↦
      hS'c.add_smul_mem hxS' hi hs
    -- the increment of `j - dj(x)` along `[x, x + d i]`
    have hinc : q (j (x + d i) - j x - L (d i)) ≤ r (d i) * r (d i) := by
      have hd' : ∀ s ∈ Icc (0 : ℝ) 1, HasDirDerivAt (fun y ↦ j y - L y) (x + s • d i) (d i)
          (dMB j (x + s • d i, d i) - L (d i)) := fun s hs ↦
        (hj1.hasDirDerivAt (hNU (hS'sub (hsegN s hs))) (d i)).sub (L.hasDirDerivAt _ _)
      have hDc : ContinuousOn (fun s : ℝ ↦ dMB j (x + s • d i, d i) - L (d i)) (Icc 0 1) := by
        have h0 : ContinuousOn (dMB j) (U ×ˢ univ) := hj1.2.2
        exact (h0.comp (by fun_prop : Continuous fun s : ℝ ↦ (x + s • d i, d i)).continuousOn
          fun s hs ↦ ⟨hNU (hS'sub (hsegN s hs)), mem_univ _⟩).sub continuousOn_const
      obtain ⟨hcl, hcv⟩ := Seminorm.isClosed_convex_setOf_le hq (r (d i) * r (d i))
      have hmem := sub_mem_of_hasDirDerivAt hd' hDc hcv hcl fun s hs ↦ by
        change q (dMB j (x + s • d i, d i) - L (d i)) ≤ r (d i) * r (d i)
        rw [hL]
        calc q (dMB j (x + s • d i, d i) - dMB j (x, d i))
            ≤ r (x + s • d i - x) * r (d i) :=
              hj.seminorm_dMB_sub_le (hS'sub.trans hNU) hS'c hq (fun z hz ↦ hb z (hS'sub hz))
                hxS' (hsegN s hs) _
          _ ≤ r (d i) * r (d i) := by
              rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_of_nonneg hs.1]
              gcongr
              calc s * r (d i) ≤ 1 * r (d i) := by gcongr; exact hs.2
                _ = r (d i) := one_mul _
      change q (j (x + d i) - L (x + d i) - (j x - L x)) ≤ _ at hmem
      convert hmem using 2
      rw [map_add]; abel
    have heq : Δ i - L (g i) = (τ i)⁻¹ • (j (x + d i) - j x - L (d i)) := by
      simp only [hΔ, hg, map_smul, smul_sub]
    have hrg : r (g i) = |τ i|⁻¹ * r (d i) := by
      simp only [hg, map_smul_eq_mul, Real.norm_eq_abs, abs_inv]
    rw [heq, map_smul_eq_mul, Real.norm_eq_abs, abs_inv]
    calc |τ i|⁻¹ * q (j (x + d i) - j x - L (d i)) ≤ |τ i|⁻¹ * (r (d i) * r (d i)) := by
          gcongr
      _ = r (d i) * r (g i) := by rw [hrg]; ring
      _ ≤ ε / (M + 1) * M := by gcongr
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
  -- Step 3: `dj(x)(g i) → R`; solve in the sequentially complete space `E`
  have h0 : Tendsto (fun i ↦ Δ i - L (g i)) l (𝓝 0) := tendsto_of_forall_seminorm hsmall
  have hLg : Tendsto (fun i ↦ L (g i)) l (𝓝 R) := by simpa using hR.sub h0
  obtain ⟨D, hD, hLD⟩ := exists_tendsto_of_seminorm_le hLemb hLg
  exact ⟨D, hD, by rw [← hL]; exact hLD⟩

/-! ### Bootstrapping -/

/-- **Linear bootstrap.** Under the hypothesis at every point of `U`, if `dj(γ q)(z q) = w q` on
`W`, with `γ` and `w` of class `C^k`, `z` continuous and `j` of class `C^{k+1}`, then `z` is of
class `C^k`. This is the locally convex counterpart of
`ContDiffMBOn.of_fderiv_eq_of_boundedBelow`. -/
theorem ContDiffMBOn.of_dMB_eq_of_equiEmbedding [SeqComplete E] (hU : IsOpen U)
    (hH : ∀ x ∈ U, EquiEmbeddingNear j x) :
    ∀ (k : ℕ), ContDiffMBOn (k + 1) j U → ∀ {H : Type u} [AddCommGroup H] [Module ℝ H]
      [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
      [LocallyConvexSpace ℝ H] [T2Space H] {W : Set H} {γ z : H → E} {w : H → F},
      IsOpen W → ContDiffMBOn k γ W → MapsTo γ W U → ContinuousOn z W → ContDiffMBOn k w W →
      (∀ q ∈ W, dMB j (γ q, z q) = w q) → ContDiffMBOn k z W := by
  intro k
  induction k with
  | zero =>
    intro _ H _ _ _ _ _ _ _ W γ z w hW hγ hγU hz hw heq
    exact hz
  | succ k ih =>
    intro hj H _ _ _ _ _ _ _ W γ z w hW hγ hγU hz hw heq
    have hzk : ContDiffMBOn k z W := ih hj.of_succ hW hγ.of_succ hγU hz hw.of_succ heq
    have hj1 : ContDiffMBOn 1 j U := hj.of_le (by omega)
    have hdj1 : ContDiffMBOn 1 (dMB j) (U ×ˢ univ) :=
      (hj.2.2 : ContDiffMBOn (k + 1) (dMB j) (U ×ˢ univ)).of_le (by omega)
    have hγ1 : ContDiffMBOn 1 γ W := hγ.of_le (by omega)
    have hw1 : ContDiffMBOn 1 w W := hw.of_le (by omega)
    -- the second-order term `d²j(γ q)(dγ(q, h), z q)`
    set B : H × H → F := fun p ↦ dMB (dMB j) ((γ p.1, z p.1), (dMB γ p, 0)) with hB
    -- the derivative of `z`, as a limit of difference quotients
    have hder : ∀ q ∈ W, ∀ h : H, ∃ D : E, HasDirDerivAt z q h D ∧
        dMB j (γ q, D) = dMB w (q, h) - B (q, h) := by
      intro q hq h
      have hγq := hγU hq
      obtain ⟨L, hL, hLemb⟩ := (hH _ hγq).exists_clm hU hj1 hγq
      have hline : Tendsto (fun t : ℝ ↦ q + t • h) (𝓝[≠] 0) (𝓝 q) := by
        have : Continuous fun t : ℝ ↦ q + t • h := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), q + t • h ∈ W := hline (hW.mem_nhds hq)
      have hzline : Tendsto (fun t : ℝ ↦ z (q + t • h)) (𝓝[≠] 0) (𝓝 (z q)) :=
        ((hz.continuousAt (hW.mem_nhds hq)).tendsto).comp hline
      have hγquot : Tendsto (fun t : ℝ ↦ t⁻¹ • (γ (q + t • h) - γ q)) (𝓝[≠] 0)
          (𝓝 (dMB γ (q, h))) := hγ1.hasDirDerivAt hq h
      have hwquot : Tendsto (fun t : ℝ ↦ t⁻¹ • (w (q + t • h) - w q)) (𝓝[≠] 0)
          (𝓝 (dMB w (q, h))) := hw1.hasDirDerivAt hq h
      have ht0 : Tendsto (fun t : ℝ ↦ t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
      have hφ : Tendsto (fun t : ℝ ↦ (((γ q, z (q + t • h)),
          (t⁻¹ • (γ (q + t • h) - γ q), (0 : E)), t) : (E × E) × (E × E) × ℝ)) (𝓝[≠] 0)
          (𝓝[{p | p.2.2 ≠ 0}] ((γ q, z q), (dMB γ (q, h), 0), 0)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun t ht ↦ ht⟩
        exact (tendsto_const_nhds.prodMk_nhds hzline).prodMk_nhds
          ((hγquot.prodMk_nhds tendsto_const_nhds).prodMk_nhds ht0)
      -- Glöckner's lemma for `dj` gives the second-order term
      have hsecond := (hdj1.tendsto_quotient (hU.prod isOpen_univ) (y := (γ q, z q))
        (v := (dMB γ (q, h), 0)) ⟨hγq, mem_univ _⟩).comp hφ
      have hkey : Tendsto (fun t : ℝ ↦ L (t⁻¹ • (z (q + t • h) - z q))) (𝓝[≠] 0)
          (𝓝 (dMB w (q, h) - B (q, h))) := by
        refine (hwquot.sub hsecond).congr' ?_
        filter_upwards [hev, self_mem_nhdsWithin] with t ht (ht0 : t ≠ 0)
        have e1 : ((γ q, z (q + t • h)) + t • (t⁻¹ • (γ (q + t • h) - γ q), (0 : E))) =
            (γ (q + t • h), z (q + t • h)) := by
          simp [Prod.smul_mk, smul_inv_smul₀ ht0]
        simp only [Function.comp_def, e1]
        rw [heq _ ht, map_smul, map_sub, hL, hL, heq q hq, ← smul_sub]
        congr 1
        abel
      obtain ⟨D, hD, hLD⟩ := exists_tendsto_of_seminorm_le hLemb hkey
      exact ⟨D, hD, by rw [← hL]; exact hLD⟩
    have hdz : ∀ p ∈ W ×ˢ (univ : Set H), dMB j (γ p.1, dMB z p) = dMB w p - B p := by
      rintro ⟨q, h⟩ ⟨hq, -⟩
      obtain ⟨D, hD, hAD⟩ := hder q hq h
      rw [hD.dMB_eq]
      exact hAD
    -- the data of the induction step, on `W × H`
    have hW2 : IsOpen (W ×ˢ (univ : Set H)) := hW.prod isOpen_univ
    have hfst : ∀ (n : ℕ), ContDiffMBOn n (fun p : H × H ↦ p.1) (W ×ˢ univ) := fun n ↦
      (ContinuousLinearMap.fst ℝ H H).contDiffMBOn n _
    have hγfst : ContDiffMBOn k (fun p : H × H ↦ γ p.1) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := γ) (f := fun p : H × H ↦ p.1) hW2 hW hγ.of_succ (hfst k)
        fun p hp ↦ hp.1
    have hzfst : ContDiffMBOn k (fun p : H × H ↦ z p.1) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := z) (f := fun p : H × H ↦ p.1) hW2 hW hzk (hfst k) fun p hp ↦ hp.1
    have hdγ : ContDiffMBOn k (dMB γ) (W ×ˢ univ) := hγ.2.2
    have hdw : ContDiffMBOn k (dMB w) (W ×ˢ univ) := hw.2.2
    have hd2j : ContDiffMBOn k (dMB (dMB j)) ((U ×ˢ univ) ×ˢ univ) := hj.2.2.2.2
    have hinner : ContDiffMBOn k (fun p : H × H ↦ ((γ p.1, z p.1), (dMB γ p, (0 : E))))
        (W ×ˢ univ) :=
      ContDiffMBOn.prodMk hW2 (ContDiffMBOn.prodMk hW2 hγfst hzfst)
        (ContDiffMBOn.prodMk hW2 hdγ (contDiffMBOn_const k (0 : E) _))
    have hBk : ContDiffMBOn k B (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := dMB (dMB j))
        (f := fun p : H × H ↦ ((γ p.1, z p.1), (dMB γ p, (0 : E)))) hW2
        ((hU.prod isOpen_univ).prod isOpen_univ) hd2j hinner
        fun p hp ↦ ⟨⟨hγU hp.1, mem_univ _⟩, mem_univ _⟩
    have hw' : ContDiffMBOn k (fun p : H × H ↦ dMB w p - B p) (W ×ˢ univ) :=
      ContDiffMBOn.comp (F₁ := F × F) hW2 isOpen_univ
        ((ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F).contDiffMBOn k univ)
        (ContDiffMBOn.prodMk hW2 hdw hBk) (mapsTo_univ _ _)
    have hdzc : ContinuousOn (dMB z) (W ×ˢ univ) :=
      hj1.continuousOn_of_dMB_eq hU hH hγfst.continuousOn (fun p hp ↦ hγU hp.1)
        hw'.continuousOn hdz
    have hdzk := ih hj.of_succ hW2 hγfst (fun p hp ↦ hγU hp.1) hdzc hw' hdz
    refine ⟨hz, fun q hq h ↦ ?_, hdzk⟩
    obtain ⟨D, hD, -⟩ := hder q hq h
    rw [hD.dMB_eq]
    exact hD

/-- **Maps with uniformly injective derivative reflect smoothness (locally convex case).**
Let `E` be sequentially complete, `j` of class `C^2` and `C^k` on the open set `U`, and assume
`EquiEmbeddingNear j x` at every `x ∈ U`. If `γ : W → U` is continuous on an open subset `W` of a
locally convex space and `j ∘ γ` is `C^k`, then `γ` is `C^k`. -/
theorem ContDiffMBOn.of_comp_of_equiEmbedding [SeqComplete E] (hU : IsOpen U)
    (hj : ContDiffMBOn 2 j U) (hH : ∀ x ∈ U, EquiEmbeddingNear j x) :
    ∀ (k : ℕ), ContDiffMBOn k j U → ∀ {H : Type u} [AddCommGroup H] [Module ℝ H]
      [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]
      [LocallyConvexSpace ℝ H] [T2Space H] {W : Set H} {γ : H → E}, IsOpen W →
      ContinuousOn γ W → MapsTo γ W U → ContDiffMBOn k (j ∘ γ) W → ContDiffMBOn k γ W := by
  have hj1 : ContDiffMBOn 1 j U := hj.of_le (by omega)
  intro k
  induction k with
  | zero =>
    intro _ H _ _ _ _ _ _ _ W γ hW hγc _ _
    exact hγc
  | succ k ih =>
    intro hjk H _ _ _ _ _ _ _ W γ hW hγc hγU hjγ
    have hγk : ContDiffMBOn k γ W := ih hjk.of_succ hW hγc hγU hjγ.of_succ
    have hjγ1 : ContDiffMBOn 1 (j ∘ γ) W := hjγ.of_le (by omega)
    -- the derivative of `γ`
    have hder : ∀ q ∈ W, ∀ h : H, ∃ D : E, HasDirDerivAt γ q h D ∧
        dMB j (γ q, D) = dMB (j ∘ γ) (q, h) := by
      intro q hq h
      have hline : Tendsto (fun t : ℝ ↦ q + t • h) (𝓝[≠] 0) (𝓝 q) := by
        have : Continuous fun t : ℝ ↦ q + t • h := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      have hγline : Tendsto (fun t : ℝ ↦ γ (q + t • h)) (𝓝[≠] 0) (𝓝 (γ q)) :=
        ((hγc.continuousAt (hW.mem_nhds hq)).tendsto).comp hline
      have hd : Tendsto (fun t : ℝ ↦ γ (q + t • h) - γ q) (𝓝[≠] 0) (𝓝 0) := by
        simpa using hγline.sub_const (γ q)
      have hR : Tendsto (fun t : ℝ ↦ t⁻¹ • (j (γ q + (γ (q + t • h) - γ q)) - j (γ q)))
          (𝓝[≠] 0) (𝓝 (dMB (j ∘ γ) (q, h))) := by
        refine (hjγ1.hasDirDerivAt hq h).congr fun t ↦ ?_
        simp
      obtain ⟨D, hD, hjD⟩ := hj.exists_tendsto_of_equiEmbedding hU (hγU hq) (hH _ (hγU hq))
        (τ := fun t ↦ t) hd (eventually_nhdsWithin_of_forall fun t ht ↦ ht) hR
      exact ⟨D, hD, hjD⟩
    -- the derivative satisfies a linear equation; bootstrap it
    have hdγ : ∀ p ∈ W ×ˢ (univ : Set H), dMB j (γ p.1, dMB γ p) = dMB (j ∘ γ) p := by
      rintro ⟨q, h⟩ ⟨hq, -⟩
      obtain ⟨D, hD, hAD⟩ := hder q hq h
      rw [hD.dMB_eq]
      exact hAD
    have hW2 : IsOpen (W ×ˢ (univ : Set H)) := hW.prod isOpen_univ
    have hγfst : ContDiffMBOn k (fun p : H × H ↦ γ p.1) (W ×ˢ univ) :=
      ContDiffMBOn.comp (g := γ) (f := fun p : H × H ↦ p.1) hW2 hW hγk
        ((ContinuousLinearMap.fst ℝ H H).contDiffMBOn k _) fun p hp ↦ hp.1
    have hdjγ : ContDiffMBOn k (dMB (j ∘ γ)) (W ×ˢ univ) := hjγ.2.2
    have hdγc : ContinuousOn (dMB γ) (W ×ˢ univ) :=
      hj1.continuousOn_of_dMB_eq hU hH hγfst.continuousOn (fun p hp ↦ hγU hp.1)
        hdjγ.continuousOn hdγ
    have hdγk := ContDiffMBOn.of_dMB_eq_of_equiEmbedding hU hH k hjk hW2 hγfst
      (fun p hp ↦ hγU hp.1) hdγc hdjγ hdγ
    refine ⟨hγc, fun q hq h ↦ ?_, hdγk⟩
    obtain ⟨D, hD, -⟩ := hder q hq h
    rw [hD.dMB_eq]
    exact hD

/-- The smooth version of `ContDiffMBOn.of_comp_of_equiEmbedding`, with the same shape as
`ContDiffMBOn.of_comp_of_boundedBelow`. -/
theorem ContDiffMBOn.of_comp_of_equiEmbedding_of_smooth [SeqComplete E] (hU : IsOpen U)
    (hj : SmoothMBOn j U) (hH : ∀ x ∈ U, EquiEmbeddingNear j x) (k : ℕ) {H : Type u}
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H] {W : Set H} {γ : H → E}
    (hW : IsOpen W) (hγc : ContinuousOn γ W) (hγU : MapsTo γ W U)
    (hjγ : ContDiffMBOn k (j ∘ γ) W) : ContDiffMBOn k γ W :=
  ContDiffMBOn.of_comp_of_equiEmbedding hU (hj 2) hH k (hj k) hW hγc hγU hjγ

end Main

/-! ### Normed spaces -/

section Normed

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : E → F} {U : Set E}

/-- **In normed spaces the hypothesis is automatic.** If `j` is `C^2` on `U` and `dj(x₀)` is
bounded below, then `EquiEmbeddingNear j x₀`: on the neighborhood where
`‖dj(y) - dj(x₀)‖ < m / 2`, every closed convex combination `z` of the `dj(y) w` satisfies
`‖z - dj(x₀) w‖ ≤ m / 2 * ‖w‖`, hence `m / 2 * ‖w‖ ≤ ‖z‖`. -/
theorem equiEmbeddingNear_of_boundedBelow (hU : IsOpen U) (hj : ContDiffMBOn 2 j U) {x₀ : E}
    (hx₀ : x₀ ∈ U) {m : ℝ} (hm : 0 < m) (hbd : ∀ v, m * ‖v‖ ≤ ‖fderiv ℝ j x₀ v‖) :
    EquiEmbeddingNear j x₀ := by
  have hC1 : ContDiffOn ℝ 1 j U := hj.contDiffOn_one hU
  have hfc : ContinuousOn (fderiv ℝ j) U := hC1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdMB : ∀ y ∈ U, ∀ w, dMB j (y, w) = fderiv ℝ j y w := fun y hy w ↦
    (((hC1.differentiableOn one_ne_zero y hy).differentiableAt
      (hU.mem_nhds hy)).hasFDerivAt.hasDirDerivAt w).dMB_eq
  set A := fderiv ℝ j x₀
  set V := U ∩ fderiv ℝ j ⁻¹' Metric.ball A (m / 2)
  have hV : V ∈ 𝓝 x₀ := inter_mem (hU.mem_nhds hx₀)
    ((hfc.continuousAt (hU.mem_nhds hx₀)).preimage_mem_nhds
      (Metric.ball_mem_nhds A (half_pos hm)))
  refine ⟨V, hV, fun p hp ↦ ?_⟩
  obtain ⟨c, hc, hpc⟩ := Seminorm.bound_of_continuous_normedSpace p hp
  refine ⟨normSeminorm ℝ F, continuous_norm, 2 * c / m, by positivity, fun w z hz ↦ ?_⟩
  have hball : z ∈ Metric.closedBall (A w) (m / 2 * ‖w‖) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _))
      Metric.isClosed_closedBall hz
    rintro _ ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖dMB j (y, w) - A w‖ ≤ _
    rw [hdMB y hy.1 w,
      ← sub_apply]
    exact ((fderiv ℝ j y - A).le_opNorm w).trans
      (by gcongr; exact (mem_ball_iff_norm.mp hy.2).le)
  rw [Metric.mem_closedBall, dist_eq_norm] at hball
  have h1 : m / 2 * ‖w‖ ≤ ‖z‖ := by
    have : ‖A w‖ ≤ ‖z‖ + ‖z - A w‖ := by
      calc ‖A w‖ = ‖z - (z - A w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖z‖ + ‖z - A w‖ := norm_sub_le _ _
    linarith [hbd w]
  rw [coe_normSeminorm]
  calc p w ≤ c * ‖w‖ := hpc w
    _ = 2 * c / m * (m / 2 * ‖w‖) := by field_simp
    _ ≤ 2 * c / m * ‖z‖ := by gcongr

/-- **The Banach case, with a pointwise lower bound.** For `E` complete, a smooth `j` whose
derivative is bounded below at every point of `U` (with a constant that may depend on the point)
reflects smoothness. This contains `ContDiffMBOn.of_comp_of_boundedBelow`, where the lower bound
is uniform on `U`. -/
theorem ContDiffMBOn.of_comp_of_boundedBelow_pointwise [CompleteSpace E] (hU : IsOpen U)
    (hj : SmoothMBOn j U) (hbd : ∀ x ∈ U, ∃ m > 0, ∀ v, m * ‖v‖ ≤ ‖fderiv ℝ j x v‖) (k : ℕ)
    {H : Type u} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [LocallyConvexSpace ℝ H] [T2Space H] {W : Set H} {γ : H → E}
    (hW : IsOpen W) (hγc : ContinuousOn γ W) (hγU : MapsTo γ W U)
    (hjγ : ContDiffMBOn k (j ∘ γ) W) : ContDiffMBOn k γ W :=
  ContDiffMBOn.of_comp_of_equiEmbedding_of_smooth hU hj
    (fun x hx ↦ by
      obtain ⟨m, hm, hb⟩ := hbd x hx
      exact equiEmbeddingNear_of_boundedBelow hU (hj 2) hx hm hb)
    k hW hγc hγU hjγ

end Normed

end LocallyConvex.Analysis

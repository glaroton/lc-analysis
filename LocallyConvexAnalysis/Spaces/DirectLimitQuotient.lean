/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Spaces.DirectLimit
public import LocallyConvexAnalysis.Spaces.DirectSum

/-!
# Direct limits as quotients of direct sums

Reference: [GN26, Lemma B.13.6(c)], (d) (p. 946).

Let `S n ⊆ V` be locally convex subspaces, indexed by a countable set and covering `V`. The
summation map `q : ⊕ₙ S n → V`, `(xₙ)ₙ ↦ ∑ₙ xₙ`, from the locally convex direct sum is an open
quotient map onto the locally convex direct limit (Lemma B.13.6(d)). Hence the images `q(⊕ₙ Wₙ)`
of the boxes of `0`-neighbourhoods, that is, the sets `⋃ₙ (W₀ + ⋯ + Wₙ)`, form a basis of
`0`-neighbourhoods of the direct limit, open if the `Wₙ` are (Lemma B.13.6(c)).

## Main definitions

* `LCDirectLimit.sumMap S`: the summation map `(xₙ)ₙ ↦ ∑ₙ xₙ` from the locally convex direct sum
  of the steps `S n` to their locally convex direct limit.

## Main results

* `locallyConvexSpace_quotient`: the quotient of a locally convex space by a subspace is locally
  convex.
* `LCDirectLimit.isOpenQuotientMap_sumMap`: for countably many steps covering `V`, the summation
  map is an open quotient map ([GN26, Lemma B.13.6(d)]).
* `LCDirectLimit.nhds_zero_hasBasis_sumMap`: the sets `⋃ₙ (W₀ + ⋯ + Wₙ)`, for
  `0`-neighbourhoods `Wₙ ⊆ S n`, form a basis of `0`-neighbourhoods of the direct limit, and
  `LCDirectLimit.isOpen_sumMap_box`: they are open if the `Wₙ` are ([GN26, Lemma B.13.6(c)]).

## Implementation notes

As in Glöckner–Neeb, `q` is continuous by the universal property of the direct sum (countable
index set), and the quotient `(⊕ₙ S n) / ker q` is a locally convex space on which the inclusions of
the `S n` are continuous, so by the universal property of the direct limit the inverse of the
induced bijection is continuous.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

/-- **Quotients of locally convex spaces are locally convex**: the images of the convex
`0`-neighbourhoods under the open quotient map form a basis of convex `0`-neighbourhoods. -/
theorem locallyConvexSpace_quotient {M : Type*} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [LocallyConvexSpace ℝ M] (N : Submodule ℝ M) :
    LocallyConvexSpace ℝ (M ⧸ N) := by
  have hb := (LocallyConvexSpace.convex_basis_zero ℝ M).map N.mkQ
  rw [N.isOpenQuotientMap_mkQ.map_nhds_eq, map_zero] at hb
  exact LocallyConvexSpace.ofBasisZero ℝ (M ⧸ N) _ _ hb fun s hs ↦ hs.2.linear_image N.mkQ

namespace LCDirectLimit

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} (S : ι → Submodule ℝ V)

open Classical in
/-- The summation map `(xₙ)ₙ ↦ ∑ₙ xₙ` from the direct sum of the steps to the direct limit. -/
def sumMap : LCDirectSum (fun n ↦ S n) →ₗ[ℝ] LCDirectLimit S :=
  DFinsupp.lsum ℕ (M := fun n ↦ S n) fun n ↦ incl S n

open Classical in
theorem sumMap_single (n : ι) (v : S n) :
    sumMap S (LCDirectSum.single n v) = incl S n v := by
  exact DFinsupp.lsum_single ℕ (M := fun n ↦ S n) _ n v

variable [∀ n, TopologicalSpace (S n)] [∀ n, IsTopologicalAddGroup (S n)]
  [∀ n, ContinuousSMul ℝ (S n)] [∀ n, LocallyConvexSpace ℝ (S n)]

/-- **The direct limit topology is the quotient topology of the direct sum**
([GN26, Lemma B.13.6(d)]): for countably many steps covering `V`, the summation map is an open
quotient map. -/
theorem isOpenQuotientMap_sumMap [Countable ι] (hcover : ∀ v : V, ∃ n, v ∈ S n) :
    IsOpenQuotientMap (sumMap S) := by
  classical
  set q := sumMap S
  -- continuity, by the universal property of the direct sum
  have hq : Continuous q := LCDirectSum.continuous_of_continuous_single q.toAddMonoidHom
    fun n ↦ by
      simp only [LinearMap.toAddMonoidHom_coe]
      exact (continuous_incl S n).congr fun v ↦ (sumMap_single S n v).symm
  have hsurj : Surjective q := fun v ↦ by
    obtain ⟨n, hn⟩ := hcover v
    exact ⟨LCDirectSum.single n ⟨v, hn⟩, sumMap_single S n _⟩
  -- the induced bijection from the quotient by the kernel
  set N := LinearMap.ker q
  have : LocallyConvexSpace ℝ (LCDirectSum (fun n ↦ S n) ⧸ N) := locallyConvexSpace_quotient N
  set e : (LCDirectSum (fun n ↦ S n) ⧸ N) ≃ₗ[ℝ] LCDirectLimit S :=
    q.quotKerEquivOfSurjective hsurj
  have he : ∀ x, e (N.mkQ x) = q x := fun x ↦ rfl
  have hec : Continuous e :=
    N.isQuotientMap_mkQ.continuous_iff.2 (hq.congr fun x ↦ (he x).symm)
  -- the inverse is continuous by the universal property of the direct limit
  have hinv : Continuous e.symm := by
    refine continuous_of_continuous_comp_incl S e.symm.toLinearMap fun n ↦ ?_
    refine (N.continuous_mkQ.comp (LCDirectSum.continuous_single n)).congr fun v ↦ ?_
    simp only [Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [eq_comm, e.symm_apply_eq, he, sumMap_single S]
  have hopen : IsOpenMap q := by
    have h1 : IsOpenMap e := fun U hU ↦ by
      have himg : ⇑e '' U = e.symm ⁻¹' U := e.toEquiv.image_eq_preimage_symm U
      rw [himg]
      exact hU.preimage hinv
    exact h1.comp N.isOpenMap_mkQ
  exact ⟨hsurj, hq, hopen⟩

/-- **A basis of `0`-neighbourhoods of the direct limit** ([GN26, Lemma B.13.6(c)]): the
images `⋃ₙ (W₀ + ⋯ + Wₙ)` of the boxes `⊕ₙ Wₙ` of `0`-neighbourhoods of the steps. -/
theorem nhds_zero_hasBasis_sumMap [Countable ι] (hcover : ∀ v : V, ∃ n, v ∈ S n) :
    (𝓝 (0 : LCDirectLimit S)).HasBasis (fun W : ∀ n, Set (S n) ↦ ∀ n, W n ∈ 𝓝 0)
      fun W ↦ sumMap S '' LCDirectSum.box W := by
  have h := (LCDirectSum.nhds_zero_hasBasis (E := fun n ↦ S n)).map (sumMap S)
  rwa [(isOpenQuotientMap_sumMap S hcover).map_nhds_eq, map_zero] at h

/-- The images of the boxes of open `0`-neighbourhoods are open
([GN26, Lemma B.13.6(c)]). -/
theorem isOpen_sumMap_box [Countable ι] (hcover : ∀ v : V, ∃ n, v ∈ S n) {W : ∀ n, Set (S n)}
    (hW : ∀ n, IsOpen (W n)) : IsOpen (sumMap S '' LCDirectSum.box W) :=
  (isOpenQuotientMap_sumMap S hcover).isOpenMap _ (LCDirectSum.isOpen_box hW)

end LCDirectLimit

end LocallyConvex.Analysis

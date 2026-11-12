/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Spaces.DirectSum
public import LocallyConvexAnalysis.Spaces.DirectLimit
public import LocallyConvexAnalysis.Calculus.Integral.Existence

/-!
# Weak completeness properties of direct sums and strict direct limits

We show that sequential completeness, Mackey completeness and quasi-completeness pass to locally
convex direct sums, and that Mackey completeness passes to strict direct limits with closed steps.

Reference: [GN26, Lemma B.13.2(f) and Proposition B.13.9(e)] (pp. 942, 947).

## Main results

* `LCDirectSum.seqComplete`, `LCDirectSum.mackeyComplete`, `LCDirectSum.quasiCompleteSpace`: a
  direct sum of Hausdorff sequentially complete (Mackey complete, quasi-complete) spaces is
  sequentially complete (Mackey complete, quasi-complete) (Lemma B.13.2(f)).
* `LCDirectLimit.IsStrict.mackeyComplete`: a strict direct limit of Mackey complete spaces with
  closed steps is Mackey complete (Proposition B.13.9(e)); the sequentially complete and
  quasi-complete cases are in `Spaces/DirectLimit.lean`.
* `isVonNBounded_range_of_cauchy`, `isVonNBounded_range_of_mackey`: Cauchy sequences and
  Mackey–Cauchy sequences are bounded.

## Implementation notes

Cauchy sequences, Mackey–Cauchy sequences and closed bounded sets are bounded. In a direct sum,
bounded sets lie in a finite partial sum (Lemma B.13.2(e)), where convergence is coordinatewise
(`LCDirectSum.tendsto_mk_of_finset`). In a strict direct limit with closed steps, they lie and are
bounded in some step (Proposition B.13.9(c)).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Bornology
open scoped Topology Pointwise

noncomputable section

namespace LocallyConvex.Analysis

section Bounded

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- Cauchy sequences are bounded. -/
theorem isVonNBounded_range_of_cauchy {u : ℕ → F}
    (hu : ∀ W ∈ 𝓝 (0 : F), ∃ N, ∀ m ≥ N, ∀ n ≥ N, u n - u m ∈ W) :
    IsVonNBounded ℝ (range u) := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have hc : CauchySeq u := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero F, tendsto_comap_iff]
    refine Filter.tendsto_def.mpr fun W hW ↦ ?_
    obtain ⟨N, hN⟩ := hu W hW
    rw [← prod_atTop_atTop_eq]
    exact mem_of_superset (prod_mem_prod (Ici_mem_atTop N) (Ici_mem_atTop N))
      fun p (hp : p ∈ Ici N ×ˢ Ici N) ↦ hN p.1 hp.1 p.2 hp.2
  exact hc.totallyBounded_range.isVonNBounded ℝ

omit [IsTopologicalAddGroup F] in
/-- `c • B` is bounded if `B` is. -/
theorem isVonNBounded_smul_set {B : Set F} (hB : IsVonNBounded ℝ B) (c : ℝ) :
    IsVonNBounded ℝ (c • B) := by
  have := hB.image (c • ContinuousLinearMap.id ℝ F)
  simpa [image_smul] using this

/-- Mackey–Cauchy sequences are bounded: `u k ∈ u 0 + r 0 • B`. -/
theorem isVonNBounded_range_of_mackey {u : ℕ → F} {B : Set F} {r : ℕ → ℝ}
    (hB : IsVonNBounded ℝ B) (hu : ∀ k l, k ≤ l → u l - u k ∈ r k • B) :
    IsVonNBounded ℝ (range u) := by
  refine ((isVonNBounded_singleton (u 0)).add (isVonNBounded_smul_set hB (r 0))).subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨u 0, rfl, u k - u 0, hu 0 k (Nat.zero_le k), add_sub_cancel _ _⟩

end Bounded

namespace LCDirectSum

variable {J : Type*} {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, TopologicalSpace (E j)]
  [∀ j, IsTopologicalAddGroup (E j)]

open Classical in
/-- **Convergence in a finite partial sum is coordinatewise.** -/
theorem tendsto_mk_of_finset {α : Type*} {l : Filter α} {f : α → LCDirectSum E} {s : Finset J}
    (hs : ∀ᶠ a in l, ∀ j ∉ s, f a j = 0) {y : ∀ j, E j}
    (hy : ∀ j ∈ s, Tendsto (fun a ↦ f a j) l (𝓝 (y j))) :
    Tendsto f l (𝓝 (DFinsupp.mk s (fun j ↦ y j) : LCDirectSum E)) := by
  classical
  set z : LCDirectSum E := DFinsupp.mk s fun j ↦ y j
  have hz : ∀ j, z j = if j ∈ s then y j else 0 := fun j ↦ by
    change (DFinsupp.mk s (fun j ↦ y j) : ∀ j, E j) j = _
    rw [DFinsupp.mk_apply]
    split_ifs <;> rfl
  refine ((nhds_hasBasis z).tendsto_right_iff).2 fun W hW ↦ ?_
  have hin : ∀ᶠ a in l, ∀ j ∈ s, f a j ∈ W j := by
    rw [eventually_all_finset]
    intro j hj
    have := hW j
    simp only [hz j, hj, ↓reduceIte] at this
    exact hy j hj this
  filter_upwards [hs, hin] with a has hain j
  by_cases hj : j ∈ s
  · exact hain j hj
  · have h0 := mem_of_mem_nhds (hW j)
    simp only [hz j, hj, ↓reduceIte] at h0
    rw [has j hj]
    exact h0

variable [∀ j, Module ℝ (E j)] [∀ j, ContinuousSMul ℝ (E j)] [∀ j, T1Space (E j)]

/-- The evaluation at `j`, as a continuous linear map. -/
def evalCLM (j : J) : LCDirectSum E →L[ℝ] E j where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_apply j

/-- **Sequential completeness** ([GN26, Lemma B.13.2(f)]). -/
instance seqComplete [∀ j, SeqComplete (E j)] : SeqComplete (LCDirectSum E) where
  exists_tendsto u hu := by
    classical
    obtain ⟨s, hs⟩ := exists_finset_of_isVonNBounded (isVonNBounded_range_of_cauchy hu)
    have hcoord : ∀ j, ∃ y : E j, Tendsto (fun k ↦ u k j) atTop (𝓝 y) := fun j ↦
      SeqComplete.exists_tendsto _ fun W hW ↦ by
        obtain ⟨N, hN⟩ := hu _ ((continuous_apply j).continuousAt.preimage_mem_nhds
          (by simpa using hW))
        exact ⟨N, fun m hm n hn ↦ by simpa using hN m hm n hn⟩
    choose y hy using hcoord
    exact ⟨_, tendsto_mk_of_finset (Eventually.of_forall fun k j hj ↦
      hs _ (mem_range_self k) j hj) fun j _ ↦ hy j⟩

/-- **Mackey completeness** ([GN26, Lemma B.13.2(f)]). -/
instance mackeyComplete [∀ j, MackeyComplete (E j)] : MackeyComplete (LCDirectSum E) where
  exists_tendsto u B r hB hr hu := by
    classical
    obtain ⟨s, hs⟩ := exists_finset_of_isVonNBounded (isVonNBounded_range_of_mackey hB hu)
    have hcoord : ∀ j, ∃ y : E j, Tendsto (fun k ↦ u k j) atTop (𝓝 y) := fun j ↦
      MackeyComplete.exists_tendsto _ (evalCLM j '' B) r (hB.image (evalCLM j)) hr
        fun k l hkl ↦ by
          obtain ⟨b, hb, he⟩ := hu k l hkl
          exact ⟨evalCLM j b, ⟨b, hb, rfl⟩, by
            beta_reduce at he ⊢
            rw [← map_smul]
            change (r k • b) j = u l j - u k j
            rw [he]
            rfl⟩
    choose y hy using hcoord
    exact ⟨_, tendsto_mk_of_finset (Eventually.of_forall fun k j hj ↦
      hs _ (mem_range_self k) j hj) fun j _ ↦ hy j⟩


section QuasiComplete

variable {J : Type*} {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, UniformSpace (E j)]
  [∀ j, IsUniformAddGroup (E j)] [∀ j, Module ℝ (E j)] [∀ j, ContinuousSMul ℝ (E j)]
  [∀ j, T1Space (E j)]

/-- **Quasi-completeness** ([GN26, Lemma B.13.2(f)]): a closed bounded set lies in a finite
partial sum, and the coordinates of a Cauchy filter on it converge in the closures of its
coordinate projections, which are closed and bounded. -/
instance quasiCompleteSpace [∀ j, QuasiCompleteSpace ℝ (E j)] :
    QuasiCompleteSpace ℝ (LCDirectSum E) where
  quasiComplete C hC hCc f hf hfC := by
    classical
    have : f.NeBot := hf.1
    obtain ⟨s, hs⟩ := exists_finset_of_isVonNBounded hC
    have hcoord : ∀ j, ∃ y : E j, Tendsto (fun x : LCDirectSum E ↦ x j) f (𝓝 y) := fun j ↦ by
      set e := evalAddHom (E := E) j
      have he : UniformContinuous e := uniformContinuous_addMonoidHom_of_continuous
        (continuous_apply j)
      have hK : IsComplete (closure (e '' C)) := QuasiCompleteSpace.quasiComplete
        ((hC.image (evalCLM j)).closure) isClosed_closure
      obtain ⟨y, -, hy⟩ := hK _ (hf.map he)
        ((map_mono hfC).trans (by rw [map_principal]; exact principal_mono.2 subset_closure))
      exact ⟨y, hy⟩
    choose y hy using hcoord
    have hlim := tendsto_mk_of_finset (l := f) (f := id) (s := s)
      (mem_of_superset (le_principal_iff.1 hfC) fun x hx ↦ hs x hx) fun j _ ↦ hy j
    exact ⟨_, hCc.mem_of_tendsto hlim (le_principal_iff.1 hfC), hlim⟩

end QuasiComplete

end LCDirectSum

namespace LCDirectLimit

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {S : ℕ → Submodule ℝ V}
  [∀ n, TopologicalSpace (S n)] [∀ n, IsTopologicalAddGroup (S n)] [∀ n, ContinuousSMul ℝ (S n)]
  [∀ n, LocallyConvexSpace ℝ (S n)]

/-- **Strict direct limits of Mackey complete spaces with closed steps are Mackey complete**
([GN26, Proposition B.13.9(e)]): the bounded set `B` and the (bounded) range of a
Mackey–Cauchy sequence lie, and are bounded, in a common step, where the sequence is Mackey–Cauchy
(bounded regularity, Proposition B.13.9(c)). -/
theorem IsStrict.mackeyComplete [∀ n, MackeyComplete (S n)] (hS : IsStrict S)
    (hclosed : ∀ n, IsClosed (range (Submodule.inclusion (hS.mono (Nat.le_succ n))))) :
    MackeyComplete (LCDirectLimit S) where
  exists_tendsto u B r hB hr hu := by
    obtain ⟨n, hn, hbn⟩ := hS.exists_subset_isVonNBounded hclosed
      (hB.union (isVonNBounded_range_of_mackey hB hu))
    set u' : ℕ → S n := fun k ↦ ⟨u k, hn _ (Or.inr (mem_range_self k))⟩
    obtain ⟨y, hy⟩ := MackeyComplete.exists_tendsto u' _ r hbn hr fun k l hkl ↦ by
      obtain ⟨b, hb, he⟩ := hu k l hkl
      refine ⟨⟨b, hn b (Or.inl hb)⟩, Or.inl hb, Subtype.ext ?_⟩
      exact he
    exact ⟨incl S n y, ((continuous_incl S n).tendsto y).comp hy⟩

end LCDirectLimit

end LocallyConvex.Analysis

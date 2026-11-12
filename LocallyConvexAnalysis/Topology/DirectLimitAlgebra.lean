/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Topology.DirectLimit
public import LocallyConvexAnalysis.Spaces.DirectLimit

/-!
# Direct limits of topological groups and vector spaces

Reference: [GN26, Definition A.7.10, Proposition A.7.11, Corollary A.7.12] (pp. 887–889).

Let `S 0 ≤ S 1 ≤ ⋯` be subgroups of a group `G` covering `G`, each a topological group, with
continuous inclusions. We study the group structure of the direct limit topology on `G`, and the
vector space structure when the `S n` are subspaces of a real vector space.

## Main definitions

* `prodSet S U n`: the products `U₀ U₁ ⋯ Uₙ` of subsets `Uₖ ⊆ S k`, in the direct limit (with an
  additive version, the sums `U₀ + U₁ + ⋯ + Uₙ`).

## Main results

* `TopDirectLimit.continuous_inv'`, `TopDirectLimit.continuous_mul_left'`,
  `TopDirectLimit.continuous_mul_right'`: in the direct limit topology, inversion and translations
  are continuous ([GN26, Proposition A.7.11]).
* `IsDirectSeq.IsCompactifying.isTopologicalGroup`: for compactifying sequences of Hausdorff
  groups, the direct limit is a topological group ([GN26, Proposition A.7.11]), and
  `IsDirectSeq.IsCompactifying.nhds_one_hasBasis`: the sets `⋃ₙ U₀ U₁ ⋯ Uₙ`, for open identity
  neighbourhoods `Uₙ ⊆ S n`, form a basis of identity neighbourhoods.
* `IsDirectSeq.isTopologicalGroup_of_locallyCompactSpace`: direct limits of locally compact
  groups are topological groups ([GN26, Example A.7.13]).
* The additive versions, and for subspaces of a real vector space:
  `IsDirectSeq.IsCompactifying.continuousSMul` and `IsDirectSeq.IsCompactifying.locallyConvexSpace`:
  compactifying direct limits of Hausdorff (locally convex) topological vector spaces are
  (locally convex) topological vector spaces ([GN26, Corollary A.7.12]).
* `IsDirectSeq.IsCompactifying.topology_eq_lcDirectLimit`: the topology of a compactifying direct
  limit of Hausdorff locally convex spaces is the locally convex direct limit topology.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology
open scoped Topology Pointwise

noncomputable section

namespace LocallyConvex.Analysis

open TopDirectLimit

universe u

namespace TopDirectLimit

variable {X : Type u} {ι : Type*} (S : ι → Set X) [∀ i, TopologicalSpace (S i)]

@[to_additive]
instance [h : Group X] : Group (TopDirectLimit S) := h

instance [h : AddCommGroup X] : AddCommGroup (TopDirectLimit S) := h

instance {𝕜 : Type*} [Semiring 𝕜] [AddCommGroup X] [h : Module 𝕜 X] :
    Module 𝕜 (TopDirectLimit S) := h

end TopDirectLimit

/-! ### Groups -/

section Group

variable {G : Type u} [Group G] {S : ℕ → Subgroup G} [t : ∀ n, TopologicalSpace (S n)]

/-- The topology of the subgroup `S n`, on the set `S n`. -/
@[to_additive (attr := reducible) /-- The topology of the subgroup `S n`, on the set `S n`. -/]
def subgroupTop (n : ℕ) : TopologicalSpace ((S n : Set G)) := t n

attribute [local instance] subgroupTop addSubgroupTop

/-- The trace of a set on the subgroup `S n`. -/
@[to_additive /-- The trace of a set on the subgroup `S n`. -/]
theorem incl_subgroup_mul (n : ℕ) (a b : S n) :
    incl (fun n ↦ (S n : Set G)) n (a * b) =
      incl (fun n ↦ (S n : Set G)) n a * incl (fun n ↦ (S n : Set G)) n b := rfl

variable [∀ n, IsTopologicalGroup (S n)]

/-- **Inversion is continuous** in the direct limit topology
([GN26, Proposition A.7.11]). -/
@[to_additive /-- **Negation is continuous** in the direct limit topology
([GN26, Proposition A.7.11]). -/]
theorem TopDirectLimit.continuous_inv' :
    Continuous fun x : TopDirectLimit (fun n ↦ (S n : Set G)) ↦ x⁻¹ :=
  continuous_iff.2 fun n ↦ (continuous_incl (fun n ↦ (S n : Set G)) n).comp
    (continuous_inv : Continuous fun a : S n ↦ a⁻¹)

/-- **Left translations are continuous** in the direct limit topology
([GN26, Proposition A.7.11]). -/
@[to_additive /-- **Translations are continuous** in the direct limit topology
([GN26, Proposition A.7.11]). -/]
theorem TopDirectLimit.continuous_mul_left' (hS : IsDirectSeq fun n ↦ (S n : Set G))
    (g : TopDirectLimit fun n ↦ (S n : Set G)) : Continuous fun x ↦ g * x := by
  obtain ⟨n₀, hg⟩ := hS.exists_mem g
  refine continuous_iff.2 fun n ↦ ?_
  set k := max n n₀
  have hcont : Continuous fun y : S k ↦ incl (fun n ↦ (S n : Set G)) k (⟨g, hS.mono
      (le_max_right n n₀) hg⟩ * y) :=
    (continuous_incl (fun n ↦ (S n : Set G)) k).comp
      ((continuous_const.mul continuous_id : Continuous fun y : S k ↦ _ * y))
  exact (hcont.comp (hS.continuous_inclusion_of_le (le_max_left n n₀))).congr fun x ↦ rfl

/-- **Right translations are continuous** in the direct limit topology
([GN26, Proposition A.7.11]). -/
@[to_additive /-- **Right translations are continuous** in the direct limit topology
([GN26, Proposition A.7.11]). -/]
theorem TopDirectLimit.continuous_mul_right' (hS : IsDirectSeq fun n ↦ (S n : Set G))
    (g : TopDirectLimit fun n ↦ (S n : Set G)) : Continuous fun x ↦ x * g := by
  obtain ⟨n₀, hg⟩ := hS.exists_mem g
  refine continuous_iff.2 fun n ↦ ?_
  set k := max n n₀
  have hcont : Continuous fun y : S k ↦ incl (fun n ↦ (S n : Set G)) k (y * ⟨g, hS.mono
      (le_max_right n n₀) hg⟩) :=
    (continuous_incl (fun n ↦ (S n : Set G)) k).comp
      ((continuous_id.mul continuous_const : Continuous fun y : S k ↦ y * _))
  exact (hcont.comp (hS.continuous_inclusion_of_le (le_max_left n n₀))).congr fun x ↦ rfl

/-- **Compactifying direct limits of Hausdorff topological groups are topological groups**
([GN26, Proposition A.7.11]): multiplication is continuous by Lemma A.7.9. -/
@[to_additive /-- **Compactifying direct limits of Hausdorff topological groups are topological
groups** ([GN26, Proposition A.7.11]): addition is continuous by Lemma A.7.9. -/]
theorem IsDirectSeq.IsCompactifying.isTopologicalGroup {hS : IsDirectSeq fun n ↦ (S n : Set G)}
    (hc : hS.IsCompactifying) [∀ n, T2Space (S n)] :
    IsTopologicalGroup (TopDirectLimit fun n ↦ (S n : Set G)) where
  continuous_mul := (hc.continuous_prod_iff hc).2 fun n ↦
    (continuous_incl (fun n ↦ (S n : Set G)) n).comp
      (continuous_mul : Continuous fun p : S n × S n ↦ p.1 * p.2)
  continuous_inv := TopDirectLimit.continuous_inv'

variable (S) in
/-- The products `U₀ U₁ ⋯ Uₙ` of subsets `Uₖ ⊆ S k`, in the direct limit. -/
@[to_additive /-- The sums `U₀ + U₁ + ⋯ + Uₙ` of subsets `Uₖ ⊆ S k`, in the direct limit. -/]
def prodSet (U : ∀ n, Set (S n)) (n : ℕ) : Set (TopDirectLimit fun n ↦ (S n : Set G)) :=
  Nat.rec (incl (fun n ↦ (S n : Set G)) 0 '' U 0)
    (fun k P ↦ P * incl (fun n ↦ (S n : Set G)) (k + 1) '' U (k + 1)) n

omit [∀ n, IsTopologicalGroup (S n)] in
@[to_additive]
theorem prodSet_subset (hS : IsDirectSeq fun n ↦ (S n : Set G)) (U : ∀ n, Set (S n)) :
    ∀ n, prodSet S U n ⊆ (S n : Set G) := by
  intro n
  induction n with
  | zero => exact image_subset_iff.2 fun x _ ↦ x.2
  | succ n ih =>
    rintro _ ⟨p, hp, _, ⟨q, -, rfl⟩, rfl⟩
    exact (S (n + 1)).mul_mem (hS.mono (Nat.le_succ n) (ih hp)) q.2

omit [∀ n, IsTopologicalGroup (S n)] in
@[to_additive]
theorem prodSet_mono (U : ∀ n, Set (S n)) (hU : ∀ n, (1 : S n) ∈ U n) :
    Monotone (prodSet S U) :=
  monotone_nat_of_le_succ fun n x hx ↦ ⟨x, hx, 1, ⟨1, hU (n + 1), rfl⟩, mul_one x⟩

@[to_additive]
theorem isOpen_preimage_prodSet (hS : IsDirectSeq fun n ↦ (S n : Set G)) {U : ∀ n, Set (S n)}
    (hU : ∀ n, IsOpen (U n)) : ∀ n, IsOpen (incl (fun n ↦ (S n : Set G)) n ⁻¹' prodSet S U n) := by
  have hinj : ∀ k, Injective (incl (fun n ↦ (S n : Set G)) k) := fun k ↦ Subtype.val_injective
  intro n
  induction n with
  | zero =>
    change IsOpen (incl (fun n ↦ (S n : Set G)) 0 ⁻¹' (incl (fun n ↦ (S n : Set G)) 0 '' U 0))
    rw [(hinj 0).preimage_image]
    exact hU 0
  | succ n ih =>
    set P := prodSet S U n
    have hP : P ⊆ (S (n + 1) : Set G) := (prodSet_subset hS U n).trans (hS.mono (Nat.le_succ n))
    set ι := incl (fun n ↦ (S n : Set G)) (n + 1)
    have : ι ⁻¹' (P * ι '' U (n + 1)) = (ι ⁻¹' P) * U (n + 1) := by
      ext y
      constructor
      · rintro ⟨p, hp, _, ⟨q, hq, rfl⟩, hpq⟩
        refine ⟨⟨p, hP hp⟩, hp, q, hq, hinj (n + 1) ?_⟩
        exact hpq
      · rintro ⟨a, ha, q, hq, rfl⟩
        exact ⟨_, ha, _, ⟨q, hq, rfl⟩, rfl⟩
    change IsOpen (ι ⁻¹' (P * ι '' U (n + 1)))
    rw [this]
    exact (hU (n + 1)).mul_left

/-- **A basis of identity neighbourhoods of a compactifying direct limit of Hausdorff groups**
([GN26, Proposition A.7.11]): the sets `⋃ₙ U₀ U₁ ⋯ Uₙ`, where `Uₙ` ranges through the open
identity neighbourhoods of `S n`. Given an identity neighbourhood `P₀`, choose open identity
neighbourhoods with `Pₖ₊₁ Pₖ₊₁ ⊆ Pₖ` and `Uₙ = Pₙ₊₁ ∩ S n`; then `U₀ ⋯ Uₙ Pₙ₊₁ ⊆ P₀`. -/
@[to_additive /-- **A basis of zero neighbourhoods of a compactifying direct limit of Hausdorff
groups** ([GN26, Proposition A.7.11]): the sets `⋃ₙ (U₀ + U₁ + ⋯ + Uₙ)`, where `Uₙ` ranges
through the open zero neighbourhoods of `S n`. -/]
theorem IsDirectSeq.IsCompactifying.nhds_one_hasBasis {hS : IsDirectSeq fun n ↦ (S n : Set G)}
    (hc : hS.IsCompactifying) [∀ n, T2Space (S n)] :
    (𝓝 (1 : TopDirectLimit fun n ↦ (S n : Set G))).HasBasis
      (fun U : ∀ n, Set (S n) ↦ ∀ n, IsOpen (U n) ∧ (1 : S n) ∈ U n)
      fun U ↦ ⋃ n, prodSet S U n := by
  have := hc.isTopologicalGroup
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨U, hU, hsub⟩ ↦ mem_of_superset ?_ hsub⟩⟩
  · -- a decreasing sequence of open identity neighbourhoods
    choose! f hfo hf1 hfm using fun (W : Set (TopDirectLimit fun n ↦ (S n : Set G)))
      (hW : W ∈ 𝓝 1) ↦ exists_open_nhds_one_mul_subset hW
    let P : ℕ → Set (TopDirectLimit fun n ↦ (S n : Set G)) := fun k ↦
      Nat.rec (interior t) (fun _ A ↦ f A) k
    have hPn : ∀ k, IsOpen (P k) ∧ (1 : TopDirectLimit fun n ↦ (S n : Set G)) ∈ P k := by
      intro k
      induction k with
      | zero => exact ⟨isOpen_interior, mem_interior_iff_mem_nhds.2 ht⟩
      | succ k ih =>
        have h := ih.1.mem_nhds ih.2
        change IsOpen (f (P k)) ∧ 1 ∈ f (P k)
        exact ⟨hfo _ h, hf1 _ h⟩
    have hPm : ∀ k, P (k + 1) * P (k + 1) ⊆ P k := fun k ↦
      hfm (P k) ((hPn k).1.mem_nhds (hPn k).2)
    set U : ∀ n, Set (S n) := fun n ↦ incl (fun n ↦ (S n : Set G)) n ⁻¹' P (n + 1)
    have hU : ∀ n, IsOpen (U n) ∧ (1 : S n) ∈ U n := fun n ↦
      ⟨(hPn (n + 1)).1.preimage (continuous_incl (fun n ↦ (S n : Set G)) n), (hPn (n + 1)).2⟩
    have hUP : ∀ n, incl (fun n ↦ (S n : Set G)) n '' U n ⊆ P (n + 1) := fun n ↦
      image_preimage_subset _ _
    have key : ∀ n, prodSet S U n * P (n + 1) ⊆ P 0 := by
      intro n
      induction n with
      | zero => exact (mul_subset_mul_right (hUP 0)).trans (hPm 0)
      | succ n ih =>
        change prodSet S U n * incl (fun n ↦ (S n : Set G)) (n + 1) '' U (n + 1) *
          P (n + 1 + 1) ⊆ P 0
        rw [mul_assoc]
        exact (mul_subset_mul_left ((mul_subset_mul_right (hUP (n + 1))).trans
          (hPm (n + 1)))).trans ih
    refine ⟨U, hU, iUnion_subset fun n ↦ ?_⟩
    exact (subset_mul_left _ (hPn (n + 1)).2).trans ((key n).trans interior_subset)
  · exact (hS.isOpen_iUnion (prodSet_mono U fun n ↦ (hU n).2)
      (isOpen_preimage_prodSet hS fun n ↦ (hU n).1)).mem_nhds
      (mem_iUnion.2 ⟨0, 1, (hU 0).2, rfl⟩)

/-- **Direct limits of locally compact groups are topological groups**
([GN26, Example A.7.13]). -/
@[to_additive /-- **Direct limits of locally compact additive groups are topological groups**
([GN26, Example A.7.13]). -/]
theorem IsDirectSeq.isTopologicalGroup_of_locallyCompactSpace
    (hS : IsDirectSeq fun n ↦ (S n : Set G)) [∀ n, LocallyCompactSpace (S n)]
    [∀ n, T2Space (S n)] : IsTopologicalGroup (TopDirectLimit fun n ↦ (S n : Set G)) :=
  hS.isCompactifying_of_locallyCompactSpace.isTopologicalGroup

end Group

/-! ### Vector spaces -/

section Module

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {S : ℕ → Submodule ℝ E}
  [t : ∀ n, TopologicalSpace (S n)]

/-- The topology of the subspace `S n`, on the set `S n`. -/
abbrev submoduleTop (n : ℕ) : TopologicalSpace ((S n : Set E)) := t n

attribute [local instance] submoduleTop

/-- The direct limit topology of the steps of a sequence of subspaces. -/
local notation "lim" S => TopDirectLimit fun n ↦ ((S n : Submodule ℝ E) : Set E)

variable [∀ n, IsTopologicalAddGroup (S n)] [∀ n, ContinuousSMul ℝ (S n)]

/-- The constant direct sequence `ℝ ⊆ ℝ ⊆ ⋯`. -/
theorem isDirectSeq_univ_real : IsDirectSeq fun _ : ℕ ↦ (univ : Set ℝ) :=
  ⟨fun _ _ _ ↦ subset_rfl, fun x ↦ ⟨0, mem_univ x⟩, fun _ ↦ continuous_inclusion _⟩

/-- The direct limit of the constant sequence `ℝ ⊆ ℝ ⊆ ⋯` is `ℝ`. -/
theorem continuous_toTopDirectLimit_univ_real :
    Continuous (X := ℝ) (Y := TopDirectLimit fun _ : ℕ ↦ (univ : Set ℝ)) id :=
  continuous_def.2 fun M hM ↦ by
    have h0 := (TopDirectLimit.isOpen_iff (S := fun _ : ℕ ↦ (univ : Set ℝ)) (M := M)).1 hM 0
    exact (Homeomorph.Set.univ ℝ).isOpen_preimage.1 h0

omit [∀ n, ContinuousSMul ℝ (S n)] in
/-- **Compactifying direct limits of Hausdorff topological vector spaces are topological vector
spaces** ([GN26, Corollary A.7.12]): addition is continuous by Proposition A.7.11, and
scalar multiplication by Lemma A.7.9, since `ℝ ⊆ ℝ ⊆ ⋯` is compactifying. -/
theorem IsDirectSeq.IsCompactifying.isTopologicalAddGroup_submodule
    {hS : IsDirectSeq fun n ↦ (S n : Set E)} (hc : hS.IsCompactifying) [∀ n, T2Space (S n)] :
    IsTopologicalAddGroup (lim S) where
  continuous_add := (hc.continuous_prod_iff hc).2 fun n ↦
    (continuous_incl (fun n ↦ (S n : Set E)) n).comp
      (continuous_add : Continuous fun p : S n × S n ↦ p.1 + p.2)
  continuous_neg := continuous_iff.2 fun n ↦ (continuous_incl (fun n ↦ (S n : Set E)) n).comp
    (continuous_neg : Continuous fun a : S n ↦ -a)

omit [∀ n, IsTopologicalAddGroup (S n)] in
/-- **Scalar multiplication on a compactifying direct limit of Hausdorff topological vector
spaces is continuous** ([GN26, Corollary A.7.12]). -/
theorem IsDirectSeq.IsCompactifying.continuousSMul {hS : IsDirectSeq fun n ↦ (S n : Set E)}
    (hc : hS.IsCompactifying) [∀ n, T2Space (S n)] : ContinuousSMul ℝ (lim S) := by
  have hR := isDirectSeq_univ_real
  have : ∀ _ : ℕ, LocallyCompactSpace (univ : Set ℝ) := fun _ ↦
    isClosed_univ.locallyCompactSpace
  have hcR := hR.isCompactifying_of_locallyCompactSpace
  have hm : Continuous fun p : (TopDirectLimit fun _ : ℕ ↦ (univ : Set ℝ)) × (lim S) ↦
      ((show ℝ from p.1) • p.2 : lim S) :=
    (hcR.continuous_prod_iff hc).2 fun n ↦ (continuous_incl (fun n ↦ (S n : Set E)) n).comp
      ((continuous_subtype_val.comp continuous_fst).smul continuous_snd :
        Continuous fun p : ↥(univ : Set ℝ) × S n ↦ (p.1 : ℝ) • p.2)
  exact ⟨hm.comp (continuous_toTopDirectLimit_univ_real.prodMap continuous_id)⟩

/-- **Compactifying direct limits of Hausdorff locally convex spaces are locally convex**
([GN26, Corollary A.7.12]): in the basis `⋃ₙ (U₀ + ⋯ + Uₙ)` of Proposition A.7.11 the
`Uₙ` may be taken convex, and ascending unions of convex sets are convex. -/
theorem IsDirectSeq.IsCompactifying.locallyConvexSpace {hS : IsDirectSeq fun n ↦ (S n : Set E)}
    (hc : hS.IsCompactifying) [∀ n, T2Space (S n)] [∀ n, LocallyConvexSpace ℝ (S n)] :
    LocallyConvexSpace ℝ (lim S) := by
  have := hc.isTopologicalAddGroup_submodule
  -- the basis of Proposition A.7.11, for the additive subgroups underlying the `S n`
  have hb := IsDirectSeq.IsCompactifying.nhds_zero_hasBasis (S := fun n ↦ (S n).toAddSubgroup)
    (t := t) (hS := hS) hc
  refine (locallyConvexSpace_iff_exists_convex_subset_zero ℝ _).2 fun U hU ↦ ?_
  obtain ⟨W, hW, hWU⟩ := hb.mem_iff.1 hU
  -- convex open `0`-neighbourhoods `C n ⊆ W n`
  have hC : ∀ n, ∃ C : Set (S n), IsOpen C ∧ (0 : S n) ∈ C ∧ Convex ℝ C ∧ C ⊆ W n := by
    intro n
    obtain ⟨D, ⟨hD, hDc⟩, hDW⟩ := (LocallyConvexSpace.convex_basis_zero ℝ (S n)).mem_iff.1
      ((hW n).1.mem_nhds (hW n).2)
    exact ⟨interior D, isOpen_interior, mem_interior_iff_mem_nhds.2 hD, hDc.interior,
      interior_subset.trans hDW⟩
  choose C hCo hC0 hCc hCW using hC
  have hsub : ∀ n, sumSet (fun n ↦ (S n).toAddSubgroup) C n ⊆
      sumSet (fun n ↦ (S n).toAddSubgroup) W n := by
    intro n
    induction n with
    | zero => exact image_mono (hCW 0)
    | succ n ih => exact add_subset_add ih (image_mono (hCW (n + 1)))
  have hconv : ∀ n, Convex ℝ (sumSet (fun n ↦ (S n).toAddSubgroup) C n : Set (lim S)) := by
    intro n
    induction n with
    | zero => exact (hCc 0).linear_image (S 0).subtype
    | succ n ih => exact ih.add ((hCc (n + 1)).linear_image (S (n + 1)).subtype)
  refine ⟨⋃ n, sumSet (fun n ↦ (S n).toAddSubgroup) C n,
    hb.mem_of_mem fun n ↦ ⟨hCo n, hC0 n⟩, ?_, (iUnion_mono hsub).trans hWU⟩
  have hdir : Directed (· ⊆ ·)
      fun n ↦ (sumSet (fun n ↦ (S n).toAddSubgroup) C n : Set (lim S)) :=
    (sumSet_mono (S := fun n ↦ (S n).toAddSubgroup) (t := t) C hC0).directed_le
  exact hdir.convex_iUnion fun n ↦ hconv n

/-- **The direct limit topology of a compactifying sequence of Hausdorff locally convex spaces is
the locally convex direct limit topology** (compare [GN26, Proposition B.13.13(a)] for
Silva spaces): it is locally convex (Corollary A.7.12), so the identity of `LCDirectLimit S` into
it is continuous by the universal property; the converse holds since it is the finest topology
making the inclusions continuous. -/
theorem IsDirectSeq.IsCompactifying.topology_eq_lcDirectLimit
    {hS : IsDirectSeq fun n ↦ (S n : Set E)} (hc : hS.IsCompactifying) [∀ n, T2Space (S n)]
    [∀ n, LocallyConvexSpace ℝ (S n)] :
    (inferInstanceAs (TopologicalSpace (LCDirectLimit S)) : TopologicalSpace E) =
      TopDirectLimit.topology fun n ↦ (S n : Set E) := by
  have := hc.isTopologicalAddGroup_submodule
  have := hc.continuousSMul
  have := hc.locallyConvexSpace
  refine le_antisymm ?_ (TopDirectLimit.topology_le fun n ↦ LCDirectLimit.continuous_incl S n)
  let f : LCDirectLimit S →ₗ[ℝ] lim S :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hf : Continuous f := LCDirectLimit.continuous_of_continuous_comp_incl S f fun n ↦
    continuous_incl (fun n ↦ (S n : Set E)) n
  exact continuous_id_iff_le.1 hf

end Module

end LocallyConvex.Analysis

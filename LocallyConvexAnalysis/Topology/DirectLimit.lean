/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-!
# Direct limits of topological spaces

Let `S i ⊆ X` be subsets of a set `X`, each with its own topology. The **direct limit topology**
on `X` is the final topology of the inclusions `S i → X` (Definition A.7.1 and
Remark A.7.15(a)). We prove its basic properties, and those of direct limits of ascending
sequences: strict, compactifying, compactly regular, and the `k_ω` property. Groups and vector
spaces are in `Topology/DirectLimitAlgebra.lean`.

Reference: [GN26, Appendix A.7] (pp. 883–892).

## Main definitions

* `TopDirectLimit S`: `X` with the direct limit topology of the subsets `S i`
  (Definition A.7.1, Remark A.7.15(a)).
* `IsDirectSeq S`: an ascending sequence `S 0 ⊆ S 1 ⊆ ⋯` of subsets covering `X`, with
  continuous inclusions (Definition A.7.1).
* `IsDirectSeq.IsStrict`: each step carries the topology induced by the next.
* `IsDirectSeq.IsCompactifying`: every point of a step has a neighbourhood whose image in some
  later step has compact closure (Definition A.7.1).
* `IsDirectSeq.CompactlyRegular`: every compact subset of the limit lies, and is compact, in some
  step (Definition A.7.5).
* `IsKOmegaSpace`, `IsLocallyKOmegaSpace`: `k_ω`-spaces and locally `k_ω` spaces
  (Definition A.7.18).

## Main results

* `TopDirectLimit.isOpen_iff`, `TopDirectLimit.isClosed_iff`: a set is open (closed) iff its
  traces on all `S i` are (Remark A.7.2(a)).
* `TopDirectLimit.topology_le`: the direct limit topology is the finest one making the inclusions
  continuous (Remark A.7.2(b)); `TopDirectLimit.continuous_iff` and
  `TopDirectLimit.eq_topology_iff`: the universal property, which characterizes it
  (Lemma A.7.3).
* `TopDirectLimit.topology_eq_comp`: a cofinal subsequence gives the same topology (Remarks
  A.7.2(d) and A.7.15(b)).
* The `T1Space` instance on `TopDirectLimit S`: the limit of `T₁` spaces is `T₁`
  (Lemma A.7.6(d)).
* `TopDirectLimit.topology_subtype_eq`: open and closed subsets carry the direct limit topology of
  their traces (Lemma A.7.6(c)); `IsDirectSeq.topology_iUnion_eq`: so do ascending unions of open
  subsets `Vₙ ⊆ S n`, with respect to the `Vₙ` (Lemma A.7.6(b)).
* `TopDirectLimit.continuous_map`: compatible continuous maps give a continuous map of direct
  limits (Definition A.7.8).

For ascending sequences `S 0 ⊆ S 1 ⊆ ⋯` covering `X`, with continuous inclusions (`IsDirectSeq`):

* `IsDirectSeq.isOpen_iUnion`: ascending unions of open subsets of the steps are open
  (Lemma A.7.6(a)).
* `IsDirectSeq.exists_subset_of_isCompact`: compact subsets of a limit of `T₁` spaces lie in some
  step (Lemma A.7.6(e)).
* `IsDirectSeq.IsStrict.isEmbedding_incl`: for strict sequences, the steps are embedded
  (Lemma A.7.6(f)), and `IsDirectSeq.IsStrict.compactlyRegular`: strict sequences of `T₁` spaces
  are compactly regular (Definition A.7.5, Lemma A.7.6(g)).
* `IsDirectSeq.isCompactifying_of_locallyCompactSpace`, `IsDirectSeq.isStrict_of_compactSpace`:
  locally compact Hausdorff steps are compactifying, compact Hausdorff steps strict
  (Remark A.7.2(c)).

For compactifying sequences of Hausdorff spaces (`IsDirectSeq.IsCompactifying`):

* `IsDirectSeq.IsCompactifying.exists_isOpen`, `IsDirectSeq.IsCompactifying.exists_disjoint`:
  Lemma A.7.4.
* `IsDirectSeq.IsCompactifying.t2Space`: the limit is Hausdorff (Lemma A.7.6(h)).
* `IsDirectSeq.IsCompactifying.isOpen_prod_iff`,
  `IsDirectSeq.IsCompactifying.continuous_prod_iff`: `lim Sₙ × lim Tₙ = lim (Sₙ × Tₙ)`
  (Lemma A.7.9).
* `IsDirectSeq.exists_nested_nhds`: nested relatively compact neighbourhoods for locally compact
  steps (Lemma A.7.22); `IsDirectSeq.IsCompactifying.isCompactifying_unionSet`: the sets `Vₙ` of
  Lemma A.7.6(b) form a compactifying sequence (Remark A.7.7).
* `IsDirectSeq.IsCompactifying.compactlyRegular`,
  `IsDirectSeq.IsCompactifying.isLocallyKOmegaSpace`: the limit is compactly regular and locally
  `k_ω` (`IsKOmegaSpace`, `IsLocallyKOmegaSpace`, Definition A.7.18, Proposition A.7.20).

## Implementation notes

* The steps are subsets of a fixed set `X`, each with its own topology; `TopDirectLimit S` is a
  type synonym for `X`. The constructions of Lemmas A.7.6(f), (h), A.7.9 and Proposition A.7.20
  are recursions on a subtype of data satisfying an invariant.
* In Proposition A.7.20, GN show that the compact subsets of `V = ⋃ⱼ Vⱼ` lie in some `Kⱼ` through
  `V = lim Kⱼ` (Lemma A.7.6(b) and Exercise A.7.7) and Lemma A.7.6(g). We argue directly: a set
  meeting every `Kⱼ` in a closed set is closed in `V` (`isOpen_iUnion_diff_of_chain`), so points
  `yⱼ ∈ L \ Kⱼ` would form an infinite closed discrete subset of `L`. We do not claim this argument
  is new.
* Example A.7.17 and Remark A.7.19 are in `Topology/KOmega.lean`, Remark A.7.21 in
  `Topology/KOmegaLimits.lean`, Examples A.7.14 and A.7.16 in `Topology/FiniteTopology.lean`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

set_option linter.unusedVariables false in
/-- `X` with the direct limit topology of the subsets `S i`, each carrying its own topology
([GN26, Definition A.7.1, Remark A.7.15(a)]). -/
@[nolint unusedArguments]
def TopDirectLimit {X : Type u} {ι : Type v} (S : ι → Set X) [∀ i, TopologicalSpace (S i)] :
    Type u :=
  X

namespace TopDirectLimit

variable {X : Type u} {ι : Type v} (S : ι → Set X) [∀ i, TopologicalSpace (S i)]

/-- The direct limit topology: the final topology of the inclusions `S i → X`. -/
instance instTopologicalSpace : TopologicalSpace (TopDirectLimit S) :=
  ⨆ i, TopologicalSpace.coinduced ((↑) : S i → X) inferInstance

/-- The direct limit topology, as a topology on `X`. -/
abbrev topology : TopologicalSpace X := instTopologicalSpace S

/-- The inclusion of the step `S i`. -/
def incl (i : ι) : S i → TopDirectLimit S := Subtype.val

@[simp] theorem incl_apply (i : ι) (x : S i) : incl S i x = (x : X) := rfl

variable {S}

/-- **Open sets** are detected on the steps ([GN26, Remark A.7.2(a)]). -/
theorem isOpen_iff {M : Set (TopDirectLimit S)} : IsOpen M ↔ ∀ i, IsOpen (incl S i ⁻¹' M) := by
  change IsOpen[⨆ i, _] M ↔ _
  rw [isOpen_iSup_iff]
  rfl

/-- **Closed sets** are detected on the steps ([GN26, Remark A.7.2(a)]). -/
theorem isClosed_iff {M : Set (TopDirectLimit S)} :
    IsClosed M ↔ ∀ i, IsClosed (incl S i ⁻¹' M) := by
  rw [← isOpen_compl_iff, isOpen_iff]
  simp only [preimage_compl, isOpen_compl_iff]

variable (S) in
/-- The inclusions are continuous ([GN26, Remark A.7.2(b)]). -/
theorem continuous_incl (i : ι) : Continuous (incl S i) :=
  continuous_iSup_rng continuous_coinduced_rng

/-- **The universal property** ([GN26, Lemma A.7.3]): a map on the direct limit is
continuous iff its restrictions to the steps are. -/
theorem continuous_iff {Y : Type w} [TopologicalSpace Y] {f : TopDirectLimit S → Y} :
    Continuous f ↔ ∀ i, Continuous (f ∘ incl S i) :=
  continuous_iSup_dom.trans (forall_congr' fun _ ↦ continuous_coinduced_dom)

/-- **The direct limit topology is the finest topology making the inclusions continuous**
([GN26, Remark A.7.2(b)]). In Mathlib's order, finer topologies are smaller. -/
theorem topology_le {τ : TopologicalSpace X} (h : ∀ i, Continuous[_, τ] ((↑) : S i → X)) :
    topology S ≤ τ :=
  iSup_le fun i ↦ continuous_iff_coinduced_le.1 (h i)

/-- **Characterization of the direct limit topology** ([GN26, Lemma A.7.3]): a topology
on `X` is the direct limit topology iff the inclusions are continuous and a map on `X` is
continuous as soon as its restrictions to the steps are. -/
theorem eq_topology_iff {τ : TopologicalSpace X} :
    τ = topology S ↔ (∀ i, Continuous[_, τ] ((↑) : S i → X)) ∧
      ∀ (Y : Type u) [TopologicalSpace Y] (f : X → Y),
        (∀ i, Continuous (f ∘ ((↑) : S i → X))) → Continuous[τ, _] f := by
  constructor
  · rintro rfl
    exact ⟨fun i ↦ continuous_incl S i, fun Y _ f hf ↦ continuous_iff.2 hf⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm ?_ (topology_le h1)
    -- the identity `(X, τ) → (X, topology S)` is continuous
    have : Continuous[τ, topology S] id := h2 (TopDirectLimit S) id fun i ↦ continuous_incl S i
    exact continuous_id_iff_le.1 this

/-- **Direct limits of maps** ([GN26, Definition A.7.8]): a map compatible with the steps
whose restrictions are continuous is continuous on the direct limits. -/
theorem continuous_map {Y : Type w} {κ : Type*} {T : κ → Set Y} [∀ k, TopologicalSpace (T k)]
    {f : X → Y} (σ : ι → κ) (hmaps : ∀ i, MapsTo f (S i) (T (σ i)))
    (hcont : ∀ i, Continuous ((hmaps i).restrict f (S i) (T (σ i)))) :
    Continuous (show TopDirectLimit S → TopDirectLimit T from f) :=
  continuous_iff.2 fun i ↦ (continuous_incl T (σ i)).comp (hcont i)

/-- **Cofinal subsequences** ([GN26, Remarks A.7.2(d)] and A.7.15(b)): if the inclusions
`S i → S j`, `i ≤ j`, are continuous and `φ : κ → ι` is cofinal, the direct limit topologies of
`S` and `S ∘ φ` agree. -/
theorem topology_eq_comp [Preorder ι] {κ : Type*} (hmono : Monotone S)
    (hcont : ∀ {i j} (hij : i ≤ j), Continuous (inclusion (hmono hij))) (φ : κ → ι)
    (hφ : ∀ i, ∃ k, i ≤ φ k) :
    topology S = topology (fun k ↦ S (φ k)) := by
  refine TopologicalSpace.ext (funext fun M ↦ propext ?_)
  refine (isOpen_iff (S := S) (M := M)).trans (Iff.trans ?_
    (isOpen_iff (S := fun k ↦ S (φ k)) (M := M)).symm)
  refine ⟨fun h k ↦ h (φ k), fun h i ↦ ?_⟩
  obtain ⟨k, hk⟩ := hφ i
  exact (h k).preimage (hcont hk)

/-- **Limits of `T₁` spaces are `T₁`** ([GN26, Lemma A.7.6(d)]), for any family of
steps. -/
instance [∀ i, T1Space (S i)] : T1Space (TopDirectLimit S) where
  t1 _ := isClosed_iff.2 fun _ ↦ (Set.subsingleton_singleton.preimage
    Subtype.val_injective).finite.isClosed

/-! ### Open and closed subsets -/

section Subset

variable (M : Set (TopDirectLimit S))

/-- The trace `M ∩ S i`, as a subset of `M`. -/
def traceSet (i : ι) : Set M := {a | (a.1 : X) ∈ S i}

/-- The inclusion of the trace `M ∩ S i` into `S i`. -/
def traceMap (i : ι) : traceSet M i → S i := fun a ↦ ⟨a.1.1, a.2⟩

/-- The trace `M ∩ S i`, with the topology induced by `S i`. -/
@[instance_reducible]
def traceTop (i : ι) : TopologicalSpace (traceSet M i) :=
  TopologicalSpace.induced (traceMap M i) inferInstance

variable {M}

/-- The trace on `S i` of a subset `N ⊆ M` whose traces on the `M ∩ S i` are traces of sets
`W i ⊆ S i`. -/
theorem incl_preimage_image_val {N : Set M} {W : ∀ i, Set (S i)}
    (hWN : ∀ i, traceMap M i ⁻¹' W i = Subtype.val ⁻¹' N) (i : ι) :
    incl S i ⁻¹' (Subtype.val '' N) = W i ∩ incl S i ⁻¹' M := by
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    have hxM : incl S i x ∈ M := hax ▸ a.2
    refine ⟨?_, hxM⟩
    have hb : (⟨⟨incl S i x, hxM⟩, x.2⟩ : traceSet M i) ∈ Subtype.val ⁻¹' N := by
      change (⟨incl S i x, hxM⟩ : M) ∈ N
      have : (⟨incl S i x, hxM⟩ : M) = a := Subtype.ext hax.symm
      rw [this]
      exact ha
    rw [← hWN i] at hb
    exact hb
  · rintro ⟨hxW, hxM⟩
    have hb : (⟨⟨incl S i x, hxM⟩, x.2⟩ : traceSet M i) ∈ traceMap M i ⁻¹' W i := hxW
    rw [hWN i] at hb
    exact ⟨_, hb, rfl⟩

/-- **The topology of open and closed subsets** ([GN26, Lemma A.7.6(c)]): if `M` is open
or closed in the direct limit, the topology it inherits is the direct limit topology of the traces
`M ∩ S i`, with the topologies inherited from the `S i`. -/
theorem topology_subtype_eq (hM : IsOpen M ∨ IsClosed M) :
    (inferInstance : TopologicalSpace M) = @topology M ι (traceSet M) (traceTop M) := by
  have hinj : Injective (Subtype.val : M → TopDirectLimit S) := Subtype.val_injective
  rcases hM with hM | hM
  · refine TopologicalSpace.ext_iff.2 fun N ↦ ?_
    refine isOpen_induced_iff.trans (Iff.trans ?_
      (@isOpen_iff M ι (traceSet M) (traceTop M) N).symm)
    constructor
    · rintro ⟨O, hO, rfl⟩ i
      exact isOpen_induced_iff.2 ⟨incl S i ⁻¹' O, isOpen_iff.1 hO i, rfl⟩
    · intro h
      choose W hW hWN using fun i ↦ isOpen_induced_iff.1 (h i)
      refine ⟨Subtype.val '' N, isOpen_iff.2 fun i ↦ ?_, hinj.preimage_image N⟩
      rw [incl_preimage_image_val hWN]
      exact (hW i).inter (hM.preimage (continuous_incl S i))
  · refine TopologicalSpace.ext_iff_isClosed.2 fun N ↦ ?_
    refine isClosed_induced_iff.trans (Iff.trans ?_
      (@isClosed_iff M ι (traceSet M) (traceTop M) N).symm)
    constructor
    · rintro ⟨C, hC, rfl⟩ i
      exact isClosed_induced_iff.2 ⟨incl S i ⁻¹' C, isClosed_iff.1 hC i, rfl⟩
    · intro h
      choose W hW hWN using fun i ↦ isClosed_induced_iff.1 (h i)
      refine ⟨Subtype.val '' N, isClosed_iff.2 fun i ↦ ?_, hinj.preimage_image N⟩
      rw [incl_preimage_image_val hWN]
      exact (hW i).inter (hM.preimage (continuous_incl S i))

end Subset

end TopDirectLimit

/-! ### `k_ω`-spaces -/

/-- A topological space is a **`k_ω`-space** ([GN26, Definition A.7.18]) if it is
compactly generated and hemicompact: some sequence of compact sets absorbs every compact set. -/
def IsKOmegaSpace (Y : Type*) [TopologicalSpace Y] : Prop :=
  CompactlyGeneratedSpace Y ∧
    ∃ K : ℕ → Set Y, (∀ n, IsCompact (K n)) ∧ ∀ L, IsCompact L → ∃ n, L ⊆ K n

/-- A topological space is **locally `k_ω`** ([GN26, Definition A.7.18]) if it is Hausdorff
and every point has an open neighbourhood which is a `k_ω`-space. -/
def IsLocallyKOmegaSpace (Y : Type*) [TopologicalSpace Y] : Prop :=
  T2Space Y ∧ ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ IsKOmegaSpace V

/-! ### Direct sequences -/

open TopDirectLimit

/-- A **direct sequence of topological spaces** ([GN26, Definition A.7.1]): an ascending
sequence of subsets covering `X`, each with its own topology, with continuous inclusions. -/
structure IsDirectSeq {X : Type u} (S : ℕ → Set X) [∀ n, TopologicalSpace (S n)] : Prop where
  mono : Monotone S
  exists_mem : ∀ x : X, ∃ n, x ∈ S n
  continuous_inclusion : ∀ n, Continuous (inclusion (mono (Nat.le_succ n)))

namespace IsDirectSeq

variable {X : Type u} {S : ℕ → Set X} [∀ n, TopologicalSpace (S n)]

/-- The inclusions `S m → S n`, `m ≤ n`, are continuous. -/
theorem continuous_inclusion_of_le (hS : IsDirectSeq S) {m n : ℕ} (h : m ≤ n) :
    Continuous (inclusion (hS.mono h)) := by
  induction n, h using Nat.le_induction with
  | base => exact continuous_id.congr fun x ↦ rfl
  | succ n hmn ih =>
    exact (hS.continuous_inclusion n).comp ih |>.congr fun x ↦ rfl

theorem preimage_val_image_val (n : ℕ) (W : Set (S n)) :
    incl S n ⁻¹' (Subtype.val '' W) = W :=
  Subtype.val_injective.preimage_image W

/-- The trace of a set on `S m` is the preimage of its trace on `S n`, `m ≤ n`. -/
theorem incl_preimage_eq (hS : IsDirectSeq S) {m n : ℕ} (h : m ≤ n) (M : Set (TopDirectLimit S)) :
    incl S m ⁻¹' M = inclusion (hS.mono h) ⁻¹' (incl S n ⁻¹' M) := rfl

/-- **Ascending unions of open subsets of the steps are open**
([GN26, Lemma A.7.6(a)]). -/
theorem isOpen_iUnion (hS : IsDirectSeq S) {V : ℕ → Set (TopDirectLimit S)} (hV : Monotone V)
    (hVo : ∀ n, IsOpen (incl S n ⁻¹' V n)) : IsOpen (⋃ n, V n) := by
  refine isOpen_iff.2 fun n ↦ ?_
  have : incl S n ⁻¹' (⋃ m, V m) =
      ⋃ m, inclusion (hS.mono (le_max_left n m)) ⁻¹' (incl S (max n m) ⁻¹' V (max n m)) := by
    ext x
    simp only [mem_preimage, mem_iUnion]
    exact ⟨fun ⟨m, hm⟩ ↦ ⟨m, hV (le_max_right n m) hm⟩, fun ⟨m, hm⟩ ↦ ⟨_, hm⟩⟩
  rw [this]
  exact _root_.isOpen_iUnion fun m ↦
    (hVo _).preimage (hS.continuous_inclusion_of_le (le_max_left n m))

/-- **Compact sets lie in some step** ([GN26, Lemma A.7.6(e)]), for `T₁` steps: otherwise
points `xₙ ∈ K \ S n` form an infinite closed discrete subset of `K`. -/
theorem exists_subset_of_isCompact [∀ n, T1Space (S n)] (hS : IsDirectSeq S)
    {K : Set (TopDirectLimit S)} (hK : IsCompact K) : ∃ n, K ⊆ S n := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  choose x hxK hxS using fun n ↦ not_subset.1 (hcon n)
  set D : Set (TopDirectLimit S) := range x
  -- every subset of `D` is closed: its traces are finite
  have hfin : ∀ n, (incl S n ⁻¹' D).Finite := by
    intro n
    refine ((finite_lt_nat n).image x).preimage Subtype.val_injective.injOn |>.subset ?_
    rintro ⟨y, hy⟩ ⟨m, rfl⟩
    refine ⟨m, ?_, rfl⟩
    by_contra hmn
    exact hxS m (hS.mono (not_lt.1 hmn) hy)
  have hclosed : ∀ A ⊆ D, IsClosed A := fun A hA ↦ isClosed_iff.2 fun n ↦
    ((hfin n).subset (preimage_mono hA)).isClosed
  -- hence `D` is compact and discrete, hence finite
  have hDc : IsCompact D := hK.of_isClosed_subset (hclosed D subset_rfl) (range_subset_iff.2 hxK)
  have hDf : D.Finite := by
    obtain ⟨F, hF⟩ := hDc.elim_finite_subcover (fun y : D ↦ (D \ {(y : TopDirectLimit S)})ᶜ)
      (fun y ↦ (hclosed _ sdiff_subset).isOpen_compl) fun z hz ↦
        mem_iUnion.2 ⟨⟨z, hz⟩, fun h ↦ h.2 rfl⟩
    refine (F.finite_toSet.image ((↑) : D → TopDirectLimit S)).subset fun z hz ↦ ?_
    obtain ⟨y, hyF, hy⟩ := mem_iUnion₂.1 (hF hz)
    have : z = y := by
      by_contra hne
      exact hy ⟨hz, hne⟩
    exact ⟨y, hyF, this.symm⟩
  -- but the `xₙ` leave every step
  obtain ⟨N, hN⟩ : ∃ N, D ⊆ S N := by
    obtain ⟨N, hN⟩ :=
      Set.Finite.bddAbove (Set.Finite.image (fun y ↦ Nat.find (hS.exists_mem y)) hDf)
    refine ⟨N, fun y hy ↦ hS.mono (hN ⟨y, hy, rfl⟩) (Nat.find_spec (hS.exists_mem y))⟩
  exact hxS N (hN (mem_range_self N))

section Union

variable {V : ℕ → Set (TopDirectLimit S)} (hVS : ∀ n, V n ⊆ S n)

/-- The set `Vₙ`, as a subset of `⋃ₙ Vₙ`. -/
def unionSet (V : ℕ → Set (TopDirectLimit S)) (n : ℕ) : Set (⋃ n, V n) := {a | a.1 ∈ V n}

/-- The inclusion of `Vₙ` into `S n`. -/
def unionMap (n : ℕ) : unionSet V n → S n := fun a ↦ ⟨a.1.1, hVS n a.2⟩

/-- `Vₙ`, with the topology induced by `S n`. -/
@[instance_reducible]
def unionTop (n : ℕ) : TopologicalSpace (unionSet V n) :=
  TopologicalSpace.induced (unionMap hVS n) inferInstance

/-- **The topology of an ascending union of open subsets of the steps**
([GN26, Lemma A.7.6(b)]): if `Vₙ ⊆ S n` are open and ascending, the topology that `V = ⋃ₙ Vₙ`
inherits from the direct limit is the direct limit topology of the `Vₙ`. -/
theorem topology_iUnion_eq (hS : IsDirectSeq S) (hV : Monotone V)
    (hVo : ∀ n, IsOpen (incl S n ⁻¹' V n)) :
    (inferInstance : TopologicalSpace (⋃ n, V n)) =
      @topology (⋃ n, V n) ℕ (unionSet V) (unionTop hVS) := by
  have hinj : Injective (Subtype.val : (⋃ n, V n) → TopDirectLimit S) := Subtype.val_injective
  refine TopologicalSpace.ext_iff.2 fun N ↦ isOpen_induced_iff.trans (Iff.trans ?_
    (@isOpen_iff (⋃ n, V n) ℕ (unionSet V) (unionTop hVS) N).symm)
  constructor
  · rintro ⟨O, hO, rfl⟩ n
    exact isOpen_induced_iff.2 ⟨incl S n ⁻¹' O, isOpen_iff.1 hO n, rfl⟩
  · intro h
    choose W hW hWN using fun n ↦ isOpen_induced_iff.1 (h n)
    refine ⟨Subtype.val '' N, isOpen_iff.2 fun k ↦ ?_, hinj.preimage_image N⟩
    have hk : ∀ m, k ≤ max k m := fun m ↦ le_max_left k m
    have : incl S k ⁻¹' (Subtype.val '' N) = ⋃ m, inclusion (hS.mono (hk m)) ⁻¹'
        (W (max k m) ∩ incl S (max k m) ⁻¹' V (max k m)) := by
      ext x
      simp only [mem_preimage, mem_iUnion, mem_inter_iff]
      constructor
      · rintro ⟨a, ha, hax⟩
        obtain ⟨m, hm⟩ := mem_iUnion.1 a.2
        have hxV : incl S k x ∈ V (max k m) := hax ▸ hV (le_max_right k m) hm
        refine ⟨m, ?_, hxV⟩
        have haV : a ∈ unionSet V (max k m) := by
          change (a : TopDirectLimit S) ∈ V (max k m)
          rw [hax]
          exact hxV
        have hb : (⟨a, haV⟩ : unionSet V (max k m)) ∈ unionMap hVS (max k m) ⁻¹' W (max k m) := by
          rw [hWN]
          exact ha
        have heq : unionMap hVS (max k m) ⟨a, haV⟩ = inclusion (hS.mono (hk m)) x :=
          Subtype.ext (by exact hax)
        change inclusion (hS.mono (hk m)) x ∈ W (max k m)
        rw [← heq]
        exact hb
      · rintro ⟨m, hxW, hxV⟩
        have hb : (⟨⟨incl S k x, mem_iUnion.2 ⟨_, hxV⟩⟩, hxV⟩ : unionSet V (max k m)) ∈
            unionMap hVS (max k m) ⁻¹' W (max k m) := hxW
        rw [hWN] at hb
        exact ⟨_, hb, rfl⟩
    rw [this]
    exact _root_.isOpen_iUnion fun m ↦ ((hW _).inter (hVo _)).preimage
      (hS.continuous_inclusion_of_le (hk m))

end Union

/-- **Strict direct sequences**: each step carries the topology induced by the next. -/
def IsStrict (hS : IsDirectSeq S) : Prop := ∀ n, IsInducing (inclusion (hS.mono (Nat.le_succ n)))

/-- In a strict direct sequence, each step carries the topology induced by every later step. -/
theorem IsStrict.isInducing_of_le {hS : IsDirectSeq S} (h : hS.IsStrict) {m n : ℕ}
    (hmn : m ≤ n) : IsInducing (inclusion (hS.mono hmn)) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    convert IsInducing.id
    funext x
    rfl
  | succ n hmn ih =>
    convert (h n).comp ih using 1
    funext x
    rfl

/-- **Extension of open sets** in a strict direct sequence: every open subset of `S m` is the
trace of an open subset of the direct limit ([GN26, proof of Lemma A.7.6(f)]). -/
theorem IsStrict.exists_isOpen_preimage_eq {hS : IsDirectSeq S} (h : hS.IsStrict) (m : ℕ)
    {W : Set (S m)} (hW : IsOpen W) :
    ∃ O : Set (TopDirectLimit S), IsOpen O ∧ incl S m ⁻¹' O = W := by
  -- extend step by step: open sets `A d ⊆ S (m + d)` with `A (d + 1) ∩ S (m + d) = A d`
  have step : ∀ d (A : Set X), A ⊆ S (m + d) → IsOpen (incl S (m + d) ⁻¹' A) →
      ∃ B : Set X, B ⊆ S (m + d + 1) ∧ IsOpen (incl S (m + d + 1) ⁻¹' B) ∧ B ∩ S (m + d) = A := by
    intro d A hA hAo
    obtain ⟨B', hB'o, hB'⟩ := (h (m + d)).isOpen_iff.1 hAo
    refine ⟨Subtype.val '' B', image_subset_iff.2 fun _ _ ↦ Subtype.prop _, ?_, ?_⟩
    · change IsOpen (incl S (m + d + 1) ⁻¹' (Subtype.val '' B'))
      rwa [preimage_val_image_val]
    · ext y
      constructor
      · rintro ⟨⟨z, hzB, rfl⟩, hz⟩
        have : (⟨z, hz⟩ : S (m + d)) ∈ inclusion (hS.mono (Nat.le_succ (m + d))) ⁻¹' B' := hzB
        rw [hB'] at this
        exact this
      · intro hy
        refine ⟨⟨inclusion (hS.mono (Nat.le_succ (m + d))) ⟨y, hA hy⟩, ?_, rfl⟩, hA hy⟩
        change (⟨y, hA hy⟩ : S (m + d)) ∈ inclusion (hS.mono (Nat.le_succ (m + d))) ⁻¹' B'
        rw [hB']
        exact hy
  choose B hBS hBo hBA using step
  classical
  let Bf : ℕ → Set X → Set X := fun d A ↦
    if hA : A ⊆ S (m + d) ∧ IsOpen (incl S (m + d) ⁻¹' A) then B d A hA.1 hA.2 else ∅
  let A : ℕ → Set X := fun d ↦ Nat.rec (Subtype.val '' W) (fun d Ad ↦ Bf d Ad) d
  have hAsucc : ∀ d, A (d + 1) = Bf d (A d) := fun d ↦ rfl
  have hinv : ∀ d, A d ⊆ S (m + d) ∧ IsOpen (incl S (m + d) ⁻¹' A d) := by
    intro d
    induction d with
    | zero =>
      refine ⟨image_subset_iff.2 fun _ _ ↦ Subtype.prop _, ?_⟩
      change IsOpen (incl S m ⁻¹' (Subtype.val '' W))
      rwa [preimage_val_image_val]
    | succ d ih =>
      rw [hAsucc]
      simp only [Bf, ih.1, ih.2, and_self, ↓reduceDIte]
      exact ⟨hBS d _ ih.1 ih.2, hBo d _ ih.1 ih.2⟩
  have hstep : ∀ d, A (d + 1) ∩ S (m + d) = A d := fun d ↦ by
    rw [hAsucc]
    simp only [Bf, (hinv d).1, (hinv d).2, and_self, ↓reduceDIte]
    exact hBA d _ (hinv d).1 (hinv d).2
  have hmonoA : Monotone A := monotone_nat_of_le_succ fun d ↦ by
    rw [← hstep d]
    exact inter_subset_left
  have htr : ∀ e d, e ≤ d → A d ∩ S (m + e) = A e := by
    intro e d hed
    induction d, hed using Nat.le_induction with
    | base => exact inter_eq_left.2 (hinv e).1
    | succ d hed ih =>
      rw [← ih, ← hstep d, inter_assoc, inter_eq_right.2 (hS.mono (by omega))]
  set O : Set (TopDirectLimit S) := ⋃ d, (A d : Set (TopDirectLimit S))
  have hOtr : ∀ d, incl S (m + d) ⁻¹' O = incl S (m + d) ⁻¹' A d := by
    intro d
    ext ⟨y, hy⟩
    change (y ∈ ⋃ e, (A e : Set (TopDirectLimit S))) ↔ y ∈ A d
    rw [mem_iUnion]
    refine ⟨fun ⟨e, he⟩ ↦ ?_, fun h ↦ ⟨d, h⟩⟩
    rcases le_total e d with hed | hde
    · exact hmonoA hed he
    · rw [← htr d e hde]
      exact ⟨he, hy⟩
  refine ⟨O, isOpen_iff.2 fun n ↦ ?_, ?_⟩
  · rw [hS.incl_preimage_eq (show n ≤ m + n by omega), hOtr n]
    exact (hinv n).2.preimage (hS.continuous_inclusion_of_le (show n ≤ m + n by omega))
  · change incl S (m + 0) ⁻¹' O = W
    rw [hOtr 0]
    change incl S m ⁻¹' (Subtype.val '' W) = W
    exact preimage_val_image_val m W

/-- **The steps of a strict direct sequence are embedded** ([GN26, Lemma A.7.6(f)]). -/
theorem IsStrict.isEmbedding_incl {hS : IsDirectSeq S} (h : hS.IsStrict) (m : ℕ) :
    IsEmbedding (incl S m) := by
  refine ⟨⟨?_⟩, Subtype.val_injective⟩
  ext W
  rw [isOpen_induced_iff]
  refine ⟨fun hW ↦ h.exists_isOpen_preimage_eq m hW, ?_⟩
  rintro ⟨O, hO, rfl⟩
  exact hO.preimage (continuous_incl S m)

/-- A direct sequence is **compactly regular** if every compact subset of the limit lies, and is
compact, in some step ([GN26, Definition A.7.5]; since the inclusions are continuous, the
topology of the step then induces the given one on the compact set if it is Hausdorff). -/
def CompactlyRegular (S : ℕ → Set X) [∀ n, TopologicalSpace (S n)] : Prop :=
  ∀ K : Set (TopDirectLimit S), IsCompact K → ∃ n, K ⊆ S n ∧ IsCompact (incl S n ⁻¹' K)

/-- **Strict direct sequences of `T₁` spaces are compactly regular**
([GN26, Lemma A.7.6(g)]). -/
theorem IsStrict.compactlyRegular [∀ n, T1Space (S n)] {hS : IsDirectSeq S} (h : hS.IsStrict) :
    CompactlyRegular S := fun K hK ↦ by
  obtain ⟨n, hn⟩ := hS.exists_subset_of_isCompact hK
  refine ⟨n, hn, ((h.isEmbedding_incl n).isInducing.isCompact_preimage_iff ?_).2 hK⟩
  intro x hx
  exact ⟨⟨x, hn hx⟩, rfl⟩

/-- **Unions of ascending chains of sets open in a subsequence of steps are open**: a variant of
Lemma A.7.6(a) and Remark A.7.2(d). -/
theorem isOpen_iUnion_of_comp (hS : IsDirectSeq S) {V : ℕ → Set (TopDirectLimit S)}
    (hV : Monotone V) {φ : ℕ → ℕ} (hφ : Monotone φ) (hφu : ∀ k, ∃ i, k ≤ φ i)
    (hVo : ∀ i, IsOpen (incl S (φ i) ⁻¹' V i)) : IsOpen (⋃ i, V i) := by
  refine isOpen_iff.2 fun k ↦ ?_
  obtain ⟨i₀, hi₀⟩ := hφu k
  have hk : ∀ i, k ≤ φ (max i₀ i) := fun i ↦ hi₀.trans (hφ (le_max_left _ _))
  have : incl S k ⁻¹' (⋃ i, V i) =
      ⋃ i, inclusion (hS.mono (hk i)) ⁻¹' (incl S (φ (max i₀ i)) ⁻¹' V (max i₀ i)) := by
    ext x
    simp only [mem_preimage, mem_iUnion]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, hV (le_max_right i₀ i) hi⟩, fun ⟨i, hi⟩ ↦ ⟨_, hi⟩⟩
  rw [this]
  exact _root_.isOpen_iUnion fun i ↦ (hVo _).preimage (hS.continuous_inclusion_of_le (hk i))

/-- A direct sequence is **compactifying** ([GN26, Definition A.7.1]) if every point of a
step has a neighbourhood whose image in some later step has compact closure. -/
def IsCompactifying (hS : IsDirectSeq S) : Prop :=
  ∀ n (x : S n), ∃ V ∈ 𝓝 x, ∃ m, ∃ h : n ≤ m, IsCompact (closure (inclusion (hS.mono h) '' V))

/-- **[GN26, Lemma A.7.4(a)]**: in a compactifying sequence of Hausdorff spaces, a compact
subset `K` of `S n` has, in every late enough step `S m`, open neighbourhoods `V ⊆ S n` whose
images have compact closure inside any prescribed open neighbourhood `U ⊆ S m`; the same holds
for the compact subsets of `K`. -/
theorem IsCompactifying.exists_isOpen {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] {n : ℕ} {K : Set (S n)} (hK : IsCompact K) :
    ∃ m₁, ∀ m (h : n ≤ m), m₁ ≤ m → ∀ K' ⊆ K, IsCompact K' → ∀ U : Set (S m), IsOpen U →
      inclusion (hS.mono h) '' K' ⊆ U → ∃ V : Set (S n), IsOpen V ∧ K' ⊆ V ∧
        IsCompact (closure (inclusion (hS.mono h) '' V)) ∧
          closure (inclusion (hS.mono h) '' V) ⊆ U := by
  choose V hV m hm hcV using hc n
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover (fun x ↦ interior (V x))
    fun x _ ↦ interior_mem_nhds.2 (hV x)
  refine ⟨t.sup m, fun M hnM hM K' hK'K hK' U hU hK'U ↦ ?_⟩
  have hmM : ∀ x ∈ t, m x ≤ M := fun x hx ↦ (Finset.le_sup hx).trans hM
  set W := ⋃ x ∈ t, interior (V x)
  have hWo : IsOpen W := isOpen_biUnion fun _ _ ↦ isOpen_interior
  set ι := inclusion (hS.mono hnM)
  -- the closure of `ι '' W` is compact
  set D : Set (S M) := ⋃ x : t, inclusion (hS.mono (hmM x x.2)) ''
    closure (inclusion (hS.mono (hm x)) '' V x)
  have hDc : IsCompact D :=
    isCompact_iUnion fun x ↦ (hcV x).image (hS.continuous_inclusion_of_le (hmM x x.2))
  have hWD : ι '' W ⊆ D := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 hw
    exact mem_iUnion.2 ⟨⟨x, hx⟩, inclusion (hS.mono (hm x)) w,
      subset_closure ⟨w, interior_subset hwx, rfl⟩, rfl⟩
  set C := closure (ι '' W)
  have hCc : IsCompact C := hDc.of_isClosed_subset isClosed_closure
    (closure_minimal hWD hDc.isClosed)
  -- shrink `W` so that the closure lies in `U`
  have hLc : IsCompact (C ∩ Uᶜ) := hCc.inter_right hU.isClosed_compl
  have hdisj : Disjoint (ι '' K') (C ∩ Uᶜ) :=
    disjoint_left.2 fun y hy hy' ↦ hy'.2 (hK'U hy)
  obtain ⟨P, Q, hP, hQ, hKP, hLQ, hPQ⟩ := SeparatedNhds.of_isCompact_isCompact
    (hK'.image (hS.continuous_inclusion_of_le hnM)) hLc hdisj
  have hsub : closure (ι '' (W ∩ ι ⁻¹' P)) ⊆ C ∩ Qᶜ := by
    refine closure_minimal ?_ (isClosed_closure.inter hQ.isClosed_compl)
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨subset_closure ⟨w, hw.1, rfl⟩, fun hwQ ↦ disjoint_left.1 hPQ hw.2 hwQ⟩
  refine ⟨W ∩ ι ⁻¹' P, hWo.inter (hP.preimage (hS.continuous_inclusion_of_le hnM)),
    fun y hy ↦ ⟨hKt (hK'K hy), hKP ⟨y, hy, rfl⟩⟩, ?_, ?_⟩
  · exact hCc.of_isClosed_subset isClosed_closure (hsub.trans inter_subset_left)
  · intro z hz
    obtain ⟨hzC, hzQ⟩ := hsub hz
    by_contra hzU
    exact hzQ (hLQ ⟨hzC, hzU⟩)

/-- **[GN26, Lemma A.7.4(b)]**: disjoint compact subsets of a step have open
neighbourhoods whose images in a later step have disjoint compact closures. -/
theorem IsCompactifying.exists_disjoint {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] {n : ℕ} {K L : Set (S n)} (hK : IsCompact K) (hL : IsCompact L)
    (hKL : Disjoint K L) (m₀ : ℕ) :
    ∃ m, ∃ h : n ≤ m, m₀ ≤ m ∧ ∃ V W : Set (S n), IsOpen V ∧ IsOpen W ∧ K ⊆ V ∧ L ⊆ W ∧
      IsCompact (closure (inclusion (hS.mono h) '' V)) ∧
      IsCompact (closure (inclusion (hS.mono h) '' W)) ∧
      Disjoint (closure (inclusion (hS.mono h) '' V)) (closure (inclusion (hS.mono h) '' W)) := by
  obtain ⟨m₁, hm₁⟩ := hc.exists_isOpen (hK.union hL)
  set m := max (max m₁ m₀) n
  have hnm : n ≤ m := le_max_right _ _
  have hcont := hS.continuous_inclusion_of_le hnm
  obtain ⟨P, Q, hP, hQ, hKP, hLQ, hPQ⟩ := SeparatedNhds.of_isCompact_isCompact
    (hK.image hcont) (hL.image hcont) ((disjoint_image_iff (inclusion_injective _)).2 hKL)
  have hm : m₁ ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  obtain ⟨V, hV, hKV, hVc, hVP⟩ := hm₁ m hnm hm K subset_union_left hK P hP hKP
  obtain ⟨W, hW, hLW, hWc, hWQ⟩ := hm₁ m hnm hm L subset_union_right hL Q hQ hLQ
  exact ⟨m, hnm, (le_max_right _ _).trans (le_max_left _ _), V, W, hV, hW, hKV, hLW, hVc, hWc,
    hPQ.mono hVP hWQ⟩

/-- One step of the construction in Lemma A.7.6(h), on subsets of `X`: disjoint sets `K`, `L`,
compact in `S n`, have open neighbourhoods in `S n` contained in disjoint sets compact in some
later step. -/
theorem IsCompactifying.step_disjoint {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] {n : ℕ} {K L : Set (TopDirectLimit S)} (hKn : K ⊆ S n) (hLn : L ⊆ S n)
    (hK : IsCompact (incl S n ⁻¹' K)) (hL : IsCompact (incl S n ⁻¹' L)) (hKL : Disjoint K L) :
    ∃ m, n < m ∧ ∃ V W K' L' : Set (TopDirectLimit S), IsOpen (incl S n ⁻¹' V) ∧
      IsOpen (incl S n ⁻¹' W) ∧ K ⊆ V ∧ L ⊆ W ∧ V ⊆ K' ∧ W ⊆ L' ∧ K' ⊆ S m ∧ L' ⊆ S m ∧
      IsCompact (incl S m ⁻¹' K') ∧ IsCompact (incl S m ⁻¹' L') ∧ Disjoint K' L' := by
  obtain ⟨m, h, hm, V₀, W₀, hV₀, hW₀, hKV, hLW, hVc, hWc, hd⟩ :=
    hc.exists_disjoint hK hL (hKL.preimage _) (n + 1)
  set ι := inclusion (hS.mono h)
  have hinj : ∀ k, Injective (incl S k) := fun k ↦ Subtype.val_injective
  refine ⟨m, hm, incl S n '' V₀, incl S n '' W₀, incl S m '' closure (ι '' V₀),
    incl S m '' closure (ι '' W₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [(hinj n).preimage_image]
  · rwa [(hinj n).preimage_image]
  · exact fun x hx ↦ ⟨⟨x, hKn hx⟩, hKV hx, rfl⟩
  · exact fun x hx ↦ ⟨⟨x, hLn hx⟩, hLW hx, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨ι v, subset_closure ⟨v, hv, rfl⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨ι v, subset_closure ⟨v, hv, rfl⟩, rfl⟩
  · exact image_subset_iff.2 fun x _ ↦ x.2
  · exact image_subset_iff.2 fun x _ ↦ x.2
  · rwa [(hinj m).preimage_image]
  · rwa [(hinj m).preimage_image]
  · exact (disjoint_image_iff (hinj m)).2 hd

/-- **Disjoint compact subsets of a step have disjoint open neighbourhoods** in the direct limit of
a compactifying sequence of Hausdorff spaces ([GN26, proof of Lemma A.7.6(h)]): ascending
unions of open sets `Vᵢ ⊆ S nᵢ` and `Wᵢ ⊆ S nᵢ` with `Vᵢ ⊆ Kᵢ₊₁ ⊆ Vᵢ₊₁` and `Wᵢ ⊆ Lᵢ₊₁ ⊆ Wᵢ₊₁`,
where `Kᵢ₊₁`, `Lᵢ₊₁` are disjoint and compact in `S nᵢ₊₁` (Lemma A.7.4(b)). -/
theorem IsCompactifying.exists_isOpen_disjoint {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] {n : ℕ} {K L : Set (TopDirectLimit S)} (hKn : K ⊆ S n)
    (hLn : L ⊆ S n) (hK : IsCompact (incl S n ⁻¹' K)) (hL : IsCompact (incl S n ⁻¹' L))
    (hKL : Disjoint K L) :
    ∃ V W : Set (TopDirectLimit S), IsOpen V ∧ IsOpen W ∧ K ⊆ V ∧ L ⊆ W ∧ Disjoint V W := by
  let Inv : ℕ × Set (TopDirectLimit S) × Set (TopDirectLimit S) → Prop := fun s ↦
    s.2.1 ⊆ S s.1 ∧ s.2.2 ⊆ S s.1 ∧
    IsCompact (incl S s.1 ⁻¹' s.2.1) ∧ IsCompact (incl S s.1 ⁻¹' s.2.2) ∧ Disjoint s.2.1 s.2.2
  choose m hm V W K' L' hVo hWo hKV hLW hVK hWL hK'S hL'S hK'c hL'c hd using
    fun (s : ℕ × Set (TopDirectLimit S) × Set (TopDirectLimit S)) (hs : Inv s) ↦
      hc.step_disjoint hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let next : {s // Inv s} → {s // Inv s} := fun s ↦
    ⟨(m s.1 s.2, K' s.1 s.2, L' s.1 s.2), hK'S _ _, hL'S _ _, hK'c _ _, hL'c _ _, hd _ _⟩
  let seq : ℕ → {s // Inv s} := fun i ↦ Nat.rec ⟨(n, K, L), hKn, hLn, hK, hL, hKL⟩
    (fun _ s ↦ next s) i
  have hseq : ∀ i, seq (i + 1) = next (seq i) := fun i ↦ rfl
  set Vs : ℕ → Set (TopDirectLimit S) := fun i ↦ V (seq i).1 (seq i).2
  set Ws : ℕ → Set (TopDirectLimit S) := fun i ↦ W (seq i).1 (seq i).2
  have hVK' : ∀ i, Vs i ⊆ (seq (i + 1)).1.2.1 := fun i ↦ by rw [hseq]; exact hVK _ _
  have hWL' : ∀ i, Ws i ⊆ (seq (i + 1)).1.2.2 := fun i ↦ by rw [hseq]; exact hWL _ _
  have hVmono : Monotone Vs := monotone_nat_of_le_succ fun i ↦ (hVK' i).trans (hKV _ _)
  have hWmono : Monotone Ws := monotone_nat_of_le_succ fun i ↦ (hWL' i).trans (hLW _ _)
  have hφ : StrictMono fun i ↦ (seq i).1.1 := strictMono_nat_of_lt_succ fun i ↦ by
    rw [hseq]; exact hm _ _
  have hφu : ∀ k, ∃ i, k ≤ (seq i).1.1 := fun k ↦ ⟨k, hφ.id_le k⟩
  refine ⟨⋃ i, Vs i, ⋃ i, Ws i, hS.isOpen_iUnion_of_comp hVmono hφ.monotone hφu
    fun i ↦ hVo _ _, hS.isOpen_iUnion_of_comp hWmono hφ.monotone hφu fun i ↦ hWo _ _,
    fun x hx ↦ mem_iUnion.2 ⟨0, hKV _ _ hx⟩, fun x hx ↦ mem_iUnion.2 ⟨0, hLW _ _ hx⟩, ?_⟩
  refine disjoint_iUnion_left.2 fun i ↦ disjoint_iUnion_right.2 fun j ↦ ?_
  have hd' := (seq (max i j + 1)).2.2.2.2.2
  exact hd'.mono ((hVmono (le_max_left i j)).trans (hVK' _))
    ((hWmono (le_max_right i j)).trans (hWL' _))

/-- **Limits of compactifying sequences of Hausdorff spaces are Hausdorff**
([GN26, Lemma A.7.6(h)]). -/
theorem IsCompactifying.t2Space {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] : T2Space (TopDirectLimit S) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨a, ha⟩ := hS.exists_mem x
  obtain ⟨b, hb⟩ := hS.exists_mem y
  have hx : x ∈ S (max a b) := hS.mono (le_max_left a b) ha
  have hy : y ∈ S (max a b) := hS.mono (le_max_right a b) hb
  obtain ⟨V, W, hV, hW, hxV, hyW, hVW⟩ := hc.exists_isOpen_disjoint (K := {x}) (L := {y})
    (singleton_subset_iff.2 hx) (singleton_subset_iff.2 hy)
    ((subsingleton_singleton.preimage Subtype.val_injective).isCompact)
    ((subsingleton_singleton.preimage Subtype.val_injective).isCompact)
    (disjoint_singleton.2 hxy)
  exact ⟨V, W, hV, hW, hxV rfl, hyW rfl, hVW⟩

/-- **Locally compact Hausdorff steps form a compactifying sequence**
([GN26, Remark A.7.2(c)]). -/
theorem isCompactifying_of_locallyCompactSpace (hS : IsDirectSeq S)
    [∀ n, LocallyCompactSpace (S n)] [∀ n, T2Space (S n)] : hS.IsCompactifying := fun n x ↦ by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds x
  exact ⟨K, hK, n, le_rfl, (hKc.image (hS.continuous_inclusion_of_le le_rfl)).closure⟩

/-- **Compact Hausdorff steps form a strict sequence** ([GN26, Remark A.7.2(c)]): a
continuous injection of a compact space into a Hausdorff space is an embedding. -/
theorem isStrict_of_compactSpace (hS : IsDirectSeq S) [∀ n, CompactSpace (S n)]
    [∀ n, T2Space (S n)] : hS.IsStrict := fun n ↦
  ((hS.continuous_inclusion n).isClosedEmbedding (inclusion_injective _)).isInducing

/-- **Nested relatively compact neighbourhoods** ([GN26, Lemma A.7.22]): for locally
compact Hausdorff steps, a point `x ∈ S 0` of an open set `U` of the direct limit has open
neighbourhoods `Vₙ ⊆ S n` whose closures in `S n` are compact, contained in `U`, and contained in
`Vₙ₊₁`. -/
theorem exists_nested_nhds [∀ n, LocallyCompactSpace (S n)] [∀ n, T2Space (S n)]
    (hS : IsDirectSeq S) {x : S 0} {U : Set (TopDirectLimit S)} (hU : IsOpen U)
    (hxU : incl S 0 x ∈ U) :
    ∃ V : ∀ n, Set (S n), (∀ n, IsOpen (V n)) ∧ (∀ n, IsCompact (closure (V n))) ∧
      (∀ n, closure (V n) ⊆ incl S n ⁻¹' U) ∧ x ∈ V 0 ∧
      ∀ n, inclusion (hS.mono (Nat.le_succ n)) '' closure (V n) ⊆ V (n + 1) := by
  let P : ∀ n, Set (S n) → Prop := fun n A ↦ IsOpen A ∧ IsCompact (closure A) ∧
    closure A ⊆ incl S n ⁻¹' U
  have hstart : ∃ A, P 0 A ∧ x ∈ A := by
    obtain ⟨A, hA, hxA, hAU, hAc⟩ := exists_open_between_and_isCompact_closure
      isCompact_singleton (hU.preimage (continuous_incl S 0)) (singleton_subset_iff.2 hxU)
    exact ⟨A, ⟨hA, hAc, hAU⟩, hxA rfl⟩
  have hstep : ∀ n (A : Set (S n)), P n A → ∃ B, P (n + 1) B ∧
      inclusion (hS.mono (Nat.le_succ n)) '' closure A ⊆ B := by
    rintro n A ⟨-, hAc, hAU⟩
    obtain ⟨B, hB, hAB, hBU, hBc⟩ := exists_open_between_and_isCompact_closure
      (hAc.image (hS.continuous_inclusion n)) (hU.preimage (continuous_incl S (n + 1)))
      (by rintro _ ⟨y, hy, rfl⟩; exact hAU hy)
    exact ⟨B, ⟨hB, hBc, hBU⟩, hAB⟩
  choose A₀ hA₀ hxA₀ using hstart
  choose B hB hAB using hstep
  let V : ∀ n, {A : Set (S n) // P n A} := fun n ↦
    Nat.rec ⟨A₀, hA₀⟩ (fun n A ↦ ⟨B n A.1 A.2, hB n A.1 A.2⟩) n
  refine ⟨fun n ↦ (V n).1, fun n ↦ (V n).2.1, fun n ↦ (V n).2.2.1, fun n ↦ (V n).2.2.2, hxA₀,
    fun n ↦ hAB n _ (V n).2⟩

/-- The sets `Vₙ` of Lemma A.7.6(b) form a direct sequence. -/
theorem isDirectSeq_unionSet (hS : IsDirectSeq S) {V : ℕ → Set (TopDirectLimit S)}
    (hVS : ∀ n, V n ⊆ S n) (hV : Monotone V) :
    @IsDirectSeq (⋃ n, V n) (unionSet V) (unionTop hVS) := by
  let := unionTop hVS
  refine ⟨fun m n h a ha ↦ hV h ha, fun a ↦ ?_, fun n ↦ ?_⟩
  · obtain ⟨n, hn⟩ := mem_iUnion.1 a.2
    exact ⟨n, hn⟩
  · exact continuous_induced_rng.2 ((hS.continuous_inclusion n).comp
      (continuous_induced_dom (f := unionMap hVS n)))

/-- **The sets `Vₙ` of Lemma A.7.6(b) form a compactifying sequence** if the `S n` do and are
Hausdorff ([GN26, Remark A.7.7]). A point of `Vₙ` has a neighbourhood `P` in `S n` whose
image has compact closure `C` in some `S m`; inside `C`, the point has a compact neighbourhood
`Q ⊆ Vₘ`, and the trace of `P` on the preimage of the interior of `Q` has closure in `Vₘ` inside
`Q`. -/
theorem IsCompactifying.isCompactifying_unionSet {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] {V : ℕ → Set (TopDirectLimit S)} (hVS : ∀ n, V n ⊆ S n)
    (hV : Monotone V) (hVo : ∀ n, IsOpen (incl S n ⁻¹' V n)) :
    @IsCompactifying (⋃ n, V n) (unionSet V) (unionTop hVS)
      (isDirectSeq_unionSet hS hVS hV) := by
  let := unionTop hVS
  intro n a
  set x := unionMap hVS n a
  obtain ⟨P, hP, m, h, hPc⟩ := hc n x
  set ι := inclusion (hS.mono h)
  set C := closure (ι '' P)
  set G := incl S m ⁻¹' V m
  have hxG : ι x ∈ G := hV h a.2
  have hLc : IsCompact (C ∩ Gᶜ) := hPc.inter_right (hVo m).isClosed_compl
  obtain ⟨O, R, hO, hR, hxO, hLR, hOR⟩ := SeparatedNhds.of_isCompact_isCompact isCompact_singleton
    hLc (disjoint_singleton_left.2 fun h ↦ h.2 hxG)
  set Q := C ∩ Rᶜ
  have hQc : IsCompact Q := hPc.inter_right hR.isClosed_compl
  have hQG : Q ⊆ G := fun y ⟨hyC, hyR⟩ ↦ by_contra fun hyG ↦ hyR (hLR ⟨hyC, hyG⟩)
  -- the neighbourhood of `a`
  set W : Set (unionSet V n) := unionMap hVS n ⁻¹' (interior P ∩ ι ⁻¹' O)
  have hWo : IsOpen W := isOpen_induced (isOpen_interior.inter (hO.preimage
    (hS.continuous_inclusion_of_le h)))
  have haW : a ∈ W := ⟨mem_interior_iff_mem_nhds.2 hP, hxO rfl⟩
  refine ⟨W, hWo.mem_nhds haW, m, h, ?_⟩
  -- its image lies in the compact set `unionMap⁻¹ Q`
  have hind : IsInducing (unionMap hVS m) := ⟨rfl⟩
  have hK : IsCompact (unionMap hVS m ⁻¹' Q) := (hind.isCompact_preimage_iff fun y hy ↦
    ⟨⟨⟨incl S m y, mem_iUnion.2 ⟨m, hQG hy⟩⟩, hQG hy⟩, rfl⟩).2 hQc
  have hKc : IsClosed (unionMap hVS m ⁻¹' Q) := hQc.isClosed.preimage continuous_induced_dom
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hKc)
  rintro _ ⟨b, ⟨hbP, hbO⟩, rfl⟩
  exact ⟨subset_closure ⟨_, interior_subset hbP, rfl⟩, fun hR' ↦ disjoint_left.1 hOR hbO hR'⟩

/-! ### Products of direct limits -/

section Prod

variable {Y : Type w} {T : ℕ → Set Y} [∀ n, TopologicalSpace (T n)]

/-- The trace of a subset of a product of direct limits on `S n × T n`. -/
def prodTrace (U : Set (TopDirectLimit S × TopDirectLimit T)) (n : ℕ) : Set (S n × T n) :=
  {p | (incl S n p.1, incl T n p.2) ∈ U}

/-- One step of the construction in Lemma A.7.9: a product `K × L` of compact subsets of `S n`
and `T n` inside a set with open traces has a product neighbourhood `V × W`, open in
`S n × T n`, inside a product `K' × L'` of compact subsets of a later step, still inside the
set. -/
theorem IsCompactifying.step_prod {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    {hT : IsDirectSeq T} (hc' : hT.IsCompactifying) [∀ n, T2Space (S n)] [∀ n, T2Space (T n)]
    {U : Set (TopDirectLimit S × TopDirectLimit T)} (hU : ∀ n, IsOpen (prodTrace U n)) {n : ℕ}
    {K : Set (TopDirectLimit S)} {L : Set (TopDirectLimit T)} (hKn : K ⊆ S n) (hLn : L ⊆ T n)
    (hK : IsCompact (incl S n ⁻¹' K)) (hL : IsCompact (incl T n ⁻¹' L)) (hKL : K ×ˢ L ⊆ U) :
    ∃ m, n < m ∧ ∃ (V K' : Set (TopDirectLimit S)) (W L' : Set (TopDirectLimit T)),
      IsOpen (incl S n ⁻¹' V) ∧ IsOpen (incl T n ⁻¹' W) ∧ K ⊆ V ∧ L ⊆ W ∧ V ⊆ K' ∧ W ⊆ L' ∧
      K' ⊆ S m ∧ L' ⊆ T m ∧ IsCompact (incl S m ⁻¹' K') ∧ IsCompact (incl T m ⁻¹' L') ∧
      K' ×ˢ L' ⊆ U := by
  obtain ⟨m₁, hm₁⟩ := hc.exists_isOpen hK
  obtain ⟨m₂, hm₂⟩ := hc'.exists_isOpen hL
  set m := max (max m₁ m₂) (n + 1)
  have hnm : n ≤ m := by omega
  set ι := inclusion (hS.mono hnm)
  set ι' := inclusion (hT.mono hnm)
  have hKL' : (ι '' (incl S n ⁻¹' K)) ×ˢ (ι' '' (incl T n ⁻¹' L)) ⊆ prodTrace U m := by
    rintro ⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    exact hKL ⟨ha, hb⟩
  obtain ⟨P, Q, hP, hQ, hKP, hLQ, hPQ⟩ := generalized_tube_lemma
    (hK.image (hS.continuous_inclusion_of_le hnm)) (hL.image (hT.continuous_inclusion_of_le hnm))
    (hU m) hKL'
  obtain ⟨V₀, hV₀, hKV, hVc, hVP⟩ := hm₁ m hnm (by omega) _ subset_rfl hK P hP hKP
  obtain ⟨W₀, hW₀, hLW, hWc, hWQ⟩ := hm₂ m hnm (by omega) _ subset_rfl hL Q hQ hLQ
  have hinjS : ∀ k, Injective (incl S k) := fun k ↦ Subtype.val_injective
  have hinjT : ∀ k, Injective (incl T k) := fun k ↦ Subtype.val_injective
  refine ⟨m, by omega, incl S n '' V₀, incl S m '' closure (ι '' V₀), incl T n '' W₀,
    incl T m '' closure (ι' '' W₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [(hinjS n).preimage_image]
  · rwa [(hinjT n).preimage_image]
  · exact fun x hx ↦ ⟨⟨x, hKn hx⟩, hKV hx, rfl⟩
  · exact fun x hx ↦ ⟨⟨x, hLn hx⟩, hLW hx, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨ι v, subset_closure ⟨v, hv, rfl⟩, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨ι' v, subset_closure ⟨v, hv, rfl⟩, rfl⟩
  · exact image_subset_iff.2 fun x _ ↦ x.2
  · exact image_subset_iff.2 fun x _ ↦ x.2
  · rwa [(hinjS m).preimage_image]
  · rwa [(hinjT m).preimage_image]
  · rintro ⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    exact hPQ (show (a, b) ∈ P ×ˢ Q from ⟨hVP ha, hWQ hb⟩)

/-- **Products of direct limits** ([GN26, Lemma A.7.9]): for compactifying sequences of
Hausdorff spaces, a subset of `lim Sₙ × lim Tₙ` is open iff its traces on all `Sₙ × Tₙ` are, so
`lim Sₙ × lim Tₙ = lim (Sₙ × Tₙ)` as topological spaces. Around a point of an open set, ascending
products `Vᵢ × Wᵢ` of open subsets of the steps fit inside products of compact sets
(`IsCompactifying.step_prod`) contained in the set. -/
theorem IsCompactifying.isOpen_prod_iff {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    {hT : IsDirectSeq T} (hc' : hT.IsCompactifying) [∀ n, T2Space (S n)] [∀ n, T2Space (T n)]
    {U : Set (TopDirectLimit S × TopDirectLimit T)} :
    IsOpen U ↔ ∀ n, IsOpen (prodTrace U n) := by
  refine ⟨fun hU n ↦ hU.preimage ((continuous_incl S n).prodMap (continuous_incl T n)),
    fun hU ↦ isOpen_iff_forall_mem_open.2 fun ⟨x, y⟩ hxy ↦ ?_⟩
  obtain ⟨a, ha⟩ := hS.exists_mem x
  obtain ⟨b, hb⟩ := hT.exists_mem y
  set n := max a b
  have hx : x ∈ S n := hS.mono (le_max_left a b) ha
  have hy : y ∈ T n := hT.mono (le_max_right a b) hb
  let Inv : ℕ × Set (TopDirectLimit S) × Set (TopDirectLimit T) → Prop := fun s ↦
    s.2.1 ⊆ S s.1 ∧ s.2.2 ⊆ T s.1 ∧ IsCompact (incl S s.1 ⁻¹' s.2.1) ∧
      IsCompact (incl T s.1 ⁻¹' s.2.2) ∧ s.2.1 ×ˢ s.2.2 ⊆ U
  choose m hm V K' W L' hVo hWo hKV hLW hVK hWL hK'S hL'T hK'c hL'c hKLU using
    fun (s : ℕ × Set (TopDirectLimit S) × Set (TopDirectLimit T)) (hs : Inv s) ↦
      hc.step_prod hc' hU hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  let next : {s // Inv s} → {s // Inv s} := fun s ↦
    ⟨(m s.1 s.2, K' s.1 s.2, L' s.1 s.2), hK'S _ _, hL'T _ _, hK'c _ _, hL'c _ _, hKLU _ _⟩
  have h0 : Inv (n, {x}, {y}) := ⟨singleton_subset_iff.2 hx, singleton_subset_iff.2 hy,
    (subsingleton_singleton.preimage Subtype.val_injective).isCompact,
    (subsingleton_singleton.preimage Subtype.val_injective).isCompact,
    by rw [singleton_prod_singleton, singleton_subset_iff]; exact hxy⟩
  let seq : ℕ → {s // Inv s} := fun i ↦ Nat.rec ⟨(n, {x}, {y}), h0⟩ (fun _ s ↦ next s) i
  have hseq : ∀ i, seq (i + 1) = next (seq i) := fun i ↦ rfl
  set Vs : ℕ → Set (TopDirectLimit S) := fun i ↦ V (seq i).1 (seq i).2
  set Ws : ℕ → Set (TopDirectLimit T) := fun i ↦ W (seq i).1 (seq i).2
  have hVK' : ∀ i, Vs i ⊆ (seq (i + 1)).1.2.1 := fun i ↦ by rw [hseq]; exact hVK _ _
  have hWL' : ∀ i, Ws i ⊆ (seq (i + 1)).1.2.2 := fun i ↦ by rw [hseq]; exact hWL _ _
  have hVmono : Monotone Vs := monotone_nat_of_le_succ fun i ↦ (hVK' i).trans (hKV _ _)
  have hWmono : Monotone Ws := monotone_nat_of_le_succ fun i ↦ (hWL' i).trans (hLW _ _)
  have hφ : StrictMono fun i ↦ (seq i).1.1 := strictMono_nat_of_lt_succ fun i ↦ by
    rw [hseq]; exact hm _ _
  have hφu : ∀ k, ∃ i, k ≤ (seq i).1.1 := fun k ↦ ⟨k, hφ.id_le k⟩
  refine ⟨(⋃ i, Vs i) ×ˢ (⋃ i, Ws i), ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨i, hi⟩ := mem_iUnion.1 ha
    obtain ⟨j, hj⟩ := mem_iUnion.1 hb
    exact (seq (max i j + 1)).2.2.2.2.2 ⟨hVK' _ (hVmono (le_max_left i j) hi),
      hWL' _ (hWmono (le_max_right i j) hj)⟩
  · exact (hS.isOpen_iUnion_of_comp hVmono hφ.monotone hφu fun i ↦ hVo _ _).prod
      (hT.isOpen_iUnion_of_comp hWmono hφ.monotone hφu fun i ↦ hWo _ _)
  · exact ⟨mem_iUnion.2 ⟨0, hKV _ _ rfl⟩, mem_iUnion.2 ⟨0, hLW _ _ rfl⟩⟩

/-- **Continuity on products of direct limits** ([GN26, Lemma A.7.9]): for compactifying
sequences of Hausdorff spaces, a map on `lim Sₙ × lim Tₙ` is continuous iff its restrictions to
the `Sₙ × Tₙ` are. -/
theorem IsCompactifying.continuous_prod_iff {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    {hT : IsDirectSeq T} (hc' : hT.IsCompactifying) [∀ n, T2Space (S n)] [∀ n, T2Space (T n)]
    {Z : Type*} [TopologicalSpace Z] {f : TopDirectLimit S × TopDirectLimit T → Z} :
    Continuous f ↔ ∀ n, Continuous fun p : S n × T n ↦ f (incl S n p.1, incl T n p.2) := by
  refine ⟨fun hf n ↦ hf.comp ((continuous_incl S n).prodMap (continuous_incl T n)),
    fun hf ↦ continuous_def.2 fun O hO ↦ (hc.isOpen_prod_iff hc').2 fun n ↦ ?_⟩
  exact hO.preimage (hf n)

end Prod

/-! ### Compact regularity of compactifying sequences -/

/-- One step of the construction in Proposition A.7.20: a set `K`, compact in `S n`, has an open
neighbourhood in `S n` contained in a set compact in a later step. -/
theorem IsCompactifying.step {hS : IsDirectSeq S} (hc : hS.IsCompactifying) [∀ n, T2Space (S n)]
    {n : ℕ} {K : Set (TopDirectLimit S)} (hKn : K ⊆ S n) (hK : IsCompact (incl S n ⁻¹' K)) :
    ∃ m, n < m ∧ ∃ V K' : Set (TopDirectLimit S), IsOpen (incl S n ⁻¹' V) ∧ K ⊆ V ∧ V ⊆ K' ∧
      K' ⊆ S m ∧ IsCompact (incl S m ⁻¹' K') := by
  obtain ⟨m₁, hm₁⟩ := hc.exists_isOpen hK
  set m := max m₁ (n + 1)
  have hnm : n ≤ m := by omega
  obtain ⟨V₀, hV₀, hKV, hVc, -⟩ := hm₁ m hnm (le_max_left _ _) _ subset_rfl hK univ isOpen_univ
    (subset_univ _)
  have hinj : ∀ k, Injective (incl S k) := fun k ↦ Subtype.val_injective
  refine ⟨m, by omega, incl S n '' V₀, incl S m '' closure (inclusion (hS.mono hnm) '' V₀), ?_,
    fun x hx ↦ ⟨⟨x, hKn hx⟩, hKV hx, rfl⟩, ?_, image_subset_iff.2 fun x _ ↦ x.2, ?_⟩
  · rwa [(hinj n).preimage_image]
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨inclusion (hS.mono hnm) v, subset_closure ⟨v, hv, rfl⟩, rfl⟩
  · rwa [(hinj m).preimage_image]

/-- **Chains of compact sets** ([GN26, proof of Proposition A.7.20]): a set `K`, compact in
a step, lies in an ascending union `⋃ⱼ Vⱼ = ⋃ⱼ Kⱼ` with `Kⱼ ⊆ Vⱼ ⊆ Kⱼ₊₁`, where `Vⱼ` is open and
`Kⱼ` compact in `S (φ j)`, for a strictly increasing `φ`. -/
theorem IsCompactifying.exists_chain {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] {n : ℕ} {K : Set (TopDirectLimit S)} (hKn : K ⊆ S n)
    (hK : IsCompact (incl S n ⁻¹' K)) :
    ∃ (φ : ℕ → ℕ) (Ks Vs : ℕ → Set (TopDirectLimit S)), StrictMono φ ∧ Ks 0 = K ∧
      (∀ j, Ks j ⊆ S (φ j)) ∧ (∀ j, IsCompact (incl S (φ j) ⁻¹' Ks j)) ∧
      (∀ j, IsOpen (incl S (φ j) ⁻¹' Vs j)) ∧ (∀ j, Ks j ⊆ Vs j) ∧ ∀ j, Vs j ⊆ Ks (j + 1) := by
  let Inv : ℕ × Set (TopDirectLimit S) → Prop := fun s ↦
    s.2 ⊆ S s.1 ∧ IsCompact (incl S s.1 ⁻¹' s.2)
  choose m hm V K' hVo hKV hVK hK'S hK'c using
    fun (s : ℕ × Set (TopDirectLimit S)) (hs : Inv s) ↦ hc.step hs.1 hs.2
  let next : {s // Inv s} → {s // Inv s} := fun s ↦ ⟨(m s.1 s.2, K' s.1 s.2), hK'S _ _, hK'c _ _⟩
  let seq : ℕ → {s // Inv s} := fun i ↦ Nat.rec ⟨(n, K), hKn, hK⟩ (fun _ s ↦ next s) i
  have hseq : ∀ i, seq (i + 1) = next (seq i) := fun i ↦ rfl
  refine ⟨fun j ↦ (seq j).1.1, fun j ↦ (seq j).1.2, fun j ↦ V (seq j).1 (seq j).2,
    strictMono_nat_of_lt_succ fun j ↦ by rw [hseq]; exact hm _ _, rfl, fun j ↦ (seq j).2.1,
    fun j ↦ (seq j).2.2, fun j ↦ hVo _ _, fun j ↦ hKV _ _, fun j ↦ ?_⟩
  change V (seq j).1 (seq j).2 ⊆ (seq (j + 1)).1.2
  rw [hseq]
  exact hVK _ _

/-- **A closedness criterion on a chain** ([GN26, proof of Proposition A.7.20]): if the
traces of `A` on all `Kⱼ` of a chain are closed, then `⋃ⱼ Vⱼ \ A` is open. -/
theorem isOpen_iUnion_diff_of_chain (hS : IsDirectSeq S) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {Ks Vs : ℕ → Set (TopDirectLimit S)} (hVo : ∀ j, IsOpen (incl S (φ j) ⁻¹' Vs j))
    (hKV : ∀ j, Ks j ⊆ Vs j) (hVK : ∀ j, Vs j ⊆ Ks (j + 1)) {A : Set (TopDirectLimit S)}
    (hA : ∀ j, IsClosed (A ∩ Ks j)) : IsOpen ((⋃ j, Vs j) \ A) := by
  rw [iUnion_sdiff]
  refine hS.isOpen_iUnion_of_comp (fun i j hij ↦ sdiff_subset_sdiff_left ?_) hφ.monotone
    (fun k ↦ ⟨k, hφ.id_le k⟩) fun j ↦ ?_
  · exact (monotone_nat_of_le_succ fun j ↦ (hVK j).trans (hKV (j + 1))) hij
  · have : Vs j \ A = Vs j \ (A ∩ Ks (j + 1)) := by
      ext x
      exact ⟨fun ⟨hx, hxA⟩ ↦ ⟨hx, fun h ↦ hxA h.1⟩,
        fun ⟨hx, hxA⟩ ↦ ⟨hx, fun h ↦ hxA ⟨h, hVK j hx⟩⟩⟩
    rw [this, preimage_sdiff]
    exact (hVo j).sdiff ((hA (j + 1)).preimage (continuous_incl S (φ j)))

/-- A set compact in a step is compact in every later step. -/
theorem isCompact_preimage_of_le (hS : IsDirectSeq S) {m m' : ℕ} (h : m ≤ m')
    {K : Set (TopDirectLimit S)} (hKm : K ⊆ S m) (hK : IsCompact (incl S m ⁻¹' K)) :
    IsCompact (incl S m' ⁻¹' K) := by
  have : incl S m' ⁻¹' K = inclusion (hS.mono h) '' (incl S m ⁻¹' K) := by
    ext ⟨x, hx⟩
    refine ⟨fun hxK ↦ ⟨⟨x, hKm hxK⟩, hxK, rfl⟩, ?_⟩
    rintro ⟨y, hy, hxy⟩
    rw [← hxy]
    exact hy
  rw [this]
  exact hK.image (hS.continuous_inclusion_of_le h)

/-- **Compact subsets of the union of a chain lie in one of its compact sets**
([GN26, proof of Proposition A.7.20]): otherwise points `yⱼ ∈ L \ Kⱼ` form an infinite closed
discrete subset of `L`, by the closedness criterion `isOpen_iUnion_diff_of_chain`. -/
theorem exists_subset_of_isCompact_of_chain [∀ n, T1Space (S n)] (hS : IsDirectSeq S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {Ks Vs : ℕ → Set (TopDirectLimit S)}
    (hVo : ∀ j, IsOpen (incl S (φ j) ⁻¹' Vs j)) (hKV : ∀ j, Ks j ⊆ Vs j)
    (hVK : ∀ j, Vs j ⊆ Ks (j + 1)) {L : Set (TopDirectLimit S)} (hL : IsCompact L)
    (hLV : L ⊆ ⋃ j, Vs j) : ∃ j, L ⊆ Ks j := by
  classical
  have hKmono : Monotone Ks := monotone_nat_of_le_succ fun j ↦ (hKV j).trans (hVK j)
  by_contra hcon
  simp only [not_exists] at hcon
  choose y hyL hyK using fun j ↦ not_subset.1 (hcon j)
  set D := range y
  set VV := ⋃ j, Vs j
  -- every subset of `D` meets each `Kⱼ` in a finite set
  have hfin : ∀ A ⊆ D, ∀ j, IsClosed (A ∩ Ks j) := by
    intro A hA j
    refine (((finite_lt_nat j).image y).subset ?_).isClosed
    rintro _ ⟨hzA, hzK⟩
    obtain ⟨i, rfl⟩ := hA hzA
    refine ⟨i, ?_, rfl⟩
    by_contra hij
    exact hyK i (hKmono (not_lt.1 hij) hzK)
  have hopen : ∀ A ⊆ D, IsOpen (VV \ A) := fun A hA ↦
    isOpen_iUnion_diff_of_chain hS hφ hVo hKV hVK (hfin A hA)
  have hDL : D ⊆ L := range_subset_iff.2 hyL
  -- `D` is compact
  have hDc : IsCompact D := by
    have : D = L \ (VV \ D) := by
      ext z
      exact ⟨fun hz ↦ ⟨hDL hz, fun h ↦ h.2 hz⟩,
        fun ⟨hzL, hz⟩ ↦ by_contra fun hzD ↦ hz ⟨hLV hzL, hzD⟩⟩
    rw [this]
    exact hL.diff (hopen D subset_rfl)
  -- and discrete, hence finite
  have hDf : D.Finite := by
    obtain ⟨F, hF⟩ := hDc.elim_finite_subcover (fun z : D ↦ VV \ (D \ {(z : TopDirectLimit S)}))
      (fun z ↦ hopen _ sdiff_subset) fun z hz ↦
        mem_iUnion.2 ⟨⟨z, hz⟩, hLV (hDL hz), fun h ↦ h.2 rfl⟩
    refine (F.finite_toSet.image ((↑) : D → TopDirectLimit S)).subset fun z hz ↦ ?_
    obtain ⟨w, hwF, hw⟩ := mem_iUnion₂.1 (hF hz)
    have : z = w := by
      by_contra hne
      exact hw.2 ⟨hz, hne⟩
    exact ⟨w, hwF, this.symm⟩
  -- but the `yⱼ` leave every `Kⱼ`
  have hj : ∀ z ∈ D, ∃ j, z ∈ Ks j := fun z hz ↦ by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hLV (hDL hz))
    exact ⟨j + 1, hVK j hj⟩
  choose! J hJ using hj
  obtain ⟨N, hN⟩ := Set.Finite.bddAbove (Set.Finite.image J hDf)
  exact hyK N (hKmono (hN ⟨y N, mem_range_self N, rfl⟩) (hJ _ (mem_range_self N)))

/-- **Compactifying sequences of Hausdorff spaces are compactly regular**
([GN26, Proposition A.7.20]): every point has an open neighbourhood `⋃ⱼ Vⱼ` along a chain
(`IsCompactifying.exists_chain`) whose compact subsets lie, and are compact, in some step; a
compact set is a finite union of compact sets of this kind. -/
theorem IsCompactifying.compactlyRegular {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] : CompactlyRegular S := by
  have := hc.t2Space
  intro K hK
  -- a chain around each point
  have hpt : ∀ x : TopDirectLimit S, ∃ n, x ∈ S n := hS.exists_mem
  choose nx hnx using hpt
  choose φ Ks Vs hφ hK0 hKS hKc hVo hKV hVK using fun x : TopDirectLimit S ↦
    hc.exists_chain (K := {x}) (n := nx x) (singleton_subset_iff.2 (hnx x))
      ((subsingleton_singleton.preimage Subtype.val_injective).isCompact)
  set VV : TopDirectLimit S → Set (TopDirectLimit S) := fun x ↦ ⋃ j, Vs x j
  have hVVo : ∀ x, IsOpen (VV x) := fun x ↦
    hS.isOpen_iUnion_of_comp (monotone_nat_of_le_succ fun j ↦ (hVK x j).trans (hKV x (j + 1)))
      (hφ x).monotone (fun k ↦ ⟨k, (hφ x).id_le k⟩) (hVo x)
  have hxVV : ∀ x, x ∈ VV x := fun x ↦ mem_iUnion.2 ⟨0, hKV x 0 (by rw [hK0]; rfl)⟩
  -- separate `x` from `K \ VV x`
  have hsep : ∀ x, ∃ P Q : Set (TopDirectLimit S), IsOpen P ∧ IsOpen Q ∧ x ∈ P ∧
      K \ VV x ⊆ Q ∧ Disjoint P Q := fun x ↦ by
    obtain ⟨P, Q, hP, hQ, hxP, hKQ, hPQ⟩ := SeparatedNhds.of_isCompact_isCompact
      isCompact_singleton (hK.diff (hVVo x)) (disjoint_singleton_left.2 fun h ↦ h.2 (hxVV x))
    exact ⟨P, Q, hP, hQ, hxP rfl, hKQ, hPQ⟩
  choose P Q hP hQ hxP hKQ hPQ using hsep
  -- the compact pieces `K \ Q x`
  have hpiece : ∀ x, ∃ p, K \ Q x ⊆ S p ∧ IsCompact (incl S p ⁻¹' (K \ Q x)) := fun x ↦ by
    have hLc : IsCompact (K \ Q x) := hK.diff (hQ x)
    have hLV : K \ Q x ⊆ VV x := fun z ⟨hzK, hzQ⟩ ↦ by_contra fun h ↦ hzQ (hKQ x ⟨hzK, h⟩)
    obtain ⟨j, hj⟩ := exists_subset_of_isCompact_of_chain hS (hφ x) (hVo x) (hKV x) (hVK x) hLc
      hLV
    exact ⟨φ x j, hj.trans (hKS x j), (hKc x j).of_isClosed_subset
      (hLc.isClosed.preimage (continuous_incl S _)) (preimage_mono hj)⟩
  choose p hpS hpc using hpiece
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover P fun x _ ↦ (hP x).mem_nhds (hxP x)
  set M := t.sup p
  have hpM : ∀ x ∈ t, p x ≤ M := fun x hx ↦ Finset.le_sup hx
  have hKpieces : K ⊆ ⋃ x ∈ t, K \ Q x := fun z hz ↦ by
    obtain ⟨x, hx, hzP⟩ := mem_iUnion₂.1 (hKt hz)
    exact mem_iUnion₂.2 ⟨x, hx, hz, fun hzQ ↦ disjoint_left.1 (hPQ x) hzP hzQ⟩
  have hKM : K ⊆ S M :=
    hKpieces.trans (iUnion₂_subset fun x hx ↦ (hpS x).trans (hS.mono (hpM x hx)))
  refine ⟨M, hKM, ?_⟩
  have hU : IsCompact (⋃ x ∈ t, incl S M ⁻¹' (K \ Q x)) := t.isCompact_biUnion fun x hx ↦
    hS.isCompact_preimage_of_le (hpM x hx) (hpS x) (hpc x)
  exact hU.of_isClosed_subset (hK.isClosed.preimage (continuous_incl S M)) fun z hz ↦ by
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (hKpieces hz)
    exact mem_iUnion₂.2 ⟨x, hx, hzx⟩

/-- **The union of a chain is a `k_ω`-space** ([GN26, proof of Proposition A.7.20]): its
compact subsets lie in the `Kⱼ`, and a set meeting each `Kⱼ` in a closed set is closed. -/
theorem isKOmegaSpace_iUnion_of_chain [∀ n, T1Space (S n)] [T2Space (TopDirectLimit S)]
    (hS : IsDirectSeq S) {φ : ℕ → ℕ} (hφ : StrictMono φ) {Ks Vs : ℕ → Set (TopDirectLimit S)}
    (hKS : ∀ j, Ks j ⊆ S (φ j)) (hKc : ∀ j, IsCompact (incl S (φ j) ⁻¹' Ks j))
    (hVo : ∀ j, IsOpen (incl S (φ j) ⁻¹' Vs j)) (hKV : ∀ j, Ks j ⊆ Vs j)
    (hVK : ∀ j, Vs j ⊆ Ks (j + 1)) : IsKOmegaSpace (⋃ j, Vs j) := by
  set VV := ⋃ j, Vs j
  have hKX : ∀ j, IsCompact (Ks j) := fun j ↦ by
    have := (hKc j).image (continuous_incl S (φ j))
    rwa [image_preimage_eq_of_subset fun x hx ↦ ⟨⟨x, hKS j hx⟩, rfl⟩] at this
  have hKVV : ∀ j, Ks j ⊆ VV := fun j ↦ (hKV j).trans (subset_iUnion Vs j)
  have hcpt : ∀ j, IsCompact ((↑) ⁻¹' Ks j : Set VV) := fun j ↦ by
    rw [Subtype.isCompact_iff,
      image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hKVV j)]
    exact hKX j
  refine ⟨compactlyGeneratedSpace_of_isClosed_of_t2 fun s hs ↦ ?_, fun j ↦ (↑) ⁻¹' Ks j, hcpt,
    fun L hL ↦ ?_⟩
  · -- the closedness criterion along the chain
    have hA : ∀ j, IsClosed (((↑) '' s : Set (TopDirectLimit S)) ∩ Ks j) := fun j ↦ by
      have h1 : ((↑) '' s : Set (TopDirectLimit S)) ∩ Ks j = (↑) '' (s ∩ (↑) ⁻¹' Ks j) := by
        rw [image_inter_preimage]
      rw [h1]
      exact (Subtype.isCompact_iff.1 ((hcpt j).of_isClosed_subset (hs _ (hcpt j))
        inter_subset_right)).isClosed
    have ho := isOpen_iUnion_diff_of_chain hS hφ hVo hKV hVK hA
    rw [← isOpen_compl_iff]
    have : sᶜ = (↑) ⁻¹' (VV \ (↑) '' s) := by
      ext z
      simp only [mem_compl_iff, mem_preimage, Set.mem_sdiff, Subtype.coe_prop, true_and,
        Subtype.val_injective.mem_set_image]
    rw [this]
    exact ho.preimage continuous_subtype_val
  · obtain ⟨j, hj⟩ := exists_subset_of_isCompact_of_chain hS hφ hVo hKV hVK
      (Subtype.isCompact_iff.1 hL) (image_subset_iff.2 fun z _ ↦ z.2)
    exact ⟨j, fun z hz ↦ hj ⟨z, hz, rfl⟩⟩

/-- **Compactifying direct limits of Hausdorff spaces are locally `k_ω`**
([GN26, Proposition A.7.20]). -/
theorem IsCompactifying.isLocallyKOmegaSpace {hS : IsDirectSeq S} (hc : hS.IsCompactifying)
    [∀ n, T2Space (S n)] : IsLocallyKOmegaSpace (TopDirectLimit S) := by
  have := hc.t2Space
  refine ⟨this, fun x ↦ ?_⟩
  obtain ⟨n, hn⟩ := hS.exists_mem x
  obtain ⟨φ, Ks, Vs, hφ, hK0, hKS, hKc, hVo, hKV, hVK⟩ := hc.exists_chain (K := {x}) (n := n)
    (singleton_subset_iff.2 hn) ((subsingleton_singleton.preimage Subtype.val_injective).isCompact)
  exact ⟨⋃ j, Vs j, hS.isOpen_iUnion_of_comp
    (monotone_nat_of_le_succ fun j ↦ (hVK j).trans (hKV (j + 1))) hφ.monotone
    (fun k ↦ ⟨k, hφ.id_le k⟩) hVo, mem_iUnion.2 ⟨0, hKV 0 (by rw [hK0]; rfl)⟩,
    isKOmegaSpace_iUnion_of_chain hS hφ hKS hKc hVo hKV hVK⟩

end IsDirectSeq

end LocallyConvex.Analysis

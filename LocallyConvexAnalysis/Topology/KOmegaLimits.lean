/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Topology.KOmega

/-!
# Direct limits and products of `k_ω`-spaces

References: [GN26, Remark A.7.21] (p. 892); H. Glöckner, R. Gramlich, T. Hartnick, *Final group
topologies, Kac–Moody groups and Pontryagin duality*, Israel J. Math. 177 (2010) 49–101, Section 4
(Proposition 4.2(c), (i), Lemma 4.3, Propositions 4.5 and 4.7, pp. 61–65).

## Main results

* `IsDirectSeq.t2Space_isKOmegaSpace_of_compactSpace`: direct limits of ascending sequences of
  compact Hausdorff spaces are Hausdorff `k_ω`-spaces.
* `IsDirectSeq.t2Space_isKOmegaSpace`: direct limits of ascending sequences of Hausdorff
  `k_ω`-spaces are Hausdorff `k_ω`-spaces, and the sequence is compactly regular (GHK,
  Proposition 4.5; Remark A.7.21(a)).
* `isKOmegaSpace_iUnion`, `IsLocallyKOmegaSpace.exists_isOpen_isKOmegaSpace`: countable unions of
  open `k_ω` subsets are `k_ω`, and σ-compact subsets of locally `k_ω`-spaces have open `k_ω`
  neighbourhoods (GHK, Lemma 4.3).
* `IsDirectSeq.isLocallyKOmegaSpace`: direct limits of locally `k_ω`-spaces are locally `k_ω`, and
  the sequence is compactly regular (GHK, Proposition 4.5; Remark A.7.21(a)).
* `IsKOmegaSpace.prod`, `IsLocallyKOmegaSpace.prod`: finite products of (locally) `k_ω`-spaces are
  (locally) `k_ω` (GHK, Proposition 4.2(c), (i)).
* `IsDirectSeq.isOpen_prod_iff`, `IsDirectSeq.isOpen_prod_iff_of_isKOmegaSpace`:
  `lim Sₙ × lim Tₙ = lim (Sₙ × Tₙ)` for locally `k_ω` steps, and the product is (locally) `k_ω`
  (GHK, Proposition 4.7; Remark A.7.21(b)).

## Implementation notes

* GHK obtain Lemma 4.3 from Hausdorff quotients of disjoint unions of `k_ω`-spaces
  (Proposition 4.2(d), (e)), and the compatibility with products from a theorem on direct limits
  of compact spaces. Here countable unions of open `k_ω` subsets are handled directly, and
  Proposition 4.7 follows from the `k`-space property of the product together with the compact
  regularity of the direct limits; we do not claim these arguments are new.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

open TopDirectLimit

universe u

/-! ### Unions of open `k_ω` subsets -/

section Unions

variable {Y : Type u} [TopologicalSpace Y]

/-- A subset `A ⊆ B`, seen inside `B`, is homeomorphic to `A`. -/
def homeomorphSubtypeOfSubset {A B : Set Y} (h : A ⊆ B) :
    ((↑) ⁻¹' A : Set B) ≃ₜ A where
  toFun b := ⟨b.1.1, b.2⟩
  invFun a := ⟨⟨a.1, h a.2⟩, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
    fun b ↦ (b.2 : ((b : B) : Y) ∈ A)
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The empty space is a `k_ω`-space. -/
theorem isKOmegaSpace_empty : IsKOmegaSpace (∅ : Set Y) := by
  have : T2Space (∅ : Set Y) := ⟨fun x ↦ absurd x.2 (notMem_empty _)⟩
  refine ⟨compactlyGeneratedSpace_of_isClosed_of_t2 fun F _ ↦ ?_, fun _ ↦ ∅,
    fun _ ↦ isCompact_empty, fun L _ ↦ ⟨0, fun x _ ↦ absurd x.2 (notMem_empty _)⟩⟩
  rw [eq_empty_of_isEmpty F]
  exact isClosed_empty

/-- A `k_ω` subset is a countable union of compact sets. -/
theorem IsKOmegaSpace.exists_iUnion {A : Set Y} (hA : IsKOmegaSpace A) :
    ∃ K : ℕ → Set Y, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ A) ∧ A ⊆ ⋃ n, K n := by
  obtain ⟨-, K, hKc, hK⟩ := hA
  refine ⟨fun n ↦ (↑) '' K n, fun n ↦ (hKc n).image continuous_subtype_val,
    fun n ↦ ?_, fun x hx ↦ ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  obtain ⟨n, hn⟩ := hK {⟨x, hx⟩} isCompact_singleton
  exact mem_iUnion.2 ⟨n, ⟨x, hx⟩, hn rfl, rfl⟩

variable [T2Space Y]

/-- **Countable unions of open `k_ω` subsets are `k_ω`** (compare Glöckner–Gramlich–Hartnick,
proof of Lemma 4.3, which passes through quotients of disjoint unions): the union is locally
`k_ω`, hence a `k`-space, and a compact subset of it is a finite union of compact subsets of the
pieces (Hausdorff property), which are absorbed by their `k_ω`-sequences. We do not claim this
argument is new. -/
theorem isKOmegaSpace_iUnion {ι : Type*} [Countable ι] {V : ι → Set Y} (hVo : ∀ k, IsOpen (V k))
    (hVk : ∀ k, IsKOmegaSpace (V k)) : IsKOmegaSpace (⋃ k, V k) := by
  set W := ⋃ k, V k
  have hloc : IsLocallyKOmegaSpace W := ⟨inferInstance, fun a ↦ by
    obtain ⟨k, hk⟩ := mem_iUnion.1 a.2
    exact ⟨((↑) : W → Y) ⁻¹' V k, (hVo k).preimage continuous_subtype_val, hk,
      (hVk k).of_homeomorph (homeomorphSubtypeOfSubset (subset_iUnion V k)).symm⟩⟩
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ι
  choose C hCc hC using fun k ↦ (hVk k).2
  have hfin : ∀ N, {k | e k ≤ N}.Finite := fun N ↦ (finite_Iic N).preimage he.injOn
  -- the compact sets `L N`
  set B : ℕ → Set Y := fun N ↦ ⋃ k ∈ {k | e k ≤ N}, ⋃ j ∈ Iic N, (↑) '' C k j
  have hBc : ∀ N, IsCompact (B N) := fun N ↦ (hfin N).isCompact_biUnion fun k _ ↦
    (finite_Iic N).isCompact_biUnion fun j _ ↦ (hCc k j).image continuous_subtype_val
  have hBW : ∀ N, B N ⊆ W := fun N ↦ iUnion₂_subset fun k _ ↦ iUnion₂_subset fun j _ ↦
    image_subset_iff.2 fun x _ ↦ subset_iUnion V k x.2
  have hemb : IsInducing ((↑) : W → Y) := IsInducing.subtypeVal
  refine ⟨hloc.compactlyGeneratedSpace, fun N ↦ (↑) ⁻¹' B N, fun N ↦
    (hemb.isCompact_preimage_iff (by rw [Subtype.range_coe]; exact hBW N)).2 (hBc N),
    fun L hL ↦ ?_⟩
  -- a compact subset of `W` is a finite union of compact subsets of the `V k`
  have hM := hL.image continuous_subtype_val
  obtain ⟨t, ht⟩ := hM.elim_finite_subcover V hVo (image_subset_iff.2 fun a _ ↦ a.2)
  obtain ⟨K, hKc, hKV, hMK⟩ := hM.finite_compact_cover t V (fun k _ ↦ hVo k) ht
  have hJ : ∀ k, ∃ j, ((↑) ⁻¹' K k : Set (V k)) ⊆ C k j := fun k ↦
    hC k _ ((IsInducing.subtypeVal.isCompact_preimage_iff
      (by rw [Subtype.range_coe]; exact hKV k)).2 (hKc k))
  choose J hJ using hJ
  refine ⟨t.sup e ⊔ t.sup J, fun a ha ↦ ?_⟩
  have haM : (a : Y) ∈ ⋃ k ∈ t, K k := hMK ▸ mem_image_of_mem _ ha
  obtain ⟨k, hkt, hak⟩ := mem_iUnion₂.1 haM
  exact mem_iUnion₂.2 ⟨k, (Finset.le_sup (f := e) hkt).trans le_sup_left,
    mem_iUnion₂.2 ⟨J k, mem_Iic.2 ((Finset.le_sup (f := J) hkt).trans le_sup_right),
      ⟨a, hKV k hak⟩, hJ k hak, rfl⟩⟩

/-- In a locally `k_ω`-space, **every compact set has an open neighbourhood which is a
`k_ω`-space**: finitely many open `k_ω` neighbourhoods of its points cover it. -/
theorem IsLocallyKOmegaSpace.exists_isOpen_isKOmegaSpace_of_isCompact
    (h : IsLocallyKOmegaSpace Y) {C : Set Y} (hC : IsCompact C) :
    ∃ U, IsOpen U ∧ C ⊆ U ∧ IsKOmegaSpace U := by
  choose V hV hxV hVk using h.2
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C ↦ V x) (fun x ↦ hV x)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxV x⟩
  refine ⟨⋃ x : t, V x.1, isOpen_iUnion fun x ↦ hV _, fun x hx ↦ ?_,
    isKOmegaSpace_iUnion (fun x ↦ hV _) fun x ↦ hVk _⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
  exact mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩

/-- **σ-compact subsets of locally `k_ω`-spaces have open `k_ω` neighbourhoods**
(Glöckner–Gramlich–Hartnick, Lemma 4.3). -/
theorem IsLocallyKOmegaSpace.exists_isOpen_isKOmegaSpace (h : IsLocallyKOmegaSpace Y)
    {C : ℕ → Set Y} (hC : ∀ n, IsCompact (C n)) :
    ∃ U, IsOpen U ∧ (⋃ n, C n) ⊆ U ∧ IsKOmegaSpace U := by
  choose U hU hCU hUk using fun n ↦ h.exists_isOpen_isKOmegaSpace_of_isCompact (hC n)
  exact ⟨⋃ n, U n, isOpen_iUnion hU, iUnion_mono hCU, isKOmegaSpace_iUnion hU hUk⟩

end Unions

namespace IsDirectSeq

variable {X : Type u} {S : ℕ → Set X} [∀ n, TopologicalSpace (S n)]

/-- **Direct limits of compact Hausdorff spaces are Hausdorff `k_ω`-spaces**: the sequence is
compactifying, so the limit is Hausdorff (Lemma A.7.6(h)); its compact subsets lie in a step
(Lemma A.7.6(e)), whose image is compact, and a set meeting the images of the steps in closed
sets is closed. -/
theorem t2Space_isKOmegaSpace_of_compactSpace (hS : IsDirectSeq S) [∀ n, CompactSpace (S n)]
    [∀ n, T2Space (S n)] : T2Space (TopDirectLimit S) ∧ IsKOmegaSpace (TopDirectLimit S) := by
  have : T2Space (TopDirectLimit S) := hS.isCompactifying_of_locallyCompactSpace.t2Space
  have hR : ∀ n, IsCompact (range (incl S n)) := fun n ↦ by
    rw [← image_univ]
    exact isCompact_univ.image (continuous_incl S n)
  refine ⟨this, compactlyGeneratedSpace_of_isClosed_of_t2 fun F hF ↦ isClosed_iff.2 fun n ↦ ?_,
    fun n ↦ range (incl S n), hR, fun L hL ↦ ?_⟩
  · have := (hF _ (hR n)).preimage (continuous_incl S n)
    rwa [preimage_inter, preimage_range, inter_univ] at this
  · obtain ⟨n, hn⟩ := hS.exists_subset_of_isCompact hL
    exact ⟨n, fun x hx ↦ ⟨⟨x, hn hx⟩, rfl⟩⟩

/-- **Direct limits of Hausdorff `k_ω`-spaces are Hausdorff `k_ω`-spaces** (Glöckner–Gramlich–
Hartnick, Proposition 4.5; [GN26, Remark A.7.21(a)]). With `k_ω`-sequences `K j m` of the
steps, made cumulative (`K' j m`, the union of the images of the `K i k` with `i ≤ j`, `k ≤ m`), the
diagonal sets `K' n n` form an ascending sequence of compact spaces with the same direct limit,
which is a Hausdorff `k_ω`-space (`t2Space_isKOmegaSpace_of_compactSpace`). -/
theorem t2Space_isKOmegaSpace (hS : IsDirectSeq S) [∀ n, T2Space (S n)]
    (hk : ∀ n, IsKOmegaSpace (S n)) :
    T2Space (TopDirectLimit S) ∧ IsKOmegaSpace (TopDirectLimit S) ∧ CompactlyRegular S := by
  choose K hKc hK using fun j ↦ (hk j).2
  -- the cumulative `k_ω`-sequences
  let K' : ∀ j, ℕ → Set (S j) := fun j m ↦
    ⋃ i : Iic j, ⋃ k : Iic m, inclusion (hS.mono (mem_Iic.1 i.2)) '' K i k
  have hK'c : ∀ j m, IsCompact (K' j m) := fun j m ↦ isCompact_iUnion fun i ↦
    isCompact_iUnion fun k ↦ (hKc i k).image (hS.continuous_inclusion_of_le (mem_Iic.1 i.2))
  have hKK' : ∀ j m, K j m ⊆ K' j m := fun j m x hx ↦ mem_iUnion.2 ⟨⟨j, mem_Iic.2 le_rfl⟩,
    mem_iUnion.2 ⟨⟨m, mem_Iic.2 le_rfl⟩, x, hx, rfl⟩⟩
  have hK'up : ∀ {j p m} (hjp : j ≤ p), m ≤ p → inclusion (hS.mono hjp) '' K' j m ⊆ K' p p := by
    rintro j p m hjp hmp _ ⟨y, hy, rfl⟩
    simp only [K', mem_iUnion] at hy
    obtain ⟨i, k, z, hz, rfl⟩ := hy
    exact mem_iUnion.2 ⟨⟨i, mem_Iic.2 ((mem_Iic.1 i.2).trans hjp)⟩, mem_iUnion.2
      ⟨⟨k, mem_Iic.2 ((mem_Iic.1 k.2).trans hmp)⟩, z, hz, rfl⟩⟩
  -- the diagonal sequence, with the topologies of the steps
  let D : ℕ → Set (TopDirectLimit S) := fun n ↦ incl S n '' K' n n
  have hDS : ∀ n, D n ⊆ S n := fun n ↦ image_subset_iff.2 fun x _ ↦ x.2
  let dmap : ∀ n, D n → S n := fun n d ↦ ⟨d.1, hDS n d.2⟩
  let tD : ∀ n, TopologicalSpace (D n) := fun n ↦ TopologicalSpace.induced (dmap n) inferInstance
  have hemb : ∀ n, @IsEmbedding _ _ (tD n) _ (dmap n) := fun n ↦
    ⟨⟨rfl⟩, fun a b h ↦ Subtype.ext (congrArg (fun y : S n ↦ (y : X)) h)⟩
  have hrange : ∀ n, range (dmap n) = K' n n := fun n ↦ by
    ext y
    constructor
    · rintro ⟨⟨_, z, hz, rfl⟩, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨incl S n y, y, hy, rfl⟩, rfl⟩
  have hcpt : ∀ n, @CompactSpace _ (tD n) := fun n ↦ by
    let := tD n
    refine ⟨((hemb n).isInducing.isCompact_iff).2 ?_⟩
    rw [image_univ, hrange]
    exact hK'c n n
  have ht2 : ∀ n, @T2Space _ (tD n) := fun n ↦ by
    let := tD n
    exact (hemb n).t2Space
  let := tD
  have hDseq : IsDirectSeq D := by
    refine ⟨monotone_nat_of_le_succ fun n ↦ ?_, fun x ↦ ?_, fun n ↦ ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨_, hK'up (Nat.le_succ n) (Nat.le_succ n) ⟨z, hz, rfl⟩, rfl⟩
    · obtain ⟨j, hj⟩ := hS.exists_mem x
      obtain ⟨m, hm⟩ := hK j {⟨x, hj⟩} isCompact_singleton
      refine ⟨max j m, ⟨_, hK'up (le_max_left j m) (le_max_right j m)
        ⟨⟨x, hj⟩, hKK' j m (hm rfl), rfl⟩, rfl⟩⟩
    · exact continuous_induced_rng.2 ((hS.continuous_inclusion n).comp
        (continuous_induced_dom (f := dmap n)))
  obtain ⟨hT2D, hkD⟩ := hDseq.t2Space_isKOmegaSpace_of_compactSpace
  -- the two direct limit topologies agree
  have key : (@TopDirectLimit.topology (TopDirectLimit S) ℕ D tD : TopologicalSpace X) =
      TopDirectLimit.topology S := by
    refine le_antisymm (TopDirectLimit.topology_le fun n ↦
      (continuous_incl S n).comp (@continuous_induced_dom _ _ (dmap n) _)) ?_
    refine TopologicalSpace.le_def.2 fun U hU ↦ ?_
    refine (@isOpen_iff X ℕ S _ U).2 fun j ↦ ?_
    have hj := topology_eq_of_absorbing (hk j) (hK'c j) fun L hL ↦
      let ⟨m, hm⟩ := hK j L hL; ⟨m, hm.trans (hKK' j m)⟩
    have : IsOpen[TopDirectLimit.topology (K' j)] (incl S j ⁻¹' U) :=
      (@isOpen_iff (S j) ℕ (K' j) _ _).2 fun m ↦ by
        set p := max j m
        let φ : K' j m → D p := fun y ↦ ⟨incl S p (inclusion (hS.mono (le_max_left j m)) y.1),
          _, hK'up (le_max_left j m) (le_max_right j m) ⟨y.1, y.2, rfl⟩, rfl⟩
        have hφ : Continuous φ := continuous_induced_rng.2
          ((hS.continuous_inclusion_of_le (le_max_left j m)).comp continuous_subtype_val)
        exact ((@isOpen_iff (TopDirectLimit S) ℕ D tD U).1 hU p).preimage hφ
    rwa [hj] at this
  let e : TopDirectLimit D ≃ₜ TopDirectLimit S :=
    { toEquiv := Equiv.refl _
      continuous_toFun := continuous_id_iff_le.2 key.le
      continuous_invFun := continuous_id_iff_le.2 key.ge }
  refine ⟨e.symm.isEmbedding.t2Space, hkD.of_homeomorph e, fun K hK ↦ ?_⟩
  -- compact regularity, through the strict sequence of compact sets
  have hK' : @IsCompact X (@TopDirectLimit.topology (TopDirectLimit S) ℕ D tD) K := by
    rw [key]
    exact hK
  have := hcpt
  have := ht2
  obtain ⟨p, hKp, hKc⟩ := hDseq.isStrict_of_compactSpace.compactlyRegular K hK'
  have himg : dmap p '' (incl D p ⁻¹' K) = incl S p ⁻¹' K := by
    ext y
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hd
    · intro hy
      exact ⟨⟨y.1, hKp hy⟩, hy, rfl⟩
  refine ⟨p, hKp.trans (hDS p), ?_⟩
  rw [← himg]
  exact hKc.image (@continuous_induced_dom _ _ (dmap p) _)

/-- The steps `Vₙ` of Lemma A.7.6(b), built from open subsets `Wₙ ⊆ S n`, are homeomorphic to the
`Wₙ`. -/
def homeomorphUnionSet {W : ∀ n, Set (S n)} (n : ℕ) :
    @Homeomorph (unionSet (fun n ↦ incl S n '' W n) n) (W n)
      (unionTop (fun _ ↦ image_subset_iff.2 fun x _ ↦ x.2) n) _ := by
  have hVS : ∀ n, incl S n '' W n ⊆ S n := fun n ↦ image_subset_iff.2 fun x _ ↦ x.2
  letI := unionTop (S := S) (V := fun n ↦ incl S n '' W n) hVS n
  have hmem : ∀ a : unionSet (fun n ↦ incl S n '' W n) n, unionMap hVS n a ∈ W n := fun a ↦ by
    obtain ⟨w, hw, hwa⟩ := a.2
    have : w = unionMap hVS n a := Subtype.ext hwa
    exact this ▸ hw
  exact
  { toFun := fun a ↦ ⟨unionMap hVS n a, hmem a⟩
    invFun := fun w ↦ ⟨⟨incl S n w, mem_iUnion.2 ⟨n, w, w.2, rfl⟩⟩, w, w.2, rfl⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_induced_dom.subtype_mk hmem
    continuous_invFun := continuous_induced_rng.2 continuous_subtype_val }

/-- **Open `k_ω` neighbourhoods in a direct limit of locally `k_ω`-spaces**
(Glöckner–Gramlich–Hartnick, proof of Proposition 4.5): a compact subset `C` of a step lies in an
open subset `U` of the direct limit which is a Hausdorff `k_ω`-space, and whose compact subsets
lie, and are compact, in some step. `U = ⋃ₙ Wₙ` for open `k_ω` subsets `Wₙ ⊆ S n` with
`Wₙ ⊆ Wₙ₊₁` (Lemma 4.3), and `U = lim Wₙ` (Lemma A.7.6(b)). -/
theorem exists_isOpen_isKOmegaSpace (hS : IsDirectSeq S)
    (hk : ∀ n, IsLocallyKOmegaSpace (S n)) {n₀ : ℕ} {C : Set (S n₀)} (hC : IsCompact C) :
    ∃ U : Set (TopDirectLimit S), IsOpen U ∧ incl S n₀ '' C ⊆ U ∧ T2Space U ∧
      IsKOmegaSpace U ∧ ∀ K ⊆ U, IsCompact K → ∃ p, K ⊆ S p ∧ IsCompact (incl S p ⁻¹' K) := by
  have : ∀ n, T2Space (S n) := fun n ↦ (hk n).1
  -- the compact sets to be covered
  classical
  let Cn : ∀ n, Set (S n) := fun n ↦ if n₀ ≤ n then incl S n ⁻¹' (incl S n₀ '' C) else ∅
  have hCn : ∀ n, IsCompact (Cn n) := fun n ↦ by
    by_cases h : n₀ ≤ n
    · simp only [Cn, h, ↓reduceIte]
      have : incl S n ⁻¹' (incl S n₀ '' C) = inclusion (hS.mono h) '' C := by
        ext y
        constructor
        · rintro ⟨c, hc, hcy⟩
          exact ⟨c, hc, Subtype.ext hcy⟩
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c, hc, rfl⟩
      rw [this]
      exact hC.image (hS.continuous_inclusion_of_le h)
    · simp only [Cn, h, ↓reduceIte, isCompact_empty]
  -- the open `k_ω` sets `Wₙ`
  have hstart : ∃ W : Set (S 0), IsOpen W ∧ IsKOmegaSpace W ∧ Cn 0 ⊆ W := by
    obtain ⟨W, hW, hCW, hWk⟩ := (hk 0).exists_isOpen_isKOmegaSpace (C := fun _ ↦ Cn 0)
      fun _ ↦ hCn 0
    exact ⟨W, hW, hWk, fun x hx ↦ hCW (mem_iUnion.2 ⟨0, hx⟩)⟩
  have hstep : ∀ n (W : Set (S n)), IsKOmegaSpace W → ∃ W' : Set (S (n + 1)), IsOpen W' ∧
      IsKOmegaSpace W' ∧ inclusion (hS.mono (Nat.le_succ n)) '' W ⊆ W' ∧ Cn (n + 1) ⊆ W' := by
    intro n W hWk
    obtain ⟨K, hKc, -, hWK⟩ := hWk.exists_iUnion
    obtain ⟨W', hW', hKW', hW'k⟩ := (hk (n + 1)).exists_isOpen_isKOmegaSpace
      (C := fun j ↦ inclusion (hS.mono (Nat.le_succ n)) '' K j ∪ Cn (n + 1))
      fun j ↦ ((hKc j).image (hS.continuous_inclusion n)).union (hCn (n + 1))
    refine ⟨W', hW', hW'k, ?_, fun x hx ↦ hKW' (mem_iUnion.2 ⟨0, Or.inr hx⟩)⟩
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hWK hw)
    exact hKW' (mem_iUnion.2 ⟨j, Or.inl ⟨w, hj, rfl⟩⟩)
  choose W₀ hW₀ hW₀k hCW₀ using hstart
  choose Wn hWn hWnk hWW hCW using hstep
  let Wseq : ∀ n, {W : Set (S n) // IsOpen W ∧ IsKOmegaSpace W ∧ Cn n ⊆ W} := fun n ↦
    Nat.rec ⟨W₀, hW₀, hW₀k, hCW₀⟩ (fun n W ↦ ⟨Wn n W.1 W.2.2.1, hWn _ _ _, hWnk _ _ _,
      hCW _ _ _⟩) n
  set W : ∀ n, Set (S n) := fun n ↦ (Wseq n).1
  have hWo : ∀ n, IsOpen (W n) := fun n ↦ (Wseq n).2.1
  have hWk : ∀ n, IsKOmegaSpace (W n) := fun n ↦ (Wseq n).2.2.1
  have hCW' : ∀ n, Cn n ⊆ W n := fun n ↦ (Wseq n).2.2.2
  have hWup : ∀ n, inclusion (hS.mono (Nat.le_succ n)) '' W n ⊆ W (n + 1) := fun n ↦
    hWW n _ (Wseq n).2.2.1
  -- the direct limit `U` of the `Wₙ`
  set V : ℕ → Set (TopDirectLimit S) := fun n ↦ incl S n '' W n
  have hVS : ∀ n, V n ⊆ S n := fun n ↦ image_subset_iff.2 fun x _ ↦ x.2
  have hinj : ∀ n, Injective (incl S n) := fun n ↦ Subtype.val_injective
  have hVo : ∀ n, IsOpen (incl S n ⁻¹' V n) := fun n ↦ by
    rw [(hinj n).preimage_image]
    exact hWo n
  have hVmono : Monotone V := monotone_nat_of_le_succ fun n ↦ by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, hWup n ⟨w, hw, rfl⟩, rfl⟩
  have hU : IsOpen (⋃ n, V n) := hS.isOpen_iUnion hVmono hVo
  have hseq := isDirectSeq_unionSet hS hVS hVmono
  let := unionTop hVS
  have hstepk : ∀ n, IsKOmegaSpace (unionSet V n) := fun n ↦
    (hWk n).of_homeomorph (homeomorphUnionSet (W := W) n).symm
  have hstept2 : ∀ n, T2Space (unionSet V n) := fun n ↦
    (homeomorphUnionSet (W := W) n).isEmbedding.t2Space
  obtain ⟨hT2, hkU, hreg⟩ := hseq.t2Space_isKOmegaSpace hstepk
  have htop := topology_iUnion_eq hVS hS hVmono hVo
  let e : (⋃ n, V n) ≃ₜ TopDirectLimit (unionSet V) :=
    { toEquiv := Equiv.refl _
      continuous_toFun := continuous_id_iff_le.2 htop.le
      continuous_invFun := continuous_id_iff_le.2 htop.ge }
  refine ⟨⋃ n, V n, hU, ?_, e.isEmbedding.t2Space, hkU.of_homeomorph e.symm, fun K hKU hK ↦ ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    have : c ∈ Cn n₀ := by
      simp only [Cn, le_rfl, ↓reduceIte]
      exact ⟨c, hc, rfl⟩
    exact mem_iUnion.2 ⟨n₀, c, hCW' n₀ this, rfl⟩
  · -- compact subsets of `U`
    have hK' : IsCompact (((↑) : (⋃ n, V n) → TopDirectLimit S) ⁻¹' K) :=
      (IsInducing.subtypeVal.isCompact_preimage_iff (by rwa [Subtype.range_coe])).2 hK
    obtain ⟨p, hKp, hKc⟩ := hreg _ (hK'.image e.continuous)
    refine ⟨p, fun k hk ↦ hVS p (hKp ⟨⟨k, hKU hk⟩, hk, rfl⟩), ?_⟩
    have himg : unionMap hVS p '' (incl (unionSet V) p ⁻¹' (e '' ((↑) ⁻¹' K))) =
        incl S p ⁻¹' K := by
      ext y
      constructor
      · rintro ⟨a, ⟨b, hb, hba⟩, rfl⟩
        change (a.1.1 : TopDirectLimit S) ∈ K
        have hab : (b : TopDirectLimit S) = a.1.1 := congrArg Subtype.val hba
        rw [← hab]
        exact hb
      · intro hy
        have hyU : (incl S p y : TopDirectLimit S) ∈ ⋃ n, V n := hKU hy
        have hyV := hKp ⟨⟨_, hyU⟩, hy, rfl⟩
        exact ⟨⟨⟨_, hyU⟩, hyV⟩, ⟨⟨_, hyU⟩, hy, rfl⟩, rfl⟩
    rw [← himg]
    exact hKc.image continuous_induced_dom

/-- **Direct limits of locally `k_ω`-spaces are locally `k_ω`** (Glöckner–Gramlich–Hartnick,
Proposition 4.5; [GN26, Remark A.7.21(a)]), and the sequence is compactly regular: every
point, and every pair of points, lies in an open `k_ω` subset (`exists_isOpen_isKOmegaSpace`),
and a compact set is a finite union of compact subsets of such sets. -/
theorem isLocallyKOmegaSpace (hS : IsDirectSeq S) (hk : ∀ n, IsLocallyKOmegaSpace (S n)) :
    IsLocallyKOmegaSpace (TopDirectLimit S) ∧ CompactlyRegular S := by
  have hpair : ∀ x y : TopDirectLimit S, ∃ n, x ∈ S n ∧ y ∈ S n := fun x y ↦ by
    obtain ⟨a, ha⟩ := hS.exists_mem x
    obtain ⟨b, hb⟩ := hS.exists_mem y
    exact ⟨max a b, hS.mono (le_max_left a b) ha, hS.mono (le_max_right a b) hb⟩
  have hT2 : T2Space (TopDirectLimit S) := ⟨fun x y hxy ↦ by
    obtain ⟨n, hx, hy⟩ := hpair x y
    obtain ⟨U, hU, hCU, hUt2, -, -⟩ := exists_isOpen_isKOmegaSpace hS hk
      (C := {⟨x, hx⟩, ⟨y, hy⟩}) ((isCompact_singleton.insert _))
    have hxU : x ∈ U := hCU ⟨⟨x, hx⟩, mem_insert _ _, rfl⟩
    have hyU : y ∈ U := hCU ⟨⟨y, hy⟩, mem_insert_of_mem _ rfl, rfl⟩
    obtain ⟨P, Q, hP, hQ, hxP, hyQ, hPQ⟩ := t2_separation
      (show (⟨x, hxU⟩ : U) ≠ ⟨y, hyU⟩ from fun h ↦ hxy (congrArg Subtype.val h))
    exact ⟨(↑) '' P, (↑) '' Q, hU.isOpenMap_subtype_val _ hP, hU.isOpenMap_subtype_val _ hQ,
      ⟨_, hxP, rfl⟩, ⟨_, hyQ, rfl⟩,
      (disjoint_image_iff Subtype.val_injective).2 hPQ⟩⟩
  choose nx hnx using hS.exists_mem
  choose U hUo hxU _hT2U hUk hreg using fun x : TopDirectLimit S ↦
    exists_isOpen_isKOmegaSpace hS hk (C := {⟨x, hnx x⟩}) isCompact_singleton
  have hxU' : ∀ x, x ∈ U x := fun x ↦ hxU x ⟨⟨x, hnx x⟩, rfl, rfl⟩
  refine ⟨⟨hT2, fun x ↦ ⟨U x, hUo x, hxU' x, hUk x⟩⟩, fun K hK ↦ ?_⟩
  -- compact regularity
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ U x) (fun x ↦ hUo x)
    fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxU' x⟩
  obtain ⟨Kc, hKcc, hKcU, hKeq⟩ := hK.finite_compact_cover t (fun x : K ↦ U x)
    (fun x _ ↦ hUo x) ht
  choose p hpS hpc using fun i : K ↦ hreg i (Kc i) (hKcU i) (hKcc i)
  refine ⟨t.sup p, hKeq.subset.trans (iUnion₂_subset fun i hi ↦
    (hpS i).trans (hS.mono (Finset.le_sup hi))), ?_⟩
  refine (t.isCompact_biUnion fun i hi ↦ hS.isCompact_preimage_of_le (Finset.le_sup hi) (hpS i)
    (hpc i)).of_isClosed_subset (hK.isClosed.preimage (continuous_incl S _)) fun x hx ↦ ?_
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hKeq.subset hx)
  exact mem_iUnion₂.2 ⟨i, hi, hxi⟩

end IsDirectSeq

/-! ### Products -/

section Prod

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]

/-- **Finite products of `k_ω`-spaces are `k_ω`** (Glöckner–Gramlich–Hartnick,
Proposition 4.2(c)), for Hausdorff spaces: `Y = lim Kₙ` and `Z = lim Lₙ` for compact `Kₙ`, `Lₙ`
(Remark A.7.19(b)), so `Y × Z = lim (Kₙ × Lₙ)` (Lemma A.7.9). -/
theorem IsKOmegaSpace.prod [T2Space Y] [T2Space Z] (hY : IsKOmegaSpace Y)
    (hZ : IsKOmegaSpace Z) : IsKOmegaSpace (Y × Z) := by
  obtain ⟨K, hKm, hKc, hKcov, hK⟩ := isKOmegaSpace_iff_exists_topology_eq.1 hY
  obtain ⟨L, hLm, hLc, hLcov, hL⟩ := isKOmegaSpace_iff_exists_topology_eq.1 hZ
  have hSK : IsDirectSeq K := ⟨hKm, hKcov, fun _ ↦ continuous_inclusion _⟩
  have hSL : IsDirectSeq L := ⟨hLm, hLcov, fun _ ↦ continuous_inclusion _⟩
  have : ∀ n, CompactSpace (K n) := fun n ↦ isCompact_iff_compactSpace.1 (hKc n)
  have : ∀ n, CompactSpace (L n) := fun n ↦ isCompact_iff_compactSpace.1 (hLc n)
  have hcK := hSK.isCompactifying_of_locallyCompactSpace
  have hcL := hSL.isCompactifying_of_locallyCompactSpace
  let eY : TopDirectLimit K ≃ₜ Y :=
    { toEquiv := Equiv.refl _
      continuous_toFun := continuous_id_iff_le.2 hK.le
      continuous_invFun := continuous_id_iff_le.2 hK.ge }
  let eZ : TopDirectLimit L ≃ₜ Z :=
    { toEquiv := Equiv.refl _
      continuous_toFun := continuous_id_iff_le.2 hL.le
      continuous_invFun := continuous_id_iff_le.2 hL.ge }
  have : T2Space (TopDirectLimit K) := eY.isEmbedding.t2Space
  have : T2Space (TopDirectLimit L) := eZ.isEmbedding.t2Space
  refine IsKOmegaSpace.of_homeomorph (eY.prodCongr eZ) ?_
  have hRK : ∀ n, IsCompact (range (incl K n)) := fun n ↦ by
    rw [← image_univ]
    exact isCompact_univ.image (continuous_incl K n)
  have hRL : ∀ n, IsCompact (range (incl L n)) := fun n ↦ by
    rw [← image_univ]
    exact isCompact_univ.image (continuous_incl L n)
  refine ⟨compactlyGeneratedSpace_of_isClosed_of_t2 fun F hF ↦ ?_,
    fun n ↦ range (incl K n) ×ˢ range (incl L n), fun n ↦ (hRK n).prod (hRL n), fun C hC ↦ ?_⟩
  · rw [← isOpen_compl_iff, hcK.isOpen_prod_iff hcL]
    intro n
    have hcl := (hF _ ((hRK n).prod (hRL n))).preimage
      ((continuous_incl K n).prodMap (continuous_incl L n))
    have : IsDirectSeq.prodTrace Fᶜ n = ((Prod.map (incl K n) (incl L n)) ⁻¹'
        (F ∩ range (incl K n) ×ˢ range (incl L n)))ᶜ := by
      ext p
      exact ⟨fun h h' ↦ h h'.1, fun h h' ↦ h ⟨h', ⟨_, rfl⟩, ⟨_, rfl⟩⟩⟩
    rw [this]
    exact hcl.isOpen_compl
  · obtain ⟨a, ha⟩ := hSK.exists_subset_of_isCompact (hC.image continuous_fst)
    obtain ⟨b, hb⟩ := hSL.exists_subset_of_isCompact (hC.image continuous_snd)
    refine ⟨max a b, fun c hc ↦ ⟨⟨⟨c.1, hKm (le_max_left a b) (ha ⟨c, hc, rfl⟩)⟩, rfl⟩,
      ⟨⟨c.2, hLm (le_max_right a b) (hb ⟨c, hc, rfl⟩)⟩, rfl⟩⟩⟩

/-- **Finite products of locally `k_ω`-spaces are locally `k_ω`** (Glöckner–Gramlich–Hartnick,
Proposition 4.2(i)). -/
theorem IsLocallyKOmegaSpace.prod (hY : IsLocallyKOmegaSpace Y) (hZ : IsLocallyKOmegaSpace Z) :
    IsLocallyKOmegaSpace (Y × Z) := by
  have := hY.1
  have := hZ.1
  refine ⟨inferInstance, fun p ↦ ?_⟩
  obtain ⟨U, hU, hpU, hUk⟩ := hY.2 p.1
  obtain ⟨V, hV, hpV, hVk⟩ := hZ.2 p.2
  exact ⟨U ×ˢ V, hU.prod hV, ⟨hpU, hpV⟩,
    (hUk.prod hVk).of_homeomorph (Homeomorph.Set.prod U V).symm⟩

end Prod

/-- **Direct limits of locally `k_ω`-spaces commute with finite products**
(Glöckner–Gramlich–Hartnick, Proposition 4.7; [GN26, Remark A.7.21(b)]): a subset of
`lim Sₙ × lim Tₙ` is open iff its traces on all `Sₙ × Tₙ` are, i.e.
`lim Sₙ × lim Tₙ = lim (Sₙ × Tₙ)`. The product is locally `k_ω`, hence a `k`-space, and a compact
subset of it lies in a product of compact subsets of some `S p` and `T p` (compact regularity),
on which the two topologies agree. We do not claim this argument is new. -/
theorem IsDirectSeq.isOpen_prod_iff {X X' : Type u} {S : ℕ → Set X} {T : ℕ → Set X'}
    [∀ n, TopologicalSpace (S n)] [∀ n, TopologicalSpace (T n)] (hS : IsDirectSeq S)
    (hT : IsDirectSeq T) (hk : ∀ n, IsLocallyKOmegaSpace (S n))
    (hk' : ∀ n, IsLocallyKOmegaSpace (T n)) {W : Set (TopDirectLimit S × TopDirectLimit T)} :
    IsOpen W ↔ ∀ n, IsOpen (IsDirectSeq.prodTrace W n) := by
  obtain ⟨hlS, hregS⟩ := hS.isLocallyKOmegaSpace hk
  obtain ⟨hlT, hregT⟩ := hT.isLocallyKOmegaSpace hk'
  have hl := hlS.prod hlT
  have := hl.1
  have := hl.compactlyGeneratedSpace
  have : ∀ n, T2Space (S n) := fun n ↦ (hk n).1
  have : ∀ n, T2Space (T n) := fun n ↦ (hk' n).1
  refine ⟨fun hW n ↦ hW.preimage ((continuous_incl S n).prodMap (continuous_incl T n)),
    fun hW ↦ ?_⟩
  rw [← isClosed_compl_iff]
  refine CompactlyGeneratedSpace.isClosed fun C hC ↦ ?_
  obtain ⟨a, haS, hac⟩ := hregS _ (hC.image continuous_fst)
  obtain ⟨b, hbT, hbc⟩ := hregT _ (hC.image continuous_snd)
  set p := max a b
  set A := incl S p ⁻¹' (Prod.fst '' C)
  set B := incl T p ⁻¹' (Prod.snd '' C)
  have hA : IsCompact A := hS.isCompact_preimage_of_le (le_max_left a b) haS hac
  have hB : IsCompact B := hT.isCompact_preimage_of_le (le_max_right a b) hbT hbc
  set g := Prod.map (incl S p) (incl T p)
  have hg : Continuous g := (continuous_incl S p).prodMap (continuous_incl T p)
  have hCg : C ⊆ g '' (A ×ˢ B) := fun c hc ↦
    ⟨(⟨c.1, hS.mono (le_max_left a b) (haS ⟨c, hc, rfl⟩)⟩,
      ⟨c.2, hT.mono (le_max_right a b) (hbT ⟨c, hc, rfl⟩)⟩), ⟨⟨c, hc, rfl⟩, ⟨c, hc, rfl⟩⟩, rfl⟩
  have hcl : IsClosed (g '' ((IsDirectSeq.prodTrace W p)ᶜ ∩ A ×ˢ B)) :=
    (((hA.prod hB).inter_left (hW p).isClosed_compl).image hg).isClosed
  have : Wᶜ ∩ C = g '' ((IsDirectSeq.prodTrace W p)ᶜ ∩ A ×ˢ B) ∩ C := by
    ext c
    constructor
    · rintro ⟨hcW, hcC⟩
      obtain ⟨q, hq, hqc⟩ := hCg hcC
      exact ⟨⟨q, ⟨fun h ↦ hcW (hqc ▸ h), hq⟩, hqc⟩, hcC⟩
    · rintro ⟨⟨q, ⟨hqW, -⟩, rfl⟩, hcC⟩
      exact ⟨hqW, hcC⟩
  rw [this]
  exact hcl.inter hC.isClosed

/-- **Direct limits of `k_ω`-spaces commute with finite products**
([GN26, Remark A.7.21(b)]), for Hausdorff steps, and the product is a `k_ω`-space. -/
theorem IsDirectSeq.isOpen_prod_iff_of_isKOmegaSpace {X X' : Type u} {S : ℕ → Set X}
    {T : ℕ → Set X'} [∀ n, TopologicalSpace (S n)] [∀ n, TopologicalSpace (T n)]
    [∀ n, T2Space (S n)] [∀ n, T2Space (T n)] (hS : IsDirectSeq S) (hT : IsDirectSeq T)
    (hk : ∀ n, IsKOmegaSpace (S n)) (hk' : ∀ n, IsKOmegaSpace (T n)) :
    IsKOmegaSpace (TopDirectLimit S × TopDirectLimit T) ∧
      ∀ W : Set (TopDirectLimit S × TopDirectLimit T),
        IsOpen W ↔ ∀ n, IsOpen (IsDirectSeq.prodTrace W n) := by
  obtain ⟨h1, h2, -⟩ := hS.t2Space_isKOmegaSpace hk
  obtain ⟨h1', h2', -⟩ := hT.t2Space_isKOmegaSpace hk'
  exact ⟨h2.prod h2', fun W ↦ hS.isOpen_prod_iff hT (fun n ↦ (hk n).isLocallyKOmegaSpace)
    fun n ↦ (hk' n).isLocallyKOmegaSpace⟩

end LocallyConvex.Analysis

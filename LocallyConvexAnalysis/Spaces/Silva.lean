/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Spaces.DirectLimit
public import LocallyConvexAnalysis.Calculus.MichalBastiani
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Silva spaces

A **Silva space** is the locally convex direct limit of an ascending sequence of Banach spaces
`E₀ ⊆ E₁ ⊆ ⋯` whose inclusions `Eₙ → Eₙ₊₁` are compact operators ([GN26, Definition B.13.12]). We
work more generally with locally convex steps and compact inclusions, in two forms: subspaces of a
vector space (`LCDirectLimit.IsSilva`) and continuous linear maps into a locally convex space
(`IsSilvaSystem`), the second being stable under finite products.

Reference: [GN26, Definition B.13.12, Proposition B.13.13] (pp. 950–952) and Proposition 2.7.1
(p. 233).

## Main definitions

* `IsSilvaSystem j u`: a presentation of `E` by continuous linear maps `j n : Eₙ → E` and compact
  operators `u n : Eₙ → Eₙ₊₁` with `j (n + 1) ∘ u n = j n`, whose ranges cover `E`, such that `E`
  carries the locally convex direct limit topology.
* `LCDirectLimit.IsSilva S`: an ascending sequence of subspaces `S n` covering `V` whose
  inclusions `S n → S (n + 1)` are compact operators ([GN26, Definition B.13.12], for locally
  convex steps).

## Main results

* `IsSilvaSystem.isOpen_iff`, `LCDirectLimit.IsSilva.isOpen_iff`: a set is open as soon as its
  traces on all steps are open, so the locally convex direct limit topology is the direct limit
  topology of the topological spaces `Eₙ` (Proposition B.13.13(a)).
* `LCDirectLimit.IsSilva.continuous_iff`: hence a map to any topological space is continuous as
  soon as its restrictions to the steps are (Lemma A.7.3).
* `LCDirectLimit.IsSilva.t2Space`: the limit is Hausdorff if the steps are `T₁`.
* `LCDirectLimit.IsSilva.exists_subset_isCompact`: compact regularity (Proposition B.13.13(b)),
  for sequential steps.
* `LCDirectLimit.IsSilva.exists_subset_isVonNBounded`: bounded regularity (Proposition
  B.13.13(c)), for steps with bounded `0`-neighbourhoods (for instance Banach spaces).
* `LCDirectLimit.IsSilva.isCompact_closure_of_isVonNBounded`: bounded sets are relatively compact
  (Proposition B.13.13(d)).
* `IsSilvaSystem.contDiffMBOn_of_comp`, `LCDirectLimit.IsSilva.contDiffMBOn_iUnion`: a map is
  `C^k` as soon as its restrictions to the steps are (Proposition 2.7.1).
* `IsSilvaSystem.prod`: the product of two Silva systems is a Silva system.

## Implementation notes

* Glöckner–Neeb deduce (a) from the theory of compactifying direct sequences of topological
  spaces (Corollary A.7.12, through Lemmas A.7.4, A.7.6 and A.7.9). We give a direct argument
  instead: given an open set `O` whose traces are open and `x ∈ O ∩ Eₘ`, we build compact sets
  `Kᵢ ⊆ Eₘ₊ᵢ` mapped into `O` and convex sets `Aᵢ` with `x + Aᵢ ⊆ Kᵢ`, where
  `Aᵢ₊₁ = Aᵢ + εᵢ Uᵢ` for a convex `0`-neighbourhood `Uᵢ` of `Eₘ₊ᵢ` whose image in `Eₘ₊ᵢ₊₁` lies
  in a compact set `Lᵢ`, and `Kᵢ₊₁ = Kᵢ + εᵢ Lᵢ`, with `εᵢ` so small that `Kᵢ₊₁` is still mapped
  into `O`. The union of the `Aᵢ` is a convex `0`-neighbourhood by Lemma B.13.6(a). It needs
  neither completeness, nor norms, nor the Hausdorff property.
* Likewise, Glöckner–Neeb deduce (b) from the theory of `k_ω`-spaces (Proposition A.7.20). We show
  directly that the compact sets `k Lₚ` cover the limit and detect closed sets, which forces a
  compact set into finitely many of them.
* Glöckner–Neeb use Lemma A.7.9 (products of compactifying direct limits) for the continuity of
  the iterated derivatives in Proposition 2.7.1; here the product of two Silva systems is again a
  Silva system (`IsSilvaSystem.prod`), which is elementary for locally convex direct limits.
* We do not claim these arguments are new.
* Reflexivity, the Fréchet dual, completeness and the `k_ω` property (Proposition B.13.13(e)–(g))
  are in `Spaces/SilvaDuality.lean`; the general comparison of the locally convex and topological
  direct limit topologies (Corollary A.7.12) is
  `IsDirectSeq.IsCompactifying.topology_eq_lcDirectLimit`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Topology Bornology
open scoped Topology Pointwise

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Silva systems -/

section System

universe u w

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {Eₙ : ℕ → Type w} [∀ n, AddCommGroup (Eₙ n)] [∀ n, Module ℝ (Eₙ n)]
  [∀ n, TopologicalSpace (Eₙ n)] [∀ n, IsTopologicalAddGroup (Eₙ n)]
  [∀ n, ContinuousSMul ℝ (Eₙ n)]

/-- A **Silva system** presenting `E`: continuous linear maps `j n : Eₙ n → E` and compact
operators `u n : Eₙ n → Eₙ (n + 1)` with `j (n + 1) ∘ u n = j n`, whose ranges cover `E`, such that
`E` carries the locally convex direct limit topology: a convex set `C ∋ 0` is a `0`-neighbourhood
as soon as all the `j n⁻¹(C)` are ([GN26, Lemma B.13.6(a)]). Silva spaces
(`LCDirectLimit.IsSilva`) are the case of injective `j n`; unlike subspaces, the presentation by
maps passes to finite products (`IsSilvaSystem.prod`). -/
structure IsSilvaSystem (j : ∀ n, Eₙ n →L[ℝ] E) (u : ∀ n, Eₙ n →L[ℝ] Eₙ (n + 1)) : Prop where
  comp_apply : ∀ n x, j (n + 1) (u n x) = j n x
  isCompactOperator : ∀ n, IsCompactOperator (u n)
  exists_mem_range : ∀ x : E, ∃ n, x ∈ range (j n)
  mem_nhds_zero : ∀ C : Set E, Convex ℝ C → (0 : E) ∈ C → (∀ n, j n ⁻¹' C ∈ 𝓝 0) → C ∈ 𝓝 0

namespace IsSilvaSystem

variable {j : ∀ n, Eₙ n →L[ℝ] E} {u : ∀ n, Eₙ n →L[ℝ] Eₙ (n + 1)}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [∀ n, IsTopologicalAddGroup (Eₙ n)]
  [∀ n, ContinuousSMul ℝ (Eₙ n)] in
/-- The ranges of a Silva system increase. -/
theorem range_mono (h : IsSilvaSystem j u) : Monotone fun n ↦ range (j n) :=
  monotone_nat_of_le_succ fun n ↦ by
    rintro _ ⟨y, rfl⟩
    exact ⟨u n y, h.comp_apply n y⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [∀ n, IsTopologicalAddGroup (Eₙ n)]
  [∀ n, ContinuousSMul ℝ (Eₙ n)] in
/-- Two points of `E` lie in a common range. -/
theorem exists_mem_range₂ (h : IsSilvaSystem j u) (x y : E) :
    ∃ n, x ∈ range (j n) ∧ y ∈ range (j n) := by
  obtain ⟨a, ha⟩ := h.exists_mem_range x
  obtain ⟨b, hb⟩ := h.exists_mem_range y
  exact ⟨max a b, h.range_mono (le_max_left _ _) ha, h.range_mono (le_max_right _ _) hb⟩

/-- The composite of `n` steps of a Silva system, `Eₙ m → Eₙ (m + d)`. -/
def iter (u : ∀ n, Eₙ n →L[ℝ] Eₙ (n + 1)) (m : ℕ) : ∀ d, Eₙ m →L[ℝ] Eₙ (m + d)
  | 0 => ContinuousLinearMap.id ℝ (Eₙ m)
  | d + 1 => (u (m + d)).comp (iter u m d)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [∀ n, IsTopologicalAddGroup (Eₙ n)]
  [∀ n, ContinuousSMul ℝ (Eₙ n)] in
theorem comp_iter_apply (h : IsSilvaSystem j u) (m : ℕ) :
    ∀ d x, j (m + d) (iter u m d x) = j m x
  | 0, _ => rfl
  | d + 1, x => (h.comp_apply (m + d) _).trans (comp_iter_apply h m d x)

variable [∀ n, LocallyConvexSpace ℝ (Eₙ n)]

omit [ContinuousSMul ℝ E] in
/-- **The direct limit topology** ([GN26, Proposition B.13.13(a)]): a set is open in a Silva
space as soon as its preimages in all steps are open. -/
theorem isOpen_iff (h : IsSilvaSystem j u) {O : Set E} :
    IsOpen O ↔ ∀ n, IsOpen (j n ⁻¹' O) := by
  refine ⟨fun hO n ↦ hO.preimage (j n).continuous, fun hO ↦ ?_⟩
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  obtain ⟨m, y₀, rfl⟩ := h.exists_mem_range x
  -- the state at stage `i`: a compact `K ⊆ Eₙ (m + i)` mapped into `O` and a convex `A ∋ 0`
  -- with `x + A ⊆ j(K)`
  let P : ∀ i, Set (Eₙ (m + i)) × Set E → Prop := fun i p ↦
    IsCompact p.1 ∧ j (m + i) '' p.1 ⊆ O ∧ (∀ a ∈ p.2, j m y₀ + a ∈ j (m + i) '' p.1) ∧
      Convex ℝ p.2 ∧ (0 : E) ∈ p.2
  have hstep : ∀ i (p : Set (Eₙ (m + i)) × Set E), P i p →
      ∃ q : Set (Eₙ (m + (i + 1))) × Set E, P (i + 1) q ∧ p.2 ⊆ q.2 ∧
        j (m + i) ⁻¹' q.2 ∈ 𝓝 0 := by
    rintro i ⟨K, A⟩ ⟨hK, hKO, hAK, hAc, hA0⟩
    -- room around `ι(K)` inside `O`
    obtain ⟨N, hN, hKN⟩ := compact_open_separated_add_right (hK.image (u (m + i)).continuous)
      (hO (m + (i + 1))) (by
        rintro _ ⟨k, hk, rfl⟩
        change j (m + i + 1) (u (m + i) k) ∈ O
        rw [h.comp_apply]
        exact hKO ⟨k, hk, rfl⟩)
    -- a convex `0`-neighbourhood of `Eₙ (m + i)` mapped into a compact set `L`
    obtain ⟨L, hL, hιL⟩ := h.isCompactOperator (m + i)
    obtain ⟨U, ⟨hU, hUc⟩, hUL⟩ := (LocallyConvexSpace.convex_basis_zero ℝ _).mem_iff.1 hιL
    -- a small multiple of `L` fits in `N`
    obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hL.isVonNBounded ℝ hN)
    set c : ℝ := max r 1
    have hc : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hcL : c⁻¹ • L ⊆ N := by
      have := hr c (by rw [Real.norm_of_nonneg hc.le]; exact le_max_left _ _)
      rintro _ ⟨l, hl, rfl⟩
      obtain ⟨n, hn, hnl⟩ := this hl
      beta_reduce at hnl ⊢
      rw [← hnl, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      exact hn
    refine ⟨(u (m + i) '' K + c⁻¹ • L, A + c⁻¹ • (j (m + i) '' U)),
      ⟨(hK.image (u (m + i)).continuous).add (hL.smul _), ?_, ?_,
        hAc.add ((hUc.linear_image (j (m + i) : Eₙ (m + i) →ₗ[ℝ] E)).smul _), ?_⟩, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hKN (add_subset_add_left hcL hy)
    · rintro _ ⟨a, ha, _, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      obtain ⟨k, hk, hka⟩ := hAK a ha
      refine ⟨u (m + i) k + c⁻¹ • u (m + i) w, ⟨u (m + i) k, ⟨k, hk, rfl⟩, c⁻¹ • u (m + i) w,
        smul_mem_smul_set (hUL hw), rfl⟩, ?_⟩
      change j (m + i + 1) (u (m + i) k + c⁻¹ • u (m + i) w) = _
      rw [map_add, map_smul, h.comp_apply, h.comp_apply, hka, add_assoc]
    · exact ⟨0, hA0, 0, ⟨0, ⟨0, mem_of_mem_nhds hU, map_zero _⟩, smul_zero _⟩, add_zero 0⟩
    · exact fun a ha ↦ ⟨a, ha, 0, ⟨0, ⟨0, mem_of_mem_nhds hU, map_zero _⟩, smul_zero _⟩,
        add_zero a⟩
    · refine mem_of_superset ((set_smul_mem_nhds_zero_iff (inv_ne_zero hc.ne')).2 hU) ?_
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨0, hA0, c⁻¹ • j (m + i) w, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, ?_⟩
      beta_reduce
      rw [zero_add, map_smul]
  let seq : ∀ i, {p : Set (Eₙ (m + i)) × Set E // P i p} := fun i ↦
    Nat.rec (motive := fun i ↦ {p : Set (Eₙ (m + i)) × Set E // P i p})
      ⟨({y₀}, {0}), isCompact_singleton,
        by rw [image_singleton, singleton_subset_iff]; exact hx,
        fun a ha ↦ by rw [mem_singleton_iff.1 ha, add_zero]; exact ⟨y₀, rfl, rfl⟩,
        convex_singleton 0, rfl⟩
      (fun i p ↦ ⟨(hstep i p.1 p.2).choose, (hstep i p.1 p.2).choose_spec.1⟩) i
  have hmono : ∀ i, (seq i).1.2 ⊆ (seq (i + 1)).1.2 := fun i ↦
    (hstep i (seq i).1 (seq i).2).choose_spec.2.1
  have htrace : ∀ i, j (m + i) ⁻¹' (seq (i + 1)).1.2 ∈ 𝓝 0 := fun i ↦
    (hstep i (seq i).1 (seq i).2).choose_spec.2.2
  set W : Set E := ⋃ i, (seq i).1.2
  have hWc : Convex ℝ W :=
    Directed.convex_iUnion (Monotone.directed_le (monotone_nat_of_le_succ hmono))
      fun i ↦ (seq i).2.2.2.2.1
  have hW0 : (0 : E) ∈ W := mem_iUnion.2 ⟨0, (seq 0).2.2.2.2.2⟩
  -- the traces of `W`: directly for `n ≥ m`, through `iter` for `n < m`
  have hge : ∀ n, m ≤ n → j n ⁻¹' W ∈ 𝓝 0 := fun n hn ↦ by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact mem_of_superset (htrace i) fun y hy ↦ mem_iUnion.2 ⟨i + 1, hy⟩
  have hW : W ∈ 𝓝 (0 : E) := by
    refine h.mem_nhds_zero W hWc hW0 fun n ↦ ?_
    have hc := (iter u n (m - n)).continuous.tendsto 0
    rw [map_zero] at hc
    refine mem_of_superset (hc (hge (n + (m - n)) (by omega))) fun y hy ↦ ?_
    rwa [mem_preimage, mem_preimage, comp_iter_apply h] at hy
  rw [← map_add_left_nhds_zero (j m y₀)]
  refine mem_map.2 (mem_of_superset hW fun w hw ↦ ?_)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hw
  exact (seq i).2.2.1 ((seq i).2.2.2.1 w hi)

omit [ContinuousSMul ℝ E] in
/-- A map from a Silva space to a topological space is continuous on an open set `U` as soon as
its composites with the steps are continuous on the preimages of `U`
([GN26, proof of Proposition 2.7.1]). -/
theorem continuousOn_of_comp (h : IsSilvaSystem j u) {Y : Type*} [TopologicalSpace Y]
    {f : E → Y} {U : Set E} (hU : IsOpen U) (hf : ∀ n, ContinuousOn (f ∘ j n) (j n ⁻¹' U)) :
    ContinuousOn f U := by
  refine (continuousOn_open_iff hU).2 fun t ht ↦ h.isOpen_iff.2 fun n ↦ ?_
  rw [preimage_inter, ← preimage_comp]
  exact (continuousOn_open_iff (hU.preimage (j n).continuous)).1 (hf n) t ht

omit [IsTopologicalAddGroup E] [∀ n, IsTopologicalAddGroup (Eₙ n)] [∀ n, ContinuousSMul ℝ (Eₙ n)]
  [∀ n, LocallyConvexSpace ℝ (Eₙ n)] in
/-- **Products of Silva systems** (compare [GN26, Lemma A.7.9]): `E × E'` is presented by
the products of the steps. For the topology, a convex set `C ∋ 0` contains
`{(x, y) | (2x, 0) ∈ C, (0, 2y) ∈ C}`. -/
theorem prod {E' : Type*} [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
    [ContinuousSMul ℝ E'] {Eₙ' : ℕ → Type*} [∀ n, AddCommGroup (Eₙ' n)] [∀ n, Module ℝ (Eₙ' n)]
    [∀ n, TopologicalSpace (Eₙ' n)] {j' : ∀ n, Eₙ' n →L[ℝ] E'}
    {u' : ∀ n, Eₙ' n →L[ℝ] Eₙ' (n + 1)} (h : IsSilvaSystem j u) (h' : IsSilvaSystem j' u') :
    IsSilvaSystem (fun n ↦ (j n).prodMap (j' n)) (fun n ↦ (u n).prodMap (u' n)) where
  comp_apply n x := Prod.ext (h.comp_apply n x.1) (h'.comp_apply n x.2)
  isCompactOperator n := by
    obtain ⟨K, hK, hKn⟩ := h.isCompactOperator n
    obtain ⟨K', hK', hK'n⟩ := h'.isCompactOperator n
    refine ⟨K ×ˢ K', hK.prod hK', ?_⟩
    rw [← Prod.mk_zero_zero, nhds_prod_eq]
    exact prod_mem_prod hKn hK'n
  exists_mem_range x := by
    obtain ⟨a, ha⟩ := h.exists_mem_range x.1
    obtain ⟨b, hb⟩ := h'.exists_mem_range x.2
    obtain ⟨y, hy⟩ := h.range_mono (le_max_left a b) ha
    obtain ⟨z, hz⟩ := h'.range_mono (le_max_right a b) hb
    exact ⟨max a b, (y, z), Prod.ext hy hz⟩
  mem_nhds_zero C hC h0 hn := by
    have hC₁ : {x : E | (x, (0 : E')) ∈ C} ∈ 𝓝 0 := by
      refine h.mem_nhds_zero _ (hC.linear_preimage (LinearMap.inl ℝ E E')) h0 fun n ↦ ?_
      have ht := (continuous_id.prodMk (continuous_const (y := (0 : Eₙ' n)))).tendsto (0 : Eₙ n)
      exact mem_of_superset (mem_map.1 (ht (hn n))) fun y hy ↦ by simpa using hy
    have hC₂ : {y : E' | ((0 : E), y) ∈ C} ∈ 𝓝 0 := by
      refine h'.mem_nhds_zero _ (hC.linear_preimage (LinearMap.inr ℝ E E')) h0 fun n ↦ ?_
      have ht := ((continuous_const (y := (0 : Eₙ n))).prodMk continuous_id).tendsto (0 : Eₙ' n)
      exact mem_of_superset (mem_map.1 (ht (hn n))) fun y hy ↦ by simpa using hy
    have h₁ : {x : E | (2 : ℝ) • x ∈ {x : E | (x, (0 : E')) ∈ C}} ∈ 𝓝 0 :=
      (continuous_const_smul (2 : ℝ)).tendsto' 0 0 (smul_zero _) hC₁
    have h₂ : {y : E' | (2 : ℝ) • y ∈ {y : E' | ((0 : E), y) ∈ C}} ∈ 𝓝 0 :=
      (continuous_const_smul (2 : ℝ)).tendsto' 0 0 (smul_zero _) hC₂
    refine mem_of_superset (show _ ∈ 𝓝 ((0, 0) : E × E') from prod_mem_nhds h₁ h₂) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have := hC hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    ext <;> simp [smul_smul]

end IsSilvaSystem

end System

/-- **`C^k` maps on Silva spaces** ([GN26, Proposition 2.7.1 and Lemma 2.7.2]): a map on an
open subset `U` of a Silva space is `C^k` as soon as its composites with the steps are `C^k` on the
preimages of `U`. The iterated directional derivatives are computed in the steps, and their
continuity follows from the direct limit topology of `E × E`, presented by the products of the
steps (`IsSilvaSystem.prod`). -/
theorem IsSilvaSystem.contDiffMBOn_of_comp {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [T2Space F] :
    ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {Eₙ : ℕ → Type w} [∀ n, AddCommGroup (Eₙ n)]
    [∀ n, Module ℝ (Eₙ n)] [∀ n, TopologicalSpace (Eₙ n)] [∀ n, IsTopologicalAddGroup (Eₙ n)]
    [∀ n, ContinuousSMul ℝ (Eₙ n)] [∀ n, LocallyConvexSpace ℝ (Eₙ n)] [∀ n, T2Space (Eₙ n)]
    {j : ∀ n, Eₙ n →L[ℝ] E} {u : ∀ n, Eₙ n →L[ℝ] Eₙ (n + 1)}, IsSilvaSystem j u →
    ∀ {U : Set E} {f : E → F}, IsOpen U → (∀ n, ContDiffMBOn k (f ∘ j n) (j n ⁻¹' U)) →
      ContDiffMBOn k f U := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ _ Eₙ _ _ _ _ _ _ _ j u h U f hU hf
    exact h.continuousOn_of_comp hU hf
  | succ k ih =>
    intro E _ _ _ _ _ Eₙ _ _ _ _ _ _ _ j u h U f hU hf
    -- directional derivatives are computed in the steps
    have hkey : ∀ n y z, y ∈ j n ⁻¹' U →
        HasDirDerivAt f (j n y) (j n z) (dMB (f ∘ j n) (y, z)) := by
      intro n y z hy
      have := (hf n).hasDirDerivAt hy z
      unfold HasDirDerivAt at this ⊢
      simpa [Function.comp_def, map_add, map_smul] using this
    refine ⟨h.continuousOn_of_comp hU fun n ↦ (hf n).continuousOn, fun x hx v ↦ ?_, ?_⟩
    · obtain ⟨n, ⟨y, rfl⟩, ⟨z, rfl⟩⟩ := h.exists_mem_range₂ x v
      have hd := hkey n y z hx
      rwa [hd.dMB_eq]
    · refine ih (h.prod h) (hU.prod isOpen_univ) fun n ↦ ?_
      have hpre : ((j n).prodMap (j n)) ⁻¹' (U ×ˢ univ) = (j n ⁻¹' U) ×ˢ univ := by
        ext
        simp
      rw [hpre]
      exact ContDiffMBOn.congr_of_isOpen ((hU.preimage (j n).continuous).prod isOpen_univ)
        (fun p hp ↦ ((hkey n p.1 p.2 hp.1).dMB_eq).symm) (hf n).2.2

namespace LCDirectLimit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Silva

variable (S : ℕ → Submodule ℝ V) [∀ n, TopologicalSpace (S n)]

/-- A **Silva sequence** ([GN26, Definition B.13.12], for locally convex steps): an
ascending sequence of subspaces covering `V` whose inclusions `S n → S (n + 1)` are compact
operators. -/
structure IsSilva : Prop where
  mono : Monotone S
  exists_mem : ∀ v : V, ∃ n, v ∈ S n
  isCompactOperator_succ : ∀ n, IsCompactOperator (Submodule.inclusion (mono (Nat.le_succ n)))

variable {S} [∀ n, IsTopologicalAddGroup (S n)] [∀ n, ContinuousSMul ℝ (S n)]

/-- The inclusions of a Silva sequence are continuous. -/
theorem IsSilva.continuous_inclusion (hS : IsSilva S) {m n : ℕ} (h : m ≤ n) :
    Continuous (Submodule.inclusion (hS.mono h)) := by
  induction n, h using Nat.le_induction with
  | base => exact continuous_id
  | succ n hmn ih => exact (hS.isCompactOperator_succ n).continuous.comp ih

variable [∀ n, LocallyConvexSpace ℝ (S n)]

omit [∀ n, LocallyConvexSpace ℝ (S n)] in
/-- A Silva sequence of subspaces is a Silva system. -/
theorem IsSilva.isSilvaSystem (hS : IsSilva S) :
    IsSilvaSystem (E := LCDirectLimit S) (fun n ↦ ⟨incl S n, continuous_incl S n⟩)
      (fun n ↦ ⟨Submodule.inclusion (hS.mono (Nat.le_succ n)),
        (hS.isCompactOperator_succ n).continuous⟩) where
  comp_apply _ _ := rfl
  isCompactOperator n := hS.isCompactOperator_succ n
  exists_mem_range x := let ⟨n, hn⟩ := hS.exists_mem x; ⟨n, ⟨x, hn⟩, rfl⟩
  mem_nhds_zero _ hC h0 hn := (mem_nhds_zero_iff_of_convex S hS.exists_mem hC h0).2 hn

/-- **The direct limit topology** ([GN26, Proposition B.13.13(a)]): for a Silva sequence, a
set is open in the locally convex direct limit as soon as its traces on all steps are open. -/
theorem IsSilva.isOpen_iff (hS : IsSilva S) {O : Set (LCDirectLimit S)} :
    IsOpen O ↔ ∀ n, IsOpen (incl S n ⁻¹' O) :=
  hS.isSilvaSystem.isOpen_iff

/-- **The universal property of the direct limit topology** ([GN26, Lemma A.7.3], with
Proposition B.13.13(a)): a map from a Silva space to a topological space is continuous as soon as
its restrictions to the steps are. -/
theorem IsSilva.continuous_iff (hS : IsSilva S) {Y : Type*} [TopologicalSpace Y]
    {f : LCDirectLimit S → Y} : Continuous f ↔ ∀ n, Continuous (f ∘ incl S n) :=
  ⟨fun hf n ↦ hf.comp (continuous_incl S n), fun hf ↦ continuous_def.2 fun _ hG ↦
    hS.isOpen_iff.2 fun n ↦ (hf n).isOpen_preimage _ hG⟩

/-- **Silva spaces are Hausdorff** ([GN26, Proposition B.13.13(b)]), as soon as the steps
are `T₁`. -/
theorem IsSilva.t2Space [∀ n, T1Space (S n)] (hS : IsSilva S) : T2Space (LCDirectLimit S) := by
  refine IsTopologicalAddGroup.t2Space_iff_zero_closed.2 ⟨hS.isOpen_iff.2 fun n ↦ ?_⟩
  rw [preimage_compl]
  exact ((subsingleton_singleton.preimage (f := incl S n) Subtype.val_injective).isClosed
    ).isOpen_compl

/-- **A `k_ω`-type criterion for closed sets** (compare [GN26, Proposition B.13.13(f)–(g)]):
if the steps are sequential spaces and `L p ⊆ S (p + 1)` are sets whose preimages are
`0`-neighbourhoods of `S p` (for instance compact sets witnessing the compactness of the
inclusions), a set `F` is closed in the direct limit as soon as its intersections with all the
sets `k L p`, `k ∈ ℕ`, are closed. -/
theorem IsSilva.isClosed_of_isClosed_inter [∀ n, SequentialSpace (S n)] (hS : IsSilva S)
    (L : ∀ p, Set (S (p + 1)))
    (hL : ∀ p, Submodule.inclusion (hS.mono (Nat.le_succ p)) ⁻¹' L p ∈ 𝓝 0)
    {F : Set (LCDirectLimit S)}
    (hF : ∀ p (k : ℕ), IsClosed (F ∩ incl S (p + 1) '' ((k : ℝ) • L p))) : IsClosed F := by
  rw [← isOpen_compl_iff, hS.isOpen_iff]
  intro p
  rw [preimage_compl, isOpen_compl_iff]
  refine IsSeqClosed.isClosed fun {x y} hx hxy ↦ ?_
  set ι := Submodule.inclusion (hS.mono (Nat.le_succ p))
  -- the convergent sequence lies in a multiple of `ι⁻¹(L p)`
  obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hxy.isCompact_insert_range.isVonNBounded ℝ (hL p))
  set k : ℕ := ⌈r⌉₊ + 1
  have hk : r ≤ ‖(k : ℝ)‖ := by
    rw [Real.norm_natCast]
    exact (Nat.le_ceil r).trans (by exact_mod_cast Nat.le_succ _)
  have hC : ∀ z ∈ insert y (range x), incl S p z ∈ incl S (p + 1) '' ((k : ℝ) • L p) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hr _ hk hz
    exact ⟨(k : ℝ) • ι w, smul_mem_smul_set hw, by simp [ι]⟩
  have hlim : Tendsto (fun j ↦ incl S p (x j)) atTop (𝓝 (incl S p y)) :=
    ((continuous_incl S p).tendsto y).comp hxy
  exact ((hF p k).mem_of_tendsto hlim (Eventually.of_forall fun j ↦
    ⟨hx j, hC _ (mem_insert_of_mem _ (mem_range_self j))⟩)).1

/-- **Silva spaces are compactly regular** ([GN26, Definition A.7.5 and Proposition B.13.13(b)]),
for `T₁` sequential steps (for instance Banach spaces): every compact subset of the limit is
contained, and compact, in some step. We argue directly: the compact sets `k L p` (with `L p`
witnessing the compactness of
`S p → S (p + 1)`) cover the limit and detect closed sets (`isClosed_of_isClosed_inter`), so a
compact set meeting infinitely many of their finite unions `D N` would contain an infinite closed
discrete set. -/
theorem IsSilva.exists_subset_isCompact [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    (hS : IsSilva S) {K : Set (LCDirectLimit S)} (hK : IsCompact K) :
    ∃ n, (∀ x ∈ K, x ∈ S n) ∧ IsCompact (incl S n ⁻¹' K) := by
  have : T2Space (LCDirectLimit S) := hS.t2Space
  choose L hL hLn using hS.isCompactOperator_succ
  -- the compact pieces `C p k = k L p` and their finite unions `D N`
  set C : ℕ → ℕ → Set (LCDirectLimit S) := fun p k ↦ incl S (p + 1) '' ((k : ℝ) • L p)
  set D : ℕ → Set (LCDirectLimit S) := fun N ↦ ⋃ p ∈ Iic N, ⋃ k ∈ Iic N, C p k
  have hCD : ∀ p k N, p ≤ N → k ≤ N → C p k ⊆ D N := fun p k N hp hk ↦
    (subset_biUnion_of_mem (u := C p) (mem_Iic.2 hk)).trans
      (subset_biUnion_of_mem (u := fun p ↦ ⋃ k ∈ Iic N, C p k) (mem_Iic.2 hp))
  have hDmono : Monotone D := fun N N' h x hx ↦ by
    obtain ⟨p, hp, k, hk, hx⟩ : ∃ p ∈ Iic N, ∃ k ∈ Iic N, x ∈ C p k := by
      simpa only [D, mem_iUnion, exists_prop] using hx
    exact hCD p k N' ((mem_Iic.1 hp).trans h) ((mem_Iic.1 hk).trans h) hx
  have hcover : ∀ v : LCDirectLimit S, ∃ N, v ∈ D N := by
    intro v
    obtain ⟨p, hp⟩ := hS.exists_mem v
    obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (absorbent_nhds_zero (𝕜 := ℝ) (hLn p) ⟨v, hp⟩)
    set k : ℕ := ⌈r⌉₊ + 1
    have hk : r ≤ ‖(k : ℝ)‖ := by
      rw [Real.norm_natCast]
      exact (Nat.le_ceil r).trans (by exact_mod_cast Nat.le_succ _)
    obtain ⟨w, hw, hwv⟩ := hr _ hk (mem_singleton _)
    refine ⟨max p k, hCD p k _ (le_max_left _ _) (le_max_right _ _)
      ⟨(k : ℝ) • Submodule.inclusion (hS.mono (Nat.le_succ p)) w, smul_mem_smul_set hw, ?_⟩⟩
    exact congrArg Subtype.val hwv
  -- `K` lies in some `D N`
  obtain ⟨N, hN⟩ : ∃ N, K ⊆ D N := by
    by_contra hcon
    push Not at hcon
    choose x hxK hxD using fun N ↦ not_subset.1 (hcon N)
    -- every subset of `range x` is closed
    have hclosed : ∀ T ⊆ range x, IsClosed T := by
      intro T hT
      refine hS.isClosed_of_isClosed_inter L hLn fun p k ↦ ?_
      refine Set.Finite.isClosed (((finite_Iio (max p k)).image x).subset ?_)
      rintro z ⟨hzT, hzC⟩
      obtain ⟨M, rfl⟩ := hT hzT
      exact ⟨M, mem_Iio.2 (lt_of_not_ge fun hM ↦ hxD M (hCD p k M
        ((le_max_left _ _).trans hM) ((le_max_right _ _).trans hM) hzC)), rfl⟩
    -- so `range x` is compact and discrete, hence finite
    have hfin : (range x).Finite := by
      refine (hK.of_isClosed_subset (hclosed _ subset_rfl) (range_subset_iff.2 hxK)).finite
        (isDiscrete_iff_forall_mem_exists_isOpen.2 fun y hy ↦
          ⟨(range x \ {y})ᶜ, (hclosed _ sdiff_subset).isOpen_compl, ?_⟩)
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        by_contra hne
        exact h1 ⟨h2, hne⟩
      · rintro rfl
        exact ⟨fun h ↦ h.2 rfl, hy⟩
    -- but each value of `x` lies in some `D M`, which `x M` avoids
    obtain ⟨M, hM⟩ := (hfin.image fun z ↦ (hcover z).choose).bddAbove
    exact hxD M (hDmono (hM ⟨x M, mem_range_self M, rfl⟩) (hcover (x M)).choose_spec)
  -- `D N ⊆ S (N + 1)`, and `K` is compact there
  have hinj : Injective (incl S (N + 1)) := Subtype.val_injective
  have hCpre : ∀ p ∈ Iic N, ∀ k ∈ Iic N, IsCompact (incl S (N + 1) ⁻¹' C p k) := by
    intro p hp k _
    set g := Submodule.inclusion (hS.mono (Nat.succ_le_succ (mem_Iic.1 hp)))
    have : C p k = incl S (N + 1) '' (g '' ((k : ℝ) • L p)) := by
      rw [← image_comp]
      rfl
    rw [this, hinj.preimage_image]
    exact ((hL p).smul _).image (hS.continuous_inclusion (Nat.succ_le_succ (mem_Iic.1 hp)))
  refine ⟨N + 1, fun x hx ↦ ?_, ?_⟩
  · obtain ⟨p, hp, k, -, y, -, rfl⟩ : ∃ p ∈ Iic N, ∃ k ∈ Iic N, x ∈ C p k := by
      simpa only [D, mem_iUnion, exists_prop] using hN hx
    exact hS.mono (Nat.succ_le_succ (mem_Iic.1 hp)) y.2
  · have hDc : IsCompact (incl S (N + 1) ⁻¹' D N) := by
      simp only [D, preimage_iUnion]
      exact (finite_Iic N).isCompact_biUnion fun p hp ↦
        (finite_Iic N).isCompact_biUnion fun k hk ↦ hCpre p hp k hk
    exact hDc.of_isClosed_subset (hK.isClosed.preimage (continuous_incl S (N + 1)))
      (preimage_mono hN)


/-- **Silva spaces are boundedly regular** ([GN26, Definition B.13.7 and Proposition B.13.13(c)]),
for `T₁` sequential steps with bounded `0`-neighbourhoods (for instance Banach spaces): every
bounded subset of the limit is contained, and bounded, in some step. The argument is that of
Glöckner–Neeb, with an increasing sequence of bounded `0`-neighbourhoods `N p` of the steps in place
of the normalized unit balls. -/
theorem IsSilva.exists_subset_isVonNBounded [∀ n, T1Space (S n)] [∀ n, SequentialSpace (S n)]
    (hS : IsSilva S) (hbdd : ∀ n, ∃ U ∈ 𝓝 (0 : S n), IsVonNBounded ℝ U)
    {B : Set (LCDirectLimit S)} (hB : IsVonNBounded ℝ B) :
    ∃ n, (∀ x ∈ B, x ∈ S n) ∧ IsVonNBounded ℝ (incl S n ⁻¹' B) := by
  have hε : Tendsto (fun q : ℕ ↦ 1 / ((q : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- `B` lies in some step
  obtain ⟨n, hn⟩ : ∃ n, ∀ x ∈ B, x ∈ S n := by
    by_contra hcon
    push Not at hcon
    choose x hxB hxS using hcon
    have ht : Tendsto (fun q : ℕ ↦ (1 / ((q : ℝ) + 1)) • x q) atTop (𝓝 0) :=
      hB.smul_tendsto_zero (Eventually.of_forall hxB) hε
    obtain ⟨m, hm, -⟩ := hS.exists_subset_isCompact ht.isCompact_insert_range
    apply hxS m
    have h2 := (S m).smul_mem ((m : ℝ) + 1) (hm _ (mem_insert_of_mem _ (mem_range_self m)))
    have h3 : ((m : ℝ) + 1) • ((1 / ((m : ℝ) + 1)) • x m) = x m := by
      rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]
    rw [← h3]
    exact h2
  -- an increasing sequence of bounded `0`-neighbourhoods
  choose U hU hUb using hbdd
  have hnext : ∀ p (N : Set (S p)), N ∈ 𝓝 0 ∧ IsVonNBounded ℝ N →
      Submodule.inclusion (hS.mono (Nat.le_succ p)) '' N + U (p + 1) ∈ 𝓝 0 ∧
        IsVonNBounded ℝ (Submodule.inclusion (hS.mono (Nat.le_succ p)) '' N + U (p + 1)) := by
    intro p N hN
    refine ⟨mem_of_superset (hU (p + 1)) fun u hu ↦
      ⟨0, ⟨0, mem_of_mem_nhds hN.1, map_zero _⟩, u, hu, zero_add u⟩, ?_⟩
    exact (hN.2.image (⟨Submodule.inclusion (hS.mono (Nat.le_succ p)),
      hS.continuous_inclusion (Nat.le_succ p)⟩ : S p →L[ℝ] S (p + 1))).add (hUb (p + 1))
  let Nseq : ∀ p, {N : Set (S p) // N ∈ 𝓝 0 ∧ IsVonNBounded ℝ N} := fun p ↦
    Nat.rec (motive := fun p ↦ {N : Set (S p) // N ∈ 𝓝 0 ∧ IsVonNBounded ℝ N})
      ⟨U 0, hU 0, hUb 0⟩ (fun p N ↦ ⟨_, hnext p N.1 N.2⟩) p
  have hNsucc : ∀ p, incl S p '' (Nseq p).1 ⊆ incl S (p + 1) '' (Nseq (p + 1)).1 := by
    rintro p _ ⟨z, hz, rfl⟩
    exact ⟨Submodule.inclusion (hS.mono (Nat.le_succ p)) z + 0,
      ⟨_, ⟨z, hz, rfl⟩, 0, mem_of_mem_nhds (hU (p + 1)), rfl⟩, by rw [add_zero]; rfl⟩
  have hNmono : ∀ r q, r ≤ q → incl S r '' (Nseq r).1 ⊆ incl S q '' (Nseq q).1 := by
    intro r q hrq
    induction q, hrq using Nat.le_induction with
    | base => exact subset_rfl
    | succ q _ ih => exact ih.trans (hNsucc q)
  by_contra hcon
  push Not at hcon
  -- `B` is not absorbed by the `N p`, `p ≥ n`
  have hna : ∀ q, ∃ x ∈ B, ∀ hx : x ∈ S (n + q),
      (⟨x, hx⟩ : S (n + q)) ∉ (((q : ℝ) + 1) ^ 2) • (Nseq (n + q)).1 := by
    intro q
    by_contra h
    push Not at h
    refine hcon (n + q) (fun x hx ↦ hS.mono (Nat.le_add_right n q) (hn x hx)) ?_
    have hb : IsVonNBounded ℝ ((((q : ℝ) + 1) ^ 2) • (Nseq (n + q)).1) := by
      have := (Nseq (n + q)).2.2.image ((((q : ℝ) + 1) ^ 2) • ContinuousLinearMap.id ℝ (S (n + q)))
      simpa [image_smul] using this
    refine hb.subset fun y hy ↦ ?_
    obtain ⟨hx, hxN⟩ := h _ hy
    exact hxN
  choose x hxB hxN using hna
  have ht : Tendsto (fun q : ℕ ↦ (1 / ((q : ℝ) + 1)) • x q) atTop (𝓝 0) :=
    hB.smul_tendsto_zero (Eventually.of_forall hxB) hε
  obtain ⟨r, hr, hrc⟩ := hS.exists_subset_isCompact ht.isCompact_insert_range
  obtain ⟨R, hR⟩ := absorbs_iff_norm.1 (hrc.isVonNBounded ℝ (Nseq r).2.1)
  set q := max r ⌈R⌉₊
  have hq : R ≤ ‖(q : ℝ) + 1‖ := by
    rw [Real.norm_of_nonneg (by positivity)]
    have : (⌈R⌉₊ : ℝ) ≤ q := by exact_mod_cast le_max_right _ _
    linarith [Nat.le_ceil R]
  have hyq : (1 / ((q : ℝ) + 1)) • x q ∈ S r := hr _ (mem_insert_of_mem _ (mem_range_self q))
  obtain ⟨z, hz, hzy⟩ := hR _ hq (show (⟨_, hyq⟩ : S r) ∈ incl S r ⁻¹' _ from
    mem_insert_of_mem _ (mem_range_self q))
  obtain ⟨z', hz', hz'z⟩ := hNmono r (n + q) ((le_max_left _ _).trans (Nat.le_add_left _ _))
    ⟨z, hz, rfl⟩
  have hxq : x q ∈ S (n + q) := hS.mono (Nat.le_add_right n q) (hn _ (hxB q))
  refine hxN q hxq ⟨z', hz', Subtype.ext ?_⟩
  have h1 : (z' : V) = (z : V) := hz'z
  have h2 : ((q : ℝ) + 1) • (z : V) = (1 / ((q : ℝ) + 1)) • x q := congrArg Subtype.val hzy
  have e1 : (((q : ℝ) + 1) ^ 2) • (z' : V) = ((q : ℝ) + 1) • (((q : ℝ) + 1) • (z : V)) := by
    rw [h1, pow_two, mul_smul]
  have e2 : ((q : ℝ) + 1) • ((1 / ((q : ℝ) + 1)) • x q) = x q := by
    rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]
  exact e1.trans ((congrArg (((q : ℝ) + 1) • ·) h2).trans e2)

/-- **Bounded subsets of Silva spaces are relatively compact** ([GN26, Proposition B.13.13(d)]),
under the hypotheses of `exists_subset_isVonNBounded`. -/
theorem IsSilva.isCompact_closure_of_isVonNBounded [∀ n, T1Space (S n)]
    [∀ n, SequentialSpace (S n)] (hS : IsSilva S)
    (hbdd : ∀ n, ∃ U ∈ 𝓝 (0 : S n), IsVonNBounded ℝ U) {B : Set (LCDirectLimit S)}
    (hB : IsVonNBounded ℝ B) : IsCompact (closure B) := by
  have : T2Space (LCDirectLimit S) := hS.t2Space
  obtain ⟨p, hp, hpb⟩ := hS.exists_subset_isVonNBounded hbdd hB
  obtain ⟨L, hL, hLn⟩ := hS.isCompactOperator_succ p
  obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hpb hLn)
  set c : ℝ := max r 0
  have hc : r ≤ ‖c‖ := by
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact le_max_left _ _
  have hBK : B ⊆ incl S (p + 1) '' (c • L) := fun y hy ↦ by
    obtain ⟨w, hw, hwy⟩ := hr c hc (show (⟨y, hp y hy⟩ : S p) ∈ incl S p ⁻¹' B from hy)
    exact ⟨c • Submodule.inclusion (hS.mono (Nat.le_succ p)) w, smul_mem_smul_set hw,
      congrArg Subtype.val hwy⟩
  have hK : IsCompact (incl S (p + 1) '' (c • L)) := (hL.smul c).image (continuous_incl S _)
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hBK hK.isClosed)

/-- **`C^k` maps on Silva spaces**, for subspaces ([GN26, Proposition 2.7.1]): a map on an
open subset `U` of a Silva space is `C^k` as soon as its restrictions to the steps are. -/
theorem IsSilva.contDiffMBOn_of_comp [∀ n, T2Space (S n)]
    (hS : IsSilva S) {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [T2Space F] {U : Set (LCDirectLimit S)}
    (hU : IsOpen U) {f : LCDirectLimit S → F} {k : ℕ}
    (hf : ∀ n, ContDiffMBOn k (f ∘ incl S n) (incl S n ⁻¹' U)) : ContDiffMBOn k f U :=
  IsSilvaSystem.contDiffMBOn_of_comp k hS.isSilvaSystem hU hf

/-- **`C^k` maps on Silva spaces** ([GN26, Proposition 2.7.1], as stated there): if
`U₀ ⊆ U₁ ⊆ ⋯` are open subsets of the steps, their union `U` is open in the Silva space, and a map
`f` on `U` is `C^k` as soon as its restrictions to the `Uₙ` are. -/
theorem IsSilva.contDiffMBOn_iUnion [∀ n, T2Space (S n)] (hS : IsSilva S) {F : Type*}
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T2Space F] {Uₙ : ∀ n, Set (S n)}
    (hUo : ∀ n, IsOpen (Uₙ n)) (hUm : Monotone fun n ↦ incl S n '' Uₙ n)
    {f : LCDirectLimit S → F} {k : ℕ} (hf : ∀ n, ContDiffMBOn k (f ∘ incl S n) (Uₙ n)) :
    IsOpen (⋃ n, incl S n '' Uₙ n) ∧ ContDiffMBOn k f (⋃ n, incl S n '' Uₙ n) := by
  set U := ⋃ n, incl S n '' Uₙ n
  -- a point of `S m` lies in `U` iff it lies in some later `Uₚ`
  have hmem : ∀ m (y : S m), incl S m y ∈ U ↔
      ∃ p, ∃ hp : m ≤ p, Submodule.inclusion (hS.mono hp) y ∈ Uₙ p := by
    intro m y
    refine ⟨fun hy ↦ ?_, fun ⟨p, hp, hy⟩ ↦ mem_iUnion.2 ⟨p, _, hy, rfl⟩⟩
    obtain ⟨n, z, hz, hzy⟩ := mem_iUnion.1 hy
    obtain ⟨z', hz', hz'z⟩ := hUm (le_max_right m n) ⟨z, hz, hzy⟩
    exact ⟨max m n, le_max_left _ _, by rwa [show Submodule.inclusion _ y = z' from
      Subtype.ext hz'z.symm]⟩
  have hpre : ∀ m, incl S m ⁻¹' U =
      ⋃ p, ⋃ hp : m ≤ p, Submodule.inclusion (hS.mono hp) ⁻¹' Uₙ p := fun m ↦ by
    ext y
    simp only [mem_preimage, mem_iUnion]
    exact hmem m y
  have hU : IsOpen U := hS.isOpen_iff.2 fun m ↦ by
    rw [hpre]
    exact isOpen_iUnion fun p ↦ isOpen_iUnion fun hp ↦
      (hUo p).preimage (hS.continuous_inclusion hp)
  refine ⟨hU, hS.contDiffMBOn_of_comp hU fun m ↦ ?_⟩
  refine ContDiffMBOn.of_local (hU.preimage (continuous_incl S m)) fun y hy ↦ ?_
  obtain ⟨p, hp, hyp⟩ := (hmem m y).1 hy
  set L : S m →L[ℝ] S p := ⟨Submodule.inclusion (hS.mono hp), hS.continuous_inclusion hp⟩
  exact ⟨L ⁻¹' Uₙ p, (hUo p).preimage L.continuous, hyp,
    ((hf p).comp_clm L (hUo p)).mono inter_subset_right⟩

end Silva

end LCDirectLimit

end LocallyConvex.Analysis

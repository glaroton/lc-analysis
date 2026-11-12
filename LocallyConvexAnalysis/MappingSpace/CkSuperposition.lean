/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.MappingSpace.SmoothTopology
public import LocallyConvexAnalysis.MappingSpace.Pushforward

/-!
# Superposition operators and restrictions on spaces of `C^r` maps

Let `Z`, `E`, `F` be Hausdorff locally convex spaces, `Z` locally compact, `U ⊆ Z` open and
`r ∈ ℕ`. The space `C^r(U, E)` carries the compact-open `C^r` topology ([GN26, Definition 1.7.10];
`ContDiffMBMap` in
`LocallyConvexAnalysis.MappingSpace.CkTopology`). This file proves the two facts about these spaces
that the manifolds of `C^ℓ` maps need (`LocallyConvexManifolds.MappingSpaceCk` in lc-manifolds).

## Main results

* `ContDiffMBMap.contDiffMBOn_compLeftOn`: **superposition operators are smooth**. For `h : E → F`
  smooth on an open set `O`, the operator `γ ↦ h ∘ γ` on the `γ ∈ C^r(U, E)` with `γ(U) ⊆ O` is
  `C^k` along `C^k` maps: if `g : X → C^r(U, E)` is `C^k` on an open set `W` and `g(w)(U) ⊆ O` for
  `w ∈ W`, then `w ↦ h ∘ g(w)` is `C^k` on `W`.
* `ContDiffMBMap.isEmbedding_restrictCover`, `ContDiffMBMap.isClosed_range_restrictCover`: for an
  open cover `(V_a)` of `U`, the restrictions `C^r(U, F) → ∏_a C^r(V_a, F)` form a linear
  topological embedding with closed range (compare [GN26, Lemma 1.7.43], and Lemma 4.1.9 for
  manifolds); hence `ContDiffMBMap.contDiffMBOn_of_restrictCLM` and
  `ContDiffMBMap.tendsto_of_tendsto_restrictCLM`: being `C^k`, or converging, in `C^r(U, F)` is a
  local property.
* `isEmbedding_restrictCompacts`, `isClosed_range_restrictCompacts`: on a locally compact space
  `Y`, the restrictions `C(Y, F) → ∏_C C(C, F)` to the compact subsets form a closed embedding.
* `isEmbedding_restrictPieces`, `isClosed_range_restrictPieces`: the same for the restrictions
  `C(L, G) → ∏_b C(L_b, G)` to the pieces of a finite cover of `L` by compact sets.
* `contDiffMBOn_pi`, `contDiffMBOn_of_isClosedEmbedding`: `C^k` maps into a product are the maps
  with `C^k` components, and a map into a closed subspace is `C^k` as soon as it is `C^k` into
  the ambient space.

## Implementation notes

* **Smoothness of superposition operators.** Glöckner–Neeb obtain the smoothness of the maps
  between spaces of `C^ℓ` maps that they need from the exponential law (their Proposition 4.1.34,
  via Theorem 1.7.30). Here `contDiffMBOn_compLeftOn` is proved by induction on `r`, as the
  continuity of superposition operators (`ContDiffMBMap.continuous_compGraph`,
  [GN26, Proposition 1.7.12]). The topology of `C^{r+1}(U, F)` is initial with respect to the
  differentials `d^(j)`, and `C^{r+1}(U, F)` is a closed subspace of `∏_j C(U × Z^j, F)`
  (Lemma 1.7.15), so it suffices to treat each `d^(j)`. For `j = 0` the restrictions to the compact
  subsets of `U` reduce the question to superposition operators on `C(C, E)` with `C` compact,
  smooth by [GN26, Proposition 1.7.1] (`smoothMBOn_pushforward`). For `j ≥ 1`,
  `d^(j)(h ∘ γ)` is obtained continuously and linearly from `d(h ∘ γ) = dh ∘ (γ ∘ pr₁, dγ)`, the
  superposition by the smooth map `dh` of an element of `C^r(U × Z, E × E)` depending continuously
  and linearly on `γ`, and the induction hypothesis applies on `U × Z`. This is where `Z` must be
  locally compact (for `j = 0`, through `isClosed_range_restrictCompacts`). We do not claim this
  argument is new.
* The operator is stated along `C^k` maps `g` rather than on an open subset of `C^r(U, E)`: the set
  `{γ : γ(U) ⊆ O}` is not open when `U` is not relatively compact, and the induction passes from
  `U` to `U × Z`, which never is.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function TopologicalSpace
open scoped Topology
open LocallyConvex.Analysis

noncomputable section

namespace LocallyConvex.Analysis

universe u

/-! ### Maps into products and closed subspaces -/

section Calculus

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T2Space V]

/-- **`C^k` maps into a product** are the maps whose components are `C^k`. -/
theorem contDiffMBOn_pi {ι : Type*} {Y : ι → Type*} [∀ a, AddCommGroup (Y a)]
    [∀ a, Module ℝ (Y a)] [∀ a, TopologicalSpace (Y a)] [∀ a, T2Space (Y a)]
    {k : ℕ} {F : V → ∀ a, Y a} {W : Set V} (hW : IsOpen W)
    (h : ∀ a, ContDiffMBOn k (fun x ↦ F x a) W) : ContDiffMBOn k F W := by
  induction k generalizing V with
  | zero => exact continuousOn_pi.2 h
  | succ k ih =>
    have hd : ∀ x ∈ W, ∀ v, HasDirDerivAt F x v (fun a ↦ dMB (fun x ↦ F x a) (x, v)) := by
      intro x hx v
      exact tendsto_pi_nhds.2 fun a ↦ (h a).2.1 x hx v
    have hdeq : ∀ p ∈ W ×ˢ (univ : Set V), dMB F p = fun a ↦ dMB (fun x ↦ F x a) p :=
      fun p hp ↦ (hd p.1 hp.1 p.2).dMB_eq
    refine ⟨continuousOn_pi.2 fun a ↦ (h a).continuousOn, fun x hx v ↦ ?_, ?_⟩
    · rw [hdeq (x, v) ⟨hx, mem_univ v⟩]
      exact hd x hx v
    · refine ContDiffMBOn.congr_of_isOpen (hW.prod isOpen_univ) (fun p hp ↦ (hdeq p hp).symm) ?_
      exact ih (hW.prod isOpen_univ) fun a ↦ (h a).2.2

/-- **`C^k` maps into a closed subspace**: if `ι : X → Y` is a continuous linear topological
embedding with closed range and `ι ∘ h` is `C^k`, then `h` is `C^k`. -/
theorem contDiffMBOn_of_isClosedEmbedding {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X]
    [T2Space X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [T2Space Y] (ι : X →L[ℝ] Y)
    (hι : Topology.IsEmbedding ι) (hcl : IsClosed (range ι)) {k : ℕ} {h : V → X} {W : Set V}
    (hW : IsOpen W) (hh : ContDiffMBOn k (fun x ↦ ι (h x)) W) : ContDiffMBOn k h W := by
  induction k generalizing V with
  | zero => exact hι.isInducing.continuousOn_iff.2 hh
  | succ k ih =>
    have hmem : ∀ x ∈ W, ∀ v, dMB (fun x ↦ ι (h x)) (x, v) ∈ range ι := by
      intro x hx v
      refine hcl.mem_of_tendsto (hh.2.1 x hx v) (Eventually.of_forall fun t ↦ ?_)
      exact ⟨t⁻¹ • (h (x + t • v) - h x), by simp⟩
    choose! D hD using hmem
    have hd : ∀ x ∈ W, ∀ v, HasDirDerivAt h x v (D x v) := by
      intro x hx v
      rw [HasDirDerivAt, hι.tendsto_nhds_iff, hD x hx v]
      refine (hh.2.1 x hx v).congr fun t ↦ ?_
      simp
    have hdeq : ∀ p ∈ W ×ˢ (univ : Set V), ι (dMB h p) = dMB (fun x ↦ ι (h x)) p := fun p hp ↦ by
      rw [(hd p.1 hp.1 p.2).dMB_eq]
      exact hD p.1 hp.1 p.2
    refine ⟨hι.isInducing.continuousOn_iff.2 hh.continuousOn, fun x hx v ↦ ?_, ?_⟩
    · rw [(hd x hx v).dMB_eq]
      exact hd x hx v
    · exact ih (hW.prod isOpen_univ) (ContDiffMBOn.congr_of_isOpen (hW.prod isOpen_univ)
        (fun p hp ↦ (hdeq p hp).symm) hh.2.2)

end Calculus

/-! ### Restriction to a finite cover by compact sets -/

section Pieces

variable {X : Type*} [TopologicalSpace X] [T2Space X] {ι : Type*} [Finite ι] {L : Set X}
  {Lb : ι → Set X} (hsub : ∀ b, Lb b ⊆ L) (hcpt : ∀ b, IsCompact (Lb b))
  {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G]

/-- The inclusion of a piece. -/
def pieceIncl (b : ι) : C(Lb b, L) := ⟨Set.inclusion (hsub b), continuous_inclusion (hsub b)⟩

omit [Module ℝ G] [ContinuousSMul ℝ G] in
include hcpt in
/-- A map into `C(L, G)` is continuous if its restrictions to the pieces of a finite cover of
`L` by compact sets are. -/
theorem continuous_of_continuous_restrict_pieces (hcov : L ⊆ ⋃ b, Lb b) {P : Type*}
    [tP : TopologicalSpace P] {ψ : P → C(L, G)}
    (h : ∀ b, Continuous fun p ↦ (ψ p).comp (pieceIncl hsub b)) : Continuous ψ := by
  refine ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun K' _ ↦ ?_
  have hlf : LocallyFinite fun b ↦ {q : P × K' | ((q.2 : L) : X) ∈ Lb b} :=
    locallyFinite_of_finite _
  refine hlf.continuous ?_ (fun b ↦ (hcpt b).isClosed.preimage
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))) fun b ↦ ?_
  · ext q
    simpa using hcov (q.2 : L).2
  · have : CompactSpace (Lb b) := isCompact_iff_compactSpace.mp (hcpt b)
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun q : {q : P × K' | ((q.2 : L) : X) ∈ Lb b} ↦
        ((ψ q.1.1).comp (pieceIncl hsub b), (⟨((q.1.2 : L) : X), q.2⟩ : Lb b)) :=
      ((h b).comp (continuous_fst.comp continuous_subtype_val)).prodMk
        ((continuous_subtype_val.comp (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))).subtype_mk _)
    exact (continuous_eval.comp hc).congr fun q ↦ rfl

/-- The restriction `C(L, G) → ∏_b C(L_b, G)` to the pieces of a finite cover. -/
def restrictPieces : C(L, G) →L[ℝ] ∀ b, C(Lb b, G) where
  toFun φ b := φ.comp (pieceIncl hsub b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun _ ↦ ContinuousMap.continuous_precomp _

omit [T2Space X] [Finite ι] in
/-- Continuity of the pieces of a map into `C(L, G)` whose restriction is continuous. -/
theorem continuous_piece_of_continuous_restrictPieces {P : Type*} [tP : TopologicalSpace P]
    {ψ : P → C(L, G)} (h : Continuous fun p ↦ restrictPieces hsub (ψ p)) (b : ι) :
    Continuous fun p ↦ (ψ p).comp (pieceIncl hsub b) :=
  (continuous_apply b).comp h

include hcpt in
/-- The restriction to the pieces of a finite cover by compact sets is a topological
embedding. -/
theorem isEmbedding_restrictPieces (hcov : L ⊆ ⋃ b, Lb b) :
    Topology.IsEmbedding (restrictPieces (G := G) hsub) := by
  refine ⟨(Topology.isInducing_iff _).2 (le_antisymm
    (continuous_iff_le_induced.1 (restrictPieces hsub).continuous) ?_), fun φ ψ hφψ ↦ ?_⟩
  · have h := continuous_of_continuous_restrict_pieces hsub hcpt hcov (P := C(L, G))
      (tP := TopologicalSpace.induced (restrictPieces (G := G) hsub) inferInstance) (ψ := id)
      (continuous_piece_of_continuous_restrictPieces hsub (P := C(L, G))
        (tP := TopologicalSpace.induced (restrictPieces (G := G) hsub) inferInstance) (ψ := id)
        continuous_induced_dom)
    simpa [induced_id] using continuous_iff_le_induced.1 h
  · ext y
    obtain ⟨b, hb⟩ := mem_iUnion.1 (hcov y.2)
    exact congrArg (fun χ ↦ χ b ⟨y, hb⟩) hφψ

include hcpt in
/-- The restriction to the pieces of a finite cover by compact sets has closed range. -/
theorem isClosed_range_restrictPieces [T2Space G] (hcov : L ⊆ ⋃ b, Lb b) :
    IsClosed (range (restrictPieces (G := G) hsub)) := by
  let S : Set (∀ b, C(Lb b, G)) := {χ | ∀ (b c : ι) (y : X) (hb : y ∈ Lb b) (hc : y ∈ Lb c),
    χ b ⟨y, hb⟩ = χ c ⟨y, hc⟩}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun b ↦ isClosed_iInter fun c ↦ isClosed_iInter fun y ↦
      isClosed_iInter fun hb ↦ isClosed_iInter fun hc ↦ isClosed_eq
        ((continuous_eval_const _).comp (continuous_apply b))
        ((continuous_eval_const _).comp (continuous_apply c))
  convert hS using 1
  ext χ
  constructor
  · rintro ⟨φ, rfl⟩ _ _ y hb hc
    rfl
  · intro hχ
    have hb : ∀ y : L, ∃ b, (y : X) ∈ Lb b := fun y ↦ mem_iUnion.1 (hcov y.2)
    choose β hβ using hb
    let φ : L → G := fun y ↦ χ (β y) ⟨y, hβ y⟩
    have hlf : LocallyFinite fun b ↦ {y : L | (y : X) ∈ Lb b} := locallyFinite_of_finite _
    have hφ : Continuous φ := by
      refine hlf.continuous ?_ (fun b ↦ (hcpt b).isClosed.preimage continuous_subtype_val)
        fun b ↦ ?_
      · ext y; simpa using ⟨β y, hβ y⟩
      · rw [continuousOn_iff_continuous_domRestrict]
        have hc : Continuous fun y : {y : L | (y : X) ∈ Lb b} ↦ χ b ⟨y.1.1, y.2⟩ :=
          (χ b).continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
        exact hc.congr fun y ↦ hχ b (β y) y y.2 (hβ y)
    refine ⟨⟨φ, hφ⟩, funext fun b ↦ ContinuousMap.ext fun y ↦ ?_⟩
    exact hχ (β _) b y (hβ _) y.2

end Pieces

/-! ### Continuous maps on a locally compact space and their restrictions to compact sets -/

section RestrictCompacts

variable {Y : Type u} [TopologicalSpace Y]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

variable (Y F) in
/-- The restrictions `C(Y, F) → ∏_C C(C, F)` to all compact subsets `C` of `Y`. -/
def restrictCompacts : C(Y, F) →L[ℝ] ∀ C : {C : Set Y // IsCompact C}, C(C.1, F) where
  toFun φ C := φ.restrict C.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_pi fun C ↦ ContinuousMap.continuous_restrict C.1

/-- `restrictCompacts Y F φ C = φ|_C`. -/
@[simp]
theorem restrictCompacts_apply (φ : C(Y, F)) (C : {C : Set Y // IsCompact C}) :
    restrictCompacts Y F φ C = φ.restrict C.1 :=
  rfl

/-- The compact-open topology is initial with respect to the restrictions to compact sets. -/
theorem isEmbedding_restrictCompacts : Topology.IsEmbedding (restrictCompacts Y F) := by
  refine ⟨⟨?_⟩, fun φ ψ h ↦ ?_⟩
  · change _ = TopologicalSpace.induced (restrictCompacts Y F)
      (⨅ C, TopologicalSpace.induced (fun χ ↦ χ C) inferInstance)
    rw [induced_iInf]
    simp only [induced_compose]
    have h := ContinuousMap.compactOpen_eq_iInf_induced (X := Y) (Y := F)
    rw [iInf_subtype'] at h
    exact h
  · ext y
    exact congrArg (fun χ ↦ χ ⟨{y}, isCompact_singleton⟩ ⟨y, rfl⟩) h

/-- On a locally compact space, the families of continuous maps on the compact sets that agree
on the intersections are the restrictions of continuous maps: `restrictCompacts` has closed
range. -/
theorem isClosed_range_restrictCompacts [LocallyCompactSpace Y] [T2Space F] :
    IsClosed (range (restrictCompacts Y F)) := by
  let S : Set (∀ C : {C : Set Y // IsCompact C}, C(C.1, F)) := {χ | ∀ (C D) (y : Y)
    (hC : y ∈ C.1) (hD : y ∈ D.1), χ C ⟨y, hC⟩ = χ D ⟨y, hD⟩}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun C ↦ isClosed_iInter fun D ↦ isClosed_iInter fun y ↦
      isClosed_iInter fun hC ↦ isClosed_iInter fun hD ↦ isClosed_eq
        ((continuous_eval_const _).comp (continuous_apply C))
        ((continuous_eval_const _).comp (continuous_apply D))
  convert hS using 1
  ext χ
  constructor
  · rintro ⟨φ, rfl⟩ C D y hC hD
    rfl
  · intro hχ
    let φ : Y → F := fun y ↦ χ ⟨{y}, isCompact_singleton⟩ ⟨y, rfl⟩
    have key : ∀ (C : {C : Set Y // IsCompact C}) (y : Y) (hy : y ∈ C.1), φ y = χ C ⟨y, hy⟩ :=
      fun C y hy ↦ hχ _ C y rfl hy
    have hφ : Continuous φ := by
      refine continuous_iff_continuousAt.2 fun y ↦ ?_
      obtain ⟨C, hC, hCy⟩ := exists_compact_mem_nhds y
      have hon : ContinuousOn φ C := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact (χ ⟨C, hC⟩).continuous.congr fun z ↦ (key ⟨C, hC⟩ z z.2).symm
      exact hon.continuousAt hCy
    refine ⟨⟨φ, hφ⟩, funext fun C ↦ ContinuousMap.ext fun y ↦ ?_⟩
    exact key C y y.2

end RestrictCompacts

/-! ### Two facts of calculus -/

section CalculusFacts

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X]
  {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [ContinuousSMul ℝ Y] [LocallyConvexSpace ℝ Y] [T2Space Y]
  {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

/-- Compositions of `C^k` maps with continuous linear maps are `C^k`. -/
theorem ContDiffMBOn.clm_comp' (L : Y →L[ℝ] G) {k : ℕ} {g : X → Y} {W : Set X} (hW : IsOpen W)
    (hg : ContDiffMBOn k g W) : ContDiffMBOn k (fun w ↦ L (g w)) W :=
  ContDiffMBOn.comp hW isOpen_univ (L.contDiffMBOn k univ) hg (mapsTo_univ _ _)

/-- Affine maps `w ↦ c + L w` are `C^k`. -/
theorem contDiffMBOn_const_add_clm (c : Y) (L : X →L[ℝ] Y) (k : ℕ) (W : Set X) :
    ContDiffMBOn k (fun w ↦ c + L w) W := by
  have h := ContDiffMBOn.add isOpen_univ (contDiffMBOn_const k c univ) (L.contDiffMBOn k univ)
  exact h.mono (subset_univ _)

end CalculusFacts

/-! ### Superposition operators on `C^r(U, E)` -/

end LocallyConvex.Analysis

namespace LocallyConvex.Analysis.ContDiffMBMap


section CompLeftOn

variable {Z : Type u} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
  [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z] [T2Space Z]
  {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable {r : ℕ} {U : Opens Z}

open scoped Classical in
/-- The superposition operator `γ ↦ h ∘ γ` on the maps `γ ∈ C^r(U, E)` with values in an open
set `O` on which `h` is `C^r` (and `0` elsewhere). -/
def compLeftOn (h : E → F) (O : Set E) (γ : ContDiffMBMap E r U) : ContDiffMBMap F r U :=
  if hγ : MapsTo γ U O ∧ IsOpen O ∧ ContDiffMBOn r h O then
    mk ((U : Set Z).indicator (h ∘ γ))
      (ContDiffMBOn.congr_of_isOpen U.isOpen (fun _ hx ↦ (indicator_of_mem hx _).symm)
        (ContDiffMBOn.comp U.isOpen hγ.2.1 hγ.2.2 γ.contDiffMBOn hγ.1))
      fun _ hx ↦ indicator_of_notMem hx _
  else 0

/-- `compLeftOn h O γ x = h (γ x)` for `x ∈ U`, if `γ(U) ⊆ O`. -/
theorem compLeftOn_apply {h : E → F} {O : Set E} (hO : IsOpen O) (hh : ContDiffMBOn r h O)
    {γ : ContDiffMBMap E r U} (hγ : MapsTo γ U O) {x : Z} (hx : x ∈ U) :
    compLeftOn h O γ x = h (γ x) := by
  rw [compLeftOn, dite_eq_left_of_eq_true (eq_true ⟨hγ, hO, hh⟩)]
  exact indicator_of_mem (show x ∈ (U : Set Z) from hx) _

/-- `γ ↦ (γ ∘ pr₁, dγ)`, `C^{r+1}(U, E) → C^r(U × Z, E × E)`, as a continuous linear map. -/
def graphDataCLM : ContDiffMBMap E (r + 1) U →L[ℝ] ContDiffMBMap (E × E) r (Opens.prodUniv U) :=
  prodMkCLM.comp (((compRightCLM (ContinuousLinearMap.fst ℝ Z Z)).comp
    (ofLECLM (Nat.le_succ r))).prod dCLM)

/-- `graphDataCLM γ (x, v) = (γ x, dγ(x, v))` for `x ∈ U`. -/
theorem graphDataCLM_apply (γ : ContDiffMBMap E (r + 1) U) {p : Z × Z} (hp : p.1 ∈ U) :
    graphDataCLM γ p = (γ p.1, dMB γ p) := by
  change (γ p.1, dMap γ p) = _
  rw [dMap_apply γ hp]

/-- The chain rule for `compLeftOn`: `d(h ∘ γ) = dh ∘ (γ ∘ pr₁, dγ)`. -/
theorem dMap_compLeftOn {h : E → F} {O : Set E} (hO : IsOpen O) (hh : ContDiffMBOn (r + 1) h O)
    {γ : ContDiffMBMap E (r + 1) U} (hγ : MapsTo γ U O) :
    dMap (compLeftOn h O γ) = compLeftOn (dMB h) (O ×ˢ univ) (graphDataCLM γ) := by
  have hγ' : MapsTo (graphDataCLM γ) (Opens.prodUniv U) (O ×ˢ univ) := fun p hp ↦ by
    rw [graphDataCLM_apply γ hp]
    exact ⟨hγ hp, mem_univ _⟩
  ext p
  by_cases hp : p.1 ∈ U
  · rw [dMap_apply _ hp, compLeftOn_apply (hO.prod isOpen_univ) hh.2.2 hγ'
      (show p ∈ Opens.prodUniv U from hp), graphDataCLM_apply γ hp]
    have hev : ⇑(compLeftOn h O γ) =ᶠ[𝓝 p.1] h ∘ γ :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hp) fun x hx ↦ by
        rw [Function.comp_apply]
        exact compLeftOn_apply hO hh hγ hx
    rw [show p = (p.1, p.2) from rfl, dMB_congr_of_eventuallyEq hev,
      ContDiffMBOn.dMB_comp hO (hh.of_le (by omega)) (γ.contDiffMBOn.of_le (by omega)) hγ hp]
  · rw [apply_of_notMem _ (show p ∉ Opens.prodUniv U from hp),
      apply_of_notMem _ (show p ∉ Opens.prodUniv U from hp)]

/-- `γ ↦ (d^(j)γ)_{j ≤ r}` as a continuous linear map. -/
def toPiCLM : ContDiffMBMap F r U →L[ℝ] ∀ j : Fin (r + 1), C(U × (Fin j → Z), F) :=
  ⟨toPi, continuous_toPi⟩

variable [LocallyCompactSpace Z]

/-- The `0`-th differential of a superposition `h ∘ g(w)` depends in a `C^k` way on `w` if `g`
does. -/
theorem contDiffMBOn_iteratedD_zero_compLeftOn {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X]
    [T2Space X] {h : E → F} {O : Set E} (hO : IsOpen O) (hh : SmoothMBOn h O) {k : ℕ}
    {g : X → ContDiffMBMap E r U} {W : Set X} (hW : IsOpen W) (hg : ContDiffMBOn k g W)
    (hgO : ∀ w ∈ W, MapsTo (g w) U O) :
    ContDiffMBOn k (fun w ↦ iteratedD 0 (Nat.zero_le r) (compLeftOn h O (g w))) W := by
  have : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  refine contDiffMBOn_of_isClosedEmbedding (restrictCompacts _ F) isEmbedding_restrictCompacts
    isClosed_range_restrictCompacts hW (contDiffMBOn_pi hW fun C ↦ ?_)
  have : CompactSpace C.1 := isCompact_iff_compactSpace.mp C.2
  let L : ContDiffMBMap E r U →L[ℝ] C(C.1, E) :=
    ((ContinuousLinearMap.proj C).comp (restrictCompacts _ E)).comp (iteratedDCLM 0 (Nat.zero_le r))
  have hL : ContDiffMBOn k (fun w ↦ L (g w)) W := ContDiffMBOn.clm_comp' L hW hg
  have hc := ContDiffMBOn.comp hW (isOpen_valuedIn hO) (contDiffMBOn_pushforward k hO (hh k)) hL
    fun w hw x ↦ hgO w hw x.1.1.2
  refine ContDiffMBOn.congr_of_isOpen hW (fun w hw ↦ ?_) hc
  ext x
  change pushforward C.1 h O (L (g w)) x = compLeftOn h O (g w) x.1.1
  rw [pushforward_apply (hh 0).continuousOn (fun x ↦ hgO w hw x.1.1.2),
    compLeftOn_apply hO (hh r) (hgO w hw) x.1.1.2]
  rfl

/-- **Superposition operators are smooth on `C^r(U, E)`**: for `h` smooth on an open set `O`, the
operator `γ ↦ h ∘ γ` on the `γ ∈ C^r(U, E)` with `γ(U) ⊆ O` is `C^k` along every `C^k` map: if
`g : X → C^r(U, E)` is `C^k` on the open set `W` and `g(w)(U) ⊆ O` for `w ∈ W`, then
`w ↦ h ∘ g(w)` is `C^k` on `W`. Here `Z` is locally compact (the case relevant for manifolds of
mappings, where `Z` is finite-dimensional). -/
theorem contDiffMBOn_compLeftOn : ∀ (r : ℕ) {Z E : Type u} [AddCommGroup Z] [Module ℝ Z]
    [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z]
    [T2Space Z] [LocallyCompactSpace Z] [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    {U : Opens Z} {h : E → F} {O : Set E}, IsOpen O → SmoothMBOn h O →
    ∀ {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
      [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X] {k : ℕ}
      {g : X → ContDiffMBMap E r U} {W : Set X}, IsOpen W → ContDiffMBOn k g W →
      (∀ w ∈ W, MapsTo (g w) U O) → ContDiffMBOn k (fun w ↦ compLeftOn h O (g w)) W := by
  intro r
  induction r with
  | zero =>
    intro Z E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U h O hO hh X _ _ _ _ _ _ _ k g W hW hg hgO
    refine contDiffMBOn_of_isClosedEmbedding toPiCLM isEmbedding_toPi isClosed_range_toPi hW
      (contDiffMBOn_pi hW fun j ↦ ?_)
    cases j using Fin.cases with
    | succ i => exact i.elim0
    | zero =>
    exact contDiffMBOn_iteratedD_zero_compLeftOn hO hh hW hg hgO
  | succ r ih =>
    intro Z E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ U h O hO hh X _ _ _ _ _ _ _ k g W hW hg hgO
    refine contDiffMBOn_of_isClosedEmbedding toPiCLM isEmbedding_toPi isClosed_range_toPi hW
      (contDiffMBOn_pi hW fun j ↦ ?_)
    cases j using Fin.cases with
    | zero => exact contDiffMBOn_iteratedD_zero_compLeftOn hO hh hW hg hgO
    | succ i =>
      have hdh : SmoothMBOn (dMB h) (O ×ˢ univ) := fun k ↦ (hh (k + 1)).2.2
      have hG : ContDiffMBOn k (fun w ↦ graphDataCLM (g w)) W := ContDiffMBOn.clm_comp' _ hW hg
      have hGO : ∀ w ∈ W, MapsTo (graphDataCLM (g w)) (Opens.prodUniv U) (O ×ˢ univ) :=
        fun w hw p hp ↦ by
          rw [graphDataCLM_apply _ hp]
          exact ⟨hgO w hw hp, mem_univ _⟩
      have hc := ih (hO.prod isOpen_univ) hdh hW hG hGO
      let T : C(U × (Fin (i + 1) → Z), (Opens.prodUniv U) × (Fin i → Z × Z)) :=
        ⟨fun p ↦ (⟨(p.1, p.2 0), p.1.2⟩, fun l ↦ (p.2 l.succ, 0)), by fun_prop⟩
      let P : C((Opens.prodUniv U) × (Fin i → Z × Z), F) →L[ℝ] C(U × (Fin (i + 1) → Z), F) :=
        ⟨⟨⟨fun φ ↦ φ.comp T, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩, ContinuousMap.continuous_precomp T⟩
      have hc' := ContDiffMBOn.clm_comp' (P.comp (iteratedDCLM i (Nat.le_of_lt_succ i.2))) hW hc
      refine ContDiffMBOn.congr_of_isOpen hW (fun w hw ↦ ?_) hc'
      change (iteratedD i (Nat.le_of_lt_succ i.2)
          (compLeftOn (dMB h) (O ×ˢ univ) (graphDataCLM (g w)))).comp T =
        iteratedD (i + 1) (by omega) (compLeftOn h O (g w))
      rw [iteratedD_succ_eq, dMap_compLeftOn hO (hh (r + 1)) (hgO w hw)]

end CompLeftOn

/-! ### Restriction to the members of an open cover -/

section Restrict

variable {Z : Type u} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
  [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z] [T2Space Z]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {r : ℕ} {U V : Opens Z}

/-- The restriction `C^r(U, F) → C^r(V, F)` for open `V ⊆ U`, a continuous linear map. -/
def restrictCLM (hVU : V ≤ U) : ContDiffMBMap F r U →L[ℝ] ContDiffMBMap F r V :=
  compRightOfContDiffCLM ((ContinuousLinearMap.id ℝ Z).contDiffMBOn r V) fun _ hx ↦ hVU hx

/-- The restriction agrees with the map on `V`. -/
theorem restrictCLM_apply (hVU : V ≤ U) (γ : ContDiffMBMap F r U) {x : Z} (hx : x ∈ V) :
    restrictCLM hVU γ x = γ x :=
  compRightOfContDiff_apply ((ContinuousLinearMap.id ℝ Z).contDiffMBOn r V)
    (fun _ hx ↦ hVU hx) γ hx

/-- The differentials of the restriction are those of the map. -/
theorem iteratedD_restrictCLM (hVU : V ≤ U) (γ : ContDiffMBMap F r U) (j : ℕ) (hj : j ≤ r)
    (p : V × (Fin j → Z)) :
    iteratedD j hj (restrictCLM hVU γ) p = iteratedD j hj γ (⟨p.1.1, hVU p.1.2⟩, p.2) := by
  simp only [iteratedD_apply]
  refine iteratedDMB_congr_of_eventuallyEq j ?_ p.2
  exact Filter.eventually_of_mem (V.isOpen.mem_nhds p.1.2) fun x hx ↦ restrictCLM_apply hVU γ hx

variable {ι : Type*} (V : ι → Opens Z) (hVU : ∀ a, V a ≤ U)

/-- The restrictions `C^r(U, F) → ∏_a C^r(V_a, F)` to the members of a family of open subsets. -/
def restrictCover : ContDiffMBMap F r U →L[ℝ] ∀ a, ContDiffMBMap F r (V a) :=
  ContinuousLinearMap.pi fun a ↦ restrictCLM (hVU a)

include hVU in
/-- **Convergence is local**: if the `V_a` cover `U`, a family converges in `C^r(U, F)` as soon as
its restrictions to all the `V_a` converge. -/
theorem tendsto_of_tendsto_restrictCLM (hcov : (U : Set Z) ⊆ ⋃ a, (V a : Set Z)) {α : Type*}
    {l : Filter α} {ψ : α → ContDiffMBMap F r U} {γ : ContDiffMBMap F r U}
    (h : ∀ a, Tendsto (fun p ↦ restrictCLM (hVU a) (ψ p)) l (𝓝 (restrictCLM (hVU a) γ))) :
    Tendsto ψ l (𝓝 γ) := by
  rw [isEmbedding_toPi.tendsto_nhds_iff, tendsto_pi_nhds]
  intro j
  rw [ContinuousMap.tendsto_compactOpen_iff_forall]
  intro K hK
  let O : ι → Set (U × (Fin j → Z)) := fun a ↦ {y | (y.1 : Z) ∈ V a}
  have hO : ∀ a, IsOpen (O a) := fun a ↦ (V a).isOpen.preimage
    (continuous_subtype_val.comp continuous_fst)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O hO fun y _ ↦ by
    obtain ⟨a, ha⟩ := mem_iUnion.1 (hcov y.1.2)
    exact mem_iUnion.2 ⟨a, ha⟩
  obtain ⟨Kb, hKb, hKbO, hKeq⟩ := hK.finite_compact_cover t O (fun a _ ↦ hO a) ht
  have hsub : ∀ b : t, Kb b.1 ⊆ K := fun b ↦ by
    rw [hKeq]
    exact subset_biUnion_of_mem (u := Kb) b.2
  have hcovK : K ⊆ ⋃ b : t, Kb b.1 := by
    rw [hKeq]
    intro y hy
    obtain ⟨a, ha, hya⟩ := mem_iUnion₂.1 hy
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hya⟩
  rw [(isEmbedding_restrictPieces (G := F) hsub (fun b ↦ hKb b.1) hcovK).tendsto_nhds_iff,
    tendsto_pi_nhds]
  intro b
  let σ : C(Kb b.1, V b.1 × (Fin j → Z)) :=
    ⟨fun y ↦ (⟨y.1.1, hKbO b.1 y.2⟩, y.1.2), by fun_prop⟩
  have key : ∀ γ' : ContDiffMBMap F r U,
      restrictPieces (G := F) hsub ((toPi γ' j).restrict K) b =
        (iteratedD j (Nat.le_of_lt_succ j.2) (restrictCLM (hVU b.1) γ')).comp σ := fun γ' ↦ by
    ext y
    exact (iteratedD_restrictCLM (hVU b.1) γ' j (Nat.le_of_lt_succ j.2) (σ y)).symm
  have h' := (ContinuousMap.continuous_precomp σ).continuousAt.tendsto.comp
    ((continuous_iteratedD j (Nat.le_of_lt_succ j.2)).continuousAt.tendsto.comp (h b.1))
  rw [← key γ] at h'
  exact h'.congr fun p ↦ (key (ψ p)).symm

include hVU in
/-- If the `V_a` cover `U`, the restrictions `C^r(U, F) → ∏_a C^r(V_a, F)` form a topological
embedding. -/
theorem isEmbedding_restrictCover (hcov : (U : Set Z) ⊆ ⋃ a, (V a : Set Z)) :
    Topology.IsEmbedding (restrictCover (F := F) (r := r) V hVU) := by
  refine ⟨Topology.isInducing_iff_nhds.2 fun γ ↦ le_antisymm
    (restrictCover (F := F) (r := r) V hVU).continuous.continuousAt.tendsto.le_comap ?_,
    fun γ η h ↦ ?_⟩
  · have : Tendsto (id : ContDiffMBMap F r U → ContDiffMBMap F r U)
        (comap (restrictCover (F := F) (r := r) V hVU)
          (𝓝 (restrictCover (F := F) (r := r) V hVU γ))) (𝓝 γ) :=
      tendsto_of_tendsto_restrictCLM V hVU hcov fun a ↦
        ((continuous_apply (A := fun a ↦ ContDiffMBMap F r (V a)) a).continuousAt.tendsto.comp
          tendsto_comap)
    exact this
  · ext x
    by_cases hx : x ∈ U
    · obtain ⟨a, ha⟩ := mem_iUnion.1 (hcov hx)
      have := congrArg (fun φ ↦ φ a x) h
      simpa [restrictCover, restrictCLM_apply (hVU a) _ ha] using this
    · rw [γ.apply_of_notMem hx, η.apply_of_notMem hx]

include hVU in
/-- If the `V_a` cover `U`, the restrictions `C^r(U, F) → ∏_a C^r(V_a, F)` have closed range: the
compatible families glue. -/
theorem isClosed_range_restrictCover (hcov : (U : Set Z) ⊆ ⋃ a, (V a : Set Z)) :
    IsClosed (range (restrictCover (F := F) (r := r) V hVU)) := by
  let S : Set (∀ a, ContDiffMBMap F r (V a)) :=
    {φ | ∀ a b (x : Z) (ha : x ∈ V a) (hb : x ∈ V b), φ a x = φ b x}
  have hev : ∀ a (x : Z) (ha : x ∈ V a),
      Continuous fun φ : ∀ a, ContDiffMBMap F r (V a) ↦ φ a x := fun a x ha ↦
    ((continuous_eval_const ((⟨x, ha⟩, Fin.elim0) : V a × (Fin 0 → Z))).comp
      (continuous_iteratedD 0 (Nat.zero_le r))).comp (continuous_apply a)
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun x ↦
      isClosed_iInter fun ha ↦ isClosed_iInter fun hb ↦ isClosed_eq (hev a x ha) (hev b x hb)
  convert hS using 1
  ext φ
  constructor
  · rintro ⟨γ, rfl⟩ a b x ha hb
    change restrictCLM (hVU a) γ x = restrictCLM (hVU b) γ x
    rw [restrictCLM_apply _ _ ha, restrictCLM_apply _ _ hb]
  · intro hφ
    classical
    have hc : ∀ x ∈ U, ∃ a, x ∈ V a := fun x hx ↦ mem_iUnion.1 (hcov hx)
    choose β hβ using hc
    let g : Z → F := fun x ↦ if hx : x ∈ U then φ (β x hx) x else 0
    have hg : ∀ a x, x ∈ V a → g x = φ a x := fun a x ha ↦ by
      have hx : x ∈ U := hVU a ha
      simp only [g, hx, dite_true]
      exact hφ _ _ x (hβ x hx) ha
    have hgC : ContDiffMBOn r g U := by
      refine ContDiffMBOn.of_local U.isOpen fun x hx ↦
        ⟨V (β x hx), (V (β x hx)).isOpen, hβ x hx, ?_⟩
      refine ContDiffMBOn.congr_of_isOpen (U.isOpen.inter (V (β x hx)).isOpen)
        (fun y hy ↦ (hg _ y hy.2).symm) ((φ (β x hx)).contDiffMBOn.mono inter_subset_right)
    refine ⟨mk g hgC fun x hx ↦ by simp [g, hx], funext fun a ↦ ?_⟩
    ext x
    change restrictCLM (hVU a) (mk g hgC _) x = φ a x
    by_cases ha : x ∈ V a
    · rw [restrictCLM_apply _ _ ha, coe_mk, hg a x ha]
    · rw [apply_of_notMem _ ha, apply_of_notMem _ ha]

include hVU in
/-- **`C^k` maps into `C^r(U, F)` are local**: if the `V_a` cover `U` and all the restrictions of
`ψ` to the `V_a` are `C^k`, then `ψ` is `C^k`. -/
theorem contDiffMBOn_of_restrictCLM (hcov : (U : Set Z) ⊆ ⋃ a, (V a : Set Z)) {X : Type*}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T2Space X] {k : ℕ}
    {ψ : X → ContDiffMBMap F r U} {W : Set X} (hW : IsOpen W)
    (h : ∀ a, ContDiffMBOn k (fun w ↦ restrictCLM (hVU a) (ψ w)) W) : ContDiffMBOn k ψ W :=
  contDiffMBOn_of_isClosedEmbedding (restrictCover V hVU) (isEmbedding_restrictCover V hVU hcov)
    (isClosed_range_restrictCover V hVU hcov) hW (contDiffMBOn_pi hW h)

end Restrict

end LocallyConvex.Analysis.ContDiffMBMap

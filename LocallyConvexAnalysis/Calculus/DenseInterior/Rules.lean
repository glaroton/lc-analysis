/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.DenseInterior.Basic
public import LocallyConvexAnalysis.MappingSpace.SmoothTopology

/-!
# Further rules for `C^k` maps on sets with dense interior

Reference: [GN26, §1.4], pp. 51–58. This file continues
`LocallyConvexAnalysis.Calculus.DenseInterior.Basic`.

## Main results

* `IsLocallyConvexSubset.exists_seq_interior`: every point of a locally convex subset `U` with
  dense interior is the limit of a sequence in `U⁰` ([GN26, proof of Lemma 1.4.16]).
* `ContinuousOn.mapsTo_of_isSeqClosed`: a map continuous on such a `U` that sends `U⁰` into a
  sequentially closed set sends `U` into it.
* `contDiffLC_subtype_iff`: a map with values in a sequentially closed vector subspace `F₀ ⊆ F`
  is `C^k` as a map into `F` if and only if it is `C^k` as a map into `F₀` ([GN26, Lemma 1.4.16]).
* `contDiffLC_iff_contDiffCurveOn`, `ContDiffLC.dLC_curve`: on a non-degenerate interval, `C^k`
  maps in the sense of Definition 1.4.4 are the `C^k` curves of Definition 1.1.1, and
  `dγ(s, r) = r γ'(s)` ([GN26, Lemma 1.4.13]).
* `contDiffLC_one_iff_partials`, `ContDiffLC.dLC_eq_add_partials`: the rule on partial
  differentials ([GN26, Proposition 1.4.11]).
* `iteratedDLC`, `ContDiffLC.iteratedDLC_extends`, `iteratedDLC_unique`: the higher differentials
  of a `C^k` map on `U` extend those of `f|U⁰` continuously and uniquely to `U × E^j`, `j ≤ k`
  ([GN26, Lemma 1.4.5], necessity of the condition).
* `contDiffLC_of_extends`, `contDiffLC_iff_extends`: conversely, if `f` is continuous, `f|U⁰` is
  `C^k` and the `d^(j) (f|U⁰)` extend continuously to `U × E^j`, then `f` is `C^k`
  ([GN26, Lemma 1.4.5], sufficiency).

## Implementation notes

* **Departure from Glöckner–Neeb in Lemma 1.4.5.** The sufficiency is deduced in the source from
  the version of Lemma 1.3.12 for sets with dense interior (Remark 1.4.12). We argue by induction
  on `k` instead, using the explicit formula `ContDiffMBOn.iteratedDMB_dMB` for the differentials
  of `d(f|U⁰)` on the open set `U⁰ × E`, whose right-hand side extends continuously. We do not
  claim this argument is new.

`C^{k,ℓ}` maps on products of sets with dense interior are in
`LocallyConvexAnalysis.Calculus.DenseInterior.Ckl`.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v

/-! ### Approximation from the interior -/

section Approximation

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Every point `x` of a locally convex subset `U` with dense interior is the limit of a sequence
in the interior of `U`: if `z` is an interior point of a convex neighbourhood `C` of `x` in `U`,
the points `x + (n + 2)⁻¹ (z - x)` of the open segment `]z, x[` lie in `C⁰`
([GN26, proof of Lemma 1.4.16, p. 58]). -/
theorem IsLocallyConvexSubset.exists_seq_interior {U : Set E} (hU : IsLocallyConvexSubset U)
    (hd : HasDenseInterior U) {x : E} (hx : x ∈ U) :
    ∃ s : ℕ → E, (∀ n, s n ∈ interior U) ∧ Tendsto s atTop (𝓝 x) := by
  obtain ⟨W, -, hxW, -, hC, z, hz⟩ :=
    hU.exists_isOpen_convex_interior hd hx (univ_mem : univ ∈ 𝓝 x)
  have hxC : x ∈ closure (U ∩ W) := subset_closure ⟨hx, hxW⟩
  set t : ℕ → ℝ := fun n ↦ ((n : ℝ) + 2)⁻¹
  have ht0 : ∀ n, 0 < t n := fun n ↦ inv_pos.2 (by positivity)
  have ht1 : ∀ n, t n < 1 := fun n ↦ inv_lt_one_of_one_lt₀ (by linarith [n.cast_nonneg (α := ℝ)])
  refine ⟨fun n ↦ x + t n • (z - x), fun n ↦ ?_, ?_⟩
  · refine interior_mono inter_subset_left
      (hC.openSegment_interior_closure_subset_interior hz hxC ?_)
    refine ⟨t n, 1 - t n, ht0 n, sub_pos.2 (ht1 n), by ring, ?_⟩
    change t n • z + (1 - t n) • x = x + t n • (z - x)
    rw [smul_sub, sub_smul, one_smul]
    abel
  · have ht : Tendsto t atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.add (ht.smul_const (z - x))

/-- A map continuous on a locally convex subset `U` with dense interior that sends `U⁰` into a
sequentially closed set `A` sends `U` into `A`. -/
theorem ContinuousOn.mapsTo_of_isSeqClosed {X : Type*} [TopologicalSpace X] {U : Set E}
    (hU : IsLocallyConvexSubset U) (hd : HasDenseInterior U) {D : E → X} (hD : ContinuousOn D U)
    {A : Set X} (hA : IsSeqClosed A) (hint : MapsTo D (interior U) A) : MapsTo D U A := by
  intro x hx
  obtain ⟨s, hs, hlim⟩ := hU.exists_seq_interior hd hx
  have hsU : Tendsto s atTop (𝓝[U] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n ↦ interior_subset (hs n)⟩
  exact hA (fun n ↦ hint (hs n)) ((hD x hx).tendsto.comp hsU)

end Approximation

/-! ### Corestriction to a sequentially closed subspace -/

section Corestriction

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Directional derivatives of maps into a sequentially closed subspace stay in the subspace. -/
theorem HasDirDerivAt.mem_of_isSeqClosed {E : Type u} [AddCommGroup E] [Module ℝ E]
    {F₀ : Submodule ℝ F} (hF₀ : IsSeqClosed (F₀ : Set F)) {g : E → F₀}
    {x h : E} {y : F} (hg : HasDirDerivAt (fun x ↦ (g x : F)) x h y) : y ∈ F₀ := by
  have hseq : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
    · exact tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    · exact inv_ne_zero (by positivity)
  exact hF₀ (fun n ↦ F₀.smul_mem _ (F₀.sub_mem (g _).2 (g _).2)) (hg.comp hseq)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The directional derivatives of `g : E → F₀` are those of `g` read in `F`. -/
theorem hasDirDerivAt_subtype_iff {E : Type u} [AddCommGroup E] [Module ℝ E]
    {F₀ : Submodule ℝ F} {g : E → F₀} {x h : E} {y : F₀} :
    HasDirDerivAt g x h y ↔ HasDirDerivAt (fun x ↦ (g x : F)) x h y := by
  unfold HasDirDerivAt
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
  rfl

/-- **Corestriction** ([GN26, Lemma 1.4.16, p. 58]). Let `U` be a locally convex subset
with dense interior and `F₀ ⊆ F` a sequentially closed vector subspace. A map `g : U → F₀` is
`C^k` if and only if it is `C^k` as a map into `F`. -/
theorem contDiffLC_subtype_iff {F₀ : Submodule ℝ F} (hF₀ : IsSeqClosed (F₀ : Set F)) :
    ∀ {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
      [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
      {g : E → F₀} {U : Set E}, IsLocallyConvexSubset U → HasDenseInterior U →
      (ContDiffLC k g U ↔ ContDiffLC k (fun x ↦ (g x : F)) U)
  | k, E, _, _, _, _, _, _, _, g, U, hU, hd => by
    refine ⟨fun hg ↦ hg.clm_comp F₀.subtypeL hd, fun hg ↦ ?_⟩
    induction k generalizing E with
    | zero => exact Topology.IsInducing.subtypeVal.continuousOn_iff.2 hg
    | succ k ih =>
      have hcont : ContinuousOn g U :=
        Topology.IsInducing.subtypeVal.continuousOn_iff.2 hg.continuousOn
      -- the differential takes values in `F₀`
      have hmem : MapsTo (dLC (fun x ↦ (g x : F)) U) (U ×ˢ univ) F₀ := by
        refine ContinuousOn.mapsTo_of_isSeqClosed (hU.prod isLocallyConvexSubset_univ)
          hd.prod_univ hg.continuousOn_dLC hF₀ fun p hp ↦ ?_
        rw [interior_prod_eq, interior_univ] at hp
        rw [dLC_of_mem_interior _ hp.1]
        exact (hg.hasDirDerivAt hp.1 p.2).mem_of_isSeqClosed hF₀
      classical
      set D : E × E → F₀ := fun p ↦
        if h : dLC (fun x ↦ (g x : F)) U p ∈ F₀ then ⟨_, h⟩ else 0 with hD
      have hDcoe : EqOn (fun p ↦ (D p : F)) (dLC (fun x ↦ (g x : F)) U) (U ×ˢ univ) :=
        fun p hp ↦ by
          simp only [hD]
          split_ifs with h
          · rfl
          · exact absurd (hmem hp) h
      have hDk : ContDiffLC k D (U ×ˢ univ) :=
        (ih (E × E) inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance D (U ×ˢ univ) (hU.prod isLocallyConvexSubset_univ)
          hd.prod_univ (hg.contDiffLC_dLC.congr hDcoe.symm))
      refine (ContDiffLC.of_hasDirDerivAt hd hcont (fun x hx h ↦ ?_) hDk).1
      have hDx : (D (x, h) : F) = dLC (fun x ↦ (g x : F)) U (x, h) :=
        hDcoe ⟨interior_subset hx, mem_univ _⟩
      rw [hasDirDerivAt_subtype_iff, hDx, dLC_of_mem_interior _ hx]
      exact hg.hasDirDerivAt hx h

end Corestriction

/-! ### Curves -/

section Curves

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- `C^k` curves on a subset `I ⊆ ℝ` ([GN26, Definition 1.1.1]): `γ` is `C^0` if it is
continuous on `I`, and `C^{k+1}` if at every `t ∈ I` the difference quotients
`(γ(s) - γ(t)) / (s - t)`, `s ∈ I \ {t}`, converge to some `γ'(t)` and `γ'` is `C^k` on `I`. For
normed `E` the first condition is `HasDerivWithinAt γ (γ' t) I t`
(`hasDerivWithinAt_iff_tendsto_slope`). -/
def ContDiffCurveOn : ℕ → (ℝ → E) → Set ℝ → Prop
  | 0, γ, I => ContinuousOn γ I
  | k + 1, γ, I => ∃ γ' : ℝ → E,
      (∀ t ∈ I, Tendsto (slope γ t) (𝓝[I \ {t}] t) (𝓝 (γ' t))) ∧ ContDiffCurveOn k γ' I

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- A derivative at an interior point gives the directional derivatives `dγ(t, r) = r γ'(t)`. -/
theorem hasDirDerivAt_of_tendsto_slope {γ : ℝ → E} {t : ℝ} {v : E}
    (h : Tendsto (slope γ t) (𝓝[≠] t) (𝓝 v)) (r : ℝ) : HasDirDerivAt γ t r (r • v) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [HasDirDerivAt, tendsto_const_nhds]
  have hline : Tendsto (fun τ : ℝ ↦ t + τ • r) (𝓝[≠] 0) (𝓝[≠] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun τ : ℝ ↦ t + τ • r := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ (hτ : τ ≠ 0)
      simpa [smul_eq_mul] using mul_ne_zero hτ hr
  have hc := ((h.comp hline).const_smul r)
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ (hτ : τ ≠ 0)
  simp only [Function.comp, slope, vsub_eq_sub, add_sub_cancel_left, smul_eq_mul, mul_inv,
    smul_smul]
  congr 1
  field_simp

/-- The derivative of a `C^1` map on an interval is `dγ(s, 1)` ([GN26, proof of Lemma 1.4.13]). -/
theorem ContDiffLC.tendsto_slope {γ : ℝ → E} {I : Set ℝ} (hI : IsLocallyConvexSubset I)
    (hd : HasDenseInterior I) (hγ : ContDiffLC 1 γ I) {s : ℝ} (hs : s ∈ I) :
    Tendsto (slope γ s) (𝓝[I \ {s}] s) (𝓝 (dLC γ I (s, 1))) := by
  have hq := hγ.tendsto_quotient hI hd (v := (1 : ℝ)) hs
  set φ : ℝ → ℝ × ℝ × ℝ := fun t ↦ (s, 1, t - s)
  have hφ : Tendsto φ (𝓝[I \ {s}] s)
      (𝓝[{p : ℝ × ℝ × ℝ | p.1 ∈ I ∧ p.1 + p.2.2 • p.2.1 ∈ I ∧ p.2.2 ≠ 0}] (s, 1, 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous φ := by fun_prop
      simpa [φ] using (this.tendsto s).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨hs, by simpa [φ] using ht.1, sub_ne_zero.2 ht.2⟩
  refine (hq.comp hφ).congr' (Eventually.of_forall fun t ↦ ?_)
  simp [φ, slope, vsub_eq_sub]

/-- **`C^k` curves** ([GN26, Lemma 1.4.13, p. 56]). On a convex set `I ⊆ ℝ` with nonempty
interior (a non-degenerate interval), `γ` is `C^k` in the sense of Definition 1.4.4 if and only
if it is a `C^k` curve. In this case `dγ(s, r) = r γ'(s)` (`ContDiffLC.dLC_curve`). -/
theorem contDiffLC_iff_contDiffCurveOn {I : Set ℝ} (hI : Convex ℝ I)
    (hne : (interior I).Nonempty) : ∀ {k : ℕ} {γ : ℝ → E},
    ContDiffLC k γ I ↔ ContDiffCurveOn k γ I := by
  have hd : HasDenseInterior I := hI.hasDenseInterior hne
  have hU : IsLocallyConvexSubset I := hI.isLocallyConvexSubset
  have hd' : HasDenseInterior (I ×ˢ (univ : Set ℝ)) := hd.prod_univ
  intro k
  induction k with
  | zero => exact Iff.rfl
  | succ k ih =>
    intro γ
    constructor
    · intro hγ
      refine ⟨fun s ↦ dLC γ I (s, 1), fun s hs ↦ (hγ.of_le (by omega)).tendsto_slope hU hd hs,
        ih.1 ?_⟩
      have hpair : ContDiffLC k (fun s : ℝ ↦ (s, (1 : ℝ))) I :=
        (contDiffLC_id k hd).prodMk hd (contDiffLC_const k 1 hd)
      exact hγ.contDiffLC_dLC.comp hd (hU.prod isLocallyConvexSubset_univ) hd' hpair
        fun s hs ↦ ⟨hs, mem_univ _⟩
    · rintro ⟨γ', hγ', hk⟩
      have hk' : ContDiffLC k γ' I := ih.2 hk
      have hcont : ContinuousOn γ I := fun s hs ↦ by
        refine continuousWithinAt_sdiff_singleton.1 (?_ : ContinuousWithinAt γ (I \ {s}) s)
        have hlim : Tendsto (fun t ↦ γ s + (t - s) • slope γ s t) (𝓝[I \ {s}] s)
            (𝓝 (γ s + (s - s) • γ' s)) := by
          refine tendsto_const_nhds.add (Tendsto.smul ?_ (hγ' s hs))
          exact ((continuous_id.sub continuous_const).tendsto s).mono_left nhdsWithin_le_nhds
        rw [sub_self, zero_smul, add_zero] at hlim
        refine hlim.congr' (Eventually.of_forall fun t ↦ ?_)
        rw [sub_smul_slope, vsub_eq_sub, add_sub_cancel]
      have hdir : ∀ x ∈ interior I, ∀ r : ℝ, HasDirDerivAt γ x r (r • γ' x) := by
        intro x hx r
        have hnhds : 𝓝[I \ {x}] x = 𝓝[≠] x := by
          rw [sdiff_eq]
          exact nhdsWithin_inter_of_mem
            (mem_nhdsWithin_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx))
        exact hasDirDerivAt_of_tendsto_slope (hnhds ▸ hγ' x (interior_subset hx)) r
      have hfst : ContDiffLC k (fun p : ℝ × ℝ ↦ γ' p.1) (I ×ˢ univ) :=
        hk'.comp hd' hU hd ((ContinuousLinearMap.fst ℝ ℝ ℝ).contDiffLC k hd') fun p hp ↦ hp.1
      have hD : ContDiffLC k (fun p : ℝ × ℝ ↦ p.2 • γ' p.1) (I ×ˢ univ) :=
        ContDiffLC.bilin (LinearMap.lsmul ℝ E) (continuous_fst.smul continuous_snd) hd'
          ((ContinuousLinearMap.snd ℝ ℝ ℝ).contDiffLC k hd') hfst
      exact (ContDiffLC.of_hasDirDerivAt hd hcont (fun x hx r ↦ hdir x hx r) hD).1

omit [IsTopologicalAddGroup E] [LocallyConvexSpace ℝ E] in
/-- The differential of a `C^1` curve: `dγ(s, r) = r dγ(s, 1) = r γ'(s)`
([GN26, (1.51)]). -/
theorem ContDiffLC.dLC_curve {γ : ℝ → E} {I : Set ℝ} (hd : HasDenseInterior I)
    (hγ : ContDiffLC 1 γ I) {s : ℝ} (hs : s ∈ I) (r : ℝ) :
    dLC γ I (s, r) = r • dLC γ I (s, 1) := by
  simpa using hγ.dLC_smul hd hs r 1

end Curves

/-! ### Partial differentials -/

section Partials

variable {E₁ E₂ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **Rule on partial differentials** ([GN26, Proposition 1.4.11, p. 55]). Let
`U ⊆ E₁ × E₂` have dense interior and `f` be continuous on `U`. Then `f` is `C^1` on `U` if and
only if its partial derivatives `d₁f(x, u)` and `d₂f(x, v)` exist at the interior points and
extend to continuous maps on `U × E₁` and `U × E₂`. In this case
`df(x, (u, v)) = d₁f(x, u) + d₂f(x, v)` on `U` (`ContDiffLC.dLC_eq_add_partials`). -/
theorem contDiffLC_one_iff_partials {f : E₁ × E₂ → F} {U : Set (E₁ × E₂)}
    (hd : HasDenseInterior U) (hf : ContinuousOn f U) :
    ContDiffLC 1 f U ↔ ∃ d₁ : (E₁ × E₂) × E₁ → F, ∃ d₂ : (E₁ × E₂) × E₂ → F,
      ContinuousOn d₁ (U ×ˢ univ) ∧ ContinuousOn d₂ (U ×ˢ univ) ∧
      (∀ p ∈ interior U, ∀ u, HasDirDerivAt f p (u, 0) (d₁ (p, u))) ∧
      ∀ p ∈ interior U, ∀ v, HasDirDerivAt f p (0, v) (d₂ (p, v)) := by
  constructor
  · intro h
    refine ⟨fun q ↦ dLC f U (q.1, (q.2, 0)), fun q ↦ dLC f U (q.1, (0, q.2)), ?_, ?_,
      fun p hp u ↦ ?_, fun p hp v ↦ ?_⟩
    · exact h.continuousOn_dLC.comp (by fun_prop) fun q hq ↦ ⟨hq.1, mem_univ _⟩
    · exact h.continuousOn_dLC.comp (by fun_prop) fun q hq ↦ ⟨hq.1, mem_univ _⟩
    · beta_reduce
      rw [dLC_of_mem_interior f (p := (p, (u, 0))) hp]
      exact h.hasDirDerivAt hp _
    · beta_reduce
      rw [dLC_of_mem_interior f (p := (p, (0, v))) hp]
      exact h.hasDirDerivAt hp _
  · rintro ⟨d₁, d₂, hc₁, hc₂, h₁, h₂⟩
    have hsub : interior U ×ˢ (univ : Set E₁) ⊆ U ×ˢ univ := prod_mono interior_subset le_rfl
    have hsub' : interior U ×ˢ (univ : Set E₂) ⊆ U ×ˢ univ := prod_mono interior_subset le_rfl
    obtain ⟨-, hdMB⟩ := contDiffMBOn_one_of_partials isOpen_interior (d₁ := fun p u ↦ d₁ (p, u))
      (d₂ := fun p v ↦ d₂ (p, v)) h₁ h₂ ((hc₁.mono hsub).comp continuousOn_id fun _ h ↦ h)
      ((hc₂.mono hsub').comp continuousOn_id fun _ h ↦ h)
    set D : (E₁ × E₂) × (E₁ × E₂) → F := fun q ↦ d₁ (q.1, q.2.1) + d₂ (q.1, q.2.2)
    have hD : ContinuousOn D (U ×ˢ univ) :=
      (hc₁.comp (s := U ×ˢ (univ : Set (E₁ × E₂)))
        (f := fun q : (E₁ × E₂) × (E₁ × E₂) ↦ (q.1, q.2.1)) (by fun_prop)
        fun q hq ↦ ⟨hq.1, mem_univ _⟩).add
      (hc₂.comp (s := U ×ˢ (univ : Set (E₁ × E₂)))
        (f := fun q : (E₁ × E₂) × (E₁ × E₂) ↦ (q.1, q.2.2)) (by fun_prop)
        fun q hq ↦ ⟨hq.1, mem_univ _⟩)
    refine (ContDiffLC.of_hasDirDerivAt (k := 0) hd hf (fun p hp w ↦ ?_) hD).1
    have hw := (contDiffMBOn_one_of_partials isOpen_interior (d₁ := fun p u ↦ d₁ (p, u))
      (d₂ := fun p v ↦ d₂ (p, v)) h₁ h₂ ((hc₁.mono hsub).comp continuousOn_id fun _ h ↦ h)
      ((hc₂.mono hsub').comp continuousOn_id fun _ h ↦ h)).1.hasDirDerivAt hp w
    rwa [hdMB p hp w.1 w.2] at hw

/-- The differential is the sum of the partial differentials ([GN26, (1.50)]). -/
theorem ContDiffLC.dLC_eq_add_partials {f : E₁ × E₂ → F} {U : Set (E₁ × E₂)}
    (hd : HasDenseInterior U) (hf : ContDiffLC 1 f U) {p : E₁ × E₂} (hp : p ∈ U) (u : E₁)
    (v : E₂) : dLC f U (p, (u, v)) = dLC f U (p, (u, 0)) + dLC f U (p, (0, v)) := by
  simpa using hf.dLC_add hd hp (u, 0) (0, v)

end Partials

/-! ### Higher differentials -/

section Higher

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [T2Space F]

/-- The `k`-th differential `d^(k) f : U × E^k → F` on a set with dense interior, defined through
[GN26, (1.36)]: `d^(k+1) f (x, y₀, …, yₖ) = d^(k) (df) ((x, y₀), (y₁, 0), …, (yₖ, 0))`,
with `df = dLC f U`. For `C^k` maps it extends `d^(k) (f|U⁰)` (`iteratedDLC_eq_iteratedDMB`)
continuously (`ContDiffLC.continuousOn_iteratedDLC`). -/
def iteratedDLC : (k : ℕ) → ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
    (E → F) → Set E → E × (Fin k → E) → F
  | 0, _, _, _, _, f, _, p => f p.1
  | k + 1, _, _, _, _, f, U, p =>
      iteratedDLC k (dLC f U) (U ×ˢ univ) ((p.1, p.2 0), fun i ↦ (p.2 i.succ, 0))

omit [T2Space F] in
/-- `d^(k) f` extends the `k`-th differential of `f|U⁰`. -/
theorem iteratedDLC_eq_iteratedDMB : ∀ {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {f : E → F} {U : Set E} {p : E × (Fin k → E)}, p.1 ∈ interior U →
    iteratedDLC k f U p = iteratedDMB k f p
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | k + 1, E, _, _, _, _, _, _, _, f, U, ⟨x, v⟩, hx => by
    have hx' : (x, v 0) ∈ interior (U ×ˢ (univ : Set E)) := by
      rw [interior_prod_eq, interior_univ]
      exact ⟨hx, mem_univ _⟩
    have hev : dLC f U =ᶠ[𝓝 (x, v 0)] dMB f :=
      (dLC_eqOn_interior f U).eventuallyEq_of_mem
        (by rw [← interior_univ, ← interior_prod_eq]; exact isOpen_interior.mem_nhds hx')
    change iteratedDLC k (dLC f U) (U ×ˢ univ) ((x, v 0), fun i ↦ (v i.succ, 0)) = _
    rw [iteratedDLC_eq_iteratedDMB hx', iteratedDMB_succ_eq_dMB]
    exact iteratedDMB_congr_of_eventuallyEq k hev _

omit [T2Space F] in
/-- The higher differentials of a `C^k` map are continuous on `U × E^j` for `j ≤ k`. -/
theorem ContDiffLC.continuousOn_iteratedDLC : ∀ {j k : ℕ} {E : Type u} [AddCommGroup E]
    [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] [T2Space E] {f : E → F} {U : Set E}, j ≤ k → ContDiffLC k f U →
    ContinuousOn (iteratedDLC j f U) (U ×ˢ univ)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hf =>
    hf.continuousOn.comp continuous_fst.continuousOn fun _ hp ↦ hp.1
  | j + 1, 0, _, _, _, _, _, _, _, _, _, _, hjk, _ => absurd hjk (by omega)
  | j + 1, k + 1, E, _, _, _, _, _, _, _, f, U, hjk, hf => by
    have h := ContDiffLC.continuousOn_iteratedDLC (j := j) (by omega) hf.contDiffLC_dLC
    refine h.comp (s := U ×ˢ univ)
      (f := fun p : E × (Fin (j + 1) → E) ↦ ((p.1, p.2 0), fun i ↦ (p.2 i.succ, 0)))
      (by fun_prop) fun p hp ↦ ⟨⟨hp.1, mem_univ _⟩, mem_univ _⟩

/-- **Higher differentials on sets with dense interior** ([GN26, Lemma 1.4.5], the
necessity of the condition). If `f` is `C^k` on `U`, then `f|U⁰` is `C^k` and, for `j ≤ k`, the
differential `d^(j) (f|U⁰)` extends to the continuous map `d^(j) f : U × E^j → F`. The extension is
unique (`iteratedDLC_unique`). -/
theorem ContDiffLC.iteratedDLC_extends {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {f : E → F} {U : Set E} (hf : ContDiffLC k f U) :
    ContDiffMBOn k f (interior U) ∧ ∀ j ≤ k, ContinuousOn (iteratedDLC j f U) (U ×ˢ univ) ∧
      EqOn (iteratedDLC j f U) (iteratedDMB j f) (interior U ×ˢ univ) :=
  ⟨hf.contDiffMBOn_interior, fun _ hj ↦
    ⟨hf.continuousOn_iteratedDLC hj, fun _ hp ↦ iteratedDLC_eq_iteratedDMB hp.1⟩⟩

/-- Uniqueness of the continuous extension of `d^(j) (f|U⁰)` to `U × E^j`. -/
theorem iteratedDLC_unique {j : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E]
    {f : E → F} {U : Set E} (hd : HasDenseInterior U)
    {D₁ D₂ : E × (Fin j → E) → F} (h₁ : ContinuousOn D₁ (U ×ˢ univ))
    (h₂ : ContinuousOn D₂ (U ×ˢ univ)) (e₁ : EqOn D₁ (iteratedDMB j f) (interior U ×ˢ univ))
    (e₂ : EqOn D₂ (iteratedDMB j f) (interior U ×ˢ univ)) : EqOn D₁ D₂ (U ×ˢ univ) := by
  refine EqOn.of_subset_closure (fun p hp ↦ (e₁ hp).trans (e₂ hp).symm) h₁ h₂
    (prod_mono interior_subset le_rfl) ?_
  have h := hd.prod_univ (E' := Fin j → E)
  rwa [HasDenseInterior, interior_prod_eq, interior_univ] at h

end Higher

/-! ### Sufficiency in Lemma 1.4.5 -/

section Sufficiency

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- **Higher differentials on sets with dense interior** ([GN26, Lemma 1.4.5, p. 52], the
sufficiency of the condition, proved on p. 56). Let `U` have dense interior and `f` be continuous
on `U`. If `f|U⁰` is `C^k` and each differential `d^(j) (f|U⁰)`, `j ≤ k`, extends to a continuous
map on `U × E^j`, then `f` is `C^k` on `U`.

Glöckner–Neeb deduce this from the version of Lemma 1.3.12 for sets with dense interior
(Remark 1.4.12). We argue by induction instead: `df` is the extension given by `d^(1) f`, and the
differentials of `d(f|U⁰)` are given on the open set `U⁰ × E` by the explicit formula
`ContDiffMBOn.iteratedDMB_dMB`,
`d^(j)(df)((x, y), (v₁, w₁), …, (vⱼ, wⱼ)) = d^(j+1) f(x, y, v) + ∑ᵢ d^(j) f(x, v₁, …, wᵢ, …, vⱼ)`,
whose right-hand side extends continuously to `(U × E) × (E × E)^j`. -/
theorem contDiffLC_of_extends : ∀ {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {f : E → F} {U : Set E}, HasDenseInterior U → ContinuousOn f U →
    ContDiffMBOn k f (interior U) →
    (∀ j ≤ k, ∃ D : E × (Fin j → E) → F, ContinuousOn D (U ×ˢ univ) ∧
      EqOn D (iteratedDMB j f) (interior U ×ˢ univ)) → ContDiffLC k f U
  | 0, _, _, _, _, _, _, _, _, _, _, _, hc, _, _ => hc
  | k + 1, E, _, _, _, _, _, _, _, f, U, hd, hc, hf, hext => by
    have hO : IsOpen (interior U ×ˢ (univ : Set E)) := isOpen_interior.prod isOpen_univ
    have hint : interior (U ×ˢ (univ : Set E)) = interior U ×ˢ univ := by
      rw [interior_prod_eq, interior_univ]
    have hsub : interior U ×ˢ (univ : Set E) ⊆ U ×ˢ univ := prod_mono interior_subset le_rfl
    -- `df` is the continuous extension of `d(f|U⁰)` given by `d^(1) f`
    obtain ⟨D₁, hD₁c, hD₁e⟩ := hext 1 (by omega)
    have hD₁c' : ContinuousOn (fun p : E × E ↦ D₁ (p.1, fun _ ↦ p.2)) (U ×ˢ univ) :=
      hD₁c.comp (by fun_prop) fun p hp ↦ ⟨hp.1, mem_univ _⟩
    have hdf : EqOn (dLC f U) (fun p : E × E ↦ D₁ (p.1, fun _ ↦ p.2)) (U ×ˢ univ) :=
      dLC_eqOn_of_continuousOn hd hD₁c' fun p hp ↦ hD₁e ⟨hp.1, mem_univ _⟩
    refine ⟨hc, hf.2.1, contDiffLC_of_extends (hd.prod_univ) (hD₁c'.congr hdf) ?_ ?_⟩
    · rw [hint]
      exact ContDiffMBOn.congr_of_isOpen hO (fun p hp ↦ (dLC_eqOn_interior f U hp).symm) hf.2.2
    · intro j hj
      obtain ⟨D, hDc, hDe⟩ := hext (j + 1) (by omega)
      obtain ⟨D', hD'c, hD'e⟩ := hext j (by omega)
      refine ⟨fun q ↦ D (q.1.1, Fin.cons q.1.2 (Prod.fst ∘ q.2)) +
        ∑ i, D' (q.1.1, Function.update (Prod.fst ∘ q.2) i (q.2 i).2), ?_, ?_⟩
      · refine ContinuousOn.add (hDc.comp (by fun_prop) fun q hq ↦ ⟨hq.1.1, mem_univ _⟩)
          (continuousOn_finsetSum _ fun i _ ↦ hD'c.comp ?_ fun q hq ↦ ⟨hq.1.1, mem_univ _⟩)
        refine (continuous_fst.comp continuous_fst).continuousOn.prodMk ?_
        exact (Continuous.update (by fun_prop) i (by fun_prop)).continuousOn
      · rintro ⟨⟨x, y⟩, u⟩ ⟨hx, -⟩
        rw [hint] at hx
        have hev : dLC f U =ᶠ[𝓝 (x, y)] dMB f :=
          (dLC_eqOn_interior f U).eventuallyEq_of_mem (hO.mem_nhds hx)
        rw [iteratedDMB_congr_of_eventuallyEq j hev]
        have := hf.iteratedDMB_dMB isOpen_interior j (by omega) x hx.1 y (Prod.fst ∘ u)
          (Prod.snd ∘ u)
        simp only [Function.comp_apply, Prod.mk.eta] at this
        simp only
        rw [this, hDe ⟨hx.1, mem_univ _⟩]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ hD'e ⟨hx.1, mem_univ _⟩

/-- **[GN26, Lemma 1.4.5]**: on a set with dense interior, `f` is `C^k` if and only if
it is continuous, `f|U⁰` is `C^k`, and the differentials `d^(j) (f|U⁰)`, `j ≤ k`, extend to
continuous maps on `U × E^j` (the extensions are the maps `iteratedDLC j f U`). -/
theorem contDiffLC_iff_extends {k : ℕ} {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {f : E → F} {U : Set E} (hd : HasDenseInterior U) :
    ContDiffLC k f U ↔ ContinuousOn f U ∧ ContDiffMBOn k f (interior U) ∧
      ∀ j ≤ k, ∃ D : E × (Fin j → E) → F, ContinuousOn D (U ×ˢ univ) ∧
        EqOn D (iteratedDMB j f) (interior U ×ˢ univ) :=
  ⟨fun hf ↦ ⟨hf.continuousOn, hf.contDiffMBOn_interior, fun _ hj ↦
    ⟨_, (hf.iteratedDLC_extends.2 _ hj).1, (hf.iteratedDLC_extends.2 _ hj).2⟩⟩,
    fun ⟨hc, hf, hext⟩ ↦ contDiffLC_of_extends hd hc hf hext⟩

end Sufficiency

end LocallyConvex.Analysis

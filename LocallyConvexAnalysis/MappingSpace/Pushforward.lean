/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.MichalBastiani
public import Mathlib.Topology.ContinuousMap.LocallyConvex

/-!
# Superposition operators on spaces of continuous maps

Let `K` be a compact Hausdorff space and `E`, `F` locally convex spaces, and give `C(K, E)` and
`C(K, F)` the compact-open topology. If `g : E → F` is `C^k` in the sense of Michal–Bastiani on
an open set `U ⊆ E`, then the **superposition operator** (pushforward)

  `C(K, g) : C(K, U) → C(K, F)`,  `γ ↦ g ∘ γ`

is `C^k` on the open set `C(K, U)` of continuous maps with values in `U`
([GN26, Proposition 1.7.1]). Its directional derivative is `dC(K, g)(γ, η) = C(K, dg)(γ, η)`,
i.e. `x ↦ dg(γ x, η x)`.

The proof follows Glöckner–Neeb: the derivative comes from Glöckner's lemma on the continuous
extension of difference quotients (`ContDiffMBOn.tendsto_quotient`) and the tube lemma over the
compact space `K`; since the derivative is again a superposition operator, now of `dg` on
`C(K, E × E) ≅ C(K, E) × C(K, E)`, the theorem follows by induction on `k`.

This is the first step towards manifolds of mappings ([GN26, Chapter 4]). No completeness
is assumed.

## Main definitions

* `valuedIn K U`: the set `C(K, U)` of continuous maps `K → E` with values in `U`; it is open
  when `U` is (`isOpen_valuedIn`).
* `pushforward g U`: the superposition operator `γ ↦ g ∘ γ` on `C(K, U)`, for `g` continuous on
  `U` (and `0` elsewhere).
* `prodCLM K E`: the identification `C(K, E) × C(K, E) ≅ C(K, E × E)`, as a continuous linear
  map.

## Main results

* `hasDirDerivAt_pushforward`: for `g` of class `C¹` on `U` and `γ` with values in `U`,
  `dC(K, g)(γ, η) = (x ↦ dg(γ x, η x))`.
* `contDiffMBOn_pushforward`: superposition operators by `C^k` maps are `C^k`
  ([GN26, Proposition 1.7.1]).
* `smoothMBOn_pushforward`: superposition operators by smooth maps are smooth.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  {F : Type u} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

section Defs

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E]

variable (K) in
/-- The continuous maps `K → E` with values in `U`. -/
def valuedIn (U : Set E) : Set C(K, E) :=
  {γ | ∀ x, γ x ∈ U}

omit [T2Space K] [AddCommGroup E] in
/-- The continuous maps with values in an open set form an open set. -/
theorem isOpen_valuedIn {U : Set E} (hU : IsOpen U) : IsOpen (valuedIn K U) := by
  have h : valuedIn K U = {γ : C(K, E) | MapsTo γ univ U} := by
    ext γ
    simp [valuedIn, MapsTo]
  rw [h]
  exact ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ hU

variable (K) in
open scoped Classical in
/-- The superposition operator `γ ↦ g ∘ γ` on the continuous maps with values in `U`, where `g`
is continuous (and `0` elsewhere). -/
def pushforward (g : E → F) (U : Set E) (γ : C(K, E)) : C(K, F) :=
  if h : (∀ x, γ x ∈ U) ∧ ContinuousOn g U then
    ⟨fun x ↦ g (γ x), h.2.comp_continuous γ.continuous h.1⟩
  else 0

omit [CompactSpace K] [T2Space K] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
omit [Module ℝ F] [AddCommGroup E] in
theorem pushforward_apply {g : E → F} {U : Set E} (hg : ContinuousOn g U) {γ : C(K, E)}
    (hγ : γ ∈ valuedIn K U) (x : K) : pushforward K g U γ x = g (γ x) := by
  have h : (∀ x, γ x ∈ U) ∧ ContinuousOn g U := ⟨hγ, hg⟩
  rw [pushforward, dite_eq_left h]
  rfl

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
omit [Module ℝ F] [AddCommGroup E] in
/-- **Superposition operators are continuous.** -/
theorem continuousOn_pushforward {g : E → F} {U : Set E} (hg : ContinuousOn g U) :
    ContinuousOn (pushforward K g U) (valuedIn K U) := by
  refine ContinuousMap.continuousOn_of_continuousOn_uncurry _ ?_
  have heval : Continuous fun p : C(K, E) × K ↦ p.1 p.2 := continuous_eval
  refine (hg.comp heval.continuousOn
    fun p (hp : p ∈ valuedIn K U ×ˢ (univ : Set K)) ↦ hp.1 p.2).congr fun p hp ↦ ?_
  exact pushforward_apply hg hp.1 p.2

end Defs

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

variable (K E) in
/-- `(γ, η) ↦ (x ↦ (γ x, η x))`, the identification `C(K, E) × C(K, E) ≅ C(K, E × E)`, as a
continuous linear map. -/
def prodCLM : C(K, E) × C(K, E) →L[ℝ] C(K, E × E) where
  toFun p := p.1.prodMk p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_of_continuous_uncurry _ <| by
    have h1 : Continuous fun q : (C(K, E) × C(K, E)) × K ↦ q.1.1 q.2 :=
      continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)
    have h2 : Continuous fun q : (C(K, E) × C(K, E)) × K ↦ q.1.2 q.2 :=
      continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)
    exact h1.prodMk h2

omit [T2Space K] [LocallyConvexSpace ℝ E] [T2Space E] in
theorem prodCLM_apply (γ η : C(K, E)) (x : K) : prodCLM K E (γ, η) x = (γ x, η x) :=
  rfl

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **The derivative of a superposition operator**: for `g` of class `C¹` on `U` and `γ` with
values in `U`, `dC(K, g)(γ, η) = (x ↦ dg(γ x, η x))`. -/
theorem hasDirDerivAt_pushforward {g : E → F} {U : Set E} (hU : IsOpen U)
    (hg : ContDiffMBOn 1 g U) {γ : C(K, E)} (hγ : γ ∈ valuedIn K U) (η : C(K, E)) :
    HasDirDerivAt (pushforward K g U) γ η
      (pushforward K (dMB g) (U ×ˢ univ) (prodCLM K E (γ, η))) := by
  have hgc : ContinuousOn g U := hg.continuousOn
  have hdg : ContinuousOn (dMB g) (U ×ˢ univ) := (hg.2.2 : ContDiffMBOn 0 _ _)
  have hγη : prodCLM K E (γ, η) ∈ valuedIn K (U ×ˢ univ) := fun x ↦ ⟨hγ x, mem_univ _⟩
  -- for small `t`, `γ + t η` still has values in `U`
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, γ + t • η ∈ valuedIn K U := by
    have hc : Continuous fun t : ℝ ↦ γ + t • η := by fun_prop
    have := hc.tendsto 0
    simp only [zero_smul, add_zero] at this
    exact this.eventually ((isOpen_valuedIn hU).mem_nhds hγ)
  rw [HasDirDerivAt, ContinuousMap.tendsto_nhds_compactOpen]
  intro L hL V hV hLV
  -- pointwise, by Glöckner's lemma, the difference quotients enter `V`
  have hpt : ∀ x ∈ L, ∀ᶠ z : ℝ × K in 𝓝 (0, x),
      z.1 ≠ 0 → z.1⁻¹ • (g (γ z.2 + z.1 • η z.2) - g (γ z.2)) ∈ V := by
    intro x hx
    have hDx : pushforward K (dMB g) (U ×ˢ univ) (prodCLM K E (γ, η)) x = dMB g (γ x, η x) :=
      pushforward_apply hdg hγη x
    have hq := hg.tendsto_quotient hU (hγ x) (v := η x)
    have hev : ∀ᶠ p : E × E × ℝ in 𝓝 (γ x, η x, 0),
        p.2.2 ≠ 0 → p.2.2⁻¹ • (g (p.1 + p.2.2 • p.2.1) - g p.1) ∈ V :=
      eventually_nhdsWithin_iff.1 (hq (hV.mem_nhds (hDx ▸ hLV hx)))
    have hψ : Continuous fun z : ℝ × K ↦ (γ z.2, η z.2, z.1) := by fun_prop
    have := (hψ.tendsto (0, x)).eventually hev
    simpa using this
  have htube := hL.eventually_forall_of_forall_eventually
    (P := fun t x ↦ t ≠ 0 → t⁻¹ • (g (γ x + t • η x) - g (γ x)) ∈ V) hpt
  have hne : ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds htube, nhdsWithin_le_nhds hsmall, hne] with t ht hts ht0
  intro x hx
  have hval : (t⁻¹ • (pushforward K g U (γ + t • η) - pushforward K g U γ)) x =
      t⁻¹ • (g (γ x + t • η x) - g (γ x)) := by
    simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, pushforward_apply hgc hts,
      pushforward_apply hgc hγ, ContinuousMap.add_apply]
  rw [hval]
  exact ht x hx ht0

/-- **Superposition operators by `C^k` maps are `C^k`** ([GN26, Proposition 1.7.1]). -/
theorem contDiffMBOn_pushforward : ∀ (k : ℕ) {E : Type u} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [T2Space E] {g : E → F} {U : Set E}, IsOpen U → ContDiffMBOn k g U →
      ContDiffMBOn k (pushforward K g U) (valuedIn K U) := by
  intro k
  induction k with
  | zero =>
    intro E _ _ _ _ _ _ _ g U _ hg
    exact continuousOn_pushforward hg
  | succ k ih =>
    intro E _ _ _ _ _ _ _ g U hU hg
    have hg1 : ContDiffMBOn 1 g U := hg.of_le (by omega)
    have hdg : ContDiffMBOn k (dMB g) (U ×ˢ univ) := hg.2.2
    have hD : ∀ γ ∈ valuedIn K U, ∀ η, dMB (pushforward K g U) (γ, η) =
        pushforward K (dMB g) (U ×ˢ univ) (prodCLM K E (γ, η)) := fun γ hγ η ↦
      (hasDirDerivAt_pushforward hU hg1 hγ η).dMB_eq
    refine ⟨continuousOn_pushforward hg.continuousOn, fun γ hγ η ↦ ?_, ?_⟩
    · rw [hD γ hγ η]
      exact hasDirDerivAt_pushforward hU hg1 hγ η
    · have hS : IsOpen (valuedIn K U ×ˢ (univ : Set C(K, E))) :=
        (isOpen_valuedIn hU).prod isOpen_univ
      have hpre : (prodCLM K E) ⁻¹' valuedIn K (U ×ˢ univ) = valuedIn K U ×ˢ univ := by
        ext p
        exact ⟨fun h ↦ ⟨fun x ↦ (h x).1, mem_univ _⟩, fun h x ↦ ⟨h.1 x, mem_univ _⟩⟩
      have h := ContDiffMBOn.comp_clm (prodCLM K E) (isOpen_valuedIn (hU.prod isOpen_univ))
        (ih (hU.prod isOpen_univ) hdg)
      rw [hpre] at h
      exact ContDiffMBOn.congr_of_isOpen hS (fun p hp ↦ (hD p.1 hp.1 p.2).symm) h

/-- **Superposition operators by smooth maps are smooth.** -/
theorem smoothMBOn_pushforward {g : E → F} {U : Set E} (hU : IsOpen U) (hg : SmoothMBOn g U) :
    SmoothMBOn (pushforward K g U) (valuedIn K U) :=
  fun k ↦ contDiffMBOn_pushforward k hU (hg k)

end LocallyConvex.Analysis

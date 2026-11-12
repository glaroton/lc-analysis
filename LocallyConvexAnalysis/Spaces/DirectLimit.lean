/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.LocallyConvex.Barrelled

/-!
# Locally convex direct limits

Reference: [GN26, Appendix B.13] (pp. 945–949).

Let `V` be a real vector space and `S n ⊆ V` subspaces, each with a topology. The **locally
convex direct limit topology** on `V` (`LCDirectLimit S`) is defined by all seminorms `p` on `V`
whose restrictions to every `S n` are continuous ([GN26, Definition B.13.4]). It need not
be Hausdorff. We prove its basic properties (Remark B.13.5, Lemmas B.13.6 and B.13.8) and the
properties of strict direct limits (Proposition B.13.9).

## Main definitions

* `LCDirectLimit S`: `V` with the locally convex direct limit topology of the subspaces `S n`
  ([GN26, Definition B.13.4]).
* `LCDirectLimit.AdmissibleSeminorm S`: the seminorms on `V` whose restrictions to all `S n` are
  continuous; they define the topology.
* `LCDirectLimit.incl S n`: the inclusion `S n → V`, as a linear map.
* `LCDirectLimit.IsStrict S`: `S₀ ⊆ S₁ ⊆ ⋯` covering `V`, each `S n` carrying the topology
  induced by `S (n + 1)` (a strict direct sequence).

## Main results

* `LCDirectLimit.continuous_incl`: the inclusions `S n → V` are continuous (Remark B.13.5(a)).
* `LCDirectLimit.continuous_of_continuous_comp_incl`: **the universal property**: a linear map to
  a locally convex space is continuous as soon as its restrictions to the `S n` are
  (Remark B.13.5(d)). In particular, the topology is the finest locally convex vector topology
  making the inclusions continuous (Remark B.13.5(b)).
* `LCDirectLimit.t2Space_of_injective`: the Hausdorff criterion of Remark B.13.5(e).
* `LCDirectLimit.mem_nhds_zero_iff_of_convex`: a convex set containing `0` is a `0`-neighbourhood
  as soon as its traces on the `S n` are (Lemma B.13.6(a)).
* `LCDirectLimit.isOpen_iff_of_convex`: for an ascending sequence, a convex set is open as soon as
  its traces are (Lemma B.13.6(b)); `LCDirectLimit.barrelledSpace`: barrelled steps give a
  barrelled limit (Lemma B.13.6(e)). Lemma B.13.6(c), (d) are in `Spaces/DirectLimitQuotient.lean`.
* `exists_absConvex_isOpen_preimage_eq`: absolutely convex open sets of a subspace extend to
  absolutely convex open sets of the whole space (Lemma B.13.8).
* **Strict direct limits** (Proposition B.13.9):
  `LCDirectLimit.IsStrict.isEmbedding_incl`: the limit induces the given topology on each `S n`
  (a); `LCDirectLimit.IsStrict.t2Space`: the limit is Hausdorff (b);
  `LCDirectLimit.IsStrict.exists_subset_isVonNBounded`,
  `LCDirectLimit.IsStrict.exists_subset_isCompact`: if each `S n` is closed in `S (n + 1)`,
  bounded (compact) sets lie, and are bounded (compact), in some `S n` (c);
  `LCDirectLimit.IsStrict.completeSpace`: the strict direct limit of complete spaces is
  complete (d); `LCDirectLimit.IsStrict.quasiCompleteSpace`,
  `LCDirectLimit.IsStrict.exists_tendsto_of_cauchySeq`: with closed steps, quasi-completeness and
  sequential completeness pass to the limit (e).

## Implementation notes

* Glöckner–Neeb consider an ascending sequence `E₁ ⊆ E₂ ⊆ ⋯` with continuous inclusions and
  `E = ⋃ₙ Eₙ`. The basic statements hold for any family of subspaces; Lemma B.13.6(a) needs the
  covering property, and strict direct limits are indexed by `ℕ`.
* Only real scalars: the universal property uses the gauge seminorms of the target, and the
  complex spaces of this library are locally convex over `ℝ`.
* The Mackey complete case of Proposition B.13.9(e) is `IsStrict.mackeyComplete`, in
  `Spaces/DirectCompleteness.lean`. Direct systems indexed by preordered sets with a cofinal
  subsequence reduce to sequences (`topology_eq_comp`, Remark B.13.10).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function Bornology
open scoped Topology Pointwise
open Topology

noncomputable section

namespace LocallyConvex.Analysis

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

set_option linter.unusedVariables false in
/-- `V` with the locally convex direct limit topology of the subspaces `S n`. -/
@[nolint unusedArguments]
def LCDirectLimit {ι : Type*} (S : ι → Submodule ℝ V) : Type _ := V

namespace LCDirectLimit

variable {ι : Type*} (S : ι → Submodule ℝ V)

instance : AddCommGroup (LCDirectLimit S) := inferInstanceAs (AddCommGroup V)

instance : Module ℝ (LCDirectLimit S) := inferInstanceAs (Module ℝ V)

variable [∀ n, TopologicalSpace (S n)]

/-- The seminorms on `V` whose restrictions to all `S n` are continuous. -/
def AdmissibleSeminorm : Type _ :=
  {p : Seminorm ℝ (LCDirectLimit S) // ∀ n, Continuous fun v : S n ↦ p (v : V)}

/-- The family of admissible seminorms. -/
def seminormFamily : SeminormFamily ℝ (LCDirectLimit S) (AdmissibleSeminorm S) := fun p ↦ p.1

/-- The locally convex direct limit topology ([GN26, Definition B.13.4]). -/
instance : TopologicalSpace (LCDirectLimit S) := (seminormFamily S).moduleFilterBasis.topology

theorem withSeminorms : WithSeminorms (seminormFamily S) := ⟨rfl⟩

instance : IsTopologicalAddGroup (LCDirectLimit S) := (withSeminorms S).isTopologicalAddGroup

instance : ContinuousSMul ℝ (LCDirectLimit S) := (withSeminorms S).continuousSMul

instance : LocallyConvexSpace ℝ (LCDirectLimit S) := (withSeminorms S).toLocallyConvexSpace

/-- The uniform structure of the topological group `LCDirectLimit S`. -/
instance : UniformSpace (LCDirectLimit S) := IsTopologicalAddGroup.rightUniformSpace _

instance : IsUniformAddGroup (LCDirectLimit S) := isUniformAddGroup_of_addCommGroup

/-- The inclusion `S n → V`. -/
def incl (n : ι) : S n →ₗ[ℝ] LCDirectLimit S := (S n).subtype

omit [∀ n, TopologicalSpace (S n)] in
@[simp] theorem incl_apply (n : ι) (v : S n) : incl S n v = (v : V) := rfl

/-- **The inclusions are continuous** ([GN26, Remark B.13.5(a)]). -/
theorem continuous_incl [∀ n, IsTopologicalAddGroup (S n)] (n : ι) : Continuous (incl S n) :=
  (withSeminorms S).continuous_of_continuous_comp (incl S n) fun p ↦ p.2 n

/-- **The universal property** ([GN26, Remark B.13.5(d)]): a linear map from the
locally convex direct limit to a locally convex space is continuous as soon as its restrictions
to the subspaces `S n` are. -/
theorem continuous_of_continuous_comp_incl {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]
    (f : LCDirectLimit S →ₗ[ℝ] F) (hf : ∀ n, Continuous (f ∘ₗ incl S n)) : Continuous f :=
  (with_gaugeSeminormFamily (𝕜 := ℝ) (E := F)).continuous_of_continuous_comp f fun s ↦
    (withSeminorms S).continuous_seminorm ⟨(gaugeSeminormFamily ℝ F s).comp f,
      fun n ↦ ((with_gaugeSeminormFamily (𝕜 := ℝ) (E := F)).continuous_seminorm s).comp (hf n)⟩

/-- **Direct systems with a cofinal subsequence** ([GN26, Remark B.13.10]): if the
subspaces `S i` are indexed by a preordered set, increase with continuous inclusions, and `φ` is
cofinal, the locally convex direct limit topologies of `S` and `S ∘ φ` agree. The identity is
continuous in both directions by the universal property, since each `S i` lies in some `S (φ k)`
with continuous inclusion. -/
theorem topology_eq_comp [Preorder ι] [∀ i, IsTopologicalAddGroup (S i)] (hmono : Monotone S)
    (hcont : ∀ {i j} (h : i ≤ j), Continuous (Submodule.inclusion (hmono h))) {κ : Type*}
    (φ : κ → ι) (hφ : ∀ i, ∃ k, i ≤ φ k) :
    (inferInstanceAs (TopologicalSpace (LCDirectLimit S)) : TopologicalSpace V) =
      inferInstanceAs (TopologicalSpace (LCDirectLimit fun k ↦ S (φ k))) := by
  let f : LCDirectLimit S →ₗ[ℝ] LCDirectLimit fun k ↦ S (φ k) := LinearMap.id
  let g : (LCDirectLimit fun k ↦ S (φ k)) →ₗ[ℝ] LCDirectLimit S := LinearMap.id
  have hf : Continuous f := continuous_of_continuous_comp_incl S f fun i ↦ by
    obtain ⟨k, hk⟩ := hφ i
    exact (continuous_incl (fun k ↦ S (φ k)) k).comp (hcont hk)
  have hg : Continuous g := continuous_of_continuous_comp_incl _ g fun k ↦
    continuous_incl S (φ k)
  exact le_antisymm (continuous_id_iff_le.1 hf) (continuous_id_iff_le.1 hg)

/-- **The Hausdorff criterion** ([GN26, Remark B.13.5(e)]): if an injective linear map to
a Hausdorff locally convex space is continuous on each `S n`, the direct limit is Hausdorff. -/
theorem t2Space_of_injective {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
    (f : LCDirectLimit S →ₗ[ℝ] F) (hinj : Injective f) (hf : ∀ n, Continuous (f ∘ₗ incl S n)) :
    T2Space (LCDirectLimit S) :=
  T2Space.of_injective_continuous hinj (continuous_of_continuous_comp_incl S f hf)

/-- **Convex `0`-neighbourhoods** ([GN26, Lemma B.13.6(a)]): if the subspaces `S n` cover
`V`, a convex set `U ∋ 0` is a `0`-neighbourhood of the direct limit as soon as its traces on all
the `S n` are `0`-neighbourhoods. -/
theorem mem_nhds_zero_iff_of_convex [∀ n, IsTopologicalAddGroup (S n)]
    [∀ n, ContinuousSMul ℝ (S n)] (hcover : ∀ v : V, ∃ n, v ∈ S n) {U : Set (LCDirectLimit S)}
    (hU : Convex ℝ U) (h0 : (0 : LCDirectLimit S) ∈ U) :
    U ∈ 𝓝 (0 : LCDirectLimit S) ↔ ∀ n, incl S n ⁻¹' U ∈ 𝓝 (0 : S n) := by
  constructor
  · intro hU' n
    exact (continuous_incl S n).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU')
  · intro h
    set U' := U ∩ -U
    have hU'c : Convex ℝ U' := hU.inter hU.neg
    have hU'b : Balanced ℝ U' := (balanced_iff_neg_mem hU'c).2 fun x hx ↦
      ⟨hx.2, by simpa [Set.mem_neg] using hx.1⟩
    have hpre : ∀ n, incl S n ⁻¹' U' ∈ 𝓝 (0 : S n) := fun n ↦ by
      rw [Set.preimage_inter]
      refine inter_mem (h n) ?_
      have e : incl S n ⁻¹' (-U) = -(incl S n ⁻¹' U) := by
        ext v
        simp only [Set.mem_preimage, Set.mem_neg, map_neg]
      rw [e]
      exact neg_mem_nhds_zero _ (h n)
    have hU'a : Absorbent ℝ U' := by
      intro v
      obtain ⟨n, hn⟩ := hcover v
      have ha : Absorbs ℝ (incl S n ⁻¹' U') {⟨v, hn⟩} := absorbent_nhds_zero (hpre n) _
      unfold Absorbs at ha ⊢
      filter_upwards [ha] with a ha'
      rintro _ rfl
      obtain ⟨w, hw, hwv⟩ := ha' rfl
      exact ⟨incl S n w, hw, by beta_reduce at hwv ⊢; rw [← map_smul, hwv]; rfl⟩
    set p := gaugeSeminorm hU'b hU'c hU'a
    have hp : ∀ n, Continuous fun v : S n ↦ p (v : V) := fun n ↦ by
      have : Continuous (p.comp (incl S n)) := Seminorm.continuous' (r := 1)
        (mem_of_superset (hpre n) fun v hv ↦ by
          rw [Seminorm.mem_closedBall_zero]
          exact gauge_le_one_of_mem hv)
      exact this
    have hpc : Continuous p := (withSeminorms S).continuous_seminorm ⟨p, hp⟩
    refine mem_of_superset ((isOpen_lt hpc (continuous_const (y := (1 : ℝ)))).mem_nhds (by simp))
      fun v hv ↦ ?_
    exact (setOfPred_gauge_lt_one_subset_self hU'c ⟨h0, by simpa [Set.mem_neg] using h0⟩ hU'a
      hv).1

/-- **Barrelled steps give a barrelled limit** ([GN26, Lemma B.13.6(e)]): a lower
semicontinuous seminorm on the direct limit restricts to lower semicontinuous, hence continuous,
seminorms on the barrelled steps, so it is one of the seminorms defining the topology. -/
theorem barrelledSpace [∀ n, IsTopologicalAddGroup (S n)] [∀ n, BarrelledSpace ℝ (S n)] :
    BarrelledSpace ℝ (LCDirectLimit S) where
  continuous_of_lowerSemicontinuous p hp :=
    (withSeminorms S).continuous_seminorm ⟨p, fun n ↦
      (p.comp (incl S n)).continuous_of_lowerSemicontinuous
        (hp.comp (continuous_incl S n))⟩

/-- **Convex open sets** ([GN26, Lemma B.13.6(b)]): for an ascending sequence of
subspaces covering `V`, with continuous inclusions, a convex set is open in the direct limit as
soon as its traces on all the steps are open. Translate to a point `x ∈ S m` and apply
Lemma B.13.6(a) (`mem_nhds_zero_iff_of_convex`). -/
theorem isOpen_iff_of_convex {S : ℕ → Submodule ℝ V} [∀ n, TopologicalSpace (S n)]
    [∀ n, IsTopologicalAddGroup (S n)] [∀ n, ContinuousSMul ℝ (S n)] (hmono : Monotone S)
    (hcont : ∀ {m n : ℕ} (h : m ≤ n), Continuous (Submodule.inclusion (hmono h)))
    (hcover : ∀ v : V, ∃ n, v ∈ S n) {U : Set (LCDirectLimit S)} (hU : Convex ℝ U) :
    IsOpen U ↔ ∀ n, IsOpen (incl S n ⁻¹' U) := by
  refine ⟨fun h n ↦ h.preimage (continuous_incl S n), fun h ↦ ?_⟩
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  obtain ⟨m, hm⟩ := hcover x
  set U' : Set (LCDirectLimit S) := (fun v ↦ x + v) ⁻¹' U
  have hU' : Convex ℝ U' := hU.translate_preimage_right x
  have h0 : (0 : LCDirectLimit S) ∈ U' := by simpa [U'] using hx
  have htr : ∀ n, incl S n ⁻¹' U' ∈ 𝓝 (0 : S n) := by
    intro n
    set k := max m n
    have hxk : x ∈ S k := hmono (le_max_left m n) hm
    -- the trace on `S k` is open, by translation
    have hA : IsOpen {y : S k | x + incl S k y ∈ U} :=
      (h k).preimage (continuous_const.add continuous_id : Continuous fun y : S k ↦ ⟨x, hxk⟩ + y)
    have hAn := hA.preimage (hcont (le_max_right m n))
    refine hAn.mem_nhds ?_
    rw [mem_preimage, map_zero]
    change x + incl S k 0 ∈ U
    rw [map_zero, add_zero]
    exact hx
  have hW := (mem_nhds_zero_iff_of_convex S hcover hU' h0).2 htr
  rw [← map_add_left_nhds_zero x]
  exact hW

end LCDirectLimit

/-- **Extension of absolutely convex open sets** ([GN26, Lemma B.13.8]): if `j : F → E`
is an injective linear topological embedding into a locally convex space, every absolutely convex
open set `V ⊆ F` is the preimage of an absolutely convex open set `Q ⊆ E`. As in Glöckner–Neeb,
`Q` is the convex join of `j(V)` and an absolutely convex open `0`-neighbourhood `W` of `E` whose
trace on `F` lies in `V`; we check openness directly, through the open sets `a • j v + b • W`. -/
theorem exists_absConvex_isOpen_preimage_eq {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousSMul ℝ F] (j : F →ₗ[ℝ] E)
    (hj : IsInducing j) (hinj : Injective j) {V : Set F} (hVo : IsOpen V) (hV : AbsConvex ℝ V) :
    ∃ Q : Set E, IsOpen Q ∧ AbsConvex ℝ Q ∧ j ⁻¹' Q = V := by
  rcases V.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, isOpen_empty, AbsConvex.empty, preimage_empty⟩
  obtain ⟨P, hPo, hPV⟩ := hj.isOpen_iff.1 hVo
  have hV0 : (0 : F) ∈ V := hV.1.zero_mem hne
  have hP0 : (0 : E) ∈ P := by
    rw [← map_zero j, ← mem_preimage, hPV]
    exact hV0
  obtain ⟨W, ⟨hW0, hWo, hWac⟩, hWP⟩ := (nhds_hasBasis_absConvex_open ℝ E).mem_iff.1
    (hPo.mem_nhds hP0)
  set Q := convexJoin ℝ (j '' V) W
  -- the open pieces `a • j v + b • W`
  have hpiece : ∀ v ∈ V, ∀ a b : ℝ, 0 ≤ a → 0 < b → a + b = 1 →
      IsOpen ((a • j v) +ᵥ b • W) ∧ (a • j v) +ᵥ b • W ⊆ Q := by
    intro v hv a b ha hb hab
    refine ⟨(hWo.smul₀ hb.ne').vadd _, ?_⟩
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact mem_convexJoin.2 ⟨j v, ⟨v, hv, rfl⟩, w, hw, a, b, ha, hb.le, hab, rfl⟩
  refine ⟨Q, ?_, ⟨?_, (hV.2.linear_image j).convexJoin hWac.2⟩, ?_⟩
  · refine isOpen_iff_forall_mem_open.2 ?_
    intro q hq
    obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, a, b, ha, hb, hab, rfl⟩ := mem_convexJoin.1 hq
    rcases hb.lt_or_eq with hb | rfl
    · exact ⟨_, (hpiece v hv a b ha hb hab).2, (hpiece v hv a b ha hb hab).1,
        ⟨b • w, smul_mem_smul_set hw, rfl⟩⟩
    · rw [add_zero] at hab
      subst hab
      -- `j v = r⁻¹ • j (r • v) + (1 - r⁻¹) • 0` for some `r > 1` with `r • v ∈ V`
      have hev : ∀ᶠ r in 𝓝 (1 : ℝ), r • v ∈ V :=
        (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
          (by simpa using hVo.mem_nhds hv)
      obtain ⟨r, hrV, hr⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))).exists
      have hr0 : 0 < r := zero_lt_one.trans hr
      have hb : 0 < 1 - r⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hr)
      obtain ⟨hO, hOQ⟩ := hpiece _ hrV r⁻¹ (1 - r⁻¹) (inv_nonneg.2 hr0.le) hb (by ring)
      refine ⟨_, hOQ, hO, ⟨0, ⟨0, hW0, smul_zero _⟩, ?_⟩⟩
      simp [map_smul, smul_smul, inv_mul_cancel₀ hr0.ne']
  · intro c hc
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, a, b, ha, hb, hab, rfl⟩ := mem_convexJoin.1 hq
    refine mem_convexJoin.2 ⟨j (c • v), ⟨c • v, hV.1 c hc (smul_mem_smul_set hv), rfl⟩, c • w,
      hWac.1 c hc (smul_mem_smul_set hw), a, b, ha, hb, hab, ?_⟩
    simp only [map_smul, smul_add, smul_comm c]
  · ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ subset_convexJoin_left ⟨0, hW0⟩ ⟨x, hx, rfl⟩⟩
    obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, a, b, ha, hb, hab, hx⟩ := mem_convexJoin.1 hx
    rcases hb.lt_or_eq with hb | rfl
    · -- `w = j y` with `y = b⁻¹ • (x - a • v)`, so `y ∈ j⁻¹(P) = V`
      have hy : j (b⁻¹ • (x - a • v)) = w := by
        rw [map_smul, map_sub, ← hx, map_smul, add_sub_cancel_left, smul_smul,
          inv_mul_cancel₀ hb.ne', one_smul]
      have hyV : b⁻¹ • (x - a • v) ∈ V := by
        rw [← hPV, mem_preimage, hy]
        exact hWP hw
      have := hV.2 hv hyV ha hb.le hab
      rwa [smul_smul, mul_inv_cancel₀ hb.ne', one_smul, add_sub_cancel] at this
    · rw [add_zero] at hab
      subst hab
      rw [one_smul, zero_smul, add_zero] at hx
      rwa [← hinj hx]

namespace LCDirectLimit

/-! ### Strict direct limits -/

section Strict

variable (S : ℕ → Submodule ℝ V) [∀ n, TopologicalSpace (S n)]

/-- A **strict direct sequence** ([GN26, before Definition B.13.7], and Definition A.7.1):
an ascending sequence of subspaces covering `V`, each carrying the topology induced by the next
one. -/
structure IsStrict : Prop where
  mono : Monotone S
  exists_mem : ∀ v : V, ∃ n, v ∈ S n
  isInducing_succ : ∀ n, IsInducing (Submodule.inclusion (mono (Nat.le_succ n)))

variable {S}

/-- In a strict direct sequence, each `S m` carries the topology induced by every `S n`,
`m ≤ n`. -/
theorem IsStrict.isInducing_inclusion (hS : IsStrict S) {m n : ℕ} (h : m ≤ n) :
    IsInducing (Submodule.inclusion (hS.mono h)) := by
  induction n, h using Nat.le_induction with
  | base => exact IsInducing.id
  | succ n hmn ih => exact (hS.isInducing_succ n).comp ih

variable [∀ n, IsTopologicalAddGroup (S n)] [∀ n, ContinuousSMul ℝ (S n)]
  [∀ n, LocallyConvexSpace ℝ (S n)]

/-- **Extension to the strict direct limit**: an absolutely convex open `0`-neighbourhood of
`S m` is the trace of a `0`-neighbourhood `W` of the strict direct limit. This is the construction
in the proof of [GN26, Proposition B.13.9(a)]: extend it step by step with Lemma B.13.8 and
take the union. At each step `S n → S (n + 1)`, `n ≥ m`, the extension may be cut down by a
prescribed absolutely convex open set `C n ⊇ S n`, as in the proof of Proposition B.13.9(c). -/
theorem IsStrict.exists_mem_nhds_preimage_eq_of_subset (hS : IsStrict S) (m : ℕ)
    {U₀ : Set (S m)} (h0 : (0 : S m) ∈ U₀) (hU₀ : IsOpen U₀) (hU₀c : AbsConvex ℝ U₀)
    (C : ∀ n, Set (S (n + 1))) (hCo : ∀ n, IsOpen (C n)) (hCc : ∀ n, AbsConvex ℝ (C n))
    (hCS : ∀ n x, Submodule.inclusion (hS.mono (Nat.le_succ n)) x ∈ C n) :
    ∃ W ∈ 𝓝 (0 : LCDirectLimit S), incl S m ⁻¹' W = U₀ ∧
      ∀ n, m ≤ n → incl S (n + 1) ⁻¹' W ⊆ C n := by
  -- one extension step `S (m + k) → S (m + (k + 1))`
  have hext : ∀ k (A : Set (S (m + k))), (0 : S (m + k)) ∈ A ∧ IsOpen A ∧ AbsConvex ℝ A →
      ∃ Q : Set (S (m + (k + 1))), ((0 : S (m + (k + 1))) ∈ Q ∧ IsOpen Q ∧ AbsConvex ℝ Q) ∧
        Submodule.inclusion (hS.mono (m + k).le_succ) ⁻¹' Q = A ∧ Q ⊆ C (m + k) :=
      fun k A hA ↦ by
    obtain ⟨Q, hQo, hQc, hQA⟩ := exists_absConvex_isOpen_preimage_eq _
      (hS.isInducing_succ (m + k)) (Submodule.inclusion_injective _) hA.2.1 hA.2.2
    refine ⟨Q ∩ C (m + k), ⟨⟨?_, ?_⟩, hQo.inter (hCo _), hQc.inter (hCc _)⟩, ?_,
      inter_subset_right⟩
    · have : (0 : S (m + k)) ∈ Submodule.inclusion (hS.mono (m + k).le_succ) ⁻¹' Q :=
        hQA ▸ hA.1
      simpa using this
    · simpa using hCS (m + k) 0
    · rw [preimage_inter, hQA]
      exact inter_eq_left.2 fun x _ ↦ hCS (m + k) x
  let seq : ∀ k, {A : Set (S (m + k)) // (0 : S (m + k)) ∈ A ∧ IsOpen A ∧ AbsConvex ℝ A} :=
    fun k ↦ Nat.rec (motive := fun k ↦
        {A : Set (S (m + k)) // (0 : S (m + k)) ∈ A ∧ IsOpen A ∧ AbsConvex ℝ A})
      ⟨U₀, h0, hU₀, hU₀c⟩ (fun k A ↦ ⟨(hext k A.1 A.2).choose, (hext k A.1 A.2).choose_spec.1⟩) k
  have hstep : ∀ k, Submodule.inclusion (hS.mono (m + k).le_succ) ⁻¹' (seq (k + 1)).1 =
      (seq k).1 := fun k ↦ (hext k (seq k).1 (seq k).2).choose_spec.2.1
  have hsubC : ∀ k, (seq (k + 1)).1 ⊆ C (m + k) := fun k ↦
    (hext k (seq k).1 (seq k).2).choose_spec.2.2
  -- compatibility of the whole sequence
  have hcompat : ∀ k l (hkl : k ≤ l) (x : S (m + k)),
      Submodule.inclusion (hS.mono (Nat.add_le_add_left hkl m)) x ∈ (seq l).1 ↔
        x ∈ (seq k).1 := by
    intro k l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact fun x ↦ Iff.rfl
    | succ l hkl ih =>
      intro x
      rw [← ih x, ← hstep l]
      exact Iff.rfl
  set W : Set (LCDirectLimit S) := ⋃ k, Subtype.val '' (seq k).1
  have hW : ∀ k (x : S (m + k)), (x : V) ∈ W ↔ x ∈ (seq k).1 := by
    intro k x
    refine ⟨fun hx ↦ ?_, fun hx ↦ mem_iUnion.2 ⟨k, x, hx, rfl⟩⟩
    obtain ⟨l, y, hy, hyx⟩ := mem_iUnion.1 hx
    rw [← hcompat k (max k l) (le_max_left _ _)]
    have := (hcompat l (max k l) (le_max_right _ _) y).2 hy
    convert this using 1
    exact Subtype.ext hyx.symm
  have hconv : Convex ℝ W := by
    refine Directed.convex_iUnion (Monotone.directed_le fun k l hkl ↦ ?_) fun k ↦
      (seq k).2.2.2.2.linear_image (S (m + k)).subtype
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, (hcompat k l hkl x).2 hx, rfl⟩
  have h0W : (0 : LCDirectLimit S) ∈ W := mem_iUnion.2 ⟨0, (0 : S m), (seq 0).2.1, rfl⟩
  refine ⟨W, (mem_nhds_zero_iff_of_convex S hS.exists_mem hconv h0W).2 fun n ↦ ?_, ?_⟩
  · have hpre : incl S n ⁻¹' W =
        Submodule.inclusion (hS.mono (Nat.le_add_left n m)) ⁻¹' (seq n).1 := by
      ext x
      exact hW n (Submodule.inclusion _ x)
    rw [hpre]
    refine ((hS.isInducing_inclusion (Nat.le_add_left n m)).continuous.isOpen_preimage _
      (seq n).2.2.1).mem_nhds ?_
    rw [mem_preimage, map_zero]
    exact (seq n).2.1
  · refine ⟨Set.ext fun x ↦ hW 0 x, fun n hn x hx ↦ ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hsubC k ((hW (k + 1) x).1 hx)

/-- An absolutely convex open `0`-neighbourhood of `S m` is the trace of a `0`-neighbourhood of
the strict direct limit ([GN26, proof of Proposition B.13.9(a)]). -/
theorem IsStrict.exists_mem_nhds_preimage_eq (hS : IsStrict S) (m : ℕ) {U₀ : Set (S m)}
    (h0 : (0 : S m) ∈ U₀) (hU₀ : IsOpen U₀) (hU₀c : AbsConvex ℝ U₀) :
    ∃ W ∈ 𝓝 (0 : LCDirectLimit S), incl S m ⁻¹' W = U₀ := by
  obtain ⟨W, hW, hWU, -⟩ := hS.exists_mem_nhds_preimage_eq_of_subset m h0 hU₀ hU₀c
    (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ ⟨balanced_univ, convex_univ⟩)
    (fun _ _ ↦ mem_univ _)
  exact ⟨W, hW, hWU⟩

/-- **The steps of a strict direct limit are embedded** ([GN26, Proposition B.13.9(a)]):
the strict direct limit induces the given topology on each `S n`. -/
theorem IsStrict.isEmbedding_incl (hS : IsStrict S) (m : ℕ) : IsEmbedding (incl S m) := by
  refine ⟨IsTopologicalAddGroup.isInducing_iff_nhds_zero.2 (le_antisymm ?_ ?_),
    Subtype.val_injective⟩
  · have := (continuous_incl S m).tendsto 0
    rw [map_zero] at this
    exact this.le_comap
  · intro N hN
    obtain ⟨U₀, ⟨h0, hU₀, hU₀c⟩, hU₀N⟩ := (nhds_hasBasis_absConvex_open ℝ (S m)).mem_iff.1 hN
    obtain ⟨W, hW, hWU⟩ := hS.exists_mem_nhds_preimage_eq m h0 hU₀ hU₀c
    exact mem_comap.2 ⟨W, hW, hWU ▸ hU₀N⟩

/-- **Strict direct limits are Hausdorff** ([GN26, Proposition B.13.9(b)]). -/
theorem IsStrict.t2Space [∀ n, T1Space (S n)] (hS : IsStrict S) : T2Space (LCDirectLimit S) := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := hS.exists_mem x
  have hN : ({⟨x, hn⟩}ᶜ : Set (S n)) ∈ 𝓝 0 :=
    compl_singleton_mem_nhds fun h ↦ hx (congrArg Subtype.val h).symm
  rw [(hS.isEmbedding_incl n).isInducing.nhds_eq_comap, map_zero] at hN
  obtain ⟨W, hW, hWN⟩ := mem_comap.1 hN
  exact ⟨W, hW, fun hxW ↦ hWN (show incl S n ⟨x, hn⟩ ∈ W from hxW) rfl⟩

/-- **Strict direct limits with closed steps are boundedly regular**
([GN26, Definition B.13.7 and Proposition B.13.9(c)]): if each `S n` is closed in `S (n + 1)`, every
bounded subset of the strict direct limit is contained and bounded in some `S n`. As in
Glöckner–Neeb, if `B` met infinitely many differences `S (n + 1) \ S n`, at points `x_n`, the
neighbourhood of `exists_mem_nhds_preimage_eq_of_subset` can be chosen with `x_n ∉ (n + 1) W`, so
`W` would not absorb `B`. -/
theorem IsStrict.exists_subset_isVonNBounded (hS : IsStrict S)
    (hclosed : ∀ n, IsClosed (range (Submodule.inclusion (hS.mono (Nat.le_succ n)))))
    {B : Set (LCDirectLimit S)} (hB : IsVonNBounded ℝ B) :
    ∃ n, (∀ x ∈ B, x ∈ S n) ∧ IsVonNBounded ℝ (incl S n ⁻¹' B) := by
  -- the steps at which `B` jumps
  set J := {n : ℕ | ∃ x ∈ B, x ∈ S (n + 1) ∧ x ∉ S n}
  obtain ⟨n, hn⟩ : ∃ n, ∀ x ∈ B, x ∈ S n := by
    by_contra hcon
    push Not at hcon
    have hJ : J.Infinite := by
      intro hfin
      obtain ⟨N, hN⟩ := hfin.bddAbove
      obtain ⟨x, hx, hxN⟩ := hcon (N + 1)
      apply hxN
      classical
      have hex : ∃ p, x ∈ S p := hS.exists_mem x
      have hp := Nat.find_spec hex
      rcases hq : Nat.find hex with _ | q
      · rw [hq] at hp
        exact hS.mono (Nat.zero_le _) hp
      · rw [hq] at hp
        have hqJ : q ∈ J := ⟨x, hx, hp, Nat.find_min hex (by omega)⟩
        exact hS.mono (Nat.succ_le_succ (hN hqJ)) hp
    -- the constraints: at a jump `n`, keep `(n + 1)⁻¹ x_n` out of the neighbourhood
    have hC : ∀ n, ∃ C : Set (S (n + 1)), IsOpen C ∧ AbsConvex ℝ C ∧
        (∀ x, Submodule.inclusion (hS.mono (Nat.le_succ n)) x ∈ C) ∧
        (n ∈ J → ∃ x ∈ B, ∃ hx : x ∈ S (n + 1),
          ((n : ℝ) + 1)⁻¹ • (⟨x, hx⟩ : S (n + 1)) ∉ C) := by
      intro n
      by_cases hnJ : n ∈ J
      · obtain ⟨x, hxB, hx1, hx0⟩ := hnJ
        set Rs := LinearMap.range (Submodule.inclusion (hS.mono (Nat.le_succ n)))
        have hRc : IsClosed (Rs : Set (S (n + 1))) := by
          rw [LinearMap.coe_range]
          exact hclosed n
        set y : S (n + 1) := ((n : ℝ) + 1)⁻¹ • ⟨x, hx1⟩
        have hyR : y ∉ (Rs : Set (S (n + 1))) := by
          rintro ⟨z, hz⟩
          apply hx0
          have hzx : (z : V) = ((n : ℝ) + 1)⁻¹ • x := congrArg Subtype.val hz
          have key : ((n : ℝ) + 1) • (z : V) = x := by
            rw [hzx]
            exact smul_inv_smul₀ (by positivity) x
          exact key ▸ (S n).smul_mem _ z.2
        have hnhds : {d : S (n + 1) | y + d ∈ (Rs : Set (S (n + 1)))ᶜ} ∈ 𝓝 0 := by
          have : (Rs : Set (S (n + 1)))ᶜ ∈ 𝓝 (y + 0) := by
            rw [add_zero]
            exact hRc.isOpen_compl.mem_nhds hyR
          exact (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds this
        obtain ⟨D, ⟨hD0, hDo, hDc⟩, hDsub⟩ := (nhds_hasBasis_absConvex_open ℝ _).mem_iff.1 hnhds
        have hRb : Balanced ℝ (Rs : Set (S (n + 1))) := fun a _ ↦ by
          rintro _ ⟨r, hr, rfl⟩
          exact Rs.smul_mem a hr
        refine ⟨Rs + D, hDo.add_left, ⟨hRb.add hDc.1, Rs.convex.add hDc.2⟩,
          fun z ↦ ⟨_, ⟨z, rfl⟩, 0, hD0, add_zero _⟩, fun _ ↦ ⟨x, hxB, hx1, ?_⟩⟩
        rintro ⟨r, hr, d, hd, hrd⟩
        have : y + -d ∈ (Rs : Set (S (n + 1)))ᶜ := hDsub (hDc.1.neg_mem_iff.2 hd)
        rw [show y = r + d from hrd.symm, add_neg_cancel_right] at this
        exact this hr
      · exact ⟨univ, isOpen_univ, ⟨balanced_univ, convex_univ⟩, fun _ ↦ mem_univ _,
          fun h ↦ (hnJ h).elim⟩
    choose C hCo hCc hCS hCJ using hC
    obtain ⟨W, hW, -, hWC⟩ := hS.exists_mem_nhds_preimage_eq_of_subset 0 (U₀ := univ)
      (mem_univ _) isOpen_univ ⟨balanced_univ, convex_univ⟩ C hCo hCc hCS
    obtain ⟨r, hr⟩ := absorbs_iff_norm.1 (hB hW)
    obtain ⟨n, hnJ, hnr⟩ := hJ.exists_gt ⌈r⌉₊
    obtain ⟨x, hxB, hx1, hxC⟩ := hCJ n hnJ
    have hrn : r ≤ ‖(n : ℝ) + 1‖ := by
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 := Nat.le_ceil r
      have h2 : (⌈r⌉₊ : ℝ) < n := by exact_mod_cast hnr
      linarith
    obtain ⟨w, hw, hwx⟩ := hr _ hrn hxB
    apply hxC
    refine hWC n (Nat.zero_le n) ?_
    rw [mem_preimage, incl_apply, Submodule.coe_smul]
    have hxw : ((n : ℝ) + 1)⁻¹ • x = w := by
      beta_reduce at hwx
      rw [← hwx]
      exact inv_smul_smul₀ (by positivity) w
    exact hxw ▸ hw
  refine ⟨n, hn, ?_⟩
  rw [isVonNBounded_iff_tendsto_smallSets_nhds, (hS.isEmbedding_incl n).isInducing.nhds_eq_comap,
    map_zero, smallSets_comap_eq_comap_image, tendsto_comap_iff]
  have : (image (incl S n) ∘ fun c : ℝ ↦ c • incl S n ⁻¹' B) = fun c ↦ c • B := by
    funext c
    rw [comp_apply, image_smul_set, image_preimage_eq_of_subset fun x hx ↦ ⟨⟨x, hn x hx⟩, rfl⟩]
  rw [this]
  exact hB.tendsto_smallSets_nhds

/-- **Strict direct limits with closed steps are compactly regular**
([GN26, Definition A.7.5 and Proposition B.13.9(c)]): every compact subset is contained and compact
in some `S n`. -/
theorem IsStrict.exists_subset_isCompact (hS : IsStrict S)
    (hclosed : ∀ n, IsClosed (range (Submodule.inclusion (hS.mono (Nat.le_succ n)))))
    {K : Set (LCDirectLimit S)} (hK : IsCompact K) :
    ∃ n, (∀ x ∈ K, x ∈ S n) ∧ IsCompact (incl S n ⁻¹' K) := by
  obtain ⟨n, hn, -⟩ := hS.exists_subset_isVonNBounded hclosed (hK.isVonNBounded ℝ)
  exact ⟨n, hn, ((hS.isEmbedding_incl n).isInducing.isCompact_preimage_iff
    fun x hx ↦ ⟨⟨x, hn x hx⟩, rfl⟩).2 hK⟩

end Strict

section StrictComplete

variable {S : ℕ → Submodule ℝ V} [∀ n, UniformSpace (S n)] [∀ n, IsUniformAddGroup (S n)]
  [∀ n, ContinuousSMul ℝ (S n)] [∀ n, LocallyConvexSpace ℝ (S n)]

/-- **Strict direct limits of complete spaces are complete** ([GN26, Proposition B.13.9(d)]). As in
Glöckner–Neeb, a Cauchy filter `F` concentrates near some step: there is `m` such that every set of
`F` meets `S m + W` for each `0`-neighbourhood `W` (otherwise the convex hull of the sets
`W_n ∩ S n` would contradict the Cauchy
property). The traces on `S m` of the sets `A + W`, `A ∈ F`, then form a Cauchy filter on `S m`, by
(a), and its limit is the limit of `F`. -/
theorem IsStrict.completeSpace [∀ n, CompleteSpace (S n)] (hS : IsStrict S) :
    CompleteSpace (LCDirectLimit S) := by
  refine ⟨fun {F} hF ↦ ?_⟩
  have : F.NeBot := hF.1
  -- `F` concentrates near some `S m`
  obtain ⟨m, hm⟩ : ∃ m, ∀ A ∈ F, ∀ W ∈ 𝓝 (0 : LCDirectLimit S),
      ∃ x ∈ A, ∃ s : LCDirectLimit S, s ∈ S m ∧ x - s ∈ W := by
    by_contra hcon
    push Not at hcon
    choose A hA W hW hAW using hcon
    have hD : ∀ m, ∃ D ∈ 𝓝 (0 : LCDirectLimit S), Convex ℝ D ∧ D ⊆ W m := fun m ↦ by
      obtain ⟨D, ⟨hD0, hDo, hDc⟩, hDW⟩ := (nhds_hasBasis_absConvex_open ℝ _).mem_iff.1 (hW m)
      exact ⟨D, hDo.mem_nhds hD0, hDc.2, hDW⟩
    choose D hD hDc hDW using hD
    -- a decreasing sequence of convex `0`-neighbourhoods
    set D' : ℕ → Set (LCDirectLimit S) := fun m ↦ ⋂ i ∈ Iic m, D i
    have hD'n : ∀ m, D' m ∈ 𝓝 0 := fun m ↦ (biInter_mem (finite_Iic m)).2 fun i _ ↦ hD i
    have hD'c : ∀ m, Convex ℝ (D' m) := fun m ↦ convex_iInter₂ fun i _ ↦ hDc i
    have hD'W : ∀ m, D' m ⊆ W m := fun m ↦ (biInter_subset_of_mem (mem_Iic.2 le_rfl)).trans (hDW m)
    have hD'anti : ∀ {m n}, m ≤ n → D' n ⊆ D' m := fun h ↦
      biInter_subset_biInter_left (Iic_subset_Iic.2 h)
    set Wc : Set (LCDirectLimit S) := convexHull ℝ (⋃ n, D' n ∩ {x | x ∈ S n})
    -- (B.30): `S m + Wc ⊆ S m + D' m`
    have hWc : ∀ m, Wc ⊆ {x : LCDirectLimit S | x ∈ S m} + D' m := fun m ↦ by
      refine convexHull_min ?_ ((S m).convex.add (hD'c m))
      intro x hx
      obtain ⟨n, hxD, hxS⟩ := mem_iUnion.1 hx
      rcases le_total n m with h | h
      · exact ⟨x, hS.mono h hxS, 0, mem_of_mem_nhds (hD'n m), add_zero x⟩
      · exact ⟨0, (S m).zero_mem, x, hD'anti h hxD, zero_add x⟩
    have hWcn : Wc ∈ 𝓝 (0 : LCDirectLimit S) := by
      have h0 : (0 : LCDirectLimit S) ∈ ⋃ n, D' n ∩ {x | x ∈ S n} :=
        mem_iUnion.2 ⟨0, mem_of_mem_nhds (hD'n 0), (S 0).zero_mem⟩
      refine (mem_nhds_zero_iff_of_convex S hS.exists_mem (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ h0)).2 fun n ↦ ?_
      refine mem_of_superset ((continuous_incl S n).continuousAt.preimage_mem_nhds (t := D' n)
        (by rw [map_zero]; exact hD'n n)) fun y hy ↦
          subset_convexHull ℝ _ (mem_iUnion.2 ⟨n, hy, y.2⟩)
    have hent : {p : LCDirectLimit S × LCDirectLimit S | p.2 - p.1 ∈ Wc} ∈
        uniformity (LCDirectLimit S) := by
      rw [uniformity_eq_comap_nhds_zero]
      exact preimage_mem_comap hWcn
    obtain ⟨A₀, hA₀, hA₀A₀⟩ := mem_prod_same_iff.1 (hF.2 hent)
    obtain ⟨x₀, hx₀⟩ := hF.1.nonempty_of_mem hA₀
    obtain ⟨m₀, hm₀⟩ := hS.exists_mem x₀
    obtain ⟨x, hxA₀, hxA⟩ := hF.1.nonempty_of_mem (inter_mem hA₀ (hA m₀))
    obtain ⟨s, hs, w, hw, hsw⟩ := hWc m₀ (hA₀A₀ (mk_mem_prod hx₀ hxA₀))
    have hsw' : s + w = x - x₀ := hsw
    have hxw : x - (x₀ + s) = w := by
      rw [← sub_sub, ← hsw', add_sub_cancel_left]
    exact hAW m₀ x hxA (x₀ + s) ((S m₀).add_mem hm₀ hs) (hD'W m₀ (hxw ▸ hw))
  -- the thickening `F + 𝓝 0` and its trace on `S m`
  set H := map (fun p : LCDirectLimit S × LCDirectLimit S ↦ p.1 + p.2) (F ×ˢ 𝓝 0)
  have hH : Cauchy H := (hF.prod cauchy_nhds).map uniformContinuous_add
  have hFH : F ≤ H := by
    intro A' hA'
    obtain ⟨A, hA, W, hW, hsub⟩ := mem_prod_iff.1 (mem_map.1 hA')
    exact mem_of_superset hA fun x hx ↦ by
      simpa using hsub (mk_mem_prod hx (mem_of_mem_nhds hW))
  set G := comap (incl S m) H
  have hGne : G.NeBot := by
    rw [comap_neBot_iff]
    intro t ht
    obtain ⟨A, hA, W, hW, hsub⟩ := mem_prod_iff.1 (mem_map.1 ht)
    obtain ⟨x, hx, s, hs, hxs⟩ := hm A hA (-W) (neg_mem_nhds_zero _ hW)
    refine ⟨⟨s, hs⟩, ?_⟩
    have := hsub (mk_mem_prod hx (show -(x - s) ∈ W from hxs))
    simpa using this
  have hui : IsUniformInducing (incl S m) :=
    AddMonoidHom.isUniformInducing_of_isInducing (hS.isEmbedding_incl m).isInducing
  have hGc : Cauchy G := by
    rw [← hui.cauchy_map_iff]
    exact hH.mono' (hGne.map _) map_comap_le
  obtain ⟨y, hy⟩ := CompleteSpace.complete hGc
  have hGy : map (incl S m) G ≤ 𝓝 (incl S m y) :=
    (map_mono hy).trans ((continuous_incl S m).tendsto y)
  have : (map (incl S m) G).NeBot := hGne.map _
  exact ⟨incl S m y, hFH.trans (le_nhds_of_cauchy_adhp hH
    (neBot_of_le (le_inf hGy map_comap_le)))⟩

/-- **Strict direct limits of quasi-complete spaces with closed steps are quasi-complete**
([GN26, Proposition B.13.9(e)]): a closed bounded set lies, and is bounded, in some step
(bounded regularity, (c)), where it is closed, hence complete; and the step is uniformly
embedded. -/
theorem IsStrict.quasiCompleteSpace [∀ n, QuasiCompleteSpace ℝ (S n)] (hS : IsStrict S)
    (hclosed : ∀ n, IsClosed (range (Submodule.inclusion (hS.mono (Nat.le_succ n))))) :
    QuasiCompleteSpace ℝ (LCDirectLimit S) where
  quasiComplete B hB hBc := by
    obtain ⟨n, hn, hbn⟩ := hS.exists_subset_isVonNBounded hclosed hB
    have hui : IsUniformInducing (incl S n) :=
      AddMonoidHom.isUniformInducing_of_isInducing (hS.isEmbedding_incl n).isInducing
    have hB' : IsComplete (incl S n ⁻¹' B) :=
      QuasiCompleteSpace.quasiComplete hbn (hBc.preimage (continuous_incl S n))
    have himg : incl S n '' (incl S n ⁻¹' B) = B :=
      image_preimage_eq_of_subset fun x hx ↦ ⟨⟨x, hn x hx⟩, rfl⟩
    rw [← himg]
    exact (isComplete_image_iff hui).2 hB'

/-- **Strict direct limits of sequentially complete spaces with closed steps are sequentially
complete** ([GN26, Proposition B.13.9(e)]): a Cauchy sequence is bounded, hence lies, and
is Cauchy, in some step. -/
theorem IsStrict.exists_tendsto_of_cauchySeq (hS : IsStrict S)
    (hclosed : ∀ n, IsClosed (range (Submodule.inclusion (hS.mono (Nat.le_succ n)))))
    (hseq : ∀ n (u : ℕ → S n), CauchySeq u → ∃ y, Tendsto u atTop (𝓝 y))
    {u : ℕ → LCDirectLimit S} (hu : CauchySeq u) : ∃ x, Tendsto u atTop (𝓝 x) := by
  obtain ⟨n, hn, -⟩ := hS.exists_subset_isVonNBounded hclosed
    (hu.totallyBounded_range.isVonNBounded ℝ)
  have hui : IsUniformInducing (incl S n) :=
    AddMonoidHom.isUniformInducing_of_isInducing (hS.isEmbedding_incl n).isInducing
  set u' : ℕ → S n := fun k ↦ ⟨u k, hn _ (mem_range_self k)⟩
  have hu' : CauchySeq u' := by
    rw [CauchySeq, ← hui.cauchy_map_iff, map_map]
    exact hu
  obtain ⟨y, hy⟩ := hseq n u' hu'
  exact ⟨incl S n y, ((continuous_incl S n).tendsto y).comp hy⟩

end StrictComplete

end LCDirectLimit

end LocallyConvex.Analysis

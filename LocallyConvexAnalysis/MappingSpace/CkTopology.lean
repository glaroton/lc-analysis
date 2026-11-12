/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.Higher
public import Mathlib.Topology.ContinuousMap.LocallyConvex

/-!
# The compact-open `C^k` topology

Let `E`, `F` be locally convex spaces, `U ⊆ E` open and `k ∈ ℕ`. The space `C^k(U, F)` of maps
that are `C^k` in the sense of Michal–Bastiani carries the **compact-open `C^k` topology**: the
initial topology with respect to the differentials

  `d^(j) : C^k(U, F) → C(U × E^j, F)`,  `γ ↦ d^(j)γ`,  `j ≤ k`,

where `C(U × E^j, F)` has the compact-open topology ([GN26, Definition 1.7.10]). We show that it is
a locally convex Hausdorff topological vector space and prove the continuity of the basic
operations between such spaces: pullbacks `γ ↦ γ ∘ f` (Proposition 1.7.11) and superposition
operators `γ ↦ f ∘ (id, γ)` (Proposition 1.7.12). The case `k = ∞` is in
`LocallyConvexAnalysis.MappingSpace.SmoothTopology`.

## Main definitions

* `ContDiffMBMap F k U`: the space `C^k(U, F)`, for `U : Opens E`, with its vector space structure
  and the compact-open `C^k` topology.
* `ContDiffMBMap.iteratedD j hj γ ∈ C(U × (Fin j → E), F)`: the differential `d^(j)γ`, `j ≤ k`.
* `ContDiffMBMap.dMap γ ∈ C^k(U × E, F)`: the differential `dγ` of `γ ∈ C^{k+1}(U, F)`.
* `ContDiffMBMap.compGraph hf γ = f ∘ (id, γ)`: the superposition operator
  `f_* : C^r(U, E) → C^r(U, F)` of a map `f : Z × E → F` of class `C^r` on `U × E`.
* `ContDiffMBMap.compRightOfContDiff hf hUV γ = γ ∘ f`: the pullback `f^* : C^r(V, F) → C^r(U, F)`
  along a map `f` of class `C^r` on `U` with `f(U) ⊆ V`.

## Main results

* `ContDiffMBMap.instIsTopologicalAddGroup`, `ContDiffMBMap.instContinuousSMulReal`,
  `ContDiffMBMap.instLocallyConvexSpaceReal`, `ContDiffMBMap.instT2Space`: `C^k(U, F)` is a
  locally convex Hausdorff topological vector space ([GN26, Definition 1.7.10]).
* `ContDiffMBMap.isEmbedding_toPi`: `γ ↦ (d^(j)γ)_{j ≤ k}` is a linear topological embedding
  `C^k(U, F) → ∏_{j ≤ k} C(U × E^j, F)`, and `ContDiffMBMap.isClosed_range_toPi`: its image is
  closed ([GN26, Lemma 1.7.15]). The key analytic input is `hasDirDerivAt_of_tendsto`:
  limits of differentiable maps whose derivatives converge in the compact-open sense are
  differentiable.
* `ContDiffMBMap.compRightCLM`: pullback `γ ↦ γ ∘ L` along a continuous linear map is continuous
  linear ([GN26, Proposition 1.7.11], for linear maps).
* `ContDiffMBMap.compLeftCLM`: postcomposition with a continuous linear map is continuous linear
  ([GN26, Corollary 1.7.13], for linear maps).
* `ContDiffMBMap.prodEquiv`: `C^k(U, F × G) ≅ C^k(U, F) × C^k(U, G)` as topological vector spaces
  ([GN26, Corollary 1.7.14]).
* `ContDiffMBOn.iteratedDMB_dMB`: for `γ` of class `C^{k+1}` and `j ≤ k`,
  `d^(j)(dγ)((x, a), (v₁, w₁), …, (vⱼ, wⱼ)) = d^(j+1)γ(x, a, v) + ∑ᵢ d^(j)γ(x, v₁, …, wᵢ, …, vⱼ)`.
* `ContDiffMBMap.dCLM`: the differential `d : C^{k+1}(U, F) → C^k(U × E, F)` is continuous
  linear, and `ContDiffMBMap.continuous_of_continuous_dMap`: a map into `C^{k+1}(U, F)` is
  continuous when its compositions with `γ ↦ γ ∈ C(U, F)` and with `d` are continuous. Together,
  the topology of `C^{k+1}(U, F)` is initial with respect to these two maps.
* `ContDiffMBMap.continuous_compGraph`: **[GN26, Proposition 1.7.12]**. For `Z`, `E`, `F`
  locally convex, `U ⊆ Z` open and `f : Z × E → F` of class `C^r` on `U × E`, the superposition
  operator `f_* : C^r(U, E) → C^r(U, F)`, `γ ↦ f ∘ (id_U, γ)`, is continuous.
* `ContDiffMBMap.continuous_compLeftOfContDiff`: **[GN26, Corollary 1.7.13]**. For
  `g : E → F` of class `C^k`, `γ ↦ g ∘ γ`, `C^k(U, E) → C^k(U, F)`, is continuous.
* `ContDiffMBMap.compRightOfContDiffCLM`: **[GN26, Proposition 1.7.11]**. For
  `f : E₁ → E₂` of class `C^r` on `U` with `f(U) ⊆ V`, `γ ↦ γ ∘ f`, `C^r(V, F) → C^r(U, F)`, is
  continuous linear.

## Implementation notes

* **Representation.** Glöckner–Neeb consider maps `U → F`. Here an element of `C^k(U, F)` is a
  map `E → F` that is `C^k` on `U` and vanishes outside `U`, so that `C^k(U, F)` is a submodule of
  `E → F` on which the family of the `d^(j)` separates points, while the differentials are the
  `iteratedDMB` of `Calculus/Higher.lean` without change. `ContDiffMBMap F k U` is a type synonym
  for this submodule, so that it does not inherit the topology of pointwise convergence. The open
  set is a bundled `U : TopologicalSpace.Opens E`. Superposition operators extend their values by
  `0` outside `U`. Only open sets `U` are treated: Glöckner–Neeb also allow locally convex subsets
  with dense interior (their Definition 1.4.4), but this library has no `C^k` maps on such sets.
* **The topology.** It is defined as the topology induced by the linear map
  `toPi : C^k(U, F) → ∏_{j ≤ k} C(U × E^j, F)`, so the vector space axioms, local convexity and
  the Hausdorff property follow from the corresponding facts for spaces of continuous maps in
  Mathlib (`ContinuousMap.instLocallyConvexSpace`), and Lemma 1.7.15 holds by definition, as in
  Glöckner–Neeb.
* **Continuity in the compact-open topology.** The domains `U × E^j` are Hausdorff but not
  locally compact, so the evaluation map need not be continuous on `C(U × E^j, F) × (U × E^j)`. We
  restrict to compact subsets, which are locally compact
  (`ContinuousMap.continuous_of_continuous_uncurry_restrict`).
* **Departure from Glöckner–Neeb in Proposition 1.7.12.** Glöckner–Neeb prove Proposition 1.7.12
  with Faà di Bruno's formula, which is not formalized here. We argue instead by induction on
  `r`. The explicit formula `ContDiffMBOn.iteratedDMB_dMB` for the differentials of `dγ`, which
  rests on the linearity of `dγ(x, ·)` and Schwarz's theorem, shows that
  `d : C^{k+1}(U, F) → C^k(U × E, F)` is continuous; conversely
  `d^(j+1)γ(x, v₀, …, vⱼ) = d^(j)(dγ)((x, v₀), (v₁, 0), …, (vⱼ, 0))` ([GN26, (1.36)]), so
  the topology of `C^{k+1}(U, F)` is initial with respect to `γ ↦ γ` and `γ ↦ dγ`. The chain rule
  gives `d(f ∘ (id, γ))(x, v) = df((x, γ x), (v, dγ(x, v)))`, that is, `d(f_* γ)` is the
  superposition operator of `df` applied to `(γ ∘ pr₁, dγ) ∈ C^{r-1}(U × Z, E × E)`, and the
  induction hypothesis applies. The case `r = 0` is the continuity of `γ ↦ f ∘ (id, γ)` on
  `C(U, E)` ([GN26, Lemma A.6.20]; `ContinuousMap.continuous_comp_graph`).
  Proposition 1.7.11, which Glöckner–Neeb also prove with Faà di Bruno's formula, is proved the
  same way from `d(γ ∘ f) = dγ ∘ (f ∘ pr₁, df)`.
  We do not claim these arguments are new.
* **Departure from Glöckner–Neeb in Lemma 1.7.15.** For the closed image, Glöckner–Neeb use their
  Exercise 1.1.13(b) on nets of `C^1` curves, whose hint goes through weak integrals. Here
  `hasDirDerivAt_of_tendsto` uses the mean value inclusion `sub_mem_of_hasDirDerivAt` (a
  consequence of the Hahn–Banach theorem) instead, so that no completeness is needed. We do not
  claim this argument is new.
* No completeness assumption is made anywhere. The Hausdorff property of `E` and `F` is part of
  the standing assumptions of the Michal–Bastiani calculus in this library (the chain rule and
  Schwarz's theorem use it).

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

universe u v w

/-! ### Identities for iterated differentials -/

section Identities

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

omit [TopologicalSpace E] in
/-- Directional derivatives of a map that only depends on the first coordinate. -/
theorem HasDirDerivAt.comp_fst {E' : Type*} [AddCommGroup E'] [Module ℝ E'] {g : E → F}
    {x h : E} {y : F} (hg : HasDirDerivAt g x h y) (a b : E') :
    HasDirDerivAt (fun p : E × E' ↦ g p.1) (x, a) (h, b) y := by
  simpa [HasDirDerivAt] using hg

omit [TopologicalSpace E] in
/-- Directional derivatives of finite sums. -/
theorem HasDirDerivAt.sum [IsTopologicalAddGroup F] {ι : Type*}
    (s : Finset ι) {g : ι → E → F} {x h : E} {y : ι → F}
    (hg : ∀ i ∈ s, HasDirDerivAt (g i) x h (y i)) :
    HasDirDerivAt (fun z ↦ ∑ i ∈ s, g i z) x h (∑ i ∈ s, y i) :=
  (tendsto_finsetSum s hg).congr fun t ↦ by
    simp only [← Finset.sum_sub_distrib, Finset.smul_sum]

end Identities

section LinearOperations

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]
  {U : Set E}

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ F] [LocallyConvexSpace ℝ G]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] in
/-- The iterated differentials of a pair of `C^k` maps are the pairs of their iterated
differentials. -/
theorem iteratedDMB_prodMk {k : ℕ} {f : E → F} {g : E → G} (hU : IsOpen U)
    (hf : ContDiffMBOn k f U) (hg : ContDiffMBOn k g U) :
    ∀ j ≤ k, ∀ x ∈ U, ∀ v : Fin j → E,
      iteratedDMB j (fun z ↦ (f z, g z)) (x, v) = (iteratedDMB j f (x, v), iteratedDMB j g (x, v))
  | 0, _, _, _, _ => rfl
  | j + 1, hj, x, hx, v => by
    rw [iteratedDMB_succ]
    have hev : (fun z ↦ iteratedDMB j (fun z ↦ (f z, g z)) (z, Fin.init v)) =ᶠ[𝓝 x]
        fun z ↦ (iteratedDMB j f (z, Fin.init v), iteratedDMB j g (z, Fin.init v)) :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun z hz ↦
        iteratedDMB_prodMk hU hf hg j (by omega) z hz _
    rw [dMB_congr_of_eventuallyEq hev]
    exact ((hf.hasContIterDerivOn.1 j (by omega) x hx v).prodMk
      (hg.hasContIterDerivOn.1 j (by omega) x hx v)).dMB_eq

omit [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- Iterated differentials of a sum of `C^k` maps. -/
theorem iteratedDMB_add {k : ℕ} {f g : E → F} (hU : IsOpen U) (hf : ContDiffMBOn k f U)
    (hg : ContDiffMBOn k g U) {j : ℕ} (hj : j ≤ k) {x : E} (hx : x ∈ U) (v : Fin j → E) :
    iteratedDMB j (fun z ↦ f z + g z) (x, v) = iteratedDMB j f (x, v) + iteratedDMB j g (x, v) := by
  have h := iteratedDMB_clm_comp hU (hf.prodMk hU hg)
    (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F) j hj x hx v
  rw [iteratedDMB_prodMk hU hf hg j hj x hx v] at h
  simpa using h

omit [LocallyConvexSpace ℝ E] [T2Space E] [LocallyConvexSpace ℝ F] [IsTopologicalAddGroup F] in
/-- Iterated differentials of a multiple of a `C^k` map. -/
theorem iteratedDMB_const_smul {k : ℕ} {f : E → F} (hU : IsOpen U) (hf : ContDiffMBOn k f U)
    (c : ℝ) {j : ℕ} (hj : j ≤ k) {x : E} (hx : x ∈ U) (v : Fin j → E) :
    iteratedDMB j (fun z ↦ c • f z) (x, v) = c • iteratedDMB j f (x, v) := by
  simpa using iteratedDMB_clm_comp hU hf (c • ContinuousLinearMap.id ℝ F) j hj x hx v

end LinearOperations

/-! ### The differentials of `dγ` -/

section DerivativeFormula

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {U : Set E}

/-- **The differentials of `dγ`.** If `γ` is `C^{k+1}` on `U` and `j ≤ k`, then
`d^(j)(dγ)((x, a), (v₁, w₁), …, (vⱼ, wⱼ))`
`  = d^(j+1)γ(x, a, v₁, …, vⱼ) + ∑ᵢ d^(j)γ(x, v₁, …, wᵢ, …, vⱼ)`
for `x ∈ U` (the `i`-th summand has `wᵢ` in place of `vᵢ`). The proof uses the linearity of
`dγ(x, ·)` and Schwarz's theorem. -/
theorem ContDiffMBOn.iteratedDMB_dMB {k : ℕ} {γ : E → F} (hU : IsOpen U)
    (hγ : ContDiffMBOn (k + 1) γ U) : ∀ j ≤ k, ∀ x ∈ U, ∀ (a : E) (v w : Fin j → E),
      iteratedDMB j (dMB γ) ((x, a), fun i ↦ (v i, w i)) =
        iteratedDMB (j + 1) γ (x, Fin.cons a v) + ∑ i, iteratedDMB j γ (x, update v i (w i))
  | 0, _, x, _, a, v, w => by
    simp [iteratedDMB_zero, iteratedDMB_one]
  | j + 1, hj, x, hx, a, v, w => by
    have hUE : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
    have hxa : (x, a) ∈ U ×ˢ (univ : Set E) := ⟨hx, mem_univ a⟩
    -- the first summand, written as a slice of `d^(j)(dγ)`
    let Φ₁ : E × E → F := fun p ↦ iteratedDMB j (dMB γ) (p, fun i ↦ (Fin.init v i, 0))
    have hΦ₁ : ∀ z b, Φ₁ (z, b) = iteratedDMB (j + 1) γ (z, Fin.cons b (Fin.init v)) :=
      fun z b ↦ by rw [iteratedDMB_succ_eq_dMB]; simp [Φ₁]
    have hΦ₁c : ContDiffMBOn 1 Φ₁ (U ×ˢ univ) :=
      (hγ.2.2.of_le (show j + 1 ≤ k by omega)).contDiffMBOn_iteratedDMB_slice (k := j) (r := 1)
        hUE _
    let Ψ : E × E → F := fun p ↦
      ∑ i : Fin j, iteratedDMB j γ (p.1, update (Fin.init v) i (Fin.init w i))
    have hev : (fun p ↦ iteratedDMB j (dMB γ) (p, Fin.init fun i ↦ (v i, w i))) =ᶠ[𝓝 (x, a)]
        fun p ↦ Φ₁ p + Ψ p :=
      Filter.eventually_of_mem (hUE.mem_nhds hxa) fun p hp ↦ by
        obtain ⟨z, b⟩ := p
        change iteratedDMB j (dMB γ) ((z, b), fun i ↦ (Fin.init v i, Fin.init w i)) =
          Φ₁ (z, b) + Ψ (z, b)
        rw [hΦ₁]
        exact hγ.iteratedDMB_dMB hU j (by omega) z hp.1 b _ _
    -- the derivative of the first summand
    have hD₁ : HasDirDerivAt Φ₁ (x, a) (v (Fin.last j), w (Fin.last j))
        (iteratedDMB (j + 2) γ (x, Fin.cons a v) +
          iteratedDMB (j + 1) γ (x, update v (Fin.last j) (w (Fin.last j)))) := by
      have h := hΦ₁c.hasDirDerivAt (k := 0) hxa (v (Fin.last j), w (Fin.last j))
      have hsplit : ((v (Fin.last j), w (Fin.last j)) : E × E) =
          (v (Fin.last j), 0) + (0, w (Fin.last j)) := by simp
      rw [hsplit, hΦ₁c.dMB_add hUE hxa, dMB_slice, dMB_slice₂] at h
      convert h using 2
      · have e : (fun z ↦ Φ₁ (z, a)) = fun z ↦ iteratedDMB (j + 1) γ (z, Fin.cons a (Fin.init v)) :=
          funext fun z ↦ hΦ₁ z a
        have key : (Fin.cons a v : Fin (j + 2) → E) =
            Fin.snoc (Fin.cons a (Fin.init v)) (v (Fin.last j)) := by
          rw [← Fin.cons_snoc_eq_snoc_cons, Fin.snoc_init_self]
        rw [e, key, iteratedDMB_succ, Fin.init_snoc, Fin.snoc_last]
      · obtain ⟨M, hM, hMs⟩ :=
          (hγ.of_le (show j + 1 ≤ k + 1 by omega)).exists_iteratedDMB_multilinear hU hx
        have e : (fun b ↦ Φ₁ (x, b)) = ⇑(M.toContinuousLinearMap (Fin.cons 0 (Fin.init v)) 0) :=
          funext fun b ↦ by simp [hΦ₁, hM, Fin.update_cons_zero]
        rw [e, ((M.toContinuousLinearMap _ 0).hasDirDerivAt a _).dMB_eq]
        simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply, Fin.update_cons_zero]
        have hσ : update v (Fin.last j) (w (Fin.last j)) =
            Fin.cons (w (Fin.last j)) (Fin.init v) ∘ (Fin.last j).cycleRange := by
          rw [Fin.cons_comp_cycleRange, Fin.insertNth_last']
          conv_lhs => rw [← Fin.snoc_init_self v, Fin.update_snoc_last]
        rw [← hM, hσ, hMs]
    -- the derivative of the second summand
    have hD₂ : HasDirDerivAt Ψ (x, a) (v (Fin.last j), w (Fin.last j))
        (∑ i : Fin j, iteratedDMB (j + 1) γ (x, update v i.castSucc (w i.castSucc))) := by
      refine HasDirDerivAt.sum _ fun i _ ↦ ?_
      have h := hγ.hasContIterDerivOn.1 j (by omega) x hx
        (Fin.snoc (update (Fin.init v) i (Fin.init w i)) (v (Fin.last j)))
      simp only [Fin.init_snoc, Fin.snoc_last] at h
      rw [Fin.snoc_update, Fin.snoc_init_self] at h
      exact h.comp_fst a _
    rw [iteratedDMB_succ, dMB_congr_of_eventuallyEq hev, (hD₁.add hD₂).dMB_eq,
      Fin.sum_univ_castSucc]
    abel

end DerivativeFormula

/-! ### Two facts on the compact-open topology -/

section CompactOpen

variable {X A B P : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace P]

omit [T2Space X] in
/-- A map into `C(X, B)` is continuous for the compact-open topology if its
restrictions to the compact subsets `K` of `X` are jointly continuous on `P × K`. -/
theorem ContinuousMap.continuous_of_continuous_uncurry_restrict (Ψ : P → C(X, B))
    (h : ∀ K : Set X, IsCompact K → Continuous fun q : P × K ↦ Ψ q.1 q.2) : Continuous Ψ := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [ContinuousAt, ContinuousMap.tendsto_compactOpen_iff_forall]
  intro K hK
  exact (ContinuousMap.continuous_of_continuous_uncurry (fun q ↦ (Ψ q).restrict K)
    (h K hK)).continuousAt.tendsto

/-- Evaluation `C(X, A) × K → A` is continuous on a compact subset `K` of a Hausdorff space. -/
theorem ContinuousMap.continuous_eval_restrict {K : Set X} (hK : IsCompact K) :
    Continuous fun q : C(X, A) × K ↦ q.1 q.2 := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact continuous_eval.comp
    ((ContinuousMap.continuous_restrict K).prodMap continuous_id)

/-- `(γ, η) ↦ (x ↦ (γ x, η x))`, `C(X, A) × C(X, B) → C(X, A × B)`, is continuous for the
compact-open topologies (`X` Hausdorff). -/
theorem ContinuousMap.continuous_prodMk_pair :
    Continuous fun p : C(X, A) × C(X, B) ↦ p.1.prodMk p.2 :=
  ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun _ hK ↦
    ((ContinuousMap.continuous_eval_restrict hK).comp
      (continuous_fst.fst.prodMk continuous_snd)).prodMk
      ((ContinuousMap.continuous_eval_restrict hK).comp
        (continuous_fst.snd.prodMk continuous_snd))

/-- For `f : X × A → B` continuous (`X` Hausdorff), `γ ↦ f ∘ (id, γ)`, `C(X, A) → C(X, B)`, is
continuous for the compact-open topologies ([GN26, Lemma A.6.20]). -/
theorem ContinuousMap.continuous_comp_graph (f : C(X × A, B)) :
    Continuous fun γ : C(X, A) ↦ f.comp ((ContinuousMap.id X).prodMk γ) :=
  ContinuousMap.continuous_of_continuous_uncurry_restrict _ fun _ hK ↦
    f.continuous.comp ((continuous_subtype_val.comp continuous_snd).prodMk
      (ContinuousMap.continuous_eval_restrict hK))

end CompactOpen

/-! ### The space `C^k(U, F)` -/

open TopologicalSpace

section Space

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

variable (F) in
/-- The `C^k` maps on the open set `U`, extended by `0` outside `U`, as a submodule of `E → F`. -/
def contDiffMBSubmodule (k : ℕ) (U : Opens E) : Submodule ℝ (E → F) where
  carrier := {f | ContDiffMBOn k f U ∧ ∀ x ∉ U, f x = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add U.isOpen hg.1, fun x hx ↦ by simp [hf.2 x hx, hg.2 x hx]⟩
  zero_mem' := ⟨contDiffMBOn_const k (0 : F) _, fun _ _ ↦ rfl⟩
  smul_mem' c f hf := by
    refine ⟨?_, fun x hx ↦ by simp [hf.2 x hx]⟩
    have h := ContDiffMBOn.comp U.isOpen isOpen_univ
      ((c • ContinuousLinearMap.id ℝ F).contDiffMBOn k univ) hf.1 (mapsTo_univ _ _)
    convert h using 1
    ext x
    simp

variable (F) in
/-- **The space `C^k(U, F)`** of `C^k` maps (in the sense of Michal–Bastiani) on an open set
`U ⊆ E`, `k ∈ ℕ`. To make the differentials `d^(j)` separate points, the maps are extended by `0`
outside `U`. Its topology, the compact-open `C^k` topology, is defined below. -/
def ContDiffMBMap (k : ℕ) (U : Opens E) : Type (max u v) := contDiffMBSubmodule F k U

namespace ContDiffMBMap

variable {k : ℕ} {U : Opens E}

/-- The vector space operations of `C^k(U, F)` are pointwise. -/
instance : AddCommGroup (ContDiffMBMap F k U) :=
  inferInstanceAs (AddCommGroup (contDiffMBSubmodule F k U))

/-- The vector space operations of `C^k(U, F)` are pointwise. -/
instance : Module ℝ (ContDiffMBMap F k U) :=
  inferInstanceAs (Module ℝ (contDiffMBSubmodule F k U))

/-- An element of `C^k(U, F)` is a map `E → F`. -/
instance : FunLike (ContDiffMBMap F k U) E F where
  coe γ := Subtype.val (γ : contDiffMBSubmodule F k U)
  coe_injective := Subtype.val_injective

/-- The element of `C^k(U, F)` given by a map `f` that is `C^k` on `U` and vanishes outside `U`. -/
def mk (f : E → F) (hf : ContDiffMBOn k f U) (h0 : ∀ x ∉ U, f x = 0) : ContDiffMBMap F k U :=
  ⟨f, hf, h0⟩

/-- The underlying map of `ContDiffMBMap.mk f hf h0` is `f`. -/
@[simp]
theorem coe_mk (f : E → F) (hf : ContDiffMBOn k f U) (h0 : ∀ x ∉ U, f x = 0) :
    ⇑(mk f hf h0) = f :=
  rfl

/-- An element of `C^k(U, F)` is `C^k` on `U`. -/
theorem contDiffMBOn (γ : ContDiffMBMap F k U) : ContDiffMBOn k γ U :=
  (γ : contDiffMBSubmodule F k U).2.1

/-- An element of `C^k(U, F)` vanishes outside `U`. -/
theorem apply_of_notMem (γ : ContDiffMBMap F k U) {x : E} (hx : x ∉ U) : γ x = 0 :=
  (γ : contDiffMBSubmodule F k U).2.2 x hx

/-- Elements of `C^k(U, F)` are equal if they agree as maps. -/
@[ext]
theorem ext {γ η : ContDiffMBMap F k U} (h : ∀ x, γ x = η x) : γ = η :=
  DFunLike.ext _ _ h

/-- The zero of `C^k(U, F)` is the zero map. -/
@[simp]
theorem coe_zero : ⇑(0 : ContDiffMBMap F k U) = 0 :=
  rfl

/-- Addition in `C^k(U, F)` is pointwise. -/
@[simp]
theorem coe_add (γ η : ContDiffMBMap F k U) : ⇑(γ + η) = γ + η :=
  rfl

/-- Scalar multiplication in `C^k(U, F)` is pointwise. -/
@[simp]
theorem coe_smul (c : ℝ) (γ : ContDiffMBMap F k U) : ⇑(c • γ) = c • ⇑γ :=
  rfl

/-- The `j`-th differential `d^(j)γ ∈ C(U × E^j, F)` of `γ ∈ C^k(U, F)`, for `j ≤ k`. -/
def iteratedD (j : ℕ) (hj : j ≤ k) (γ : ContDiffMBMap F k U) : C(U × (Fin j → E), F) where
  toFun p := iteratedDMB j γ (p.1, p.2)
  continuous_toFun := (γ.contDiffMBOn.hasContIterDerivOn.2 j hj).comp_continuous
    (continuous_subtype_val.prodMap continuous_id) fun p ↦ ⟨p.1.2, mem_univ _⟩

/-- `d^(j)γ(x, v) = iteratedDMB j γ (x, v)`. -/
@[simp]
theorem iteratedD_apply (j : ℕ) (hj : j ≤ k) (γ : ContDiffMBMap F k U)
    (p : U × (Fin j → E)) : iteratedD j hj γ p = iteratedDMB j γ (p.1, p.2) :=
  rfl

/-- `d^(j) : C^k(U, F) → C(U × E^j, F)` as a linear map. -/
def iteratedDL (j : ℕ) (hj : j ≤ k) : ContDiffMBMap F k U →ₗ[ℝ] C(U × (Fin j → E), F) where
  toFun := iteratedD j hj
  map_add' γ η := by
    ext p
    exact iteratedDMB_add U.isOpen γ.contDiffMBOn η.contDiffMBOn hj p.1.2 p.2
  map_smul' c γ := by
    ext p
    exact iteratedDMB_const_smul U.isOpen γ.contDiffMBOn c hj p.1.2 p.2

/-- The linear map `Φ : C^k(U, F) → ∏_{j ≤ k} C(U × E^j, F)`, `γ ↦ (d^(j)γ)_{j ≤ k}`
([GN26, Lemma 1.7.15]). -/
def toPi : ContDiffMBMap F k U →ₗ[ℝ] ∀ j : Fin (k + 1), C(U × (Fin j → E), F) :=
  LinearMap.pi fun j ↦ iteratedDL j (Nat.lt_succ_iff.mp j.2)

/-- The differentials `d^(j)`, `j ≤ k`, separate the points of `C^k(U, F)`; in fact `d^(0)`
already does, since the elements of `C^k(U, F)` vanish outside `U`. -/
theorem toPi_injective : Function.Injective (toPi (F := F) (k := k) (U := U)) := by
  intro γ η h
  ext x
  by_cases hx : x ∈ U
  · have := congrArg (fun φ ↦ φ 0 (⟨x, hx⟩, Fin.elim0)) h
    exact this
  · rw [γ.apply_of_notMem hx, η.apply_of_notMem hx]

/-- **The compact-open `C^k` topology** ([GN26, Definition 1.7.10]): the initial topology
with respect to the maps `d^(j) : C^k(U, F) → C(U × E^j, F)`, `j ≤ k`, where the spaces of
continuous maps carry the compact-open topology. -/
instance : TopologicalSpace (ContDiffMBMap F k U) :=
  .induced toPi inferInstance

/-- **[GN26, Lemma 1.7.15]** (embedding part): `γ ↦ (d^(j)γ)_{j ≤ k}` is a linear
topological embedding `C^k(U, F) → ∏_{j ≤ k} C(U × E^j, F)`. -/
theorem isEmbedding_toPi : Topology.IsEmbedding (toPi (F := F) (k := k) (U := U)) :=
  ⟨⟨rfl⟩, toPi_injective⟩

/-- `C^k(U, F)` is a topological additive group ([GN26, Definition 1.7.10]). -/
instance : IsTopologicalAddGroup (ContDiffMBMap F k U) :=
  isTopologicalAddGroup_induced toPi

/-- Scalar multiplication on `C^k(U, F)` is continuous ([GN26, Definition 1.7.10]). -/
instance : ContinuousSMul ℝ (ContDiffMBMap F k U) :=
  continuousSMul_induced toPi

/-- `C^k(U, F)` is locally convex ([GN26, Definition 1.7.10]). -/
instance : LocallyConvexSpace ℝ (ContDiffMBMap F k U) :=
  LocallyConvexSpace.induced toPi

/-- `C^k(U, F)` is Hausdorff. -/
instance : T2Space (ContDiffMBMap F k U) :=
  isEmbedding_toPi.t2Space

/-- `γ ↦ (d^(j)γ)_{j ≤ k}` is continuous. -/
theorem continuous_toPi : Continuous (toPi (F := F) (k := k) (U := U)) :=
  continuous_induced_dom

/-- `d^(j) : C^k(U, F) → C(U × E^j, F)` is continuous. -/
theorem continuous_iteratedD (j : ℕ) (hj : j ≤ k) :
    Continuous (iteratedD (F := F) (U := U) j hj) :=
  (continuous_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1))).comp continuous_toPi

/-- `d^(j) : C^k(U, F) → C(U × E^j, F)` as a continuous linear map. -/
def iteratedDCLM (j : ℕ) (hj : j ≤ k) : ContDiffMBMap F k U →L[ℝ] C(U × (Fin j → E), F) :=
  ⟨iteratedDL j hj, continuous_iteratedD j hj⟩

/-- A map into `C^k(U, F)` is continuous if and only if its compositions with all the
differentials `d^(j)`, `j ≤ k`, are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {φ : X → ContDiffMBMap F k U} :
    Continuous φ ↔ ∀ j (hj : j ≤ k), Continuous fun x ↦ iteratedD j hj (φ x) := by
  refine ⟨fun h j hj ↦ (continuous_iteratedD j hj).comp h, fun h ↦ ?_⟩
  refine continuous_induced_rng.2 (continuous_pi fun j ↦ ?_)
  exact h j (Nat.lt_succ_iff.mp j.2)

end ContDiffMBMap

end Space

/-! ### Linear operations between spaces of `C^k` maps -/

section Operations

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {G : Type w} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G] [T2Space G]

namespace ContDiffMBMap

variable {k : ℕ} {U : Opens E}

/-! #### Lowering the order -/

/-- The inclusion `C^l(U, F) → C^k(U, F)` for `k ≤ l`. -/
def ofLE {l : ℕ} (hkl : k ≤ l) (γ : ContDiffMBMap F l U) : ContDiffMBMap F k U :=
  mk γ (γ.contDiffMBOn.of_le hkl) fun _ hx ↦ γ.apply_of_notMem hx

/-- `ofLE` does not change the underlying map. -/
@[simp]
theorem coe_ofLE {l : ℕ} (hkl : k ≤ l) (γ : ContDiffMBMap F l U) : ⇑(ofLE hkl γ) = γ :=
  rfl

/-- The inclusion `C^l(U, F) → C^k(U, F)`, `k ≤ l`, is continuous linear. -/
def ofLECLM {l : ℕ} (hkl : k ≤ l) : ContDiffMBMap F l U →L[ℝ] ContDiffMBMap F k U where
  toFun := ofLE hkl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_iff.2 fun j hj ↦ continuous_iteratedD j (hj.trans hkl)

/-! #### Pullback along continuous linear maps -/

/-- The pullback `γ ↦ γ ∘ L` along a continuous linear map `L : E₁ → E`. -/
def compRight (L : E₁ →L[ℝ] E) (γ : ContDiffMBMap F k U) :
    ContDiffMBMap F k (Opens.comap (L : C(E₁, E)) U) :=
  mk (γ ∘ L) (by simpa using γ.contDiffMBOn.comp_clm L U.isOpen)
    fun _ hx ↦ γ.apply_of_notMem (by simpa using hx)

/-- `(γ ∘ L)(x) = γ(L x)`. -/
@[simp]
theorem compRight_apply (L : E₁ →L[ℝ] E) (γ : ContDiffMBMap F k U) (x : E₁) :
    compRight L γ x = γ (L x) :=
  rfl

/-- `d^(j)(γ ∘ L)(x, v) = d^(j)γ(L x, L v₁, …, L vⱼ)`. -/
theorem iteratedD_compRight (L : E₁ →L[ℝ] E) (γ : ContDiffMBMap F k U) (j : ℕ) (hj : j ≤ k) :
    iteratedD j hj (compRight L γ) = (iteratedD j hj γ).comp
      ⟨fun p ↦ (⟨L p.1, p.1.2⟩, fun i ↦ L (p.2 i)), by fun_prop⟩ := by
  ext p
  exact iteratedDMB_comp_linearMap (⇑γ) (L : E₁ →ₗ[ℝ] E) j p.1 p.2

/-- **Pullback along a continuous linear map** `L : E₁ → E`,
`C^k(U, F) → C^k(L⁻¹(U), F)`, `γ ↦ γ ∘ L`, is continuous linear
([GN26, Proposition 1.7.11], in the special case of a linear map). -/
def compRightCLM (L : E₁ →L[ℝ] E) :
    ContDiffMBMap F k U →L[ℝ] ContDiffMBMap F k (Opens.comap (L : C(E₁, E)) U) where
  toFun := compRight L
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_iff.2 fun j hj ↦ by
    simp only [iteratedD_compRight]
    exact (ContinuousMap.continuous_precomp _).comp (continuous_iteratedD j hj)

/-! #### Postcomposition with continuous linear maps and pairs -/

/-- Postcomposition `γ ↦ g ∘ γ` with a continuous linear map `g : F → G`. -/
def compLeft (g : F →L[ℝ] G) (γ : ContDiffMBMap F k U) : ContDiffMBMap G k U :=
  mk (g ∘ γ) (ContDiffMBOn.comp U.isOpen isOpen_univ (g.contDiffMBOn k univ) γ.contDiffMBOn
    (mapsTo_univ _ _)) fun _ hx ↦ by simp [γ.apply_of_notMem hx]

/-- `(g ∘ γ)(x) = g(γ x)`. -/
@[simp]
theorem compLeft_apply (g : F →L[ℝ] G) (γ : ContDiffMBMap F k U) (x : E) :
    compLeft g γ x = g (γ x) :=
  rfl

/-- `d^(j)(g ∘ γ) = g ∘ d^(j)γ` for `g` continuous linear. -/
theorem iteratedD_compLeft (g : F →L[ℝ] G) (γ : ContDiffMBMap F k U) (j : ℕ) (hj : j ≤ k) :
    iteratedD j hj (compLeft g γ) = (g : C(F, G)).comp (iteratedD j hj γ) := by
  ext p
  exact iteratedDMB_clm_comp U.isOpen γ.contDiffMBOn g j hj p.1 p.1.2 p.2

/-- **Postcomposition with a continuous linear map** `g : F → G`,
`C^k(U, F) → C^k(U, G)`, `γ ↦ g ∘ γ`, is continuous linear ([GN26, Corollary 1.7.13],
in the special case of a linear map). -/
def compLeftCLM (g : F →L[ℝ] G) : ContDiffMBMap F k U →L[ℝ] ContDiffMBMap G k U where
  toFun := compLeft g
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := continuous_iff.2 fun j hj ↦ by
    simp only [iteratedD_compLeft]
    exact (ContinuousMap.continuous_postcomp _).comp (continuous_iteratedD j hj)

/-- The pair `x ↦ (γ x, η x)` of `γ ∈ C^k(U, F)` and `η ∈ C^k(U, G)`. -/
def prodMk (γ : ContDiffMBMap F k U) (η : ContDiffMBMap G k U) : ContDiffMBMap (F × G) k U :=
  mk (fun x ↦ (γ x, η x)) (γ.contDiffMBOn.prodMk U.isOpen η.contDiffMBOn)
    fun _ hx ↦ by simp [γ.apply_of_notMem hx, η.apply_of_notMem hx]

/-- `(γ, η)(x) = (γ x, η x)`. -/
@[simp]
theorem prodMk_apply (γ : ContDiffMBMap F k U) (η : ContDiffMBMap G k U) (x : E) :
    prodMk γ η x = (γ x, η x) :=
  rfl

/-- `d^(j)(γ, η) = (d^(j)γ, d^(j)η)`. -/
theorem iteratedD_prodMk (γ : ContDiffMBMap F k U) (η : ContDiffMBMap G k U) (j : ℕ)
    (hj : j ≤ k) :
    iteratedD j hj (prodMk γ η) = (iteratedD j hj γ).prodMk (iteratedD j hj η) := by
  ext p <;> simp only [iteratedD_apply, ContinuousMap.prod_eval]
  · exact congrArg Prod.fst
      (iteratedDMB_prodMk U.isOpen γ.contDiffMBOn η.contDiffMBOn j hj p.1 p.1.2 p.2)
  · exact congrArg Prod.snd
      (iteratedDMB_prodMk U.isOpen γ.contDiffMBOn η.contDiffMBOn j hj p.1 p.1.2 p.2)

/-- `(γ, η) ↦ (x ↦ (γ x, η x))`, `C^k(U, F) × C^k(U, G) → C^k(U, F × G)`, is continuous
linear. -/
def prodMkCLM : ContDiffMBMap F k U × ContDiffMBMap G k U →L[ℝ] ContDiffMBMap (F × G) k U where
  toFun p := prodMk p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_iff.2 fun j hj ↦ by
    simp only [iteratedD_prodMk]
    exact ContinuousMap.continuous_prodMk_pair.comp
      (((continuous_iteratedD j hj).comp continuous_fst).prodMk
        ((continuous_iteratedD j hj).comp continuous_snd))

/-- **[GN26, Corollary 1.7.14]**: `γ ↦ (pr₁ ∘ γ, pr₂ ∘ γ)` is an isomorphism of
topological vector spaces `C^k(U, F × G) ≅ C^k(U, F) × C^k(U, G)`. -/
def prodEquiv : ContDiffMBMap (F × G) k U ≃L[ℝ] ContDiffMBMap F k U × ContDiffMBMap G k U :=
  ContinuousLinearEquiv.equivOfInverse
    ((compLeftCLM (ContinuousLinearMap.fst ℝ F G)).prod
      (compLeftCLM (ContinuousLinearMap.snd ℝ F G)))
    prodMkCLM (fun γ ↦ by ext x <;> rfl) fun p ↦ by ext x <;> rfl

end ContDiffMBMap

end Operations

/-! ### The differential `d : C^{k+1}(U, F) → C^k(U × E, F)` -/

section Differential

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

/-- The open set `U × E ⊆ E × E`, the preimage of `U` under the first projection. -/
abbrev Opens.prodUniv (U : Opens E) : Opens (E × E) :=
  Opens.comap ((ContinuousLinearMap.fst ℝ E E : E × E →L[ℝ] E) : C(E × E, E)) U

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E] in
/-- The open set `Opens.prodUniv U` is `U × E`. -/
theorem Opens.coe_prodUniv (U : Opens E) :
    (Opens.prodUniv U : Set (E × E)) = (U : Set E) ×ˢ univ := by
  ext p
  simp

namespace ContDiffMBMap

variable {k : ℕ} {U : Opens E}

/-- The differential `dγ ∈ C^k(U × E, F)` of `γ ∈ C^{k+1}(U, F)` (extended by `0` outside
`U × E`). -/
def dMap (γ : ContDiffMBMap F (k + 1) U) : ContDiffMBMap F k (Opens.prodUniv U) :=
  mk ((Opens.prodUniv U : Set (E × E)).indicator (dMB γ))
    (ContDiffMBOn.congr_of_isOpen (Opens.prodUniv U).isOpen
      (fun _ hp ↦ (indicator_of_mem hp _).symm)
      (by rw [Opens.coe_prodUniv]; exact γ.contDiffMBOn.2.2))
    fun _ hp ↦ indicator_of_notMem hp _

/-- On `U × E`, `dMap γ` is the differential `dγ`. -/
theorem dMap_apply (γ : ContDiffMBMap F (k + 1) U) {p : E × E} (hp : p.1 ∈ U) :
    dMap γ p = dMB γ p :=
  indicator_of_mem (show p ∈ (Opens.prodUniv U : Set (E × E)) from hp) _

/-- Near points of `U × E`, `dMap γ` agrees with the differential `dγ`. -/
theorem dMap_eventuallyEq (γ : ContDiffMBMap F (k + 1) U) {p : E × E} (hp : p.1 ∈ U) :
    ⇑(dMap γ) =ᶠ[𝓝 p] dMB γ :=
  Filter.eventually_of_mem ((Opens.prodUniv U).isOpen.mem_nhds hp) fun _ hq ↦ dMap_apply γ hq

/-- The differential is additive. -/
theorem dMap_add (γ η : ContDiffMBMap F (k + 1) U) : dMap (γ + η) = dMap γ + dMap η := by
  ext p
  by_cases hp : p.1 ∈ U
  · simp only [coe_add, Pi.add_apply, dMap_apply _ hp]
    exact ((γ.contDiffMBOn.hasDirDerivAt hp p.2).add
      (η.contDiffMBOn.hasDirDerivAt hp p.2)).dMB_eq
  · have hp' : p ∉ Opens.prodUniv U := hp
    simp [apply_of_notMem _ hp']

/-- The differential is homogeneous. -/
theorem dMap_smul (c : ℝ) (γ : ContDiffMBMap F (k + 1) U) : dMap (c • γ) = c • dMap γ := by
  ext p
  by_cases hp : p.1 ∈ U
  · simp only [coe_smul, Pi.smul_apply, dMap_apply _ hp]
    exact ((γ.contDiffMBOn.hasDirDerivAt hp p.2).const_smul c).dMB_eq
  · have hp' : p ∉ Opens.prodUniv U := hp
    simp [apply_of_notMem _ hp']

/-- The differentials of `dγ`, as continuous maps:
`d^(j)(dγ) = d^(j+1)γ ∘ A + ∑ᵢ d^(j)γ ∘ Bᵢ`, where
`A((x, a), (v, w)) = (x, a, v₁, …, vⱼ)` and `Bᵢ((x, a), (v, w)) = (x, v₁, …, wᵢ, …, vⱼ)`. -/
theorem iteratedD_dMap (γ : ContDiffMBMap F (k + 1) U) (j : ℕ) (hj : j ≤ k) :
    iteratedD j hj (dMap γ) =
      (iteratedD (j + 1) (by omega) γ).comp
          ⟨fun p ↦ (⟨p.1.1.1, p.1.2⟩, Fin.cons p.1.1.2 fun i ↦ (p.2 i).1), by fun_prop⟩ +
        ∑ i : Fin j, (iteratedD j (by omega) γ).comp
          ⟨fun p ↦ (⟨p.1.1.1, p.1.2⟩, update (fun l ↦ (p.2 l).1) i (p.2 i).2), by fun_prop⟩ := by
  ext p
  simp only [iteratedD_apply, ContinuousMap.add_apply, ContinuousMap.sum_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [iteratedDMB_congr_of_eventuallyEq j (dMap_eventuallyEq γ p.1.2)]
  exact γ.contDiffMBOn.iteratedDMB_dMB U.isOpen j hj p.1.1.1 p.1.2 p.1.1.2 _ _

/-- **The differential** `d : C^{k+1}(U, F) → C^k(U × E, F)`, `γ ↦ dγ`, is continuous linear. -/
def dCLM : ContDiffMBMap F (k + 1) U →L[ℝ] ContDiffMBMap F k (Opens.prodUniv U) where
  toFun := dMap
  map_add' := dMap_add
  map_smul' := dMap_smul
  cont := continuous_iff.2 fun j hj ↦ by
    simp only [iteratedD_dMap]
    exact ((ContinuousMap.continuous_precomp _).comp (continuous_iteratedD _ _)).add
      (continuous_finsetSum _ fun i _ ↦
        (ContinuousMap.continuous_precomp _).comp (continuous_iteratedD _ _))

/-- The differential `d : C^{k+1}(U, F) → C^k(U × E, F)` is continuous. -/
theorem continuous_dMap : Continuous (dMap (F := F) (k := k) (U := U)) :=
  dCLM.continuous

/-- [GN26, (1.36)], for elements of `C^{k+1}(U, F)`:
`d^(j+1)γ(x, v₀, …, vⱼ) = d^(j)(dγ)((x, v₀), (v₁, 0), …, (vⱼ, 0))`. -/
theorem iteratedD_succ_eq (γ : ContDiffMBMap F (k + 1) U) (j : ℕ) (hj : j + 1 ≤ k + 1) :
    iteratedD (j + 1) hj γ = (iteratedD j (by omega) (dMap γ)).comp
      ⟨fun p ↦ (⟨(p.1, p.2 0), p.1.2⟩, fun i ↦ (p.2 i.succ, 0)), by fun_prop⟩ := by
  ext p
  simp only [iteratedD_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [iteratedDMB_succ_eq_dMB, iteratedDMB_congr_of_eventuallyEq j
    (dMap_eventuallyEq γ (p := ((p.1 : E), p.2 0)) p.1.2)]

/-- **A continuity criterion for maps into `C^{k+1}(U, F)`**: `φ : X → C^{k+1}(U, F)` is
continuous as soon as `x ↦ φ x ∈ C(U, F)` and `x ↦ d(φ x) ∈ C^k(U × E, F)` are continuous.
Together with the continuity of `d` (`ContDiffMBMap.dCLM`), this says that the topology of
`C^{k+1}(U, F)` is initial with respect to these two maps. -/
theorem continuous_of_continuous_dMap {X : Type*} [TopologicalSpace X]
    {φ : X → ContDiffMBMap F (k + 1) U}
    (h₀ : Continuous fun x ↦ iteratedD 0 (Nat.zero_le _) (φ x))
    (h₁ : Continuous fun x ↦ dMap (φ x)) : Continuous φ := by
  refine continuous_iff.2 fun j hj ↦ ?_
  cases j with
  | zero => exact h₀
  | succ j =>
    simp only [iteratedD_succ_eq]
    exact (ContinuousMap.continuous_precomp _).comp ((continuous_iteratedD _ _).comp h₁)

end ContDiffMBMap

end Differential

/-! ### Superposition operators: Proposition 1.7.12 -/

section Superposition

variable {Z : Type u} [AddCommGroup Z] [Module ℝ Z] [TopologicalSpace Z]
  [IsTopologicalAddGroup Z] [ContinuousSMul ℝ Z] [LocallyConvexSpace ℝ Z] [T2Space Z]
  {E : Type w} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace ContDiffMBMap

variable {r : ℕ} {U : Opens Z}

omit [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The graph map `x ↦ (x, γ x)` of `γ ∈ C^r(U, E)` is `C^r` on `U`. -/
theorem contDiffMBOn_graph (γ : ContDiffMBMap E r U) : ContDiffMBOn r (fun x ↦ (x, γ x)) U :=
  ContDiffMBOn.prodMk U.isOpen ((ContinuousLinearMap.id ℝ Z).contDiffMBOn r U) γ.contDiffMBOn

/-- The superposition operator `f_* : C^r(U, E) → C^r(U, F)`, `γ ↦ f ∘ (id_U, γ)`, for a map
`f : Z × E → F` of class `C^r` on `U × E` (the result is extended by `0` outside `U`). -/
def compGraph {f : Z × E → F} (hf : ContDiffMBOn r f ((U : Set Z) ×ˢ univ))
    (γ : ContDiffMBMap E r U) : ContDiffMBMap F r U :=
  mk ((U : Set Z).indicator fun x ↦ f (x, γ x))
    (ContDiffMBOn.congr_of_isOpen U.isOpen (fun _ hx ↦ (indicator_of_mem hx _).symm)
      (ContDiffMBOn.comp U.isOpen (U.isOpen.prod isOpen_univ) hf (contDiffMBOn_graph γ)
        fun _ hx ↦ ⟨hx, mem_univ _⟩))
    fun _ hx ↦ indicator_of_notMem hx _

/-- `f_* γ (x) = f(x, γ x)` for `x ∈ U`. -/
theorem compGraph_apply {f : Z × E → F} (hf : ContDiffMBOn r f ((U : Set Z) ×ˢ univ))
    (γ : ContDiffMBMap E r U) {x : Z} (hx : x ∈ U) : compGraph hf γ x = f (x, γ x) :=
  indicator_of_mem (show x ∈ (U : Set Z) from hx) fun x ↦ f (x, γ x)

/-- The `0`-th differential of `f_* γ` only depends on that of `γ`, continuously. -/
theorem continuous_iteratedD_zero_compGraph {f : Z × E → F}
    (hf : ContDiffMBOn r f ((U : Set Z) ×ˢ univ)) :
    Continuous fun γ ↦ iteratedD 0 (Nat.zero_le r) (compGraph hf γ) := by
  let f' : C((U × (Fin 0 → Z)) × E, F) :=
    ⟨fun q ↦ f (q.1.1, q.2), hf.continuousOn.comp_continuous (by fun_prop)
      fun q ↦ ⟨q.1.1.2, mem_univ _⟩⟩
  have e : (fun γ ↦ iteratedD 0 (Nat.zero_le r) (compGraph hf γ)) =
      fun γ ↦ f'.comp ((ContinuousMap.id _).prodMk (iteratedD 0 (Nat.zero_le r) γ)) := by
    funext γ
    ext p
    exact compGraph_apply hf γ p.1.2
  rw [e]
  exact (ContinuousMap.continuous_comp_graph f').comp (continuous_iteratedD 0 _)

/-- The differential of `f ∘ (id, γ)`, as a map on `U × Z × E × E`:
`(x, v, a, b) ↦ df((x, a), (v, b))`. -/
def graphDiff (f : Z × E → F) : (Z × Z) × (E × E) → F :=
  dMB f ∘ ContinuousLinearEquiv.prodProdProdComm ℝ Z Z E E

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- `(x, v, a, b) ↦ df((x, a), (v, b))` is `C^r` on `U × Z × E × E` if `f` is `C^{r+1}` on
`U × E`. -/
theorem contDiffMBOn_graphDiff {f : Z × E → F}
    (hf : ContDiffMBOn (r + 1) f ((U : Set Z) ×ˢ univ)) :
    ContDiffMBOn r (graphDiff f) ((Opens.prodUniv U : Set (Z × Z)) ×ˢ univ) := by
  have h := hf.2.2.comp_clm
    (ContinuousLinearEquiv.prodProdProdComm ℝ Z Z E E : (Z × Z) × (E × E) →L[ℝ] (Z × E) × (Z × E))
    ((U.isOpen.prod isOpen_univ).prod isOpen_univ)
  have hpre : (ContinuousLinearEquiv.prodProdProdComm ℝ Z Z E E :
      (Z × Z) × (E × E) →L[ℝ] (Z × E) × (Z × E)) ⁻¹' (((U : Set Z) ×ˢ univ) ×ˢ univ) =
      (Opens.prodUniv U : Set (Z × Z)) ×ˢ univ := by
    ext ⟨⟨x, v⟩, a, b⟩
    simp
  rw [hpre] at h
  exact h

/-- `γ ↦ (γ ∘ pr₁, dγ)`, `C^{r+1}(U, E) → C^r(U × Z, E × E)`. -/
def graphData (γ : ContDiffMBMap E (r + 1) U) : ContDiffMBMap (E × E) r (Opens.prodUniv U) :=
  prodMk (compRight (ContinuousLinearMap.fst ℝ Z Z) (ofLE (Nat.le_succ r) γ)) (dMap γ)

/-- `γ ↦ (γ ∘ pr₁, dγ)` is continuous. -/
theorem continuous_graphData : Continuous (graphData (E := E) (r := r) (U := U)) :=
  prodMkCLM.continuous.comp (((compRightCLM _).continuous.comp
    (ofLECLM (Nat.le_succ r)).continuous).prodMk
    continuous_dMap)

/-- The chain rule for superposition operators: `d(f_* γ) = (df)_*(γ ∘ pr₁, dγ)`. -/
theorem dMap_compGraph {f : Z × E → F} (hf : ContDiffMBOn (r + 1) f ((U : Set Z) ×ˢ univ))
    (γ : ContDiffMBMap E (r + 1) U) :
    dMap (compGraph hf γ) = compGraph (contDiffMBOn_graphDiff hf) (graphData γ) := by
  ext p
  by_cases hp : p.1 ∈ U
  · rw [dMap_apply _ hp, compGraph_apply _ _ (show p ∈ Opens.prodUniv U from hp)]
    have hev : ⇑(compGraph hf γ) =ᶠ[𝓝 p.1] f ∘ fun x ↦ (x, γ x) :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hp) fun x hx ↦ compGraph_apply hf γ hx
    rw [show p = (p.1, p.2) from rfl, dMB_congr_of_eventuallyEq hev,
      ContDiffMBOn.dMB_comp (U.isOpen.prod isOpen_univ) (hf.of_le (by omega))
        ((contDiffMBOn_graph γ).of_le (by omega)) (fun _ hx ↦ ⟨hx, mem_univ _⟩) hp]
    have hd : HasDirDerivAt (fun x ↦ (x, γ x)) p.1 p.2 (p.2, dMB γ (p.1, p.2)) :=
      ((ContinuousLinearMap.id ℝ Z).hasDirDerivAt p.1 p.2).prodMk
        (γ.contDiffMBOn.hasDirDerivAt hp p.2)
    rw [hd.dMB_eq]
    simp [graphDiff, graphData, dMap_apply γ hp]
  · rw [apply_of_notMem _ (show p ∉ Opens.prodUniv U from hp),
      apply_of_notMem _ (show p ∉ Opens.prodUniv U from hp)]


/-- **[GN26, Proposition 1.7.12]**: for `f : Z × E → F` of class `C^r` on `U × E`, the
superposition operator `f_* : C^r(U, E) → C^r(U, F)`, `γ ↦ f ∘ (id_U, γ)`, is continuous.

Instead of Faà di Bruno's formula, the proof uses induction on `r`, the chain rule
`d(f_* γ) = (df)_*(γ ∘ pr₁, dγ)` (`ContDiffMBMap.dMap_compGraph`), the continuity of
`d : C^{r+1}(U, E) → C^r(U × Z, E)` (`ContDiffMBMap.dCLM`) and the continuity criterion
`ContDiffMBMap.continuous_of_continuous_dMap`. -/
theorem continuous_compGraph {f : Z × E → F} (hf : ContDiffMBOn r f ((U : Set Z) ×ˢ univ)) :
    Continuous (compGraph hf) := by
  induction r generalizing Z E with
  | zero =>
    refine continuous_iff.2 fun j hj ↦ ?_
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact continuous_iteratedD_zero_compGraph hf
  | succ r ih =>
    refine continuous_of_continuous_dMap (continuous_iteratedD_zero_compGraph hf) ?_
    simp only [dMap_compGraph hf]
    exact (ih (contDiffMBOn_graphDiff hf)).comp continuous_graphData

/-- The superposition operator `C^k(U, g) : C^k(U, E) → C^k(U, F)`, `γ ↦ g ∘ γ`, for a map
`g : E → F` of class `C^k` (the result is extended by `0` outside `U`). -/
def compLeftOfContDiff {g : E → F} (hg : ContDiffMBOn r g univ) :
    ContDiffMBMap E r U → ContDiffMBMap F r U :=
  compGraph (f := g ∘ Prod.snd) <| by
    have h := hg.comp_clm (ContinuousLinearMap.snd ℝ Z E) isOpen_univ
    rw [preimage_univ] at h
    exact h.mono (subset_univ _)

/-- `C^k(U, g)(γ)(x) = g(γ x)` for `x ∈ U`. -/
theorem compLeftOfContDiff_apply {g : E → F} (hg : ContDiffMBOn r g univ)
    (γ : ContDiffMBMap E r U) {x : Z} (hx : x ∈ U) : compLeftOfContDiff hg γ x = g (γ x) :=
  compGraph_apply _ γ hx

/-- **[GN26, Corollary 1.7.13]**: for `g : E → F` of class `C^k`, the superposition
operator `C^k(U, g) : C^k(U, E) → C^k(U, F)`, `γ ↦ g ∘ γ`, is continuous. -/
theorem continuous_compLeftOfContDiff {g : E → F} (hg : ContDiffMBOn r g univ) :
    Continuous (compLeftOfContDiff (U := U) hg) :=
  continuous_compGraph _

end ContDiffMBMap

end Superposition

/-! ### Lemma 1.7.15: the image of `toPi` is closed -/

section ClosedImage

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [LocallyConvexSpace ℝ E] [T2Space E] in
/-- **Limits of differentiable maps.** Let `gᵢ → g₀` pointwise on the open set `U` along a
nontrivial filter, where (eventually) each `gᵢ` has continuous directional derivatives `Dᵢ z` in
the direction `y` at the points `z ∈ U`, and let `Dᵢ → D₀` in the compact-open sense on `U` (for
every compact `K ⊆ U` and open `O ⊇ D₀(K)`, eventually `Dᵢ(K) ⊆ O`), with `D₀` continuous.
Then `g₀` has directional derivative `D₀ x` in the direction `y` at every `x ∈ U`.

This plays the role of [GN26, Exercise 1.1.13(b)] (limits of `C^1` curves whose
derivatives converge uniformly), which they prove with weak integrals; here we use the mean value
inclusion `sub_mem_of_hasDirDerivAt`, and no completeness is needed. -/
theorem hasDirDerivAt_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {g D : ι → E → F}
    {g₀ D₀ : E → F} {U : Set E} (hU : IsOpen U) {y : E}
    (hd : ∀ᶠ i in l, ∀ z ∈ U, HasDirDerivAt (g i) z y (D i z))
    (hDc : ∀ᶠ i in l, ContinuousOn (D i) U)
    (hg : ∀ z ∈ U, Tendsto (fun i ↦ g i z) l (𝓝 (g₀ z)))
    (hD : ∀ K ⊆ U, IsCompact K → ∀ O, IsOpen O → MapsTo D₀ K O → ∀ᶠ i in l, MapsTo (D i) K O)
    (hD₀ : ContinuousOn D₀ U) {x : E} (hx : x ∈ U) : HasDirDerivAt g₀ x y (D₀ x) := by
  rw [HasDirDerivAt, tendsto_iff_forall_eventually_mem]
  intro N hN
  obtain ⟨W, hW, hWcl, hWc, hWN⟩ := exists_closed_convex_nhds_subset hN
  -- a segment around `x` on which `D₀` stays in the interior of `W`
  have hc : Continuous fun s : ℝ ↦ x + s • y := by fun_prop
  have hS : {s : ℝ | x + s • y ∈ U ∧ D₀ (x + s • y) ∈ interior W} ∈ 𝓝 (0 : ℝ) := by
    have h1 : U ∩ D₀ ⁻¹' interior W ∈ 𝓝 x :=
      inter_mem (hU.mem_nhds hx) ((hD₀.continuousAt (hU.mem_nhds hx)).preimage_mem_nhds
        (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hW)))
    have h2 := (hc.tendsto 0)
    simp only [zero_smul, add_zero] at h2
    exact h2 h1
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  set K := (fun s : ℝ ↦ x + s • y) '' Icc (-(ε / 2)) (ε / 2)
  have hsK : ∀ s ∈ Icc (-(ε / 2)) (ε / 2), x + s • y ∈ U ∧ D₀ (x + s • y) ∈ interior W :=
    fun s hs ↦ hεS (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hs.1, hs.2])
  have hKU : K ⊆ U := by rintro _ ⟨s, hs, rfl⟩; exact (hsK s hs).1
  have hKO : MapsTo D₀ K (interior W) := by rintro _ ⟨s, hs, rfl⟩; exact (hsK s hs).2
  have hev := hD K hKU (isCompact_Icc.image hc) _ isOpen_interior hKO
  have ht : Ioo (-(ε / 2)) (ε / 2) ∈ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [ht, self_mem_nhdsWithin] with t ht ht0
  have ht0 : t ≠ 0 := ht0
  refine hWN ?_
  have hxt : x + t • y ∈ U := (hsK t (Ioo_subset_Icc_self ht)).1
  have hlim : Tendsto (fun i ↦ t⁻¹ • (g i (x + t • y) - g i x)) l
      (𝓝 (t⁻¹ • (g₀ (x + t • y) - g₀ x))) :=
    ((hg _ hxt).sub (hg x hx)).const_smul t⁻¹
  refine hWcl.mem_of_tendsto hlim ?_
  filter_upwards [hev, hd, hDc] with i hi hdi hDci
  -- the mean value inclusion for `g i` on the segment from `x` to `x + t • y`
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, x + s • t • y ∈ K := fun s hs ↦ by
    refine ⟨s * t, ⟨?_, ?_⟩, by simp only [mul_smul]⟩ <;>
    rcases le_total 0 t with h | h <;> nlinarith [ht.1, ht.2, hs.1, hs.2]
  have h := sub_mem_of_hasDirDerivAt (f := g i) (z := x) (w := t • y)
    (D := fun s ↦ t • D i (x + s • t • y))
    (fun s hs ↦ (hdi _ (hKU (hmem s hs))).smul_dir t)
    (continuousOn_const.smul (hDci.comp (by fun_prop) fun s hs ↦ hKU (hmem s hs)))
    (hWc.smul_preimage t⁻¹) (hWcl.preimage (continuous_const_smul t⁻¹))
    (fun s hs ↦ by
      change t⁻¹ • t • D i (x + s • t • y) ∈ W
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      exact interior_subset (hi (hmem s hs)))
  exact h

namespace ContDiffMBMap

variable {k : ℕ} {U : Opens E}

/-- The candidate preimage of a family `h = (hⱼ)_{j ≤ k}` under `toPi`, at level `j`: `hⱼ` on
`U × E^j`, extended by `0`. -/
def extendPi (h : ∀ j : Fin (k + 1), C(U × (Fin j → E), F)) (j : ℕ) (hj : j ≤ k) :
    E × (Fin j → E) → F := fun p ↦ by
  classical
  exact if hp : p.1 ∈ U then h ⟨j, Nat.lt_succ_of_le hj⟩ (⟨p.1, hp⟩, p.2) else 0

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- The values of `extendPi` on `U × E^j`. -/
theorem extendPi_of_mem (h : ∀ j : Fin (k + 1), C(U × (Fin j → E), F)) {j : ℕ} (hj : j ≤ k)
    {x : E} (hx : x ∈ U) (v : Fin j → E) :
    extendPi h j hj (x, v) = h ⟨j, Nat.lt_succ_of_le hj⟩ (⟨x, hx⟩, v) := by
  simp [extendPi, hx]

omit [AddCommGroup E] [Module ℝ E] [Module ℝ F] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] [T2Space E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `extendPi` is continuous on `U × E^j`. -/
theorem continuousOn_extendPi (h : ∀ j : Fin (k + 1), C(U × (Fin j → E), F)) {j : ℕ}
    (hj : j ≤ k) : ContinuousOn (extendPi h j hj) ((U : Set E) ×ˢ univ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun q : ((U : Set E) ×ˢ (univ : Set (Fin j → E))) ↦
      h ⟨j, Nat.lt_succ_of_le hj⟩ (⟨q.1.1, q.2.1⟩, q.1.2) :=
    (h _).continuous.comp (by fun_prop)
  refine hc.congr fun q ↦ ?_
  exact (extendPi_of_mem h hj q.2.1 q.1.2).symm

/-- **[GN26, Lemma 1.7.15]** (closed image): the image of
`γ ↦ (d^(j)γ)_{j ≤ k}`, `C^k(U, F) → ∏_{j ≤ k} C(U × E^j, F)`, is closed. -/
theorem isClosed_range_toPi : IsClosed (range (toPi (F := F) (k := k) (U := U))) := by
  refine closure_subset_iff_isClosed.1 fun h hh ↦ ?_
  set l := Filter.comap (toPi (F := F) (k := k) (U := U)) (𝓝 h)
  have hl : l.NeBot := by
    refine Filter.comap_neBot fun t ht ↦ ?_
    obtain ⟨_, hz, γ, rfl⟩ := mem_closure_iff_nhds.1 hh t ht
    exact ⟨γ, hz⟩
  have hlim : ∀ j (hj : j ≤ k), Tendsto (iteratedD j hj) l
      (𝓝 (h ⟨j, Nat.lt_succ_of_le hj⟩)) := fun j hj ↦
    ((continuous_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1))).tendsto h).comp tendsto_comap
  have hpt : ∀ j (hj : j ≤ k), ∀ x ∈ U, ∀ v : Fin j → E,
      Tendsto (fun γ : ContDiffMBMap F k U ↦ iteratedDMB j γ (x, v)) l
        (𝓝 (extendPi h j hj (x, v))) := fun j hj x hx v ↦ by
    rw [extendPi_of_mem h hj hx]
    exact ((continuous_eval_const (⟨x, hx⟩, v)).tendsto _).comp (hlim j hj)
  obtain ⟨f, hfdef⟩ : ∃ f : E → F, f = fun x ↦ extendPi h 0 (Nat.zero_le k) (x, Fin.elim0) :=
    ⟨_, rfl⟩
  have hder : ∀ j (hj : j + 1 ≤ k), ∀ x ∈ U, ∀ v : Fin (j + 1) → E,
      HasDirDerivAt (fun z ↦ extendPi h j (by omega) (z, Fin.init v)) x
        (v (Fin.last j)) (extendPi h (j + 1) hj (x, v)) := by
    intro j hj x hx v
    refine hasDirDerivAt_of_tendsto (g := fun γ z ↦ iteratedDMB j γ (z, Fin.init v))
      (D := fun γ z ↦ iteratedDMB (j + 1) γ (z, v)) (l := l) U.isOpen
      (Eventually.of_forall fun γ z hz ↦
        γ.contDiffMBOn.hasContIterDerivOn.1 j (by omega) z hz v)
      (Eventually.of_forall fun γ ↦ (γ.contDiffMBOn.hasContIterDerivOn.2 (j + 1) hj).comp
        (Continuous.prodMk_left v).continuousOn fun z hz ↦ ⟨hz, mem_univ _⟩)
      (fun z hz ↦ hpt j (by omega) z hz _) ?_
      ((continuousOn_extendPi h hj).comp (Continuous.prodMk_left v).continuousOn
        fun z hz ↦ ⟨hz, mem_univ _⟩) hx
    intro K hKU hK O hO hKO
    let K' : Set (U × (Fin (j + 1) → E)) :=
      (fun z : U ↦ (z, v)) '' ((↑) ⁻¹' K)
    have hK' : IsCompact K' := by
      refine IsCompact.image ?_ (by fun_prop)
      rw [Subtype.isCompact_iff, image_preimage_eq_of_subset (by rwa [Subtype.range_coe])]
      exact hK
    have hmaps : MapsTo (h ⟨j + 1, Nat.lt_succ_of_le hj⟩) K' O := by
      rintro _ ⟨z, hz, rfl⟩
      have := hKO hz
      simp only [Function.comp_apply] at this
      rwa [extendPi_of_mem h hj z.2] at this
    have h2 : ∀ᶠ γ in l, MapsTo (iteratedD (j + 1) hj γ) K' O :=
      (hlim (j + 1) hj).eventually (ContinuousMap.eventually_mapsTo hK' hO hmaps)
    filter_upwards [h2] with γ hγ z hz
    have hmem : ((⟨z, hKU hz⟩ : U), v) ∈ K' := ⟨⟨z, hKU hz⟩, hz, rfl⟩
    simpa only [iteratedD_apply] using hγ hmem
  -- the differentials of `f` are the components of `h`
  have key : ∀ j (hj : j ≤ k), ∀ x ∈ U, ∀ v : Fin j → E,
      iteratedDMB j f (x, v) = extendPi h j hj (x, v) := by
    intro j
    induction j with
    | zero =>
      intro hj x hx v
      rw [Subsingleton.elim v Fin.elim0, hfdef]
      rfl
    | succ j ih =>
      intro hj x hx v
      rw [iteratedDMB_succ j f x v]
      have hev : (fun z ↦ iteratedDMB j f (z, Fin.init v)) =ᶠ[𝓝 x]
          fun z ↦ extendPi h j (by omega) (z, Fin.init v) :=
        Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz ↦ ih (by omega) z hz _
      rw [dMB_congr_of_eventuallyEq hev, (hder j hj x hx v).dMB_eq]
  have hf : ContDiffMBOn k f U := by
    refine HasContIterDerivOn.contDiffMBOn U.isOpen ⟨fun j hj x hx v ↦ ?_, fun j hj ↦ ?_⟩
    · rw [key (j + 1) hj x hx v]
      have hev : (fun z ↦ extendPi h j (by omega) (z, Fin.init v)) =ᶠ[𝓝 x]
          fun z ↦ iteratedDMB j f (z, Fin.init v) :=
        Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun z hz ↦ (key j (by omega) z hz _).symm
      exact (hder j hj x hx v).congr_of_eventuallyEq hev
    · exact (continuousOn_extendPi h hj).congr fun p hp ↦ key j hj p.1 hp.1 p.2
  have h0 : ∀ x ∉ U, f x = 0 := fun x hx ↦ by simp [hfdef, extendPi, hx]
  refine ⟨mk f hf h0, ?_⟩
  funext j
  ext p
  have e : toPi (mk f hf h0) j p = iteratedDMB j f ((p.1 : E), p.2) := rfl
  rw [e, key j (Nat.lt_succ_iff.mp j.2) p.1 p.1.2 p.2, extendPi_of_mem]

end ContDiffMBMap

end ClosedImage

/-! ### Pullbacks: Proposition 1.7.11 -/

section Pullback

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type w} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

namespace ContDiffMBMap

variable {r : ℕ} {U : Opens E₁} {V : Opens E₂}

/-- The pullback `f^* : C^r(V, F) → C^r(U, F)`, `γ ↦ γ ∘ f`, along a map `f : E₁ → E₂` of class
`C^r` on `U` with `f(U) ⊆ V` (the result is extended by `0` outside `U`). -/
def compRightOfContDiff {f : E₁ → E₂} (hf : ContDiffMBOn r f U) (hUV : MapsTo f U V)
    (γ : ContDiffMBMap F r V) : ContDiffMBMap F r U :=
  mk ((U : Set E₁).indicator (γ ∘ f))
    (ContDiffMBOn.congr_of_isOpen U.isOpen (fun _ hx ↦ (indicator_of_mem hx _).symm)
      (ContDiffMBOn.comp U.isOpen V.isOpen γ.contDiffMBOn hf hUV))
    fun _ hx ↦ indicator_of_notMem hx _

/-- `f^* γ (x) = γ (f x)` for `x ∈ U`. -/
theorem compRightOfContDiff_apply {f : E₁ → E₂} (hf : ContDiffMBOn r f U) (hUV : MapsTo f U V)
    (γ : ContDiffMBMap F r V) {x : E₁} (hx : x ∈ U) :
    compRightOfContDiff hf hUV γ x = γ (f x) :=
  indicator_of_mem (show x ∈ (U : Set E₁) from hx) (γ ∘ f)

/-- The `0`-th differential of `f^* γ` depends continuously on that of `γ`. -/
theorem continuous_iteratedD_zero_compRightOfContDiff {f : E₁ → E₂} (hf : ContDiffMBOn r f U)
    (hUV : MapsTo f U V) :
    Continuous fun γ : ContDiffMBMap F r V ↦
      iteratedD 0 (Nat.zero_le r) (compRightOfContDiff hf hUV γ) := by
  have hc : Continuous fun x : U ↦ (⟨f x, hUV x.2⟩ : V) :=
    (hf.continuousOn.domRestrict).subtype_mk _
  let A : C(U × (Fin 0 → E₁), V × (Fin 0 → E₂)) :=
    ⟨fun p ↦ (⟨f p.1, hUV p.1.2⟩, Fin.elim0), (hc.comp continuous_fst).prodMk continuous_const⟩
  have e : (fun γ : ContDiffMBMap F r V ↦
      iteratedD 0 (Nat.zero_le r) (compRightOfContDiff hf hUV γ)) =
      fun γ ↦ (iteratedD 0 (Nat.zero_le r) γ).comp A := by
    funext γ
    ext p
    exact compRightOfContDiff_apply hf hUV γ p.1.2
  rw [e]
  exact (ContinuousMap.continuous_precomp A).comp (continuous_iteratedD 0 _)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] in
/-- `(x, v) ↦ (f x, df(x, v))` is `C^r` on `U × E₁` if `f` is `C^{r+1}` on `U`. -/
theorem contDiffMBOn_tangentMap {f : E₁ → E₂} (hf : ContDiffMBOn (r + 1) f U) :
    ContDiffMBOn r (fun p : E₁ × E₁ ↦ (f p.1, dMB f p)) (Opens.prodUniv U) := by
  have h1 := (hf.of_le (Nat.le_succ r)).comp_clm (ContinuousLinearMap.fst ℝ E₁ E₁) U.isOpen
  have h2 := hf.2.2
  rw [← Opens.coe_prodUniv] at h2
  exact ContDiffMBOn.prodMk (Opens.prodUniv U).isOpen h1 h2

omit [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- `(x, v) ↦ (f x, df(x, v))` maps `U × E₁` to `V × E₂` if `f(U) ⊆ V`. -/
theorem mapsTo_tangentMap {f : E₁ → E₂} (hUV : MapsTo f U V) :
    MapsTo (fun p : E₁ × E₁ ↦ (f p.1, dMB f p)) (Opens.prodUniv U) (Opens.prodUniv V) :=
  fun _ hp ↦ hUV hp

/-- The chain rule for pullbacks: `d(f^* γ) = (f, df)^*(dγ)`. -/
theorem dMap_compRightOfContDiff {f : E₁ → E₂} (hf : ContDiffMBOn (r + 1) f U)
    (hUV : MapsTo f U V) (γ : ContDiffMBMap F (r + 1) V) :
    dMap (compRightOfContDiff hf hUV γ) =
      compRightOfContDiff (contDiffMBOn_tangentMap hf) (mapsTo_tangentMap hUV) (dMap γ) := by
  ext p
  by_cases hp : p.1 ∈ U
  · rw [dMap_apply _ hp, compRightOfContDiff_apply (contDiffMBOn_tangentMap hf)
      (mapsTo_tangentMap hUV) _ (show p ∈ Opens.prodUniv U from hp),
      dMap_apply γ (show f p.1 ∈ V from hUV hp)]
    have hev : ⇑(compRightOfContDiff hf hUV γ) =ᶠ[𝓝 p.1] ⇑γ ∘ f :=
      Filter.eventually_of_mem (U.isOpen.mem_nhds hp) fun x hx ↦
        compRightOfContDiff_apply hf hUV γ hx
    rw [show p = (p.1, p.2) from rfl, dMB_congr_of_eventuallyEq hev,
      ContDiffMBOn.dMB_comp V.isOpen (γ.contDiffMBOn.of_le (by omega)) (hf.of_le (by omega))
        hUV hp]
  · rw [apply_of_notMem _ (show p ∉ Opens.prodUniv U from hp),
      apply_of_notMem _ (show p ∉ Opens.prodUniv U from hp)]

/-- **[GN26, Proposition 1.7.11]**: for `f : E₁ → E₂` of class `C^r` on `U` with
`f(U) ⊆ V`, the pullback `f^* : C^r(V, F) → C^r(U, F)`, `γ ↦ γ ∘ f`, is continuous.

Glöckner–Neeb use Faà di Bruno's formula; the proof here is an induction on `r`, with the chain
rule `d(f^* γ) = (f, df)^*(dγ)` (`ContDiffMBMap.dMap_compRightOfContDiff`). -/
theorem continuous_compRightOfContDiff {f : E₁ → E₂} (hf : ContDiffMBOn r f U)
    (hUV : MapsTo f U V) : Continuous (compRightOfContDiff (F := F) hf hUV) := by
  induction r generalizing E₁ E₂ with
  | zero =>
    refine continuous_iff.2 fun j hj ↦ ?_
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    exact continuous_iteratedD_zero_compRightOfContDiff hf hUV
  | succ r ih =>
    refine continuous_of_continuous_dMap
      (continuous_iteratedD_zero_compRightOfContDiff hf hUV) ?_
    simp only [dMap_compRightOfContDiff hf hUV]
    exact (ih (contDiffMBOn_tangentMap hf) _).comp continuous_dMap

/-- **[GN26, Proposition 1.7.11]**: the pullback `f^* : C^r(V, F) → C^r(U, F)` as a
continuous linear map. -/
def compRightOfContDiffCLM {f : E₁ → E₂} (hf : ContDiffMBOn r f U) (hUV : MapsTo f U V) :
    ContDiffMBMap F r V →L[ℝ] ContDiffMBMap F r U where
  toFun := compRightOfContDiff hf hUV
  map_add' γ η := by
    ext x
    by_cases hx : x ∈ U
    · simp [compRightOfContDiff_apply hf hUV _ hx]
    · simp [apply_of_notMem _ hx]
  map_smul' c γ := by
    ext x
    by_cases hx : x ∈ U
    · simp [compRightOfContDiff_apply hf hUV _ hx]
    · simp [apply_of_notMem _ hx]
  cont := continuous_compRightOfContDiff hf hUV

end ContDiffMBMap

end Pullback

end LocallyConvex.Analysis

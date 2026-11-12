/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Real
public import LocallyConvexAnalysis.Analytic.HomogeneousSeries
public import LocallyConvexAnalysis.Analytic.HartogsLemma
public import Mathlib.Algebra.Group.ForwardDiff

/-! # Series of real homogeneous polynomials

The real case of Bochnak–Siciak, *Analytic functions in topological vector spaces*, Studia Math.
39 (1971), part II: a series of continuous real homogeneous polynomials which is bounded at each
point of a neighbourhood of `0` has a complexification which converges, with geometric bounds,
on a neighbourhood of `0` in `E_ℂ` (Proposition 5.4). Consequently, when `E_ℂ` is a Baire space
and `F` is Mackey complete, analyticity in the sense of Bochnak and Siciak coincides with
Milnor's real analyticity, the existence of a complex analytic extension (Theorem 7.1;
[GN26, Remark 2.2.7]).

## Main results

* `ContinuousMultilinearMap.complexify`: the complex multilinear extension
  `A_ℂ : E_ℂⁿ → F_ℂ` of a continuous real multilinear map, and `IsContHomPoly.complexify`, the
  complexification of a continuous real homogeneous polynomial.
* `IsContHomPoly.sum_fwdDiff`: the `n`-th forward difference of a homogeneous polynomial of
  degree `n` is `n!` times its value, at every base point; `exists_plane_bound` turns pointwise
  bounds on a real plane into exponential bounds (Baire's theorem in `ℝ²`).
* `mk_add_circleMap_smul_auxDir`: the complex line through `x + i y` with direction
  `(x - i y)/2` meets the complex multiples of real vectors exactly on the circle `|λ| = 2`.
* `posLog_seminorm_le_integral_circle`: Jensen's inequality on that line bounds the complexified
  polynomial at `x + i y` by its values at the real points `cos (θ/2) x + sin (θ/2) y`.
* `exists_nhds_complexify_geometric`, `exists_nhds_hasSum_complexify`: **Bochnak–Siciak,
  Proposition 5.4**, with the ratio `9/10` independent of the point and of the seminorm.
* `realAnalyticOn_of_bsAnalyticOn`, `realAnalyticOn_iff_bsAnalyticOn`: **Bochnak–Siciak,
  Theorem 7.1**, for a Mackey complete target.

## Implementation notes

* Bochnak and Siciak prove Proposition 5.4 with Siciak's polynomial lemma for a real segment,
  whose proof rests on potential theory (Siciak's extremal function, Fekete points, continuity of
  the extremal function along increasing unions of compact sets). It is replaced here by an
  elementary device: on the auxiliary line `λ ↦ (x + i y) + λ (x - i y)/2`, the points with
  `|λ| = 2` are `2 e^{iθ/2} (cos (θ/2) x + sin (θ/2) y)`, where the complexified polynomial is
  known from its real values. Jensen's inequality (`posLog_le_circleAverage`) and dominated
  convergence on the circle then give the bounds at the centre `x + i y`; the uniform bound
  needed for dominated convergence comes from Baire's theorem in the real plane
  `span {x, y}`, so no Baire assumption on `E` is needed for Proposition 5.4.
* As in the complex case (`MackeyComplete.exists_hasSum_of_geometric`), the ratio of the
  geometric bounds does not depend on the seminorm, so Mackey completeness of `F` suffices where
  Bochnak and Siciak assume sequential completeness.
* The Baire property is assumed for `E_ℂ = E × E`; it holds for Fréchet spaces
  (`Complexification.baireSpace`). Products of Baire spaces need not be Baire.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
* [J. Bochnak, J. Siciak, *Polynomials and multilinear mappings in topological
  vector-spaces*][BS71a]
* [J. Bochnak, J. Siciak, *Analytic functions in topological vector-spaces*][BS71b]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology Pointwise

noncomputable section

namespace LocallyConvex.Analysis

universe u v

open Complexification

/-! ### Complexification of continuous multilinear maps -/

section Complexify

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Selecting, in each slot `i`, the imaginary part if `i ∈ S` and the real part otherwise. -/
def selReIm (S : Finset ι) (i : ι) : Complexification E →L[ℝ] E :=
  if i ∈ S then imCLM else reCLM

omit [Fintype ι] in
theorem selReIm_of_mem {S : Finset ι} {i : ι} (h : i ∈ S) :
    (selReIm S i : Complexification E →L[ℝ] E) = imCLM := by simp [selReIm, h]

omit [Fintype ι] in
theorem selReIm_of_not_mem {S : Finset ι} {i : ι} (h : i ∉ S) :
    (selReIm S i : Complexification E →L[ℝ] E) = reCLM := by simp [selReIm, h]

/-- Multiplication by `c : ℂ` on `F_ℂ`, composed with `F ↪ F_ℂ`. -/
def ofRealMul (c : ℂ) : F →L[ℝ] Complexification F :=
  ((c • ContinuousLinearMap.id ℂ (Complexification F)).restrictScalars ℝ).comp ofReal

@[simp] theorem ofRealMul_apply (c : ℂ) (w : F) : ofRealMul c w = c • ofReal w := rfl

variable (A : ContinuousMultilinearMap ℝ (fun _ : ι ↦ E) F)

/-- The real multilinear map `z ↦ ∑_S i^{|S|} A(w_S)`, `w_S i = Im zᵢ` for `i ∈ S` and
`Re zᵢ` otherwise: the expansion of `A (z₁, …, zₙ)` for `zⱼ = Re zⱼ + i Im zⱼ`. -/
def complexifyReal :
    ContinuousMultilinearMap ℝ (fun _ : ι ↦ Complexification E) (Complexification F) :=
  ∑ S : Finset ι, (ofRealMul (Complex.I ^ S.card)).compContinuousMultilinearMap
    (A.compContinuousLinearMap (selReIm S))

theorem complexifyReal_apply (z : ι → Complexification E) :
    complexifyReal A z = ∑ S : Finset ι,
      Complex.I ^ S.card • ofReal (A fun i ↦ selReIm S i (z i)) := by
  simp [complexifyReal]

/-- Splitting a sum over subsets according to whether they contain `j`. -/
theorem sum_finset_eq_sum_not_mem {M : Type*} [AddCommMonoid M] (f : Finset ι → M) (j : ι) :
    ∑ S : Finset ι, f S = ∑ S ∈ Finset.univ.filter (fun S ↦ j ∉ S), (f S + f (insert j S)) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S ↦ j ∉ S)]
  congr 1
  refine Finset.sum_bij' (fun S _ ↦ S.erase j) (fun S _ ↦ insert j S) (fun S hS ↦ ?_)
    (fun S hS ↦ ?_) (fun S hS ↦ ?_) (fun S hS ↦ ?_) (fun S hS ↦ ?_)
  · simp
  · simp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hS
    exact Finset.insert_erase hS
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact Finset.erase_insert hS
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hS
    rw [Finset.insert_erase hS]

/-- The slot `j` of the expansion: `A_ℂ(…, u, …) = R (Re u) + i R (Im u)` with `R` real
linear. -/
theorem complexifyReal_update (z : ι → Complexification E) (j : ι) (u : Complexification E) :
    complexifyReal A (update z j u) =
      ∑ S ∈ Finset.univ.filter (fun S ↦ j ∉ S), Complex.I ^ S.card •
        ofReal (A (update (fun i ↦ selReIm S i (z i)) j (re u))) +
      Complex.I • ∑ S ∈ Finset.univ.filter (fun S ↦ j ∉ S), Complex.I ^ S.card •
        ofReal (A (update (fun i ↦ selReIm S i (z i)) j (im u))) := by
  rw [complexifyReal_apply, sum_finset_eq_sum_not_mem _ j, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S hS ↦ ?_
  have hjS : j ∉ S := (Finset.mem_filter.1 hS).2
  have e1 : (fun i ↦ selReIm S i (update z j u i)) =
      update (fun i ↦ selReIm S i (z i)) j (re u) := by
    ext1 i
    by_cases hi : i = j
    · subst hi; simp [selReIm_of_not_mem hjS]
    · simp [hi]
  have e2 : (fun i ↦ selReIm (insert j S) i (update z j u i)) =
      update (fun i ↦ selReIm S i (z i)) j (im u) := by
    ext1 i
    by_cases hi : i = j
    · subst hi; simp [selReIm_of_mem (Finset.mem_insert_self i S)]
    · have : selReIm (E := E) (insert j S) i = selReIm S i := by
        simp [selReIm, Finset.mem_insert, hi]
      simp [hi, this]
  rw [e1, e2, Finset.card_insert_of_notMem hjS, pow_succ, mul_comm, mul_smul]

/-- `A_ℂ` commutes with complex scalars in each slot. -/
theorem complexifyReal_update_smul (z : ι → Complexification E) (j : ι) (c : ℂ)
    (u : Complexification E) :
    complexifyReal A (update z j (c • u)) = c • complexifyReal A (update z j u) := by
  refine map_smul_of_map_I_smul (T := fun u ↦ complexifyReal A (update z j u))
    (fun v w ↦ (complexifyReal A).map_update_add z j v w)
    (fun r w ↦ (complexifyReal A).map_update_smul z j r w) (fun w ↦ ?_) c u
  rw [complexifyReal_update, complexifyReal_update, smul_add, smul_smul, Complex.I_mul_I,
    neg_one_smul, add_comm]
  simp only [re_smul, im_smul, Complex.I_re, Complex.I_im, zero_smul, one_smul, zero_sub,
    zero_add]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [← neg_one_smul ℝ (im w), A.map_update_smul, map_smul, neg_one_smul, smul_neg]

/-- The complex multilinear extension of a continuous real multilinear map:
`A_ℂ (x₁ + i y₁, …, xₙ + i yₙ)`, complex multilinear and continuous. -/
def _root_.ContinuousMultilinearMap.complexify :
    ContinuousMultilinearMap ℂ (fun _ : ι ↦ Complexification E) (Complexification F) where
  toFun := complexifyReal A
  map_update_add' := by
    intro _ z j u v
    convert (complexifyReal A).map_update_add z j u v
  map_update_smul' := by
    intro _ z j c u
    convert complexifyReal_update_smul A z j c u
  cont := (complexifyReal A).cont

theorem _root_.ContinuousMultilinearMap.complexify_apply (z : ι → Complexification E) :
    A.complexify z = ∑ S : Finset ι,
      Complex.I ^ S.card • ofReal (A fun i ↦ selReIm S i (z i)) :=
  complexifyReal_apply A z

/-- `A_ℂ` extends `A`. -/
theorem _root_.ContinuousMultilinearMap.complexify_apply_ofReal (v : ι → E) :
    A.complexify (fun i ↦ ofReal (v i)) = ofReal (A v) := by
  rw [A.complexify_apply, Finset.sum_eq_single ∅]
  · simp [selReIm_of_not_mem (Finset.notMem_empty _)]
  · intro S _ hS
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
    have : (A fun k ↦ selReIm S k (ofReal (v k))) = 0 :=
      A.map_coord_zero i (by simp [selReIm_of_mem hi])
    simp [this]
  · simp

end Complexify

/-! ### Complexification of continuous homogeneous polynomials -/

section ComplexifyPoly

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {n : ℕ} {p : E → F}

/-- The complexification `p_ℂ : E_ℂ → F_ℂ` of a continuous real homogeneous polynomial: the
diagonal of the complexification of a multilinear map whose diagonal is `p`. -/
def IsContHomPoly.complexify (hp : IsContHomPoly ℝ n p) :
    Complexification E → Complexification F :=
  fun z ↦ (Classical.choose hp).complexify fun _ ↦ z

/-- `p_ℂ` is a continuous complex homogeneous polynomial of the same degree. -/
theorem IsContHomPoly.isContHomPoly_complexify (hp : IsContHomPoly ℝ n p) :
    IsContHomPoly ℂ n hp.complexify :=
  ⟨_, fun _ ↦ rfl⟩

/-- `p_ℂ` extends `p`. -/
theorem IsContHomPoly.complexify_ofReal (hp : IsContHomPoly ℝ n p) (v : E) :
    hp.complexify (ofReal v) = ofReal (p v) := by
  rw [IsContHomPoly.complexify, (Classical.choose hp).complexify_apply_ofReal (fun _ ↦ v),
    ← Classical.choose_spec hp v]

/-- `p_ℂ (μ v) = μⁿ p v` for `v ∈ E` and `μ ∈ ℂ`. -/
theorem IsContHomPoly.complexify_smul_ofReal (hp : IsContHomPoly ℝ n p) (μ : ℂ) (v : E) :
    hp.complexify (μ • ofReal v) = μ ^ n • ofReal (p v) := by
  rw [hp.isContHomPoly_complexify.map_smul, hp.complexify_ofReal]

end ComplexifyPoly

/-! ### Forward differences -/

section FwdDiff

variable {𝕜 : Type*} [Field 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] {n : ℕ} {p : E → F}

/-- **The `n`-th forward difference of a homogeneous polynomial of degree `n`**:
`∑_{j ≤ n} (-1)^{n-j} C(n, j) p (c + j v) = n! p v`, for every base point `c`. -/
theorem IsContHomPoly.sum_fwdDiff (hp : IsContHomPoly 𝕜 n p) (c v : E) :
    ∑ j ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - j) * n.choose j) • p (c + (j : 𝕜) • v) =
      (n.factorial : 𝕜) • p v := by
  classical
  obtain ⟨A, hA⟩ := hp
  set b : Finset (Fin n) → F := fun S ↦ A (S.piecewise (fun _ ↦ v) (fun _ ↦ c))
  have hexp : ∀ t : 𝕜, p (c + t • v) = ∑ S : Finset (Fin n), t ^ S.card • b S := by
    intro t
    rw [hA]
    have e1 : (fun _ : Fin n ↦ c + t • v) = (fun _ ↦ t • v) + (fun _ ↦ c) := by
      ext; simp [add_comm]
    rw [e1, A.map_add_univ]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    have e2 : S.piecewise (fun _ : Fin n ↦ t • v) (fun _ ↦ c) =
        S.piecewise (fun i ↦ (fun _ ↦ t) i • (S.piecewise (fun _ ↦ v) (fun _ ↦ c)) i)
          (S.piecewise (fun _ ↦ v) (fun _ ↦ c)) := by
      ext i; by_cases hi : i ∈ S <;> simp [hi]
    rw [e2, A.map_piecewise_smul, Finset.prod_const]
  set z : ℕ → ℤ := fun j ↦ (-1 : ℤ) ^ (n - j) * n.choose j
  have hcoef : ∀ k ≤ n, ∑ j ∈ Finset.range (n + 1), z j • (j : 𝕜) ^ k =
      if k = n then (n.factorial : 𝕜) else 0 := by
    intro k hk
    have h := fwdDiff_iter_eq_sum_shift (1 : 𝕜) (fun r : 𝕜 ↦ r ^ k) n 0
    simp only [zero_add, nsmul_eq_mul, mul_one] at h
    rw [← h]
    split_ifs with hkn
    · subst hkn
      rw [fwdDiff_iter_eq_factorial]
      simp
    · rw [fwdDiff_iter_pow_eq_zero_of_lt (lt_of_le_of_ne hk hkn)]
      simp
  calc ∑ j ∈ Finset.range (n + 1), z j • p (c + (j : 𝕜) • v)
      = ∑ S : Finset (Fin n), (∑ j ∈ Finset.range (n + 1), z j • (j : 𝕜) ^ S.card) • b S := by
        simp only [hexp, Finset.smul_sum, Finset.sum_smul, smul_assoc]
        exact Finset.sum_comm
    _ = (n.factorial : 𝕜) • b Finset.univ := by
        rw [Finset.sum_eq_single Finset.univ]
        · rw [hcoef _ (by simp)]; simp
        · intro S _ hS
          have hlt : S.card < n := by
            have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)
            simpa using this
          rw [hcoef _ hlt.le]; simp [hlt.ne]
        · simp
    _ = (n.factorial : 𝕜) • p v := by simp [b, hA]

end FwdDiff

/-- **Bounds from a shifted set**, real case (a substitute for [BS71a, Lemma 2], which
uses roots of unity): if `q (p (c + j v)) ≤ M` for `j = 0, …, n`, then `n! q (p v) ≤ 2ⁿ M`. -/
theorem IsContHomPoly.factorial_mul_seminorm_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {n : ℕ} {p : E → F} (hp : IsContHomPoly ℝ n p) (q : Seminorm ℝ F) {c v : E} {M : ℝ}
    (h : ∀ j ≤ n, q (p (c + (j : ℝ) • v)) ≤ M) : (n.factorial : ℝ) * q (p v) ≤ 2 ^ n * M := by
  have e : (n.factorial : ℝ) * q (p v) = q ((n.factorial : ℝ) • p v) := by
    rw [map_smul_eq_mul, Real.norm_natCast]
  rw [e, ← hp.sum_fwdDiff c v]
  calc q (∑ j ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - j) * n.choose j) • p (c + (j : ℝ) • v))
      ≤ ∑ j ∈ Finset.range (n + 1),
          q (((-1 : ℤ) ^ (n - j) * n.choose j) • p (c + (j : ℝ) • v)) :=
        Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * M := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        rw [← Int.cast_smul_eq_zsmul ℝ, map_smul_eq_mul]
        have hn : ‖(((-1 : ℤ) ^ (n - j) * n.choose j : ℤ) : ℝ)‖ = n.choose j := by
          push_cast
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
        rw [hn]
        exact mul_le_mul_of_nonneg_left (h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
          (Nat.cast_nonneg _)
    _ = 2 ^ n * M := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

/-! ### Uniform bounds on real planes -/

section Plane

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {p : ℕ → E → F}

/-- **Exponential bounds on a real plane.** If `(q (pₙ (s x + t y)))ₙ` is bounded at each point
of the square `|s|, |t| < 2`, then `q (pₙ (s x + t y)) ≤ M Kⁿ` uniformly on `|s|, |t| ≤ 1`.
Baire's theorem in the plane gives a uniform bound on a small disc, and the forward differences
(`IsContHomPoly.factorial_mul_seminorm_le`) carry it to a disc about the origin. `M` and `K`
depend on `q`. -/
theorem exists_plane_bound (hp : ∀ n, IsContHomPoly ℝ n (p n)) {q : Seminorm ℝ F}
    (hq : Continuous q) (x y : E)
    (hb : ∀ s t : ℝ, |s| < 2 → |t| < 2 → ∃ C, ∀ n, q (p n (s • x + t • y)) ≤ C) :
    ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ ∀ n, ∀ s t : ℝ, |s| ≤ 1 → |t| ≤ 1 →
      q (p n (s • x + t • y)) ≤ M * K ^ n := by
  set w : ℝ × ℝ → E := fun st ↦ st.1 • x + st.2 • y with hw
  have hwc : Continuous w :=
    (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hwlin : ∀ (a b : ℝ × ℝ) (r : ℝ), w (a + r • b) = w a + r • w b := by
    intro a b r
    simp only [w, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      add_smul, mul_smul, smul_add]
    abel
  set X := ball (0 : ℝ × ℝ) 2
  have hX : IsOpen X := isOpen_ball
  have : BaireSpace X := hX.baireSpace
  have : Nonempty X := ⟨⟨0, mem_ball_self (by norm_num)⟩⟩
  set A : ℕ → Set X := fun m ↦ {st | ∀ n, q (p n (w st)) ≤ m}
  have hA : ∀ m, IsClosed (A m) := by
    intro m
    have : A m = ⋂ n, (fun st : X ↦ q (p n (w st))) ⁻¹' Iic (m : ℝ) := by ext; simp [A]
    rw [this]
    exact isClosed_iInter fun n ↦ isClosed_Iic.preimage
      (hq.comp ((hp n).continuous.comp (hwc.comp continuous_subtype_val)))
  have hcov : ⋃ m, A m = univ := by
    refine eq_univ_of_forall fun st ↦ mem_iUnion.2 ?_
    have hst : ‖(st : ℝ × ℝ)‖ < 2 := mem_ball_zero_iff.1 st.2
    rw [Prod.norm_def, max_lt_iff] at hst
    obtain ⟨C, hC⟩ := hb _ _ (by simpa using hst.1) (by simpa using hst.2)
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨m, fun n ↦ (hC n).trans hm⟩
  obtain ⟨m, c0, hc0⟩ := nonempty_interior_of_iUnion_of_closed hA hcov
  have hO : IsOpen ((↑) '' interior (A m) : Set (ℝ × ℝ)) :=
    hX.isOpenMap_subtype_val _ isOpen_interior
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ (mem_image_of_mem _ hc0)
  set c : ℝ × ℝ := (c0 : ℝ × ℝ)
  have hbd : ∀ v ∈ ball c ρ, ∀ n, q (p n (w v)) ≤ m := by
    intro v hv n
    obtain ⟨v', hv', rfl⟩ := hball hv
    exact interior_subset hv' n
  refine ⟨Real.exp 1 * m, 4 * Real.exp 1 / ρ, by positivity, by positivity,
    fun n s t hs ht ↦ ?_⟩
  set r : ℝ := ρ / (2 * (n + 1)) with hr_def
  have hr : 0 < r := by positivity
  have hst : ‖((s, t) : ℝ × ℝ)‖ ≤ 1 := by
    rw [Prod.norm_def]
    exact max_le (by simpa using hs) (by simpa using ht)
  have hj : ∀ j ≤ n, q (p n (w c + (j : ℝ) • w (r • (s, t)))) ≤ m := by
    intro j hjn
    rw [← hwlin]
    refine hbd _ ?_ n
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_natCast,
      Real.norm_of_nonneg hr.le]
    have hjn' : (j : ℝ) ≤ n := by exact_mod_cast hjn
    calc (j : ℝ) * (r * ‖((s, t) : ℝ × ℝ)‖) ≤ n * (r * 1) := by gcongr
      _ = ρ * (n / (2 * (n + 1))) := by rw [hr_def]; ring
      _ < ρ * 1 := by
          gcongr
          rw [div_lt_one (by positivity)]
          linarith
      _ = ρ := mul_one ρ
  have key := (hp n).factorial_mul_seminorm_le q hj
  have hwv : w (r • (s, t)) = r • w (s, t) := by
    simp only [w, Prod.smul_mk, smul_eq_mul, mul_smul, smul_add]
  rw [hwv, (hp n).map_smul, map_smul_eq_mul, norm_pow, Real.norm_of_nonneg hr.le] at key
  set Q := q (p n (s • x + t • y))
  have hfact : ((n : ℝ) + 1) ^ n / n.factorial ≤ Real.exp 1 ^ (n + 1) := by
    have h := Real.pow_div_factorial_le_exp (x := (n : ℝ) + 1) (by positivity) (n + 1)
    rw [Real.exp_one_pow]
    push_cast at h ⊢
    calc ((n : ℝ) + 1) ^ n / n.factorial
        = ((n : ℝ) + 1) ^ (n + 1) / (n + 1).factorial := by
          rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
          push_cast
          field_simp
      _ ≤ Real.exp ((n : ℝ) + 1) := h
  have hpos : (0 : ℝ) < n.factorial * r ^ n := by positivity
  have hQ : Q ≤ 2 ^ n * m / (n.factorial * r ^ n) := by
    rw [le_div_iff₀ hpos]
    linarith [key]
  calc Q ≤ 2 ^ n * m / (n.factorial * r ^ n) := hQ
    _ = m * (4 / ρ) ^ n * (((n : ℝ) + 1) ^ n / n.factorial) := by
        have hρ0 : ρ ≠ 0 := hρ.ne'
        have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
        rw [hr_def, div_pow, mul_pow, div_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        field_simp
    _ ≤ m * (4 / ρ) ^ n * Real.exp 1 ^ (n + 1) := by gcongr
    _ = Real.exp 1 * m * (4 * Real.exp 1 / ρ) ^ n := by ring

end Plane

/-! ### Jensen's inequality along an auxiliary complex line -/

section Functional

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- **Hahn–Banach**, real case: a continuous seminorm is attained by a continuous functional
which it dominates. -/
theorem exists_clm_eq_seminorm_real [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F] {q : Seminorm ℝ F} (hq : Continuous q) (v : F) :
    ∃ φ : F →L[ℝ] ℝ, φ v = q v ∧ ∀ w, |φ w| ≤ q w := by
  let f : F →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' v (q v) (by
    intro c hc
    rcases smul_eq_zero.1 hc with rfl | rfl
    · simp
    · simp)
  obtain ⟨g, hg, hgq⟩ :=
    Module.Dual.exists_continuous_extension_of_le_seminorm_real f.domain f.toFun hq (by
      rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      have : f ⟨c • v, hx⟩ = c • q v := LinearPMap.mkSpanSingleton'_apply _ _ _ _ _
      change f ⟨c • v, hx⟩ ≤ q (c • v)
      rw [this, map_smul_eq_mul, smul_eq_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (le_abs_self c) (apply_nonneg q v))
  refine ⟨g, ?_, hgq⟩
  rw [hg ⟨v, Submodule.mem_span_singleton_self v⟩]
  exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/-- The complexification `φ_ℂ (u + i v) = φ u + i φ v` of a continuous real functional, a
continuous complex functional on `F_ℂ`. -/
def complexifyFunctional (φ : F →L[ℝ] ℝ) : Complexification F →L[ℂ] ℂ where
  toFun z := (φ (re z) : ℂ) + (φ (im z) : ℂ) * Complex.I
  map_add' z w := by simp only [re_add, im_add, map_add, Complex.ofReal_add]; ring
  map_smul' c z := by
    apply Complex.ext <;>
      simp only [re_smul, im_smul, map_sub, map_add, map_smul, smul_eq_mul, RingHom.id_apply,
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  cont := by
    refine (Complex.continuous_ofReal.comp (φ.continuous.comp continuous_re)).add
      ((Complex.continuous_ofReal.comp (φ.continuous.comp continuous_im)).mul continuous_const)

@[simp] theorem complexifyFunctional_re (φ : F →L[ℝ] ℝ) (z : Complexification F) :
    (complexifyFunctional φ z).re = φ (re z) := by
  simp [complexifyFunctional]

@[simp] theorem complexifyFunctional_im (φ : F →L[ℝ] ℝ) (z : Complexification F) :
    (complexifyFunctional φ z).im = φ (im z) := by
  simp [complexifyFunctional]

theorem complexifyFunctional_smul_ofReal (φ : F →L[ℝ] ℝ) (c : ℂ) (v : F) :
    complexifyFunctional φ (c • ofReal v) = c * φ v := by
  rw [map_smul, smul_eq_mul]
  congr 1
  simp [complexifyFunctional]

end Functional

theorem cos_eq_two_mul_cos_half_sq (θ : ℝ) : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
  rw [← Real.cos_two_mul]; ring_nf

theorem sin_eq_two_mul_sin_half (θ : ℝ) :
    Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
  rw [← Real.sin_two_mul]; ring_nf

/-- The scalars of the auxiliary line on the circle `|λ| = 2`:
`1 + e^{iθ} = 2 e^{iθ/2} cos (θ/2)`. -/
theorem one_add_exp_eq (θ : ℝ) :
    1 + Complex.exp (θ * Complex.I) =
      2 * Complex.exp ((θ / 2 : ℝ) * Complex.I) * (Real.cos (θ / 2) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.exp_ofReal_mul_I_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    rw [cos_eq_two_mul_cos_half_sq θ]; ring
  · simp only [Complex.add_im, Complex.one_im, Complex.exp_ofReal_mul_I_im, Complex.mul_im,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [sin_eq_two_mul_sin_half θ]; ring

/-- `i (1 - e^{iθ}) = 2 e^{iθ/2} sin (θ/2)`. -/
theorem I_mul_one_sub_exp_eq (θ : ℝ) :
    Complex.I * (1 - Complex.exp (θ * Complex.I)) =
      2 * Complex.exp ((θ / 2 : ℝ) * Complex.I) * (Real.sin (θ / 2) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
    rw [sin_eq_two_mul_sin_half θ]; ring
  · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
    rw [cos_eq_two_mul_cos_half_sq θ]
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2)]

section Jensen

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The direction `(x - i y)/2` of the auxiliary line `λ ↦ (x + i y) + λ (x - i y)/2`. -/
def auxDir (x y : E) : Complexification E :=
  (1 / 2 : ℂ) • (ofReal x - Complex.I • ofReal y)

/-- **The auxiliary line meets the real directions on a circle**: for `|λ| = 2`, the point
`(x + i y) + λ (x - i y)/2` is the complex multiple `2 e^{iθ/2}` of the real vector
`cos (θ/2) x + sin (θ/2) y`, where `λ = 2 e^{iθ}`. -/
theorem mk_add_circleMap_smul_auxDir (x y : E) (θ : ℝ) :
    mk x y + circleMap 0 2 θ • auxDir x y =
      (2 * Complex.exp ((θ / 2 : ℝ) * Complex.I)) •
        ofReal (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y) := by
  have h1 := one_add_exp_eq θ
  have h2 := I_mul_one_sub_exp_eq θ
  rw [map_add, map_smul, map_smul, ← Complexification.ofReal_smul,
    ← Complexification.ofReal_smul, mk_eq_add_I_smul, circleMap, auxDir]
  change ofReal x + Complex.I • ofReal y + _ = _
  simp only [zero_add, Complex.ofReal_ofNat]
  linear_combination (norm := module) h1 • ofReal x + h2 • ofReal y

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] {n : ℕ} {P : E → F}

/-- **Jensen's inequality on the auxiliary line.** For a real functional `φ` and `κ > 0`,
`log⁺ (|φ_ℂ (P_ℂ (x + i y))| / κⁿ)` is at most the average over `θ ∈ [0, 2π]` of
`log⁺ ((2/κ)ⁿ |φ (P (cos (θ/2) x + sin (θ/2) y))|)`: only values of `P` at real points enter
the right hand side. -/
theorem posLog_le_integral_circle (hp : IsContHomPoly ℝ n P) (φ : F →L[ℝ] ℝ) (x y : E) {κ : ℝ}
    (hκ : 0 < κ) :
    Real.posLog (‖complexifyFunctional φ (hp.complexify (mk x y))‖ / κ ^ n) ≤
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.posLog ((2 / κ) ^ n * |φ (P (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y))|) := by
  have : PolynormableSpace ℂ ℂ := polynormableSpace_complex
  set φC := complexifyFunctional φ
  set c : ℂ := (((κ ^ n)⁻¹ : ℝ) : ℂ)
  set g : ℂ → ℂ := fun l ↦ c * φC (hp.complexify (mk x y + l • auxDir x y))
  have hline := hp.isContHomPoly_complexify.line (mk x y) (auxDir x y)
  have hg : Continuous g := continuous_const.mul (φC.continuous.comp hline.1)
  have hgℓ : ∀ ℓ : ℂ →L[ℂ] ℂ, AnalyticOnNhd ℂ (ℓ ∘ g) (closedBall 0 2) := fun ℓ ↦ by
    have h := hline.2 (ℓ.comp (c • φC))
    have e : ℓ ∘ g = ⇑(ℓ.comp (c • φC)) ∘ fun z : ℂ ↦ hp.complexify (mk x y + z • auxDir x y) := by
      funext z
      simp only [Function.comp, g, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
    rw [e]
    exact h.mono (subset_univ _)
  have hJ := posLog_le_circleAverage (c := 0) (R := 2) hg hgℓ two_pos
    (q := normSeminorm ℂ ℂ) continuous_norm
  have h0 : normSeminorm ℂ ℂ (g 0) = ‖φC (hp.complexify (mk x y))‖ / κ ^ n := by
    simp [g, c, div_eq_inv_mul, abs_of_pos hκ]
  have hcirc : ∀ θ : ℝ, normSeminorm ℂ ℂ (g (circleMap 0 2 θ)) =
      (2 / κ) ^ n * |φ (P (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y))| := by
    intro θ
    simp only [g, coe_normSeminorm]
    rw [mk_add_circleMap_smul_auxDir, hp.complexify_smul_ofReal, complexifyFunctional_smul_ofReal]
    simp only [c, norm_mul, norm_pow, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_ofNat, mul_one]
    rw [abs_inv, abs_of_pos (pow_pos hκ n), div_pow]
    field_simp
  rw [h0, Real.circleAverage_def] at hJ
  simp only [hcirc, smul_eq_mul] at hJ
  exact hJ

/-- **Seminorm form of `posLog_le_integral_circle`**: if `v ∈ F` satisfies
`|φ v| ≤ |φ_ℂ (P_ℂ (x + i y))|` for all real functionals (e.g. `v` the real or the imaginary
part of `P_ℂ (x + i y)`), then `log⁺ (q v / κⁿ)` is at most the average of
`log⁺ ((2/κ)ⁿ q (P (cos (θ/2) x + sin (θ/2) y)))`. -/
theorem posLog_seminorm_le_integral_circle [LocallyConvexSpace ℝ F] (hp : IsContHomPoly ℝ n P)
    {q : Seminorm ℝ F} (hq : Continuous q) (x y : E) {κ : ℝ} (hκ : 0 < κ) {v : F}
    (hv : ∀ φ : F →L[ℝ] ℝ, |φ v| ≤ ‖complexifyFunctional φ (hp.complexify (mk x y))‖) :
    Real.posLog (q v / κ ^ n) ≤
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.posLog ((2 / κ) ^ n * q (P (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y))) := by
  obtain ⟨φ, hφv, hφq⟩ := exists_clm_eq_seminorm_real hq v
  have hκn : 0 < κ ^ n := pow_pos hκ n
  have hw : Continuous fun θ : ℝ ↦ Real.cos (θ / 2) • x + Real.sin (θ / 2) • y :=
    ((Real.continuous_cos.comp (continuous_id.div_const 2)).smul continuous_const).add
      ((Real.continuous_sin.comp (continuous_id.div_const 2)).smul continuous_const)
  calc Real.posLog (q v / κ ^ n)
      ≤ Real.posLog (‖complexifyFunctional φ (hp.complexify (mk x y))‖ / κ ^ n) := by
        refine Real.posLog_le_posLog (by linarith [div_nonneg (apply_nonneg q v) hκn.le]) ?_
        gcongr
        rw [← hφv]
        exact (le_abs_self _).trans (hv φ)
    _ ≤ _ := posLog_le_integral_circle hp φ x y hκ
    _ ≤ _ := by
        gcongr
        refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ fun θ _ ↦ ?_
        · exact (Real.continuous_posLog.comp (continuous_const.mul
            (continuous_abs.comp (φ.continuous.comp (hp.continuous.comp hw))))).intervalIntegrable
              _ _
        · exact (Real.continuous_posLog.comp (continuous_const.mul
            (hq.comp (hp.continuous.comp hw)))).intervalIntegrable _ _
        · have h0 : 0 ≤ (2 / κ) ^ n * |φ (P (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y))| := by
            positivity
          exact Real.posLog_le_posLog (by linarith) (by gcongr; exact hφq _)

end Jensen

/-! ### [BS71b, Proposition 5.4] -/

/-- An eventual bound `aₙ ≤ θⁿ` gives a bound `aₙ ≤ C θⁿ` for all `n`. -/
theorem exists_const_mul_pow_of_eventually {a : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (h : ∀ᶠ n in atTop, a n ≤ θ ^ n) : ∃ C, ∀ n, a n ≤ C * θ ^ n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  refine ⟨1 + ∑ k ∈ Finset.range N, |a k| / θ ^ k, fun n ↦ ?_⟩
  have hpos : 0 < θ ^ n := pow_pos hθ n
  have hS : 0 ≤ ∑ k ∈ Finset.range N, |a k| / θ ^ k :=
    Finset.sum_nonneg fun k _ ↦ by positivity
  by_cases hn : N ≤ n
  · nlinarith [hN n hn]
  · have hk : |a n| / θ ^ n ≤ ∑ k ∈ Finset.range N, |a k| / θ ^ k :=
      Finset.single_le_sum (f := fun k ↦ |a k| / θ ^ k) (fun k _ ↦ by positivity)
        (Finset.mem_range.2 (not_le.1 hn))
    have ha : a n ≤ |a n| / θ ^ n * θ ^ n := by
      rw [div_mul_cancel₀ _ hpos.ne']; exact le_abs_self _
    nlinarith

section Prop54

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] {p : ℕ → E → F}

/-- **Geometric bounds at a complex point from bounds at real points.** Let `z = x + i y`. If
`(q (pₙ (s x + t y)))ₙ` is bounded at each point of the square `|s|, |t| < 2`, and
`((5/2)ⁿ q (pₙ (cos (θ/2) x + sin (θ/2) y)))ₙ` is bounded for each `θ`, then any `vₙ ∈ F`
dominated through every real functional by `(pₙ)_ℂ (z)` (its real or imaginary part) satisfies
`q (vₙ) ≤ C (9/10)ⁿ`.

Jensen's inequality on the auxiliary line (`posLog_seminorm_le_integral_circle`) bounds
`n⁻¹ log⁺ (q (vₙ)/(4/5)ⁿ)` by the average over the circle of
`n⁻¹ log⁺ ((5/2)ⁿ q (pₙ (cos (θ/2) x + sin (θ/2) y)))`; these functions tend to `0` pointwise and
are uniformly bounded by `exists_plane_bound`, so their averages tend to `0` (dominated
convergence). -/
theorem exists_geometric_of_circle (hp : ∀ n, IsContHomPoly ℝ n (p n)) {q : Seminorm ℝ F}
    (hq : Continuous q) (x y : E)
    (hsq : ∀ s t : ℝ, |s| < 2 → |t| < 2 → ∃ C, ∀ n, q (p n (s • x + t • y)) ≤ C)
    (hcirc : ∀ θ : ℝ, ∃ C, ∀ n,
      (5 / 2 : ℝ) ^ n * q (p n (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y)) ≤ C)
    {v : ℕ → F}
    (hv : ∀ n, ∀ φ : F →L[ℝ] ℝ,
      |φ (v n)| ≤ ‖complexifyFunctional φ ((hp n).complexify (mk x y))‖) :
    ∃ C, ∀ n, q (v n) ≤ C * (9 / 10 : ℝ) ^ n := by
  obtain ⟨M, K, hM, hK, hMK⟩ := exists_plane_bound hp hq x y hsq
  set w : ℝ → E := fun θ ↦ Real.cos (θ / 2) • x + Real.sin (θ / 2) • y
  have hw : Continuous w :=
    ((Real.continuous_cos.comp (continuous_id.div_const 2)).smul continuous_const).add
      ((Real.continuous_sin.comp (continuous_id.div_const 2)).smul continuous_const)
  set G : ℕ → ℝ → ℝ := fun n θ ↦ Real.posLog ((5 / 2 : ℝ) ^ n * q (p n (w θ)))
  have hGc : ∀ n, Continuous (G n) := fun n ↦
    Real.continuous_posLog.comp (continuous_const.mul (hq.comp ((hp n).continuous.comp hw)))
  set f : ℕ → ℝ → ℝ := fun n θ ↦ (n : ℝ)⁻¹ * G n θ
  set B : ℝ := Real.posLog M + Real.posLog (5 / 2 * K)
  -- uniform bound
  have hfB : ∀ n ≥ 1, ∀ θ, ‖f n θ‖ ≤ B := by
    intro n hn θ
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hG0 : 0 ≤ G n θ := Real.posLog_nonneg
    have hle : (5 / 2 : ℝ) ^ n * q (p n (w θ)) ≤ M * (5 / 2 * K) ^ n := by
      have := hMK n (Real.cos (θ / 2)) (Real.sin (θ / 2)) (Real.abs_cos_le_one _)
        (Real.abs_sin_le_one _)
      calc (5 / 2 : ℝ) ^ n * q (p n (w θ)) ≤ (5 / 2 : ℝ) ^ n * (M * K ^ n) := by gcongr
        _ = M * (5 / 2 * K) ^ n := by rw [mul_pow]; ring
    have hGB : G n θ ≤ Real.posLog M + n * Real.posLog (5 / 2 * K) := by
      calc G n θ ≤ Real.posLog (M * (5 / 2 * K) ^ n) :=
            Real.posLog_le_posLog (by
              have : 0 ≤ (5 / 2 : ℝ) ^ n * q (p n (w θ)) := by positivity
              linarith) hle
        _ ≤ Real.posLog M + Real.posLog ((5 / 2 * K) ^ n) := Real.posLog_mul
        _ = Real.posLog M + n * Real.posLog (5 / 2 * K) := by rw [Real.posLog_pow]
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hG0)]
    have h1 : (n : ℝ)⁻¹ * Real.posLog M ≤ Real.posLog M :=
      mul_le_of_le_one_left Real.posLog_nonneg (inv_le_one_of_one_le₀ hn')
    calc (n : ℝ)⁻¹ * G n θ ≤ (n : ℝ)⁻¹ * (Real.posLog M + n * Real.posLog (5 / 2 * K)) := by
          gcongr
      _ = (n : ℝ)⁻¹ * Real.posLog M + Real.posLog (5 / 2 * K) := by
          field_simp
      _ ≤ B := by simp only [B]; linarith
  -- pointwise limit
  have hflim : ∀ θ, Tendsto (fun n ↦ f n θ) atTop (𝓝 0) := by
    intro θ
    obtain ⟨C, hC⟩ := hcirc θ
    have hup : ∀ n, f n θ ≤ (n : ℝ)⁻¹ * Real.posLog C := fun n ↦ by
      refine mul_le_mul_of_nonneg_left (Real.posLog_le_posLog ?_ (hC n)) (by positivity)
      have : 0 ≤ (5 / 2 : ℝ) ^ n * q (p n (w θ)) := by positivity
      linarith
    have hlow : ∀ n, 0 ≤ f n θ := fun n ↦ mul_nonneg (by positivity) Real.posLog_nonneg
    have h0 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * Real.posLog C) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop |>.mul_const
        (Real.posLog C)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 hlow hup
  -- dominated convergence
  have hint : Tendsto (fun n ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, f n θ) atTop (𝓝 0) := by
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (a := 0) (b := 2 * Real.pi) (l := atTop) (F := f)
      (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ B)
      (Eventually.of_forall fun n ↦
        ((continuous_const.mul (hGc n)).aestronglyMeasurable))
      ((eventually_ge_atTop 1).mono fun n hn ↦ MeasureTheory.ae_of_all _ fun θ _ ↦ hfB n hn θ)
      intervalIntegrable_const
      (MeasureTheory.ae_of_all _ fun θ _ ↦ hflim θ)
    simpa using this
  set ε : ℝ := Real.log (9 / 8)
  have hε : 0 < ε := Real.log_pos (by norm_num)
  have hev : ∀ᶠ n in atTop, ∫ θ in (0 : ℝ)..2 * Real.pi, f n θ < 2 * Real.pi * ε :=
    hint.eventually (gt_mem_nhds (by positivity))
  refine exists_const_mul_pow_of_eventually (by norm_num) ?_
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  have hκ : (0 : ℝ) < 4 / 5 := by norm_num
  have hJ := posLog_seminorm_le_integral_circle (hp n) hq x y hκ (hv n)
  have e25 : (2 / (4 / 5) : ℝ) = 5 / 2 := by norm_num
  rw [e25] at hJ
  have hGf : ∫ θ in (0 : ℝ)..2 * Real.pi, G n θ = n * ∫ θ in (0 : ℝ)..2 * Real.pi, f n θ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext θ
    simp only [f]
    field_simp
  change Real.posLog (q (v n) / (4 / 5) ^ n) ≤
    (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, G n θ at hJ
  rw [hGf] at hJ
  have hlog : Real.posLog (q (v n) / (4 / 5) ^ n) ≤ n * ε := by
    calc _ ≤ (2 * Real.pi)⁻¹ * (n * ∫ θ in (0 : ℝ)..2 * Real.pi, f n θ) := hJ
      _ ≤ (2 * Real.pi)⁻¹ * (n * (2 * Real.pi * ε)) := by gcongr
      _ = n * ε := by field_simp
  have hpow : Real.exp (n * ε) = (9 / 8 : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hq0 : 0 ≤ q (v n) / (4 / 5) ^ n := by positivity
  have hle : q (v n) / (4 / 5) ^ n ≤ (9 / 8 : ℝ) ^ n := by
    rw [← hpow]
    by_cases h1 : q (v n) / (4 / 5) ^ n ≤ 1
    · exact h1.trans (Real.one_le_exp (by positivity))
    · rw [not_le] at h1
      rw [Real.posLog_eq_log (by rw [abs_of_nonneg hq0]; exact h1.le)] at hlog
      exact (Real.log_le_iff_le_exp (by linarith)).1 hlog
  calc q (v n) = q (v n) / (4 / 5) ^ n * (4 / 5) ^ n := by
        rw [div_mul_cancel₀ _ (by positivity)]
    _ ≤ (9 / 8 : ℝ) ^ n * (4 / 5) ^ n := by gcongr
    _ = (9 / 10 : ℝ) ^ n := by rw [← mul_pow]; norm_num

variable [LocallyConvexSpace ℝ E]

/-- **[BS71b, Proposition 5.4]** (geometric form). Let `∑ pₙ` be a series of
continuous real homogeneous polynomials such that `(q (pₙ y))ₙ` is bounded for every continuous
seminorm `q` and every `y` in a neighbourhood `Y` of `0`. Then on a neighbourhood of `0` in
`E_ℂ` the complexified terms satisfy `q (Re (pₙ)_ℂ z), q (Im (pₙ)_ℂ z) ≤ C (9/10)ⁿ`, with the
ratio `9/10` independent of `z` and `q`. No Baire or completeness assumption is made.

Bochnak and Siciak use Siciak's polynomial lemma (potential theory on a real segment). Here
the complexified polynomial is restricted to the complex line through `x + i y` with direction
`(x - i y)/2`, which meets the complex multiples of real vectors on a circle about `x + i y`
(`mk_add_circleMap_smul_auxDir`); Jensen's inequality on that circle and Baire's theorem in the
real plane `span {x, y}` replace the polynomial lemma. -/
theorem exists_nhds_complexify_geometric (hp : ∀ n, IsContHomPoly ℝ n (p n)) {Y : Set E}
    (hY : Y ∈ 𝓝 (0 : E))
    (hb : ∀ y ∈ Y, ∀ q : Seminorm ℝ F, Continuous q → ∃ C, ∀ n, q (p n y) ≤ C) :
    ∃ Z ∈ 𝓝 (0 : Complexification E), ∀ z ∈ Z, ∀ q : Seminorm ℝ F, Continuous q →
      ∃ C, ∀ n, q (re ((hp n).complexify z)) ≤ C * (9 / 10 : ℝ) ^ n ∧
        q (im ((hp n).complexify z)) ≤ C * (9 / 10 : ℝ) ^ n := by
  obtain ⟨s, r, hr, hball⟩ := ((PolynormableSpace.withSeminorms ℝ E).mem_nhds_iff 0 Y).1 hY
  set N : Seminorm ℝ E := s.sup fun q ↦ q.1
  have hN : ∀ v, N v < r → v ∈ Y := fun v hv ↦ hball (by rwa [Seminorm.mem_ball_zero])
  have hNb : N.ball 0 (r / 5) ∈ 𝓝 (0 : E) :=
    ((PolynormableSpace.withSeminorms ℝ E).mem_nhds_iff 0 _).2 ⟨s, r / 5, by positivity, le_rfl⟩
  refine ⟨re ⁻¹' N.ball 0 (r / 5) ∩ im ⁻¹' N.ball 0 (r / 5),
    inter_mem (continuous_re.continuousAt.preimage_mem_nhds (by simpa using hNb))
      (continuous_im.continuousAt.preimage_mem_nhds (by simpa using hNb)), ?_⟩
  rintro z ⟨hx, hy⟩ q hq
  rw [mem_preimage, Seminorm.mem_ball_zero] at hx hy
  set x := re z
  set y := im z
  have hx0 : 0 ≤ N x := apply_nonneg N x
  have hy0 : 0 ≤ N y := apply_nonneg N y
  have hcomb : ∀ a b : ℝ, N (a • x + b • y) ≤ |a| * N x + |b| * N y := fun a b ↦ by
    calc N (a • x + b • y) ≤ N (a • x) + N (b • y) := map_add_le_add _ _ _
      _ = |a| * N x + |b| * N y := by
          rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have hsq : ∀ s t : ℝ, |s| < 2 → |t| < 2 → ∃ C, ∀ n, q (p n (s • x + t • y)) ≤ C := by
    intro s t hs ht
    refine hb _ (hN _ ?_) q hq
    calc N (s • x + t • y) ≤ |s| * N x + |t| * N y := hcomb s t
      _ ≤ 2 * N x + 2 * N y := by gcongr
      _ < r := by linarith
  have hcirc : ∀ θ : ℝ, ∃ C, ∀ n,
      (5 / 2 : ℝ) ^ n * q (p n (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y)) ≤ C := by
    intro θ
    have hmem : (5 / 2 : ℝ) • (Real.cos (θ / 2) • x + Real.sin (θ / 2) • y) ∈ Y := by
      refine hN _ ?_
      rw [map_smul_eq_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2)]
      have h1 := hcomb (Real.cos (θ / 2)) (Real.sin (θ / 2))
      have h2 : |Real.cos (θ / 2)| * N x + |Real.sin (θ / 2)| * N y ≤ N x + N y := by
        gcongr
        · exact (mul_le_of_le_one_left hx0 (Real.abs_cos_le_one _))
        · exact (mul_le_of_le_one_left hy0 (Real.abs_sin_le_one _))
      nlinarith
    obtain ⟨C, hC⟩ := hb _ hmem q hq
    refine ⟨C, fun n ↦ ?_⟩
    have h := hC n
    rwa [(hp n).map_smul, map_smul_eq_mul, norm_pow,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 2)] at h
  have hre := exists_geometric_of_circle hp hq x y hsq hcirc
    (v := fun n ↦ re ((hp n).complexify z)) fun n φ ↦ by
      rw [← complexifyFunctional_re]
      exact Complex.abs_re_le_norm _
  have him := exists_geometric_of_circle hp hq x y hsq hcirc
    (v := fun n ↦ im ((hp n).complexify z)) fun n φ ↦ by
      rw [← complexifyFunctional_im]
      exact Complex.abs_im_le_norm _
  obtain ⟨C₁, hC₁⟩ := hre
  obtain ⟨C₂, hC₂⟩ := him
  refine ⟨max C₁ C₂, fun n ↦ ⟨(hC₁ n).trans ?_, (hC₂ n).trans ?_⟩⟩ <;>
    exact mul_le_mul_of_nonneg_right (by simp) (by positivity)

end Prop54

/-! ### Mackey completeness of the complexification -/

section MackeyComplexification

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- The complexification of a Mackey complete space is Mackey complete. -/
instance Complexification.mackeyComplete [MackeyComplete F] :
    MackeyComplete (Complexification F) where
  exists_tendsto u B r hB hr hu := by
    have hre : ∀ k l, k ≤ l → re (u l) - re (u k) ∈ r k • (re '' B) := fun k l hkl ↦ by
      obtain ⟨b, hbB, hb⟩ := hu k l hkl
      exact ⟨re b, ⟨b, hbB, rfl⟩, by simp only at hb ⊢; rw [← re_real_smul, hb, re_sub]⟩
    have him : ∀ k l, k ≤ l → im (u l) - im (u k) ∈ r k • (im '' B) := fun k l hkl ↦ by
      obtain ⟨b, hbB, hb⟩ := hu k l hkl
      exact ⟨im b, ⟨b, hbB, rfl⟩, by simp only at hb ⊢; rw [← im_real_smul, hb, im_sub]⟩
    obtain ⟨a, ha⟩ := MackeyComplete.exists_tendsto (fun k ↦ re (u k)) _ r
      (hB.image (reCLM : Complexification F →L[ℝ] F)) hr hre
    obtain ⟨b, hb⟩ := MackeyComplete.exists_tendsto (fun k ↦ im (u k)) _ r
      (hB.image (imCLM : Complexification F →L[ℝ] F)) hr him
    exact ⟨mk a b, ha.prodMk_nhds hb⟩

/-- Baire products give Baire complexifications (e.g. for Fréchet spaces). -/
instance Complexification.baireSpace [BaireSpace (F × F)] : BaireSpace (Complexification F) :=
  inferInstanceAs (BaireSpace (F × F))

end MackeyComplexification

/-! ### Translations of complex analytic maps -/

/-- Complex analyticity is invariant under translations: if `g` is complex analytic on `H`, then
`z ↦ g (z - c)` is complex analytic on `c + H`. -/
theorem ComplexAnalyticOn.comp_sub_const {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] {F : Type v} [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] {g : E → F} {H : Set E} (hg : ComplexAnalyticOn g H) (c : E) :
    ComplexAnalyticOn (fun z ↦ g (z - c)) {z | z - c ∈ H} := by
  refine ⟨hg.1.comp (continuous_id.sub continuous_const).continuousOn fun z hz ↦ hz,
    fun x hx ↦ ?_⟩
  obtain ⟨p, hp, Y, hY, hYH, hsum⟩ := hg.2 (x - c) hx
  refine ⟨p, hp, Y, hY, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · change x + y - c ∈ H
    rw [add_sub_right_comm]
    exact hYH y hy
  · simp only
    rw [add_sub_right_comm]
    exact hsum y hy

/-! ### [BS71b, Theorem 7.1] -/

section Theorem71

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] {p : ℕ → E → F}

/-- **[BS71b, Proposition 5.4]**: under the hypotheses of
`exists_nhds_complexify_geometric` and with `F` Mackey complete, the complexified series
`∑ (pₙ)_ℂ` converges on a neighbourhood of `0` in `E_ℂ`. -/
theorem exists_nhds_hasSum_complexify [MackeyComplete F] (hp : ∀ n, IsContHomPoly ℝ n (p n))
    {Y : Set E} (hY : Y ∈ 𝓝 (0 : E))
    (hb : ∀ y ∈ Y, ∀ q : Seminorm ℝ F, Continuous q → ∃ C, ∀ n, q (p n y) ≤ C) :
    ∃ Z ∈ 𝓝 (0 : Complexification E), ∀ z ∈ Z,
      ∃ S, HasSum (fun n ↦ (hp n).complexify z) S := by
  have : PolynormableSpace ℂ (Complexification F) := polynormableSpace_complex
  obtain ⟨Z, hZ, hgeom⟩ := exists_nhds_complexify_geometric hp hY hb
  refine ⟨Z, hZ, fun z hz ↦ ?_⟩
  refine MackeyComplete.exists_hasSum_of_geometric (θ := 9 / 10) (by norm_num) (by norm_num)
    fun Q hQ ↦ ?_
  set q : Seminorm ℝ F :=
    (Q.restrictScalars ℝ).comp (ofReal : F →L[ℝ] Complexification F).toLinearMap
  have hq : Continuous q := hQ.comp ofReal.continuous
  obtain ⟨C, hC⟩ := hgeom z hz q hq
  refine ⟨2 * C, fun n ↦ ?_⟩
  set w := (hp n).complexify z
  have hw : w = ofReal (re w) + Complex.I • ofReal (im w) := mk_eq_add_I_smul _ _
  calc Q w ≤ Q (ofReal (re w)) + Q (Complex.I • ofReal (im w)) := by
        conv_lhs => rw [hw]
        exact map_add_le_add _ _ _
    _ = q (re w) + q (im w) := by
        rw [map_smul_eq_mul, Complex.norm_I, one_mul]; rfl
    _ ≤ C * (9 / 10) ^ n + C * (9 / 10) ^ n := add_le_add (hC n).1 (hC n).2
    _ = 2 * C * (9 / 10) ^ n := by ring

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] in
/-- The terms of a convergent series are bounded for every continuous seminorm. -/
theorem exists_bound_of_tendsto_sum_real {u : ℕ → F} {L : F}
    (h : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, u n) atTop (𝓝 L)) {q : Seminorm ℝ F}
    (hq : Continuous q) : ∃ C, ∀ n, q (u n) ≤ C := by
  have ht : Tendsto u atTop (𝓝 0) := by
    have h1 := (h.comp (tendsto_add_atTop_nat 1)).sub h
    rw [sub_self] at h1
    refine h1.congr fun n ↦ ?_
    simp [Finset.sum_range_succ]
  obtain ⟨C, hC⟩ := ((hq.tendsto 0).comp ht).bddAbove_range
  exact ⟨C, fun n ↦ hC ⟨n, rfl⟩⟩

variable [T2Space E] [T2Space F]

/-- **[BS71b, Theorem 7.1]** (with a Mackey complete target). Let `E` be a real
locally convex space whose complexification `E_ℂ = E × E` is a Baire space (e.g. `E` a Fréchet
space, `Complexification.baireSpace`), and `F` a Mackey complete real locally convex space. Then
every map `f : U → F` which is analytic in the sense of Bochnak and Siciak (continuous and
locally the sum of a series of continuous homogeneous polynomials) is real analytic in the sense
of Milnor: it extends to a complex analytic map on an open subset of `E_ℂ`
([GN26, Remark 2.2.7]). With `RealAnalyticOn.bsAnalyticOn`, the two notions coincide.

Around `a ∈ U`, the complexified Taylor series converges on a neighbourhood of `0` in `E_ℂ`
(`exists_nhds_hasSum_complexify`), its sum is complex analytic there by the complex case of
Theorem 5.2 (`complexAnalyticOn_of_tendsto_sum`, which uses the Baire property of `E_ℂ`), and
the local extensions are glued by `RealAnalyticOn.of_local`. Bochnak and Siciak assume `F`
sequentially complete. -/
theorem realAnalyticOn_of_bsAnalyticOn [BaireSpace (Complexification E)] [MackeyComplete F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : BSAnalyticOn f U) : RealAnalyticOn f U := by
  refine RealAnalyticOn.of_local hU fun a ha ↦ ?_
  obtain ⟨p, hp, Y, hY, hYU, hsum⟩ := hf.2 a ha
  have hb : ∀ y ∈ Y, ∀ q : Seminorm ℝ F, Continuous q → ∃ C, ∀ n, q (p n y) ≤ C :=
    fun y hy q hq ↦ exists_bound_of_tendsto_sum_real (hsum y hy) hq
  obtain ⟨Z, hZ, hS⟩ := exists_nhds_hasSum_complexify hp hY hb
  set H := interior Z
  set g₀ : Complexification E → Complexification F := fun z ↦ ∑' n, (hp n).complexify z
  have hg₀ : ComplexAnalyticOn g₀ H := by
    refine complexAnalyticOn_of_tendsto_sum (fun n ↦ (hp n).isContHomPoly_complexify)
      isOpen_interior fun z hz ↦ ?_
    obtain ⟨S, hS'⟩ := hS z (interior_subset hz)
    have e : g₀ z = S := hS'.tsum_eq
    rw [e]
    exact hS'.tendsto_sum_nat
  have hval : ∀ y ∈ Y, ofReal y ∈ Z → g₀ (ofReal y) = ofReal (f (a + y)) := by
    intro y hy hyZ
    obtain ⟨S, hS'⟩ := hS _ hyZ
    have h1 : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (hp n).complexify (ofReal y)) atTop
        (𝓝 (ofReal (f (a + y)))) := by
      refine ((ofReal.continuous.tendsto _).comp (hsum y hy)).congr fun N ↦ ?_
      simp [Function.comp, map_sum, (hp _).complexify_ofReal]
    simp only [g₀]
    rw [hS'.tsum_eq]
    exact tendsto_nhds_unique hS'.tendsto_sum_nat h1
  set W : Set E := (fun x ↦ x - a) ⁻¹' (interior Y ∩ ofReal ⁻¹' H)
  have hW : IsOpen W :=
    (isOpen_interior.inter (isOpen_interior.preimage ofReal.continuous)).preimage
      (continuous_id.sub continuous_const)
  have haW : a ∈ W := by
    refine ⟨by simpa using mem_interior_iff_mem_nhds.2 hY, ?_⟩
    simp only [sub_self, mem_preimage, map_zero]
    exact mem_interior_iff_mem_nhds.2 hZ
  refine ⟨W, hW, haW, {z | z - ofReal a ∈ H}, ?_, fun z ↦ g₀ (z - ofReal a),
    hg₀.comp_sub_const (ofReal a), fun x hx ↦ ?_⟩
  · exact isOpen_interior.preimage (continuous_id.sub continuous_const)
  · obtain ⟨-, hxY, hxH⟩ := hx
    have e : ofReal x - ofReal a = ofReal (x - a) := (map_sub ofReal x a).symm
    refine ⟨?_, ?_⟩
    · change ofReal x - ofReal a ∈ H
      rw [e]
      exact hxH
    · change g₀ (ofReal x - ofReal a) = ofReal (f x)
      rw [e, hval _ (interior_subset hxY) (interior_subset hxH), add_sub_cancel]

/-- **Milnor real analyticity equals Bochnak–Siciak analyticity** when `E_ℂ` is a Baire space and
`F` is Mackey complete (e.g. `E` Fréchet and `F` sequentially complete). -/
theorem realAnalyticOn_iff_bsAnalyticOn [BaireSpace (Complexification E)] [MackeyComplete F]
    {f : E → F} {U : Set E} (hU : IsOpen U) : RealAnalyticOn f U ↔ BSAnalyticOn f U :=
  ⟨fun h ↦ h.bsAnalyticOn hU, realAnalyticOn_of_bsAnalyticOn hU⟩

end Theorem71

end LocallyConvex.Analysis

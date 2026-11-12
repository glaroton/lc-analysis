/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.Complex
public import LocallyConvexAnalysis.Analytic.HartogsLemma
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # Series of homogeneous polynomials

Pointwise convergence of a series `∑ pₙ` of continuous homogeneous polynomials between complex
topological vector spaces, after Bochnak and Siciak, *Analytic functions in topological vector
spaces*, Studia Math. 39 (1971), 77–112 (part II, §§4–5). Bochnak and Siciak assume
throughout that `F` is locally convex and sequentially complete. Here `F` is only assumed
**Mackey complete** (`LocallyConvex.Analysis.MackeyComplete`), which is strictly weaker, and only
for the analyticity of the sum; the Baire lemma needs neither completeness nor local convexity of
`F`.
Mackey completeness cannot be dropped (`not_mackeyComplete_geomSpan`).

## Main results

* `complexAnalyticOn_of_tendsto_sum` (**[BS71b, Theorem 5.2]**, complex case): over a
  complex locally convex Baire space `E`, with `F` Mackey complete, the sum of a series of
  continuous homogeneous polynomials converging pointwise on an open set `H` is complex analytic
  on `H`. Its ingredients:
  * `exists_line_geometric_bound`, `exists_compact_geometric_bound`: locally uniform geometric
    bounds along complex lines (the case needed of [BS71b, Proposition 4.1]), from
    Baire's theorem in `ℂ`, the Bernstein–Walsh inequality and Hartogs' lemma
    (`LocallyConvex.Analysis.hartogs_lemma`);
  * `gateauxAnalyticOn_of_tendsto` (Theorem 5.1): the sum is Gâteaux analytic, with Taylor
    coefficients along lines given by `hasPowerSeriesOnDisc_of_closedBall`;
  * `isContHomPoly_of_tendsto` (compare [BS71a, Theorem 2]): over a Baire space,
    pointwise limits of continuous homogeneous polynomials are continuous homogeneous
    polynomials;
  * `continuousOn_of_tendsto`: the sum is continuous;
  * `MackeyComplete.exists_hasSum_of_geometric`: in a Mackey complete space, a series with
    geometric bounds `q (vₙ) ≤ C_q θⁿ`, the ratio `θ` being the same for all seminorms,
    converges. The bounds along lines above have such a uniform ratio.

* `IsContHomPoly.seminorm_le_of_shift`: a bound `q (p (c + w)) ≤ M` on a balanced set `W`
  gives `q (p w) ≤ M` on `W`. This is a sharp complex form of Bochnak–Siciak, *Polynomials and
  multilinear mappings in topological vector spaces*, Studia Math. 39 (1971), 59–76, Lemma 2
  (ii), which over `ℝ` or `ℂ` gives the bound on `(2e)⁻¹ W`.
* `exists_nhds_geometric_bound`: over a complex **Baire** space `E`, if `∑ pₙ` converges on an
  absorbing set, then for each continuous seminorm `q` and each `θ > 0` the terms satisfy
  `q (pₙ w) ≤ C θⁿ` on a `0`-neighbourhood ([BS71b, Proposition 5.2], 1°: normal
  convergence at zero).
* `continuousAt_zero_of_tendsto_sum`: over a Baire space, the sum of a series converging on a
  `0`-neighbourhood is continuous at `0` ([BS71b, Proposition 5.2], 2°).

## Counterexamples

The two counterexamples showing that the hypotheses of `complexAnalyticOn_of_tendsto_sum` are
needed (`E` Baire, `F` Mackey complete) are in
`LocallyConvexAnalysis.Counterexamples.HomogeneousSeries`.

## Implementation notes

* Bochnak and Siciak propagate the bounds of Proposition 5.2 through Siciak's polynomial lemma
  (§4), which rests on potential theory in `ℂ` (Siciak's extremal function, Fekete points,
  regularity for the Dirichlet problem). Here only lines are needed: on a line through a point
  of `H`, a dilation by `λ > 1` makes the terms pointwise bounded, Baire's theorem in `ℂ` and the
  Bernstein–Walsh inequality give a uniform exponential bound, and Hartogs' lemma brings the
  growth rate below `λ`.
* Coefficient estimates for polynomials use discrete Fourier inversion over roots of unity
  (`seminorm_coeff_le_of_circle`), so no vector-valued integration is needed.
* The real case ([BS71b, Proposition 5.4 and Theorem 5.2] for `K = ℝ`) is not
  formalized.

## References

* [J. Bochnak, J. Siciak, *Polynomials and multilinear mappings in topological
  vector-spaces*][BS71a]
* [J. Bochnak, J. Siciak, *Analytic functions in topological vector-spaces*][BS71b]
-/

@[expose] public section

open Set Filter Function Metric Finset
open scoped Topology Real Pointwise

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Moving the centre of a bound (Bochnak–Siciak) -/

section Shift

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] {n : ℕ} {p : E → F}

/-- Averaging a homogeneous polynomial over a circle of roots of unity: with `m = n + 1` and
`ω = e^{2πi/m}`, `∑_{j < m} p (ωʲ c + w) = m • p w`. -/
theorem IsContHomPoly.sum_rootsOfUnity (hp : IsContHomPoly ℂ n p) (c w : E) :
    ∑ j ∈ range (n + 1), p (Complex.exp (2 * π * Complex.I / (n + 1 : ℕ)) ^ j • c + w) =
      ((n + 1 : ℕ) : ℂ) • p w := by
  classical
  obtain ⟨A, hA⟩ := hp
  set m := n + 1 with hm
  set ω := Complex.exp (2 * π * Complex.I / (m : ℕ))
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (by omega)
  set b : Finset (Fin n) → F := fun S ↦ A (S.piecewise (fun _ ↦ c) (fun _ ↦ w))
  have hexp : ∀ j : ℕ, p (ω ^ j • c + w) = ∑ S : Finset (Fin n), (ω ^ j) ^ S.card • b S := by
    intro j
    rw [hA]
    have e1 : (fun _ : Fin n ↦ ω ^ j • c + w) = (fun _ ↦ ω ^ j • c) + (fun _ ↦ w) := rfl
    rw [e1, A.map_add_univ]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    have e2 : S.piecewise (fun _ : Fin n ↦ ω ^ j • c) (fun _ ↦ w) =
        S.piecewise (fun i ↦ (fun _ ↦ ω ^ j) i • (S.piecewise (fun _ ↦ c) (fun _ ↦ w)) i)
          (S.piecewise (fun _ ↦ c) (fun _ ↦ w)) := by
      ext i; by_cases hi : i ∈ S <;> simp [hi]
    rw [e2, A.map_piecewise_smul, Finset.prod_const]
  have hgeom : ∀ k ≤ n, ∑ j ∈ range m, (ω ^ j) ^ k = if k = 0 then (m : ℂ) else 0 := by
    intro k hk
    have e : ∀ j, (ω ^ j) ^ k = (ω ^ k) ^ j := fun j ↦ by rw [← pow_mul, ← pow_mul, mul_comm]
    simp only [e]
    split_ifs with hk0
    · subst hk0; simp
    · have hne : ω ^ k ≠ 1 := by
        rw [Ne, hω.pow_eq_one_iff_dvd]
        exact fun h ↦ hk0 (Nat.eq_zero_of_dvd_of_lt h (by omega))
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
        zero_div]
  calc ∑ j ∈ range m, p (ω ^ j • c + w)
      = ∑ S : Finset (Fin n), (∑ j ∈ range m, (ω ^ j) ^ S.card) • b S := by
        simp only [hexp, Finset.sum_smul]; exact Finset.sum_comm
    _ = (m : ℂ) • b ∅ := by
        rw [Finset.sum_eq_single (∅ : Finset (Fin n))]
        · rw [Finset.card_empty, hgeom 0 (Nat.zero_le _)]; simp
        · intro S _ hS
          have hc : S.card ≠ 0 := by rwa [Ne, Finset.card_eq_zero]
          rw [hgeom S.card ((Finset.card_le_univ S).trans (by simp))]; simp [hc]
        · simp
    _ = (m : ℂ) • p w := by simp [b, hA]

/-- **Moving the centre of a bound** (Bochnak–Siciak, *Studia Math.* 39 (1971), Lemma 2 of
part I, used in the proof of Proposition 5.2 of part II): if a continuous homogeneous
polynomial satisfies `q (p (c + w)) ≤ M` on a balanced set `W`, then `q (p w) ≤ M` on `W`.
Only the algebraic structure of `p` is used, through `IsContHomPoly.sum_rootsOfUnity`. -/
theorem IsContHomPoly.seminorm_le_of_shift (hp : IsContHomPoly ℂ n p) (q : Seminorm ℂ F)
    {W : Set E} (hW : Balanced ℂ W) {c : E} {M : ℝ} (h : ∀ w ∈ W, q (p (c + w)) ≤ M) {w : E}
    (hw : w ∈ W) : q (p w) ≤ M := by
  set m := n + 1
  set ω := Complex.exp (2 * π * Complex.I / (m : ℕ))
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (by omega)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one (by omega)
  have hterm : ∀ j : ℕ, q (p (ω ^ j • c + w)) ≤ M := by
    intro j
    have hj : ω ^ j ≠ 0 := pow_ne_zero _ (by rw [← norm_ne_zero_iff, hω1]; exact one_ne_zero)
    have e : ω ^ j • c + w = ω ^ j • (c + (ω ^ j)⁻¹ • w) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ hj, one_smul]
    have hw' : (ω ^ j)⁻¹ • w ∈ W := hW.smul_mem (by simp [norm_pow, hω1]) hw
    rw [e, hp.map_smul, map_smul_eq_mul, norm_pow, norm_pow, hω1]
    simp only [one_pow, one_mul]
    exact h _ hw'
  have hm0 : (0 : ℝ) < m := by positivity
  have key : (m : ℝ) * q (p w) ≤ m * M := by
    have h1 : q (((m : ℕ) : ℂ) • p w) = m * q (p w) := by
      rw [map_smul_eq_mul, Complex.norm_natCast]
    rw [← h1, ← hp.sum_rootsOfUnity c w]
    calc q (∑ j ∈ range m, p (ω ^ j • c + w)) ≤ ∑ j ∈ range m, q (p (ω ^ j • c + w)) :=
          Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
      _ ≤ ∑ _j ∈ range m, M := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = m * M := by simp
  exact le_of_mul_le_mul_left key hm0

end Shift

/-! ### Normal convergence at zero over a Baire space ([BS71b, Proposition 5.2]) -/

section Baire

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  {p : ℕ → E → F}

omit [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] in
/-- If `∑ pₙ (a)` converges, the terms are bounded for each continuous seminorm. -/
theorem exists_bound_of_tendsto_sum [IsTopologicalAddGroup F] {q : Seminorm ℂ F}
    (hq : Continuous q) {a : E} {y : F}
    (h : Tendsto (fun N ↦ ∑ n ∈ range N, p n a) atTop (𝓝 y)) :
    ∃ C, 0 ≤ C ∧ ∀ n, q (p n a) ≤ C := by
  have h0 : Tendsto (fun n ↦ p n a) atTop (𝓝 0) := by
    have h2 := (h.comp (tendsto_add_atTop_nat 1)).sub h
    rw [sub_self] at h2
    exact h2.congr fun n ↦ by simp [Finset.sum_range_succ]
  have ht := (hq.tendsto 0).comp h0
  rw [map_zero] at ht
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  exact ⟨C, (apply_nonneg q _).trans (hC ⟨0, rfl⟩), fun n ↦ hC ⟨n, rfl⟩⟩

/-- **Normal convergence at zero** (Bochnak–Siciak, *Studia Math.* 39 (1971), part II,
Proposition 5.2, 1°). Let `E` be a complex Baire space and let `pₙ` be continuous homogeneous
polynomials of degree `n` such that `∑ pₙ (a)` converges for every `a` in an absorbing set `A`.
Then for every continuous seminorm `q` on `F` and every `θ > 0` there are a `0`-neighbourhood
`W` and `C` with `q (pₙ w) ≤ C θⁿ` for all `n` and `w ∈ W`. No completeness of `F` is needed,
and `F` need not be locally convex. -/
theorem exists_nhds_geometric_bound [BaireSpace E] [IsTopologicalAddGroup F]
    (hp : ∀ n, IsContHomPoly ℂ n (p n)) {A : Set E} (hA : Absorbent ℂ A)
    (hconv : ∀ a ∈ A, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, p n a) atTop (𝓝 y))
    {q : Seminorm ℂ F} (hq : Continuous q) {θ : ℝ} (hθ : 0 < θ) :
    ∃ W ∈ 𝓝 (0 : E), ∃ C, ∀ n, ∀ w ∈ W, q (p n w) ≤ C * θ ^ n := by
  -- pointwise geometric bounds on all of `E`
  have hpt : ∀ x : E, ∃ N k : ℕ, ∀ n, q (p n x) ≤ N * (k : ℝ) ^ n := by
    intro x
    obtain ⟨r, hr, hrA⟩ := (hA x).exists_pos
    obtain ⟨a, ha, hxa⟩ := hrA (r : ℂ) (by simp [abs_of_pos hr]) (mem_singleton x)
    obtain ⟨y, hy⟩ := hconv a ha
    obtain ⟨C, hC0, hC⟩ := exists_bound_of_tendsto_sum hq hy
    refine ⟨⌈C⌉₊, ⌈r⌉₊, fun n ↦ ?_⟩
    rw [← hxa, (hp n).map_smul, map_smul_eq_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
    calc r ^ n * q (p n a) ≤ (⌈r⌉₊ : ℝ) ^ n * ⌈C⌉₊ :=
          mul_le_mul (pow_le_pow_left₀ hr.le (Nat.le_ceil r) n) ((hC n).trans (Nat.le_ceil C))
            (apply_nonneg _ _) (by positivity)
      _ = _ := by ring
  -- Baire
  set K : ℕ × ℕ → Set E := fun i ↦ {x | ∀ n, q (p n x) ≤ i.1 * (i.2 : ℝ) ^ n}
  have hKc : ∀ i, IsClosed (K i) := fun i ↦ by
    simp only [K, Set.ofPred_forall]
    exact isClosed_iInter fun n ↦ isClosed_le (hq.comp (hp n).continuous) continuous_const
  have hKU : ⋃ i, K i = Set.univ := eq_univ_of_forall fun x ↦ by
    obtain ⟨N, k, h⟩ := hpt x
    exact mem_iUnion.2 ⟨(N, k), by simpa [K] using h⟩
  obtain ⟨⟨N, k⟩, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hKc hKU
  have hnhds : {w : E | x₀ + w ∈ K (N, k)} ∈ 𝓝 (0 : E) := by
    have h1 : Tendsto (fun w : E ↦ x₀ + w) (𝓝 0) (𝓝 x₀) := by
      simpa using (tendsto_const_nhds (x := x₀)).add (tendsto_id (x := 𝓝 (0 : E)))
    exact h1 (mem_interior_iff_mem_nhds.1 hx₀)
  set B := balancedCore ℂ {w : E | x₀ + w ∈ K (N, k)}
  have hB : B ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hnhds
  -- the bound on `x₀ + B` moves to `B`
  have hB' : ∀ n, ∀ w ∈ B, q (p n w) ≤ N * ((k + 1 : ℕ) : ℝ) ^ n := fun n w hw ↦ by
    refine ((hp n).seminorm_le_of_shift q (balancedCore.balanced _)
      (fun v hv ↦ (balancedCore_subset _ hv : v ∈ {w : E | x₀ + w ∈ K (N, k)}) n) hw).trans ?_
    gcongr; exact_mod_cast Nat.le_succ k
  -- rescale
  set s : ℝ := θ / (k + 1 : ℕ)
  have hs : 0 < s := by positivity
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨(s : ℂ) • B, (set_smul_mem_nhds_zero_iff hs0).2 hB, N, fun n w hw ↦ ?_⟩
  obtain ⟨b, hb, rfl⟩ := hw
  rw [(hp n).map_smul, map_smul_eq_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs.le]
  calc s ^ n * q (p n b) ≤ s ^ n * (N * ((k + 1 : ℕ) : ℝ) ^ n) := by gcongr; exact hB' n b hb
    _ = N * θ ^ n := by
        simp only [s, div_pow]
        field_simp

/-- **Continuity at zero** (Bochnak–Siciak, part II, Proposition 5.2, 2°): over a complex Baire
space, the sum of a series of continuous homogeneous polynomials converging on a
`0`-neighbourhood is continuous at `0`. No completeness of `F` is needed. -/
theorem continuousAt_zero_of_tendsto_sum [BaireSpace E] [IsTopologicalAddGroup F]
    [PolynormableSpace ℂ F] (hp : ∀ n, IsContHomPoly ℂ n (p n)) {U : Set E} (hU : U ∈ 𝓝 0)
    {f : E → F} (hf : ∀ x ∈ U, Tendsto (fun N ↦ ∑ n ∈ range N, p n x) atTop (𝓝 (f x))) :
    ContinuousAt f 0 := by
  refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
  obtain ⟨W, hW, C, hC⟩ := exists_nhds_geometric_bound hp (absorbent_nhds_zero hU)
    (fun a ha ↦ ⟨f a, hf a ha⟩) hq (by norm_num : (0 : ℝ) < 1 / 2)
  have hC0 : 0 ≤ C := by
    have := hC 0 0 (mem_of_mem_nhds hW)
    simpa using (apply_nonneg q _).trans this
  -- tail estimate
  have htail : ∀ x ∈ U ∩ W, ∀ K, q (f x - ∑ n ∈ range K, p n x) ≤ 2 * C * (1 / 2) ^ K := by
    intro x hx K
    have hlim : Tendsto (fun N ↦ q (∑ n ∈ range N, p n x - ∑ n ∈ range K, p n x)) atTop
        (𝓝 (q (f x - ∑ n ∈ range K, p n x))) :=
      (hq.tendsto _).comp ((hf x hx.1).sub_const _)
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨K, fun N hN ↦ ?_⟩)
    rw [← Finset.sum_range_add_sum_Ico _ hN, add_sub_cancel_left]
    calc q (∑ n ∈ Ico K N, p n x) ≤ ∑ n ∈ Ico K N, q (p n x) :=
          Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
      _ ≤ ∑ n ∈ Ico K N, C * (1 / 2) ^ n := Finset.sum_le_sum fun n _ ↦ hC n x hx.2
      _ ≤ 2 * C * (1 / 2) ^ K := by
          rw [← Finset.mul_sum]
          have : ∑ n ∈ Ico K N, ((1 : ℝ) / 2) ^ n ≤ 2 * (1 / 2) ^ K := by
            rw [Finset.sum_Ico_eq_sum_range]
            simp only [pow_add, ← Finset.mul_sum]
            have hg : ∑ i ∈ range (N - K), ((1 : ℝ) / 2) ^ i ≤ 2 := by
              have := sum_geometric_two_le (N - K)
              simpa [one_div] using this
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) K]
          nlinarith
  -- choose `K` with a small tail
  obtain ⟨K, hK⟩ : ∃ K, 2 * C * (1 / 2) ^ K < ε / 3 := by
    have ht : Tendsto (fun K ↦ 2 * C * ((1 : ℝ) / 2) ^ K) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (2 * C)
    exact (ht.eventually (gt_mem_nhds (by positivity))).exists
  -- the partial sum is continuous
  have hSc : Continuous fun x ↦ ∑ n ∈ range K, p n x :=
    continuous_finsetSum _ fun n _ ↦ (hp n).continuous
  have hS : ∀ᶠ x in 𝓝 0, q (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) < ε / 3 := by
    have := (hq.tendsto _).comp ((hSc.tendsto 0).sub_const (∑ n ∈ range K, p n 0))
    rw [sub_self, map_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hS, inter_mem hU hW] with x hx hxUW
  have h0UW : (0 : E) ∈ U ∩ W := ⟨mem_of_mem_nhds hU, mem_of_mem_nhds hW⟩
  have e : f x - f 0 = (f x - ∑ n ∈ range K, p n x) +
      (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) - (f 0 - ∑ n ∈ range K, p n 0) := by abel
  rw [e]
  calc q ((f x - ∑ n ∈ range K, p n x) + (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) -
        (f 0 - ∑ n ∈ range K, p n 0))
      ≤ q (f x - ∑ n ∈ range K, p n x) + q (∑ n ∈ range K, p n x - ∑ n ∈ range K, p n 0) +
          q (f 0 - ∑ n ∈ range K, p n 0) := by
        refine (map_sub_le_add q _ _).trans ?_
        gcongr
        exact map_add_le_add q _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h1 := htail x hxUW K
        have h2 := htail 0 h0UW K
        linarith
    _ = ε := by ring

end Baire

/-! ### Exponential sums -/

section ExpSum

/-- A nonzero constant is not eventually an exponential sum `∑ cᵢ λᵢⁿ` in which the base `1`
carries no weight. The bases may repeat. -/
theorem not_eventually_const_eq_expSum : ∀ (m : ℕ) (c lam : Fin m → ℂ) {a : ℂ} (N : ℕ),
    (∀ i, lam i = 1 → c i = 0) → a ≠ 0 → ¬ ∀ n ≥ N, a = ∑ i, c i * lam i ^ n
  | 0, c, lam, a, N, _, ha, h => ha (by simpa using h N le_rfl)
  | m + 1, c, lam, a, N, hc1, ha, h => by
    set l := lam (Fin.last m) with hl_def
    by_cases hl : l = 1
    · have hcl : c (Fin.last m) = 0 := hc1 _ hl
      refine not_eventually_const_eq_expSum m (fun i ↦ c i.castSucc) (fun i ↦ lam i.castSucc) N
        (fun i h ↦ hc1 _ h) ha fun n hn ↦ ?_
      rw [h n hn, Fin.sum_univ_castSucc, hcl, zero_mul, add_zero]
    · refine not_eventually_const_eq_expSum m (fun i ↦ c i.castSucc * (lam i.castSucc - l))
        (fun i ↦ lam i.castSucc) (a := a * (1 - l)) N (fun i h ↦ by simp [hc1 _ h])
        (mul_ne_zero ha (sub_ne_zero.2 (Ne.symm hl))) fun n hn ↦ ?_
      have h1 := h (n + 1) (by omega)
      have h0 := h n hn
      rw [Fin.sum_univ_castSucc] at h1 h0
      have e : ∑ i : Fin m, c i.castSucc * (lam i.castSucc - l) * lam i.castSucc ^ n =
          (∑ i : Fin m, c i.castSucc * lam i.castSucc ^ (n + 1)) -
            l * ∑ i : Fin m, c i.castSucc * lam i.castSucc ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e]
      linear_combination h1 - l * h0

/-- A non-constant affine sequence `a n + b` is not eventually an exponential sum
`∑ cᵢ λᵢⁿ`. The bases may repeat. -/
theorem not_eventually_affine_eq_expSum : ∀ (m : ℕ) (c lam : Fin m → ℂ) {a b : ℂ} (N : ℕ),
    a ≠ 0 → ¬ ∀ n ≥ N, a * n + b = ∑ i, c i * lam i ^ n
  | 0, c, lam, a, b, N, ha, h => by
    have h0 := h N le_rfl
    have h1 := h (N + 1) (by omega)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h0 h1
    push_cast at h1
    exact ha (by linear_combination h1 - h0)
  | m + 1, c, lam, a, b, N, ha, h => by
    set l := lam (Fin.last m) with hl_def
    have key : ∀ n ≥ N, a * (1 - l) * n + (a + b * (1 - l)) =
        ∑ i : Fin m, c i.castSucc * (lam i.castSucc - l) * lam i.castSucc ^ n := by
      intro n hn
      have h1 := h (n + 1) (by omega)
      have h0 := h n hn
      rw [Fin.sum_univ_castSucc] at h1 h0
      push_cast at h1
      have e : ∑ i : Fin m, c i.castSucc * (lam i.castSucc - l) * lam i.castSucc ^ n =
          (∑ i : Fin m, c i.castSucc * lam i.castSucc ^ (n + 1)) -
            l * ∑ i : Fin m, c i.castSucc * lam i.castSucc ^ n := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [e]
      linear_combination h1 - l * h0
    by_cases hl : l = 1
    · refine not_eventually_const_eq_expSum m (fun i ↦ c i.castSucc * (lam i.castSucc - l))
        (fun i ↦ lam i.castSucc) (a := a) N (fun i h ↦ by simp [h, hl]) ha fun n hn ↦ ?_
      have := key n hn
      rw [hl] at this ⊢
      simpa using this
    · exact not_eventually_affine_eq_expSum m _ _ N
        (mul_ne_zero ha (sub_ne_zero.2 (Ne.symm hl))) key

end ExpSum

/-! ### Homogeneous polynomials along lines -/

section Lines

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- `p : E → F` is an (algebraic) homogeneous polynomial of degree `k`: the diagonal of a
`k`-linear map, without any continuity. -/
def IsHomPoly (k : ℕ) (p : E → F) : Prop :=
  ∃ A : MultilinearMap ℂ (fun _ : Fin k ↦ E) F, ∀ x, p x = A fun _ ↦ x

theorem IsHomPoly.add {k : ℕ} {p q : E → F} (hp : IsHomPoly k p) (hq : IsHomPoly k q) :
    IsHomPoly k (p + q) := by
  obtain ⟨A, hA⟩ := hp
  obtain ⟨B, hB⟩ := hq
  exact ⟨A + B, fun x ↦ by simp [hA, hB]⟩

theorem IsHomPoly.zero {k : ℕ} : IsHomPoly k (0 : E → F) := ⟨0, fun _ ↦ rfl⟩

theorem IsHomPoly.sum {ι : Type*} (s : Finset ι) {k : ℕ} {p : ι → E → F}
    (hp : ∀ i ∈ s, IsHomPoly k (p i)) : IsHomPoly k (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsHomPoly.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hp a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hp i (Finset.mem_insert_of_mem hi))

theorem IsHomPoly.map_smul {k : ℕ} {p : E → F} (hp : IsHomPoly k p) (c : ℂ) (x : E) :
    p (c • x) = c ^ k • p x := by
  obtain ⟨A, hA⟩ := hp
  rw [hA, hA, show (fun _ : Fin k ↦ c • x) = fun i ↦ c • (fun _ : Fin k ↦ x) i from rfl,
    A.map_smul_univ]
  simp

theorem IsContHomPoly.isHomPoly [TopologicalSpace E] [TopologicalSpace F] {k : ℕ} {p : E → F}
    (hp : IsContHomPoly ℂ k p) : IsHomPoly k p := by
  obtain ⟨A, hA⟩ := hp
  exact ⟨A.toMultilinearMap, hA⟩

/-- The coefficient of `tᵏ` in `A (u + t v, …, u + t v)`. -/
def dirCoeff {n : ℕ} (A : MultilinearMap ℂ (fun _ : Fin n ↦ E) F) (u : E) (k : ℕ) (v : E) : F :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) ↦ S.card = k),
    A (S.piecewise (fun _ ↦ v) (fun _ ↦ u))

/-- **Expansion along a line**: `A (u + t v, …) = ∑_{k ≤ n} tᵏ dirCoeff A u k v`. -/
theorem apply_add_smul_eq_sum {n : ℕ} (A : MultilinearMap ℂ (fun _ : Fin n ↦ E) F) (u v : E)
    (t : ℂ) : A (fun _ ↦ u + t • v) =
      ∑ k ∈ range (n + 1), t ^ k • dirCoeff A u k v := by
  classical
  have e1 : (fun _ : Fin n ↦ u + t • v) = (fun _ ↦ t • v) + (fun _ ↦ u) := by
    ext; simp [add_comm]
  rw [e1, A.map_add_univ]
  have e2 : ∀ S : Finset (Fin n), A (S.piecewise (fun _ ↦ t • v) (fun _ ↦ u)) =
      t ^ S.card • A (S.piecewise (fun _ ↦ v) (fun _ ↦ u)) := by
    intro S
    have : S.piecewise (fun _ : Fin n ↦ t • v) (fun _ ↦ u) =
        S.piecewise (fun i ↦ (fun _ ↦ t) i • (S.piecewise (fun _ ↦ v) (fun _ ↦ u)) i)
          (S.piecewise (fun _ ↦ v) (fun _ ↦ u)) := by
      ext i; by_cases hi : i ∈ S <;> simp [hi]
    rw [this, A.map_piecewise_smul, Finset.prod_const]
  simp only [e2, dirCoeff, Finset.smul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1))
    (fun S _ ↦ Finset.mem_range.2 (Nat.lt_succ_of_le ((Finset.card_le_univ S).trans
      (by simp))))]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun S hS ↦ ?_
  rw [(Finset.mem_filter.1 hS).2]

theorem dirCoeff_eq_zero {n : ℕ} (A : MultilinearMap ℂ (fun _ : Fin n ↦ E) F) (u : E) {k : ℕ}
    (hk : n < k) (v : E) : dirCoeff A u k v = 0 := by
  refine Finset.sum_eq_zero fun S hS ↦ ?_
  have := (Finset.mem_filter.1 hS).2
  have := (Finset.card_le_univ S).trans (by simp : Fintype.card (Fin n) ≤ n)
  omega

/-- The coefficients along lines are homogeneous polynomials in the direction. -/
theorem isHomPoly_dirCoeff {n : ℕ} (A : MultilinearMap ℂ (fun _ : Fin n ↦ E) F) (u : E)
    (k : ℕ) : IsHomPoly k (dirCoeff A u k) := by
  classical
  have h : dirCoeff A u k = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) ↦ S.card = k),
      fun v ↦ A (S.piecewise (fun _ ↦ v) (fun _ ↦ u)) := by
    ext v; simp [dirCoeff]
  rw [h]
  refine IsHomPoly.sum _ fun S hS ↦ ?_
  have hk : S.card = k := (Finset.mem_filter.1 hS).2
  have hl : Sᶜ.card = n - k := by rw [Finset.card_compl, Fintype.card_fin, hk]
  let C := MultilinearMap.curryFinFinset ℂ F E hk hl A
  refine ⟨{ toFun := fun w ↦ C w (fun _ ↦ u)
            map_update_add' := fun w i x y ↦ by simp [C.map_update_add]
            map_update_smul' := fun w i c x ↦ by simp [C.map_update_smul] }, fun v ↦ ?_⟩
  exact (MultilinearMap.curryFinFinset_apply_const hk hl A v u).symm

/-- The coefficients along lines of a continuous multilinear map are continuous. -/
theorem continuous_dirCoeff [TopologicalSpace E] [TopologicalSpace F] [IsTopologicalAddGroup F]
    {n : ℕ} (A : ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) F) (u : E) (k : ℕ) :
    Continuous (dirCoeff A.toMultilinearMap u k) := by
  classical
  refine continuous_finsetSum _ fun S _ ↦ A.cont.comp (continuous_pi fun i ↦ ?_)
  by_cases hi : i ∈ S
  · simp only [Finset.piecewise, hi, ite_true]; exact continuous_id
  · simp only [Finset.piecewise, hi, ite_false]; exact continuous_const

end Lines

/-! ### Coefficient bounds from roots of unity -/

section Coeff

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- **Cauchy estimates for polynomials** without integrals: if `q (∑_{k ≤ N} tᵏ aₖ) ≤ M` on the
circle `|t| = r`, then `q (aₖ) ≤ M / rᵏ` (discrete Fourier inversion over the `(N+1)`-st roots of
unity). -/
theorem seminorm_coeff_le_of_circle (q : Seminorm ℂ F) {N : ℕ} (a : ℕ → F) {r M : ℝ}
    (hr : 0 < r) (h : ∀ t : ℂ, ‖t‖ = r → q (∑ k ∈ range (N + 1), t ^ k • a k) ≤ M) {k : ℕ}
    (hk : k ≤ N) : q (a k) ≤ M / r ^ k := by
  set m := N + 1
  set ω := Complex.exp (2 * π * Complex.I / (m : ℕ))
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m (by omega)
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one (by omega)
  have hgeom : ∀ i ∈ range m, ∑ j ∈ range m, (ω ^ (m - k + i)) ^ j =
      if i = k then (m : ℂ) else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    split_ifs with hik
    · subst hik
      rw [show m - i + i = m by omega, hω.pow_eq_one]; simp
    · have hne : ω ^ (m - k + i) ≠ 1 := by
        rw [Ne, hω.pow_eq_one_iff_dvd]
        rintro ⟨c, hc⟩
        rcases c with _ | _ | c
        · omega
        · omega
        · have h2 : 2 * m ≤ m * (c + 1 + 1) := by nlinarith
          omega
      rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self,
        zero_div]
  have key : ∑ j ∈ range m, (ω ^ (m - k)) ^ j •
      (∑ i ∈ range m, ((r : ℂ) * ω ^ j) ^ i • a i) = ((m : ℂ) * (r : ℂ) ^ k) • a k := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ i ∈ range m, ∑ j ∈ range m, ((ω ^ (m - k)) ^ j * ((r : ℂ) * ω ^ j) ^ i) • a i =
        ((r : ℂ) ^ i * if i = k then (m : ℂ) else 0) • a i := by
      intro i hi
      rw [← Finset.sum_smul, ← hgeom i hi, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, add_mul, pow_add, mul_comm j i]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_eq_single k]
    · simp [mul_comm]
    · intro i _ hik; simp [hik]
    · intro hk'; exact absurd (Finset.mem_range.2 (by omega)) hk'
  have hm0 : (0 : ℝ) < m := by positivity
  have hbound : q (((m : ℂ) * (r : ℂ) ^ k) • a k) ≤ m * M := by
    rw [← key]
    calc q (∑ j ∈ range m, (ω ^ (m - k)) ^ j • ∑ i ∈ range m, ((r : ℂ) * ω ^ j) ^ i • a i)
        ≤ ∑ j ∈ range m, q ((ω ^ (m - k)) ^ j • ∑ i ∈ range m, ((r : ℂ) * ω ^ j) ^ i • a i) :=
          Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
      _ ≤ ∑ _j ∈ range m, M := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [map_smul_eq_mul, norm_pow, norm_pow, hω1, one_pow, one_pow, one_mul]
          exact h _ (by rw [norm_mul, norm_pow, hω1, one_pow, mul_one, Complex.norm_real,
            Real.norm_of_nonneg hr.le])
      _ = m * M := by simp
  rw [map_smul_eq_mul, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hr.le] at hbound
  rw [le_div_iff₀ (by positivity)]
  nlinarith [apply_nonneg q (a k), pow_pos hr k]

end Coeff

/-! ### Propagation of bounds along complex lines ([BS71b, Proposition 4.1]) -/

section Propagation

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] {p : ℕ → E → F}

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- A continuous homogeneous polynomial restricted to an affine complex line is continuous and
weakly entire. -/
theorem IsContHomPoly.line {n : ℕ} {P : E → F} (hP : IsContHomPoly ℂ n P) (u v : E) :
    Continuous (fun z : ℂ ↦ P (u + z • v)) ∧
      ∀ ℓ : F →L[ℂ] ℂ, AnalyticOnNhd ℂ (ℓ ∘ fun z : ℂ ↦ P (u + z • v)) univ := by
  refine ⟨hP.continuous.comp (continuous_const.add (continuous_id.smul continuous_const)),
    fun ℓ ↦ ?_⟩
  obtain ⟨A, hA⟩ := hP
  have e : (ℓ ∘ fun z : ℂ ↦ P (u + z • v)) =
      fun z ↦ ∑ k ∈ range (n + 1), z ^ k * ℓ (dirCoeff A.toMultilinearMap u k v) := by
    funext z
    simp only [Function.comp, hA]
    rw [show (A fun _ ↦ u + z • v) = A.toMultilinearMap (fun _ ↦ u + z • v) from rfl,
      apply_add_smul_eq_sum, map_sum]
    simp
  rw [e]
  exact (Differentiable.differentiableOn (by fun_prop)).analyticOnNhd isOpen_univ

variable [PolynormableSpace ℂ F]

omit [ContinuousSMul ℂ F] in
/-- **Bounds along a complex line** (the case needed of [BS71b, Proposition 4.1]):
if `∑ pₙ` converges pointwise on an open set `H` and `x + z₀ y ∈ H`, then there are `r > 0`
and `θ < 1` such that for every continuous seminorm `q` there is `C` with
`q (pₙ (x + z y)) ≤ C θⁿ` for `|z - z₀| ≤ r`. The ratio `θ` depends only on the geometry of `H`
along the line, not on `q`; this is what makes Mackey completeness of `F` sufficient later.
Bochnak and Siciak use Siciak's polynomial lemma; here Baire's theorem in `ℂ`, the
Bernstein–Walsh inequality and Hartogs' lemma (`hartogs_lemma`) are used. -/
theorem exists_line_geometric_bound (hp : ∀ n, IsContHomPoly ℂ n (p n)) {H : Set E}
    (hH : IsOpen H) (hconv : ∀ a ∈ H, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, p n a) atTop (𝓝 y))
    {x y : E} {z₀ : ℂ} (hz₀ : x + z₀ • y ∈ H) :
    ∃ r > 0, ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ q : Seminorm ℂ F, Continuous q → ∃ C, 0 ≤ C ∧
      ∀ n, ∀ z ∈ closedBall z₀ r, q (p n (x + z • y)) ≤ C * θ ^ n := by
  -- Step 1: a dilation `λ > 1` keeping a disc about `z₀` inside `H`
  have hΦ : Continuous fun w : ℂ × ℂ ↦ w.1 • (x + w.2 • y) := by fun_prop
  have hmem : (fun w : ℂ × ℂ ↦ w.1 • (x + w.2 • y)) ⁻¹' H ∈ 𝓝 ((1 : ℂ), z₀) :=
    hΦ.continuousAt.preimage_mem_nhds (hH.mem_nhds (by simpa using hz₀))
  obtain ⟨δ, hδ, hδH⟩ := Metric.mem_nhds_iff.1 hmem
  set lam : ℝ := 1 + δ / 2
  have hlam : 1 < lam := by simp only [lam]; linarith
  have hlam0 : 0 < lam := by linarith
  set R₀ : ℝ := δ / 2
  have hR₀ : 0 < R₀ := by positivity
  have hinH : ∀ z ∈ closedBall z₀ R₀, (lam : ℂ) • (x + z • y) ∈ H := by
    intro z hz
    have : ((lam : ℂ), z) ∈ ball ((1 : ℂ), z₀) δ := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, (mem_closedBall.1 hz).trans_lt (by simp only [R₀]; linarith)⟩
      rw [dist_eq_norm, show (lam : ℂ) - 1 = ((δ / 2 : ℝ) : ℂ) by simp [lam],
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    exact hδH this
  set g : ℕ → ℂ → F := fun n z ↦ p n ((lam : ℂ) • (x + z • y))
  have hgline : ∀ n, g n = fun z ↦ p n ((lam : ℂ) • x + z • ((lam : ℂ) • y)) := fun n ↦ by
    funext z; simp only [g, smul_add, smul_comm (lam : ℂ) z y]
  -- the ratio `θ = λ^{-1/2}`, independent of the seminorm
  set ε : ℝ := Real.log lam / 2
  have hε : 0 < ε := by simp only [ε]; exact half_pos (Real.log_pos hlam)
  set θ : ℝ := Real.exp (-ε)
  have hθpos : 0 < θ := Real.exp_pos _
  have hθ1 : θ < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hθlam : ∀ n : ℕ, Real.exp (n * ε) / lam ^ n = θ ^ n := by
    intro n
    have hl : lam ^ n = Real.exp (n * (2 * ε)) := by
      rw [Real.exp_nat_mul, show 2 * ε = Real.log lam by simp only [ε]; ring,
        Real.exp_log hlam0]
    rw [hl, ← Real.exp_sub, ← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨R₀ / 2, by positivity, θ, hθpos.le, hθ1, fun q hq ↦ ?_⟩
  have hpt : ∀ z ∈ closedBall z₀ R₀, ∃ C, ∀ n, q (g n z) ≤ C := by
    intro z hz
    obtain ⟨yy, hyy⟩ := hconv _ (hinH z hz)
    obtain ⟨C, -, hC⟩ := exists_bound_of_tendsto_sum hq hyy
    exact ⟨C, hC⟩
  -- Step 2: Baire's theorem in `ℂ` gives a small disc with a uniform bound
  set T : Option ℕ → Set ℂ := fun i ↦ match i with
    | none => (ball z₀ R₀)ᶜ
    | some M => closedBall z₀ R₀ ∩ {z | ∀ n, q (g n z) ≤ M}
  have hTc : ∀ i, IsClosed (T i) := by
    rintro (_ | M)
    · exact isOpen_ball.isClosed_compl
    · simp only [T, Set.ofPred_forall]
      refine isClosed_closedBall.inter (isClosed_iInter fun n ↦ isClosed_le ?_ continuous_const)
      rw [hgline n]
      exact hq.comp ((hp n).line _ _).1
  have hTU : ⋃ i, T i = Set.univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    by_cases hz : z ∈ ball z₀ R₀
    · obtain ⟨C, hC⟩ := hpt z (ball_subset_closedBall hz)
      exact mem_iUnion.2 ⟨some ⌈C⌉₊, ball_subset_closedBall hz,
        fun n ↦ (hC n).trans (Nat.le_ceil C)⟩
    · exact mem_iUnion.2 ⟨none, hz⟩
  obtain ⟨z₁, hz₁b, hz₁i⟩ := (dense_iUnion_interior_of_closed hTc hTU).inter_open_nonempty _
    isOpen_ball ⟨z₀, mem_ball_self hR₀⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz₁i
  obtain ⟨M, rfl⟩ : ∃ M, i = some M := by
    cases i with
    | none => exact absurd (interior_subset hi) (by simpa [T] using hz₁b)
    | some M => exact ⟨M, rfl⟩
  obtain ⟨s₀, hs₀, hs₀T⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hi)
  set s : ℝ := s₀ / 2
  have hs : 0 < s := by positivity
  have hMdisc : ∀ z ∈ closedBall z₁ s, ∀ n, q (g n z) ≤ M := fun z hz ↦
    (hs₀T (closedBall_subset_ball (by simp only [s]; linarith) hz)).2
  clear_value s
  -- Step 3: Bernstein–Walsh on `closedBall z₀ R₀`
  set K : ℝ := max 1 (2 * R₀ / s)
  set M' : ℝ := max (M : ℝ) 1
  set B : ℝ := Real.log (2 * M' * K)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hM'1 : 1 ≤ M' := le_max_right _ _
  have hBW : ∀ n ≥ 1, ∀ z ∈ closedBall z₀ R₀, q (g n z) ≤ Real.exp (n * B) := by
    intro n hn z hz
    obtain ⟨A, hA⟩ := hp n
    set u : E := (lam : ℂ) • (x + z₁ • y)
    set v : E := (lam : ℂ) • y
    have hexp : ∀ w : ℂ, g n (z₁ + w) =
        ∑ k ∈ range (n + 1), w ^ k • dirCoeff A.toMultilinearMap u k v := by
      intro w
      have : (lam : ℂ) • (x + (z₁ + w) • y) = u + w • v := by
        simp only [u, v, add_smul, smul_add, smul_comm (lam : ℂ) w y]; abel
      simp only [g, this, hA]
      exact apply_add_smul_eq_sum A.toMultilinearMap u v w
    have hcoef : ∀ k ≤ n, q (dirCoeff A.toMultilinearMap u k v) ≤ M / s ^ k := by
      intro k hk
      refine seminorm_coeff_le_of_circle q (N := n) (fun k ↦ dirCoeff A.toMultilinearMap u k v)
        (M := M) hs (fun t ht ↦ ?_) hk
      rw [← hexp]
      exact hMdisc _ (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, ht]) n
    have hw : ‖z - z₁‖ ≤ 2 * R₀ := by
      calc ‖z - z₁‖ ≤ ‖z - z₀‖ + ‖z₀ - z₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ R₀ + R₀ := by
            gcongr
            · exact mem_closedBall_iff_norm.1 hz
            · rw [← dist_eq_norm, dist_comm]; exact (mem_ball.1 hz₁b).le
        _ = 2 * R₀ := by ring
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hsum : q (g n z) ≤ (n + 1) * (M * K ^ n) := by
      have hz' := hexp (z - z₁)
      rw [add_sub_cancel] at hz'
      rw [hz']
      calc q (∑ k ∈ range (n + 1), (z - z₁) ^ k • dirCoeff A.toMultilinearMap u k v)
          ≤ ∑ k ∈ range (n + 1), q ((z - z₁) ^ k • dirCoeff A.toMultilinearMap u k v) :=
            Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
        _ ≤ ∑ _k ∈ range (n + 1), M * K ^ n := by
            refine Finset.sum_le_sum fun k hk ↦ ?_
            have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
            rw [map_smul_eq_mul, norm_pow]
            calc ‖z - z₁‖ ^ k * q (dirCoeff A.toMultilinearMap u k v)
                ≤ (2 * R₀) ^ k * (M / s ^ k) :=
                  mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hw k) (hcoef k hk')
                    (apply_nonneg q _) (by positivity)
              _ = M * (2 * R₀ / s) ^ k := by rw [div_pow]; ring
              _ ≤ M * K ^ k := by gcongr; exact le_max_right _ _
              _ ≤ M * K ^ n := by gcongr
        _ = (n + 1) * (M * K ^ n) := by simp
    calc q (g n z) ≤ (n + 1) * (M * K ^ n) := hsum
      _ ≤ 2 ^ n * (M' ^ n * K ^ n) := by
          gcongr
          · exact_mod_cast Nat.lt_two_pow_self
          · exact (le_max_left _ _).trans (le_self_pow₀ hM'1 (by omega))
      _ = (2 * M' * K) ^ n := by ring
      _ = Real.exp (n * B) := by
          rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  -- Step 4: Hartogs' lemma
  obtain ⟨N, hN⟩ := hartogs_lemma (g := g)
    (fun n ↦ by rw [hgline n]; exact ((hp n).line _ _).1)
    (fun n ℓ ↦ by rw [hgline n]; exact ((hp n).line _ _).2 ℓ) hq hR₀ hBW hpt hε
  -- Step 5: undo the dilation
  have hpn : ∀ n z, q (p n (x + z • y)) = q (g n z) / lam ^ n := by
    intro n z
    simp only [g]
    rw [(hp n).map_smul, map_smul_eq_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hlam0.le]
    field_simp
  have hcomp : ∀ n, ∃ D, ∀ z ∈ closedBall z₀ (R₀ / 2), q (p n (x + z • y)) ≤ D := fun n ↦ by
    obtain ⟨D, hD⟩ := (isCompact_closedBall z₀ (R₀ / 2)).exists_bound_of_continuousOn
      (f := fun z ↦ q (p n (x + z • y))) (hq.comp ((hp n).line x y).1).continuousOn
    exact ⟨D, fun z hz ↦ (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hD z hz)⟩
  choose D hD using hcomp
  set C : ℝ := 1 + ∑ n ∈ range N, |D n| / θ ^ n
  have hS0 : 0 ≤ ∑ n ∈ range N, |D n| / θ ^ n :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hC1 : 1 ≤ C := by simp only [C]; linarith
  refine ⟨C, by linarith, fun n z hz ↦ ?_⟩
  by_cases hn : n < N
  · have hle : |D n| / θ ^ n ≤ C := by
      have := Finset.single_le_sum (f := fun n ↦ |D n| / θ ^ n) (fun i _ ↦ by positivity)
        (Finset.mem_range.2 hn)
      simp only [C]; linarith
    calc q (p n (x + z • y)) ≤ |D n| := (hD n z hz).trans (le_abs_self _)
      _ = |D n| / θ ^ n * θ ^ n := by field_simp
      _ ≤ C * θ ^ n := by gcongr
  · rw [not_lt] at hn
    calc q (p n (x + z • y)) = q (g n z) / lam ^ n := hpn n z
      _ ≤ Real.exp (n * ε) / lam ^ n := by gcongr; exact hN n hn z hz
      _ = θ ^ n := hθlam n
      _ ≤ C * θ ^ n := le_mul_of_one_le_left (by positivity) hC1

omit [ContinuousSMul ℂ F] in
/-- The bounds of `exists_line_geometric_bound` are uniform on compact subsets of the line, still
with a ratio `θ` independent of the seminorm. -/
theorem exists_compact_geometric_bound (hp : ∀ n, IsContHomPoly ℂ n (p n)) {H : Set E}
    (hH : IsOpen H) (hconv : ∀ a ∈ H, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, p n a) atTop (𝓝 y))
    {x y : E} {K : Set ℂ} (hK : IsCompact K) (hKH : ∀ z ∈ K, x + z • y ∈ H) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ q : Seminorm ℂ F, Continuous q → ∃ C, 0 ≤ C ∧
      ∀ n, ∀ z ∈ K, q (p n (x + z • y)) ≤ C * θ ^ n := by
  classical
  have hloc : ∀ z ∈ K, ∃ r > 0, ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ q : Seminorm ℂ F, Continuous q →
      ∃ C, 0 ≤ C ∧ ∀ n, ∀ w ∈ closedBall z r, q (p n (x + w • y)) ≤ C * θ ^ n := fun z hz ↦
    exists_line_geometric_bound hp hH hconv (hKH z hz)
  choose! r hr θ hθ0 hθ1 hθC using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun z ↦ closedBall z (r z))
    (fun z hz ↦ closedBall_mem_nhds z (hr z hz))
  set Θ : NNReal := t.sup fun z ↦ (θ z).toNNReal
  have hΘ1 : (Θ : ℝ) < 1 := by
    have : Θ < 1 := (Finset.sup_lt_iff (by simp)).2 fun z hz ↦
      Real.toNNReal_lt_one.2 (hθ1 z (htK z hz))
    exact_mod_cast this
  have hθΘ : ∀ z ∈ t, θ z ≤ Θ := fun z hz ↦
    (Real.le_coe_toNNReal _).trans
      (by exact_mod_cast Finset.le_sup (f := fun z ↦ (θ z).toNNReal) hz)
  refine ⟨Θ, Θ.2, hΘ1, fun q hq ↦ ?_⟩
  choose! C hC0 hC using fun z (hz : z ∈ K) ↦ hθC z hz q hq
  refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg fun z hz ↦ hC0 z (htK z hz), fun n w hw ↦ ?_⟩
  obtain ⟨z, hzt, hwz⟩ := mem_iUnion₂.1 (hcover hw)
  calc q (p n (x + w • y)) ≤ C z * θ z ^ n := hC z (htK z hzt) n w hwz
    _ ≤ (∑ z ∈ t, C z) * Θ ^ n := by
        have h0 := hθ0 z (htK z hzt)
        exact mul_le_mul (Finset.single_le_sum (fun z hz ↦ hC0 z (htK z hz)) hzt)
          (pow_le_pow_left₀ h0 (hθΘ z hzt) n) (by positivity)
          (Finset.sum_nonneg fun z hz ↦ hC0 z (htK z hz))

end Propagation

/-! ### Gâteaux analyticity of the sum -/

section Gateaux

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F]
  (A : ∀ n, ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) F) {H : Set E}

omit [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] in
/-- In a Mackey complete space, a series whose terms satisfy `q (vₙ) ≤ C_q θⁿ` for every
continuous seminorm `q`, with **one** ratio `θ < 1` for all `q`, converges. Indeed, with
`θ < θ' < 1`, the partial sums `uₙ` satisfy `u_l - u_k ∈ θ'^k • B` for `k ≤ l`, where the set
`B` of the vectors `θ'^{-k} (u_l - u_k)` is bounded: the partial sums are Mackey–Cauchy. If the
ratio depended on `q`, the set `B` need not be bounded. -/
theorem MackeyComplete.exists_hasSum_of_geometric [Module ℝ F] [IsScalarTower ℝ ℂ F]
    [MackeyComplete F] {v : ℕ → F} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hv : ∀ q : Seminorm ℂ F, Continuous q → ∃ C, ∀ n, q (v n) ≤ C * θ ^ n) :
    ∃ s, HasSum v s := by
  set θ' : ℝ := (1 + θ) / 2
  have hθ'0 : 0 < θ' := by simp only [θ']; linarith
  have hθ'1 : θ' < 1 := by simp only [θ']; linarith
  have hθθ' : θ ≤ θ' := by simp only [θ']; linarith
  have h1θ : 0 < 1 - θ := by linarith
  set u : ℕ → F := fun N ↦ ∑ n ∈ range N, v n
  have hdiff : ∀ k l, k ≤ l → u l - u k = ∑ n ∈ Ico k l, v n := fun k l hkl ↦ by
    simp only [u]
    rw [← Finset.sum_range_add_sum_Ico _ hkl]
    abel
  set B : Set F := {w | ∃ k l, k ≤ l ∧ w = (θ' ^ k)⁻¹ • (u l - u k)}
  have hB : Bornology.IsVonNBounded ℂ B := by
    refine (PolynormableSpace.withSeminorms ℂ F).isVonNBounded_iff_seminorm_bounded.2
      fun q ↦ ?_
    obtain ⟨C, hC⟩ := hv q.1 q.2
    have hC' : 0 ≤ |C| / (1 - θ) := div_nonneg (abs_nonneg C) h1θ.le
    refine ⟨|C| / (1 - θ) + 1, by linarith, ?_⟩
    rintro _ ⟨k, l, hkl, rfl⟩
    have hpos : 0 < θ' ^ k := pow_pos hθ'0 k
    have h1 : q.1 (u l - u k) ≤ |C| * (θ ^ k / (1 - θ)) := by
      rw [hdiff k l hkl]
      calc q.1 (∑ n ∈ Ico k l, v n) ≤ ∑ n ∈ Ico k l, q.1 (v n) :=
            Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
        _ ≤ ∑ n ∈ Ico k l, |C| * θ ^ n := Finset.sum_le_sum fun n _ ↦
            (hC n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
        _ = |C| * ∑ n ∈ Ico k l, θ ^ n := by rw [Finset.mul_sum]
        _ ≤ |C| * (θ ^ k / (1 - θ)) := by
            gcongr
            exact geom_sum_Ico_le_of_lt_one hθ0 hθ1
    calc q.1 ((θ' ^ k)⁻¹ • (u l - u k)) = (θ' ^ k)⁻¹ * q.1 (u l - u k) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul_eq_mul, RCLike.norm_ofReal,
            abs_of_nonneg (by positivity)]
      _ ≤ (θ' ^ k)⁻¹ * (|C| * (θ ^ k / (1 - θ))) := by gcongr
      _ = |C| / (1 - θ) * (θ ^ k / θ' ^ k) := by ring
      _ ≤ |C| / (1 - θ) * 1 := mul_le_mul_of_nonneg_left
          (div_le_one_of_le₀ (pow_le_pow_left₀ hθ0 hθθ' k) hpos.le) hC'
      _ < |C| / (1 - θ) + 1 := by linarith
  obtain ⟨y, hy⟩ := MackeyComplete.exists_tendsto u B (fun k ↦ θ' ^ k) (hB.restrict_scalars ℝ)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hθ'0.le hθ'1) fun k l hkl ↦
      ⟨(θ' ^ k)⁻¹ • (u l - u k), ⟨k, l, hkl, rfl⟩, by
        change θ' ^ k • ((θ' ^ k)⁻¹ • (u l - u k)) = u l - u k
        rw [smul_smul, mul_inv_cancel₀ (pow_pos hθ'0 k).ne', one_smul]⟩
  refine ⟨y, hasSum_of_tendsto_of_dominated hy fun q hq ↦ ?_⟩
  obtain ⟨C, hC⟩ := hv q hq
  exact ⟨fun n ↦ C * θ ^ n, (summable_geometric_of_lt_one hθ0 hθ1).mul_left C, hC⟩

omit [ContinuousSMul ℂ F] in
/-- Geometric bounds for the coefficients of the series along a line, with a ratio `θ`
independent of the seminorm. -/
theorem exists_dirCoeff_bound (hH : IsOpen H)
    (hconv : ∀ a ∈ H, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 y))
    {x y : E} {R : ℝ} (hR : 0 < R) (hsub : ∀ z ∈ closedBall (0 : ℂ) R, x + z • y ∈ H) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ q : Seminorm ℂ F, Continuous q → ∃ C, 0 ≤ C ∧
      ∀ n k, q (dirCoeff (A n).toMultilinearMap x k y) ≤ C * θ ^ n / R ^ k := by
  obtain ⟨θ, hθ0, hθ1, hθC⟩ := exists_compact_geometric_bound
    (p := fun n a ↦ A n fun _ ↦ a) (fun n ↦ ⟨A n, fun _ ↦ rfl⟩) hH hconv
    (isCompact_closedBall 0 R) hsub
  refine ⟨θ, hθ0, hθ1, fun q hq ↦ ?_⟩
  obtain ⟨C, hC0, hC⟩ := hθC q hq
  refine ⟨C, hC0, fun n k ↦ ?_⟩
  by_cases hk : k ≤ n
  · refine seminorm_coeff_le_of_circle q (N := n) (fun k ↦ dirCoeff (A n).toMultilinearMap x k y)
      hR (fun t ht ↦ ?_) hk
    rw [← apply_add_smul_eq_sum]
    exact hC n t (by rw [mem_closedBall, dist_zero_right, ht])
  · rw [dirCoeff_eq_zero _ _ (by omega), map_zero]
    positivity

variable [T2Space F]

/-- **Expansion along lines** ([BS71b, Theorem 5.1], complex case): if `∑ pₙ`
converges to `f` on an open set `H` and `F` is Mackey complete, then on each complex line
`z ↦ x + z y` the sum is a power series on every disc whose closure lies in `H`. -/
theorem hasPowerSeriesOnDisc_of_closedBall [Module ℝ F] [IsScalarTower ℝ ℂ F]
    [MackeyComplete F] (hH : IsOpen H) {f : E → F}
    (hf : ∀ a ∈ H, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 (f a)))
    {x y : E} {R : ℝ} (hR : 0 < R) (hsub : ∀ z ∈ closedBall (0 : ℂ) R, x + z • y ∈ H) :
    HasPowerSeriesOnDisc (fun z ↦ f (x + z • y))
      (fun k ↦ ∑' n, dirCoeff (A n).toMultilinearMap x k y) 0 R := by
  have hconv : ∀ a ∈ H, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 y) :=
    fun a ha ↦ ⟨f a, hf a ha⟩
  set c : ℕ → ℕ → F := fun n k ↦ dirCoeff (A n).toMultilinearMap x k y
  have hb : ∀ k, HasSum (fun n ↦ c n k) (∑' n, c n k) := by
    intro k
    obtain ⟨θ, hθ0, hθ1, hθC⟩ := exists_dirCoeff_bound A hH hconv hR hsub
    obtain ⟨s, hs⟩ := MackeyComplete.exists_hasSum_of_geometric (v := fun n ↦ c n k) hθ0 hθ1
        fun q hq ↦ by
      obtain ⟨C, -, hC⟩ := hθC q hq
      exact ⟨C / R ^ k, fun n ↦ (hC n k).trans_eq (by ring)⟩
    rwa [hs.tsum_eq]
  intro w hw
  rw [zero_add]
  set ρ : ℝ := ‖w‖ / R
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one hR).2 hw
  -- the expansion of the partial sums
  have hS : ∀ N, ∑ n ∈ range N, (A n fun _ ↦ x + w • y) =
      ∑ n ∈ range N, ∑ k ∈ range N, w ^ k • c n k := by
    intro N
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [show (A n fun _ ↦ x + w • y) = (A n).toMultilinearMap (fun _ ↦ x + w • y) from rfl,
      apply_add_smul_eq_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (Finset.mem_range.1 hn)) fun k _ hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    simp only [dirCoeff_eq_zero _ _ hk, smul_zero]
  refine hasSum_of_tendsto_of_dominated ?_ fun q hq ↦ ?_
  · refine tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
    obtain ⟨θ, hθ0, hθ1, hθC⟩ := exists_dirCoeff_bound A hH hconv hR hsub
    obtain ⟨C, hC0, hC⟩ := hθC q hq
    set β : ℕ → ℝ := fun K ↦ C / (1 - θ) * (ρ ^ K / (1 - ρ))
    have hβ : Tendsto β atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).div_const (1 - ρ)).const_mul
        (C / (1 - θ))
      simpa [β] using this
    have key : ∀ K, q (∑ k ∈ range K, w ^ k • ∑' n, c n k - f (x + w • y)) ≤ β K := by
      intro K
      have hlim : Tendsto (fun N ↦ ∑ k ∈ range K, w ^ k • ∑ n ∈ range N, c n k -
          ∑ n ∈ range N, (A n fun _ ↦ x + w • y)) atTop
          (𝓝 (∑ k ∈ range K, w ^ k • ∑' n, c n k - f (x + w • y))) := by
        refine Tendsto.sub (tendsto_finsetSum _ fun k _ ↦ ?_) (hf _ (hsub w ?_))
        · exact ((hb k).tendsto_sum_nat).const_smul _
        · rw [mem_closedBall, dist_zero_right]; exact hw.le
      refine le_of_tendsto ((hq.tendsto _).comp hlim) (eventually_atTop.2 ⟨K, fun N hN ↦ ?_⟩)
      simp only [Function.comp]
      set D : F := ∑ n ∈ range N, ∑ k ∈ Ico K N, w ^ k • c n k
      have e : ∑ k ∈ range K, w ^ k • ∑ n ∈ range N, c n k -
          ∑ n ∈ range N, (A n fun _ ↦ x + w • y) = -D := by
        rw [hS N]
        simp only [Finset.smul_sum]
        rw [Finset.sum_comm]
        simp only [D, ← Finset.sum_range_add_sum_Ico _ hN, Finset.sum_add_distrib]
        abel
      rw [e, map_neg_eq_map]
      have hθs : ∑ n ∈ range N, θ ^ n ≤ 1 / (1 - θ) := by
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hθ0 hθ1
        rwa [← Finset.range_eq_Ico, pow_zero] at this
      have hρs : ∑ k ∈ Ico K N, ρ ^ k ≤ ρ ^ K / (1 - ρ) := geom_sum_Ico_le_of_lt_one hρ0 hρ1
      calc q D ≤ ∑ n ∈ range N, ∑ k ∈ Ico K N, q (w ^ k • c n k) := by
            refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans
              (Finset.sum_le_sum fun n _ ↦ ?_)
            exact Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
        _ ≤ ∑ n ∈ range N, ∑ k ∈ Ico K N, C * θ ^ n * ρ ^ k := by
            refine Finset.sum_le_sum fun n _ ↦ Finset.sum_le_sum fun k _ ↦ ?_
            rw [map_smul_eq_mul, norm_pow]
            calc ‖w‖ ^ k * q (c n k) ≤ ‖w‖ ^ k * (C * θ ^ n / R ^ k) := by
                  gcongr; exact hC n k
              _ = C * θ ^ n * ρ ^ k := by simp only [ρ, div_pow]; field_simp
        _ = C * (∑ n ∈ range N, θ ^ n) * (∑ k ∈ Ico K N, ρ ^ k) := by
            rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun n _ ↦ ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ ↦ by ring
        _ ≤ C * (1 / (1 - θ)) * (ρ ^ K / (1 - ρ)) := by
            gcongr
        _ = β K := by simp only [β]; ring
    filter_upwards [hβ.eventually (gt_mem_nhds hε)] with K hK
    exact (key K).trans_lt hK
  · obtain ⟨θ, hθ0, hθ1, hθC⟩ := exists_dirCoeff_bound A hH hconv hR hsub
    obtain ⟨C, hC0, hC⟩ := hθC q hq
    refine ⟨fun k ↦ C / (1 - θ) * ρ ^ k,
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left _, fun k ↦ ?_⟩
    have hsumm : Summable fun n ↦ C / R ^ k * θ ^ n :=
      (summable_geometric_of_lt_one hθ0 hθ1).mul_left _
    have hqb : q (∑' n, c n k) ≤ ∑' n, C / R ^ k * θ ^ n :=
      seminorm_le_of_hasSum hq (hb k) hsumm fun n ↦ by
        rw [mul_comm (C / R ^ k), mul_div_assoc', mul_comm (θ ^ n)]; exact hC n k
    rw [tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1] at hqb
    rw [map_smul_eq_mul, norm_pow]
    calc ‖w‖ ^ k * q (∑' n, c n k) ≤ ‖w‖ ^ k * (C / R ^ k * (1 - θ)⁻¹) := by gcongr
      _ = C / (1 - θ) * ρ ^ k := by simp only [ρ, div_pow]; field_simp

/-- **Gâteaux analyticity of the sum** ([BS71b, Theorem 5.1], complex case, with a
Mackey complete target): the sum of a series of continuous homogeneous polynomials converging
on an open set `H` is Gâteaux analytic on `H`. No Baire hypothesis is needed. -/
theorem gateauxAnalyticOn_of_tendsto [Module ℝ F] [IsScalarTower ℝ ℂ F] [MackeyComplete F]
    (hH : IsOpen H) {f : E → F}
    (hf : ∀ a ∈ H, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 (f a))) :
    GateauxAnalyticOn f H := by
  intro x _ y z₀ hz₀
  have hΩ : IsOpen {z : ℂ | x + z • y ∈ H} :=
    hH.preimage (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ z₀ hz₀
  refine ⟨ε / 2, by positivity, (ball_subset_ball (by linarith)).trans hball,
    fun k ↦ ∑' n, dirCoeff (A n).toMultilinearMap (x + z₀ • y) k y, ?_⟩
  have hsub : ∀ z ∈ closedBall (0 : ℂ) (ε / 2), (x + z₀ • y) + z • y ∈ H := by
    intro z hz
    have : z₀ + z ∈ ball z₀ ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [mem_closedBall, dist_zero_right] at hz
      linarith
    have h := hball this
    simp only [Set.mem_ofPred_eq, add_smul] at h
    rwa [add_assoc]
  have hps := hasPowerSeriesOnDisc_of_closedBall A hH hf (by positivity) hsub
  intro w hw
  have := hps w hw
  simp only [zero_add] at this
  simpa only [add_smul, add_assoc] using this

end Gateaux

/-! ### Pointwise limits of homogeneous polynomials ([BS71a, Theorem 2]) -/

section Limits

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]

/-- **Pointwise limits of continuous homogeneous polynomials** over a Baire space (compare
[BS71a, Theorem 2]): if continuous homogeneous polynomials `Q_N` of degree `k`
converge pointwise to `P`, then `P` is a continuous homogeneous polynomial of degree `k`.
The multilinear map of `P` is the pointwise limit of the polarizations; continuity of `P`
follows from a uniform bound on a `0`-neighbourhood (Baire and
`IsContHomPoly.seminorm_le_of_shift`) and the Cauchy estimates along lines
(`seminorm_coeff_le_of_circle`). No completeness of `F` is needed. -/
theorem isContHomPoly_of_tendsto [BaireSpace E] {k : ℕ} {Q : ℕ → E → F}
    (hQ : ∀ N, IsContHomPoly ℂ k (Q N)) {P : E → F}
    (hP : ∀ v, Tendsto (fun N ↦ Q N v) atTop (𝓝 (P v))) : IsContHomPoly ℂ k P := by
  classical
  -- the algebraic multilinear map
  choose B hBsym hB using fun N ↦ (hQ N).exists_symm
  set c : ℂ := ((2 ^ Fintype.card (Fin k) * (Fintype.card (Fin k)).factorial : ℕ) : ℂ)⁻¹
  set Pol : (Fin k → E) → F := fun x ↦
    c • ∑ ε : Fin k → ℤˣ, (∏ j, ε j) • P (∑ j, ε j • x j)
  have hconvB : ∀ x, Tendsto (fun N ↦ B N x) atTop (𝓝 (Pol x)) := by
    intro x
    have e : ∀ N, B N x = c • ∑ ε : Fin k → ℤˣ, (∏ j, ε j) • Q N (∑ j, ε j • x j) := by
      intro N
      rw [← ContinuousMultilinearMap.coe_coe, MultilinearMap.eq_polarization (hBsym N) x]
      congr 1
      refine Finset.sum_congr rfl fun ε _ ↦ ?_
      rw [hB N]
      rfl
    simp only [e, Pol]
    exact (tendsto_finsetSum _ fun ε _ ↦ (hP _).const_smul _).const_smul _
  let Atil : MultilinearMap ℂ (fun _ : Fin k ↦ E) F :=
    { toFun := Pol
      map_update_add' := fun m i x y ↦ by
        refine tendsto_nhds_unique (hconvB _) ?_
        refine ((hconvB (Function.update m i x)).add (hconvB (Function.update m i y))).congr
          fun N ↦ ?_
        exact ((B N).map_update_add m i x y).symm
      map_update_smul' := fun m i a x ↦ by
        refine tendsto_nhds_unique (hconvB _) ?_
        refine ((hconvB (Function.update m i x)).const_smul a).congr fun N ↦ ?_
        exact ((B N).map_update_smul m i a x).symm }
  have hdiag : ∀ v, P v = Atil fun _ ↦ v := fun v ↦
    tendsto_nhds_unique (hP v) ((hconvB fun _ ↦ v).congr fun N ↦ (hB N v).symm)
  have hPhom : IsHomPoly k P := ⟨Atil, hdiag⟩
  refine isContHomPoly_iff_continuous.2 ⟨?_, Atil, funext fun v ↦ hdiag v⟩
  refine continuous_iff_continuousAt.2 fun x₀ ↦ tendsto_nhds_iff_seminorm.2 fun q hq ε hε ↦ ?_
  -- Step 1: a uniform bound on a balanced `0`-neighbourhood
  obtain ⟨W₀, hW₀, hW₀b, M, hM0, hM⟩ : ∃ W₀ ∈ 𝓝 (0 : E), Balanced ℂ W₀ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ w ∈ W₀, q (P w) ≤ M := by
    set S : ℕ → Set E := fun M ↦ {v | ∀ N, q (Q N v) ≤ M}
    have hSc : ∀ M, IsClosed (S M) := fun M ↦ by
      simp only [S, Set.ofPred_forall]
      exact isClosed_iInter fun N ↦ isClosed_le (hq.comp (hQ N).continuous) continuous_const
    have hSU : ⋃ M, S M = Set.univ := eq_univ_of_forall fun v ↦ by
      obtain ⟨C, hC⟩ := ((hq.tendsto _).comp (hP v)).bddAbove_range
      exact mem_iUnion.2 ⟨⌈C⌉₊, fun N ↦ (hC ⟨N, rfl⟩).trans (Nat.le_ceil C)⟩
    obtain ⟨M, x₁, hx₁⟩ := nonempty_interior_of_iUnion_of_closed hSc hSU
    have hV : {w : E | x₁ + w ∈ S M} ∈ 𝓝 (0 : E) := by
      have h1 : Tendsto (fun w : E ↦ x₁ + w) (𝓝 0) (𝓝 x₁) := by
        simpa using (tendsto_const_nhds (x := x₁)).add (tendsto_id (x := 𝓝 (0 : E)))
      exact h1 (mem_interior_iff_mem_nhds.1 hx₁)
    refine ⟨balancedCore ℂ _, balancedCore_mem_nhds_zero hV, balancedCore.balanced _, M,
      Nat.cast_nonneg M, fun w hw ↦ ?_⟩
    refine le_of_tendsto ((hq.tendsto _).comp (hP w)) (Eventually.of_forall fun N ↦ ?_)
    exact (hQ N).seminorm_le_of_shift q (balancedCore.balanced _)
      (fun v hv ↦ (balancedCore_subset _ hv : v ∈ {w : E | x₁ + w ∈ S M}) N) hw
  -- Step 2: a smaller balanced neighbourhood and the size of `x₀`
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hW₀
  set W₁ := balancedCore ℂ V
  have hW₁ : W₁ ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hV
  have hW₁b : Balanced ℂ W₁ := balancedCore.balanced _
  have hW₁W₀ : ∀ a ∈ W₁, ∀ b ∈ W₁, a + b ∈ W₀ := fun a ha b hb ↦
    hVV a (balancedCore_subset _ ha) b (balancedCore_subset _ hb)
  obtain ⟨r, hr, hrW⟩ := (absorbent_nhds_zero (𝕜 := ℂ) hW₁ x₀).exists_pos
  set μ : ℝ := max r 1
  have hμ1 : 1 ≤ μ := le_max_right _ _
  have hμ0 : 0 < μ := by linarith
  obtain ⟨w₀, hw₀, hx₀⟩ := hrW (μ : ℂ) (by
    rw [Complex.norm_real, Real.norm_of_nonneg hμ0.le]; exact le_max_left _ _) (mem_singleton x₀)
  -- Step 3: the size of the neighbourhood of `x₀`
  set L : ℝ := μ ^ k * M
  have hL0 : 0 ≤ L := by positivity
  set δ : ℝ := min (μ / 2) (ε * μ / (4 * (L + 1)))
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδμ : δ ≤ μ / 2 := min_le_left _ _
  have hnhds : {x : E | x - x₀ ∈ (δ : ℂ) • W₁} ∈ 𝓝 x₀ := by
    have h1 : (δ : ℂ) • W₁ ∈ 𝓝 (0 : E) :=
      (set_smul_mem_nhds_zero_iff (by exact_mod_cast hδ0.ne')).2 hW₁
    exact (continuous_sub_right x₀).continuousAt.preimage_mem_nhds (by simpa using h1)
  filter_upwards [hnhds] with x hx
  obtain ⟨w₁, hw₁, hxw⟩ := hx
  -- Step 4: Cauchy estimates along the line `t ↦ x₀ + t (x - x₀)`
  set h : E := x - x₀
  set a : ℕ → F := fun j ↦ dirCoeff Atil x₀ j h
  have hline : ∀ t : ℂ, P (x₀ + t • h) = ∑ j ∈ range (k + 1), t ^ j • a j := fun t ↦ by
    rw [hdiag]; exact apply_add_smul_eq_sum Atil x₀ h t
  set ρ : ℝ := μ / δ
  have hρ : 0 < ρ := by positivity
  have hcircle : ∀ t : ℂ, ‖t‖ = ρ → q (∑ j ∈ range (k + 1), t ^ j • a j) ≤ L := by
    intro t ht
    rw [← hline]
    have hs : ‖t * δ / μ‖ = 1 := by
      rw [norm_div, norm_mul, ht, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hδ0.le, Real.norm_of_nonneg hμ0.le]
      simp only [ρ]; field_simp
    have hmem : w₀ + (t * δ / μ) • w₁ ∈ W₀ :=
      hW₁W₀ _ hw₀ _ (hW₁b.smul_mem hs.le hw₁)
    have e : x₀ + t • h = (μ : ℂ) • (w₀ + (t * δ / μ) • w₁) := by
      have hμc : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ0.ne'
      rw [smul_add, smul_smul, ← hx₀, ← hxw, smul_smul]
      congr 2
      field_simp
    rw [e, hPhom.map_smul, map_smul_eq_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hμ0.le]
    exact mul_le_mul_of_nonneg_left (hM _ hmem) (by positivity)
  have hcoef : ∀ j ≤ k, q (a j) ≤ L / ρ ^ j := fun j hj ↦
    seminorm_coeff_le_of_circle q a hρ hcircle hj
  -- Step 5: the estimate
  have hdiff : P x - P x₀ = ∑ j ∈ range k, a (j + 1) := by
    have h1 := hline 1
    have h0 := hline 0
    simp only [one_smul, one_pow, zero_smul, add_zero] at h1 h0
    rw [show x₀ + h = x by simp [h], Finset.sum_range_succ'] at h1
    rw [Finset.sum_range_succ', Finset.sum_eq_zero (fun j _ ↦ by simp)] at h0
    rw [h1, h0]
    simp
  set σ : ℝ := δ / μ
  have hσ0 : 0 ≤ σ := by positivity
  have hσ : σ ≤ 1 / 2 := by
    simp only [σ]; rw [div_le_iff₀ hμ0]; linarith
  have hσρ : ∀ j, L / ρ ^ (j + 1) = L * σ * σ ^ j := fun j ↦ by
    simp only [ρ, σ, div_pow, pow_succ]; field_simp
  calc q (P x - P x₀) = q (∑ j ∈ range k, a (j + 1)) := by rw [hdiff]
    _ ≤ ∑ j ∈ range k, q (a (j + 1)) :=
        Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _
    _ ≤ ∑ j ∈ range k, L * σ * σ ^ j := Finset.sum_le_sum fun j hj ↦ by
        rw [← hσρ]; exact hcoef (j + 1) (by have := Finset.mem_range.1 hj; omega)
    _ = L * σ * ∑ j ∈ range k, σ ^ j := by rw [Finset.mul_sum]
    _ ≤ L * σ * 2 := by
        gcongr
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hσ0 (by linarith)
        rw [← Finset.range_eq_Ico, pow_zero] at this
        calc ∑ j ∈ range k, σ ^ j ≤ 1 / (1 - σ) := this
          _ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    _ < ε := by
        have h1 : σ ≤ ε / (4 * (L + 1)) := by
          simp only [σ]
          rw [div_le_iff₀ hμ0]
          calc δ ≤ ε * μ / (4 * (L + 1)) := min_le_right _ _
            _ = ε / (4 * (L + 1)) * μ := by ring
        calc L * σ * 2 ≤ L * (ε / (4 * (L + 1))) * 2 := by gcongr
          _ < ε := by
              rw [mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
              nlinarith

end Limits

/-! ### [BS71b, Theorem 5.2] -/

section Theorem52

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℂ E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]
  (A : ∀ n, ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E) F) {H : Set E}

omit [ContinuousSMul ℂ F] in
/-- The coefficients along a line through a point of `H` are summable. -/
theorem hasSum_dirCoeff [Module ℝ F] [IsScalarTower ℝ ℂ F] [MackeyComplete F]
    (hH : IsOpen H)
    (hconv : ∀ a ∈ H, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 y))
    {x : E} (hx : x ∈ H) (y : E) (k : ℕ) :
    HasSum (fun n ↦ dirCoeff (A n).toMultilinearMap x k y)
      (∑' n, dirCoeff (A n).toMultilinearMap x k y) := by
  have hΩ : IsOpen {z : ℂ | x + z • y ∈ H} :=
    hH.preimage (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ 0 (by simpa using hx)
  have hsub : ∀ z ∈ closedBall (0 : ℂ) (ε / 2), x + z • y ∈ H := fun z hz ↦
    hball (closedBall_subset_ball (by linarith) hz)
  obtain ⟨θ, hθ0, hθ1, hθC⟩ := exists_dirCoeff_bound A hH hconv (half_pos hε) hsub
  obtain ⟨s, hs⟩ := MackeyComplete.exists_hasSum_of_geometric
      (v := fun n ↦ dirCoeff (A n).toMultilinearMap x k y) hθ0 hθ1 fun q hq ↦ by
    obtain ⟨C, -, hC⟩ := hθC q hq
    exact ⟨C / (ε / 2) ^ k, fun n ↦ (hC n k).trans_eq (by ring)⟩
  rwa [hs.tsum_eq]

/-- **Continuity of the sum** ([BS71b, proof of Theorem 5.2]): over a Baire space,
the sum of a series of continuous homogeneous polynomials converging on an open set `H` is
continuous on `H`, if `F` is Mackey complete. At `x ∈ H`, the Taylor coefficients
`h ↦ ∑ₙ dirCoeff (Aₙ) x k h` are continuous homogeneous polynomials
(`isContHomPoly_of_tendsto`), their series converges to `f (x + h)` near `h = 0`
(`hasPowerSeriesOnDisc_of_closedBall`), and `continuousAt_zero_of_tendsto_sum` applies. -/
theorem continuousOn_of_tendsto [BaireSpace E] [Module ℝ F] [IsScalarTower ℝ ℂ F]
    [MackeyComplete F] (hH : IsOpen H)
    {f : E → F} (hf : ∀ a ∈ H, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 (f a))) :
    ContinuousOn f H := by
  have hconv : ∀ a ∈ H, ∃ y, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 y) :=
    fun a ha ↦ ⟨f a, hf a ha⟩
  intro x hx
  set T : ℕ → E → F := fun k h ↦ ∑' n, dirCoeff (A n).toMultilinearMap x k h
  -- the Taylor coefficients at `x` are continuous homogeneous polynomials
  have hT : ∀ k, IsContHomPoly ℂ k (T k) := by
    intro k
    refine isContHomPoly_of_tendsto (Q := fun N h ↦ ∑ n ∈ range N,
      dirCoeff (A n).toMultilinearMap x k h) (fun N ↦ ?_)
      fun h ↦ (hasSum_dirCoeff A hH hconv hx h k).tendsto_sum_nat
    have e : (fun h ↦ ∑ n ∈ range N, dirCoeff (A n).toMultilinearMap x k h) =
        ∑ n ∈ range N, dirCoeff (A n).toMultilinearMap x k := by
      ext h; simp [Finset.sum_apply]
    obtain ⟨B, hB⟩ := IsHomPoly.sum (range N) fun n _ ↦ isHomPoly_dirCoeff
      (A n).toMultilinearMap x k
    refine isContHomPoly_iff_continuous.2 ⟨continuous_finsetSum _ fun n _ ↦
      continuous_dirCoeff (A n) x k, B, ?_⟩
    rw [e]
    exact funext hB
  -- the Taylor series at `x` converges near `0`
  have hV : {h : E | x + h ∈ H} ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
      (by simpa using hH.mem_nhds hx)
  set W := balancedCore ℂ {h : E | x + h ∈ H}
  have hW : W ∈ 𝓝 (0 : E) := balancedCore_mem_nhds_zero hV
  have hU : (1 / 2 : ℂ) • W ∈ 𝓝 (0 : E) :=
    (set_smul_mem_nhds_zero_iff (by norm_num)).2 hW
  have hexp : ∀ h ∈ (1 / 2 : ℂ) • W,
      Tendsto (fun K ↦ ∑ k ∈ range K, T k h) atTop (𝓝 (f (x + h))) := by
    rintro _ ⟨w, hw, rfl⟩
    have hsub : ∀ z ∈ closedBall (0 : ℂ) 2, x + z • ((1 / 2 : ℂ) • w) ∈ H := by
      intro z hz
      rw [mem_closedBall, dist_zero_right] at hz
      have : (z * (1 / 2)) • w ∈ W := (balancedCore.balanced _).smul_mem
        (by rw [norm_mul]; norm_num; linarith) hw
      rw [smul_smul]
      exact (balancedCore_subset _ this : (z * (1 / 2)) • w ∈ {h : E | x + h ∈ H})
    have hps := hasPowerSeriesOnDisc_of_closedBall A hH hf (by norm_num) hsub 1 (by norm_num)
    simp only [one_pow, one_smul, zero_add] at hps
    exact hps.tendsto_sum_nat
  have hc := continuousAt_zero_of_tendsto_sum hT hU (f := fun h ↦ f (x + h)) hexp
  have := hc.comp_of_eq (continuous_sub_right x).continuousAt (sub_self x)
  simpa [Function.comp_def] using this.continuousWithinAt

end Theorem52

/-! ### The main theorem -/

section Main

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]
  [T2Space E] {F : Type*} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [LocallyConvexSpace ℝ F]
  [T2Space F]

attribute [local instance] polynormableSpace_complex

/-- **[BS71b, Theorem 5.2]** (complex case). Let `E` be a complex locally convex
**Baire** space and `F` a **Mackey complete** complex locally convex space (e.g. a sequentially
complete one, `SeqComplete.mackeyComplete`). If a series `∑ pₙ` of continuous homogeneous
polynomials converges on an open set `H ⊆ E`, then its sum is complex analytic on `H`.

Both hypotheses are needed: `not_continuousAt_bsSum` (with `E` not Baire) and
`not_cAnalyticOn_geomFun` with `not_mackeyComplete_geomSpan` (with `F` not Mackey complete,
already for `E = ℂ`). Bochnak and Siciak assume `F` sequentially complete; Mackey completeness
suffices because the geometric bounds along lines have a ratio independent of the seminorm
(`exists_line_geometric_bound`). The proof replaces their potential-theoretic polynomial lemma by
Hartogs' lemma (`hartogs_lemma`), proved from Jensen's formula. -/
theorem complexAnalyticOn_of_tendsto_sum [BaireSpace E] [MackeyComplete F]
    {p : ℕ → E → F} (hp : ∀ n, IsContHomPoly ℂ n (p n)) {H : Set E} (hH : IsOpen H)
    {f : E → F} (hf : ∀ x ∈ H, Tendsto (fun N ↦ ∑ n ∈ range N, p n x) atTop (𝓝 (f x))) :
    ComplexAnalyticOn f H := by
  choose A hA using hp
  have hf' : ∀ a ∈ H, Tendsto (fun N ↦ ∑ n ∈ range N, A n fun _ ↦ a) atTop (𝓝 (f a)) :=
    fun a ha ↦ by simpa only [hA] using hf a ha
  exact (complexAnalyticOn_iff_gateauxAnalyticOn hH).2
    ⟨continuousOn_of_tendsto A hH hf', gateauxAnalyticOn_of_tendsto A hH hf'⟩

end Main

end LocallyConvex.Analysis

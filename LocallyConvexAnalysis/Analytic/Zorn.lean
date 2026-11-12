/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Analytic.SeparateAnalyticity

/-! # Zorn's theorem for one seminorm, and Hartogs' theorem on products

Zorn's theorem: a Gâteaux analytic map on a Baire space which is bounded near one point is
bounded near the points of a neighbourhood. We prove it for each continuous seminorm `q` of the
target separately, without completeness (`exists_nhds_seminorm_bound_of_near`), and deduce
Hartogs' theorem for separately analytic maps on products `E₁ × E₂` of locally convex spaces
(`complexAnalyticOn_of_separately_prod`), following Mujica, *Complex Analysis in Banach Spaces*,
North-Holland Math. Studies 120 (1986), Lemma 36.2, Lemma 36.6, Proposition 36.7, Theorems 36.5
and 36.8 (Banach spaces).

## Main results

* `taylorCoeff f y k h`: the coefficient of `λᵏ` in `λ ↦ f (y + λ h)`; it is homogeneous
  (`taylorCoeff_smul`).
* `planeFun_line_identity`, `planeFun_hasSum_shift`: on a complex plane, the Taylor coefficients
  are given by the double Taylor coefficients of Osgood's lemma (the plane is handled through
  `continuousOn_of_separately`, Hartogs' theorem in `ℂ²`).
* `seminorm_taylorCoeff_sub_le`, `qCont_taylorCoeff`: Taylor coefficients bounded on a ball are
  `q`-continuous; `seminorm_taylorCoeff_le_of_shift`: the shift lemma.
* `exists_nhds_seminorm_bound`: Baire's theorem for a family of `q`-continuous maps.
* `exists_taylorCoeff_ball_bound`, `exists_nhds_seminorm_bound_of_near`: **Zorn's theorem for
  one seminorm**.
* `exists_near_seminorm_bound`: [Muj86, Lemma 36.2] for one seminorm.
* `locallyBoundedOn_of_separately`, `complexAnalyticOn_of_separately_prod`: **Hartogs' theorem
  on products**, for `E₁`, `E₁ × E₂` Baire, `E₂` first countable and `F` Mackey complete.

## Implementation notes

* The Taylor coefficients of a Gâteaux analytic map are not shown to be homogeneous polynomials
  in the algebraic sense ([Muj86, Theorem 36.4], needs polynomials on finite dimensional
  subspaces). Everything is done on complex planes, where `λ ↦ ℓ (T_y(m, h + λ v))` is a
  polynomial of degree `≤ m`: this suffices for continuity estimates and for the averaging over
  roots of unity of the shift lemma.
* [Muj86, Lemma 36.6] expands the Taylor polynomials at a point `c` through those at a nearby
  point `x`. Here `T_c(k, t)` is the weak limit of the `q`-continuous maps
  `∑_{m < N} Q_m(t)`, where `Q_m(t)` extracts the coefficient of `λᵏ` of `T_x(m, e + λ t)` by
  roots of unity; only bounds pass through the limit, so no completeness is needed.
* Completeness (Mackey) enters only through Gâteaux analyticity of separately analytic maps
  (`gateauxAnalyticOn_of_separately`), where it is necessary (`not_complexAnalyticOn_sepG`).

## References

* [J. Bochnak, J. Siciak, *Polynomials and multilinear mappings in topological
  vector-spaces*][BS71a]
* [J. Mujica, *Complex Analysis in Banach Spaces*][Muj86]
-/

@[expose] public section

open Set Filter Function Metric
open scoped Topology Real

noncomputable section

namespace LocallyConvex.Analysis

universe u v

section Taylor

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
  {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]
  {f : E → F} {U : Set E}

/-- The `k`-th Taylor coefficient of `f` at `y` along the direction `h`: the coefficient of `λᵏ`
in `λ ↦ f (y + λ h)`. -/
def taylorCoeff (f : E → F) (y : E) (k : ℕ) (h : E) : F :=
  (k.factorial : ℂ)⁻¹ • cDeriv^[k] (fun l : ℂ ↦ f (y + l • h)) 0

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
omit [TopologicalSpace E] in
/-- Taylor expansion along a line. -/
theorem hasPowerSeriesOnDisc_taylorCoeff (hG : GateauxAnalyticOn f U) {y h : E} {R : ℝ}
    (hR : 0 < R) (hsub : ∀ l : ℂ, ‖l‖ ≤ R → y + l • h ∈ U) :
    HasPowerSeriesOnDisc (fun l : ℂ ↦ f (y + l • h)) (fun k ↦ taylorCoeff f y k h) 0 R :=
  (hG.cAnalyticOn_line y h).hasPowerSeriesOnDisc hR fun l hl ↦
    hsub l (by simpa using hl)

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
omit [TopologicalSpace E] in
/-- Homogeneity: `T(μ h) = μᵏ T(h)` for `|μ| ≤ 1`. -/
theorem taylorCoeff_smul (hG : GateauxAnalyticOn f U) {y h : E} {R : ℝ} (hR : 0 < R)
    (hsub : ∀ l : ℂ, ‖l‖ ≤ R → y + l • h ∈ U) {μ : ℂ} (hμ : ‖μ‖ ≤ 1) (k : ℕ) :
    taylorCoeff f y k (μ • h) = μ ^ k • taylorCoeff f y k h := by
  have h0 := hasPowerSeriesOnDisc_taylorCoeff hG hR hsub
  have hsubμ : ∀ l : ℂ, ‖l‖ ≤ R → y + l • (μ • h) ∈ U := fun l hl ↦ by
    rw [smul_smul]
    exact hsub _ (by rw [norm_mul]; nlinarith [norm_nonneg l, norm_nonneg μ])
  have h1 := hasPowerSeriesOnDisc_taylorCoeff hG hR hsubμ
  have h2 : HasPowerSeriesOnDisc (fun l : ℂ ↦ f (y + l • (μ • h)))
      (fun k ↦ μ ^ k • taylorCoeff f y k h) 0 R := by
    intro z hz
    have hzμ : ‖z * μ‖ < R := by
      rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg μ]
    have := h0 (z * μ) hzμ
    simp only [zero_add, smul_smul, mul_pow] at this ⊢
    exact this
  exact congrFun (h1.coeff_unique h2 hR hR) k

/-! ### Complex planes -/

/-- On a closed bidisc of a complex plane in `U`, `q ∘ f` is bounded: the restriction of `f` to the
plane is separately analytic, hence continuous (`continuousOn_of_separately`). -/
theorem exists_complexPlane_bound (hU : IsOpen U) (hG : GateauxAnalyticOn f U) {y h v : E} {R : ℝ}
    (hbox : ∀ ζ σ : ℂ, ‖ζ‖ ≤ R → ‖σ‖ ≤ R → y + ζ • h + σ • v ∈ U) {q : Seminorm ℂ F}
    (hq : Continuous q) :
    ∃ M, ∀ ζ σ : ℂ, ‖ζ‖ ≤ R → ‖σ‖ ≤ R → q (f (y + ζ • h + σ • v)) ≤ M := by
  set g : ℂ → ℂ → F := fun ζ σ ↦ f (y + ζ • h + σ • v)
  set W : Set (ℂ × ℂ) := {z | y + z.1 • h + z.2 • v ∈ U}
  have hc : Continuous fun z : ℂ × ℂ ↦ y + z.1 • h + z.2 • v :=
    (continuous_const.add (continuous_fst.smul continuous_const)).add
      (continuous_snd.smul continuous_const)
  have hW : IsOpen W := hU.preimage hc
  have h₁ : ∀ σ, CAnalyticOn (fun ζ ↦ g ζ σ) {ζ | (ζ, σ) ∈ W} := fun σ ↦ by
    have := hG.cAnalyticOn_line (y + σ • v) h
    convert this using 1
    · funext ζ; simp only [g]; congr 1; abel
    · ext ζ; simp only [W, mem_ofPred_eq]; constructor <;> intro hz <;> convert hz using 1 <;> abel
  have h₂ : ∀ ζ, CAnalyticOn (g ζ) {σ | (ζ, σ) ∈ W} := fun ζ ↦ hG.cAnalyticOn_line (y + ζ • h) v
  have hcont := continuousOn_of_separately hW h₁ h₂
  have hK : closedBall (0 : ℂ) R ×ˢ closedBall (0 : ℂ) R ⊆ W := fun z hz ↦
    hbox z.1 z.2 (by simpa using hz.1) (by simpa using hz.2)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall 0 R).prod (isCompact_closedBall 0 R))
    |>.exists_bound_of_continuousOn (hq.comp_continuousOn (hcont.mono hK))
  exact ⟨M, fun ζ σ hζ hσ ↦ (le_abs_self _).trans
    (hM (ζ, σ) ⟨by simpa using hζ, by simpa using hσ⟩)⟩

variable (f) in
/-- The scalar function of two variables on a complex plane. -/
def planeFun (ℓ : F →L[ℂ] ℂ) (y h v : E) : ℂ → ℂ → ℂ := fun ζ σ ↦ ℓ (f (y + ζ • h + σ • v))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [TopologicalSpace E] in
theorem osgoodHyp_planeFun (hG : GateauxAnalyticOn f U) {y h v : E}
    (hbox : ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → y + ζ • h + σ • v ∈ U) {q : Seminorm ℂ F} {M : ℝ}
    (hM : ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → q (f (y + ζ • h + σ • v)) ≤ M) (ℓ : F →L[ℂ] ℂ)
    (hℓ : ∀ w, ‖ℓ w‖ ≤ q w) : OsgoodHyp (planeFun f ℓ y h v) 3 M := by
  refine ⟨by norm_num, fun ζ hζ ↦ ?_, fun σ hσ ↦ ?_, fun ζ hζ σ hσ ↦ ?_⟩
  · refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball 0 (by norm_num)]
    exact ((hG.cAnalyticOn_line (y + ζ • h) v).differentiableOn_clm ℓ).mono fun σ hσ ↦
      hbox ζ σ (by simpa using hζ) (by simpa using hσ)
  · have := ((hG.cAnalyticOn_line (y + σ • v) h).differentiableOn_clm ℓ).mono
      (show ball (0 : ℂ) 3 ⊆ {ζ | y + σ • v + ζ • h ∈ U} from fun ζ hζ ↦ by
        have := hbox ζ σ (by simpa using (mem_ball_zero_iff.1 hζ).le)
          (by simpa using (mem_ball_zero_iff.1 hσ).le)
        simp only [mem_ofPred_eq]; convert this using 1; abel)
    refine this.congr fun ζ _ ↦ ?_
    simp only [planeFun, Function.comp]; congr 2; abel
  · exact (hℓ _).trans (hM ζ σ (by simpa using hζ)
      (by simpa using (mem_sphere_zero_iff_norm.1 hσ).le))

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
omit [TopologicalSpace E] in
/-- **The Taylor coefficients on a complex plane**: for `|λ| ≤ 1`,
`ℓ (T_y(m, h + λ v)) = ∑_{a + b = m} c_{a b} λᵃ`, where `c` are the double Taylor coefficients of
`(ζ, σ) ↦ ℓ (f (y + ζ h + σ v))`. -/
theorem planeFun_line_identity (hG : GateauxAnalyticOn f U) {y h v : E}
    (hbox : ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → y + ζ • h + σ • v ∈ U) {q : Seminorm ℂ F} {M : ℝ}
    (hM : ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → q (f (y + ζ • h + σ • v)) ≤ M) (ℓ : F →L[ℂ] ℂ)
    (hℓ : ∀ w, ‖ℓ w‖ ≤ q w) (m : ℕ) {l : ℂ} (hl : ‖l‖ ≤ 1) :
    ℓ (taylorCoeff f y m (h + l • v)) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      osgoodCoeff₂ (planeFun f ℓ y h v) p.1 p.2 * l ^ p.1 := by
  have hO := osgoodHyp_planeFun hG hbox hM ℓ hℓ
  have hdom : ∀ t : ℂ, ‖t‖ ≤ 3 / 2 → y + t • (h + l • v) ∈ U := fun t ht ↦ by
    have := hbox t (t * l) (by linarith) (by rw [norm_mul]; nlinarith [norm_nonneg t])
    rw [smul_add, smul_smul, ← add_assoc]
    convert this using 2
  have hP := hasPowerSeriesOnDisc_taylorCoeff hG (by norm_num) hdom
  set φ : ℂ → ℂ := fun t ↦ ℓ (f (y + t • (h + l • v)))
  have h1 := coeff_eq_iteratedDeriv_of_hasSum (g := φ) (x := 0)
    (c := fun m ↦ ℓ (taylorCoeff f y m (h + l • v))) (r := 3 / 2) (by norm_num) (fun t ht ↦ by
      have := (hP t ht).map ℓ ℓ.continuous
      simpa [φ, Function.comp_def] using this) m
  have h2 := coeff_eq_iteratedDeriv_of_hasSum (g := φ) (x := 0)
    (c := fun m ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      osgoodCoeff₂ (planeFun f ℓ y h v) p.1 p.2 * l ^ p.1) (r := 3 / 2) (by norm_num)
    (fun t ht ↦ by
      have := hO.hasSum_line hl (t := t) (by simpa using ht)
      have e : planeFun f ℓ y h v t (l * t) = φ (0 + t) := by
        simp only [planeFun, φ, zero_add, smul_add, smul_smul, ← add_assoc, mul_comm l t]
      rw [← e]
      simpa [smul_eq_mul] using this) m
  simpa using h1.trans h2.symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
omit [TopologicalSpace E] in
/-- The coefficients of the expansion at `y + h` in the direction `v` are the sums of the double
coefficients: `ℓ (T_{y+h}(k, v)) = ∑_b c_{k b}`. -/
theorem planeFun_hasSum_shift (hG : GateauxAnalyticOn f U) {y h v : E}
    (hbox : ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → y + ζ • h + σ • v ∈ U) {q : Seminorm ℂ F} {M : ℝ}
    (hM : ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → q (f (y + ζ • h + σ • v)) ≤ M) (ℓ : F →L[ℂ] ℂ)
    (hℓ : ∀ w, ‖ℓ w‖ ≤ q w) (k : ℕ) :
    HasSum (fun b ↦ osgoodCoeff₂ (planeFun f ℓ y h v) k b) (ℓ (taylorCoeff f (y + h) k v)) := by
  have hO := osgoodHyp_planeFun hG hbox hM ℓ hℓ
  have hk := hO.hasSum_coeff₂ k (ζ := 1) (by norm_num)
  simp only [one_pow, one_mul] at hk
  have hdom : ∀ σ : ℂ, ‖σ‖ ≤ 3 → y + h + σ • v ∈ U := fun σ hσ ↦ by
    simpa using hbox 1 σ (by norm_num) hσ
  have hP := hasPowerSeriesOnDisc_taylorCoeff hG (by norm_num) hdom
  have e : osgoodCoeff (planeFun f ℓ y h v) k 1 = ℓ (taylorCoeff f (y + h) k v) := by
    rw [hP.clm_apply (by norm_num) ℓ k, osgoodCoeff]
    congr 2
    funext σ
    simp [planeFun, Function.comp]
  rwa [e] at hk

/-! ### Extraction of coefficients of a polynomial on the unit circle -/

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
/-- For `P(λ) = ∑_{a + b = m} c_{a b} λᵃ` and `a ≤ m`, the average of `ω^{j(m + 1 - a)} P(ωʲ)`
over the `(m+1)`-th roots of unity is `c_{a, m - a}`. -/
theorem avg_antidiagonal (m a : ℕ) (ha : a ≤ m) (c : ℕ → ℕ → ℂ) :
    ((m + 1 : ℕ) : ℂ)⁻¹ * ∑ j ∈ Finset.range (m + 1), (rootN (m + 1) ^ j) ^ (m + 1 - a) *
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 p.2 * (rootN (m + 1) ^ j) ^ p.1 =
      c a (m - a) := by
  have hrw : ∀ j, (rootN (m + 1) ^ j) ^ (m + 1 - a) *
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 p.2 * (rootN (m + 1) ^ j) ^ p.1 =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        c p.1 p.2 * (rootN (m + 1) ^ j) ^ (m + 1 - a + p.1) := fun j ↦ by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [pow_add]; ring
  simp only [hrw]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp only [← Finset.mul_sum]
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal m,
      ((m + 1 : ℕ) : ℂ)⁻¹ * (c p.1 p.2 * ∑ j ∈ Finset.range (m + 1),
        (rootN (m + 1) ^ j) ^ (m + 1 - a + p.1)) = if p = (a, m - a) then c a (m - a) else 0 := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [mul_left_comm, avg_rootN_pow (m + 1) (by omega)]
    by_cases hpa : p = (a, m - a)
    · subst hpa
      have hd : m + 1 ∣ m + 1 - a + a := by rw [Nat.sub_add_cancel (by omega)]
      simp [hd]
    · have hp1 : p.1 ≠ a := fun h ↦ hpa (Prod.ext h (by simp; omega))
      have hnd : ¬ (m + 1 ∣ m + 1 - a + p.1) := by
        rintro ⟨d, hd⟩
        rcases d with _ | _ | d
        · omega
        · omega
        · have : (m + 1) * (d + 1 + 1) = (m + 1) * d + 2 * (m + 1) := by ring
          omega
      simp [hpa, hnd]
  rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp [Finset.HasAntidiagonal.mem_antidiagonal, ha]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
/-- If `|∑_{a + b = m} c_{a b} λᵃ| ≤ n` on the unit circle, then `|c_{a b}| ≤ n`, and the
polynomial moves by at most `(m + 1) n |λ|` from its value at `0` on the closed unit disc. -/
theorem norm_antidiagonal_sub_le {m : ℕ} {c : ℕ → ℕ → ℂ} {n : ℝ}
    (hb : ∀ l : ℂ, ‖l‖ = 1 →
      ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 p.2 * l ^ p.1‖ ≤ n)
    {l : ℂ} (hl : ‖l‖ ≤ 1) :
    ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 p.2 * l ^ p.1 -
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 p.2 * (0 : ℂ) ^ p.1‖ ≤
      (m + 1) * n * ‖l‖ := by
  have hω0 : ‖rootN (m + 1)‖ = 1 :=
    (Complex.isPrimitiveRoot_exp (m + 1) (by omega)).norm'_eq_one (by omega)
  have hω : ∀ j, ‖rootN (m + 1) ^ j‖ = 1 := fun j ↦ by rw [norm_pow, hω0, one_pow]
  have hc : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal m, ‖c p.1 p.2‖ ≤ n := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have e := avg_antidiagonal m p.1 (by omega) c
    rw [show m - p.1 = p.2 by omega] at e
    rw [← e, norm_mul, norm_inv, Complex.norm_natCast]
    calc ((m + 1 : ℕ) : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (m + 1), (rootN (m + 1) ^ j) ^ (m + 1 - p.1) *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 p.2 * (rootN (m + 1) ^ j) ^ p.1‖
        ≤ ((m + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (m + 1), n := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
          rw [norm_mul, norm_pow, hω, one_pow, one_mul]
          exact hb _ (hω j)
      _ = n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
  have hn : 0 ≤ n := (norm_nonneg _).trans (hb 1 (by simp))
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
        (c p.1 p.2 * l ^ p.1 - c p.1 p.2 * (0 : ℂ) ^ p.1)‖
      ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, n * ‖l‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
        rw [← mul_sub, norm_mul]
        rcases Nat.eq_zero_or_pos p.1 with h0 | h0
        · rw [h0, pow_zero, pow_zero, sub_self, norm_zero, mul_zero]; positivity
        · rw [zero_pow h0.ne', sub_zero, norm_pow]
          refine mul_le_mul (hc p hp) ?_ (by positivity) hn
          calc ‖l‖ ^ p.1 ≤ ‖l‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hl h0
            _ = ‖l‖ := pow_one _
    _ = (m + 1) * n * ‖l‖ := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast; ring

/-! ### Seminorm balls -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
theorem lineDom_of_ball {y : E} {N : Seminorm ℂ E} {ρ : ℝ} (hy : ∀ z, N z < 8 * ρ → y + z ∈ U)
    {h : E} (hh : N h < ρ) : ∀ l : ℂ, ‖l‖ ≤ 3 → y + l • h ∈ U := fun l hl ↦
  hy _ (by rw [map_smul_eq_mul]; nlinarith [norm_nonneg l, apply_nonneg N h])

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
theorem planeDom_of_ball {y : E} {N : Seminorm ℂ E} {ρ : ℝ} (hy : ∀ z, N z < 8 * ρ → y + z ∈ U)
    {h v : E} (hh : N h < ρ) (hv : N v < ρ) :
    ∀ ζ σ : ℂ, ‖ζ‖ ≤ 3 → ‖σ‖ ≤ 3 → y + ζ • h + σ • v ∈ U := fun ζ σ hζ hσ ↦ by
  rw [add_assoc]
  refine hy _ ((map_add_le_add N _ _).trans_lt ?_)
  rw [map_smul_eq_mul, map_smul_eq_mul]
  nlinarith [norm_nonneg ζ, norm_nonneg σ, apply_nonneg N h, apply_nonneg N v]

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F] in
/-- Every line through `y` meets `U` in a disc about `0`. -/
theorem exists_lineDom {y : E} {N : Seminorm ℂ E} {ρ : ℝ} (hρ : 0 < ρ)
    (hy : ∀ z, N z < 8 * ρ → y + z ∈ U) (h : E) :
    ∃ R > 0, ∀ l : ℂ, ‖l‖ ≤ R → y + l • h ∈ U := by
  refine ⟨ρ / (N h + 1), by positivity, fun l hl ↦ hy _ ?_⟩
  rw [map_smul_eq_mul]
  have h1 : N h + 1 > 0 := by positivity
  calc ‖l‖ * N h ≤ ρ / (N h + 1) * N h := by gcongr
    _ < ρ := by rw [div_mul_eq_mul_div, div_lt_iff₀ h1]; nlinarith [apply_nonneg N h]
    _ ≤ 8 * ρ := by linarith

/-- **Taylor coefficients bounded on a ball move little.** If `q (T_y(m, w)) ≤ n` for `N' w < r`,
then `q (T_y(m, h + λ v) - T_y(m, h)) ≤ (m + 1) n |λ|` for `N' h, N' v < r/2` and `|λ| ≤ 1`
(the coefficients of the polynomial `λ ↦ ℓ (T_y(m, h + λ v))` are bounded by `n`). Here `N`
controls the domain and `N' ≥ N` the ball. -/
theorem seminorm_taylorCoeff_sub_le (hU : IsOpen U) (hG : GateauxAnalyticOn f U) {y : E}
    {N N' : Seminorm ℂ E} (hNN' : ∀ z, N z ≤ N' z) {ρ r : ℝ} (hr : r ≤ ρ)
    (hy : ∀ z, N z < 8 * ρ → y + z ∈ U) {q : Seminorm ℂ F}
    (hq : Continuous q) {m : ℕ} {n : ℝ} (hb : ∀ w, N' w < r → q (taylorCoeff f y m w) ≤ n)
    {h v : E} (hh : N' h < r / 2) (hv : N' v < r / 2) {l : ℂ} (hl : ‖l‖ ≤ 1) :
    q (taylorCoeff f y m (h + l • v) - taylorCoeff f y m h) ≤ (m + 1) * n * ‖l‖ := by
  have h0r : 0 ≤ N' h := apply_nonneg N' h
  have hbox := planeDom_of_ball hy (h := h) (v := v) (by linarith [hNN' h])
    (by linarith [hNN' v])
  obtain ⟨M, hM⟩ := exists_complexPlane_bound hU hG hbox hq (R := 3)
  refine seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_
  have hid := fun l' (hl' : ‖l'‖ ≤ 1) ↦ planeFun_line_identity hG hbox hM ℓ hℓ m hl'
  have h0 := hid 0 (by simp)
  rw [zero_smul, add_zero] at h0
  rw [map_sub, hid l hl, h0]
  refine norm_antidiagonal_sub_le (fun l' hl' ↦ ?_) hl
  rw [← hid l' hl'.le]
  refine (hℓ _).trans (hb _ ((map_add_le_add N' _ _).trans_lt ?_))
  rw [map_smul_eq_mul, hl', one_mul]; linarith

/-- **Shift lemma** (compare [BS71a, Lemma 2]): if `q (T_y(k, t₀ + v)) ≤ n` for
`N v < r`, then `q (T_y(k, v)) ≤ n` for `N v < r`; average over the `(k+1)`-th roots of unity
along the plane spanned by `v` and `t₀`. -/
theorem seminorm_taylorCoeff_le_of_shift (hU : IsOpen U) (hG : GateauxAnalyticOn f U) {y : E}
    {N N' : Seminorm ℂ E} (hNN' : ∀ z, N z ≤ N' z) {ρ : ℝ} (hρ : 0 < ρ)
    (hy : ∀ z, N z < 8 * ρ → y + z ∈ U)
    {q : Seminorm ℂ F} (hq : Continuous q) {k : ℕ} {t₀ : E} (ht₀ : N t₀ < ρ / 2) {r : ℝ}
    (hr : r ≤ ρ / 2) {n : ℝ} (hb : ∀ v, N' v < r → q (taylorCoeff f y k (t₀ + v)) ≤ n) {v : E}
    (hv : N' v < r) : q (taylorCoeff f y k v) ≤ n := by
  have hbox := planeDom_of_ball hy (h := v) (v := t₀) (by linarith [hNN' v]) (by linarith)
  obtain ⟨M, hM⟩ := exists_complexPlane_bound hU hG hbox hq (R := 3)
  refine seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_
  set c := osgoodCoeff₂ (planeFun f ℓ y v t₀)
  have hid := fun l' (hl' : ‖l'‖ ≤ 1) ↦ planeFun_line_identity hG hbox hM ℓ hℓ k hl'
  set ω := rootN (k + 1)
  have hω0 : ‖ω‖ = 1 := (Complex.isPrimitiveRoot_exp (k + 1) (by omega)).norm'_eq_one (by omega)
  have hωj : ∀ j : ℕ, ‖ω ^ j‖ = 1 := fun j ↦ by rw [norm_pow, hω0, one_pow]
  have hωne : ∀ j : ℕ, ω ^ j ≠ 0 := fun j h0 ↦ by simpa [h0] using hωj j
  -- the value at `0` is the average over the roots of unity
  have h0 := hid 0 (by simp)
  rw [zero_smul, add_zero] at h0
  have havg := avg_antidiagonal k 0 (Nat.zero_le _) c
  have hc0 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 p.2 * (0 : ℂ) ^ p.1 =
      c 0 (k - 0) := by
    rw [Finset.sum_eq_single (0, k)]
    · simp
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have : p.1 ≠ 0 := fun h ↦ hne (Prod.ext h (by simp; omega))
      simp [zero_pow this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  rw [h0, hc0, ← havg]
  have hterm : ∀ j : ℕ, ‖(ω ^ j) ^ (k + 1 - 0) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      c p.1 p.2 * (ω ^ j) ^ p.1‖ ≤ n := by
    intro j
    rw [← hid _ (hωj j).le, norm_mul, norm_pow, hωj, one_pow, one_mul]
    -- `v + ωʲ t₀ = ωʲ (t₀ + ω⁻ʲ v)`
    have e : v + ω ^ j • t₀ = ω ^ j • (t₀ + (ω ^ j)⁻¹ • v) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ (hωne j), one_smul, add_comm]
    obtain ⟨R, hR, hRdom⟩ := exists_lineDom hρ hy (t₀ + (ω ^ j)⁻¹ • v)
    rw [e, taylorCoeff_smul hG hR hRdom (hωj j).le, map_smul, norm_smul, norm_pow, hωj,
      one_pow, one_mul]
    refine (hℓ _).trans (hb _ ?_)
    rw [map_smul_eq_mul, norm_inv, hωj, inv_one, one_mul]; exact hv
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc ((k + 1 : ℕ) : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (k + 1), (ω ^ j) ^ (k + 1 - 0) *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, c p.1 p.2 * (ω ^ j) ^ p.1‖
      ≤ ((k + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (k + 1), n := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hterm j)
    _ = n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

end Taylor

/-! ### Continuity for one seminorm -/

section QCont

variable {F : Type v} [AddCommGroup F] [Module ℂ F]

/-- `φ` is continuous for the seminorm `q`. -/
def QCont (q : Seminorm ℂ F) {X : Type*} [TopologicalSpace X] (φ : X → F) : Prop :=
  ∀ x, Tendsto (fun x' ↦ q (φ x' - φ x)) (𝓝 x) (𝓝 0)

variable {q : Seminorm ℂ F} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem QCont.continuous {φ : X → F} (h : QCont q φ) : Continuous fun x ↦ q (φ x) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h x)
    (fun _ ↦ norm_nonneg _) fun x' ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_sub_map_le_sub q _ _

theorem QCont.comp {φ : X → F} (h : QCont q φ) {g : Y → X} (hg : Continuous g) :
    QCont q (φ ∘ g) := fun y ↦ (h (g y)).comp (hg.tendsto y)

theorem QCont.sum {ι : Type*} (s : Finset ι) {φ : ι → X → F} (a : ι → ℂ)
    (h : ∀ i ∈ s, QCont q (φ i)) : QCont q fun x ↦ ∑ i ∈ s, a i • φ i x := by
  intro x
  have hlim : Tendsto (fun x' ↦ ∑ i ∈ s, ‖a i‖ * q (φ i x' - φ i x)) (𝓝 x) (𝓝 0) := by
    simpa using tendsto_finsetSum s fun i hi ↦ (h i hi x).const_mul ‖a i‖
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ apply_nonneg _ _) fun x' ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine (Finset.le_sum_of_subadditive q (map_zero q).le (map_add_le_add q) _ _).trans
    (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [← smul_sub, map_smul_eq_mul]

theorem QCont.const_smul {φ : X → F} (h : QCont q φ) (a : ℂ) : QCont q fun x ↦ a • φ x := by
  simpa using QCont.sum (s := {()}) (φ := fun _ ↦ φ) (fun _ ↦ a) fun _ _ ↦ h

end QCont

/-! ### Baire's theorem for one seminorm -/

section Baire

variable {E : Type u} [TopologicalSpace E] [BaireSpace E]
  {F : Type v} [AddCommGroup F] [Module ℂ F]

/-- **Baire's theorem for a family of `q`-continuous maps** (compare [Muj86, Lemma 2.7]): if
`(q (φᵢ t))ᵢ` is bounded at each point of a nonempty open set `O`, it is bounded uniformly on a
neighbourhood of some point of `O`. -/
theorem exists_nhds_seminorm_bound {O : Set E} (hO : IsOpen O) (hne : O.Nonempty)
    {q : Seminorm ℂ F} {φ : ℕ → E → F} (hc : ∀ i, Continuous fun t ↦ q (φ i t))
    (hpt : ∀ t ∈ O, ∃ C, ∀ i, q (φ i t) ≤ C) :
    ∃ t₀ ∈ O, ∃ W ∈ 𝓝 t₀, W ⊆ O ∧ ∃ n : ℝ, ∀ t ∈ W, ∀ i, q (φ i t) ≤ n := by
  have : BaireSpace O := hO.baireSpace
  have : Nonempty O := hne.to_subtype
  set A : ℕ → Set O := fun m ↦ {t | ∀ i, q (φ i t) ≤ m}
  have hA : ∀ m, IsClosed (A m) := by
    intro m
    have : A m = ⋂ i, (fun t : O ↦ q (φ i t)) ⁻¹' Iic (m : ℝ) := by ext; simp [A]
    rw [this]
    exact isClosed_iInter fun i ↦ isClosed_Iic.preimage ((hc i).comp continuous_subtype_val)
  have hcov : ⋃ m, A m = univ := by
    refine eq_univ_of_forall fun t ↦ mem_iUnion.2 ?_
    obtain ⟨C, hC⟩ := hpt t t.2
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨m, fun i ↦ (hC i).trans hm⟩
  obtain ⟨m, t₀, ht₀⟩ := nonempty_interior_of_iUnion_of_closed hA hcov
  have hW : IsOpen ((↑) '' interior (A m) : Set E) := hO.isOpenMap_subtype_val _ isOpen_interior
  refine ⟨t₀, t₀.2, _, hW.mem_nhds (mem_image_of_mem _ ht₀), ?_, m, ?_⟩
  · rintro _ ⟨t, -, rfl⟩; exact t.2
  · rintro _ ⟨t, ht, rfl⟩ i
    exact interior_subset ht i

end Baire

/-! ### Zorn's theorem for one seminorm -/

section Zorn

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
  {F : Type v} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℂ F] [PolynormableSpace ℂ F] [T2Space F]
  {f : E → F} {U : Set E}

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] in
/-- A neighbourhood of `t` contains a ball for a seminorm `N' ≥ N` whose balls are
neighbourhoods. -/
theorem exists_seminorm_ball_subset {N : Seminorm ℂ E} (hN : ∀ ε > 0, N.ball 0 ε ∈ 𝓝 (0 : E))
    {t : E} {W : Set E} (hW : W ∈ 𝓝 t) :
    ∃ N' : Seminorm ℂ E, (∀ z, N z ≤ N' z) ∧ (∀ ε > 0, N'.ball 0 ε ∈ 𝓝 (0 : E)) ∧
      ∃ r > 0, ∀ z, N' z < r → t + z ∈ W := by
  obtain ⟨s, r, hr, hsub⟩ := ((PolynormableSpace.withSeminorms ℂ E).mem_nhds_iff t W).1 hW
  set P : Seminorm ℂ E := s.sup fun p ↦ p.1
  refine ⟨N ⊔ P, fun z ↦ le_sup_left (a := N z) (b := P z) |>.trans_eq
    (Seminorm.sup_apply N P z).symm, fun ε hε ↦ ?_, r, hr, fun z hz ↦ hsub ?_⟩
  · rw [Seminorm.ball_sup]
    exact inter_mem (hN ε hε)
      (((PolynormableSpace.withSeminorms ℂ E).mem_nhds_iff 0 _).2 ⟨s, ε, hε, le_rfl⟩)
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    exact (le_sup_right (a := N z) (b := P z)).trans_lt
      ((Seminorm.sup_apply N P z).symm ▸ hz)

omit [PolynormableSpace ℂ E] in
/-- **Taylor coefficients bounded on a ball are `q`-continuous everywhere** (by homogeneity,
from `seminorm_taylorCoeff_sub_le`). -/
theorem qCont_taylorCoeff (hU : IsOpen U) (hG : GateauxAnalyticOn f U) {y : E}
    {N N' : Seminorm ℂ E} (hNN' : ∀ z, N z ≤ N' z) (hN' : ∀ ε > 0, N'.ball 0 ε ∈ 𝓝 (0 : E))
    {ρ r : ℝ} (hρ : 0 < ρ) (hr0 : 0 < r) (hr : r ≤ ρ) (hy : ∀ z, N z < 8 * ρ → y + z ∈ U)
    {q : Seminorm ℂ F} (hq : Continuous q) {m : ℕ} {n : ℝ}
    (hb : ∀ w, N' w < r → q (taylorCoeff f y m w) ≤ n) : QCont q (taylorCoeff f y m) := by
  intro h
  have hn : 0 ≤ n := (apply_nonneg q _).trans (hb 0 (by simpa using hr0))
  set s : ℝ := min 1 (r / (4 * (N' h + 1)))
  have hs : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsh : N' ((s : ℂ) • h) < r / 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have h1 : 0 < N' h + 1 := by positivity
    calc s * N' h ≤ r / (4 * (N' h + 1)) * N' h := by gcongr; exact min_le_right _ _
      _ < r / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [apply_nonneg N' h]
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun _ ↦
    ha.trans_le (apply_nonneg q _), fun ε hε ↦ ?_⟩
  set C : ℝ := (m + 1) * n / s ^ m
  have hC : 0 ≤ C := by positivity
  set δ : ℝ := min 1 (ε / (C + 1))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hnb : (fun h' : E ↦ h' - h) ⁻¹' N'.ball 0 (δ * r / (4 * s)) ∈ 𝓝 h := by
    have hc : Continuous fun h' : E ↦ h' - h := continuous_id.sub continuous_const
    have hb0 := hN' (δ * r / (4 * s)) (by positivity)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hb0)
  filter_upwards [hnb] with h' hh'
  have hh'' : N' (h' - h) < δ * r / (4 * s) := by simpa [Seminorm.mem_ball] using hh'
  set v : E := ((s / δ : ℝ) : ℂ) • (h' - h)
  have hv : N' v < r / 2 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc s / δ * N' (h' - h) < s / δ * (δ * r / (4 * s)) := by gcongr
      _ = r / 4 := by field_simp
      _ < r / 2 := by linarith
  have hsh' : (s : ℂ) • h' = (s : ℂ) • h + (δ : ℂ) • v := by
    simp only [v, smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hδ.ne']
    rw [smul_sub]; abel
  have hest := seminorm_taylorCoeff_sub_le hU hG hNN' hr hy hq hb hsh hv (l := (δ : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]; exact min_le_left _ _)
  rw [← hsh', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] at hest
  have hsnorm : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]; exact hs1
  obtain ⟨R₁, hR₁, hd₁⟩ := exists_lineDom hρ hy h'
  obtain ⟨R₂, hR₂, hd₂⟩ := exists_lineDom hρ hy h
  rw [taylorCoeff_smul hG hR₁ hd₁ hsnorm, taylorCoeff_smul hG hR₂ hd₂ hsnorm, ← smul_sub,
    map_smul_eq_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at hest
  have hsm : 0 < s ^ m := pow_pos hs m
  have hle : q (taylorCoeff f y m h' - taylorCoeff f y m h) ≤ C * δ := by
    have h1 : q (taylorCoeff f y m h' - taylorCoeff f y m h) ≤ (m + 1) * n * δ / s ^ m := by
      rw [le_div_iff₀ hsm]; linarith [hest]
    calc _ ≤ (m + 1) * n * δ / s ^ m := h1
      _ = C * δ := by simp only [C]; ring
  calc q (taylorCoeff f y m h' - taylorCoeff f y m h) ≤ C * δ := hle
    _ ≤ C * (ε / (C + 1)) := by gcongr; exact min_le_right _ _
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

/-- **Bounds for the Taylor coefficients at `c` from those at a nearby point** (the step of
[Muj86, Lemma 36.6 and Proposition 36.7]). Let `x = c - e` with `N e` small, and assume the Taylor
coefficients `T_x(m, ·)` are `q`-continuous. Then each `T_c(k, ·)` is `q`-bounded on a ball:
`T_c(k, t) = ∑_m Q_m(t)` weakly, where `Q_m(t)` extracts the coefficient of `λᵏ` of
`T_x(m, e + λ t)` by roots of unity; the partial sums are `q`-continuous and pointwise bounded,
so Baire's theorem and the shift lemma apply. -/
theorem exists_taylorCoeff_ball_bound [BaireSpace E] (hU : IsOpen U) (hG : GateauxAnalyticOn f U)
    {c e : E} {N : Seminorm ℂ E} (hN : ∀ ε > 0, N.ball 0 ε ∈ 𝓝 (0 : E)) {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z, N z < 8 * ρ → c + z ∈ U) (he : N e < ρ / 16) {q : Seminorm ℂ F}
    (hq : Continuous q) (hTx : ∀ m, QCont q (taylorCoeff f (c - e) m)) (k : ℕ) :
    ∃ N₂ : Seminorm ℂ E, (∀ z, N z ≤ N₂ z) ∧ (∀ ε > 0, N₂.ball 0 ε ∈ 𝓝 (0 : E)) ∧
      ∃ r₂ > 0, r₂ ≤ ρ / 2 ∧ ∃ n : ℝ, ∀ w, N₂ w < r₂ → q (taylorCoeff f c k w) ≤ n := by
  set x := c - e
  have hx : ∀ z, N z < 8 * (ρ / 2) → x + z ∈ U := fun z hz ↦ by
    have : x + z = c + (z - e) := by simp only [x]; abel
    rw [this]
    exact hc _ ((map_sub_le_add N _ _).trans_lt (by linarith))
  set ω : ℕ → ℂ := fun m ↦ rootN (m + 1)
  have hω : ∀ m j, ‖ω m ^ j‖ = 1 := fun m j ↦ by
    have : ‖ω m‖ = 1 := (Complex.isPrimitiveRoot_exp (m + 1) (by omega)).norm'_eq_one (by omega)
    rw [norm_pow, this, one_pow]
  set Q : ℕ → E → F := fun m t ↦ ∑ j ∈ Finset.range (m + 1),
    (((m + 1 : ℕ) : ℂ)⁻¹ * (ω m ^ j) ^ (m + 1 - k)) • taylorCoeff f x m (e + ω m ^ j • t)
  set S : ℕ → E → F := fun i t ↦ ∑ b ∈ Finset.range i, (1 : ℂ) • Q (k + b) t
  have hQ : ∀ m, QCont q (Q m) := fun m ↦ QCont.sum _ _ fun j _ ↦
    (hTx m).comp (continuous_const.add (continuous_const.smul continuous_id))
  have hS : ∀ i, QCont q (S i) := fun i ↦ QCont.sum _ (fun _ ↦ 1) fun b _ ↦ hQ (k + b)
  -- the functional identity on a plane
  have hplane : ∀ t, N t < ρ / 4 → ∃ M, ∀ ℓ : F →L[ℂ] ℂ, (∀ w, ‖ℓ w‖ ≤ q w) →
      (∀ i, ℓ (S i t) = ∑ b ∈ Finset.range i, osgoodCoeff₂ (planeFun f ℓ x e t) k b) ∧
      (∀ b, ‖osgoodCoeff₂ (planeFun f ℓ x e t) k b‖ ≤ max M 0 * (2 / 3) ^ b) ∧
      HasSum (fun b ↦ osgoodCoeff₂ (planeFun f ℓ x e t) k b) (ℓ (taylorCoeff f c k t)) := by
    intro t ht
    have hbox := planeDom_of_ball hx (h := e) (v := t) (by linarith) (by linarith)
    obtain ⟨M, hM⟩ := exists_complexPlane_bound hU hG hbox hq (R := 3)
    refine ⟨M, fun ℓ hℓ ↦ ⟨fun i ↦ ?_, fun b ↦ ?_, ?_⟩⟩
    · simp only [S, Q, one_smul, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      have hid : ∀ j, ℓ (taylorCoeff f x (k + b) (e + ω (k + b) ^ j • t)) =
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + b),
            osgoodCoeff₂ (planeFun f ℓ x e t) p.1 p.2 * (ω (k + b) ^ j) ^ p.1 := fun j ↦
        planeFun_line_identity hG hbox hM ℓ hℓ (k + b) (hω _ j).le
      simp only [hid, mul_assoc, ← Finset.mul_sum]
      have := avg_antidiagonal (k + b) k (by omega) (osgoodCoeff₂ (planeFun f ℓ x e t))
      rw [show k + b - k = b by omega] at this
      exact this
    · have hO := osgoodHyp_planeFun hG hbox hM ℓ hℓ
      have h1 := hO.norm_coeff₂_le k b
      have hM0 : 0 ≤ M := hO.bound_nonneg
      calc ‖osgoodCoeff₂ (planeFun f ℓ x e t) k b‖ ≤ M / 3 ^ k / (3 / 2) ^ b := h1
        _ ≤ M / 1 / (3 / 2) ^ b := by
            gcongr; exact one_le_pow₀ (by norm_num)
        _ = max M 0 * (2 / 3) ^ b := by
            rw [max_eq_left hM0, div_one, div_eq_mul_inv, ← inv_pow]; norm_num
    · have := planeFun_hasSum_shift hG hbox hM ℓ hℓ k
      simpa [x] using this
  have hgeom : ∀ i, ∑ b ∈ Finset.range i, (2 / 3 : ℝ) ^ b ≤ 3 := fun i ↦ by
    have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
      (by norm_num)).sum_le_tsum (Finset.range i) (fun b _ ↦ by positivity)
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at this
    linarith [show (1 - 2 / 3 : ℝ)⁻¹ = 3 by norm_num]
  -- Baire's theorem on a ball
  set O := interior {t : E | N t < ρ / 4}
  have hO : IsOpen O := isOpen_interior
  have h0O : (0 : E) ∈ O := mem_interior_iff_mem_nhds.2 (by
    simpa [Seminorm.ball] using hN (ρ / 4) (by positivity))
  have hOsub : ∀ t ∈ O, N t < ρ / 4 := fun t ht ↦ interior_subset ht
  obtain ⟨t₀, ht₀, W₁, hW₁, hW₁O, n, hn⟩ := exists_nhds_seminorm_bound hO ⟨0, h0O⟩
    (φ := S) (q := q) (fun i ↦ (hS i).continuous) (fun t ht ↦ by
      obtain ⟨M, hM⟩ := hplane t (hOsub t ht)
      refine ⟨3 * max M 0, fun i ↦ seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_⟩
      obtain ⟨hid, hb, -⟩ := hM ℓ hℓ
      rw [hid i]
      calc ‖∑ b ∈ Finset.range i, osgoodCoeff₂ (planeFun f ℓ x e t) k b‖
          ≤ ∑ b ∈ Finset.range i, max M 0 * (2 / 3 : ℝ) ^ b :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ ↦ hb b)
        _ = max M 0 * ∑ b ∈ Finset.range i, (2 / 3 : ℝ) ^ b := by rw [Finset.mul_sum]
        _ ≤ max M 0 * 3 := by gcongr; exact hgeom i
        _ = 3 * max M 0 := by ring)
  -- the bound passes to the Taylor coefficients at `c`
  have hTc : ∀ t ∈ W₁, q (taylorCoeff f c k t) ≤ n := by
    intro t ht
    obtain ⟨M, hM⟩ := hplane t (hOsub t (hW₁O ht))
    refine seminorm_le_of_forall_clm hq fun ℓ hℓ ↦ ?_
    obtain ⟨hid, -, hsum⟩ := hM ℓ hℓ
    refine le_of_tendsto ((continuous_norm.tendsto _).comp hsum.tendsto_sum_nat)
      (Eventually.of_forall fun i ↦ ?_)
    simp only [Function.comp, ← hid i]
    exact (hℓ _).trans (hn t ht i)
  obtain ⟨N₂, hNN₂, hN₂, r, hr, hsub⟩ := exists_seminorm_ball_subset hN hW₁
  refine ⟨N₂, hNN₂, hN₂, min r (ρ / 2), lt_min hr (by positivity), min_le_right _ _, n,
    fun w hw ↦ ?_⟩
  exact seminorm_taylorCoeff_le_of_shift hU hG hNN₂ hρ hc hq (t₀ := t₀)
    (by linarith [hOsub t₀ ht₀]) (min_le_right _ _)
    (fun v hv ↦ hTc _ (hsub v (hv.trans_le (min_le_left _ _)))) hw

/-- **Zorn's theorem for one seminorm** (compare [Muj86, Theorem 36.5 and Proposition 36.7], for
Banach spaces). Let `E` be a Baire space and `f` Gâteaux analytic on `U`. If `q ∘ f` is bounded
near a point `c - e` close enough to `c` (`N e < ρ/16`, where the `N`-ball of radius `8ρ` about
`c` lies in `U`), then `q ∘ f` is bounded near `c`. No completeness of `F` is used. -/
theorem exists_nhds_seminorm_bound_of_near [BaireSpace E] (hU : IsOpen U)
    (hG : GateauxAnalyticOn f U) {c e : E} {N : Seminorm ℂ E}
    (hN : ∀ ε > 0, N.ball 0 ε ∈ 𝓝 (0 : E)) {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z, N z < 8 * ρ → c + z ∈ U) (he : N e < ρ / 16) {q : Seminorm ℂ F}
    (hq : Continuous q) (hx : ∃ W ∈ 𝓝 (c - e), ∃ M, ∀ z ∈ W, q (f z) ≤ M) :
    ∃ W ∈ 𝓝 c, ∃ M, ∀ z ∈ W, q (f z) ≤ M := by
  set x := c - e
  have hxU : ∀ z, N z < 8 * (ρ / 2) → x + z ∈ U := fun z hz ↦ by
    have : x + z = c + (z - e) := by simp only [x]; abel
    rw [this]
    exact hc _ ((map_sub_le_add N _ _).trans_lt (by linarith))
  -- Step 1: the Taylor coefficients at `x` are `q`-continuous
  obtain ⟨W₀, hW₀, M₀, hM₀⟩ := hx
  obtain ⟨N₁, hNN₁, hN₁, r₁, hr₁, hsub₁⟩ := exists_seminorm_ball_subset hN hW₀
  set r := min (r₁ / 3) (ρ / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hTx : ∀ m, QCont q (taylorCoeff f x m) := by
    intro m
    refine qCont_taylorCoeff hU hG hNN₁ hN₁ (half_pos hρ) hr (min_le_right _ _) hxU hq
      (n := |M₀|) fun w hw ↦ ?_
    have hNw : N w < ρ / 2 := (hNN₁ w).trans_lt (hw.trans_le (min_le_right _ _))
    have hP := hasPowerSeriesOnDisc_taylorCoeff hG (by norm_num : (0 : ℝ) < 3)
      (lineDom_of_ball hxU hNw)
    have hbd : ∀ ζ ∈ sphere (0 : ℂ) 2, q (f (x + ζ • w)) ≤ |M₀| := fun ζ hζ ↦ by
      refine (hM₀ _ (hsub₁ _ ?_)).trans (le_abs_self _)
      rw [map_smul_eq_mul, mem_sphere_zero_iff_norm.1 hζ]
      have := hw.trans_le (min_le_left _ _)
      linarith
    have h1 := hP.seminorm_coeff_le (ρ := 2) (by norm_num) (by norm_num) hq
      (fun ζ hζ ↦ by simpa using hbd ζ (by simpa using hζ)) m
    calc q (taylorCoeff f x m w) ≤ |M₀| / 2 ^ m := h1
      _ ≤ |M₀| := div_le_self (abs_nonneg _) (one_le_pow₀ (by norm_num))
  -- Step 2: the Taylor coefficients at `c` are `q`-continuous
  have hTc : ∀ k, QCont q (taylorCoeff f c k) := by
    intro k
    obtain ⟨N₂, hNN₂, hN₂, r₂, hr₂, hr₂ρ, n, hn⟩ :=
      exists_taylorCoeff_ball_bound hU hG hN hρ hc he hq hTx k
    exact qCont_taylorCoeff hU hG hNN₂ hN₂ hρ hr₂ (by linarith) hc hq hn
  -- Step 3: Baire's theorem for `(2ᵏ T_c(k, ·))ₖ`
  set O := interior {t : E | N t < ρ / 2}
  have h0O : (0 : E) ∈ O := mem_interior_iff_mem_nhds.2 (by
    simpa [Seminorm.ball] using hN (ρ / 2) (by positivity))
  have hOsub : ∀ t ∈ O, N t < ρ / 2 := fun t ht ↦ interior_subset ht
  have hlineC : ∀ t, N t < ρ → HasPowerSeriesOnDisc (fun l : ℂ ↦ f (c + l • t))
      (fun k ↦ taylorCoeff f c k t) 0 3 := fun t ht ↦
    hasPowerSeriesOnDisc_taylorCoeff hG (by norm_num)
      (lineDom_of_ball (ρ := ρ) (fun z hz ↦ hc z (by linarith)) ht)
  obtain ⟨t₁, ht₁, W₂, hW₂, -, n', hn'⟩ := exists_nhds_seminorm_bound isOpen_interior
    ⟨0, h0O⟩ (q := q) (φ := fun k t ↦ (2 : ℂ) ^ k • taylorCoeff f c k t)
    (fun k ↦ ((hTc k).const_smul _).continuous) (fun t ht ↦ by
      have hNt : N t < ρ := by linarith [hOsub t ht]
      have hcont : ContinuousOn (fun l : ℂ ↦ f (c + l • t)) (sphere 0 2) :=
        (hG.cAnalyticOn_line c t).continuousOn.mono fun l hl ↦
          lineDom_of_ball (ρ := ρ) (fun z hz ↦ hc z (by linarith)) hNt l
            (by rw [mem_sphere_zero_iff_norm.1 hl]; norm_num)
      obtain ⟨M, hM⟩ := exists_seminorm_bound_sphere hcont hq
      refine ⟨M, fun k ↦ ?_⟩
      have h1 := (hlineC t hNt).seminorm_coeff_le (ρ := 2) (by norm_num) (by norm_num) hq
        (fun ζ hζ ↦ by simpa using hM ζ (by simpa using hζ)) k
      rw [map_smul_eq_mul, norm_pow, Complex.norm_ofNat]
      have h2 : (0 : ℝ) < 2 ^ k := by positivity
      rw [le_div_iff₀ h2] at h1
      linarith)
  -- the shift lemma gives geometric bounds on a ball about `0`
  obtain ⟨N₃, hNN₃, hN₃, r₃, hr₃, hsub₃⟩ := exists_seminorm_ball_subset hN hW₂
  set r₃' := min r₃ (ρ / 2)
  have hgeo : ∀ k, ∀ v, N₃ v < r₃' → q (taylorCoeff f c k v) ≤ n' * (1 / 2) ^ k := by
    intro k v hv
    refine seminorm_taylorCoeff_le_of_shift hU hG hNN₃ hρ hc hq (t₀ := t₁)
      (by linarith [hOsub t₁ ht₁]) (min_le_right _ _) (fun w hw ↦ ?_) hv
    have h1 := hn' _ (hsub₃ w (hw.trans_le (min_le_left _ _))) k
    rw [map_smul_eq_mul, norm_pow, Complex.norm_ofNat] at h1
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ h2]
    linarith
  refine ⟨(fun z ↦ z - c) ⁻¹' N₃.ball 0 r₃', ?_, 2 * n', fun z hz ↦ ?_⟩
  · exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using hN₃ r₃' (lt_min hr₃ (by positivity)))
  · have hz' : N₃ (z - c) < r₃' := by simpa [Seminorm.mem_ball] using hz
    have hNz : N (z - c) < ρ := by
      linarith [hNN₃ (z - c), min_le_right r₃ (ρ / 2)]
    have hS := (hlineC (z - c) hNz) 1 (by norm_num)
    simp only [zero_add, one_smul, one_pow, add_sub_cancel] at hS
    have := seminorm_le_of_hasSum hq hS
      ((summable_geometric_two).mul_left n') (fun k ↦ hgeo k _ hz')
    rw [tsum_mul_left, tsum_geometric_two] at this
    linarith

end Zorn

/-! ### Separately analytic maps on products -/

section Products

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [Module ℂ E₁] [IsScalarTower ℝ ℂ E₁]
  [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℂ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u} [AddCommGroup E₂] [Module ℝ E₂] [Module ℂ E₂] [IsScalarTower ℝ ℂ E₂]
  [TopologicalSpace E₂] [IsTopologicalAddGroup E₂] [ContinuousSMul ℂ E₂]
  [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F]

attribute [local instance] polynormableSpace_complex

omit [Module ℝ E₁] [IsScalarTower ℝ ℂ E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℂ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁] [Module ℝ E₂] [IsScalarTower ℝ ℂ E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℂ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  [Module ℝ F] [IsScalarTower ℝ ℂ F] [IsTopologicalAddGroup F] [ContinuousSMul ℂ F]
  [LocallyConvexSpace ℝ F] [T2Space F] in
/-- **Baire's theorem for separately continuous maps** ([Muj86, Lemma 36.2], one seminorm): if
`E₁` is a Baire space and `E₂` is first countable, a separately analytic `f` is `q`-bounded on a
neighbourhood of `(x', b)` for points `x'` in any neighbourhood of `a`. -/
theorem exists_near_seminorm_bound [BaireSpace E₁] [FirstCountableTopology E₂]
    {f : E₁ × E₂ → F} {U : Set (E₁ × E₂)} (hU : IsOpen U)
    (h₁ : ∀ y, ComplexAnalyticOn (fun x ↦ f (x, y)) {x | (x, y) ∈ U})
    (h₂ : ∀ x, ComplexAnalyticOn (fun y ↦ f (x, y)) {y | (x, y) ∈ U}) {a : E₁} {b : E₂}
    (hab : (a, b) ∈ U) {q : Seminorm ℂ F} (hq : Continuous q) {W : Set E₁} (hW : W ∈ 𝓝 a) :
    ∃ x' ∈ W, ∃ G ∈ 𝓝 (x', b), ∃ M, ∀ z ∈ G, q (f z) ≤ M := by
  obtain ⟨A₀, B₀, hA₀, hB₀, haA, hbB, hAB⟩ := isOpen_prod_iff.1 hU a b hab
  set A := A₀ ∩ interior W
  have hA : IsOpen A := hA₀.inter isOpen_interior
  have haA' : a ∈ A := ⟨haA, mem_interior_iff_mem_nhds.2 hW⟩
  obtain ⟨V, hVb, hVanti⟩ := (𝓝 b).exists_antitone_basis
  have : BaireSpace A := hA.baireSpace
  have : Nonempty A := ⟨⟨a, haA'⟩⟩
  -- shrink the basis into `B₀`
  obtain ⟨n₀, -, hVn₀⟩ := hVb.mem_iff.1 (hB₀.mem_nhds hbB)
  have hn₀ : ∀ n ≥ n₀, V n ⊆ B₀ := fun n hn ↦ (hVanti hn).trans hVn₀
  set C : ℕ → Set A := fun n ↦ {x | ∀ y ∈ V (n + n₀), q (f (x, y)) ≤ n}
  have hC : ∀ n, IsClosed (C n) := by
    intro n
    have : C n = ⋂ y ∈ V (n + n₀), (fun x : A ↦ q (f (x, y))) ⁻¹' Iic (n : ℝ) := by
      ext; simp [C]
    rw [this]
    refine isClosed_biInter fun y hy ↦ isClosed_Iic.preimage (hq.comp ?_)
    have hcont := (h₁ y).1
    refine hcont.comp_continuous continuous_subtype_val fun x ↦ ?_
    exact hAB ⟨x.2.1, hn₀ (n + n₀) (by omega) hy⟩
  have hcov : ⋃ n, C n = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    have hU₂ : IsOpen {y | ((x : E₁), y) ∈ U} := hU.preimage (continuous_const.prodMk continuous_id)
    have hxb : ((x : E₁), b) ∈ U := hAB ⟨x.2.1, hbB⟩
    have hca : ContinuousAt (fun y ↦ f ((x : E₁), y)) b :=
      (h₂ x).1.continuousAt (hU₂.mem_nhds hxb)
    have hev : ∀ᶠ y in 𝓝 b, q (f ((x : E₁), y)) < q (f ((x : E₁), b)) + 1 :=
      ((hq.tendsto _).comp hca).eventually (gt_mem_nhds (by linarith))
    obtain ⟨n₁, -, hn₁⟩ := hVb.mem_iff.1 hev
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge (q (f ((x : E₁), b)) + 1)
    refine ⟨max n₁ n₂, fun y hy ↦ ?_⟩
    have hy' := hVanti (show n₁ ≤ max n₁ n₂ + n₀ by omega) hy
    exact (hn₁ hy').le.trans (hn₂.trans (by exact_mod_cast le_max_right n₁ n₂))
  obtain ⟨n, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hC hcov
  have hG : IsOpen ((↑) '' interior (C n) : Set E₁) := hA.isOpenMap_subtype_val _ isOpen_interior
  refine ⟨x₀, interior_subset x₀.2.2, ((↑) '' interior (C n)) ×ˢ V (n + n₀),
    prod_mem_nhds (hG.mem_nhds (mem_image_of_mem _ hx₀)) (hVb.mem_of_mem trivial), n,
    fun z hz ↦ ?_⟩
  obtain ⟨⟨x, hx, hxz⟩, hy⟩ := hz
  have h := interior_subset hx z.2 hy
  rw [hxz] at h
  exact h

omit [T2Space E₁] [T2Space E₂] in
/-- **Separately analytic maps are locally bounded** (compare [Muj86, Theorem 36.8], for Banach
spaces), if `E₁` and `E₁ × E₂` are Baire spaces, `E₂` is first countable (e.g. both Fréchet)
and `F` is Mackey complete: by Baire's theorem `q ∘ f` is bounded near points `(x', b)` with
`x'` arbitrarily close to `a`, and Zorn's theorem for one seminorm
(`exists_nhds_seminorm_bound_of_near`) carries the bound to `(a, b)`. -/
theorem locallyBoundedOn_of_separately [BaireSpace E₁] [FirstCountableTopology E₂]
    [BaireSpace (E₁ × E₂)] [MackeyComplete F] {f : E₁ × E₂ → F} {U : Set (E₁ × E₂)}
    (hU : IsOpen U) (h₁ : ∀ y, ComplexAnalyticOn (fun x ↦ f (x, y)) {x | (x, y) ∈ U})
    (h₂ : ∀ x, ComplexAnalyticOn (fun y ↦ f (x, y)) {y | (x, y) ∈ U}) :
    LocallyBoundedOn f U := by
  rintro ⟨a, b⟩ hab q hq
  have hG := gateauxAnalyticOn_of_separately hU h₁ h₂
  obtain ⟨s, r, hr, hsub⟩ :=
    ((PolynormableSpace.withSeminorms ℂ (E₁ × E₂)).mem_nhds_iff (a, b) U).1 (hU.mem_nhds hab)
  set N : Seminorm ℂ (E₁ × E₂) := s.sup fun p ↦ p.1
  have hN : ∀ ε > 0, N.ball 0 ε ∈ 𝓝 (0 : E₁ × E₂) := fun ε hε ↦
    ((PolynormableSpace.withSeminorms ℂ (E₁ × E₂)).mem_nhds_iff 0 _).2 ⟨s, ε, hε, le_rfl⟩
  set ρ := r / 8
  have hρ : 0 < ρ := by positivity
  have hc : ∀ z, N z < 8 * ρ → (a, b) + z ∈ U := fun z hz ↦ hsub (by
    rw [Seminorm.mem_ball, add_sub_cancel_left]
    have : 8 * ρ = r := by simp only [ρ]; ring
    linarith)
  -- points `x'` with `N (a - x', 0) < ρ / 16` form a neighbourhood of `a`
  have hW : (fun x' : E₁ ↦ ((a - x', 0) : E₁ × E₂)) ⁻¹' N.ball 0 (ρ / 16) ∈ 𝓝 a := by
    have hcont : Continuous fun x' : E₁ ↦ ((a - x', 0) : E₁ × E₂) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    have h0 : ((a - a, 0) : E₁ × E₂) = 0 := by simp
    exact hcont.continuousAt (x := a) |>.preimage_mem_nhds
      (by rw [h0]; exact hN (ρ / 16) (by positivity))
  obtain ⟨x', hx', G, hG', M, hM⟩ := exists_near_seminorm_bound hU h₁ h₂ hab hq hW
  have he : ((a, b) : E₁ × E₂) - ((a - x', 0) : E₁ × E₂) = (x', b) := by
    ext <;> simp
  have hx'' : N (a - x', 0) < ρ / 16 := by simpa [Seminorm.mem_ball] using hx'
  obtain ⟨W, hW', M', hM'⟩ := exists_nhds_seminorm_bound_of_near (f := f) hU hG hN hρ hc
    (e := ((a - x', 0) : E₁ × E₂)) hx'' hq ⟨G, he ▸ hG', M, hM⟩
  exact ⟨W, hW', M', hM'⟩

/-- **Hartogs' theorem on products of locally convex spaces** (compare [Muj86, Theorem 36.8], for
Banach spaces): if `E₁` and `E₁ × E₂` are Baire spaces, `E₂` is first countable (e.g. `E₁`, `E₂`
Fréchet spaces) and `F` is Mackey complete, a separately complex analytic map on an open subset
of `E₁ × E₂` is complex analytic. -/
theorem complexAnalyticOn_of_separately_prod [BaireSpace E₁] [FirstCountableTopology E₂]
    [BaireSpace (E₁ × E₂)] [MackeyComplete F] {f : E₁ × E₂ → F} {U : Set (E₁ × E₂)}
    (hU : IsOpen U) (h₁ : ∀ y, ComplexAnalyticOn (fun x ↦ f (x, y)) {x | (x, y) ∈ U})
    (h₂ : ∀ x, ComplexAnalyticOn (fun y ↦ f (x, y)) {y | (x, y) ∈ U}) :
    ComplexAnalyticOn f U :=
  complexAnalyticOn_of_separately_of_locallyBoundedOn hU h₁ h₂
    (locallyBoundedOn_of_separately hU h₁ h₂)

end Products

end LocallyConvex.Analysis

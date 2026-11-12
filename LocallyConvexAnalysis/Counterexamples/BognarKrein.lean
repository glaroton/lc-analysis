/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Krein.OrthoComplemented
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# A closed positive definite subspace of a Krein space that is not a Krein space

Reference: J. Bognár, *Indefinite Inner Product Spaces*, Springer (1974), Example V.3.3 (p. 104),
which takes up Example I.9.7 (pp. 19–20).

Bognár's space is `ℓ²` with `[x, y] = Σ_{j ≥ 1} (-1)^j ξ_j η̄_j`, a Krein space with fundamental
symmetry `J = diag((-1)^j)`, and

`𝔏 = {x | ξ_{2j} = 2j / (2j - 1) · ξ_{2j-1}, j = 1, 2, …}`.

In Example I.9.7 he shows that `𝔏` is positive definite, `𝔏^[⊥⊥] = 𝔏`, and `𝔏` is not
ortho-complemented; in Example V.3.3 that `𝔏` is closed, positive definite (so nondegenerate,
and decomposable as `𝔏 ⊕ 0`), but not intrinsically complete, hence not a Krein space: "a
closed, non-degenerate subspace of a Krein space, though decomposable, need not be a Krein
space".

Here (0-based indices, `x i = ξ_{i+1}`, over `𝕜 = ℝ` or `ℂ`): `J x = (s_i x_i)` with `s_i = -1`
for even `i` and `+1` for odd `i` (`J`), and `L = {x | x_{2k+1} = d_k x_{2k}}` with
`d_k = (2k + 2) / (2k + 1)` (`L`). For `x ∈ L`,

`[x, x] = Σ_k (d_k² - 1) |x_{2k}|²`   (`re_form_of_mem`),

which is positive for `x ≠ 0`, while `d_k² - 1 ≤ 3 / (2k + 1) → 0`: `L` is not uniformly
positive. By `FundamentalSymmetry.not_isOrthoComplemented_of_posDef` ([Bog74, Theorem V.3.4] and
the open mapping theorem), `L` is neither intrinsically complete, nor a Krein space, nor
ortho-complemented (`bognar_example`).

## Main definitions

* `s`: the signs `s_i = -1` for even `i`, `+1` for odd `i`.
* `J`: the fundamental symmetry `J = diag(s_i)` of `ℓ²`.
* `d`: the coefficients `d_k = (2k + 2) / (2k + 1)`.
* `L`: Bognár's subspace `L = {x | x_{2k+1} = d_k x_{2k}}` of `ℓ²`.

## Main results

* `isClosed_L`: `L` is closed.
* `re_form_of_mem`: for `x ∈ L`, `re [x, x] = Σ_k (d_k² - 1) ‖x_{2k}‖²`.
* `re_form_pos`: `L` is positive definite.
* `not_uniformlyPositive`: `L` is not uniformly positive: `[x, x] / ‖x‖²` gets arbitrarily small
  on `L`.
* `bognar_example`: **[Bog74, Example V.3.3]** (with Example I.9.7). `L` is closed, positive
  definite (hence nondegenerate) and decomposable (`L = L ⊕ 0`), but it is not intrinsically
  complete, not a Krein space, and not ortho-complemented.

## Implementation notes

Bognár proves the failure of intrinsic completeness with an explicit intrinsic Cauchy sequence
whose would-be limit is not in `ℓ²`; here it follows from the failure of uniform positivity.

## References

* [J. Bognár, *Indefinite Inner Product Spaces*][Bog74]
-/

@[expose] public section

open Filter RCLike
open scoped InnerProductSpace ComplexConjugate lp

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples.BognarKrein

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The signs `s_i = -1` for even `i`, `+1` for odd `i` (Bognár's `(-1)^j`, `j = i + 1`). -/
def s (i : ℕ) : ℝ := if Even i then -1 else 1

theorem abs_s (i : ℕ) : |s i| = 1 := by unfold s; split_ifs <;> simp

theorem s_mul_s (i : ℕ) : s i * s i = 1 := by unfold s; split_ifs <;> norm_num

theorem s_even (k : ℕ) : s (2 * k) = -1 := by simp [s]

theorem s_odd (k : ℕ) : s (2 * k + 1) = 1 := by
  simp only [s, Nat.not_even_iff_odd.2 (odd_two_mul_add_one k), ite_false]

theorem memℓp_s_mul (x : ℓ²(ℕ, 𝕜)) : Memℓp (fun i ↦ (s i : 𝕜) * x i) 2 :=
  (lp.memℓp x).mono' fun i ↦ by rw [norm_mul, norm_ofReal, abs_s, one_mul]

/-- The fundamental symmetry `J x = (s_i x_i)_i`, as a linear map. -/
def Jₗ : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨fun i ↦ (s i : 𝕜) * x i, memℓp_s_mul 𝕜 x⟩
  map_add' x y := lp.ext <| funext fun i ↦ by
    change (s i : 𝕜) * (x + y) i = (s i : 𝕜) * x i + (s i : 𝕜) * y i
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := lp.ext <| funext fun i ↦ by
    change (s i : 𝕜) * (c • x) i = (c • _ : ℓ²(ℕ, 𝕜)) i
    rw [lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    change (s i : 𝕜) * (c * x i) = c * ((s i : 𝕜) * x i)
    ring

/-- The fundamental symmetry `J = diag(s_i)` of `ℓ²`. -/
def J : FundamentalSymmetry 𝕜 ℓ²(ℕ, 𝕜) where
  op := (Jₗ 𝕜).mkContinuous 1 fun x ↦ by
    rw [one_mul]
    exact lp.norm_mono two_ne_zero fun i ↦ by
      change ‖(s i : 𝕜) * x i‖ ≤ ‖x i‖
      rw [norm_mul, norm_ofReal, abs_s, one_mul]
  inner_op x y := by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    refine tsum_congr fun i ↦ ?_
    change ⟪(s i : 𝕜) * x i, y i⟫_𝕜 = ⟪x i, (s i : 𝕜) * y i⟫_𝕜
    rw [RCLike.inner_apply', RCLike.inner_apply', map_mul, conj_ofReal]
    ring
  op_op x := lp.ext <| funext fun i ↦ by
    change (s i : 𝕜) * ((s i : 𝕜) * x i) = x i
    rw [← mul_assoc, ← ofReal_mul, s_mul_s, ofReal_one, one_mul]

theorem J_op_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) : (J 𝕜).op x i = (s i : 𝕜) * x i := rfl

/-- The coefficients `d_k = (2k + 2) / (2k + 1)` (Bognár's `2j / (2j - 1)`, `j = k + 1`). -/
def d (k : ℕ) : ℝ := (2 * k + 2) / (2 * k + 1)

theorem d_eq (k : ℕ) : d k = 1 + 1 / (2 * k + 1) := by
  unfold d
  field_simp
  ring

theorem one_lt_d (k : ℕ) : 1 < d k := by
  rw [d_eq]
  have : (0 : ℝ) < 1 / (2 * k + 1) := by positivity
  linarith

theorem d_sq_sub_one_le (k : ℕ) : d k ^ 2 - 1 ≤ 3 / (2 * k + 1) := by
  rw [d_eq]
  have ht : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have ht0 : 0 ≤ 1 / (2 * (k : ℝ) + 1) := by positivity
  have e : 3 / (2 * (k : ℝ) + 1) = 3 * (1 / (2 * k + 1)) := by ring
  rw [e]
  nlinarith

/-- Bognár's subspace `L = {x | x_{2k+1} = d_k x_{2k}}`. -/
def L : Submodule 𝕜 ℓ²(ℕ, 𝕜) where
  carrier := {x | ∀ k, x (2 * k + 1) = (d k : 𝕜) * x (2 * k)}
  add_mem' {x y} hx hy k := by
    change (x + y) (2 * k + 1) = (d k : 𝕜) * (x + y) (2 * k)
    rw [lp.coeFn_add, Pi.add_apply, Pi.add_apply, hx k, hy k, mul_add]
  zero_mem' k := by simp
  smul_mem' c x hx k := by
    change (c • x) (2 * k + 1) = (d k : 𝕜) * (c • x) (2 * k)
    rw [lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hx k]
    ring

theorem mem_L {x : ℓ²(ℕ, 𝕜)} : x ∈ L 𝕜 ↔ ∀ k, x (2 * k + 1) = (d k : 𝕜) * x (2 * k) :=
  Iff.rfl

/-- `L` is closed. -/
theorem isClosed_L : IsClosed (L 𝕜 : Set ℓ²(ℕ, 𝕜)) := by
  have hc : ∀ i, Continuous fun x : ℓ²(ℕ, 𝕜) ↦ x i :=
    fun i ↦ (lp.lipschitzWith_one_eval 2 i).continuous
  have : (L 𝕜 : Set ℓ²(ℕ, 𝕜)) = ⋂ k, {x | x (2 * k + 1) = (d k : 𝕜) * x (2 * k)} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [this]
  exact isClosed_iInter fun k ↦ isClosed_eq (hc _) (continuous_const.mul (hc _))

theorem summable_norm_sq (x : ℓ²(ℕ, 𝕜)) : Summable fun i ↦ ‖x i‖ ^ 2 := by
  have := (reCLM (K := 𝕜)).summable (lp.summable_inner x x)
  refine this.congr fun i ↦ ?_
  simp [reCLM_apply]

/-- The form of `J` on `ℓ²`: `re [x, x] = Σ_i s_i ‖x_i‖²`. -/
theorem re_form (x : ℓ²(ℕ, 𝕜)) : re ⟪(J 𝕜).op x, x⟫_𝕜 = ∑' i, s i * ‖x i‖ ^ 2 := by
  rw [lp.inner_eq_tsum, ← reCLM_apply, ContinuousLinearMap.map_tsum _ (lp.summable_inner _ _)]
  refine tsum_congr fun i ↦ ?_
  have e : ∀ z : 𝕜, conj ((s i : 𝕜) * z) * z = ((s i * ‖z‖ ^ 2 : ℝ) : 𝕜) := fun z ↦ by
    rw [map_mul (starRingEnd 𝕜), conj_ofReal, mul_assoc, RCLike.conj_mul]
    push_cast
    ring
  rw [reCLM_apply, J_op_apply, RCLike.inner_apply', e, ofReal_re]

/-- **The form on `L`**: `re [x, x] = Σ_k (d_k² - 1) ‖x_{2k}‖²` for `x ∈ L`. -/
theorem re_form_of_mem {x : ℓ²(ℕ, 𝕜)} (hx : x ∈ L 𝕜) :
    re ⟪(J 𝕜).op x, x⟫_𝕜 = ∑' k, (d k ^ 2 - 1) * ‖x (2 * k)‖ ^ 2 := by
  have hs := summable_norm_sq 𝕜 x
  have he : Summable fun k ↦ ‖x (2 * k)‖ ^ 2 :=
    hs.comp_injective fun a b h ↦ by simpa using h
  have ho : Summable fun k ↦ ‖x (2 * k + 1)‖ ^ 2 :=
    hs.comp_injective fun a b h ↦ by simpa using h
  have hodd : ∀ k, ‖x (2 * k + 1)‖ ^ 2 = d k ^ 2 * ‖x (2 * k)‖ ^ 2 := fun k ↦ by
    rw [hx k, norm_mul, norm_ofReal, abs_of_pos (zero_lt_one.trans (one_lt_d k)), mul_pow]
  have hR : ∑' k, (d k ^ 2 - 1) * ‖x (2 * k)‖ ^ 2 =
      ∑' k, ‖x (2 * k + 1)‖ ^ 2 - ∑' k, ‖x (2 * k)‖ ^ 2 := by
    rw [← ho.tsum_sub he]
    exact tsum_congr fun k ↦ by rw [hodd]; ring
  have he' : Summable fun k ↦ s (2 * k) * ‖x (2 * k)‖ ^ 2 := by
    simpa only [s_even, neg_one_mul] using he.neg
  have ho' : Summable fun k ↦ s (2 * k + 1) * ‖x (2 * k + 1)‖ ^ 2 := by
    simpa only [s_odd, one_mul] using ho
  rw [re_form, ← tsum_even_add_odd he' ho', hR]
  simp only [s_even, s_odd, neg_one_mul, one_mul, tsum_neg]
  ring

/-- `L` is **positive definite**. -/
theorem re_form_pos {x : ℓ²(ℕ, 𝕜)} (hx : x ∈ L 𝕜) (h0 : x ≠ 0) : 0 < re ⟪(J 𝕜).op x, x⟫_𝕜 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (lp.ext (funext h))
  obtain ⟨k, hk⟩ : ∃ k, x (2 * k) ≠ 0 := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · exact ⟨k, hi⟩
    · refine ⟨k, fun h ↦ hi ?_⟩
      rw [hx k, h, mul_zero]
  have hs := summable_norm_sq 𝕜 x
  have he : Summable fun k ↦ ‖x (2 * k)‖ ^ 2 :=
    hs.comp_injective fun a b h ↦ by simpa using h
  have hd : ∀ k, 0 < d k ^ 2 - 1 := fun k ↦ by nlinarith [one_lt_d k]
  have hle : ∀ k, d k ^ 2 - 1 ≤ 3 := fun k ↦ (d_sq_sub_one_le k).trans
    (div_le_self (by norm_num) (by have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith))
  have hsum : Summable fun k ↦ (d k ^ 2 - 1) * ‖x (2 * k)‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hd k).le (sq_nonneg _))
      (fun k ↦ mul_le_mul_of_nonneg_right (hle k) (sq_nonneg _)) (he.mul_left 3)
  rw [re_form_of_mem 𝕜 hx]
  exact hsum.tsum_pos (fun k ↦ mul_nonneg (hd k).le (sq_nonneg _)) k
    (mul_pos (hd k) (by positivity))

/-- `L` is **not uniformly positive**: `[x, x] / ‖x‖²` gets arbitrarily small on `L`. -/
theorem not_uniformlyPositive (c : ℝ) (hc : 0 < c) :
    ∃ x ∈ L 𝕜, re ⟪(J 𝕜).op x, x⟫_𝕜 < c * ‖x‖ ^ 2 := by
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (3 / c)
  let x : ℓ²(ℕ, 𝕜) := lp.single 2 (2 * k₀) 1 + lp.single 2 (2 * k₀ + 1) (d k₀ : 𝕜)
  have hx_even : ∀ k, x (2 * k) = if k = k₀ then 1 else 0 := fun k ↦ by
    simp only [x, lp.coeFn_add, Pi.add_apply, lp.single_apply]
    by_cases h : k = k₀
    · subst h; simp
    · simp [h, show 2 * k ≠ 2 * k₀ + 1 by omega]
  have hx_odd : ∀ k, x (2 * k + 1) = if k = k₀ then (d k₀ : 𝕜) else 0 := fun k ↦ by
    simp only [x, lp.coeFn_add, Pi.add_apply, lp.single_apply]
    by_cases h : k = k₀
    · subst h; simp
    · simp [h, show 2 * k + 1 ≠ 2 * k₀ by omega]
  have hxL : x ∈ L 𝕜 := fun k ↦ by
    rw [hx_even, hx_odd]
    by_cases h : k = k₀
    · subst h; simp
    · simp [h]
  refine ⟨x, hxL, ?_⟩
  have hform : re ⟪(J 𝕜).op x, x⟫_𝕜 = d k₀ ^ 2 - 1 := by
    rw [re_form_of_mem 𝕜 hxL, tsum_eq_single k₀ fun k hk ↦ by simp [hx_even, hk]]
    simp [hx_even]
  have hnorm : 1 ≤ ‖x‖ := by
    have := lp.norm_apply_le_norm two_ne_zero x (2 * k₀)
    simpa [hx_even] using this
  have hsmall : d k₀ ^ 2 - 1 < c := by
    refine (d_sq_sub_one_le k₀).trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hc] at hk₀
    have : (0 : ℝ) ≤ k₀ := k₀.cast_nonneg
    nlinarith
  rw [hform]
  have : c ≤ c * ‖x‖ ^ 2 := le_mul_of_one_le_right hc.le (one_le_pow₀ hnorm)
  linarith

/-- **[Bog74, Example V.3.3]** (with Example I.9.7). In the Krein space `(ℓ², [·, ·])`,
`[x, y] = ⟪J x, y⟫` with `J = diag(-1, 1, -1, 1, …)`, the subspace
`L = {x | x_{2k+1} = (2k + 2)/(2k + 1) x_{2k}}` is closed, positive definite (hence nondegenerate),
and decomposable (`L = L ⊕ 0`), but it is not intrinsically complete, not a Krein space, and not
ortho-complemented. Over `𝕜 = ℝ` and `ℂ` (Bognár: `ℂ`). -/
theorem bognar_example :
    IsClosed (L 𝕜 : Set ℓ²(ℕ, 𝕜)) ∧
      (∀ x ∈ L 𝕜, x ≠ 0 → 0 < re ⟪(J 𝕜).op x, x⟫_𝕜) ∧
      (∀ v ∈ L 𝕜, (∀ z ∈ L 𝕜, ⟪(J 𝕜).op v, z⟫_𝕜 = 0) → v = 0) ∧
      Nonempty (AlgFundamentalDecomposition (J 𝕜).form (L 𝕜)) ∧
      ¬ IntrinsicallyComplete (J 𝕜).form (L 𝕜) ∧ ¬ IsKreinSpace (J 𝕜).form (L 𝕜) ∧
      ¬ (J 𝕜).IsOrthoComplemented (L 𝕜) := by
  have hpos : ∀ x ∈ L 𝕜, x ≠ 0 → 0 < re ⟪(J 𝕜).op x, x⟫_𝕜 := fun x hx h0 ↦ re_form_pos 𝕜 hx h0
  refine ⟨isClosed_L 𝕜, hpos, fun v hv hz ↦ ?_, ⟨?_⟩,
    FundamentalSymmetry.not_isOrthoComplemented_of_posDef (isClosed_L 𝕜) hpos
      (not_uniformlyPositive 𝕜)⟩
  · by_contra h0
    have := hpos v hv h0
    rw [hz v hv, map_zero] at this
    exact lt_irrefl _ this
  · exact
      { pos := L 𝕜
        neg := ⊥
        sup_eq := sup_bot_eq _
        disjoint := disjoint_bot_right
        orth := fun x _ y hy ↦ by rw [(Submodule.mem_bot 𝕜).1 hy, map_zero]
        pos_def := hpos
        neg_def := fun x hx h0 ↦ absurd ((Submodule.mem_bot 𝕜).1 hx) h0 }

end LocallyConvex.Analysis.Counterexamples.BognarKrein

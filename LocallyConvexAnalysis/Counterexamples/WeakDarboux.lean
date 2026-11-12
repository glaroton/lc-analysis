/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Darboux's theorem fails for weak symplectic forms

Let `E` be a Banach space. A continuous bilinear form `ω` on `E` is *strongly nondegenerate* if
`ω^♭ : E → E*`, `v ↦ ω(v, ·)`, is an isomorphism onto the dual, and *weakly nondegenerate* if
`ω^♭` is only injective. A (weak) symplectic form on an open subset of `E` is a smooth closed
`2`-form which is (weakly) nondegenerate at every point. In infinite dimensions the difference is
real: the canonical form on the cotangent bundle of a manifold modeled on a non-reflexive space,
and many forms of mathematical physics (wave equation, fluids), are only weakly nondegenerate.

**The Darboux–Weinstein theorem** (A. Weinstein, *Symplectic structures on Banach manifolds*,
Bull. Amer. Math. Soc. 75 (1969), 1040–1041, the Theorem on p. 1040; see also A. Weinstein,
*Symplectic manifolds and their Lagrangian submanifolds*, Adv. Math. 6 (1971), 329–346,
Corollary 4.2, p. 334). Let `Ω`
be a strongly nondegenerate symplectic form on a neighborhood of `0` in a Banach space `B`, and
let `Ω₁` be the constant form equal to `Ω` at `0`. Then there are neighborhoods `U`, `V` of `0` and
a diffeomorphism `f : U → V` with `f(0) = 0`, `df(0) = id` and `f^* Ω₁ = Ω`. The proof is Moser's
path method, which inverts `Ω_t^♭` along `Ω_t = Ω + t (Ω₁ - Ω)`; this uses that invertibility is
an open condition. The theorem is formalized in lc-manifolds, for strong symplectic forms on
Banach manifolds (`LocallyConvexManifolds/Darboux.lean`, `Darboux.exists_darboux_local`).

**Marsden's counterexample** (J. E. Marsden, *Darboux's theorem fails for weak symplectic forms*,
Proc. Amer. Math. Soc. 32 (1972), 590–592; the example and its Proposition are on p. 591). Let
`H` be a real Hilbert space and `S : H → H` a bounded operator which is self-adjoint, positive
(`(S e, e) > 0` for `e ≠ 0`) and not onto, such that `a I + S` is onto for every `a > 0`. Let
`A_x = S + ‖x‖² I` and `g_x(e, f) = (A_x e, f)`: a smooth weak Riemannian metric on `H`, strong
(`A_x` onto) exactly when `x ≠ 0`. Let `Ω` be the form on `H × H` induced by `g`, the pullback
of the canonical form of `T*H` by the Legendre map `(x, e) ↦ (x, g_x(e, ·))`. Then `Ω` is a weak
symplectic form, but no chart around `(0, 0)` makes it constant. The reason is that a chart
transports `Ω_p^♭` by isomorphisms, so whether `Ω_p^♭` is onto cannot change inside a chart
domain; it is onto at `(x, 0)` for `x ≠ 0`, because `g_x` is strong there, and not at `(0, 0)`,
because `g_0(e, f) = (S e, f)` and `S` is not onto.

## Main definitions

* `DiffForm.d₁`, `DiffForm.d₂`: the exterior derivatives of a `1`-form and of a `2`-form on a
  normed space (see the conventions below).
* `Marsden.A`, `Marsden.g`: the operators `A_x = S + ‖x‖² I` and the weak Riemannian metric
  `g_x(e, f) = (A_x e, f)` on `H`.
* `Marsden.θ`, `Marsden.Ω`: the `1`-form `θ_{(x,e)}(e₁, e₂) = g_x(e, e₁)` on `H × H` and the
  `2`-form `Ω = -dθ`.
* `Marsden.L2.S`: the diagonal operator `S = diag(1 / (n + 1))` on `H = ℓ²(ℕ, ℝ)`.

## Main results

* Exterior derivatives: `dθ` is alternating, `C^m` if `θ` is `C^{m+1}` (`DiffForm.contDiff_d₁`),
  and `DiffForm.d₂_d₁`: `d(dθ) = 0` at every point where `θ` is `C²`, by symmetry of the second
  derivative.
* `Marsden.contDiff_Ω`, `Marsden.Ω_eq_neg_d₁`, `Marsden.d₂_Ω`: `Ω` is smooth (Fréchet `C^∞` on
  `H × H`), exact (`Ω = -dθ`, by definition) and closed. `Marsden.Ω_apply`: it is given by
  Marsden's formula; `Marsden.Ω_apply_zero_section`: on the zero section,
  `Ω_{(x,0)}(u, v) = g_x(e₄, e₁) - g_x(e₂, e₃)`. None of this uses any property of `S`.
* `Marsden.injective_Ω`: `Ω` is weakly nondegenerate at every point (this uses only positivity of
  `S`); `Marsden.surjective_Ω_of_ne_zero`: it is strongly nondegenerate at `(x, 0)` for `x ≠ 0`
  (here `H` is complete and the Riesz representation theorem is used);
  `Marsden.not_surjective_Ω_zero`: it is not strongly nondegenerate at `(0, 0)`.
* `surjective_iff_of_pullback`: the linear-algebra core: if `ω(u, v) = ω₀(L u, L v)` for a
  continuous linear equivalence `L`, then `ω^♭` is onto iff `ω₀^♭` is.
* `Marsden.no_common_model`: the minimal version of the main theorem: for `x ≠ 0` there is no
  constant bilinear form `ω₀` on any normed space `F` with `Ω_{(0,0)} = L₀^* ω₀` and
  `Ω_{(x,0)} = L₁^* ω₀` for linear isomorphisms `L₀, L₁ : H × H ≃ F`. Only the isomorphisms at
  these two points matter.
* `Marsden.no_darboux_chart`: the chart version: there are no neighborhood `U` of `(0, 0)`, map
  `φ : H × H → H × H` and constant `ω₀` such that at every `p ∈ U` the derivative `dφ_p` is a
  continuous linear automorphism and `Ω_p(u, v) = ω₀(dφ_p u, dφ_p v)`. Neither `C¹` regularity of
  `φ` nor openness of `U` is assumed, so this is stronger than the nonexistence of Darboux charts.
* `Marsden.no_vector_bundle_chart`: the referee's remark in the paper (`Ω` cannot be made constant
  even by a vector bundle chart of `T(TM)`): no family of linear isomorphisms `L_p` of the fibers,
  continuous in `p` or not, carries `Ω_p` to a fixed form `Ω₀` at every point `p`.
* The concrete example (`Marsden.L2`): `H = ℓ²(ℕ, ℝ)` and `S = diag(1 / (n + 1))`. Then `S` is
  self-adjoint and positive (`Marsden.L2.S_symm`, `Marsden.L2.S_pos`), `a I + S` is onto for
  `a > 0`, being `diag(a + 1 / (n + 1))` with entries bounded below by `a`
  (`Marsden.L2.S_add_smul_surj`), and `S` is not onto: `(1 / (n + 1))ₙ ∈ ℓ²` would need the
  preimage `(1, 1, …) ∉ ℓ²` (`Marsden.L2.not_surjective_S`). Hence `Marsden.L2.no_darboux_chart`
  and `Marsden.L2.no_vector_bundle_chart`.

## Implementation notes

* **Conventions.** For a `1`-form `θ : E → E*` on a normed space we set
  `(dθ)_p(u, v) = Dθ_p(u)(v) - Dθ_p(v)(u)` (`DiffForm.d₁`), where `Dθ_p(u)(v)` is the derivative
  of `p ↦ θ_p(v)` in the direction `u`; this is `u(θ(v)) - v(θ(u))` for constant vector fields
  `u`, `v`. For a `2`-form we use the cyclic-sum formula
  `(dβ)_p(u, v, w) = Dβ_p(u)(v, w) + Dβ_p(v)(w, u) + Dβ_p(w)(u, v)` (`DiffForm.d₂`), which is the
  exterior derivative of an alternating `β`. On `H × H` let `θ_{(x,e)}(e₁, e₂) = g_x(e, e₁)`, the
  pullback of the canonical `1`-form by the Legendre map, and `Ω = -dθ` (`Marsden.Ω`). Then,
  with `u = (e₁, e₂)` and `v = (e₃, e₄)` (`Marsden.Ω_apply`),
  `Ω_{(x,e)}(u, v) = D_x(g(e, e₁))·e₃ - D_x(g(e, e₃))·e₁ + g_x(e₄, e₁) - g_x(e₂, e₃)`,
  which is exactly the right-hand side of Marsden's formula for `2 Ω` on p. 591. Thus our `Ω` is
  twice the form of the paper; the factor plays no role in nondegeneracy or in the existence of
  Darboux charts.
* **Deviations from the paper.** Marsden takes `S` compact with dense range and obtains that
  `a I + S` is onto from the Fredholm alternative. We assume directly what the proof uses: `S`
  self-adjoint, positive, not onto, and `a I + S` onto for `a > 0`; compactness and density of
  the range are not needed. For the concrete diagonal operator they hold anyway
  (`Marsden.L2.isCompactOperator_S`, `Marsden.L2.denseRange_S`). Marsden works with charts of a
  Banach manifold `TM`; here the manifold is the open set `H × H` itself, and a chart is a map
  with invertible derivative. The referee's remark in the paper is
  `Marsden.no_vector_bundle_chart`, with concrete instance `Marsden.L2.no_vector_bundle_chart`.
-/

@[expose] public section

open Set Filter Function
open scoped Topology NNReal ENNReal lp ContDiff RealInnerProductSpace

noncomputable section

namespace LocallyConvex.Analysis.Counterexamples

/-! ### Exterior derivatives on a normed space -/

namespace DiffForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exterior derivative of a `1`-form `θ : E → E*`:
`(dθ)_p(u, v) = Dθ_p(u)(v) - Dθ_p(v)(u)`, where `Dθ_p(u)(v) = fderiv ℝ θ p u v` is the derivative
of `p ↦ θ_p(v)` in the direction `u`. -/
def d₁ (θ : E → E →L[ℝ] ℝ) (p : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ θ p - (fderiv ℝ θ p).flip

@[simp]
theorem d₁_apply (θ : E → E →L[ℝ] ℝ) (p u v : E) :
    d₁ θ p u v = fderiv ℝ θ p u v - fderiv ℝ θ p v u := rfl

/-- `dθ` is alternating. -/
theorem d₁_antisymm (θ : E → E →L[ℝ] ℝ) (p u v : E) : d₁ θ p u v = -d₁ θ p v u := by
  simp

/-- The exterior derivative of a `2`-form `β : E → L²(E; ℝ)`, by the cyclic-sum formula
`(dβ)_p(u, v, w) = Dβ_p(u)(v, w) + Dβ_p(v)(w, u) + Dβ_p(w)(u, v)`, which is the standard formula
for an alternating `β`. -/
def d₂ (β : E → E →L[ℝ] E →L[ℝ] ℝ) (p u v w : E) : ℝ :=
  fderiv ℝ β p u v w + fderiv ℝ β p v w u + fderiv ℝ β p w u v

/-- The flip of bilinear forms, as a continuous linear map. -/
private abbrev flipL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem d₁_eq (θ : E → E →L[ℝ] ℝ) : d₁ θ = fun p ↦ fderiv ℝ θ p - flipL E (fderiv ℝ θ p) :=
  rfl

/-- If `θ` is `C^n` with `m + 1 ≤ n`, then `dθ` is `C^m`. -/
theorem contDiff_d₁ {θ : E → E →L[ℝ] ℝ} {m n : WithTop ℕ∞} (hθ : ContDiff ℝ n θ)
    (hmn : m + 1 ≤ n) : ContDiff ℝ m (d₁ θ) := by
  rw [d₁_eq]
  have h := hθ.fderiv_right hmn
  exact h.sub ((flipL E).contDiff.comp h)

/-- **`d ∘ d = 0` on `1`-forms.** If `θ` is `C²` at `p`, then `d(dθ)` vanishes at `p`. This is
the symmetry of the second derivative. -/
theorem d₂_d₁ {θ : E → E →L[ℝ] ℝ} {p : E} (hθ : ContDiffAt ℝ 2 θ p) (u v w : E) :
    d₂ (d₁ θ) p u v w = 0 := by
  have hD : DifferentiableAt ℝ (fderiv ℝ θ) p :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hs : IsSymmSndFDerivAt ℝ θ p := hθ.isSymmSndFDerivAt (by simp)
  have h := hD.hasFDerivAt.sub ((flipL E).hasFDerivAt.comp p hD.hasFDerivAt)
  replace h : HasFDerivAt (d₁ θ) _ p := h
  simp only [d₂, h.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, flipL,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearMap.coe_flipₗᵢ, ContinuousLinearMap.flip_apply]
  set D2 := fderiv ℝ (fderiv ℝ θ) p
  have e₁ : D2 u v w = D2 v u w := by rw [hs u v]
  have e₂ : D2 u w v = D2 w u v := by rw [hs u w]
  have e₃ : D2 v w u = D2 w v u := by rw [hs v w]
  linarith

end DiffForm

/-! ### Marsden's example -/

namespace Marsden

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The operator `A_x = S + ‖x‖² I`, applied to `e`. -/
def A (S : H →L[ℝ] H) (x e : H) : H := S e + ‖x‖ ^ 2 • e

/-- Marsden's weak metric `g_x(e, f) = (A_x e, f) = (S e, f) + ‖x‖² (e, f)`. -/
def g (S : H →L[ℝ] H) (x e f : H) : ℝ := ⟪A S x e, f⟫

/-- The `1`-form `θ` on `H × H`, `θ_{(x, e)}(e₁, e₂) = g_x(e, e₁)`: the pullback of the canonical
`1`-form of the cotangent bundle by the Legendre map `(x, e) ↦ (x, g_x(e, ·))`. -/
def θ (S : H →L[ℝ] H) (p : H × H) : H × H →L[ℝ] ℝ :=
  (innerSL ℝ (A S p.1 p.2)).comp (ContinuousLinearMap.fst ℝ H H)

/-- The `2`-form `Ω = -dθ` on `H × H`. With the conventions of this file it is twice the form
`Ω` of Marsden's paper (see `Ω_apply`). -/
def Ω (S : H →L[ℝ] H) : H × H → (H × H) →L[ℝ] (H × H) →L[ℝ] ℝ :=
  -DiffForm.d₁ (θ S)

variable (S : H →L[ℝ] H)

/-- `θ_{(x,e)}(e₁, e₂) = g_x(e, e₁)`. -/
theorem θ_apply (p v : H × H) : θ S p v = g S p.1 p.2 v.1 := by
  simp [θ, g, real_inner_comm]

/-- `(x, e) ↦ A_x e` is smooth. -/
theorem contDiff_A : ContDiff ℝ ∞ fun p : H × H ↦ A S p.1 p.2 :=
  (S.contDiff.comp contDiff_snd).add ((contDiff_norm_sq ℝ).comp contDiff_fst |>.smul contDiff_snd)

/-- `θ` is smooth. -/
theorem contDiff_θ : ContDiff ℝ ∞ (θ S) :=
  ((innerSL ℝ).contDiff.comp (contDiff_A S)).clm_comp contDiff_const

/-- **`Ω` is smooth.** -/
theorem contDiff_Ω : ContDiff ℝ ∞ (Ω S) :=
  (DiffForm.contDiff_d₁ (m := ∞) (contDiff_θ S) (by simp)).neg

/-- **`Ω` is exact**: `Ω = d(-θ)`, i.e. `Ω = -dθ`. -/
theorem Ω_eq_neg_d₁ : Ω S = -DiffForm.d₁ (θ S) := rfl

/-- **`Ω` is closed**: `dΩ = 0`, with the cyclic-sum formula for `d` of a `2`-form. -/
theorem d₂_Ω (p u v w : H × H) : DiffForm.d₂ (Ω S) p u v w = 0 := by
  have hθ : ContDiffAt ℝ 2 (θ S) p := (contDiff_θ S).contDiffAt.of_le (by simp)
  have h := DiffForm.d₂_d₁ hθ u v w
  simp only [DiffForm.d₂, Ω] at h ⊢
  rw [fderiv_neg]
  simp only [neg_apply]
  linarith

/-- `Ω` is alternating. -/
theorem Ω_antisymm (p u v : H × H) : Ω S p u v = -Ω S p v u := by
  simp [Ω]

/-- The derivative of `θ`: `Dθ_{(x,e)}(e₁, e₂)(e₃, e₄) = g_x(e₂, e₃) + 2 (x, e₁)(e, e₃)`. -/
theorem fderiv_θ_apply (p u v : H × H) :
    fderiv ℝ (θ S) p u v = g S p.1 u.2 v.1 + 2 * ⟪p.1, u.1⟫ * ⟪p.2, v.1⟫ := by
  have hθ : DifferentiableAt ℝ (θ S) p := (contDiff_θ S).differentiable (by simp) p
  have h1 : fderiv ℝ (θ S) p u v = fderiv ℝ (fun q ↦ θ S q v) p u := by
    rw [fderiv_clm_apply hθ (differentiableAt_const v)]
    simp
  rw [h1]
  set ℓ₁ : H × H →L[ℝ] ℝ := (innerSL ℝ v.1).comp (S.comp (ContinuousLinearMap.snd ℝ H H))
  set ℓ₂ : H × H →L[ℝ] ℝ := (innerSL ℝ v.1).comp (ContinuousLinearMap.snd ℝ H H)
  have hfun : (fun q ↦ θ S q v) = fun q ↦ ℓ₁ q + ‖q.1‖ ^ 2 * ℓ₂ q := by
    funext q
    simp [ℓ₁, ℓ₂, θ, A, real_inner_comm]
  have hd := ℓ₁.hasFDerivAt.add ((hasFDerivAt_fst (p := p)).norm_sq.mul ℓ₂.hasFDerivAt)
  rw [hfun, show (fun q ↦ ℓ₁ q + ‖q.1‖ ^ 2 * ℓ₂ q) = ⇑ℓ₁ + (fun x ↦ ‖x.1‖ ^ 2) * ⇑ℓ₂ from rfl,
    hd.fderiv]
  simp [ℓ₁, ℓ₂, g, A, inner_add_left, inner_smul_right, real_inner_comm]
  ring

/-- **Marsden's formula.** Writing `p = (x, e)`, `u = (e₁, e₂)`, `v = (e₃, e₄)`,
`Ω_p(u, v) = D_x(g(e, e₁))·e₃ - D_x(g(e, e₃))·e₁ + g_x(e₄, e₁) - g_x(e₂, e₃)`, where
`D_x(g(e, e₁))·e₃ = 2 (x, e₃)(e, e₁)`. -/
theorem Ω_apply (p u v : H × H) :
    Ω S p u v = 2 * ⟪p.1, v.1⟫ * ⟪p.2, u.1⟫ - 2 * ⟪p.1, u.1⟫ * ⟪p.2, v.1⟫
      + g S p.1 v.2 u.1 - g S p.1 u.2 v.1 := by
  simp only [Ω, neg_apply, Pi.neg_apply, DiffForm.d₁_apply, fderiv_θ_apply]
  ring

/-- At the zero section, `Ω_{(x,0)}(u, v) = g_x(e₄, e₁) - g_x(e₂, e₃)`. -/
theorem Ω_apply_zero_section (x : H) (u v : H × H) :
    Ω S (x, 0) u v = g S x v.2 u.1 - g S x u.2 v.1 := by
  simp [Ω_apply]

/-- `g_x(e, 0) = 0`. -/
theorem g_zero_right (x e : H) : g S x e 0 = 0 := by simp [g]

/-- `g_x(0, f) = 0`. -/
theorem g_zero_left (x f : H) : g S x 0 f = 0 := by simp [g, A]

/-- `g_x` is symmetric when `S` is. -/
theorem g_symm (hsymm : ∀ e f, ⟪S e, f⟫ = ⟪e, S f⟫) (x e f : H) : g S x e f = g S x f e := by
  simp only [g, A, inner_add_left, real_inner_smul_left, hsymm e f, real_inner_comm (S f) e,
    real_inner_comm f e]

/-- `g_x` is positive definite when `S` is. -/
theorem g_self_pos (hpos : ∀ e, e ≠ 0 → 0 < ⟪S e, e⟫) (x : H) {e : H} (he : e ≠ 0) :
    0 < g S x e e := by
  have := hpos e he
  simp only [g, A, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  positivity

/-! #### Nondegeneracy -/

/-- **`Ω` is weakly nondegenerate** at every point: `Ω_p^♭ : v ↦ Ω_p(v, ·)` is injective. -/
theorem injective_Ω (hpos : ∀ e, e ≠ 0 → 0 < ⟪S e, e⟫) (p : H × H) : Injective (Ω S p) := by
  refine (injective_iff_map_eq_zero (Ω S p)).mpr fun u hu ↦ ?_
  have h1 : u.1 = 0 := by
    by_contra hne
    have h := congrArg (fun φ : H × H →L[ℝ] ℝ ↦ φ (0, u.1)) hu
    simp only [Ω_apply, zero_apply, inner_zero_right, mul_zero, sub_zero,
      g_zero_right] at h
    linarith [g_self_pos S hpos p.1 hne]
  have h2 : u.2 = 0 := by
    by_contra hne
    have h := congrArg (fun φ : H × H →L[ℝ] ℝ ↦ φ (u.2, 0)) hu
    simp only [Ω_apply, zero_apply, h1, inner_zero_right, mul_zero,
      zero_mul, sub_zero, g_zero_right] at h
    linarith [g_self_pos S hpos p.1 hne]
  exact Prod.ext h1 h2

/-- **`Ω` is strongly nondegenerate along the zero section away from `0`**: if `x ≠ 0` then
`Ω_{(x,0)}^♭` is onto the dual. Here `A_x = S + ‖x‖² I` is onto, and the Riesz representation
theorem identifies `(H × H)*` with `H × H`. -/
theorem surjective_Ω_of_ne_zero [CompleteSpace H] (hsymm : ∀ e f, ⟪S e, f⟫ = ⟪e, S f⟫)
    (hsurj : ∀ a : ℝ, 0 < a → ∀ y, ∃ z, S z + a • z = y) {x : H} (hx : x ≠ 0) :
    Surjective (Ω S (x, 0)) := by
  intro φ
  have ha : 0 < ‖x‖ ^ 2 := by positivity
  obtain ⟨z₁, hz₁⟩ :=
    hsurj _ ha ((InnerProductSpace.toDual ℝ H).symm (φ.comp (ContinuousLinearMap.inr ℝ H H)))
  obtain ⟨z₂, hz₂⟩ :=
    hsurj _ ha (-(InnerProductSpace.toDual ℝ H).symm (φ.comp (ContinuousLinearMap.inl ℝ H H)))
  refine ⟨(z₁, z₂), ContinuousLinearMap.ext fun v ↦ ?_⟩
  have e₁ : g S x z₁ v.2 = φ (0, v.2) := by
    change ⟪S z₁ + ‖x‖ ^ 2 • z₁, v.2⟫ = _
    rw [hz₁, InnerProductSpace.toDual_symm_apply]
    simp
  have e₂ : g S x z₂ v.1 = -φ (v.1, 0) := by
    change ⟪S z₂ + ‖x‖ ^ 2 • z₂, v.1⟫ = _
    rw [hz₂, inner_neg_left, InnerProductSpace.toDual_symm_apply]
    simp
  have hv : φ v = φ (v.1, 0) + φ (0, v.2) := by rw [← map_add]; simp
  rw [Ω_apply_zero_section, g_symm S hsymm x v.2, e₁, e₂, hv]
  ring

/-- **`Ω` is not strongly nondegenerate at `(0, 0)`**: `Ω_{(0,0)}^♭` is not onto the dual,
because `g_0(e, f) = (S e, f)` and `S` is not onto. -/
theorem not_surjective_Ω_zero (hsymm : ∀ e f, ⟪S e, f⟫ = ⟪e, S f⟫) (hS : ¬ Surjective S) :
    ¬ Surjective (Ω S ((0 : H), (0 : H))) := by
  intro h
  obtain ⟨y, hy⟩ := not_forall.mp hS
  obtain ⟨u, hu⟩ := h ((innerSL ℝ y).comp (ContinuousLinearMap.snd ℝ H H))
  refine hy ⟨u.1, ext_inner_right ℝ fun f ↦ ?_⟩
  have h' := congrArg (fun φ : H × H →L[ℝ] ℝ ↦ φ (0, f)) hu
  simp only [Ω_apply_zero_section, g_zero_right, sub_zero] at h'
  simp only [g, A, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul,
    add_zero, ContinuousLinearMap.coe_comp, comp_apply, ContinuousLinearMap.coe_snd',
    innerSL_apply_apply] at h'
  rw [hsymm, real_inner_comm] at h'
  exact h'

end Marsden

/-! ### No Darboux chart -/

/-- Surjectivity of `β^♭` is invariant under pullback by a linear isomorphism: if
`β(u, v) = β₀(L u, L v)` for a continuous linear equivalence `L`, then `β^♭` is onto `E*` if and
only if `β₀^♭` is onto `F*`. -/
theorem surjective_iff_of_pullback {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {β : E →L[ℝ] E →L[ℝ] ℝ}
    {β₀ : F →L[ℝ] F →L[ℝ] ℝ} (L : E ≃L[ℝ] F) (h : ∀ u v, β u v = β₀ (L u) (L v)) :
    Surjective β ↔ Surjective β₀ := by
  constructor
  · intro hβ ψ
    obtain ⟨u, hu⟩ := hβ (ψ.comp (L : E →L[ℝ] F))
    refine ⟨L u, ContinuousLinearMap.ext fun y ↦ ?_⟩
    have := congrArg (fun φ : E →L[ℝ] ℝ ↦ φ (L.symm y)) hu
    simpa [h] using this
  · intro hβ₀ φ
    obtain ⟨w, hw⟩ := hβ₀ (φ.comp (L.symm : F →L[ℝ] E))
    refine ⟨L.symm w, ContinuousLinearMap.ext fun v ↦ ?_⟩
    have := congrArg (fun ψ : F →L[ℝ] ℝ ↦ ψ (L v)) hw
    simpa [h] using this

namespace Marsden

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : H →L[ℝ] H)

/-- **No linear model at `(0, 0)` and `(x, 0)` simultaneously.** For `x ≠ 0` there is no constant
continuous bilinear form `β₀` on a normed space `F` together with linear isomorphisms
`L₀, L₁ : H × H ≃ F` such that `Ω_{(0,0)} = L₀^* β₀` and `Ω_{(x,0)} = L₁^* β₀`. -/
theorem no_common_model (hsymm : ∀ e f, ⟪S e, f⟫ = ⟪e, S f⟫)
    (hsurj : ∀ a : ℝ, 0 < a → ∀ y, ∃ z, S z + a • z = y) (hS : ¬ Surjective S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (β₀ : F →L[ℝ] F →L[ℝ] ℝ)
    {x : H} (hx : x ≠ 0) (L₀ L₁ : (H × H) ≃L[ℝ] F)
    (h₀ : ∀ u v, Ω S ((0 : H), (0 : H)) u v = β₀ (L₀ u) (L₀ v))
    (h₁ : ∀ u v, Ω S (x, 0) u v = β₀ (L₁ u) (L₁ v)) : False :=
  not_surjective_Ω_zero S hsymm hS <| (surjective_iff_of_pullback L₀ h₀).mpr <|
    (surjective_iff_of_pullback L₁ h₁).mp (surjective_Ω_of_ne_zero S hsymm hsurj hx)

/-- **Darboux's theorem fails for `Ω` at `(0, 0)`** (Marsden). There is no neighborhood `U` of
`(0, 0)`, map `φ : H × H → H × H` and constant continuous bilinear form `β₀` such that at every
`p ∈ U` the derivative `dφ_p` is a continuous linear automorphism of `H × H` and
`Ω_p(u, v) = β₀(dφ_p u, dφ_p v)`. -/
theorem no_darboux_chart (hsymm : ∀ e f, ⟪S e, f⟫ = ⟪e, S f⟫)
    (hsurj : ∀ a : ℝ, 0 < a → ∀ y, ∃ z, S z + a • z = y) (hS : ¬ Surjective S) :
    ¬ ∃ U ∈ 𝓝 ((0 : H), (0 : H)), ∃ (φ : H × H → H × H) (β₀ : (H × H) →L[ℝ] (H × H) →L[ℝ] ℝ),
      ∀ p ∈ U, ∃ L : (H × H) ≃L[ℝ] (H × H), fderiv ℝ φ p = L ∧
        ∀ u v, Ω S p u v = β₀ (L u) (L v) := by
  rintro ⟨U, hU, φ, β₀, h⟩
  -- `H ≠ 0`, since `S` is not onto
  obtain ⟨y, hy⟩ : ∃ y : H, y ≠ 0 := by
    by_contra! h0
    exact hS fun z ↦ ⟨0, by rw [h0 z, map_zero]⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  set x : H := (r / (2 * ‖y‖)) • y
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hxn : ‖x‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hxn
    linarith
  have hxU : (x, (0 : H)) ∈ U := hball (by
    rw [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_mk, hxn,
      norm_zero, max_eq_left (by positivity)]
    linarith)
  obtain ⟨L₀, -, h₀⟩ := h _ (mem_of_mem_nhds hU)
  obtain ⟨L₁, -, h₁⟩ := h _ hxU
  exact no_common_model S hsymm hsurj hS β₀ hx L₀ L₁ h₀ h₁

/-- **No vector bundle chart of `T(H × H)` makes `Ω` constant near `(0, 0)`** (the referee's remark
in Marsden's paper, p. 592). There are no neighborhood `U` of `(0, 0)`, constant continuous
bilinear form `β₀` on a normed space `F` and linear isomorphisms `L_p : H × H ≃ F`, `p ∈ U`, with
`Ω_p(u, v) = β₀(L_p u, L_p v)`; no continuity of `p ↦ L_p` is assumed. -/
theorem no_vector_bundle_chart (hsymm : ∀ e f, ⟪S e, f⟫ = ⟪e, S f⟫)
    (hsurj : ∀ a : ℝ, 0 < a → ∀ y, ∃ z, S z + a • z = y) (hS : ¬ Surjective S)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (β₀ : F →L[ℝ] F →L[ℝ] ℝ)
    (L : H × H → (H × H) ≃L[ℝ] F) :
    ¬ ∃ U ∈ 𝓝 ((0 : H), (0 : H)), ∀ p ∈ U, ∀ u v, Ω S p u v = β₀ (L p u) (L p v) := by
  rintro ⟨U, hU, h⟩
  obtain ⟨y, hy⟩ : ∃ y : H, y ≠ 0 := by
    by_contra! h0
    exact hS fun z ↦ ⟨0, by rw [h0 z, map_zero]⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  set x : H := (r / (2 * ‖y‖)) • y
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hxn : ‖x‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hx : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hxn
    linarith
  have hxU : (x, (0 : H)) ∈ U := hball (by
    rw [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_mk, hxn,
      norm_zero, max_eq_left (by positivity)]
    linarith)
  exact no_common_model S hsymm hsurj hS β₀ hx (L _) (L _) (h _ (mem_of_mem_nhds hU))
    (h _ hxU)

end Marsden

/-! ### The concrete example on `ℓ²` -/

namespace Marsden.L2

/-- The Hilbert space `ℓ²(ℕ, ℝ)`. -/
abbrev H := lp (fun _ : ℕ ↦ ℝ) 2

/-- The diagonal operator `S x = (xₙ / (n + 1))ₙ`, as a linear map. -/
def diagLin : H →ₗ[ℝ] H where
  toFun x := ⟨fun n ↦ x n / ((n : ℝ) + 1), (lp.memℓp x).norm.mono fun n ↦ by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (by
      rw [Real.norm_of_nonneg (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)])⟩
  map_add' x y := lp.ext <| funext fun n ↦ add_div (x n) (y n) _
  map_smul' c x := lp.ext <| funext fun n ↦ mul_div_assoc c (x n) _

/-- The diagonal operator `S = diag(1 / (n + 1))` on `ℓ²`. -/
def S : H →L[ℝ] H :=
  diagLin.mkContinuous 1 fun x ↦ by
    rw [one_mul]
    refine lp.norm_mono (by norm_num) fun n ↦ ?_
    change ‖x n / ((n : ℝ) + 1)‖ ≤ ‖x n‖
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (by
      rw [Real.norm_of_nonneg (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)])

@[simp]
theorem S_apply (x : H) (n : ℕ) : S x n = x n / ((n : ℝ) + 1) := rfl

/-- `S` is self-adjoint. -/
theorem S_symm (e f : H) : ⟪S e, f⟫ = ⟪e, S f⟫ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  simp
  ring

/-- `S` is positive: `(S e, e) > 0` for `e ≠ 0`. -/
theorem S_pos (e : H) (he : e ≠ 0) : 0 < ⟪S e, e⟫ := by
  have he' : (e : ℕ → ℝ) ≠ 0 := fun h ↦ he (lp.ext (h.trans (lp.coeFn_zero _ _).symm))
  obtain ⟨n, hn⟩ := Function.ne_iff.mp he'
  have hn' : e n ≠ 0 := hn
  have hi : ∀ i, ⟪S e i, e i⟫ = e i * e i / ((i : ℝ) + 1) := fun i ↦ by
    rw [S_apply, real_inner_eq_re_inner]
    simp
    ring
  rw [lp.inner_eq_tsum]
  have hs : Summable fun i ↦ ⟪S e i, e i⟫ := lp.summable_inner (S e) e
  simp only [hi] at hs ⊢
  exact hs.tsum_pos (fun i ↦ div_nonneg (mul_self_nonneg _) (by positivity)) n
    (div_pos (mul_self_pos.mpr hn') (by positivity))

/-- `a I + S` is onto for every `a > 0`: it is the diagonal operator `diag(a + 1 / (n + 1))`, whose
entries are bounded below by `a`. -/
theorem S_add_smul_surj (a : ℝ) (ha : 0 < a) (y : H) : ∃ z, S z + a • z = y := by
  refine ⟨⟨fun n ↦ y n / (a + 1 / ((n : ℝ) + 1)),
    ((lp.memℓp y).norm.const_mul a⁻¹).mono fun n ↦ ?_⟩, lp.ext (funext fun n ↦ ?_)⟩
  · have hc : ‖a + 1 / ((n : ℝ) + 1)‖ = a + 1 / ((n : ℝ) + 1) := Real.norm_of_nonneg (by positivity)
    rw [norm_div, hc, div_le_iff₀ (by positivity)]
    have hy : 0 ≤ ‖y n‖ := norm_nonneg _
    calc ‖y n‖ = a⁻¹ * ‖y n‖ * a := by field_simp
      _ ≤ a⁻¹ * ‖y n‖ * (a + 1 / ((n : ℝ) + 1)) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · have hc : 0 < a + 1 / ((n : ℝ) + 1) := by positivity
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, S_apply, smul_eq_mul]
    change y n / (a + 1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1) + a * (y n / (a + 1 / ((n : ℝ) + 1)))
      = y n
    field_simp
    ring

/-- `S` is not onto: `(1 / (n + 1))ₙ ∈ ℓ²` is not in its range, since its only preimage under the
diagonal operator would be the constant sequence `1`. -/
theorem not_surjective_S : ¬ Surjective S := by
  intro h
  have hw : Memℓp (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) 2 := by
    refine memℓp_gen ?_
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have hs := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    refine hs.congr fun n ↦ ?_
    rw [h2, Real.rpow_two, Real.norm_of_nonneg (by positivity), div_pow, one_pow]
    push_cast
    ring
  obtain ⟨z, hz⟩ := h ⟨_, hw⟩
  have hz1 : ∀ n, z n = 1 := fun n ↦ by
    have := congrArg (fun w : H ↦ w n) hz
    simp only [S_apply] at this
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp at this
    exact this
  have := (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simp only [hz1, norm_one, Real.one_rpow] at this
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp this)

/-- **Marsden's example on `ℓ²`.** `Ω` is weakly nondegenerate everywhere. -/
theorem injective_Ω (p : H × H) : Injective (Ω S p) :=
  Marsden.injective_Ω S S_pos p

/-- `Ω_{(x,0)}^♭` is onto for `x ≠ 0`. -/
theorem surjective_Ω_of_ne_zero {x : H} (hx : x ≠ 0) : Surjective (Ω S (x, 0)) :=
  Marsden.surjective_Ω_of_ne_zero S S_symm S_add_smul_surj hx

/-- `Ω_{(0,0)}^♭` is not onto. -/
theorem not_surjective_Ω_zero : ¬ Surjective (Ω S ((0 : H), (0 : H))) :=
  Marsden.not_surjective_Ω_zero S S_symm not_surjective_S

/-- **Darboux's theorem fails for the weak symplectic form `Ω` on `ℓ² × ℓ²`** (Marsden). -/
theorem no_darboux_chart :
    ¬ ∃ U ∈ 𝓝 ((0 : H), (0 : H)), ∃ (φ : H × H → H × H) (β₀ : (H × H) →L[ℝ] (H × H) →L[ℝ] ℝ),
      ∀ p ∈ U, ∃ L : (H × H) ≃L[ℝ] (H × H), fderiv ℝ φ p = L ∧
        ∀ u v, Ω S p u v = β₀ (L u) (L v) :=
  Marsden.no_darboux_chart S S_symm S_add_smul_surj not_surjective_S

/-! #### `S` is compact with dense range -/

/-- The truncation `S_N x = (x₀ / 1, …, x_{N-1} / N, 0, 0, …)`, a finite-rank operator. -/
def truncS (N : ℕ) : H →L[ℝ] H :=
  (∑ i : Fin N, (lp.singleContinuousLinearMap ℝ (fun _ : ℕ ↦ ℝ) 2 (i : ℕ)).comp
    ((1 / ((i : ℝ) + 1)) • ContinuousLinearMap.proj i)).comp
    (ContinuousLinearMap.pi fun i : Fin N ↦ lp.evalCLM ℝ (fun _ : ℕ ↦ ℝ) 2 (i : ℕ))

theorem truncS_apply (N : ℕ) (x : H) (n : ℕ) :
    truncS N x n = if n < N then x n / ((n : ℝ) + 1) else 0 := by
  simp only [truncS, ContinuousLinearMap.comp_apply, FunLike.coe_sum,
    Finset.sum_apply, lp.coeFn_sum]
  split_ifs with hn
  · rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp [lp.evalCLM, div_eq_inv_mul]
    · intro i _ hi
      have : (n : ℕ) ≠ i := fun h ↦ hi (Fin.ext h.symm)
      simp [Pi.single_eq_of_ne this]
    · simp
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    have : n ≠ (i : ℕ) := fun h ↦ hn (h ▸ i.2)
    simp [Pi.single_eq_of_ne this]

theorem isCompactOperator_truncS (N : ℕ) : IsCompactOperator (truncS N) :=
  (isCompactOperator_of_locallyCompactSpace_rng _).comp_clm _

theorem norm_S_sub_truncS_le (N : ℕ) : ‖S - truncS N‖ ≤ 1 / ((N : ℝ) + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ ?_
  have : ‖(S - truncS N) x‖ ≤ ‖(1 / ((N : ℝ) + 1)) • x‖ := by
    refine lp.norm_mono (by norm_num) fun n ↦ ?_
    change ‖(S x - truncS N x) n‖ ≤ ‖(1 / ((N : ℝ) + 1)) • x n‖
    rw [lp.coeFn_sub, Pi.sub_apply, S_apply, truncS_apply]
    split_ifs with hn
    · rw [sub_self, norm_zero]
      exact norm_nonneg _
    · rw [sub_zero, norm_div, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1),
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N + 1)), div_eq_inv_mul,
        one_div]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ (not_lt.1 hn))
  rwa [norm_smul, Real.norm_of_nonneg (by positivity)] at this

/-- **The diagonal operator `S = diag(1 / (n + 1))` is compact**, as a norm limit of finite-rank
operators (Marsden's hypothesis on `S`). -/
theorem isCompactOperator_S : IsCompactOperator S := by
  refine isCompactOperator_of_tendsto (l := Filter.atTop) (F := truncS) ?_
    (Filter.Eventually.of_forall isCompactOperator_truncS)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun N ↦ norm_nonneg _) (fun N ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact norm_S_sub_truncS_le N

/-- **The diagonal operator `S` has dense range** (Marsden's hypothesis on `S`): its range
contains the finitely supported sequences. -/
theorem denseRange_S : DenseRange S := by
  intro f
  have hsingle : ∀ (i : ℕ) (c : ℝ), (lp.single 2 i c : H) ∈ LinearMap.range (S : H →ₗ[ℝ] H) := by
    intro i c
    refine ⟨(lp.single 2 i (c * ((i : ℝ) + 1)) : H), lp.ext (funext fun n ↦ ?_)⟩
    change S (lp.single 2 i (c * ((i : ℝ) + 1)) : H) n = (lp.single 2 i c : H) n
    rw [S_apply]
    by_cases hn : n = i
    · subst hn
      rw [lp.single_apply_self, lp.single_apply_self]
      field_simp
    · rw [lp.single_apply_ne _ _ _ hn, lp.single_apply_ne _ _ _ hn, zero_div]
  have hsum := lp.hasSum_single (E := fun _ : ℕ ↦ ℝ) (p := 2) (by norm_num) f
  refine mem_closure_of_tendsto hsum (Filter.Eventually.of_forall fun s ↦ ?_)
  exact (LinearMap.range (S : H →ₗ[ℝ] H)).sum_mem fun i _ ↦ hsingle i (f i)

/-- **The referee's remark for the concrete example**: no vector bundle chart of `T(H × H)` makes
`Ω` constant near `(0, 0)`. -/
theorem no_vector_bundle_chart {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β₀ : F →L[ℝ] F →L[ℝ] ℝ) (L : H × H → (H × H) ≃L[ℝ] F) :
    ¬ ∃ U ∈ 𝓝 ((0 : H), (0 : H)), ∀ p ∈ U, ∀ u v, Ω S p u v = β₀ (L p u) (L p v) :=
  Marsden.no_vector_bundle_chart S S_symm S_add_smul_surj not_surjective_S β₀ L

end Marsden.L2

end LocallyConvex.Analysis.Counterexamples

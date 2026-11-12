/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Frobenius.Chart
public import LocallyConvexAnalysis.Complex.NormedComplexification

/-!
# The Nijenhuis tensor and the involutivity of `ker(F + i)`

For a field of operators `A : G → L(G)` on a normed space `G`, the **Nijenhuis tensor** at `z` is
the bilinear map
`N_A(z)(a, b) = DA(z)(A a) b − DA(z)(A b) a + A (DA(z)(b) a) − A (DA(z)(a) b)`
(`nijenhuis`), where `A = A(z)`. It is the value at `z` of
`N_A(X, Y) = [AX, AY] + A²[X, Y] − A[X, AY] − A[AX, Y]` for any vector fields `X`, `Y`
differentiable at `z` with `X z = a`, `Y z = b` (`nijenhuis_apply_eq`): the expression is tensorial.
This is the form used by J.-P. Penot, *Sur le théorème de Frobenius*, Bull. Soc. Math. France 98
(1970), §3, p. 73.

On a complex Banach space, let `F` be a holomorphic field of operators with `F² = −1`. The
**main result** (`lieBracket_mem_ker_of_nijenhuis`) is the step (4) ⇒ (6) of Penot's
Théorème 3.5 (pp. 73–75): if `N_F(z) = 0`, then the distribution `p ↦ ker(F(p) + i)` (the vectors
of type `(0, 1)`) is involutive at `z`. We prove it directly: differentiating `F² = −1` shows that
`DF(z)(v)` anticommutes with `F(z)`, so it maps `ker(F + i)` into `ker(F − i)`; for `Z`, `W` of
type `(0, 1)` the vector `c = DF(W) Z − DF(Z) W` therefore lies in `ker(F − i)`, while
`N_F(Z, W) = (F + i) c` puts it in `ker(F + i)`. Hence `c = 0`, and `(F + i)[Z, W] = c`.
Penot passes instead through the projector `P = (1 − iF)/2` and the identity `N_F = −4 N_P`.

The **complexification** of a field `J` of real operators is handled in `nijenhuis_ofReal`: if
`F(x + i0)` extends `J(x)` complex linearly for real `x` near `x₀`, then
`N_F(x₀)(a + i0, b + i0) = N_J(x₀)(a, b) + i0`, so `N_J(x₀) = 0` implies `N_F(x₀) = 0`
(`nijenhuis_eq_zero_of_ofReal`). This is Penot's (2) ⇒ (4).

Finally, the **graph form** (`exists_graph_frob_of_nijenhuis`): fix `z₀` and `A = F(z₀)`. The
projections `Q = (1 + iA)/2` and `P = (1 − iA)/2` split `G ≅ ker(A + i) × ker(A − i)`
(`typeSplit`). For `z` near `z₀`, `ker(F(z) + i)` is the image of `ker(A + i)` under
`Q_z = (1 + iF(z))/2`, hence the graph of `g(z) = T_z S_z⁻¹` with `S_z = Q Q_z` and `T_z = P Q_z`
restricted to `ker(A + i)` (`apply_eq_neg_I_iff_graph`; the invertibility of `S_z` and
`‖Q_z − Q‖ < 1` hold near `z₀`). The map `g` is holomorphic, and by the involutivity above and
`lieBracket_mem_graph_iff` it satisfies Penot's condition (Frob). This is the input of the
holomorphic Frobenius theorem in Penot's proof of (6) ⇒ (1) (p. 75). Penot extends the projector
instead and invokes his Théorème 2.3 for projectors; we do not claim the graph argument is new.

## Main results

* `nijenhuis`, `nijenhuis_apply_eq`: the Nijenhuis tensor and its tensoriality.
* `lieBracket_mem_ker_of_nijenhuis`: `N_F = 0` ⇒ `ker(F + i)` involutive.
* `nijenhuis_ofReal`, `nijenhuis_eq_zero_of_ofReal`: complexification.
* `typeSplit`, `apply_eq_neg_I_iff_graph`, `exists_graph_frob_of_nijenhuis`: the graph form and
  (Frob).

## References

* [J.-P. Penot, *Sur le théorème de Frobenius*][Pen70]
-/

@[expose] public section

open Set Filter
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

section Nijenhuis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/-- The **Nijenhuis tensor** of a field of operators `A` at `z`:
`N_A(z)(a, b) = DA(z)(A a) b − DA(z)(A b) a + A (DA(z)(b) a) − A (DA(z)(a) b)`. -/
def nijenhuis (A : G → G →L[𝕜] G) (z : G) : G →ₗ[𝕜] G →ₗ[𝕜] G :=
  LinearMap.mk₂ 𝕜
    (fun a b ↦ fderiv 𝕜 A z (A z a) b - fderiv 𝕜 A z (A z b) a +
      A z (fderiv 𝕜 A z b a) - A z (fderiv 𝕜 A z a b))
    (fun a a' b ↦ by simp only [map_add, add_apply]; abel)
    (fun c a b ↦ by
      simp only [map_smul, smul_apply, smul_sub, smul_add])
    (fun a b b' ↦ by simp only [map_add, add_apply]; abel)
    (fun c a b ↦ by
      simp only [map_smul, smul_apply, smul_sub, smul_add])

theorem nijenhuis_apply (A : G → G →L[𝕜] G) (z a b : G) :
    nijenhuis 𝕜 A z a b = fderiv 𝕜 A z (A z a) b - fderiv 𝕜 A z (A z b) a +
      A z (fderiv 𝕜 A z b a) - A z (fderiv 𝕜 A z a b) := rfl

/-- The derivative of `p ↦ A(p) X(p)`. -/
theorem fderiv_clm_apply_field {A : G → G →L[𝕜] G} {X : G → G} {z : G}
    (hA : DifferentiableAt 𝕜 A z) (hX : DifferentiableAt 𝕜 X z) (v : G) :
    fderiv 𝕜 (fun p ↦ A p (X p)) z v = fderiv 𝕜 A z v (X z) + A z (fderiv 𝕜 X z v) := by
  rw [(hA.hasFDerivAt.clm_apply hX.hasFDerivAt).fderiv]
  simp [add_comm]

/-- **The Nijenhuis tensor is tensorial**: for vector fields `X`, `Y` differentiable at `z`,
`N_A(z)(X z, Y z) = [AX, AY] + A²[X, Y] − A[X, AY] − A[AX, Y]` at `z`. -/
theorem nijenhuis_apply_eq {A : G → G →L[𝕜] G} {X Y : G → G} {z : G}
    (hA : DifferentiableAt 𝕜 A z) (hX : DifferentiableAt 𝕜 X z) (hY : DifferentiableAt 𝕜 Y z) :
    nijenhuis 𝕜 A z (X z) (Y z) =
      VectorField.lieBracket 𝕜 (fun p ↦ A p (X p)) (fun p ↦ A p (Y p)) z +
        A z (A z (VectorField.lieBracket 𝕜 X Y z)) -
        A z (VectorField.lieBracket 𝕜 X (fun p ↦ A p (Y p)) z) -
        A z (VectorField.lieBracket 𝕜 (fun p ↦ A p (X p)) Y z) := by
  simp only [VectorField.lieBracket_eq, fderiv_clm_apply_field hA hX,
    fderiv_clm_apply_field hA hY, nijenhuis_apply, map_sub, map_add]
  abel

end Nijenhuis

section Involutive

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Differentiating `F² = −1`: `DF(z)(v)` anticommutes with `F(z)`. -/
theorem fderiv_anticomm_of_sq_eq_neg_one {F : G → G →L[ℂ] G} {z : G}
    (hF : DifferentiableAt ℂ F z)
    (hsq : ∀ᶠ p in 𝓝 z, (F p).comp (F p) = -ContinuousLinearMap.id ℂ G) (v w : G) :
    fderiv ℂ F z v (F z w) + F z (fderiv ℂ F z v w) = 0 := by
  have h1 := hF.hasFDerivAt.clm_comp hF.hasFDerivAt
  have h2 : HasFDerivAt (fun p ↦ (F p).comp (F p)) (0 : G →L[ℂ] G →L[ℂ] G) z :=
    (hasFDerivAt_const (-ContinuousLinearMap.id ℂ G) z).congr_of_eventuallyEq hsq
  have := congrArg (fun L : G →L[ℂ] G →L[ℂ] G ↦ L v w) (h1.unique h2)
  simpa [add_comm] using this

/-- Differentiating `F Z = −i Z`. -/
theorem fderiv_of_mem_ker {F : G → G →L[ℂ] G} {Z : G → G} {z : G}
    (hF : DifferentiableAt ℂ F z) (hZ : DifferentiableAt ℂ Z z)
    (hZF : ∀ᶠ p in 𝓝 z, F p (Z p) = -(Complex.I • Z p)) (v : G) :
    fderiv ℂ F z v (Z z) + F z (fderiv ℂ Z z v) = -(Complex.I • fderiv ℂ Z z v) := by
  have h1 := hF.hasFDerivAt.clm_apply hZ.hasFDerivAt
  have h2 := ((hZ.hasFDerivAt.const_smul Complex.I).neg).congr_of_eventuallyEq hZF
  have := congrArg (fun L : G →L[ℂ] G ↦ L v) (h1.unique h2)
  simpa [add_comm] using this

/-- **Vanishing Nijenhuis tensor gives an involutive `(0, 1)` distribution** ([Pen70, Théorème 3.5],
(4) ⇒ (6), pp. 73–75). Let `F` be differentiable at `z` with `F(p)² = −1` near `z` and
`N_F(z) = 0`. If `Z`, `W` are differentiable at `z` and of type `(0, 1)` near `z`
(`F Z = −i Z`, `F W = −i W`), then so is `[Z, W]` at `z`. -/
theorem lieBracket_mem_ker_of_nijenhuis {F : G → G →L[ℂ] G} {z : G}
    (hF : DifferentiableAt ℂ F z)
    (hsq : ∀ᶠ p in 𝓝 z, (F p).comp (F p) = -ContinuousLinearMap.id ℂ G)
    (hN : nijenhuis ℂ F z = 0) {Z W : G → G} (hZ : DifferentiableAt ℂ Z z)
    (hW : DifferentiableAt ℂ W z) (hZF : ∀ᶠ p in 𝓝 z, F p (Z p) = -(Complex.I • Z p))
    (hWF : ∀ᶠ p in 𝓝 z, F p (W p) = -(Complex.I • W p)) :
    F z (VectorField.lieBracket ℂ Z W z) = -(Complex.I • VectorField.lieBracket ℂ Z W z) := by
  set I := Complex.I
  have hZz : F z (Z z) = -(I • Z z) := hZF.self_of_nhds
  have hWz : F z (W z) = -(I • W z) := hWF.self_of_nhds
  set c := fderiv ℂ F z (W z) (Z z) - fderiv ℂ F z (Z z) (W z) with hc
  -- `c ∈ ker(F − i)`, since `DF(v)` anticommutes with `F`
  have hac := fderiv_anticomm_of_sq_eq_neg_one hF hsq
  have hc1 : F z c = I • c := by
    have e1 := hac (W z) (Z z)
    have e2 := hac (Z z) (W z)
    rw [hZz, map_neg, map_smul] at e1
    rw [hWz, map_neg, map_smul] at e2
    rw [hc, map_sub, smul_sub]
    rw [← sub_eq_zero]
    linear_combination (norm := module) e1 - e2
  -- `c ∈ ker(F + i)`, from `N_F(Z, W) = 0`
  have hc2 : F z c = -(I • c) := by
    have e := LinearMap.congr_fun₂ hN (Z z) (W z)
    rw [nijenhuis_apply, hZz, hWz, map_neg, map_neg, map_smul, map_smul] at e
    simp only [LinearMap.zero_apply, FunLike.coe_neg, Pi.neg_apply,
      smul_apply] at e
    rw [hc, map_sub, smul_sub, ← sub_eq_zero]
    linear_combination (norm := module) e
  have hc0 : c = 0 := by
    have : (2 * I) • c = 0 := by linear_combination (norm := module) hc2 - hc1
    exact (smul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  -- `(F + i)[Z, W] = c`
  have hdZ := fderiv_of_mem_ker hF hZ hZF (W z)
  have hdW := fderiv_of_mem_ker hF hW hWF (Z z)
  rw [VectorField.lieBracket_eq, map_sub, smul_sub]
  have : c = 0 := hc0
  rw [hc] at this
  linear_combination (norm := module) hdW - hdZ + this

end Involutive

section Complexified

open NormedComplexification Complexification

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every `p ∈ E_ℂ` is `Re p + i Im p`. -/
theorem NormedComplexification.eq_ofRealCLM_add_I_smul (p : NormedComplexification E) :
    p = ofRealCLM (re (toCx p)) + Complex.I • ofRealCLM (im (toCx p)) := by
  change toCx p = ofReal (re (toCx p)) + Complex.I • ofReal (im (toCx p))
  ext <;> simp

/-- A complex bilinear map on `E_ℂ` vanishing on real vectors vanishes. -/
theorem NormedComplexification.bilinear_ext {X : Type*} [AddCommGroup X] [Module ℂ X]
    {B : NormedComplexification E →ₗ[ℂ] NormedComplexification E →ₗ[ℂ] X}
    (h : ∀ a b : E, B (ofRealCLM a) (ofRealCLM b) = 0) : B = 0 := by
  ext p q
  rw [eq_ofRealCLM_add_I_smul p, eq_ofRealCLM_add_I_smul q]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, h, smul_zero,
    add_zero, LinearMap.zero_apply]

/-- If `F(x + i0)` extends `J(x)` complex linearly for real `x` near `x₀`, then the derivative of
`F` at `x₀ + i0` in real directions extends the derivative of `J`. -/
theorem fderiv_ofReal_of_extends {J : E → E →L[ℝ] E}
    {F : NormedComplexification E → NormedComplexification E →L[ℂ] NormedComplexification E}
    {x : E} (hJ : DifferentiableAt ℝ J x) (hF : DifferentiableAt ℂ F (ofRealCLM x))
    (hext : ∀ᶠ y in 𝓝 x, ∀ b, F (ofRealCLM y) (ofRealCLM b) = ofRealCLM (J y b)) (a b : E) :
    fderiv ℂ F (ofRealCLM x) (ofRealCLM a) (ofRealCLM b) = ofRealCLM (fderiv ℝ J x a b) := by
  have h1 := ((ContinuousLinearMap.apply ℂ _ (ofRealCLM b)).restrictScalars ℝ).hasFDerivAt.comp x
    ((hF.hasFDerivAt.restrictScalars ℝ).comp x (ofRealCLM (E := E)).hasFDerivAt)
  have h2 := (ofRealCLM (E := E)).hasFDerivAt.comp x
    ((ContinuousLinearMap.apply ℝ E b).hasFDerivAt.comp x hJ.hasFDerivAt)
  have h3 := h2.congr_of_eventuallyEq (hext.mono fun y hy ↦ hy b)
  have := congrArg (fun L : E →L[ℝ] NormedComplexification E ↦ L a) (h1.unique h3)
  simpa using this

/-- **The Nijenhuis tensor of a complexification** ([Pen70, Théorème 3.5], (2) ⇒ (4), p. 74): if
`F(x + i0)` extends `J(x)` complex linearly for real `x` near `x₀`, then
`N_F(x₀)(a + i0, b + i0) = N_J(x₀)(a, b) + i0`. -/
theorem nijenhuis_ofReal {J : E → E →L[ℝ] E}
    {F : NormedComplexification E → NormedComplexification E →L[ℂ] NormedComplexification E}
    {x : E} (hJ : DifferentiableAt ℝ J x) (hF : DifferentiableAt ℂ F (ofRealCLM x))
    (hext : ∀ᶠ y in 𝓝 x, ∀ b, F (ofRealCLM y) (ofRealCLM b) = ofRealCLM (J y b)) (a b : E) :
    nijenhuis ℂ F (ofRealCLM x) (ofRealCLM a) (ofRealCLM b) =
      ofRealCLM (nijenhuis ℝ J x a b) := by
  have hself : ∀ b, F (ofRealCLM x) (ofRealCLM b) = ofRealCLM (J x b) := hext.self_of_nhds
  have hD := fderiv_ofReal_of_extends hJ hF hext
  simp only [nijenhuis_apply, hself, hD, map_sub, map_add]

/-- If `J` has vanishing Nijenhuis tensor at `x₀`, so does its complex extension `F`. -/
theorem nijenhuis_eq_zero_of_ofReal {J : E → E →L[ℝ] E}
    {F : NormedComplexification E → NormedComplexification E →L[ℂ] NormedComplexification E}
    {x : E} (hJ : DifferentiableAt ℝ J x) (hF : DifferentiableAt ℂ F (ofRealCLM x))
    (hext : ∀ᶠ y in 𝓝 x, ∀ b, F (ofRealCLM y) (ofRealCLM b) = ofRealCLM (J y b))
    (hN : nijenhuis ℝ J x = 0) : nijenhuis ℂ F (ofRealCLM x) = 0 :=
  bilinear_ext fun a b ↦ by
    rw [nijenhuis_ofReal hJ hF hext, hN]; simp only [LinearMap.zero_apply, map_zero]

end Complexified

section Conj

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The Lie bracket commutes with a linear change of variables. -/
theorem lieBracket_comp_equiv (ℓ : E ≃L[𝕜] F) {V W : F → F} {y : E}
    (hV : DifferentiableAt 𝕜 V (ℓ y)) (hW : DifferentiableAt 𝕜 W (ℓ y)) :
    VectorField.lieBracket 𝕜 (fun y ↦ ℓ.symm (V (ℓ y))) (fun y ↦ ℓ.symm (W (ℓ y))) y =
      ℓ.symm (VectorField.lieBracket 𝕜 V W (ℓ y)) := by
  have hd : ∀ {Z : F → F}, DifferentiableAt 𝕜 Z (ℓ y) →
      HasFDerivAt (fun y ↦ ℓ.symm (Z (ℓ y)))
        ((ℓ.symm : F →L[𝕜] E).comp ((fderiv 𝕜 Z (ℓ y)).comp (ℓ : E →L[𝕜] F))) y :=
    fun hZ ↦ ℓ.symm.hasFDerivAt.comp y (hZ.hasFDerivAt.comp y ℓ.hasFDerivAt)
  rw [VectorField.lieBracket_eq, VectorField.lieBracket_eq]
  beta_reduce
  rw [(hd hV).fderiv, (hd hW).fderiv]
  simp [map_sub]

end Conj

section Graph

universe v

variable {G : Type v} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The projection `(1 + iA)/2` onto the vectors of type `(0, 1)`, `ker(A + i)`. -/
def qProj (A : G →L[ℂ] G) : G →L[ℂ] G :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.id ℂ G + Complex.I • A)

/-- The projection `(1 − iA)/2` onto the vectors of type `(1, 0)`, `ker(A − i)`. -/
def pProj (A : G →L[ℂ] G) : G →L[ℂ] G :=
  (2⁻¹ : ℂ) • (ContinuousLinearMap.id ℂ G - Complex.I • A)

theorem qProj_apply (A : G →L[ℂ] G) (v : G) :
    qProj A v = (2⁻¹ : ℂ) • (v + Complex.I • A v) := rfl

theorem pProj_apply (A : G →L[ℂ] G) (v : G) :
    pProj A v = (2⁻¹ : ℂ) • (v - Complex.I • A v) := rfl

theorem qProj_add_pProj (A : G →L[ℂ] G) (v : G) : qProj A v + pProj A v = v := by
  rw [qProj_apply, pProj_apply]; module

variable {A : G →L[ℂ] G}

theorem I_smul_I_smul (v : G) : Complex.I • Complex.I • v = -v := by
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem apply_qProj (hA : ∀ v, A (A v) = -v) (v : G) :
    A (qProj A v) = -(Complex.I • qProj A v) := by
  simp only [qProj_apply, map_smul, map_add, hA, smul_add]
  match_scalars <;> first | ring1 | linear_combination (1 / 2 : ℂ) * Complex.I_sq

theorem apply_pProj (hA : ∀ v, A (A v) = -v) (v : G) :
    A (pProj A v) = Complex.I • pProj A v := by
  simp only [pProj_apply, map_smul, map_sub, hA, smul_sub]
  match_scalars <;> first | ring1 | linear_combination (1 / 2 : ℂ) * Complex.I_sq

theorem pProj_qProj (hA : ∀ v, A (A v) = -v) (v : G) : pProj A (qProj A v) = 0 := by
  rw [pProj_apply, apply_qProj hA, smul_neg, I_smul_I_smul]; simp

theorem qProj_pProj (hA : ∀ v, A (A v) = -v) (v : G) : qProj A (pProj A v) = 0 := by
  rw [qProj_apply, apply_pProj hA, I_smul_I_smul]; simp

/-- `A v = −i v` if and only if `(1 + iA)/2` fixes `v`. -/
theorem apply_eq_neg_I_smul_iff (hA : ∀ v, A (A v) = -v) (v : G) :
    A v = -(Complex.I • v) ↔ qProj A v = v := by
  constructor
  · intro h
    rw [qProj_apply, h, smul_neg, I_smul_I_smul]; module
  · intro h
    rw [← h, apply_qProj hA]

theorem qProj_qProj (hA : ∀ v, A (A v) = -v) (v : G) : qProj A (qProj A v) = qProj A v :=
  (apply_eq_neg_I_smul_iff hA _).1 (apply_qProj hA v)

/-- The space `ker(A + i)` of vectors of type `(0, 1)`, as the kernel of `(1 − iA)/2`. -/
abbrev typeZeroOne (A : G →L[ℂ] G) : Submodule ℂ G := LinearMap.ker (pProj A : G →ₗ[ℂ] G)

/-- The space `ker(A − i)` of vectors of type `(1, 0)`, as the kernel of `(1 + iA)/2`. -/
abbrev typeOneZero (A : G →L[ℂ] G) : Submodule ℂ G := LinearMap.ker (qProj A : G →ₗ[ℂ] G)

theorem isClosed_typeZeroOne (A : G →L[ℂ] G) : IsClosed (typeZeroOne A : Set G) :=
  ContinuousLinearMap.isClosed_ker (pProj A)

theorem isClosed_typeOneZero (A : G →L[ℂ] G) : IsClosed (typeOneZero A : Set G) :=
  ContinuousLinearMap.isClosed_ker (qProj A)

/-- The splitting `G ≅ ker(A + i) × ker(A − i)`, `v ↦ ((1 + iA)v/2, (1 − iA)v/2)`. -/
def typeSplit (hA : ∀ v, A (A v) = -v) : G ≃L[ℂ] typeZeroOne A × typeOneZero A :=
  ContinuousLinearEquiv.equivOfInverse
    (((qProj A).codRestrict (typeZeroOne A) fun v ↦ pProj_qProj hA v).prod
      ((pProj A).codRestrict (typeOneZero A) fun v ↦ LinearMap.mem_ker.2 (qProj_pProj hA v)))
    ((typeZeroOne A).subtypeL.coprod (typeOneZero A).subtypeL)
    (fun v ↦ qProj_add_pProj A v)
    (fun ⟨⟨u, hu⟩, ⟨m, hm⟩⟩ ↦ by
      have hu' : pProj A u = 0 := LinearMap.mem_ker.1 hu
      have hm' : qProj A m = 0 := LinearMap.mem_ker.1 hm
      have hqu : qProj A u = u := by
        have := qProj_add_pProj A u; rwa [hu', add_zero] at this
      have hpm : pProj A m = m := by
        have := qProj_add_pProj A m; rwa [hm', zero_add] at this
      ext
      · change qProj A (u + m) = u
        rw [map_add, hqu, hm', add_zero]
      · change pProj A (u + m) = m
        rw [map_add, hu', hpm, zero_add])

@[simp] theorem typeSplit_fst (hA : ∀ v, A (A v) = -v) (v : G) :
    ((typeSplit hA v).1 : G) = qProj A v := rfl

@[simp] theorem typeSplit_snd (hA : ∀ v, A (A v) = -v) (v : G) :
    ((typeSplit hA v).2 : G) = pProj A v := rfl

@[simp] theorem typeSplit_symm_apply (hA : ∀ v, A (A v) = -v) (q : typeZeroOne A × typeOneZero A) :
    (typeSplit hA).symm q = (q.1 : G) + q.2 := rfl

end Graph

section GraphFrob

universe w

variable {G : Type w} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {A : G →L[ℂ] G}

/-- `S = (1 + iA)/2 ∘ (1 + iB)/2` on `ker(A + i)`. -/
def graphS (A B : G →L[ℂ] G) (hA : ∀ v, A (A v) = -v) :
    typeZeroOne A →L[ℂ] typeZeroOne A :=
  ((qProj A).codRestrict (typeZeroOne A) fun v ↦ LinearMap.mem_ker.2 (pProj_qProj hA v)).comp
    ((qProj B).comp (typeZeroOne A).subtypeL)

/-- `T = (1 − iA)/2 ∘ (1 + iB)/2` from `ker(A + i)` to `ker(A − i)`. -/
def graphT (A B : G →L[ℂ] G) (hA : ∀ v, A (A v) = -v) :
    typeZeroOne A →L[ℂ] typeOneZero A :=
  ((pProj A).codRestrict (typeOneZero A) fun v ↦ LinearMap.mem_ker.2 (qProj_pProj hA v)).comp
    ((qProj B).comp (typeZeroOne A).subtypeL)

/-- The map whose graph is `ker(B + i)`, over `ker(A + i)` with values in `ker(A − i)`:
`g = T S⁻¹`. -/
def graphMap (A B : G →L[ℂ] G) (hA : ∀ v, A (A v) = -v) :
    typeZeroOne A →L[ℂ] typeOneZero A :=
  (graphT A B hA).comp (Ring.inverse (graphS A B hA))

/-- The field of graph maps of `ker(F z + i)`, in the coordinates `typeSplit` of `A`. -/
def graphField (F : G → G →L[ℂ] G) (A : G →L[ℂ] G) (hA : ∀ v, A (A v) = -v)
    (q : typeZeroOne A × typeOneZero A) : typeZeroOne A →L[ℂ] typeOneZero A :=
  graphMap A (F ((typeSplit hA).symm q)) hA

theorem graphS_self (hA : ∀ v, A (A v) = -v) : graphS A A hA = 1 := by
  ext ⟨u, hu⟩
  have hu' : pProj A u = 0 := LinearMap.mem_ker.1 hu
  change qProj A (qProj A u) = u
  rw [qProj_qProj hA]
  have := qProj_add_pProj A u
  rwa [hu', add_zero] at this

/-- **`ker(B + i)` is the graph of `graphMap A B`** when `B` is close to `A`: if `B² = −1`,
`S = graphS A B` is invertible and `‖(1 + iB)/2 − (1 + iA)/2‖ < 1`, then
`B v = −i v` if and only if the `(1, 0)` part of `v` (for `A`) is `T S⁻¹` of its `(0, 1)` part. -/
theorem apply_eq_neg_I_iff_graph (hA : ∀ v, A (A v) = -v) {B : G →L[ℂ] G}
    (hB : ∀ v, B (B v) = -v) (hS : IsUnit (graphS A B hA)) (hnorm : ‖qProj B - qProj A‖ < 1)
    (v : G) :
    B v = -(Complex.I • v) ↔ (typeSplit hA v).2 = graphMap A B hA (typeSplit hA v).1 := by
  set ℓ := typeSplit hA
  set S := graphS A B hA
  set u := Ring.inverse S (ℓ v).1
  have hSu : S u = (ℓ v).1 := by
    have := congrArg (fun L : typeZeroOne A →L[ℂ] typeZeroOne A ↦ L (ℓ v).1)
      (Ring.mul_inverse_cancel S hS)
    simpa using this
  have hSu' : qProj A (qProj B u) = qProj A v := congrArg Subtype.val hSu
  have hg : graphMap A B hA (ℓ v).1 = graphT A B hA u := rfl
  rw [hg, Subtype.ext_iff, typeSplit_snd]
  change _ ↔ pProj A v = pProj A (qProj B u)
  constructor
  · intro hv
    have hBv : qProj B v = v := (apply_eq_neg_I_smul_iff hB v).1 hv
    set x := qProj B u - v
    have hQx : qProj B x = x := by rw [map_sub, qProj_qProj hB, hBv]
    have hqx : qProj A x = 0 := by rw [map_sub, hSu', sub_self]
    have hx : (qProj B - qProj A) x = x := by
      rw [sub_apply, hQx, hqx, sub_zero]
    have hle := (qProj B - qProj A).le_opNorm x
    rw [hx] at hle
    have hx0 : x = 0 := by
      have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
      exact norm_le_zero_iff.1 this
    rw [show qProj B u = v from sub_eq_zero.1 hx0]
  · intro h
    have hQu : qProj B u = v := by
      rw [← qProj_add_pProj A (qProj B u), hSu', ← h, qProj_add_pProj]
    rw [← hQu, apply_qProj hB]

/-- **The `(0, 1)` distribution of an integrable complex structure satisfies (Frob)**
([Pen70, Théorème 3.5], (6) ⇒ (1), p. 75, first half). Let `G` be a complex Banach space, `O ⊆ G`
open and `F : O → L(G)` holomorphic with `F(z)² = −1` and `N_F(z) = 0`. Near `z₀ ∈ O`, in the
coordinates `G ≅ ker(F(z₀) + i) × ker(F(z₀) − i)` (`typeSplit`), the distribution
`z ↦ ker(F(z) + i)` is the field of graphs of the holomorphic map `graphField F A` (for any
`A = F(z₀)`), which satisfies Penot's integrability condition (Frob). -/
theorem exists_graph_frob_of_nijenhuis [CompleteSpace G] {F : G → G →L[ℂ] G} {O : Set G}
    (hO : IsOpen O) (hF : DifferentiableOn ℂ F O) (hsq : ∀ z ∈ O, ∀ v, F z (F z v) = -v)
    (hN : ∀ z ∈ O, nijenhuis ℂ F z = 0) {z₀ : G} (h₀ : z₀ ∈ O) {A : G →L[ℂ] G}
    (hA0 : F z₀ = A) (hA : ∀ v, A (A v) = -v) :
    ∃ O' : Set G, IsOpen O' ∧ z₀ ∈ O' ∧ O' ⊆ O ∧
      (∀ z ∈ O', ∀ v, F z v = -(Complex.I • v) ↔
        (typeSplit hA v).2 = graphField F A hA (typeSplit hA z) (typeSplit hA v).1) ∧
      DifferentiableOn ℂ (graphField F A hA) (typeSplit hA '' O') ∧
      ∀ q ∈ typeSplit hA '' O', ∀ a b,
        fderiv ℂ (graphField F A hA) q (a, graphField F A hA q a) b =
          fderiv ℂ (graphField F A hA) q (b, graphField F A hA q b) a := by
  set ℓ := typeSplit hA
  have : CompleteSpace (typeZeroOne A) := (isClosed_typeZeroOne A).completeSpace_coe
  have : CompleteSpace (typeOneZero A) := (isClosed_typeOneZero A).completeSpace_coe
  -- the operators `Q_z`, `S_z`, `T_z` depend holomorphically on `z`
  have hQd : DifferentiableOn ℂ (fun z ↦ qProj (F z)) O :=
    ((differentiableOn_const _).add (hF.const_smul Complex.I)).const_smul (2⁻¹ : ℂ)
  have hSd : DifferentiableOn ℂ (fun z ↦ graphS A (F z) hA) O :=
    (differentiableOn_const _).clm_comp (hQd.clm_comp (differentiableOn_const _))
  have hTd : DifferentiableOn ℂ (fun z ↦ graphT A (F z) hA) O :=
    (differentiableOn_const _).clm_comp (hQd.clm_comp (differentiableOn_const _))
  set O' := (O ∩ (fun z ↦ qProj (F z) - qProj A) ⁻¹' Metric.ball 0 1) ∩
    (fun z ↦ graphS A (F z) hA) ⁻¹' {x | IsUnit x}
  have hO₁ : IsOpen (O ∩ (fun z ↦ qProj (F z) - qProj A) ⁻¹' Metric.ball 0 1) :=
    (hQd.continuousOn.sub continuousOn_const).isOpen_inter_preimage hO Metric.isOpen_ball
  have hO' : IsOpen O' :=
    (hSd.continuousOn.mono inter_subset_left).isOpen_inter_preimage hO₁
      (Units.isOpen (R := typeZeroOne A →L[ℂ] typeZeroOne A))
  have hO'O : O' ⊆ O := fun z hz ↦ hz.1.1
  have hz₀ : z₀ ∈ O' := by
    refine ⟨⟨h₀, by simp [hA0]⟩, ?_⟩
    change IsUnit (graphS A (F z₀) hA)
    rw [hA0, graphS_self]; exact isUnit_one
  have hgraph : ∀ z ∈ O', ∀ v, F z v = -(Complex.I • v) ↔
      (ℓ v).2 = graphField F A hA (ℓ z) (ℓ v).1 := fun z hz v ↦ by
    have hnorm : ‖qProj (F z) - qProj A‖ < 1 := by simpa using hz.1.2
    have hfz : graphField F A hA (ℓ z) = graphMap A (F z) hA := by
      simp only [graphField, ℓ, ContinuousLinearEquiv.symm_apply_apply]
    rw [hfz]
    exact apply_eq_neg_I_iff_graph hA (hsq z (hO'O hz)) hz.2 hnorm v
  -- holomorphy of the graph field
  have hgd : ∀ z ∈ O', DifferentiableAt ℂ (fun z ↦ graphMap A (F z) hA) z := fun z hz ↦ by
    have hzO := hO'O hz
    change DifferentiableAt ℂ
      (fun z ↦ (graphT A (F z) hA).comp (Ring.inverse (graphS A (F z) hA))) z
    have hu : IsUnit (graphS A (F z) hA) := hz.2
    have hinv : DifferentiableAt ℂ (fun z ↦ Ring.inverse (graphS A (F z) hA)) z :=
      (differentiableAt_inverse (𝕜 := ℂ) (R := typeZeroOne A →L[ℂ] typeZeroOne A) hu).comp
        (f := fun z ↦ graphS A (F z) hA) z
        ((hSd z hzO).differentiableAt (hO.mem_nhds hzO))
    exact ((hTd z hzO).differentiableAt (hO.mem_nhds hzO)).clm_comp hinv
  have hfd : ∀ z ∈ O', DifferentiableAt ℂ (graphField F A hA) (ℓ z) := fun z hz ↦ by
    have h := hgd z hz
    rw [← ℓ.symm_apply_apply z] at h
    exact h.comp _ ℓ.symm.differentiableAt
  refine ⟨O', hO', hz₀, hO'O, hgraph, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hfd z hz).differentiableWithinAt
  -- (Frob), from the involutivity of `ker(F + i)`
  rintro _ ⟨z, hz, rfl⟩ a b
  set f := graphField F A hA
  have hS : ∀ c, DifferentiableAt ℂ (fun q' ↦ (c, f q' c)) (ℓ z) := fun c ↦
    (differentiableAt_const c).prodMk ((hfd z hz).clm_apply (differentiableAt_const c))
  have hSf : ∀ c, ∀ᶠ q' in 𝓝 (ℓ z),
      (fun q' ↦ (c, f q' c)) q' ∈ (f q' : typeZeroOne A →ₗ[ℂ] typeOneZero A).graph := fun c ↦
    Eventually.of_forall fun _ ↦ (LinearMap.mem_graph_iff _ _).2 rfl
  set X : typeZeroOne A → G → G := fun c z' ↦ ℓ.symm (c, f (ℓ z') c) with hXdef
  have hX : ∀ c, DifferentiableAt ℂ (X c) z := fun c ↦
    ℓ.symm.differentiableAt.comp z ((hS c).comp z ℓ.differentiableAt)
  have hXF : ∀ c, ∀ᶠ z' in 𝓝 z, F z' (X c z') = -(Complex.I • X c z') := fun c ↦
    eventually_of_mem (hO'.mem_nhds hz) fun z' hz' ↦
      (hgraph z' hz' _).2 (by simp only [X, ContinuousLinearEquiv.apply_symm_apply])
  have hsq' : ∀ᶠ p in 𝓝 z, (F p).comp (F p) = -ContinuousLinearMap.id ℂ G :=
    eventually_of_mem (hO'.mem_nhds hz) fun p hp ↦
      ContinuousLinearMap.ext fun v ↦ by simp [hsq p (hO'O hp) v]
  have hFz : DifferentiableAt ℂ F z := (hF z (hO'O hz)).differentiableAt (hO.mem_nhds (hO'O hz))
  have hbr := lieBracket_mem_ker_of_nijenhuis hFz hsq' (hN z (hO'O hz)) (hX a) (hX b)
    (hXF a) (hXF b)
  have hc : VectorField.lieBracket ℂ (X a) (X b) z =
      ℓ.symm (VectorField.lieBracket ℂ (fun q' ↦ (a, f q' a)) (fun q' ↦ (b, f q' b)) (ℓ z)) :=
    lieBracket_comp_equiv ℓ (hS a) (hS b)
  have hg := (hgraph z hz _).1 hbr
  rw [hc, ContinuousLinearEquiv.apply_symm_apply] at hg
  exact (lieBracket_mem_graph_iff (hfd z hz) (hS a) (hS b) (hSf a) (hSf b)).1
    ((LinearMap.mem_graph_iff _ _).2 hg)

end GraphFrob

end LocallyConvex.Analysis

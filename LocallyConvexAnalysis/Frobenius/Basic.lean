/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.ODE.Flow
public import LocallyConvexAnalysis.Analytic.BanachHolomorphic

/-!
# The local Frobenius theorem on Banach spaces, after Penot

Let `E`, `F` be Banach spaces over `𝕜 = ℝ` or `ℂ`, `O ⊆ E × F` open and `f : O → L(E, F)` of
class `C^n`, `1 ≤ n ≤ ∞`, satisfying the integrability condition

  (Frob) `D₁f(q)(a)(b) + D₂f(q)(f(q) a)(b) = D₁f(q)(b)(a) + D₂f(q)(f(q) b)(a)`

for `q ∈ O`, `a, b ∈ E` (written `Df(q)(a, f(q) a)(b) = Df(q)(b, f(q) b)(a)`). Then near every
`(x₀, y₀) ∈ O` there is a `C^n` map `α` with `α(x₀, y) = y` and `D₁α(x, y) = f(x, α(x, y))`.
For `𝕜 = ℂ` and `f` holomorphic, `α` is holomorphic. This is J.-P. Penot, *Sur le théorème de
Frobenius*, Bull. Soc. Math. France 98 (1970), 47–80, Théorème 1.1 (p. 48) and Remarque 1
(p. 49): the Frobenius theorem follows from the implicit function theorem.

## Main definitions

* `penotRHS 𝕜 f`: the right-hand side of Penot's equation,
  `(x, y, δ) ↦ (s ↦ f(s x, y + ∫₀ˢ δ) x)`, with values in `C([-1, 1], F)`.
* `penotMap 𝕜 f`: **Penot's map** `(x, y, δ) ↦ (x, y, δ - (s ↦ f(s x, y + ∫₀ˢ δ) x))`, whose
  zeros in the last component are the derivatives `δ = γ'` of the curves `γ(s) = ∫₀ˢ δ` with
  `γ'(s) = f(s x, y + γ(s)) x` ([Pen70, proof of Théorème 1.1]).

## Main results

* `contDiffOn_penotMap`: Penot's map is `C^n` if `f` is.
* `hasFDerivAt_penotMap_zero`: at `(0, y₀, 0)` the derivative of Penot's map is the invertible
  shear `(a, b, c) ↦ (a, b, c - w(a))`, with `w(a)` the constant curve `f(0, y₀) a`.
* `exists_frobenius`: **the local Frobenius theorem on Banach spaces** ([Pen70, Théorème 1.1]):
  if `f` is `C^n`, `1 ≤ n ≤ ∞`, and satisfies (Frob), then for every `(x₀, y₀) ∈ O` there are
  `r > 0` and a `C^n` map `α` on `B(x₀, r) × B(y₀, r) ⊆ O` with `α(x₀, y) = y` and
  `D₁α(x, y) = f(x, α(x, y))`. The case `x₀ = 0` is `exists_frobenius_zero`.
* `exists_frobenius_holomorphic`: for `𝕜 = ℂ` and `f` holomorphic satisfying (Frob), the
  solution `α` is holomorphic (complex analytic) ([Pen70, Remarque 1]).

## Implementation notes

The proof follows Penot.

* **The equation.** For `(x, y)` near `(x₀, y₀) = (0, y₀)` we look for a curve `γ` with `γ(0) = 0`
  and `γ'(s) = f(s x, y + γ(s)) x`; then `α(x, y) = y + γ(1)`. The unknown is `δ = γ'` in the
  Banach space `C([-1, 1], F)`, with `γ(s) = ∫₀ˢ δ`: the zeros of the last component of
  `(x, y, δ) ↦ (x, y, δ - (s ↦ f(s x, y + ∫₀ˢ δ) x))` (`penotMap`). This map is `C^n` because
  superposition operators are (`contDiffOn_superpose`), and at `(0, y₀, 0)` its derivative is an
  invertible shear (`hasFDerivAt_penotMap_zero`). The inverse function theorem gives a `C^n`
  family of solutions `δ = φ(x, y)`, and `φ(0, y) = 0`.
* **The derivative of `α`.** Differentiating the fixed point identity, `K(s) = ∂ₓ(∫₀ˢ φ)(z)`
  solves the linear equation `u' = Df(c(s))(s z, u) x + f(c(s)) z`, `u(0) = 0`, with
  `c(s) = (s x, y + ∫₀ˢ φ(x, y))`. By (Frob), so does `L(s) = s f(c(s)) z`. Hence `K = L` on
  `[0, 1]`, and at `s = 1` this is `D₁α(x, y) z = f(x, α(x, y)) z`.

We depart from Penot in two places. Instead of the implicit function theorem on curves
`γ ∈ C¹` with `γ(0) = 0`, we apply Mathlib's inverse function theorem to `penotMap`, with the
derivative `δ = γ'` as unknown. And `K = L` follows from the uniqueness of solutions of linear
ODEs (Mathlib's `ODE_solution_unique_of_mem_Icc_right`, a Gronwall argument), where Penot shows
that both curves are mapped to the same point by `D₃g(x, y, φ(x, y))`, which he assumes
invertible after shrinking the neighbourhoods. We do not claim this argument is new.

* The curves are parametrized by `[-1, 1]`, as in `LocallyConvexAnalysis.ODE.Flow`, whose
  superposition operators, primitive `primitiveCLM` and evaluations are reused; only `[0, 1]`
  matters.
* `E` and `F` carry compatible real structures (`[NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]`) for the
  integrals and the derivatives in the real variable `s`; for `𝕜 = ℂ` these are Mathlib's
  instances. Completeness of `E` and `F` is needed for the inverse function theorem and for the
  integrals.
* Penot also treats `f` real analytic (`r = ω`) with a real analytic implicit function theorem.
  That case is `exists_frobenius_realAnalytic` in `LocallyConvexAnalysis.Frobenius.Analytic`,
  obtained instead from the real analytic dependence of flows on initial values.
* The global versions (integral manifolds of involutive subbundles, [Pen70, Part II]) and the
  application to the Newlander–Nirenberg theorem for real analytic almost complex structures on
  Banach manifolds are planned.

## References

* [J.-P. Penot, *Sur le théorème de Frobenius*][Pen70]
-/

@[expose] public section

open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section

namespace LocallyConvex.Analysis

/-- The interval `[-1, 1]`, on which the curves of Penot's equation are parametrized. -/
local notation "𝕀" => (Icc (-1 : ℝ) 1)

section PenotMap

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [IsScalarTower ℝ 𝕜 F]

variable (𝕜 E) in
/-- The segments `x ↦ (s ↦ s x)`, as a continuous linear map `E → C([-1, 1], E)`. -/
def lineI : E →L[𝕜] C(𝕀, E) :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟨fun s ↦ ((s : ℝ) : 𝕜) • x,
        (RCLike.continuous_ofReal.comp continuous_subtype_val).smul continuous_const⟩
      map_add' := fun _ _ ↦ by ext s; exact smul_add _ _ _
      map_smul' := fun c x ↦ by ext; exact smul_comm _ c x }
    1 fun x ↦ by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s ↦ ?_
      change ‖((s : ℝ) : 𝕜) • x‖ ≤ ‖x‖
      rw [norm_smul, RCLike.norm_ofReal]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.2 s.2)

@[simp]
theorem lineI_apply (x : E) (s : 𝕀) : lineI 𝕜 E x s = ((s : ℝ) : 𝕜) • x :=
  rfl

variable (𝕜 E F) in
/-- Pairing of curves, `(a, b) ↦ (s ↦ (a s, b s))`, as a continuous linear map
`C([-1, 1], E) × C([-1, 1], F) → C([-1, 1], E × F)`. -/
def pairI : C(𝕀, E) × C(𝕀, F) →L[𝕜] C(𝕀, E × F) :=
  LinearMap.mkContinuous
    { toFun := fun q ↦ q.1.prodMk q.2
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 fun q ↦ by
      rw [one_mul]
      refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun s ↦ ?_
      rw [Prod.norm_def, Prod.norm_def]
      exact max_le_max (q.1.norm_coe_le_norm s) (q.2.norm_coe_le_norm s)

omit [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
@[simp]
theorem pairI_apply (q : C(𝕀, E) × C(𝕀, F)) (s : 𝕀) : pairI 𝕜 E F q s = (q.1 s, q.2 s) :=
  rfl

variable (𝕜 E F) in
/-- **Penot's curves.** `(x, y, δ) ↦ (s ↦ (s x, y + ∫₀ˢ δ))`, a continuous linear map
`E × F × C([-1, 1], F) → C([-1, 1], E × F)`. -/
def penotCurve : E × F × C(𝕀, F) →L[𝕜] C(𝕀, E × F) :=
  pairI 𝕜 E F ∘L
    ((lineI 𝕜 E ∘L ContinuousLinearMap.fst 𝕜 E (F × C(𝕀, F))).prod
      (constI 𝕜 ∘L (ContinuousLinearMap.fst 𝕜 F C(𝕀, F) ∘L
          ContinuousLinearMap.snd 𝕜 E (F × C(𝕀, F))) +
        primitiveCLM 𝕜 ∘L (ContinuousLinearMap.snd 𝕜 F C(𝕀, F) ∘L
          ContinuousLinearMap.snd 𝕜 E (F × C(𝕀, F)))))

@[simp]
theorem penotCurve_apply (p : E × F × C(𝕀, F)) (s : 𝕀) :
    penotCurve 𝕜 E F p s = (((s : ℝ) : 𝕜) • p.1, p.2.1 + ∫ τ in (0 : ℝ)..s, extendI p.2.2 τ) :=
  rfl

variable (𝕜) in
/-- The right-hand side of Penot's equation, `(x, y, δ) ↦ (s ↦ f(s x, y + ∫₀ˢ δ) x)`. -/
def penotRHS (f : E × F → E →L[𝕜] F) (p : E × F × C(𝕀, F)) : C(𝕀, F) :=
  pointwiseApply 𝕜 𝕀 E F (superpose f (penotCurve 𝕜 E F p)) (constI 𝕜 p.1)

/-- On the curves with values in `O`, `penotRHS f (x, y, δ) (s) = f(s x, y + ∫₀ˢ δ) x`. -/
theorem penotRHS_apply {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hf : ContinuousOn f O)
    {p : E × F × C(𝕀, F)} (hp : penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O) (s : 𝕀) :
    penotRHS 𝕜 f p s = f (penotCurve 𝕜 E F p s) p.1 := by
  simp only [penotRHS, pointwiseApply_apply, superpose_apply hf hp, constI_apply]

variable (𝕜) in
/-- **Penot's map** `(x, y, δ) ↦ (x, y, δ - (s ↦ f(s x, y + ∫₀ˢ δ) x))`. Its zeros in the last
component are the derivatives `δ = γ'` of the curves `γ(s) = ∫₀ˢ δ` with
`γ' (s) = f(s x, y + γ(s)) x` ([Pen70, proof of Théorème 1.1]). -/
def penotMap (f : E × F → E →L[𝕜] F) (p : E × F × C(𝕀, F)) : E × F × C(𝕀, F) :=
  (p.1, p.2.1, p.2.2 - penotRHS 𝕜 f p)

/-- The set of `(x, y, δ)` whose Penot curve has values in `O`, an open set. -/
theorem isOpen_penotDomain {O : Set (E × F)} (hO : IsOpen O) :
    IsOpen {p : E × F × C(𝕀, F) | penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O} :=
  (isOpen_mapsInto hO).preimage (penotCurve 𝕜 E F).continuous

/-- The right-hand side of Penot's equation is `C^n` if `f` is. -/
theorem contDiffOn_penotRHS {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    {n : ℕ∞} (hf : ContDiffOn 𝕜 n f O) :
    ContDiffOn 𝕜 n (penotRHS 𝕜 f)
      {p : E × F × C(𝕀, F) | penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O} := by
  have hA : ContDiffOn 𝕜 n (fun p : E × F × C(𝕀, F) ↦ superpose f (penotCurve 𝕜 E F p))
      {p : E × F × C(𝕀, F) | penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O} :=
    (contDiffOn_superpose hO hf).comp (penotCurve 𝕜 E F).contDiff.contDiffOn fun _ hp ↦ hp
  have hv : ContDiff 𝕜 n (fun p : E × F × C(𝕀, F) ↦ constI 𝕜 p.1) :=
    ((constI 𝕜 (E := E)).contDiff (n := n)).comp contDiff_fst
  exact (pointwiseApply 𝕜 𝕀 E F).isBoundedBilinearMap.contDiff.comp_contDiffOn
    (hA.prodMk hv.contDiffOn)

/-- Penot's map is `C^n` if `f` is. -/
theorem contDiffOn_penotMap {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    {n : ℕ∞} (hf : ContDiffOn 𝕜 n f O) :
    ContDiffOn 𝕜 n (penotMap 𝕜 f)
      {p : E × F × C(𝕀, F) | penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O} :=
  contDiffOn_fst.prodMk ((contDiff_fst.comp contDiff_snd).contDiffOn.prodMk
    ((contDiff_snd.comp contDiff_snd).contDiffOn.sub (contDiffOn_penotRHS hO hf)))

/-- **The derivative of the right-hand side of Penot's equation**, pointwise:
`D Q(x, y, δ) (u, v, η) (s) = Df(c(s)) (s u, v + ∫₀ˢ η) x + f(c(s)) u`, where `c` is the Penot
curve of `(x, y, δ)`. -/
theorem hasFDerivAt_penotRHS {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    (hf : ContDiffOn 𝕜 1 f O) {p : E × F × C(𝕀, F)} (hp : penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O) :
    ∃ D : (E × F × C(𝕀, F)) →L[𝕜] C(𝕀, F), HasFDerivAt (penotRHS 𝕜 f) D p ∧
      ∀ v s, D v s = fderiv 𝕜 f (penotCurve 𝕜 E F p s) (penotCurve 𝕜 E F v s) p.1 +
        f (penotCurve 𝕜 E F p s) v.1 := by
  have hfc : ContinuousOn f O := hf.continuousOn
  have hDc : ContinuousOn (fderiv 𝕜 f) O := hf.continuousOn_fderiv_of_isOpen hO le_rfl
  have hA := ((hasFDerivAt_superpose hO hf hp).comp p (penotCurve 𝕜 E F).hasFDerivAt)
  have hv := (constI 𝕜 (E := E)).hasFDerivAt.comp p (hasFDerivAt_fst (p := p))
  refine ⟨_, (pointwiseApply 𝕜 𝕀 E F).hasFDerivAt_of_bilinear hA hv, fun v s ↦ ?_⟩
  change pointwiseApply 𝕜 𝕀 E F (superpose f (penotCurve 𝕜 E F p)) (constI 𝕜 v.1) s +
    pointwiseApply 𝕜 𝕀 E F (pointwiseApply 𝕜 𝕀 (E × F) (E →L[𝕜] F)
      (superpose (fderiv 𝕜 f) (penotCurve 𝕜 E F p)) (penotCurve 𝕜 E F v)) (constI 𝕜 p.1) s = _
  rw [pointwiseApply_apply, pointwiseApply_apply, pointwiseApply_apply,
    superpose_apply hfc hp, superpose_apply (F := E × F →L[𝕜] E →L[𝕜] F) hDc hp, constI_apply,
    constI_apply, add_comm]

omit [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
/-- The extension of the zero curve is zero. -/
@[simp]
theorem extendI_zero (τ : ℝ) : extendI (0 : C(𝕀, F)) τ = 0 :=
  rfl

/-- The Penot curve of `(0, y, 0)` is the constant curve `(0, y)`. -/
theorem penotCurve_zero_apply (y : F) (s : 𝕀) :
    penotCurve 𝕜 E F ((0 : E), y, (0 : C(𝕀, F))) s = (0, y) := by
  simp

/-- The right-hand side of Penot's equation vanishes for `x = 0`. -/
theorem penotRHS_zero (f : E × F → E →L[𝕜] F) (y : F) (δ : C(𝕀, F)) :
    penotRHS 𝕜 f ((0 : E), y, δ) = 0 := by
  simp [penotRHS]

variable (𝕜) in
/-- The shear `(a, b, c) ↦ (a, b, c + σ w(a))` of `E × F × C([-1, 1], F)`. -/
def penotShearCLM (σ : 𝕜) (w : E →L[𝕜] C(𝕀, F)) :
    (E × F × C(𝕀, F)) →L[𝕜] (E × F × C(𝕀, F)) :=
  ContinuousLinearMap.id 𝕜 _ + σ • ((ContinuousLinearMap.inr 𝕜 E (F × C(𝕀, F)) ∘L
    ContinuousLinearMap.inr 𝕜 F C(𝕀, F)) ∘L w ∘L ContinuousLinearMap.fst 𝕜 E (F × C(𝕀, F)))

omit [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
@[simp]
theorem penotShearCLM_apply (σ : 𝕜) (w : E →L[𝕜] C(𝕀, F)) (p : E × F × C(𝕀, F)) :
    penotShearCLM 𝕜 σ w p = (p.1, p.2.1, p.2.2 + σ • w p.1) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [penotShearCLM]

variable (𝕜) in
/-- The shear `(a, b, c) ↦ (a, b, c - w(a))` as a linear homeomorphism. -/
def penotShear (w : E →L[𝕜] C(𝕀, F)) : (E × F × C(𝕀, F)) ≃L[𝕜] (E × F × C(𝕀, F)) :=
  ContinuousLinearEquiv.equivOfInverse (penotShearCLM 𝕜 (-1) w) (penotShearCLM 𝕜 1 w)
    (fun p ↦ by simp) (fun p ↦ by simp)

/-- At `(0, y₀, 0)` the derivative of Penot's map is the shear `(a, b, c) ↦ (a, b, c - w(a))`
with `w(a)` the constant curve `f(0, y₀) a`; in particular it is invertible. -/
theorem hasFDerivAt_penotMap_zero {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    (hf : ContDiffOn 𝕜 1 f O) {y₀ : F} (h₀ : ((0 : E), y₀) ∈ O) :
    HasFDerivAt (penotMap 𝕜 f)
      ((penotShear 𝕜 (constI 𝕜 ∘L f ((0 : E), y₀)) : (E × F × C(𝕀, F)) →L[𝕜] _))
      ((0 : E), y₀, (0 : C(𝕀, F))) := by
  set p₀ : E × F × C(𝕀, F) := (0, y₀, 0)
  have hp₀ : penotCurve 𝕜 E F p₀ ∈ mapsInto 𝕀 O := fun s ↦ by
    rw [penotCurve_zero_apply]; exact h₀
  obtain ⟨D, hD, hDv⟩ := hasFDerivAt_penotRHS hO hf hp₀
  have H := (hasFDerivAt_fst (𝕜 := 𝕜) (p := p₀)).prodMk
    ((hasFDerivAt_snd (𝕜 := 𝕜) (p := p₀)).fst.prodMk
      ((hasFDerivAt_snd (𝕜 := 𝕜) (p := p₀)).snd.sub hD))
  refine H.congr_fderiv (ContinuousLinearMap.ext fun v ↦
    Prod.ext (by simp [penotShear]) (Prod.ext (by simp [penotShear]) ?_))
  ext s
  change v.2.2 s - D v s = _
  rw [hDv]
  simp [penotShear, p₀, sub_eq_add_neg]

end PenotMap

section Frobenius

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [IsScalarTower ℝ 𝕜 F] [CompleteSpace F]

/-- **The local Frobenius theorem at `x₀ = 0`** ([Pen70, Théorème 1.1]). See `exists_frobenius`. -/
theorem exists_frobenius_zero {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    {n : ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn 𝕜 n f O)
    (hfrob : ∀ q ∈ O, ∀ a b : E, fderiv 𝕜 f q (a, f q a) b = fderiv 𝕜 f q (b, f q b) a)
    {y₀ : F} (h₀ : ((0 : E), y₀) ∈ O) :
    ∃ r > (0 : ℝ), ∃ α : E × F → F, ContDiffOn 𝕜 n α (ball (0 : E) r ×ˢ ball y₀ r) ∧
      (∀ y ∈ ball y₀ r, α (0, y) = y) ∧
      ∀ x ∈ ball (0 : E) r, ∀ y ∈ ball y₀ r, (x, α (x, y)) ∈ O ∧
        HasFDerivAt (fun x' ↦ α (x', y)) (f (x, α (x, y))) x := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le hn1).ne'
  have hf1 : ContDiffOn 𝕜 1 f O := hf.of_le hn1
  have hfc : ContinuousOn f O := hf.continuousOn
  have hDc : ContinuousOn (fderiv 𝕜 f) O := hf1.continuousOn_fderiv_of_isOpen hO le_rfl
  set D : Set (E × F × C(𝕀, F)) := {p | penotCurve 𝕜 E F p ∈ mapsInto 𝕀 O}
  have hD : IsOpen D := isOpen_penotDomain hO
  set p₀ : E × F × C(𝕀, F) := (0, y₀, 0)
  have hp₀ : p₀ ∈ D := fun s ↦ by
    change penotCurve 𝕜 E F ((0 : E), y₀, (0 : C(𝕀, F))) s ∈ O
    rw [penotCurve_zero_apply]; exact h₀
  have hΨ : ContDiffOn 𝕜 n (penotMap 𝕜 f) D := contDiffOn_penotMap hO hf
  have hder := hasFDerivAt_penotMap_zero hO hf1 h₀
  -- the inverse function theorem at `p₀`
  set H := (hΨ.contDiffAt (hD.mem_nhds hp₀)).toOpenPartialHomeomorph (penotMap 𝕜 f) hder hn0
  have hH : ∀ p, H p = penotMap 𝕜 f p := fun _ ↦ rfl
  set S := D ∩ fderiv 𝕜 (penotMap 𝕜 f) ⁻¹'
    range ((↑) : ((E × F × C(𝕀, F)) ≃L[𝕜] (E × F × C(𝕀, F))) → _ →L[𝕜] _)
  have hS : IsOpen S := (hΨ.continuousOn_fderiv_of_isOpen hD hn1).isOpen_inter_preimage hD
    ContinuousLinearEquiv.isOpen
  have hp₀S : p₀ ∈ S := ⟨hp₀, _, hder.fderiv.symm⟩
  set V₀ := H.target ∩ H.symm ⁻¹' S
  have hV₀ : IsOpen V₀ := H.continuousOn_symm.isOpen_inter_preimage H.open_target hS
  have hsymm : ContDiffOn 𝕜 n H.symm V₀ := by
    intro q hq
    obtain ⟨hqD, e, he⟩ := hq.2
    have hd : HasFDerivAt H (e : _ →L[𝕜] _) (H.symm q) := by
      rw [he]
      exact (((hΨ.differentiableOn hn0) _ hqD).differentiableAt (hD.mem_nhds hqD)).hasFDerivAt
    exact (H.contDiffAt_symm hq.1 hd (hΨ.contDiffAt (hD.mem_nhds hqD))).contDiffWithinAt
  have hfix : ∀ y : F, penotMap 𝕜 f ((0 : E), y, (0 : C(𝕀, F))) = (0, y, 0) := fun y ↦ by
    simp [penotMap, penotRHS_zero]
  have hp₀src : p₀ ∈ H.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ hder hn0
  have hfix₀ : penotMap 𝕜 f p₀ = p₀ := hfix y₀
  have hp₀tgt : p₀ ∈ H.target := by
    have := ContDiffAt.image_mem_toOpenPartialHomeomorph_target
      (hΨ.contDiffAt (hD.mem_nhds hp₀)) hder hn0
    rwa [hfix₀] at this
  have hsymm₀ : H.symm p₀ = p₀ := by
    have := H.left_inv hp₀src
    rwa [hH, hfix₀] at this
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.1
    (inter_mem (H.open_source.mem_nhds hp₀src) (hD.mem_nhds hp₀))
  have hW : V₀ ∩ H.symm ⁻¹' ball p₀ a ∈ 𝓝 p₀ := by
    refine inter_mem (hV₀.mem_nhds ⟨hp₀tgt, ?_⟩)
      ((H.continuousAt_symm hp₀tgt).preimage_mem_nhds ?_)
    · rw [mem_preimage, hsymm₀]; exact hp₀S
    · rw [hsymm₀]; exact ball_mem_nhds _ ha
  obtain ⟨b₁, hb₁, hbW⟩ := Metric.mem_nhds_iff.1 hW
  set b := min a b₁
  have hb : 0 < b := lt_min ha hb₁
  have hqb : ∀ x y, x ∈ ball (0 : E) b → y ∈ ball y₀ b →
      ((x, y, 0) : E × F × C(𝕀, F)) ∈ ball p₀ b := by
    intro x y hx hy
    rw [mem_ball] at hx hy ⊢
    rw [Prod.dist_eq, Prod.dist_eq, dist_self]
    exact max_lt hx (max_lt hy hb)
  have hqb₁ : ∀ x y, x ∈ ball (0 : E) b → y ∈ ball y₀ b →
      ((x, y, 0) : E × F × C(𝕀, F)) ∈ V₀ ∩ H.symm ⁻¹' ball p₀ a := fun x y hx hy ↦
    hbW (ball_subset_ball (min_le_right _ _) (hqb x y hx hy))
  -- the solutions `φ(x, y)` of Penot's equation
  set φ : E × F → C(𝕀, F) := fun q ↦ (H.symm (q.1, q.2, 0)).2.2 with hφ_def
  have key : ∀ x y, x ∈ ball (0 : E) b → y ∈ ball y₀ b →
      H.symm (x, y, 0) = (x, y, φ (x, y)) ∧ ((x, y, φ (x, y)) : E × F × C(𝕀, F)) ∈ D ∧
      φ (x, y) = penotRHS 𝕜 f (x, y, φ (x, y)) := by
    intro x y hx hy
    obtain ⟨⟨hqV, -⟩, hqa⟩ := hqb₁ x y hx hy
    have hHp : penotMap 𝕜 f (H.symm (x, y, 0)) = (x, y, 0) := by
      rw [← hH]; exact H.right_inv hqV
    have h1 : (H.symm (x, y, 0)).1 = x := congrArg Prod.fst hHp
    have h2 : (H.symm (x, y, 0)).2.1 = y := congrArg (fun q ↦ q.2.1) hHp
    have h3 := congrArg (fun q ↦ q.2.2) hHp
    simp only [penotMap, h1, h2] at h3
    have hp : H.symm (x, y, 0) = (x, y, φ (x, y)) := Prod.ext h1 (Prod.ext h2 rfl)
    have h3' : φ (x, y) - penotRHS 𝕜 f (x, y, φ (x, y)) = 0 := by rw [← hp]; exact h3
    refine ⟨hp, ?_, sub_eq_zero.1 h3'⟩
    rw [← hp]; exact (has hqa).2
  set one : 𝕀 := ⟨1, by norm_num⟩
  set α : E × F → F := fun q ↦ q.2 + primitiveCLM 𝕜 (φ q) one with hα_def
  -- smoothness
  have hι : ContDiff 𝕜 n (fun q : E × F ↦ ((q.1, q.2, 0) : E × F × C(𝕀, F))) :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hmaps : MapsTo (fun q : E × F ↦ ((q.1, q.2, 0) : E × F × C(𝕀, F)))
      (ball (0 : E) b ×ˢ ball y₀ b) V₀ := fun q hq ↦ (hqb₁ _ _ hq.1 hq.2).1
  have hφs : ContDiffOn 𝕜 n φ (ball (0 : E) b ×ˢ ball y₀ b) :=
    (contDiff_snd.comp contDiff_snd).comp_contDiffOn (hsymm.comp hι.contDiffOn hmaps)
  have hαs : ContDiffOn 𝕜 n α (ball (0 : E) b ×ˢ ball y₀ b) :=
    contDiffOn_snd.add (((evalI 𝕜 (E := F) one).contDiff.comp
      (primitiveCLM 𝕜 (E := F)).contDiff).comp_contDiffOn hφs)
  refine ⟨b, hb, α, hαs, fun y hy ↦ ?_, fun x hx y hy ↦ ?_⟩
  · -- `α(0, y) = y`, by injectivity of `H` near `p₀`
    have hsrc : ((0 : E), y, (0 : C(𝕀, F))) ∈ H.source := by
      refine (has (ball_subset_ball (min_le_left _ _) (hqb 0 y (mem_ball_self hb) hy))).1
    have htgt : ((0 : E), y, (0 : C(𝕀, F))) ∈ H.target := (hqb₁ 0 y (mem_ball_self hb) hy).1.1
    have hinj : ((0 : E), y, (0 : C(𝕀, F))) = H.symm (0, y, 0) :=
      H.injOn hsrc (H.map_target htgt) (by rw [H.right_inv htgt, hH, hfix])
    have hφ0 : φ (0, y) = 0 := by
      change (H.symm (0, y, 0)).2.2 = 0
      rw [← hinj]
    simp [α, hφ0]
  · -- the identity `D₁α(x, y) = f(x, α(x, y))`
    obtain ⟨-, hpD, hφeq⟩ := key x y hx hy
    set δ := φ (x, y) with hδ
    set p : E × F × C(𝕀, F) := (x, y, δ) with hp
    have hI : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → t ∈ 𝕀 := fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
    -- the curve `c(s) = (s x, y + ∫₀ˢ δ)` for real `s`
    set c : ℝ → E × F := fun s ↦ (((s : ℝ) : 𝕜) • x, y + ∫ τ in (0 : ℝ)..s, extendI δ τ)
      with hc
    have hcO : ∀ s : ℝ, s ∈ 𝕀 → c s ∈ O := fun s hs ↦ hpD ⟨s, hs⟩
    have hδs : ∀ s : ℝ, s ∈ 𝕀 → extendI δ s = f (c s) x := fun s hs ↦ by
      rw [extendI_of_mem _ hs]
      conv_lhs => rw [hφeq]
      exact penotRHS_apply hfc hpD ⟨s, hs⟩
    have hc1 : c 1 = (x, α (x, y)) := by
      simp [c, α, one, primitiveCLM_apply]
      rfl
    have hxα : (x, α (x, y)) ∈ O := hc1 ▸ hcO 1 ⟨by norm_num, le_rfl⟩
    refine ⟨hxα, ?_⟩
    -- the derivative of `φ`, from the fixed point identity
    have hqU : (x, y) ∈ ball (0 : E) b ×ˢ ball y₀ b := ⟨hx, hy⟩
    have hUo : IsOpen (ball (0 : E) b ×ˢ ball y₀ b) := isOpen_ball.prod isOpen_ball
    have hφd : HasFDerivAt φ (fderiv 𝕜 φ (x, y)) (x, y) :=
      (((hφs.differentiableOn hn0) _ hqU).differentiableAt (hUo.mem_nhds hqU)).hasFDerivAt
    set φ' := fderiv 𝕜 φ (x, y) with hφ'
    obtain ⟨DR, hDR, hDRv⟩ := hasFDerivAt_penotRHS hO hf1 hpD
    have hΦ : HasFDerivAt (fun q : E × F ↦ ((q.1, q.2, φ q) : E × F × C(𝕀, F)))
        ((ContinuousLinearMap.fst 𝕜 E F).prod ((ContinuousLinearMap.snd 𝕜 E F).prod φ'))
        (x, y) :=
      hasFDerivAt_fst.prodMk (hasFDerivAt_snd.prodMk hφd)
    have hcomp : HasFDerivAt (fun q : E × F ↦ penotRHS 𝕜 f (q.1, q.2, φ q))
        (DR ∘L ((ContinuousLinearMap.fst 𝕜 E F).prod ((ContinuousLinearMap.snd 𝕜 E F).prod φ')))
        (x, y) := by
      have hDR' : HasFDerivAt (penotRHS 𝕜 f) DR
          ((fun q : E × F ↦ ((q.1, q.2, φ q) : E × F × C(𝕀, F))) (x, y)) := hDR
      exact hDR'.comp (x, y) hΦ
    have hev : φ =ᶠ[𝓝 (x, y)] fun q : E × F ↦ penotRHS 𝕜 f (q.1, q.2, φ q) := by
      filter_upwards [hUo.mem_nhds hqU] with q hq
      exact (key q.1 q.2 hq.1 hq.2).2.2
    have hφ'eq : φ' = DR ∘L ((ContinuousLinearMap.fst 𝕜 E F).prod
        ((ContinuousLinearMap.snd 𝕜 E F).prod φ')) :=
      hφd.unique (hcomp.congr_of_eventuallyEq hev)
    -- the derivative of `α` in the direction of `E`
    set P : C(𝕀, F) →L[𝕜] F := (evalI 𝕜 one).comp (primitiveCLM 𝕜 (E := F)) with hP
    have hαd : HasFDerivAt α ((ContinuousLinearMap.snd 𝕜 E F) + P ∘L φ') (x, y) :=
      hasFDerivAt_snd.add (P.hasFDerivAt.comp (x, y) hφd)
    refine (hαd.comp x (hasFDerivAt_prodMk_left (𝕜 := 𝕜) x y)).congr_fderiv
      (ContinuousLinearMap.ext fun z ↦ ?_)
    set k := φ' (z, 0) with hk_def
    have hk : k = DR (z, 0, k) := by
      conv_lhs => rw [hk_def, hφ'eq]
      rfl
    -- `K(s) = ∫₀ˢ k` and `L(s) = s f(c(s)) z` solve the same linear equation
    set K : ℝ → F := fun s ↦ ∫ τ in (0 : ℝ)..s, extendI k τ with hK
    set L : ℝ → F := fun s ↦ ((s : ℝ) : 𝕜) • f (c s) z with hL
    set v : ℝ → F → F := fun s u ↦ fderiv 𝕜 f (c s) (((s : ℝ) : 𝕜) • z, u) x + f (c s) z
      with hv
    set A := superpose (fderiv 𝕜 f) (penotCurve 𝕜 E F p)
    have hlip : ∀ t ∈ Ico (0 : ℝ) 1, LipschitzOnWith (‖A‖₊ * ‖x‖₊) (v t) univ := by
      intro t ht
      have htI : t ∈ 𝕀 := hI t (Ico_subset_Icc_self ht)
      have hA : ‖fderiv 𝕜 f (c t)‖ ≤ ‖A‖ := by
        have := A.norm_coe_le_norm ⟨t, htI⟩
        rwa [superpose_apply (F := E × F →L[𝕜] E →L[𝕜] F) hDc hpD] at this
      refine (LipschitzWith.of_dist_le_mul fun u u' ↦ ?_).lipschitzOnWith
      have hvv : v t u - v t u' = fderiv 𝕜 f (c t) (0, u - u') x := by
        simp only [hv, add_sub_add_right_eq_sub, ← sub_apply, ← map_sub,
          Prod.mk_sub_mk, sub_self]
      have h0 : ‖((0 : E), u - u')‖ = ‖u - u'‖ := by simp [Prod.norm_def]
      rw [dist_eq_norm, dist_eq_norm, hvv, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      calc ‖fderiv 𝕜 f (c t) (0, u - u') x‖ ≤ ‖fderiv 𝕜 f (c t) (0, u - u')‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv 𝕜 f (c t)‖ * ‖((0 : E), u - u')‖ * ‖x‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖A‖ * ‖x‖ * ‖u - u'‖ := by
            rw [h0, mul_right_comm]; gcongr
    have hKd : ∀ t ∈ 𝕀, HasDerivAt K (v t (K t)) t := by
      intro t ht
      refine (hasDerivAt_primitive k t).congr_deriv ?_
      have hkt : k ⟨t, ht⟩ = DR (z, 0, k) ⟨t, ht⟩ := congrArg (fun γ : C(𝕀, F) ↦ γ ⟨t, ht⟩) hk
      rw [extendI_of_mem _ ht, hkt, hDRv]
      simp only [penotCurve_apply, zero_add, hv, hK]
      rfl
    have hcd : ∀ t, HasDerivAt c (x, extendI δ t) t := fun t ↦ by
      have h1 : HasDerivAt (fun s : ℝ ↦ ((s : ℝ) : 𝕜) • x) x t := by
        have := (hasDerivAt_id t).smul_const x
        simp only [id, one_smul] at this
        convert this using 1
        funext s
        exact (RCLike.real_smul_eq_coe_smul (K := 𝕜) s x).symm
      exact h1.prodMk ((hasDerivAt_primitive δ t).const_add y)
    have hLd : ∀ t ∈ 𝕀, HasDerivAt L (v t (L t)) t := by
      intro t ht
      have hct := hcO t ht
      have hfd : HasFDerivAt f (fderiv 𝕜 f (c t)) (c t) :=
        (((hf1.differentiableOn one_ne_zero) _ hct).differentiableAt
          (hO.mem_nhds hct)).hasFDerivAt
      have hg : HasFDerivAt (fun q ↦ f q z)
          ((ContinuousLinearMap.apply 𝕜 F z) ∘L fderiv 𝕜 f (c t)) (c t) :=
        (ContinuousLinearMap.apply 𝕜 F z).hasFDerivAt.comp (c t) hfd
      have hgc : HasDerivAt (fun s ↦ f (c s) z) (fderiv 𝕜 f (c t) (x, extendI δ t) z) t :=
        (hg.restrictScalars ℝ).comp_hasDerivAt t (hcd t)
      have hLfun : L = fun s : ℝ ↦ s • f (c s) z :=
        funext fun s ↦ (RCLike.real_smul_eq_coe_smul (K := 𝕜) s _).symm
      have hL' : HasDerivAt L (t • fderiv 𝕜 f (c t) (x, extendI δ t) z + (1 : ℝ) • f (c t) z) t :=
        hLfun ▸ (hasDerivAt_id t).smul hgc
      refine hL'.congr_deriv ?_
      rw [hδs t ht, hfrob (c t) hct x z, one_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
      simp only [hv, hL]
      rw [← Prod.smul_mk, map_smul, smul_apply]
    have hKc : ContinuousOn K (Icc 0 1) := fun t ht ↦
      (hKd t (hI t ht)).continuousAt.continuousWithinAt
    have hLc : ContinuousOn L (Icc 0 1) := fun t ht ↦
      (hLd t (hI t ht)).continuousAt.continuousWithinAt
    have hKL := ODE_solution_unique_of_mem_Icc_right (v := v) (s := fun _ ↦ univ) hlip hKc
      (fun t ht ↦ (hKd t (hI t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) hLc
      (fun t ht ↦ (hLd t (hI t (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun _ _ ↦ mem_univ _) (by simp [hK, hL])
    have h1 : K 1 = L 1 := hKL ⟨zero_le_one, le_rfl⟩
    have hgoal : ((ContinuousLinearMap.snd 𝕜 E F) + P ∘L φ')
        (ContinuousLinearMap.inl 𝕜 E F z) = K 1 := by
      simp [hK, k, one, hP, primitiveCLM_apply]
    rw [ContinuousLinearMap.comp_apply, hgoal, h1]
    simp [hL, hc1]

/-- **The local Frobenius theorem on Banach spaces** (J.-P. Penot, *Sur le théorème de Frobenius*,
Bull. Soc. Math. France 98 (1970), Théorème 1.1, p. 48), over `𝕜 = ℝ` or `ℂ`. Let `O` be open in
`E × F` and `f : O → L(E, F)` of class `C^n`, `1 ≤ n ≤ ∞`, satisfying the integrability
condition (Frob): for `q ∈ O` and `a, b ∈ E`,
`D₁f(q)(a)(b) + D₂f(q)(f(q) a)(b) = D₁f(q)(b)(a) + D₂f(q)(f(q) b)(a)`,
written here as `Df(q)(a, f(q) a)(b) = Df(q)(b, f(q) b)(a)`. Then for every `(x₀, y₀) ∈ O` there
are `r > 0` and a `C^n` map `α` on `B(x₀, r) × B(y₀, r) ⊆ O` with `α(x₀, y) = y` and
`D₁α(x, y) = f(x, α(x, y))`. -/
theorem exists_frobenius {f : E × F → E →L[𝕜] F} {O : Set (E × F)} (hO : IsOpen O)
    {n : ℕ∞} (hn : 1 ≤ n) (hf : ContDiffOn 𝕜 n f O)
    (hfrob : ∀ q ∈ O, ∀ a b : E, fderiv 𝕜 f q (a, f q a) b = fderiv 𝕜 f q (b, f q b) a)
    {x₀ : E} {y₀ : F} (h₀ : (x₀, y₀) ∈ O) :
    ∃ r > (0 : ℝ), ball x₀ r ×ˢ ball y₀ r ⊆ O ∧ ∃ α : E × F → F,
      ContDiffOn 𝕜 n α (ball x₀ r ×ˢ ball y₀ r) ∧ (∀ y ∈ ball y₀ r, α (x₀, y) = y) ∧
      ∀ x ∈ ball x₀ r, ∀ y ∈ ball y₀ r, (x, α (x, y)) ∈ O ∧
        HasFDerivAt (fun x' ↦ α (x', y)) (f (x, α (x, y))) x := by
  -- translate `x₀` to `0`
  set e : E × F := (x₀, 0)
  set g : E × F → E →L[𝕜] F := fun q ↦ f (q + e) with hg
  set O' : Set (E × F) := (· + e) ⁻¹' O
  have hO' : IsOpen O' := hO.preimage (continuous_id.add continuous_const)
  have hg' : ContDiffOn 𝕜 n g O' :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn fun _ hq ↦ hq
  have hgD : ∀ q, fderiv 𝕜 g q = fderiv 𝕜 f (q + e) := fun _ ↦ fderiv_comp_add_right e
  have hgfrob : ∀ q ∈ O', ∀ a b : E, fderiv 𝕜 g q (a, g q a) b = fderiv 𝕜 g q (b, g q b) a :=
    fun q hq a b ↦ by rw [hgD]; exact hfrob _ hq a b
  have h₀' : ((0 : E), y₀) ∈ O' := by simpa [O', e] using h₀
  obtain ⟨r₁, hr₁, β, hβs, hβ0, hβ⟩ := exists_frobenius_zero hO' hn hg' hgfrob h₀'
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO _ h₀
  set r := min r₁ ρ
  have hr : 0 < r := lt_min hr₁ hρ
  have hsub : ∀ x ∈ ball x₀ r, x - x₀ ∈ ball (0 : E) r₁ := fun x hx ↦ by
    rw [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact (mem_ball.1 hx).trans_le (min_le_left _ _)
  have hsuby : ∀ y ∈ ball y₀ r, y ∈ ball y₀ r₁ := fun y hy ↦
    ball_subset_ball (min_le_left _ _) hy
  refine ⟨r, hr, ?_, fun q ↦ β (q.1 - x₀, q.2), ?_, fun y hy ↦ ?_, fun x hx y hy ↦ ?_⟩
  · rw [ball_prod_same]
    exact (ball_subset_ball (min_le_right _ _)).trans hρO
  · refine hβs.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
      fun q hq ↦ ⟨hsub _ hq.1, hsuby _ hq.2⟩
  · simpa using hβ0 y (hsuby y hy)
  · obtain ⟨hO1, hd⟩ := hβ _ (hsub x hx) y (hsuby y hy)
    have hx' : x - x₀ + x₀ = x := sub_add_cancel x x₀
    refine ⟨by simpa [O', e, hx'] using hO1, ?_⟩
    have hd' := hd.comp x ((hasFDerivAt_id x).sub_const x₀)
    have he : (x - x₀, β (x - x₀, y)) + e = (x, β (x - x₀, y)) := by
      simp [e, hx']
    simp only [hg, he, ContinuousLinearMap.comp_id] at hd'
    exact hd'

end Frobenius

section Holomorphic

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **The holomorphic Frobenius theorem on complex Banach spaces.** If `f : O → L(E, F)` is
holomorphic and satisfies (Frob), the solution `α` of `D₁α = f(x, α)`, `α(x₀, y) = y`, given by
`exists_frobenius` is holomorphic (complex analytic). This is [Pen70, Remarque 1]. -/
theorem exists_frobenius_holomorphic {f : E × F → E →L[ℂ] F} {O : Set (E × F)} (hO : IsOpen O)
    (hf : DifferentiableOn ℂ f O)
    (hfrob : ∀ q ∈ O, ∀ a b : E, fderiv ℂ f q (a, f q a) b = fderiv ℂ f q (b, f q b) a)
    {x₀ : E} {y₀ : F} (h₀ : (x₀, y₀) ∈ O) :
    ∃ r > (0 : ℝ), ball x₀ r ×ˢ ball y₀ r ⊆ O ∧ ∃ α : E × F → F,
      ComplexAnalyticOn α (ball x₀ r ×ˢ ball y₀ r) ∧ (∀ y ∈ ball y₀ r, α (x₀, y) = y) ∧
      ∀ x ∈ ball x₀ r, ∀ y ∈ ball y₀ r, (x, α (x, y)) ∈ O ∧
        HasFDerivAt (fun x' ↦ α (x', y)) (f (x, α (x, y))) x := by
  obtain ⟨r, hr, hsub, α, hα, h0, hd⟩ :=
    exists_frobenius (𝕜 := ℂ) hO (n := 1) le_rfl (by exact_mod_cast hf.contDiffOn_one_complex hO)
      hfrob h₀
  have hU : IsOpen (ball x₀ r ×ˢ ball y₀ r) := isOpen_ball.prod isOpen_ball
  exact ⟨r, hr, hsub, α, (hα.differentiableOn one_ne_zero).complexAnalyticOn hU, h0, hd⟩

end Holomorphic

end LocallyConvex.Analysis

/-
Copyright (c) 2026 glaroton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: glaroton
-/
module

public import LocallyConvexAnalysis.Calculus.SmoothExponentialLaw

/-!
# Mixed differentials in any order

A direction of `E₁ × E₂` is *pure* if it is of the form `(v, 0)` or `(0, w)`; we encode a
sequence of pure directions as `u : Fin n → E₁ ⊕ E₂`. We show that the iterated directional
derivatives of a `C^{k,ℓ}` map along pure directions may be taken in any order, and express the
differentials of a `C^{m,m}` map through its mixed differentials.

Reference: [GN26, Proposition 1.7.21] (p. 95) and formula (1.108) in Proposition 1.7.33(b)
(p. 109).

## Main definitions

* `dirOf E₁ E₂`: the pure direction `(v, 0)` or `(0, w)` of `E₁ × E₂` tagged by `v ∈ E₁` or
  `w ∈ E₂`.
* `leftSet u`, `rightSet u`: the positions of the left and right entries of
  `u : Fin n → α ⊕ β`.
* `leftVec u`, `rightVec u`: the left and right entries of `u`, in the order in which they
  appear.

## Main results

* `ContDiffMBOn₂.hasDirDerivAt_dirOf`, `ContDiffMBOn₂.iteratedDMB_dirOf`: for a `C^{k,ℓ}` map
  `f` and pure directions with at most `k` left and `ℓ` right ones, the iterated directional
  derivatives of `f` along them exist on `U × V`, and equal the mixed differential
  `d^(i,j) f(x, y, leftVec u, rightVec u)` (Proposition 1.7.21).
* `ContDiffMBOn₂.iteratedDMB₂_perm_left`, `ContDiffMBOn₂.iteratedDMB₂_perm_right`: the mixed
  differentials are symmetric in the `vᵢ` and in the `wⱼ`. Together with the previous item this is
  Proposition 1.7.21: the derivatives may be taken in any order;
  `ContDiffMBOn₂.iteratedDMB_append_perm` is its literal form.
* `ContDiffMBOn₂.iteratedDMB_eq_sum`: the formula (1.108),
  `d^(m) f(x, y, w) = ∑_I d^(|I|, m - |I|) f(x, y, (w_{i,1})_{i ∈ I}, (w_{j,2})_{j ∉ I})`, for
  `C^{m,m}` maps.

## References

* [H. Glöckner, K.-H. Neeb, *Infinite-Dimensional Lie Groups*][GN26]
-/

@[expose] public section

open Set Filter Function
open scoped Topology

noncomputable section

namespace LocallyConvex.Analysis

/-! ### Left and right parts of a sequence of tagged directions -/

section Combinatorics

variable {α β : Type*} {n : ℕ}

/-- The positions of the left entries. -/
def leftSet (u : Fin n → α ⊕ β) : Finset (Fin n) := Finset.univ.filter fun a ↦ (u a).isLeft

/-- The positions of the right entries. -/
def rightSet (u : Fin n → α ⊕ β) : Finset (Fin n) := Finset.univ.filter fun a ↦ (u a).isRight

/-- The left entries, in order. -/
def leftVec [Zero α] (u : Fin n → α ⊕ β) : Fin (leftSet u).card → α := fun c ↦
  Sum.elim id (fun _ ↦ 0) (u ((leftSet u).orderEmbOfFin rfl c))

/-- The right entries, in order. -/
def rightVec [Zero β] (u : Fin n → α ⊕ β) : Fin (rightSet u).card → β := fun c ↦
  Sum.elim (fun _ ↦ 0) id (u ((rightSet u).orderEmbOfFin rfl c))

/-- Changing the cardinality proof in `orderEmbOfFin`. -/
theorem orderEmbOfFin_cast {γ : Type*} [LinearOrder γ] (s : Finset γ) {k : ℕ} (h : s.card = k)
    (c : Fin s.card) : s.orderEmbOfFin h (Fin.cast h c) = s.orderEmbOfFin rfl c := by
  subst h
  rfl

/-- `orderEmbOfFin` of equal finsets. -/
theorem orderEmbOfFin_congr {γ : Type*} [LinearOrder γ] {s t : Finset γ} (hst : s = t)
    (c : Fin s.card) :
    s.orderEmbOfFin rfl c = t.orderEmbOfFin rfl (Fin.cast (congrArg Finset.card hst) c) := by
  subst hst
  rfl

/-- The order embedding of `s.map castSucc` is `castSucc` of that of `s`. -/
theorem orderEmbOfFin_map_castSucc (s : Finset (Fin n)) (h : (s.map Fin.castSuccEmb).card = s.card)
    (c : Fin (s.map Fin.castSuccEmb).card) :
    (s.map Fin.castSuccEmb).orderEmbOfFin rfl c =
      Fin.castSucc (s.orderEmbOfFin rfl (Fin.cast h c)) := by
  have := Finset.orderEmbOfFin_unique (s := s.map Fin.castSuccEmb) h
    (f := fun c ↦ Fin.castSucc (s.orderEmbOfFin rfl c))
    (fun c ↦ Finset.mem_map_of_mem _ (s.orderEmbOfFin_mem rfl c))
    (Fin.strictMono_castSucc.comp (s.orderEmbOfFin rfl).strictMono)
  exact ((congrFun this (Fin.cast h c)).trans (orderEmbOfFin_cast _ h c)).symm

/-- The order embedding of `insert (last n) (s.map castSucc)`. -/
theorem orderEmbOfFin_insert_last (s : Finset (Fin n))
    (h : (insert (Fin.last n) (s.map Fin.castSuccEmb)).card = s.card + 1)
    (c : Fin (insert (Fin.last n) (s.map Fin.castSuccEmb)).card) :
    (insert (Fin.last n) (s.map Fin.castSuccEmb)).orderEmbOfFin rfl c =
      Fin.lastCases (Fin.last n) (fun c' ↦ Fin.castSucc (s.orderEmbOfFin rfl c'))
        (Fin.cast h c) := by
  have hmono : StrictMono (Fin.lastCases (motive := fun _ ↦ Fin (n + 1)) (Fin.last n)
      fun c' ↦ Fin.castSucc (s.orderEmbOfFin rfl c')) := by
    intro a b hab
    induction b using Fin.lastCases with
    | last =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (lt_irrefl _)
      | cast a =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        exact Fin.castSucc_lt_last _
    | cast b =>
      induction a using Fin.lastCases with
      | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last b).le)
      | cast a =>
        simp only [Fin.lastCases_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.2 ((s.orderEmbOfFin rfl).strictMono
          (Fin.castSucc_lt_castSucc_iff.1 hab))
  have := Finset.orderEmbOfFin_unique (s := insert (Fin.last n) (s.map Fin.castSuccEmb)) h
    (f := Fin.lastCases (motive := fun _ ↦ Fin (n + 1)) (Fin.last n)
      fun c' ↦ Fin.castSucc (s.orderEmbOfFin rfl c'))
    (fun c ↦ by
      induction c using Fin.lastCases with
      | last => simp
      | cast c =>
        simp only [Fin.lastCases_castSucc]
        exact Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ (s.orderEmbOfFin_mem rfl c)))
    hmono
  exact ((congrFun this (Fin.cast h c)).trans (orderEmbOfFin_cast _ h c)).symm

variable (u : Fin (n + 1) → α ⊕ β)

theorem leftSet_of_last_inl {a : α} (ha : u (Fin.last n) = Sum.inl a) :
    leftSet u = insert (Fin.last n) ((leftSet (Fin.init u)).map Fin.castSuccEmb) := by
  ext c
  induction c using Fin.lastCases with
  | last => simp [leftSet, ha]
  | cast c =>
    simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.castSucc_ne_last, false_or, Finset.mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_inj, exists_eq_right]
    rfl

theorem rightSet_of_last_inl {a : α} (ha : u (Fin.last n) = Sum.inl a) :
    rightSet u = (rightSet (Fin.init u)).map Fin.castSuccEmb := by
  ext c
  induction c using Fin.lastCases with
  | last =>
    simp only [rightSet, Finset.mem_filter, Finset.mem_univ, true_and, ha, Sum.isRight_inl,
      Bool.false_eq_true, false_iff, Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
    exact fun c _ h ↦ Fin.castSucc_ne_last c h
  | cast c =>
    simp only [rightSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castSuccEmb_apply, Fin.castSucc_inj, exists_eq_right]
    rfl

theorem rightSet_of_last_inr {b : β} (hb : u (Fin.last n) = Sum.inr b) :
    rightSet u = insert (Fin.last n) ((rightSet (Fin.init u)).map Fin.castSuccEmb) := by
  ext c
  induction c using Fin.lastCases with
  | last => simp [rightSet, hb]
  | cast c =>
    simp only [rightSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.castSucc_ne_last, false_or, Finset.mem_map, Fin.castSuccEmb_apply,
      Fin.castSucc_inj, exists_eq_right]
    rfl

theorem leftSet_of_last_inr {b : β} (hb : u (Fin.last n) = Sum.inr b) :
    leftSet u = (leftSet (Fin.init u)).map Fin.castSuccEmb := by
  ext c
  induction c using Fin.lastCases with
  | last =>
    simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and, hb, Sum.isLeft_inr,
      Bool.false_eq_true, false_iff, Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
    exact fun c _ h ↦ Fin.castSucc_ne_last c h
  | cast c =>
    simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castSuccEmb_apply, Fin.castSucc_inj, exists_eq_right]
    rfl

theorem leftVec_of_last_inl [Zero α] {a : α} (ha : u (Fin.last n) = Sum.inl a)
    (h : (leftSet u).card = (leftSet (Fin.init u)).card + 1) (c : Fin (leftSet u).card) :
    leftVec u c = Fin.snoc (α := fun _ ↦ α) (leftVec (Fin.init u)) a (Fin.cast h c) := by
  have hS := leftSet_of_last_inl u ha
  have h₂ : (insert (Fin.last n) ((leftSet (Fin.init u)).map Fin.castSuccEmb)).card =
      (leftSet (Fin.init u)).card + 1 := (congrArg Finset.card hS).symm.trans h
  have e := orderEmbOfFin_congr hS c
  rw [orderEmbOfFin_insert_last _ h₂] at e
  have hc : Fin.cast h₂ (Fin.cast (congrArg Finset.card hS) c) = Fin.cast h c := Fin.ext rfl
  rw [hc] at e
  simp only [leftVec]
  rw [e]
  obtain ⟨d, hd⟩ : ∃ d, Fin.cast h c = d := ⟨_, rfl⟩
  rw [hd]
  induction d using Fin.lastCases with
  | last => simp [ha]
  | cast d =>
    simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc, leftVec]
    rfl

theorem rightVec_of_last_inl [Zero β] {a : α} (ha : u (Fin.last n) = Sum.inl a)
    (h : (rightSet u).card = (rightSet (Fin.init u)).card) (c : Fin (rightSet u).card) :
    rightVec u c = rightVec (Fin.init u) (Fin.cast h c) := by
  have hS := rightSet_of_last_inl u ha
  have h₂ : ((rightSet (Fin.init u)).map Fin.castSuccEmb).card =
      (rightSet (Fin.init u)).card := (congrArg Finset.card hS).symm.trans h
  have e := orderEmbOfFin_congr hS c
  rw [orderEmbOfFin_map_castSucc _ h₂] at e
  have hc : Fin.cast h₂ (Fin.cast (congrArg Finset.card hS) c) = Fin.cast h c := Fin.ext rfl
  rw [hc] at e
  simp only [rightVec]
  rw [e]
  rfl

theorem rightVec_of_last_inr [Zero β] {b : β} (hb : u (Fin.last n) = Sum.inr b)
    (h : (rightSet u).card = (rightSet (Fin.init u)).card + 1) (c : Fin (rightSet u).card) :
    rightVec u c = Fin.snoc (α := fun _ ↦ β) (rightVec (Fin.init u)) b (Fin.cast h c) := by
  have hS := rightSet_of_last_inr u hb
  have h₂ : (insert (Fin.last n) ((rightSet (Fin.init u)).map Fin.castSuccEmb)).card =
      (rightSet (Fin.init u)).card + 1 := (congrArg Finset.card hS).symm.trans h
  have e := orderEmbOfFin_congr hS c
  rw [orderEmbOfFin_insert_last _ h₂] at e
  have hc : Fin.cast h₂ (Fin.cast (congrArg Finset.card hS) c) = Fin.cast h c := Fin.ext rfl
  rw [hc] at e
  simp only [rightVec]
  rw [e]
  obtain ⟨d, hd⟩ : ∃ d, Fin.cast h c = d := ⟨_, rfl⟩
  rw [hd]
  induction d using Fin.lastCases with
  | last => simp [hb]
  | cast d =>
    simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc, rightVec]
    rfl

theorem leftVec_of_last_inr [Zero α] {b : β} (hb : u (Fin.last n) = Sum.inr b)
    (h : (leftSet u).card = (leftSet (Fin.init u)).card) (c : Fin (leftSet u).card) :
    leftVec u c = leftVec (Fin.init u) (Fin.cast h c) := by
  have hS := leftSet_of_last_inr u hb
  have h₂ : ((leftSet (Fin.init u)).map Fin.castSuccEmb).card =
      (leftSet (Fin.init u)).card := (congrArg Finset.card hS).symm.trans h
  have e := orderEmbOfFin_congr hS c
  rw [orderEmbOfFin_map_castSucc _ h₂] at e
  have hc : Fin.cast h₂ (Fin.cast (congrArg Finset.card hS) c) = Fin.cast h c := Fin.ext rfl
  rw [hc] at e
  simp only [leftVec]
  rw [e]
  rfl

section Append

variable {i j : ℕ} (v : Fin i → α) (w : Fin j → β)

/-- The entries of `Fin.append (inl ∘ v) (inr ∘ w)`. -/
theorem append_inl_inr (x : Fin (i + j)) :
    Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) x = if h : (x : ℕ) < i then Sum.inl (v ⟨x, h⟩)
      else Sum.inr (w ⟨x - i, by have := x.2; omega⟩) := by
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) x
  · simp [Fin.append_left]
  · simp [Fin.append_right]

variable (π : Equiv.Perm (Fin (i + j)))

/-- The left part of a shuffle of `inl ∘ v` and `inr ∘ w` is `v` composed with an injection. -/
theorem exists_leftVec_append [Zero α] :
    ∃ g : Fin (leftSet (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π)).card → Fin i,
      Injective g ∧ ∀ c, leftVec (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π) c = v (g c) := by
  set u := Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π
  have key : ∀ a, (u a).isLeft = true → ((π a : Fin (i + j)) : ℕ) < i := fun a ha ↦ by
    by_contra h
    simp [u, append_inl_inr, h] at ha
  have hlt : ∀ c, ((π ((leftSet u).orderEmbOfFin rfl c) : Fin (i + j)) : ℕ) < i := fun c ↦
    key _ (Finset.mem_filter.1 ((leftSet u).orderEmbOfFin_mem rfl c)).2
  refine ⟨fun c ↦ ⟨π ((leftSet u).orderEmbOfFin rfl c), hlt c⟩, fun c c' hcc ↦ ?_, fun c ↦ ?_⟩
  · have h₃ := congrArg (fun z : Fin i ↦ (z : ℕ)) hcc
    dsimp only at h₃
    exact ((leftSet u).orderEmbOfFin rfl).injective (π.injective (Fin.ext h₃))
  · have hval : ∀ a (h : ((π a : Fin (i + j)) : ℕ) < i), u a = Sum.inl (v ⟨π a, h⟩) :=
      fun a h ↦ by simp [u, append_inl_inr, h]
    change Sum.elim id (fun _ ↦ 0) (u ((leftSet u).orderEmbOfFin rfl c)) =
      v ⟨π ((leftSet u).orderEmbOfFin rfl c), hlt c⟩
    rw [hval _ (hlt c)]
    rfl

/-- The right part of a shuffle of `inl ∘ v` and `inr ∘ w` is `w` composed with an injection. -/
theorem exists_rightVec_append [Zero β] :
    ∃ g : Fin (rightSet (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π)).card → Fin j,
      Injective g ∧ ∀ c, rightVec (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π) c = w (g c) := by
  set u := Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π
  have key : ∀ a, (u a).isRight = true → ¬ ((π a : Fin (i + j)) : ℕ) < i := fun a ha h ↦ by
    simp [u, append_inl_inr, h] at ha
  have hge : ∀ c, ¬ ((π ((rightSet u).orderEmbOfFin rfl c) : Fin (i + j)) : ℕ) < i := fun c ↦
    key _ (Finset.mem_filter.1 ((rightSet u).orderEmbOfFin_mem rfl c)).2
  have hlt : ∀ c, ((π ((rightSet u).orderEmbOfFin rfl c) : Fin (i + j)) : ℕ) - i < j := fun c ↦
    Nat.sub_lt_left_of_lt_add (not_lt.1 (hge c)) (Fin.isLt _)
  refine ⟨fun c ↦ ⟨π ((rightSet u).orderEmbOfFin rfl c) - i, hlt c⟩, fun c c' hcc ↦ ?_,
    fun c ↦ ?_⟩
  · have h₁ := hge c
    have h₂ := hge c'
    have h₃ := congrArg (fun z : Fin j ↦ (z : ℕ)) hcc
    dsimp only at h₃
    have : π ((rightSet u).orderEmbOfFin rfl c) = π ((rightSet u).orderEmbOfFin rfl c') :=
      Fin.ext (by omega)
    exact ((rightSet u).orderEmbOfFin rfl).injective (π.injective this)
  · have hval : ∀ a (h : ¬ ((π a : Fin (i + j)) : ℕ) < i),
        u a = Sum.inr (w ⟨π a - i, by have := (π a).2; omega⟩) :=
      fun a h ↦ by simp [u, append_inl_inr, h]
    change Sum.elim (fun _ ↦ 0) id (u ((rightSet u).orderEmbOfFin rfl c)) =
      w ⟨π ((rightSet u).orderEmbOfFin rfl c) - i, hlt c⟩
    rw [hval _ (hge c)]
    rfl

/-- The left and right parts have `i` and `j` entries. -/
theorem card_leftSet_append [Zero α] [Zero β] :
    (leftSet (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π)).card = i ∧
      (rightSet (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π)).card = j := by
  obtain ⟨g, hg, -⟩ := exists_leftVec_append v w π
  obtain ⟨g', hg', -⟩ := exists_rightVec_append v w π
  have h₁ := Fintype.card_le_of_injective g hg
  have h₂ := Fintype.card_le_of_injective g' hg'
  have h₃ := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun a ↦ ((Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π) a).isLeft)
  have h₄ : (rightSet (Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π)) =
      Finset.univ.filter fun a ↦ ¬ ((Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π) a).isLeft := by
    ext a
    simp [rightSet]
  simp only [Fintype.card_fin] at h₁ h₂
  rw [← leftSet, ← h₄, Finset.card_univ, Fintype.card_fin] at h₃
  omega

end Append

end Combinatorics

/-! ### Mixed differentials along pure directions -/

section Mixed

universe u u' v

variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [LocallyConvexSpace ℝ E₁] [T2Space E₁]
  {E₂ : Type u'} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂]
  {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  {k ℓ : ℕ} {f : E₁ × E₂ → F} {U : Set E₁} {V : Set E₂}

variable (E₁ E₂) in
/-- The pure direction `(v, 0)` or `(0, w)` of `E₁ × E₂` tagged by `v ∈ E₁` or `w ∈ E₂`. -/
def dirOf : E₁ ⊕ E₂ → E₁ × E₂ := Sum.elim (fun v ↦ (v, 0)) fun w ↦ (0, w)

omit [TopologicalSpace E₁] [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁]
  [LocallyConvexSpace ℝ E₁] [T2Space E₁] [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F] in
/-- Mixed differentials at equal arguments, up to casts of the numbers of directions. -/
theorem iteratedDMB₂_cast (f : E₁ × E₂ → F) {i i' j j' : ℕ} (hi : i = i') (hj : j = j')
    (p : E₁ × E₂) (v : Fin i → E₁) (w : Fin j → E₂) (v' : Fin i' → E₁) (w' : Fin j' → E₂)
    (hv : ∀ c, v c = v' (Fin.cast hi c)) (hw : ∀ c, w c = w' (Fin.cast hj c)) :
    iteratedDMB₂ i j f (p, v, w) = iteratedDMB₂ i' j' f (p, v', w') := by
  subst hi hj
  have hv' : v = v' := funext hv
  have hw' : w = w' := funext hw
  rw [hv', hw']

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **[GN26, Proposition 1.7.21]**, for any order of the directions: for a `C^{k,ℓ}` map
`f` on `U × V` and pure directions `dirOf ∘ u` with at most `k` left and `ℓ` right ones, the
iterated directional derivative of `f` along them is the mixed differential
`d^(i,j) f(x, y, leftVec u, rightVec u)` on `U × V`. By induction on the number of directions,
with `ContDiffMBOn₂.hasDirDerivAt_left` and `ContDiffMBOn₂.hasDirDerivAt_right`. -/
theorem ContDiffMBOn₂.iteratedDMB_dirOf (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) : ∀ (n : ℕ) (u : Fin n → E₁ ⊕ E₂),
      (leftSet u).card ≤ k → (rightSet u).card ≤ ℓ → ∀ p ∈ U ×ˢ V,
        iteratedDMB n f (p, dirOf E₁ E₂ ∘ u) =
          iteratedDMB₂ (leftSet u).card (rightSet u).card f (p, leftVec u, rightVec u) := by
  intro n
  induction n with
  | zero =>
    intro u _ _ p _
    have h0 : ∀ s : Finset (Fin 0), s.card = 0 := fun s ↦ by
      rw [Finset.eq_empty_of_isEmpty s, Finset.card_empty]
    exact (iteratedDMB₂_cast f (h0 _) (h0 _) p _ _ Fin.elim0 Fin.elim0
      (fun c ↦ (Fin.cast (h0 _) c).elim0) fun c ↦ (Fin.cast (h0 _) c).elim0).symm
  | succ n ih =>
    intro u hk hℓ p hp
    obtain ⟨x, y⟩ := p
    obtain ⟨hx, hy⟩ := hp
    have hUV : IsOpen (U ×ˢ V) := hU.prod hV
    rcases hlast : u (Fin.last n) with a | b
    · -- the last direction is `(a, 0)`
      have hS := leftSet_of_last_inl u hlast
      have hL : (leftSet u).card = (leftSet (Fin.init u)).card + 1 := by
        rw [hS, Finset.card_insert_of_notMem (by simp [Fin.castSucc_ne_last]), Finset.card_map]
      have hR : (rightSet u).card = (rightSet (Fin.init u)).card := by
        rw [rightSet_of_last_inl u hlast, Finset.card_map]
      have hev : (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u)) =ᶠ[𝓝 (x, y)]
          fun z ↦ iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
            (z, leftVec (Fin.init u), rightVec (Fin.init u)) :=
        Filter.eventually_of_mem (hUV.mem_nhds ⟨hx, hy⟩) fun z hz ↦
          ih (Fin.init u) (by omega) (by omega) z hz
      have hd := hf.hasDirDerivAt_left (by omega) (by omega) hx hy
        (Fin.snoc (α := fun _ ↦ E₁) (leftVec (Fin.init u)) a) (rightVec (Fin.init u))
      simp only [Fin.init_snoc, Fin.snoc_last] at hd
      have hd' := hasDirDerivAt_slice (g := fun z ↦
          iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
          (z, leftVec (Fin.init u), rightVec (Fin.init u))) |>.2 hd
      rw [iteratedDMB_succ]
      change dMB (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u))
        ((x, y), dirOf E₁ E₂ (u (Fin.last n))) = _
      rw [hlast]
      change dMB (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u)) ((x, y), (a, 0)) = _
      rw [dMB_congr_of_eventuallyEq hev, hd'.dMB_eq]
      exact (iteratedDMB₂_cast f hL hR _ _ _ _ _ (leftVec_of_last_inl u hlast hL)
        (rightVec_of_last_inl u hlast hR)).symm
    · -- the last direction is `(0, b)`
      have hS := rightSet_of_last_inr u hlast
      have hR : (rightSet u).card = (rightSet (Fin.init u)).card + 1 := by
        rw [hS, Finset.card_insert_of_notMem (by simp [Fin.castSucc_ne_last]), Finset.card_map]
      have hL : (leftSet u).card = (leftSet (Fin.init u)).card := by
        rw [leftSet_of_last_inr u hlast, Finset.card_map]
      have hev : (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u)) =ᶠ[𝓝 (x, y)]
          fun z ↦ iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
            (z, leftVec (Fin.init u), rightVec (Fin.init u)) :=
        Filter.eventually_of_mem (hUV.mem_nhds ⟨hx, hy⟩) fun z hz ↦
          ih (Fin.init u) (by omega) (by omega) z hz
      have hd := hf.hasDirDerivAt_right hU hV _ (by omega) _ (by omega) x hx y hy
        (leftVec (Fin.init u)) (rightVec (Fin.init u)) b
      have hd' := hasDirDerivAt_slice₂ (g := fun z ↦
          iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
          (z, leftVec (Fin.init u), rightVec (Fin.init u))) |>.2 hd
      rw [iteratedDMB_succ]
      change dMB (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u))
        ((x, y), dirOf E₁ E₂ (u (Fin.last n))) = _
      rw [hlast]
      change dMB (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u)) ((x, y), (0, b)) = _
      rw [dMB_congr_of_eventuallyEq hev, hd'.dMB_eq]
      exact (iteratedDMB₂_cast f hL hR _ _ _ _ _ (leftVec_of_last_inr u hlast hL)
        (rightVec_of_last_inr u hlast hR)).symm

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **[GN26, Proposition 1.7.21]**, existence: under the hypotheses of
`ContDiffMBOn₂.iteratedDMB_dirOf`, each directional derivative in the iteration exists on
`U × V`. -/
theorem ContDiffMBOn₂.hasDirDerivAt_dirOf (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) {n : ℕ} (u : Fin (n + 1) → E₁ ⊕ E₂)
    (hk : (leftSet u).card ≤ k) (hℓ : (rightSet u).card ≤ ℓ) {p : E₁ × E₂} (hp : p ∈ U ×ˢ V) :
    HasDirDerivAt (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u)) p
      (dirOf E₁ E₂ (u (Fin.last n))) (iteratedDMB (n + 1) f (p, dirOf E₁ E₂ ∘ u)) := by
  obtain ⟨x, y⟩ := p
  obtain ⟨hx, hy⟩ := hp
  have hUV : IsOpen (U ×ˢ V) := hU.prod hV
  have hcard : (leftSet (Fin.init u)).card ≤ k ∧ (rightSet (Fin.init u)).card ≤ ℓ := by
    rcases hlast : u (Fin.last n) with a | b
    · rw [leftSet_of_last_inl u hlast, Finset.card_insert_of_notMem
        (by simp [Fin.castSucc_ne_last]), Finset.card_map] at hk
      rw [rightSet_of_last_inl u hlast, Finset.card_map] at hℓ
      exact ⟨by omega, hℓ⟩
    · rw [rightSet_of_last_inr u hlast, Finset.card_insert_of_notMem
        (by simp [Fin.castSucc_ne_last]), Finset.card_map] at hℓ
      rw [leftSet_of_last_inr u hlast, Finset.card_map] at hk
      exact ⟨hk, by omega⟩
  have hev : (fun z ↦ iteratedDMB n f (z, dirOf E₁ E₂ ∘ Fin.init u)) =ᶠ[𝓝 (x, y)]
      fun z ↦ iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
        (z, leftVec (Fin.init u), rightVec (Fin.init u)) :=
    Filter.eventually_of_mem (hUV.mem_nhds ⟨hx, hy⟩) fun z hz ↦
      hf.iteratedDMB_dirOf hU hV n (Fin.init u) hcard.1 hcard.2 z hz
  rw [hf.iteratedDMB_dirOf hU hV (n + 1) u hk hℓ _ ⟨hx, hy⟩]
  refine HasDirDerivAt.congr_of_eventuallyEq ?_ hev.symm
  rcases hlast : u (Fin.last n) with a | b
  · have hL : (leftSet u).card = (leftSet (Fin.init u)).card + 1 := by
      rw [leftSet_of_last_inl u hlast, Finset.card_insert_of_notMem
        (by simp [Fin.castSucc_ne_last]), Finset.card_map]
    have hR : (rightSet u).card = (rightSet (Fin.init u)).card := by
      rw [rightSet_of_last_inl u hlast, Finset.card_map]
    have hd := hf.hasDirDerivAt_left (by omega) hcard.2 hx hy
      (Fin.snoc (α := fun _ ↦ E₁) (leftVec (Fin.init u)) a) (rightVec (Fin.init u))
    simp only [Fin.init_snoc, Fin.snoc_last] at hd
    rw [iteratedDMB₂_cast f hL hR _ _ _ _ _ (leftVec_of_last_inl u hlast hL)
      (rightVec_of_last_inl u hlast hR)]
    exact hasDirDerivAt_slice (g := fun z ↦
          iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
        (z, leftVec (Fin.init u), rightVec (Fin.init u))) |>.2 hd
  · have hR : (rightSet u).card = (rightSet (Fin.init u)).card + 1 := by
      rw [rightSet_of_last_inr u hlast, Finset.card_insert_of_notMem
        (by simp [Fin.castSucc_ne_last]), Finset.card_map]
    have hL : (leftSet u).card = (leftSet (Fin.init u)).card := by
      rw [leftSet_of_last_inr u hlast, Finset.card_map]
    have hd := hf.hasDirDerivAt_right hU hV _ hcard.1 _ (by omega) x hx y hy
      (leftVec (Fin.init u)) (rightVec (Fin.init u)) b
    rw [iteratedDMB₂_cast f hL hR _ _ _ _ _ (leftVec_of_last_inr u hlast hL)
      (rightVec_of_last_inr u hlast hR)]
    exact hasDirDerivAt_slice₂ (g := fun z ↦
          iteratedDMB₂ (leftSet (Fin.init u)).card (rightSet (Fin.init u)).card f
        (z, leftVec (Fin.init u), rightVec (Fin.init u))) |>.2 hd

omit [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [LocallyConvexSpace ℝ E₂] [T2Space E₂] in
/-- **The mixed differentials are symmetric in the first-variable directions**
([GN26, Proposition 1.7.21]): `x ↦ d^(0,j) f(x, y, w)` is `C^k`. -/
theorem ContDiffMBOn₂.iteratedDMB₂_perm_left (hU : IsOpen U) (hf : ContDiffMBOn₂ k ℓ f U V)
    {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ) {x : E₁} (hx : x ∈ U) {y : E₂} (hy : y ∈ V)
    (v : Fin i → E₁) (w : Fin j → E₂) (σ : Equiv.Perm (Fin i)) :
    iteratedDMB₂ i j f ((x, y), v ∘ σ, w) = iteratedDMB₂ i j f ((x, y), v, w) :=
  (hf.contDiffMBOn_left j hj y hy w).iteratedDMB_perm hU hi hx v σ

omit [LocallyConvexSpace ℝ E₁] [T2Space E₁] in
/-- **The mixed differentials are symmetric in the second-variable directions**
([GN26, Proposition 1.7.21]): the partial maps `f(x, ·)` are `C^ℓ`. -/
theorem ContDiffMBOn₂.iteratedDMB₂_perm_right (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) {i j : ℕ} (hj : j ≤ ℓ) {x : E₁} (hx : x ∈ U) {y : E₂}
    (hy : y ∈ V) (v : Fin i → E₁) (w : Fin j → E₂) (σ : Equiv.Perm (Fin j)) :
    iteratedDMB₂ i j f ((x, y), v, w ∘ σ) = iteratedDMB₂ i j f ((x, y), v, w) := by
  have hev : (fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w ∘ σ)) =ᶠ[𝓝 x]
      fun x' ↦ iteratedDMB j (fun y' ↦ f (x', y')) (y, w) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun x' hx' ↦
      (hf.contDiffMBOn_right x' hx').iteratedDMB_perm hV hj hy w σ
  exact iteratedDMB_congr_of_eventuallyEq i hev v

/-- **Proposition 1.7.21**, literal form: for a `C^{k,ℓ}` map `f`, `i ≤ k`, `j ≤ ℓ`, and a
permutation `π` of `{1, ..., i + j}`, the iterated directional derivative of `f` along the
directions `(v₁, 0), ..., (vᵢ, 0), (0, w₁), ..., (0, wⱼ)`, taken in the order prescribed by `π`,
exists on `U × V` (`ContDiffMBOn₂.hasDirDerivAt_dirOf`) and equals `d^(i,j) f(x, y, v, w)`. -/
theorem ContDiffMBOn₂.iteratedDMB_append_perm (hU : IsOpen U) (hV : IsOpen V)
    (hf : ContDiffMBOn₂ k ℓ f U V) {i j : ℕ} (hi : i ≤ k) (hj : j ≤ ℓ) (v : Fin i → E₁)
    (w : Fin j → E₂) (π : Equiv.Perm (Fin (i + j))) {p : E₁ × E₂} (hp : p ∈ U ×ˢ V) :
    iteratedDMB (i + j) f (p, dirOf E₁ E₂ ∘ Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π) =
      iteratedDMB₂ i j f (p, v, w) := by
  obtain ⟨x, y⟩ := p
  have hp' := hp
  simp only [Set.mem_prod] at hp'
  set u := Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π
  obtain ⟨hL, hR⟩ := card_leftSet_append v w π
  obtain ⟨g, hg, hgv⟩ := exists_leftVec_append v w π
  obtain ⟨g', hg', hgw⟩ := exists_rightVec_append v w π
  have hgb : Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hg, by simp [hL]⟩
  have hgb' : Bijective g' :=
    (Fintype.bijective_iff_injective_and_card g').2 ⟨hg', by simp [hR]⟩
  set σ : Equiv.Perm (Fin i) := (finCongr hL).symm.trans (Equiv.ofBijective g hgb)
  set σ' : Equiv.Perm (Fin j) := (finCongr hR).symm.trans (Equiv.ofBijective g' hgb')
  rw [show dirOf E₁ E₂ ∘ Fin.append (Sum.inl ∘ v) (Sum.inr ∘ w) ∘ π = dirOf E₁ E₂ ∘ u from rfl,
    hf.iteratedDMB_dirOf hU hV (i + j) u (hL.trans_le hi) (hR.trans_le hj) _ hp,
    iteratedDMB₂_cast f hL hR _ _ _ (v ∘ σ) (w ∘ σ') (fun c ↦ by rw [hgv]; simp [σ])
      (fun c ↦ by rw [hgw]; simp [σ']),
    hf.iteratedDMB₂_perm_right hU hV hj hp'.1 hp'.2,
    hf.iteratedDMB₂_perm_left hU hi hj hp'.1 hp'.2]

/-- **The formula (1.108)** of [GN26, Proposition 1.7.33(b)]: for a `C^{m,m}` map `f`
(which is `C^m`, `ContDiffMBOn₂.contDiffMBOn_prod`) and `w ∈ (E₁ × E₂)^m`,
`d^(m) f(x, y, w) = ∑_I d^(|I|, m - |I|) f(x, y, (w_{i,1})_{i ∈ I}, (w_{j,2})_{j ∉ I})`, the
indices in increasing order. Expand `d^(m) f(x, y, ·)` multilinearly along
`w_a = (w_{a,1}, 0) + (0, w_{a,2})` and apply `ContDiffMBOn₂.iteratedDMB_dirOf` to each term. -/
theorem ContDiffMBOn₂.iteratedDMB_eq_sum (hU : IsOpen U) (hV : IsOpen V) {m : ℕ}
    (hf : ContDiffMBOn₂ m m f U V) {p : E₁ × E₂} (hp : p ∈ U ×ˢ V) (w : Fin m → E₁ × E₂) :
    iteratedDMB m f (p, w) = ∑ I : Finset (Fin m), iteratedDMB₂ I.card Iᶜ.card f
      (p, fun a ↦ (w (I.orderEmbOfFin rfl a)).1, fun b ↦ (w (Iᶜ.orderEmbOfFin rfl b)).2) := by
  classical
  obtain ⟨M, hM, -⟩ := (hf.contDiffMBOn_prod hU hV).exists_iteratedDMB_multilinear (hU.prod hV) hp
  have hw : w = (fun a ↦ ((w a).1, (0 : E₂))) + fun a ↦ ((0 : E₁), (w a).2) :=
    funext fun a ↦ by simp
  rw [← hM w]
  conv_lhs => rw [hw, M.map_add_univ]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  -- the term of `I` is a derivative along pure directions
  set u : Fin m → E₁ ⊕ E₂ := fun a ↦ if a ∈ I then Sum.inl (w a).1 else Sum.inr (w a).2
  have hpw : I.piecewise (fun a ↦ ((w a).1, (0 : E₂))) (fun a ↦ ((0 : E₁), (w a).2)) =
      dirOf E₁ E₂ ∘ u := funext fun a ↦ by
    by_cases ha : a ∈ I <;> simp [Finset.piecewise, ha, u, dirOf]
  have hL : leftSet u = I := by
    ext a
    by_cases ha : a ∈ I <;> simp [leftSet, ha, u]
  have hR : rightSet u = Iᶜ := by
    ext a
    by_cases ha : a ∈ I <;> simp [rightSet, ha, u]
  rw [hM, hpw,
    hf.iteratedDMB_dirOf hU hV m u ((Finset.card_le_univ _).trans (by simp))
      ((Finset.card_le_univ _).trans (by simp)) p hp]
  refine iteratedDMB₂_cast f (congrArg Finset.card hL) (congrArg Finset.card hR) p _ _ _ _
    (fun c ↦ ?_) fun c ↦ ?_
  · simp only [leftVec]
    rw [orderEmbOfFin_congr hL c]
    have hmem := I.orderEmbOfFin_mem rfl (Fin.cast (congrArg Finset.card hL) c)
    simp [u, hmem]
  · simp only [rightVec]
    rw [orderEmbOfFin_congr hR c]
    have hmem := Iᶜ.orderEmbOfFin_mem rfl (Fin.cast (congrArg Finset.card hR) c)
    rw [Finset.mem_compl] at hmem
    simp [u, hmem]

end Mixed

end LocallyConvex.Analysis

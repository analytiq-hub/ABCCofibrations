/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Anderson–Brown–Cisinski cofibration categories

Following Definition 1.1.1 of Rădulescu-Banu, *Cofibrations in Homotopy Theory*,
https://arxiv.org/abs/math/0610009.

`ABCPrecofibrationCategory` imposes CF1–CF4 on existing mathlib morphism classes.
`ABCCofibrationCategory` adds CF5–CF6. An initial object is supplied separately
by `[HasInitial C]`; no general cocompleteness or fibrations are required.
Coproducts are indexed by `Type w`, making the smallness universe explicit.
These are assumptions carried by typeclasses, not new Lean `axiom` declarations.
-/

public section

universe w v u

open CategoryTheory Limits

namespace ABCCofibrations

open HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- ABC axioms CF1–CF4, relative to the supplied initial object and morphism classes. -/
class ABCPrecofibrationCategory : Prop where
  /-- CF1: the initial object is cofibrant. -/
  initial_cofibrant : IsCofibrant (⊥_ C)
  /-- CF1: cofibrations compose, including those with noncofibrant source. -/
  cofibrations_comp : (cofibrations C).IsStableUnderComposition
  /-- CF1: every isomorphism is a weak equivalence. -/
  weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f
  /-- CF1: an isomorphism with cofibrant source is a cofibration. -/
  cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] [IsCofibrant A] :
    Cofibration f
  /-- CF2: weak equivalences satisfy two out of three. -/
  weakEquivalences_twoOutOfThree : (weakEquivalences C).HasTwoOutOfThreeProperty
  /-- CF3: the required pushouts exist. -/
  hasPushout {A B D : C} (i : A ⟶ B) (f : A ⟶ D)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] : HasPushout i f
  /-- CF3: cobase change preserves cofibrations for these pushouts. -/
  cofibration_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ E} {j : D ⟶ E} (h : IsPushout i f g j)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] : Cofibration j
  /-- CF3: cobase change also preserves trivial cofibrations. -/
  weakEquivalence_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ E} {j : D ⟶ E} (h : IsPushout i f g j)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence j
  /-- CF4: factor maps with cofibrant source; no functorial choice is assumed. -/
  factorization {A B : C} (f : A ⟶ B) [IsCofibrant A] :
    ∃ (Z : C) (i : A ⟶ Z) (p : Z ⟶ B),
      Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f

attribute [instance] ABCPrecofibrationCategory.initial_cofibrant
  ABCPrecofibrationCategory.cofibrations_comp
  ABCPrecofibrationCategory.weakEquivalences_twoOutOfThree
  ABCPrecofibrationCategory.hasPushout

namespace ABCPrecofibrationCategory

variable {C} [ABCPrecofibrationCategory C]

/-- CF1 and composition imply that a cofibration preserves cofibrancy. -/
theorem cofibrant_target {A B : C} (i : A ⟶ B) [IsCofibrant A] [Cofibration i] :
    IsCofibrant B :=
  isCofibrant_of_cofibration i

/-- Every object admits a weak equivalence from a cofibrant object, by CF4. -/
theorem exists_cofibrant_replacement (A : C) :
    ∃ (Q : C) (q : Q ⟶ A), IsCofibrant Q ∧ WeakEquivalence q := by
  obtain ⟨Q, i, q, hi, hq, _⟩ := factorization (initial.to A)
  let := hi
  exact ⟨Q, q, cofibrant_target i, hq⟩

/-- Cofibrancy does not depend on the chosen initial object: for any initial
`I`, an object is cofibrant exactly when `I → A` is a cofibration. The two
initial objects are compared by their unique isomorphism, using CF1. -/
theorem isCofibrant_iff_of_isInitial {I : C} (hI : IsInitial I) (A : C) :
    IsCofibrant A ↔ Cofibration (hI.to A) := by
  let e : ⊥_ C ≅ I := initialIsInitial.uniqueUpToIso hI
  have hI' : IsCofibrant I := by
    have : Cofibration e.hom := cofibration_of_isIso e.hom
    change Cofibration (initial.to I)
    rwa [show initial.to I = e.hom from initialIsInitial.hom_ext _ _]
  have h₁ : initial.to A = e.hom ≫ hI.to A := initialIsInitial.hom_ext _ _
  have h₂ : hI.to A = e.inv ≫ initial.to A := hI.hom_ext _ _
  constructor
  · intro hA
    have : Cofibration e.inv := cofibration_of_isIso e.inv
    rw [h₂]
    infer_instance
  · intro hA
    have : Cofibration e.hom := cofibration_of_isIso e.hom
    change Cofibration (initial.to A)
    rw [h₁]
    infer_instance

/-- The empty coproduct is cofibrant by CF1 alone: it is an initial object. -/
theorem isCofibrant_coproduct_of_isEmpty {ι : Type w} [IsEmpty ι] (A : ι → C)
    [HasCoproduct A] : IsCofibrant (∐ A) := by
  let hI : IsInitial (∐ A) :=
    isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (Discrete.functor A))
      (colimit.isColimit _)
  let e : ⊥_ C ≅ ∐ A := initialIsInitial.uniqueUpToIso hI
  have : Cofibration e.hom := cofibration_of_isIso e.hom
  exact cofibrant_target e.hom

/-- In a sequence whose successive maps are cofibrations and whose first
object is cofibrant, every object is cofibrant. -/
theorem isCofibrant_obj_of_sequence (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    IsCofibrant (F.obj n) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    let := ih
    let := hf n
    exact cofibrant_target (F.map (homOfLE (Nat.le_succ n)))

/-- The hypothesis of CF6 on successive maps implies that every map
`A_m → A_n` of the sequence is a cofibration, as in the paper's
formulation with all `a_{mn}`. -/
theorem cofibration_map_of_le (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) {m n : ℕ} (h : m ≤ n) :
    Cofibration (F.map (homOfLE h)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
    let := isCofibrant_obj_of_sequence F h0 hf m
    rw [show homOfLE h = 𝟙 _ from Subsingleton.elim _ _, F.map_id]
    exact cofibration_of_isIso _
  | succ k ih =>
    let := ih (Nat.le_add_right m k)
    let := hf (m + k)
    rw [show homOfLE h = homOfLE (Nat.le_add_right m k) ≫ homOfLE (Nat.le_succ (m + k)) from
      Subsingleton.elim _ _, F.map_comp]
    infer_instance

/-- Likewise, trivial successive maps make every map of the sequence a weak
equivalence. -/
theorem weakEquivalence_map_of_le (F : ℕ ⥤ C)
    (hw : ∀ n, WeakEquivalence (F.map (homOfLE (Nat.le_succ n)))) {m n : ℕ} (h : m ≤ n) :
    WeakEquivalence (F.map (homOfLE h)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
    rw [show homOfLE h = 𝟙 _ from Subsingleton.elim _ _, F.map_id]
    exact weakEquivalence_of_isIso _
  | succ k ih =>
    let := ih (Nat.le_add_right m k)
    let := hw (m + k)
    rw [show homOfLE h = homOfLE (Nat.le_add_right m k) ≫ homOfLE (Nat.le_succ (m + k)) from
      Subsingleton.elim _ _, F.map_comp]
    infer_instance

end ABCPrecofibrationCategory

/-- ABC axioms CF1–CF6, with CF5 for families indexed by `Type w`. -/
class ABCCofibrationCategory : Prop extends ABCPrecofibrationCategory C where
  /-- CF5: existence for each small family (not all objects must be cofibrant). -/
  hasCoproductOfCofibrant {ι : Type w} (A : ι → C) (hA : ∀ i, IsCofibrant (A i)) :
    HasCoproduct A
  /-- CF5: such coproducts are cofibrant. -/
  coproduct_cofibrant {ι : Type w} (A : ι → C) (hA : ∀ i, IsCofibrant (A i))
    [HasCoproduct A] : IsCofibrant (∐ A)
  /-- CF5: coproducts of cofibrations with cofibrant sources are cofibrations. -/
  coproduct_cofibration {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i))
    [HasCoproduct A] [HasCoproduct B] : Cofibration (Limits.Sigma.map f)
  /-- CF5: the same coproduct map is trivial when every summand is trivial. -/
  coproduct_weakEquivalence {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i))
    (hw : ∀ i, WeakEquivalence (f i)) [HasCoproduct A] [HasCoproduct B] :
    WeakEquivalence (Limits.Sigma.map f)
  /-- CF6: sequential colimits of cofibrations starting cofibrantly exist. -/
  hasSequentialColimit (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) : HasColimit F
  /-- CF6: the transfinite composite from the first object is a cofibration. -/
  sequential_cofibration (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) [HasColimit F] :
    Cofibration (colimit.ι F 0)
  /-- CF6: this composite is trivial when all successive maps are trivial. -/
  sequential_weakEquivalence (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (hw : ∀ n, WeakEquivalence (F.map (homOfLE (Nat.le_succ n)))) [HasColimit F] :
    WeakEquivalence (colimit.ι F 0)

namespace ABCCofibrationCategory

variable {C}

section

variable [ABCCofibrationCategory.{w} C]

/-- CF1 and CF5 provide coproducts of both ends of a family of cofibrations. -/
theorem hasCoproduct_target {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i)) : HasCoproduct B := by
  apply hasCoproductOfCofibrant
  intro i
  let := hA i
  let := hf i
  exact ABCPrecofibrationCategory.cofibrant_target (f i)

/-- The sequential colimit is itself cofibrant, using CF6 and CF1. -/
theorem sequential_colimit_cofibrant (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) [HasColimit F] :
    IsCofibrant (colimit F) := by
  let := h0
  let := sequential_cofibration F h0 hf
  exact ABCPrecofibrationCategory.cofibrant_target (colimit.ι F 0)

end

/-- CF5 in the paper asserts existence of `∐ A_i` and `∐ B_i` for families
of cofibrations `A_i → B_i` with cofibrant sources. Using identity maps, this
is equivalent to the existence field used here, for families of cofibrant
objects. -/
theorem cf5_existence_iff [ABCPrecofibrationCategory C] :
    (∀ {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i), (∀ i, IsCofibrant (A i)) →
        (∀ i, Cofibration (f i)) → HasCoproduct A ∧ HasCoproduct B) ↔
      (∀ {ι : Type w} (A : ι → C), (∀ i, IsCofibrant (A i)) → HasCoproduct A) := by
  constructor
  · intro h ι A hA
    exact (h (fun i ↦ 𝟙 (A i)) hA (fun i ↦ by
      let := hA i
      exact ABCPrecofibrationCategory.cofibration_of_isIso _)).1
  · intro h ι A B f hA hf
    refine ⟨h A hA, h B fun i ↦ ?_⟩
    let := hA i
    let := hf i
    exact ABCPrecofibrationCategory.cofibrant_target (f i)

variable [ABCCofibrationCategory.{w} C]

/-- CF5 for any colimit cofan, not only the chosen coproduct: its cocone
point is cofibrant. -/
theorem isCofibrant_of_isColimit {ι : Type w} (A : ι → C) (hA : ∀ i, IsCofibrant (A i))
    {c : Cofan A} (hc : IsColimit c) : IsCofibrant c.pt := by
  let := hasCoproductOfCofibrant A hA
  let := coproduct_cofibrant A hA
  let e : ∐ A ≅ c.pt := (colimit.isColimit _).coconePointUniqueUpToIso hc
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.hom
  exact ABCPrecofibrationCategory.cofibrant_target e.hom

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCCofibrationCategory.{w} C] in
/-- The comparison between arbitrary colimit cofans is the chosen coproduct
map up to the canonical isomorphisms. -/
private theorem eq_comp_sigmaMap {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasCoproduct A] [HasCoproduct B] {cA : Cofan A} {cB : Cofan B}
    (hcA : IsColimit cA) (hcB : IsColimit cB) (φ : cA.pt ⟶ cB.pt)
    (hφ : ∀ i, cA.inj i ≫ φ = f i ≫ cB.inj i) :
    φ = (hcA.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫ Limits.Sigma.map f ≫
      ((colimit.isColimit _).coconePointUniqueUpToIso hcB).hom := by
  refine Cofan.IsColimit.hom_ext hcA _ _ fun i ↦ ?_
  rw [hφ]
  have h₁ := hcA.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨i⟩
  have h₂ := (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hcB ⟨i⟩
  simp only [Cofan.inj] at h₁ h₂ ⊢
  rw [reassoc_of% h₁, ← h₂]
  simp [Limits.Sigma.map]

/-- CF5 for arbitrary colimit cofans: a map between them compatible with a
family of cofibrations with cofibrant sources is a cofibration. -/
theorem cofibration_of_isColimit {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i))
    {cA : Cofan A} {cB : Cofan B} (hcA : IsColimit cA) (hcB : IsColimit cB)
    (φ : cA.pt ⟶ cB.pt) (hφ : ∀ i, cA.inj i ≫ φ = f i ≫ cB.inj i) : Cofibration φ := by
  let := hasCoproductOfCofibrant A hA
  let := hasCoproduct_target f hA hf
  have hB : ∀ i, IsCofibrant (B i) := fun i ↦ by
    let := hA i
    let := hf i
    exact ABCPrecofibrationCategory.cofibrant_target (f i)
  let := isCofibrant_of_isColimit A hA hcA
  have : IsCofibrant (colimit.cocone (Discrete.functor B)).pt := coproduct_cofibrant B hB
  let := coproduct_cofibration f hA hf
  let := ABCPrecofibrationCategory.cofibration_of_isIso
    (hcA.coconePointUniqueUpToIso (colimit.isColimit _)).hom
  let := ABCPrecofibrationCategory.cofibration_of_isIso
    ((colimit.isColimit _).coconePointUniqueUpToIso hcB).hom
  rw [eq_comp_sigmaMap f hcA hcB φ hφ]
  infer_instance

/-- The trivial-cofibration part of CF5 for arbitrary colimit cofans. -/
theorem weakEquivalence_of_isColimit {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i))
    (hw : ∀ i, WeakEquivalence (f i))
    {cA : Cofan A} {cB : Cofan B} (hcA : IsColimit cA) (hcB : IsColimit cB)
    (φ : cA.pt ⟶ cB.pt) (hφ : ∀ i, cA.inj i ≫ φ = f i ≫ cB.inj i) : WeakEquivalence φ := by
  let := hasCoproductOfCofibrant A hA
  let := hasCoproduct_target f hA hf
  let := coproduct_weakEquivalence f hA hf hw
  let := ABCPrecofibrationCategory.weakEquivalence_of_isIso
    (hcA.coconePointUniqueUpToIso (colimit.isColimit _)).hom
  let := ABCPrecofibrationCategory.weakEquivalence_of_isIso
    ((colimit.isColimit _).coconePointUniqueUpToIso hcB).hom
  rw [eq_comp_sigmaMap f hcA hcB φ hφ]
  infer_instance

/-- CF6 for any colimit cocone of the sequence, not only the chosen colimit. -/
theorem sequential_cofibration_of_isColimit (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) {c : Cocone F}
    (hc : IsColimit c) : Cofibration (c.ι.app 0) := by
  let := hasSequentialColimit F h0 hf
  let := h0
  let := sequential_cofibration F h0 hf
  have : IsCofibrant (colimit.cocone F).pt := sequential_colimit_cofibrant F h0 hf
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hc
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.hom
  rw [← (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc 0]
  exact inferInstanceAs (Cofibration (colimit.ι F 0 ≫ e.hom))

/-- The trivial part of CF6 for any colimit cocone of the sequence. -/
theorem sequential_weakEquivalence_of_isColimit (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (hw : ∀ n, WeakEquivalence (F.map (homOfLE (Nat.le_succ n)))) {c : Cocone F}
    (hc : IsColimit c) : WeakEquivalence (c.ι.app 0) := by
  let := hasSequentialColimit F h0 hf
  let := sequential_weakEquivalence F h0 hf hw
  let e := (colimit.isColimit F).coconePointUniqueUpToIso hc
  let := ABCPrecofibrationCategory.weakEquivalence_of_isIso e.hom
  rw [← (colimit.isColimit F).comp_coconePointUniqueUpToIso_hom hc 0]
  exact inferInstanceAs (WeakEquivalence (colimit.ι F 0 ≫ e.hom))

end ABCCofibrationCategory

end ABCCofibrations

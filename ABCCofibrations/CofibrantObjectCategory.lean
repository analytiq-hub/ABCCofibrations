/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Cylinder
public import ABCCofibrations.CofibrantSubcategory
public import ABCCofibrations.FibrantSubcategory

/-!
# Brown's categories of cofibrant objects (§2.1)

Definition 2.1.1 (axioms CFObj1–CFObj4) and Proposition 2.1.2: a category of
cofibrant objects is a precofibration category, and the cofibrant objects of a
precofibration category form a category of cofibrant objects; dually for
fibrant objects.

The cylinder axiom CFObj4 asks for a good cylinder (mathlib's `Cylinder` with
`Cylinder.IsGood`) relative to any chosen binary coproduct; binary coproducts
always exist, as pushouts over the initial object. The only axiom of a
precofibration category which needs proof is CF4, obtained from Brown's
factorization through a cylinder.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

section

variable {C : Type u} [Category.{v} C]

/-- The square `A ⟶ A ⨿ X`, `B ⟶ B ⨿ X` along `f : A ⟶ B` is a pushout. -/
theorem isPushout_coprod_map_inl {A B : C} (f : A ⟶ B) (X : C)
    [HasBinaryCoproduct A X] [HasBinaryCoproduct B X] :
    IsPushout f coprod.inl coprod.inl (coprod.map f (𝟙 X)) :=
  IsPushout.of_isColimit' ⟨by simp⟩
    (PushoutCocone.IsColimit.mk _ (fun s ↦ coprod.desc s.inl (coprod.inr ≫ s.inr))
      (fun s ↦ by simp)
      (fun s ↦ by
        ext
        · simpa using s.condition
        · simp)
      (fun s m h₁ h₂ ↦ by
        ext
        · simpa using h₁
        · simpa using congrArg (fun t ↦ coprod.inr ≫ t) h₂))

end

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- **Definition 2.1.1.** A category of cofibrant objects (axioms CFObj1–CFObj4). -/
class CategoryOfCofibrantObjects : Prop where
  /-- CFObj1: all objects are cofibrant. -/
  isCofibrant (A : C) : IsCofibrant A
  /-- CFObj1: isomorphisms are cofibrations. -/
  cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : Cofibration f
  /-- CFObj1: isomorphisms are weak equivalences. -/
  weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f
  /-- CFObj1: cofibrations compose. -/
  cofibrations_comp : (cofibrations C).IsStableUnderComposition
  /-- CFObj2: two out of three. -/
  weakEquivalences_twoOutOfThree : (weakEquivalences C).HasTwoOutOfThreeProperty
  /-- CFObj3: pushouts along cofibrations exist. -/
  hasPushout {A B D : C} (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] : HasPushout i f
  /-- CFObj3: cobase change preserves cofibrations. -/
  cofibration_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout i f g j) [Cofibration i] : Cofibration j
  /-- CFObj3: cobase change preserves trivial cofibrations. -/
  weakEquivalence_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E}
    {j : D ⟶ E} (h : IsPushout i f g j) [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence j
  /-- CFObj4: the codiagonal factors as a cofibration followed by a weak
  equivalence. -/
  exists_good_cylinder (A : C) [HasBinaryCoproduct A A] : ∃ P : Cylinder A, P.IsGood

namespace CategoryOfCofibrantObjects

attribute [instance] isCofibrant cofibrations_comp weakEquivalences_twoOutOfThree

variable {C} [CategoryOfCofibrantObjects C]

/-- Binary coproducts exist: they are pushouts over the initial object. -/
theorem hasBinaryCoproduct (A B : C) : HasBinaryCoproduct A B := by
  have : Cofibration (initial.to A) := isCofibrant A
  have := hasPushout (initial.to A) (initial.to B)
  exact ⟨⟨_, isCoproductOfIsInitialIsPushout _ _ _ _ initialIsInitial
    (pushoutIsPushout (initial.to A) (initial.to B))⟩⟩

theorem cofibration_coprod_inl (A B : C) [HasBinaryCoproduct A B] :
    Cofibration (coprod.inl : A ⟶ A ⨿ B) := by
  have : Cofibration (initial.to B) := isCofibrant B
  exact cofibration_of_isPushout (IsPushout.of_hasBinaryCoproduct' A B).flip

theorem cofibration_coprod_inr (A B : C) [HasBinaryCoproduct A B] :
    Cofibration (coprod.inr : B ⟶ A ⨿ B) := by
  have : Cofibration (initial.to A) := isCofibrant A
  exact cofibration_of_isPushout (IsPushout.of_hasBinaryCoproduct' A B)

/-- Brown's factorization in a category of cofibrant objects: every map factors
as a cofibration followed by a retraction of a trivial cofibration. -/
theorem exists_brown_factorization {A B : C} (f : A ⟶ B) :
    ∃ (B' : C) (f' : A ⟶ B') (r : B' ⟶ B) (s : B ⟶ B'), Cofibration f' ∧
      WeakEquivalence r ∧ Cofibration s ∧ WeakEquivalence s ∧ f' ≫ r = f ∧ s ≫ r = 𝟙 B := by
  have := hasBinaryCoproduct A A
  have := hasBinaryCoproduct B A
  obtain ⟨P, hP⟩ := exists_good_cylinder A
  have := cofibration_coprod_inl A A
  have := cofibration_coprod_inr B A
  have : Cofibration P.i₀ := by
    rw [← P.inl_i]
    infer_instance
  have := weakEquivalence_of_isIso (𝟙 A)
  have : WeakEquivalence P.i₀ := weakEquivalence_of_postcomp_of_fac P.i₀_π
  have := hasPushout P.i₀ f
  let t := IsPushout.of_hasPushout P.i₀ f
  have hs : Cofibration (pushout.inr P.i₀ f) := cofibration_of_isPushout t
  have hsw : WeakEquivalence (pushout.inr P.i₀ f) := weakEquivalence_of_isPushout t
  let r : pushout P.i₀ f ⟶ B := pushout.desc (P.π ≫ f) (𝟙 B) (by simp)
  have hsr : pushout.inr P.i₀ f ≫ r = 𝟙 B := pushout.inr_desc _ _ _
  have := weakEquivalence_of_isIso (𝟙 B)
  have hr : WeakEquivalence r := weakEquivalence_of_precomp_of_fac hsr
  let f' := P.i₁ ≫ pushout.inl P.i₀ f
  -- The map `B ⨿ A ⟶ B'` is a cobase change of `P.i`.
  have lower : IsPushout (coprod.map f (𝟙 A)) P.i (coprod.desc (pushout.inr P.i₀ f) f')
      (pushout.inl P.i₀ f) := by
    refine IsPushout.of_top ?_ ?_ (isPushout_coprod_map_inl f A)
    · simpa using t.flip
    · ext
      · simp [t.w]
      · simp [f']
  have : Cofibration (coprod.desc (pushout.inr P.i₀ f) f') := cofibration_of_isPushout lower.flip
  have hf' : Cofibration f' := by
    rw [show f' = coprod.inr ≫ coprod.desc (pushout.inr P.i₀ f) f' by simp]
    infer_instance
  exact ⟨_, f', r, _, hf', hr, hs, hsw, by simp [f', r], hsr⟩

/-- **Proposition 2.1.2(1)**, first part: a category of cofibrant objects is a
precofibration category. -/
theorem toPrecofibrationCategory : ABCPrecofibrationCategory C where
  initial_cofibrant := isCofibrant _
  cofibrations_comp := cofibrations_comp
  weakEquivalence_of_isIso := weakEquivalence_of_isIso
  cofibration_of_isIso f _ _ := cofibration_of_isIso f
  weakEquivalences_twoOutOfThree := weakEquivalences_twoOutOfThree
  hasPushout i f _ _ _ := hasPushout i f
  cofibration_of_isPushout h _ _ _ := cofibration_of_isPushout h
  weakEquivalence_of_isPushout h _ _ _ _ := weakEquivalence_of_isPushout h
  factorization f _ := by
    obtain ⟨B', f', r, -, hf', hr, -, -, hfac, -⟩ := exists_brown_factorization f
    exact ⟨B', f', r, hf', hr, hfac⟩

end CategoryOfCofibrantObjects

variable {C}

/-- A precofibration category in which all objects are cofibrant is a category
of cofibrant objects. -/
theorem CategoryOfCofibrantObjects.of_precofibration [ABCPrecofibrationCategory C]
    [∀ X : C, IsCofibrant X] : CategoryOfCofibrantObjects C where
  isCofibrant := inferInstance
  cofibration_of_isIso f _ := ABCPrecofibrationCategory.cofibration_of_isIso f
  weakEquivalence_of_isIso := ABCPrecofibrationCategory.weakEquivalence_of_isIso
  cofibrations_comp := inferInstance
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout i f _ := ABCPrecofibrationCategory.hasPushout i f
  cofibration_of_isPushout h _ := ABCPrecofibrationCategory.cofibration_of_isPushout h
  weakEquivalence_of_isPushout h _ _ := ABCPrecofibrationCategory.weakEquivalence_of_isPushout h
  exists_good_cylinder A _ := ABCPrecofibrationCategory.exists_good_cylinder A

/-- **Proposition 2.1.2(1)**, second part: the cofibrant objects of a
precofibration category form a category of cofibrant objects. -/
instance cofibrantObject_categoryOfCofibrantObjects [ABCPrecofibrationCategory C] :
    CategoryOfCofibrantObjects (CofibrantObject C) :=
  CategoryOfCofibrantObjects.of_precofibration

section Fibrant

variable (D : Type u) [Category.{v} D] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences D] [HasTerminal D]

/-- A category of fibrant objects (axioms FObj1–FObj4): a category of cofibrant
objects on the opposite category. -/
abbrev CategoryOfFibrantObjects : Prop := CategoryOfCofibrantObjects Dᵒᵖ

variable {D}

/-- **Proposition 2.1.2(2)**, first part: a category of fibrant objects is a
prefibration category. -/
theorem CategoryOfFibrantObjects.toPrefibrationCategory [CategoryOfFibrantObjects D] :
    ABCPrefibrationCategory D :=
  CategoryOfCofibrantObjects.toPrecofibrationCategory (C := Dᵒᵖ)

/-- **Proposition 2.1.2(2)**, second part: the fibrant objects of a
prefibration category form a category of fibrant objects. -/
instance fibrantObject_categoryOfFibrantObjects [ABCPrefibrationCategory D] :
    CategoryOfFibrantObjects (FibrantObject D) := by
  have : ∀ X : (FibrantObject D)ᵒᵖ, IsCofibrant X := fun X ↦
    (ABCPrefibrationCategory.isFibrant_iff_isCofibrant_op X.unop).1 inferInstance
  exact CategoryOfCofibrantObjects.of_precofibration

end Fibrant

end ABCCofibrations

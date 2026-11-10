/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantObjectCategory
public import ABCCofibrations.RightProperness

/-!
# Baues and Waldhausen cofibration categories (§2.3–§2.4)

Definition 2.3.1 (Baues cofibration categories) and Proposition 2.3.2: a
Baues cofibration category with an initial object is a left proper
precofibration category, and dually.

Definition 2.4.1 (Waldhausen cofibration categories) and Proposition 2.4.2:
the cofibrant objects of a pointed precofibration category form a Waldhausen
cofibration category; a Waldhausen cofibration category satisfying two out of
three and the cylinder axiom is a precofibration category; and dually.

Fibration versions are defined on the opposite category.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra ZeroObject

namespace ABCCofibrations

section Baues

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C]

/-- **Definition 2.3.1.** A Baues cofibration category (axioms BCF1–BCF4,
BCF6). No initial object is required. -/
class BauesCofibrationCategory : Prop where
  /-- BCF1: isomorphisms are cofibrations. -/
  cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : Cofibration f
  /-- BCF1: isomorphisms are weak equivalences. -/
  weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f
  /-- BCF1: cofibrations compose. -/
  cofibrations_comp : (cofibrations C).IsStableUnderComposition
  /-- BCF2: two out of three. -/
  weakEquivalences_twoOutOfThree : (weakEquivalences C).HasTwoOutOfThreeProperty
  /-- BCF3: pushouts along cofibrations exist. -/
  hasPushout {A B D : C} (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] : HasPushout i f
  /-- BCF3: cobase change preserves cofibrations. -/
  cofibration_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout i f g j) [Cofibration i] : Cofibration j
  /-- BCF3(a): cobase change preserves trivial cofibrations. -/
  weakEquivalence_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E}
    {j : D ⟶ E} (h : IsPushout i f g j) [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence j
  /-- BCF3(b): the cobase change of a weak equivalence along a cofibration is a
  weak equivalence. -/
  weakEquivalence_of_isPushout_of_cofibration {A B D E : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ E} {j : D ⟶ E} (h : IsPushout i f g j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence g
  /-- BCF4: every map factors as a cofibration followed by a weak equivalence. -/
  factorization {A B : C} (f : A ⟶ B) :
    ∃ (Z : C) (i : A ⟶ Z) (p : Z ⟶ B), Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f
  /-- BCF6: every object has a fibrant model, a trivial cofibration into an
  object on which every trivial cofibration has a retraction. -/
  exists_fibrant_model (A : C) : ∃ (B : C) (i : A ⟶ B), Cofibration i ∧ WeakEquivalence i ∧
    ∀ ⦃X : C⦄ (j : X ⟶ B), Cofibration j → WeakEquivalence j → ∃ r : B ⟶ X, j ≫ r = 𝟙 X

namespace BauesCofibrationCategory

variable {C} [BauesCofibrationCategory C] [HasInitial C]

/-- **Proposition 2.3.2(1)**, first part: a Baues cofibration category with an
initial object is a precofibration category. -/
theorem toPrecofibrationCategory : ABCPrecofibrationCategory C where
  initial_cofibrant := by
    change Cofibration (initial.to (⊥_ C))
    rw [show initial.to (⊥_ C) = 𝟙 _ from initialIsInitial.hom_ext _ _]
    exact cofibration_of_isIso _
  cofibrations_comp := cofibrations_comp
  weakEquivalence_of_isIso := weakEquivalence_of_isIso
  cofibration_of_isIso f _ _ := cofibration_of_isIso f
  weakEquivalences_twoOutOfThree := weakEquivalences_twoOutOfThree
  hasPushout i f _ _ _ := hasPushout i f
  cofibration_of_isPushout h _ _ _ := cofibration_of_isPushout h
  weakEquivalence_of_isPushout h _ _ _ _ := weakEquivalence_of_isPushout h
  factorization f _ := factorization f

/-- **Proposition 2.3.2(1)**: a Baues cofibration category with an initial
object is a left proper precofibration category. Axiom PCF is BCF3(b). -/
theorem leftProper :
    letI := toPrecofibrationCategory (C := C)
    ABCPrecofibrationCategory.LeftProper C :=
  letI := toPrecofibrationCategory (C := C)
  { hasPushout := fun i r _ _ ↦ hasPushout i r
    weakEquivalence_of_isPushout := fun h _ _ _ ↦ weakEquivalence_of_isPushout_of_cofibration h }

end BauesCofibrationCategory

variable (D : Type u) [Category.{v} D] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences D]

/-- A Baues fibration category: a Baues cofibration category on the opposite
category. -/
abbrev BauesFibrationCategory : Prop := BauesCofibrationCategory Dᵒᵖ

variable {D} [BauesFibrationCategory D] [HasTerminal D]

/-- **Proposition 2.3.2(2)**, first part: a Baues fibration category with a
terminal object is a prefibration category. -/
theorem BauesFibrationCategory.toPrefibrationCategory : ABCPrefibrationCategory D :=
  BauesCofibrationCategory.toPrecofibrationCategory (C := Dᵒᵖ)

/-- **Proposition 2.3.2(2)**: a Baues fibration category with a terminal object
is a right proper prefibration category. -/
theorem BauesFibrationCategory.rightProper :
    letI := BauesFibrationCategory.toPrefibrationCategory (D := D)
    ABCPrefibrationCategory.RightProper D :=
  BauesCofibrationCategory.leftProper (C := Dᵒᵖ)

end Baues

section Waldhausen

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasZeroObject C]

/-- **Definition 2.4.1.** A Waldhausen cofibration category (axioms
WCF1–WCF3). -/
class WaldhausenCofibrationCategory : Prop where
  /-- WCF1: all objects are cofibrant. -/
  isCofibrant (A : C) : IsCofibrant A
  /-- WCF1: isomorphisms are cofibrations. -/
  cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : Cofibration f
  /-- WCF1: isomorphisms are weak equivalences. -/
  weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f
  /-- WCF1: cofibrations compose. -/
  cofibrations_comp : (cofibrations C).IsStableUnderComposition
  /-- WCF2: pushouts along cofibrations exist. -/
  hasPushout {A B D : C} (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] : HasPushout i f
  /-- WCF2: cobase change preserves cofibrations. -/
  cofibration_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout i f g j) [Cofibration i] : Cofibration j
  /-- WCF3: the gluing axiom. -/
  gluing ⦃A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C⦄
    {f₁₂ : A₁ ⟶ A₂} {f₁₃ : A₁ ⟶ A₃} {f₂₄ : A₂ ⟶ A₄} {f₃₄ : A₃ ⟶ A₄}
    {g₁₂ : B₁ ⟶ B₂} {g₁₃ : B₁ ⟶ B₃} {g₂₄ : B₂ ⟶ B₄} {g₃₄ : B₃ ⟶ B₄}
    {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄}
    [Cofibration f₁₂] [Cofibration g₁₂]
    (hA : IsPushout f₁₂ f₁₃ f₂₄ f₃₄) (hB : IsPushout g₁₂ g₁₃ g₂₄ g₃₄)
    (h₁₂ : f₁₂ ≫ u₂ = u₁ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₃ = u₁ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₄ = u₂ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₄ = u₃ ≫ g₃₄)
    [WeakEquivalence u₁] [WeakEquivalence u₂] [WeakEquivalence u₃] : WeakEquivalence u₄

namespace WaldhausenCofibrationCategory

variable {C} [WaldhausenCofibrationCategory C]

/-- The gluing axiom gives cobase change of trivial cofibrations: glue the
identity square of `f` to the pushout square of `i` along `f`. -/
theorem weakEquivalence_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E}
    {j : D ⟶ E} (h : IsPushout i f g j) [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence j := by
  have := cofibration_of_isIso (𝟙 A)
  have := weakEquivalence_of_isIso (𝟙 A)
  have := weakEquivalence_of_isIso (𝟙 D)
  exact gluing (u₁ := 𝟙 A) (u₂ := i) (u₃ := 𝟙 D) (u₄ := j)
    (IsPushout.of_id_fst (f := f)) h (by simp) (by simp) h.w.symm (by simp)

/-- **Proposition 2.4.2(1)(b).** A Waldhausen cofibration category satisfying
two out of three and the cylinder axiom CFObj4 is a category of cofibrant
objects, hence (Proposition 2.1.2(1)) a precofibration category. -/
theorem toCategoryOfCofibrantObjects (h₂ : (weakEquivalences C).HasTwoOutOfThreeProperty)
    (hcyl : ∀ (A : C) [HasBinaryCoproduct A A], ∃ P : Cylinder A, P.IsGood) :
    CategoryOfCofibrantObjects C where
  isCofibrant := isCofibrant
  cofibration_of_isIso := cofibration_of_isIso
  weakEquivalence_of_isIso := weakEquivalence_of_isIso
  cofibrations_comp := cofibrations_comp
  weakEquivalences_twoOutOfThree := h₂
  hasPushout := hasPushout
  cofibration_of_isPushout := cofibration_of_isPushout
  weakEquivalence_of_isPushout := weakEquivalence_of_isPushout
  exists_good_cylinder := hcyl

/-- **Proposition 2.4.2(1)(b).** -/
theorem toPrecofibrationCategory (h₂ : (weakEquivalences C).HasTwoOutOfThreeProperty)
    (hcyl : ∀ (A : C) [HasBinaryCoproduct A A], ∃ P : Cylinder A, P.IsGood) :
    ABCPrecofibrationCategory C :=
  have := toCategoryOfCofibrantObjects h₂ hcyl
  CategoryOfCofibrantObjects.toPrecofibrationCategory

end WaldhausenCofibrationCategory

variable {C}

/-- A pointed precofibration category in which all objects are cofibrant is a
Waldhausen cofibration category; the gluing axiom is the gluing lemma. -/
theorem WaldhausenCofibrationCategory.of_precofibration [ABCPrecofibrationCategory C]
    [∀ X : C, IsCofibrant X] : WaldhausenCofibrationCategory C where
  isCofibrant := inferInstance
  cofibration_of_isIso f _ := ABCPrecofibrationCategory.cofibration_of_isIso f
  weakEquivalence_of_isIso := ABCPrecofibrationCategory.weakEquivalence_of_isIso
  cofibrations_comp := inferInstance
  hasPushout i f _ := ABCPrecofibrationCategory.hasPushout i f
  cofibration_of_isPushout h _ := ABCPrecofibrationCategory.cofibration_of_isPushout h
  gluing _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB h₁₂ h₁₃ h₂₄ h₃₄ _ _ _ :=
    ABCPrecofibrationCategory.gluing_weakEquivalence hA hB h₁₂ h₁₃ h₂₄ h₃₄

/-- The cofibrant objects of a pointed precofibration category have a zero
object. -/
theorem cofibrantObject_hasZeroObject [ABCPrecofibrationCategory C] :
    HasZeroObject (CofibrantObject C) := by
  have : IsCofibrant (0 : C) := by
    let e : ⊥_ C ≅ 0 := initialIsInitial.uniqueUpToIso (isZero_zero C).isInitial
    have := ABCPrecofibrationCategory.cofibration_of_isIso e.hom
    exact ABCPrecofibrationCategory.cofibrant_target e.hom
  exact ⟨⟨CofibrantObject.mk 0,
    IsZero.of_full_of_faithful_of_isZero CofibrantObject.ι _ (isZero_zero C)⟩⟩

/-- **Proposition 2.4.2(1)(a).** The cofibrant objects of a pointed
precofibration category form a Waldhausen cofibration category. -/
theorem cofibrantObject_waldhausen [ABCPrecofibrationCategory C] :
    letI := cofibrantObject_hasZeroObject (C := C)
    WaldhausenCofibrationCategory (CofibrantObject C) :=
  letI := cofibrantObject_hasZeroObject (C := C)
  WaldhausenCofibrationCategory.of_precofibration

section Fibration

variable (D : Type u) [Category.{v} D] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences D] [HasZeroObject D]

/-- A Waldhausen fibration category: a Waldhausen cofibration category on the
opposite category. -/
abbrev WaldhausenFibrationCategory : Prop := WaldhausenCofibrationCategory Dᵒᵖ

variable {D}

/-- **Proposition 2.4.2(2)(b).** A Waldhausen fibration category satisfying two
out of three and the path object axiom FObj4 (cylinders in the opposite
category) is a prefibration category. -/
theorem WaldhausenFibrationCategory.toPrefibrationCategory [WaldhausenFibrationCategory D]
    (h₂ : (weakEquivalences D).HasTwoOutOfThreeProperty)
    (hcyl : ∀ (A : Dᵒᵖ) [HasBinaryCoproduct A A], ∃ P : Cylinder A, P.IsGood) :
    ABCPrefibrationCategory D :=
  WaldhausenCofibrationCategory.toPrecofibrationCategory (C := Dᵒᵖ)
    (by rw [weakEquivalences_op]; infer_instance) hcyl

/-- **Proposition 2.4.2(2)(a).** The fibrant objects of a pointed prefibration
category form a Waldhausen fibration category. -/
theorem fibrantObject_waldhausen [ABCPrefibrationCategory D] [HasZeroObject (FibrantObject D)] :
    WaldhausenFibrationCategory (FibrantObject D) := by
  have : ∀ X : (FibrantObject D)ᵒᵖ, IsCofibrant X := fun X ↦
    (ABCPrefibrationCategory.isFibrant_iff_isCofibrant_op X.unop).1 inferInstance
  exact WaldhausenCofibrationCategory.of_precofibration

end Fibration

end Waldhausen

end ABCCofibrations

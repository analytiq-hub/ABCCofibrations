/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationCategory
public import ABCCofibrations.RightProperness
public import Mathlib.AlgebraicTopology.ModelCategory.Opposite
public import Mathlib.AlgebraicTopology.ModelCategory.Instances
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Quillen model categories (§2.2)

Mathlib's `ModelCategory` is a Quillen model category in the sense of
Definition 2.2.2, except that axiom M1 only asks for finite limits and
colimits. Proposition 2.2.3 (the lifting characterizations) is in mathlib; we
restate it. Proposition 2.2.4: a Quillen model category is a precofibration and
a prefibration category, and with small coproducts and sequential colimits
(resp. small products and inverse sequential limits) — which M1 provides in the
paper — a cofibration (resp. fibration) category. Proposition 2.2.5: a left
(right) proper Quillen model category is left (right) proper as a
precofibration (prefibration) category.

CF5 and CF6 follow because cofibrations and trivial cofibrations are defined by
a left lifting property, so they are stable under coproducts and under
transfinite composition.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace ABCCofibrations.QuillenModelCategory

variable (C : Type u) [Category.{v} C] [ModelCategory C]

/-- **Proposition 2.2.3.** In a Quillen model category, cofibrations, trivial
cofibrations, fibrations and trivial fibrations are characterized by lifting
properties. -/
theorem lifting_characterizations :
    cofibrations C = (trivialFibrations C).llp ∧ trivialCofibrations C = (fibrations C).llp ∧
      fibrations C = (trivialCofibrations C).rlp ∧
        trivialFibrations C = (cofibrations C).rlp := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [trivialFibrations_llp, fibrations_llp, trivialCofibrations_rlp, cofibrations_rlp]

variable {C}

theorem trivialCofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] :
    trivialCofibrations C f := by
  rw [← fibrations_llp]
  intro _ _ p _
  infer_instance

theorem weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f :=
  ⟨(trivialCofibration_of_isIso f).2⟩

theorem cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : Cofibration f :=
  ⟨(trivialCofibration_of_isIso f).1⟩

variable (C)

/-- **Proposition 2.2.4**, CF1–CF4: a Quillen model category is a
precofibration category. -/
theorem precofibrationCategory : ABCPrecofibrationCategory C where
  initial_cofibrant := by
    change Cofibration (initial.to (⊥_ C))
    rw [show initial.to (⊥_ C) = 𝟙 _ from initialIsInitial.hom_ext _ _]
    exact cofibration_of_isIso _
  cofibrations_comp := inferInstance
  weakEquivalence_of_isIso := weakEquivalence_of_isIso
  cofibration_of_isIso f _ _ := cofibration_of_isIso f
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout _ _ _ _ _ := inferInstance
  cofibration_of_isPushout h _ _ hi := ⟨(cofibrations C).of_isPushout h.flip hi.mem⟩
  weakEquivalence_of_isPushout h _ _ hi hw :=
    ⟨((trivialCofibrations C).of_isPushout h.flip ⟨hi.mem, hw.mem⟩).2⟩
  factorization f _ := by
    let h := factorizationData (cofibrations C) (trivialFibrations C) f
    exact ⟨h.Z, h.i, h.p, ⟨h.hi⟩, ⟨h.hp.2⟩, h.fac⟩

/-- **Proposition 2.2.4**, F1–F4: a Quillen model category is a prefibration
category. -/
theorem prefibrationCategory : ABCPrefibrationCategory C :=
  precofibrationCategory Cᵒᵖ

variable {C} in
/-- A sequential colimit is a transfinite composition of shape `ℕ`. -/
noncomputable def transfiniteCompositionOfShapeNat (W : MorphismProperty C) (F : ℕ ⥤ C)
    [HasColimit F] (hF : ∀ n, W (F.map (homOfLE (Nat.le_succ n)))) :
    W.TransfiniteCompositionOfShape ℕ (colimit.ι F 0) where
  F := F
  isoBot := Iso.refl _
  incl := (colimit.cocone F).ι
  isColimit := colimit.isColimit F
  fac := by simp
  map_mem j _ := hF j

/-- **Proposition 2.2.4**, CF1–CF6: a Quillen model category with small
coproducts and sequential colimits is a cofibration category. -/
theorem cofibrationCategory [HasCoproducts.{w} C] [HasColimitsOfShape ℕ C] :
    ABCCofibrationCategory.{w} C := by
  have := precofibrationCategory C
  have hcof : (cofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← trivialFibrations_llp]
    infer_instance
  have htriv : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← fibrations_llp]
    infer_instance
  exact
  { hasCoproductOfCofibrant := fun _ _ ↦ inferInstance
    coproduct_cofibrant := fun {ι} A hA _ ↦ by
      have hg : Cofibration (Limits.Sigma.map fun i ↦ initial.to (A i)) :=
        ⟨(cofibrations C).colimMap _ fun j ↦ (hA j.as).mem⟩
      have : IsIso (initial.to (∐ fun _ : ι ↦ ⊥_ C)) :=
        ⟨⟨Sigma.desc fun _ ↦ 𝟙 _, initialIsInitial.hom_ext _ _,
          Sigma.hom_ext _ _ fun _ ↦ initialIsInitial.hom_ext _ _⟩⟩
      have := cofibration_of_isIso (initial.to (∐ fun _ : ι ↦ ⊥_ C))
      change Cofibration (initial.to (∐ A))
      rw [show initial.to (∐ A) = initial.to (∐ fun _ : ι ↦ ⊥_ C) ≫
        Limits.Sigma.map (fun i ↦ initial.to (A i)) from initialIsInitial.hom_ext _ _]
      infer_instance
    coproduct_cofibration := fun f _ hf _ _ ↦
      ⟨(cofibrations C).colimMap _ fun j ↦ (hf j.as).mem⟩
    coproduct_weakEquivalence := fun f _ hf hw _ _ ↦
      ⟨((trivialCofibrations C).colimMap _ fun j ↦ ⟨(hf j.as).mem, (hw j.as).mem⟩).2⟩
    hasSequentialColimit := fun _ _ _ ↦ inferInstance
    sequential_cofibration := fun F _ hf _ ↦
      ⟨transfiniteCompositionsOfShape_le _ ℕ _
        ⟨transfiniteCompositionOfShapeNat _ F fun n ↦ (hf n).mem⟩⟩
    sequential_weakEquivalence := fun F _ hf hw _ ↦
      ⟨(transfiniteCompositionsOfShape_le _ ℕ _
        ⟨transfiniteCompositionOfShapeNat (trivialCofibrations C) F
          fun n ↦ ⟨(hf n).mem, (hw n).mem⟩⟩).2⟩ }

/-- **Proposition 2.2.4**, F1–F6: a Quillen model category with small products
and inverse sequential limits is a fibration category. -/
theorem fibrationCategory [HasProducts.{w} C] [HasLimitsOfShape ℕᵒᵖ C] :
    ABCFibrationCategory.{w} C :=
  cofibrationCategory Cᵒᵖ

/-- A Quillen model category is left proper if the pushout of a weak
equivalence along a cofibration is a weak equivalence. -/
def IsLeftProper : Prop :=
  ∀ ⦃A B D E : C⦄ {i : A ⟶ B} {r : A ⟶ D} {r' : B ⟶ E} {j : D ⟶ E},
    IsPushout i r r' j → Cofibration i → WeakEquivalence r → WeakEquivalence r'

/-- A Quillen model category is right proper if the pullback of a weak
equivalence along a fibration is a weak equivalence. -/
def IsRightProper : Prop :=
  ∀ ⦃A B D E : C⦄ {p : B ⟶ A} {r : D ⟶ A} {r' : E ⟶ B} {j : E ⟶ D},
    IsPullback r' j p r → Fibration p → WeakEquivalence r → WeakEquivalence r'

/-- **Proposition 2.2.5**, cofibration part: a left proper Quillen model
category is a left proper precofibration category. -/
theorem leftProper (h : IsLeftProper C) :
    letI := precofibrationCategory C
    ABCPrecofibrationCategory.LeftProper C :=
  letI := precofibrationCategory C
  { hasPushout := fun _ _ _ _ ↦ inferInstance
    weakEquivalence_of_isPushout := fun hsq _ hi hr ↦ h hsq hi hr }

/-- **Proposition 2.2.5**, fibration part: a right proper Quillen model
category is a right proper prefibration category. -/
theorem rightProper (h : IsRightProper C) :
    letI := prefibrationCategory C
    ABCPrefibrationCategory.RightProper C :=
  letI := prefibrationCategory C
  ABCPrefibrationCategory.RightProper.mk (fun _ _ _ _ ↦ inferInstance)
    fun hsq _ hp hr ↦ h hsq hp hr

end ABCCofibrations.QuillenModelCategory

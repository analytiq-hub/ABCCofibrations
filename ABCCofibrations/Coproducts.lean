/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Binary coproducts of cofibrant objects

The binary case of Lemma 1.2.1(1) of Rădulescu-Banu,
*Cofibrations in Homotopy Theory*. Only CF1–CF4 are assumed.
The pushout arguments retain the cofibrancy hypotheses of CF3.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The pushout over the initial object gives a coproduct of cofibrant objects. -/
theorem hasBinaryCoproduct (A B : C) [IsCofibrant A] [IsCofibrant B] :
    HasBinaryCoproduct A B := by
  let c := BinaryCofan.mk (pushout.inl (initial.to A) (initial.to B))
    (pushout.inr (initial.to A) (initial.to B))
  exact ⟨⟨c, isCoproductOfIsInitialIsPushout _ _ _ _ initialIsInitial
    (pushoutIsPushout _ _)⟩⟩

variable {A B : C} [IsCofibrant A] [IsCofibrant B] [HasBinaryCoproduct A B]

/-- The left coproduct inclusion is a cofibration, by the restricted pushout axiom. -/
theorem cofibration_coprod_inl : Cofibration (coprod.inl : A ⟶ A ⨿ B) :=
  cofibration_of_isPushout (IsPushout.of_hasBinaryCoproduct' A B).flip

/-- The right coproduct inclusion is a cofibration. -/
theorem cofibration_coprod_inr : Cofibration (coprod.inr : B ⟶ A ⨿ B) :=
  cofibration_of_isPushout (IsPushout.of_hasBinaryCoproduct' A B)

/-- A binary coproduct of cofibrant objects is cofibrant. -/
theorem coprod_cofibrant : IsCofibrant (A ⨿ B) := by
  let := cofibration_coprod_inl (A := A) (B := B)
  exact cofibrant_target (coprod.inl : A ⟶ A ⨿ B)

omit [IsCofibrant B] [HasBinaryCoproduct A B] in
/-- Adding a fixed cofibrant summand preserves cofibrations. -/
theorem cofibration_coprod_map_id (f : A ⟶ B) [Cofibration f]
    (X : C) [IsCofibrant X] [HasBinaryCoproduct A X] [HasBinaryCoproduct B X] :
    Cofibration (coprod.map f (𝟙 X)) := by
  let := coprod_cofibrant (A := A) (B := X)
  exact cofibration_of_isPushout (IsPushout.of_coprod_inl_with_id f X).flip

omit [IsCofibrant B] [HasBinaryCoproduct A B] in
/-- Adding a fixed cofibrant summand preserves trivial cofibrations. -/
theorem weakEquivalence_coprod_map_id (f : A ⟶ B) [Cofibration f]
    [WeakEquivalence f] (X : C) [IsCofibrant X]
    [HasBinaryCoproduct A X] [HasBinaryCoproduct B X] :
    WeakEquivalence (coprod.map f (𝟙 X)) := by
  let := coprod_cofibrant (A := A) (B := X)
  exact weakEquivalence_of_isPushout (IsPushout.of_coprod_inl_with_id f X).flip

end ABCCofibrations.ABCPrecofibrationCategory

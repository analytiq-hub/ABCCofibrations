/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# A sanity-check model of the ABC axioms

Types, with every map both a cofibration and a weak equivalence, satisfy CF1–CF6.
The morphism-class instances below are local to avoid imposing this structure
on `Type` elsewhere. This example also checks the coproduct universe parameter.
-/

public section

universe u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.Examples

local instance : CategoryWithCofibrations (Type u) where
  cofibrations := ⊤

local instance : CategoryWithWeakEquivalences (Type u) where
  weakEquivalences := ⊤

local instance {A B : Type u} (f : A ⟶ B) : Cofibration f := ⟨True.intro⟩
local instance {A B : Type u} (f : A ⟶ B) : WeakEquivalence f := ⟨True.intro⟩

/-- A concrete model: types with both distinguished morphism classes maximal. -/
example : ABCCofibrationCategory.{u} (Type u) where
  initial_cofibrant := inferInstance
  cofibrations_comp := { comp_mem := fun _ _ _ _ ↦ True.intro }
  weakEquivalence_of_isIso _ := inferInstance
  cofibration_of_isIso _ := inferInstance
  weakEquivalences_twoOutOfThree :=
    { comp_mem := fun _ _ _ _ ↦ True.intro
      of_postcomp := fun _ _ _ _ ↦ True.intro
      of_precomp := fun _ _ _ _ ↦ True.intro }
  hasPushout _ _ := inferInstance
  cofibration_of_isPushout _ := inferInstance
  weakEquivalence_of_isPushout _ := inferInstance
  factorization {_ B} f := ⟨B, f, 𝟙 B, inferInstance, inferInstance, Category.comp_id f⟩
  hasCoproductOfCofibrant _ _ := inferInstance
  coproduct_cofibrant _ _ := inferInstance
  coproduct_cofibration _ _ _ := inferInstance
  coproduct_weakEquivalence _ _ _ _ := inferInstance
  hasSequentialColimit _ _ _ := inferInstance
  sequential_cofibration _ _ _ := inferInstance
  sequential_weakEquivalence _ _ _ _ := inferInstance

end ABCCofibrations.Examples

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.QuillenModelCategory
public import ABCCofibrations.Saturation

/-!
# Quillen model categories have saturated weak equivalences (Theorem 7.2.4)

A (mathlib) model category with sequential colimits satisfies CF6, because
cofibrations and trivial cofibrations are defined by a left lifting property and
hence are stable under transfinite composition. Lemma 7.2.2 then shows that its
weak equivalences are saturated. (The paper's axiom M1 provides all colimits.)
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace ABCCofibrations.QuillenModelCategory

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasColimitsOfShape ℕ C]

/-- CF6(1) for a model category with sequential colimits. -/
theorem sequentialCofibrationAxiom :
    letI := precofibrationCategory C
    ABCPrecofibrationCategory.SequentialCofibrationAxiom C := by
  let := precofibrationCategory C
  have hcof : (cofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← trivialFibrations_llp]
    infer_instance
  exact ⟨fun _ _ _ ↦ inferInstance, fun F _ hf _ ↦
    ⟨transfiniteCompositionsOfShape_le _ ℕ _
      ⟨transfiniteCompositionOfShapeNat _ F fun n ↦ (hf n).mem⟩⟩⟩

omit [HasColimitsOfShape ℕ C] in
/-- CF6(2) for a model category with sequential colimits. -/
theorem trivialSequentialAxiom :
    letI := precofibrationCategory C
    ABCPrecofibrationCategory.TrivialSequentialAxiom C := by
  let := precofibrationCategory C
  have htriv : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← fibrations_llp]
    infer_instance
  intro F _ hf hw _
  exact ⟨(transfiniteCompositionsOfShape_le _ ℕ _
    ⟨transfiniteCompositionOfShapeNat (trivialCofibrations C) F
      fun n ↦ ⟨(hf n).mem, (hw n).mem⟩⟩).2⟩

/-- **Theorem 7.2.4.** A model category with sequential colimits has saturated
weak equivalences: a map is a weak equivalence iff it becomes an isomorphism in
the homotopy category. -/
theorem weakEquivalence_iff_isIso_map {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) := by
  let := precofibrationCategory C
  exact ABCPrecofibrationCategory.weakEquivalence_iff_isIso_map L sequentialCofibrationAxiom
    trivialSequentialAxiom f

end ABCCofibrations.QuillenModelCategory

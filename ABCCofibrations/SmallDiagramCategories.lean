/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SmallDiagramPrecategory

/-!
# Small diagram structures and native duals

Theorem 9.2.4(1)(b),(2)(b), CF1–CF6 and F1–F6, for arbitrary small
indexing categories. The inverse structures are transported by duality.
This module supplies the Reedy F1–F4 structure; the full Reedy structures
are completed in `ReedyCofibrationCategory` and `SmallReedyFibrationCategory`.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

namespace PointwiseDiagram
variable (D : Type w) [SmallCategory D] [IsDirect D]
  (M : Type u) [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]

/-- Theorem 9.2.4(1)(b), CF1–CF6, without finiteness restrictions. -/
instance (priority := 100) cofibrationCategory_small :
    ABCCofibrationCategory.{w} (PointwiseDiagram D M) :=
  cofibrationCategory_of_precofibrationCategory
end PointwiseDiagram

namespace ReedyFibDiagram
variable (D : Type w) [SmallCategory D] [IsInverse D]
  (M : Type u) [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCFibrationCategory.{w} M]

/-- The F1–F4 part of Theorem 9.2.4(2)(a) for arbitrary small inverse diagrams. -/
theorem prefibrationCategory_small : ABCPrefibrationCategory (ReedyFibDiagram D M) := by
  refine ABCPrecofibrationCategory.of_equivalence (D' := ReedyDiagram Dᵒᵖ Mᵒᵖ)
    (show (ReedyFibDiagram D M)ᵒᵖ ≌ ReedyDiagram Dᵒᵖ Mᵒᵖ from Functor.opUnopEquiv D M) ?_ ?_
  · ext X Y f
    change (∃ _ _, _) ↔ ∃ _ _, _
    exact ⟨fun ⟨a, b, h⟩ ↦ ⟨b, a, h⟩, fun ⟨a, b, h⟩ ↦ ⟨b, a, h⟩⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (Opposite.op e))⟩
end ReedyFibDiagram

namespace PointwiseFibDiagram
variable (D : Type w) [SmallCategory D] [IsInverse D]
  (M : Type u) [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCFibrationCategory.{w} M]

/-- Theorem 9.2.4(2)(b), F1–F6, for arbitrary small inverse diagrams, by duality. -/
theorem fibrationCategory_small : ABCFibrationCategory.{w} (PointwiseFibDiagram D M) := by
  refine ABCCofibrationCategory.of_equivalence (D' := PointwiseDiagram Dᵒᵖ Mᵒᵖ)
    (show (PointwiseFibDiagram D M)ᵒᵖ ≌ PointwiseDiagram Dᵒᵖ Mᵒᵖ from
      Functor.opUnopEquiv D M) ?_ ?_
  · ext X Y f
    change (∀ e, Fibration _) ↔ ∀ e, Cofibration _
    exact ⟨fun h e ↦ (cofibration_op_iff _).2 (h e.unop),
      fun h e ↦ (cofibration_op_iff _).1 (h (Opposite.op e))⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (Opposite.op e))⟩
end PointwiseFibDiagram
end ABCCofibrations

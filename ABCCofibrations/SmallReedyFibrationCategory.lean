/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyCofibrationCategory

/-! # Full inverse Reedy diagram structures by duality -/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

namespace ReedyFibDiagram
variable (D : Type w) [SmallCategory D] [IsInverse D]
  (M : Type u) [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCFibrationCategory.{w} M]

/-- Theorem 9.2.4(2)(a), F1–F6, for small inverse diagrams, by duality. -/
theorem fibrationCategory_small : ABCFibrationCategory.{w} (ReedyFibDiagram D M) := by
  refine ABCCofibrationCategory.of_equivalence (D' := ReedyDiagram Dᵒᵖ Mᵒᵖ)
    (show (ReedyFibDiagram D M)ᵒᵖ ≌ ReedyDiagram Dᵒᵖ Mᵒᵖ from Functor.opUnopEquiv D M) ?_ ?_
  · ext X Y f
    change (∃ _ _, _) ↔ ∃ _ _, _
    exact ⟨fun ⟨a, b, h⟩ ↦ ⟨b, a, h⟩, fun ⟨a, b, h⟩ ↦ ⟨b, a, h⟩⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (Opposite.op e))⟩
end ReedyFibDiagram
end ABCCofibrations

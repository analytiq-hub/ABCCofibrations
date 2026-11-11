/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyFactorization
public import ABCCofibrations.EquivalenceTransfer

/-!
# The Reedy fibration structure (Theorem 9.2.4(2)(a))

For a finite inverse category `D` and a prefibration category `M`, diagrams with
pointwise weak equivalences and Reedy fibrations form a prefibration category.
The structure is transported from the Reedy precofibration structure on
`Dᵒᵖ ⥤ Mᵒᵖ` along `(D ⥤ M)ᵒᵖ ≌ Dᵒᵖ ⥤ Mᵒᵖ`.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

/-- The category of `D`-diagrams in `M`, to carry the Reedy fibration structure. -/
def ReedyFibDiagram (D : Type*) [Category D] (M : Type*) [Category M] : Type _ := D ⥤ M

namespace ReedyFibDiagram

variable (D : Type w) [SmallCategory D] (M : Type u₂) [Category.{v₂} M]
  [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]

instance : Category (ReedyFibDiagram D M) := inferInstanceAs (Category (D ⥤ M))

instance : HasTerminal (ReedyFibDiagram D M) := inferInstanceAs (HasTerminal (D ⥤ M))

instance : CategoryWithWeakEquivalences (ReedyFibDiagram D M) where
  weakEquivalences := fun _ _ f ↦ ∀ e, WeakEquivalence (NatTrans.app f e)

instance : CategoryWithFibrations (ReedyFibDiagram D M) where
  fibrations := fun X Y f ↦ ∃ (_ : ∀ e, HasColimit (latchingDiagram (Functor.op (C := D) (D := M) X) e))
    (_ : ∀ e, HasColimit (latchingDiagram (Functor.op (C := D) (D := M) Y) e)), IsReedyFibration f

variable [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsInverse D] [ABCPrefibrationCategory M]

/-- **Theorem 9.2.4(2)(a)** (axioms F1–F4), for finite inverse categories: the
diagrams over `D` in a prefibration category, with pointwise weak equivalences
and Reedy fibrations, form a prefibration category. -/
theorem prefibrationCategory : ABCPrefibrationCategory (ReedyFibDiagram D M) := by
  refine ABCPrecofibrationCategory.of_equivalence (D' := ReedyDiagram Dᵒᵖ Mᵒᵖ)
    (show (ReedyFibDiagram D M)ᵒᵖ ≌ ReedyDiagram Dᵒᵖ Mᵒᵖ from Functor.opUnopEquiv D M) ?_ ?_
  · ext X Y f
    change (∃ _ _, _) ↔ ∃ _ _, _
    exact ⟨fun ⟨a, b, h⟩ ↦ ⟨b, a, h⟩, fun ⟨a, b, h⟩ ↦ ⟨b, a, h⟩⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (op e))⟩

end ReedyFibDiagram

end ABCCofibrations

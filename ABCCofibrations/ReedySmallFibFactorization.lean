/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallFactorization
public import ABCCofibrations.ReedyDegreeLimits

/-! # Reedy factorizations over arbitrary small inverse categories by duality -/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

/-- The F4 factorization for every small inverse category, by duality.
Only F5(1) is needed beyond the prefibration axioms. -/
theorem reedy_fibration_factorization_small
    {D : Type w} [SmallCategory D] [IsInverse D]
    {M : Type u} [Category.{v} M] [CategoryWithFibrations M]
    [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCPrefibrationCategory M]
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram Y.op d)]
    (hY : IsReedyFibrant Y) (f : X ⟶ Y) :
    ∃ (Z : D ⥤ M) (_ : ∀ d, HasColimit (latchingDiagram Z.op d))
      (i : X ⟶ Z) (p : Z ⟶ Y),
      (∀ d, WeakEquivalence (i.app d)) ∧ IsReedyFibration p ∧ i ≫ p = f := by
  obtain ⟨Z, hLZ, a, r, ha, hr, har⟩ := reedy_factorization_small h5 hY (NatTrans.op f)
  refine ⟨Z.unop, hLZ, NatTrans.unop r, NatTrans.unop a, ?_, ha, ?_⟩
  · intro d
    exact (weakEquivalences_op_iff _).1 (hr (Opposite.op d))
  · exact congrArg NatTrans.unop har

end ABCCofibrations

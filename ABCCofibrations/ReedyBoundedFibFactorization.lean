/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBoundedFactorization
public import ABCCofibrations.ReedyDegreeLimits

/-! # Bounded inverse Reedy factorizations by duality -/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

/-- The F4 factorization for a bounded inverse category. It is the opposite
of the bounded direct construction, and needs F5(1) but not F6. -/
theorem reedy_fibration_factorization_bounded
    {D : Type w} [SmallCategory D] (deg : D → ℕ)
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg b < deg a ∨ ∃ h : a = b, f = eqToHom h)
    (N : ℕ) (hbound : ∀ d, deg d < N)
    {M : Type u} [Category.{v} M] [CategoryWithFibrations M]
    [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCPrefibrationCategory M]
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram Y.op d)]
    (hY : IsReedyFibrant Y) (f : X ⟶ Y) :
    ∃ (Z : D ⥤ M) (_ : ∀ d, HasColimit (latchingDiagram Z.op d))
      (i : X ⟶ Z) (p : Z ⟶ Y),
      (∀ d, WeakEquivalence (i.app d)) ∧ IsReedyFibration p ∧ i ≫ p = f := by
  obtain ⟨Z, hLZ, a, r, ha, hr, har⟩ := reedy_factorization_bounded h5 N Dᵒᵖ
    (oppositeDegree deg) (inverseDegree_op deg hdeg) (fun d ↦ hbound d.unop)
    Y.op X.op hY (NatTrans.op f)
  refine ⟨Z.unop, hLZ, NatTrans.unop r, NatTrans.unop a, ?_, ha, ?_⟩
  · intro d
    exact (weakEquivalences_op_iff _).1 (hr (Opposite.op d))
  · exact congrArg NatTrans.unop har

end ABCCofibrations

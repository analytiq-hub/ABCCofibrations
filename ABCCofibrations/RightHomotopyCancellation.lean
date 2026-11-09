/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyOpposite

/-!
# Cancellation up to right homotopy

The right-homotopy side of Theorem 6.4.3(2)(b), transported from opposite
left homotopy. Equality after an ambient weak equivalence is also covered.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {A B : C} [IsFibrant A] [IsFibrant B] [HasBinaryProduct B B]

namespace RightHomotopyRel

/-- A weak equivalence before the source can be cancelled from a right
homotopy. Its domain need not be fibrant. -/
theorem of_precomp_weakEquivalence {f g : A ⟶ B}
    {D : C} (a : D ⟶ A) [WeakEquivalence a]
    (h : RightHomotopyRel (a ≫ f) (a ≫ g)) : RightHomotopyRel f g := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  apply (rightHomotopy_iff_op f g).2
  apply ABCPrecofibrationCategory.LeftHomotopyRel.of_postcomp_weakEquivalence a.op
  simpa only [op_comp] using (rightHomotopy_iff_op _ _).1 h

/-- Equality after precomposition by an ambient weak equivalence implies
right homotopy, even if its domain is not fibrant. -/
theorem of_precomp_weakEquivalence_eq {f g : A ⟶ B}
    {D : C} (a : D ⟶ A) [WeakEquivalence a]
    (h : a ≫ f = a ≫ g) : RightHomotopyRel f g := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  apply (rightHomotopy_iff_op f g).2
  apply ABCPrecofibrationCategory.LeftHomotopyRel.of_postcomp_weakEquivalence_eq a.op
  simpa only [op_comp] using congrArg Quiver.Hom.op h

/-- A weak equivalence after the target can be cancelled from right
homotopy when the targets are fibrant. -/
theorem of_postcomp_weakEquivalence {f g : A ⟶ B}
    {D : C} [IsFibrant D] [HasBinaryProduct D D]
    (b : B ⟶ D) [WeakEquivalence b]
    (h : RightHomotopyRel (f ≫ b) (g ≫ b)) : RightHomotopyRel f g := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op D) (Opposite.op D)
  apply (rightHomotopy_iff_op f g).2
  apply ABCPrecofibrationCategory.LeftHomotopyRel.of_precomp_weakEquivalence b.op
  simpa only [op_comp] using (rightHomotopy_iff_op _ _).1 h

/-- Precomposition by a weak equivalence between fibrant objects reflects
and preserves right homotopy. -/
theorem precomp_weakEquivalence_iff {f g : A ⟶ B}
    {D : C} [IsFibrant D] (a : D ⟶ A) [WeakEquivalence a] :
    RightHomotopyRel (a ≫ f) (a ≫ g) ↔ RightHomotopyRel f g :=
  ⟨of_precomp_weakEquivalence a, fun h ↦ h.precomp a⟩

/-- Postcomposition by a weak equivalence between fibrant objects reflects
and preserves right homotopy. -/
theorem postcomp_weakEquivalence_iff {f g : A ⟶ B}
    {D : C} [IsFibrant D] [HasBinaryProduct D D]
    (b : B ⟶ D) [WeakEquivalence b] :
    RightHomotopyRel (f ≫ b) (g ≫ b) ↔ RightHomotopyRel f g :=
  ⟨of_postcomp_weakEquivalence b, fun h ↦ h.postcomp b⟩

end RightHomotopyRel
end ABCCofibrations.ABCPrefibrationCategory

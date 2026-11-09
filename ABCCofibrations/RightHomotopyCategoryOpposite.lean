/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.RightHomotopyWeakEquivalences

/-!
# The right-homotopy quotient and the opposite left-homotopy quotient

The equivalence is built on native mathlib fibrant objects and quotient
categories, using the already proved comparison of homotopy relations.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- Opposite arrows give a functor from fibrant objects to opposite
left-homotopy classes of cofibrant opposite objects. -/
def fibrantToOppositeLeftHomotopyCategory :
    FibrantObject C ⥤ (ABCPrecofibrationCategory.LeftHomotopyCategory Cᵒᵖ)ᵒᵖ where
  obj X := Opposite.op (ABCPrecofibrationCategory.toLeftHomotopyCategory.obj
    (CofibrantObject.mk (Opposite.op X.obj)))
  map f := (ABCPrecofibrationCategory.toLeftHomotopyCategory.map
    (CofibrantObject.homMk f.hom.op)).op

/-- The functor descends to the native right-homotopy quotient. -/
noncomputable def rightHomotopyCategoryToOpposite :
    RightHomotopyCategory C ⥤ (ABCPrecofibrationCategory.LeftHomotopyCategory Cᵒᵖ)ᵒᵖ :=
  CategoryTheory.Quotient.lift _ fibrantToOppositeLeftHomotopyCategory (by
    intro X Y f g h
    apply congrArg Quiver.Hom.op
    apply ABCPrecofibrationCategory.toLeftHomotopyCategory_map_eq_iff _ _ |>.2
    let := hasBinaryProduct Y.obj Y.obj
    let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op Y.obj) (Opposite.op Y.obj)
    exact (rightHomotopy_iff_op f.hom g.hom).1 h)

instance rightHomotopyCategoryToOpposite_faithful :
    (rightHomotopyCategoryToOpposite (C := C)).Faithful where
  map_injective := by
    rintro ⟨X⟩ ⟨Y⟩ f g h
    obtain ⟨f, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective f
    obtain ⟨g, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective g
    apply (toRightHomotopyCategory_map_eq_iff f g).2
    let := hasBinaryProduct Y.obj Y.obj
    let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op Y.obj) (Opposite.op Y.obj)
    apply (rightHomotopy_iff_op f.hom g.hom).2
    apply (ABCPrecofibrationCategory.toLeftHomotopyCategory_map_eq_iff
      (CofibrantObject.homMk f.hom.op) (CofibrantObject.homMk g.hom.op)).1
    exact Quiver.Hom.op_inj h

instance rightHomotopyCategoryToOpposite_full :
    (rightHomotopyCategoryToOpposite (C := C)).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨g, hg⟩ := (ABCPrecofibrationCategory.toLeftHomotopyCategory (C := Cᵒᵖ)).map_surjective
      f.unop
    refine ⟨toRightHomotopyCategory.map (FibrantObject.homMk g.hom.unop), ?_⟩
    exact congrArg Quiver.Hom.op hg

instance rightHomotopyCategoryToOpposite_essSurj :
    (rightHomotopyCategoryToOpposite (C := C)).EssSurj where
  mem_essImage := by
    rintro ⟨⟨Y⟩⟩
    let : IsFibrant Y.obj.unop := (isFibrant_iff_isCofibrant_op Y.obj.unop).2 Y.property
    exact ⟨toRightHomotopyCategory.obj (FibrantObject.mk Y.obj.unop), ⟨Iso.refl _⟩⟩

instance rightHomotopyCategoryToOpposite_isEquivalence :
    (rightHomotopyCategoryToOpposite (C := C)).IsEquivalence where

/-- The comparison preserves and reflects the descended weak equivalences. -/
theorem weakEquivalence_rightHomotopyCategoryToOpposite_map_iff
    {X Y : RightHomotopyCategory C} (f : X ⟶ Y) :
    WeakEquivalence (rightHomotopyCategoryToOpposite.map f) ↔ WeakEquivalence f := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective f
  change WeakEquivalence ((ABCPrecofibrationCategory.toLeftHomotopyCategory.map
    (CofibrantObject.homMk f.hom.op)).op) ↔ WeakEquivalence (toRightHomotopyCategory.map f)
  rw [weakEquivalences_op_iff,
    ABCPrecofibrationCategory.weakEquivalence_toLeftHomotopyCategory_map_iff,
    weakEquivalence_toRightHomotopyCategory_map_iff]
  exact weakEquivalences_op_iff f.hom

/-- The native right-homotopy quotient is equivalent to the opposite of the
left-homotopy quotient on the opposite category. -/
noncomputable def rightHomotopyCategoryOppositeEquivalence :
    RightHomotopyCategory C ≌ (ABCPrecofibrationCategory.LeftHomotopyCategory Cᵒᵖ)ᵒᵖ :=
  rightHomotopyCategoryToOpposite.asEquivalence

end ABCCofibrations.ABCPrefibrationCategory

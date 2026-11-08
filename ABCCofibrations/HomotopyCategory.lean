/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.LeftHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# Cofibrant objects modulo left homotopy

The category `πₗ Mcof` following Theorem 6.3.3 in Rădulescu-Banu,
*Cofibrations in Homotopy Theory*. We use mathlib's full subcategory
`CofibrantObject C` and its quotient-category construction.

The relation is a congruence, so quotient equality is exactly left homotopy.
Weak equivalences descend to this quotient and can be checked on any
representative. Identification with the localization is a subsequent result;
no such identification is assumed here.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- Left homotopy on the full subcategory of cofibrant objects. Endpoint
coproducts are supplied locally, so no global coproduct assumption is needed. -/
noncomputable def cofibrantLeftHomotopyRel : HomRel (CofibrantObject C) := by
  intro X Y f g
  let := hasBinaryCoproduct X.obj X.obj
  exact LeftHomotopyRel f.hom g.hom

instance : Congruence (cofibrantLeftHomotopyRel (C := C)) where
  equivalence := by
    intro X Y
    let := hasBinaryCoproduct X.obj X.obj
    exact LeftHomotopyRel.equivalence.comap (fun (f : X ⟶ Y) ↦ f.hom)
  comp_left := by
    intro X Y Z f g g' h
    let := hasBinaryCoproduct X.obj X.obj
    let := hasBinaryCoproduct Y.obj Y.obj
    exact LeftHomotopyRel.precomp h f.hom
  comp_right := by
    intro X Y Z f f' g h
    let := hasBinaryCoproduct X.obj X.obj
    exact LeftHomotopyRel.postcomp h g.hom

variable (C) in
/-- The category of cofibrant objects modulo left homotopy, denoted `πₗ Mcof`
in the paper. This definition does not assert the localization property. -/
abbrev LeftHomotopyCategory := CategoryTheory.Quotient (cofibrantLeftHomotopyRel (C := C))

/-- The quotient functor from cofibrant objects to left-homotopy classes. -/
def toLeftHomotopyCategory : CofibrantObject C ⥤ LeftHomotopyCategory C :=
  CategoryTheory.Quotient.functor _

instance : (toLeftHomotopyCategory (C := C)).Full := by
  dsimp [toLeftHomotopyCategory]
  infer_instance

/-- The quotient makes exactly the identifications given by left homotopy. -/
theorem toLeftHomotopyCategory_map_eq_iff {X Y : CofibrantObject C} (f g : X ⟶ Y) :
    (toLeftHomotopyCategory (C := C)).map f = toLeftHomotopyCategory.map g ↔
      cofibrantLeftHomotopyRel f g :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

instance : (weakEquivalences (CofibrantObject C)).HasQuotient
    (cofibrantLeftHomotopyRel (C := C)) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    let := hasBinaryCoproduct X.obj X.obj
    exact LeftHomotopyRel.weakEquivalence_iff h

instance : CategoryWithWeakEquivalences (LeftHomotopyCategory C) where
  weakEquivalences := (weakEquivalences (CofibrantObject C)).quotient
    (cofibrantLeftHomotopyRel (C := C))

/-- A homotopy class is a weak equivalence precisely when its representative is. -/
theorem weakEquivalence_toLeftHomotopyCategory_map_iff
    {X Y : CofibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence ((toLeftHomotopyCategory (C := C)).map f) ↔ WeakEquivalence f.hom := by
  rw [← weakEquivalence_iff_of_objectProperty]
  simp only [weakEquivalence_iff, toLeftHomotopyCategory]
  exact MorphismProperty.quotient_iff _ _ _

end ABCCofibrations.ABCPrecofibrationCategory

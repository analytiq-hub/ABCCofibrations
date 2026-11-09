/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyOpposite
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# Fibrant objects modulo right homotopy

The category `πᵣ Mfib` following Theorem 6.3.3 in Rădulescu-Banu,
*Cofibrations in Homotopy Theory*. We use mathlib's full subcategory
`FibrantObject C` and its quotient-category construction.

The relation is a congruence, so quotient equality is exactly right homotopy.
Weak equivalences descend to this quotient and can be checked on any
representative. Identification with the localization is a subsequent result;
no such identification is assumed here.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- Right homotopy on the full subcategory of fibrant objects. Endpoint
products are supplied locally, so no global product assumption is needed. -/
noncomputable def fibrantRightHomotopyRel : HomRel (FibrantObject C) := by
  intro X Y f g
  let := hasBinaryProduct Y.obj Y.obj
  exact RightHomotopyRel f.hom g.hom

instance : Congruence (fibrantRightHomotopyRel (C := C)) where
  equivalence := by
    intro X Y
    let := hasBinaryProduct Y.obj Y.obj
    exact RightHomotopyRel.equivalence.comap (fun (f : X ⟶ Y) ↦ f.hom)
  comp_left := by
    intro X Y Z f g g' h
    let := hasBinaryProduct Z.obj Z.obj
    exact RightHomotopyRel.precomp h f.hom
  comp_right := by
    intro X Y Z f f' g h
    let := hasBinaryProduct Y.obj Y.obj
    let := hasBinaryProduct Z.obj Z.obj
    exact RightHomotopyRel.postcomp h g.hom

variable (C) in
/-- The category of fibrant objects modulo right homotopy, denoted `πᵣ Mfib`
in the paper. This definition does not assert the localization property. -/
abbrev RightHomotopyCategory := CategoryTheory.Quotient (fibrantRightHomotopyRel (C := C))

/-- The quotient functor from fibrant objects to right-homotopy classes. -/
def toRightHomotopyCategory : FibrantObject C ⥤ RightHomotopyCategory C :=
  CategoryTheory.Quotient.functor _

instance : (toRightHomotopyCategory (C := C)).Full := by
  dsimp [toRightHomotopyCategory]
  infer_instance

/-- The quotient makes exactly the identifications given by right homotopy. -/
theorem toRightHomotopyCategory_map_eq_iff {X Y : FibrantObject C} (f g : X ⟶ Y) :
    (toRightHomotopyCategory (C := C)).map f = toRightHomotopyCategory.map g ↔
      fibrantRightHomotopyRel f g :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

instance : (weakEquivalences (FibrantObject C)).HasQuotient
    (fibrantRightHomotopyRel (C := C)) where
  iff X Y f g h := by
    simp only [← weakEquivalence_iff, weakEquivalence_iff_of_objectProperty]
    let := hasBinaryProduct Y.obj Y.obj
    exact RightHomotopyRel.weakEquivalence_iff h

instance : CategoryWithWeakEquivalences (RightHomotopyCategory C) where
  weakEquivalences := (weakEquivalences (FibrantObject C)).quotient
    (fibrantRightHomotopyRel (C := C))

/-- A homotopy class is a weak equivalence precisely when its representative is. -/
theorem weakEquivalence_toRightHomotopyCategory_map_iff
    {X Y : FibrantObject C} (f : X ⟶ Y) :
    WeakEquivalence ((toRightHomotopyCategory (C := C)).map f) ↔ WeakEquivalence f.hom := by
  rw [← weakEquivalence_iff_of_objectProperty]
  simp only [weakEquivalence_iff, toRightHomotopyCategory]
  exact MorphismProperty.quotient_iff _ _ _

end ABCCofibrations.ABCPrefibrationCategory

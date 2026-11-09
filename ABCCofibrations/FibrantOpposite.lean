/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationBasic
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# Opposite fibrant objects are cofibrant objects of the opposite

Taking opposites identifies mathlib's native full subcategory of fibrant
objects, reversed, with the full subcategory of cofibrant objects of `Cᵒᵖ`.
The underlying objects and arrows are literally `op` and `unop`; only the
fibrancy/cofibrancy proofs are transported, through
`isFibrant_iff_isCofibrant_op`, which accounts for the chosen terminal object
of `C` and the chosen initial object of `Cᵒᵖ`.

Mathlib's `ObjectProperty.opEquivalence` would give an equivalence with the
full subcategory of `(fibrantObjects C).op`, which is only propositionally
the property `cofibrantObjects Cᵒᵖ`. The direct construction below keeps
the object and arrow equations definitional.

The equivalence preserves and reflects weak equivalences, so a
cofibration-side theorem about functors inverting weak equivalences on
cofibrant objects applies to fibrant objects by precomposing with its
inverse. This module depends only on F1–F4 and lies below all localization
modules in the import graph.
-/

@[expose] public section

universe v u

open CategoryTheory Opposite HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [Limits.HasTerminal C] [ABCPrefibrationCategory C]

/-- The opposite of a fibrant object, regarded as a cofibrant object of `Cᵒᵖ`. -/
def fibrantObjectOpFunctor : (FibrantObject C)ᵒᵖ ⥤ CofibrantObject Cᵒᵖ where
  obj X := CofibrantObject.mk (op X.unop.obj)
  map f := CofibrantObject.homMk f.unop.hom.op

/-- A cofibrant object of `Cᵒᵖ`, regarded as the opposite of a fibrant object. -/
def cofibrantObjectUnopFunctor : CofibrantObject Cᵒᵖ ⥤ (FibrantObject C)ᵒᵖ where
  obj Y :=
    have : IsFibrant Y.obj.unop := (isFibrant_iff_isCofibrant_op Y.obj.unop).2 Y.property
    op (FibrantObject.mk Y.obj.unop)
  map {X Y} g :=
    have : IsFibrant X.obj.unop := (isFibrant_iff_isCofibrant_op X.obj.unop).2 X.property
    have : IsFibrant Y.obj.unop := (isFibrant_iff_isCofibrant_op Y.obj.unop).2 Y.property
    (FibrantObject.homMk g.hom.unop).op

/-- Reversed fibrant objects of `C` are the cofibrant objects of `Cᵒᵖ`.
Both unit and counit are identities on underlying objects. -/
def fibrantObjectOpEquivalence : (FibrantObject C)ᵒᵖ ≌ CofibrantObject Cᵒᵖ where
  functor := fibrantObjectOpFunctor
  inverse := cofibrantObjectUnopFunctor
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    apply Quiver.Hom.unop_inj
    ext
    simp [fibrantObjectOpFunctor, cofibrantObjectUnopFunctor])
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    ext
    simp [fibrantObjectOpFunctor, cofibrantObjectUnopFunctor])
  functor_unitIso_comp _ := by
    ext
    simp [fibrantObjectOpFunctor, cofibrantObjectUnopFunctor]

@[simp]
theorem fibrantObjectOpEquivalence_functor_obj_obj (X : (FibrantObject C)ᵒᵖ) :
    (fibrantObjectOpEquivalence.functor.obj X).obj = op X.unop.obj := rfl

@[simp]
theorem fibrantObjectOpEquivalence_functor_map_hom {X Y : (FibrantObject C)ᵒᵖ} (f : X ⟶ Y) :
    (fibrantObjectOpEquivalence.functor.map f).hom = f.unop.hom.op := rfl

@[simp]
theorem fibrantObjectOpEquivalence_inverse_obj_unop_obj (Y : CofibrantObject Cᵒᵖ) :
    (fibrantObjectOpEquivalence.inverse.obj Y).unop.obj = Y.obj.unop := rfl

@[simp]
theorem fibrantObjectOpEquivalence_inverse_map_unop_hom
    {X Y : CofibrantObject Cᵒᵖ} (g : X ⟶ Y) :
    (fibrantObjectOpEquivalence.inverse.map g).unop.hom = g.hom.unop := rfl

/-- The functor sends the reversal of a fibrant-object arrow to its
opposite arrow, as a map of cofibrant objects. -/
theorem fibrantObjectOpEquivalence_functor_map_op {X Y : FibrantObject C} (f : X ⟶ Y) :
    fibrantObjectOpEquivalence.functor.map f.op = CofibrantObject.homMk f.hom.op := rfl

/-- The inverse followed by `unop` recovers the underlying opposite arrow. -/
theorem fibrantObjectOpEquivalence_inverse_map_homMk {X Y : FibrantObject C} (f : X ⟶ Y) :
    fibrantObjectOpEquivalence.inverse.map (fibrantObjectOpEquivalence.functor.map f.op) =
      f.op := rfl

/-- The equivalence preserves and reflects weak equivalences. -/
theorem weakEquivalence_fibrantObjectOpEquivalence_functor_map_iff
    {X Y : (FibrantObject C)ᵒᵖ} (f : X ⟶ Y) :
    WeakEquivalence (fibrantObjectOpEquivalence.functor.map f) ↔ WeakEquivalence f.unop := by
  rw [weakEquivalence_iff, weakEquivalence_iff]
  exact Iff.rfl

/-- The inverse equivalence preserves and reflects weak equivalences. -/
theorem weakEquivalence_fibrantObjectOpEquivalence_inverse_map_iff
    {X Y : CofibrantObject Cᵒᵖ} (g : X ⟶ Y) :
    WeakEquivalence (fibrantObjectOpEquivalence.inverse.map g).unop ↔ WeakEquivalence g := by
  rw [← weakEquivalence_fibrantObjectOpEquivalence_functor_map_iff]
  rfl

/-- The weak equivalences of cofibrant objects of `Cᵒᵖ` are exactly the
reversed weak equivalences of fibrant objects. -/
theorem weakEquivalences_cofibrantObject_op_inverseImage :
    (weakEquivalences (CofibrantObject Cᵒᵖ)).inverseImage fibrantObjectOpEquivalence.functor =
      (weakEquivalences (FibrantObject C)).op := by
  ext X Y f
  exact (weakEquivalence_iff _).symm.trans
    ((weakEquivalence_fibrantObjectOpEquivalence_functor_map_iff f).trans (weakEquivalence_iff _))

/-- A functor on fibrant objects inverts weak equivalences exactly when its
transport to cofibrant objects of `Cᵒᵖ` does. -/
theorem isInvertedBy_inverse_comp_op_iff {D : Type*} [Category D] (F : FibrantObject C ⥤ D) :
    (weakEquivalences (CofibrantObject Cᵒᵖ)).IsInvertedBy
        (fibrantObjectOpEquivalence.inverse ⋙ F.op) ↔
      (weakEquivalences (FibrantObject C)).IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    have hf' : weakEquivalences (CofibrantObject Cᵒᵖ)
        (fibrantObjectOpEquivalence.functor.map f.op) :=
      (weakEquivalence_iff _).1
        ((weakEquivalence_fibrantObjectOpEquivalence_functor_map_iff f.op).2 ⟨hf⟩)
    have : IsIso (F.map f).op := h _ hf'
    exact isIso_of_op (F.map f)
  · intro h X Y g hg
    have hg' : weakEquivalences (FibrantObject C)
        (fibrantObjectOpEquivalence.inverse.map g).unop :=
      (weakEquivalence_iff _).1
        ((weakEquivalence_fibrantObjectOpEquivalence_inverse_map_iff g).2 ⟨hg⟩)
    have := h _ hg'
    change IsIso (F.map (fibrantObjectOpEquivalence.inverse.map g).unop).op
    infer_instance

end ABCCofibrations.ABCPrefibrationCategory

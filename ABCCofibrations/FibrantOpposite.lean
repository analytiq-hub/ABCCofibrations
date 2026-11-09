/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationBasic
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Localization.Equivalence
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

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

/-! ### Transporting morphism classes, localizations, and fractions

Let `W` be a class of morphisms of fibrant objects and `W'` a class of
cofibrant objects of `Cᵒᵖ` corresponding to it under the equivalence. Then
inverting functors, localization functors, and fractions correspond. These
general statements are instantiated for weak equivalences and for trivial
(co)fibrations. -/

section Transport

variable (W : MorphismProperty (FibrantObject C)) (W' : MorphismProperty (CofibrantObject Cᵒᵖ))
  (hW : ∀ {X Y : FibrantObject C} (f : X ⟶ Y),
    W' (fibrantObjectOpEquivalence.functor.map f.op) ↔ W f)

include hW in
/-- Membership of a cofibrant-side arrow is membership of its transport. -/
theorem mem_iff_inverse_map_unop {X Y : CofibrantObject Cᵒᵖ} (g : X ⟶ Y) :
    W' g ↔ W (fibrantObjectOpEquivalence.inverse.map g).unop :=
  hW (fibrantObjectOpEquivalence.inverse.map g).unop

include hW in
/-- A functor on fibrant objects inverts `W` exactly when its transport to
cofibrant objects of `Cᵒᵖ` inverts `W'`. -/
theorem isInvertedBy_inverse_comp_op_iff_of {D : Type*} [Category D] (F : FibrantObject C ⥤ D) :
    W'.IsInvertedBy (fibrantObjectOpEquivalence.inverse ⋙ F.op) ↔ W.IsInvertedBy F := by
  constructor
  · intro h X Y f hf
    have : IsIso (F.map f).op := h _ ((hW f).2 hf)
    exact isIso_of_op (F.map f)
  · intro h X Y g hg
    have := h _ ((mem_iff_inverse_map_unop W W' hW g).1 hg)
    change IsIso (F.map (fibrantObjectOpEquivalence.inverse.map g).unop).op
    infer_instance

include hW in
/-- The transport of a localization of fibrant objects at `W` is a
localization of cofibrant objects of `Cᵒᵖ` at `W'`. -/
theorem isLocalization_inverse_comp_op {D : Type*} [Category D]
    (L : FibrantObject C ⥤ D) [L.IsLocalization W] :
    (fibrantObjectOpEquivalence.inverse ⋙ L.op).IsLocalization W' :=
  Functor.IsLocalization.of_equivalence_source L.op W.op _ W' fibrantObjectOpEquivalence
    (fun _ _ f hf ↦ W'.le_isoClosure _ ((hW f.unop).2 hf))
    ((isInvertedBy_inverse_comp_op_iff_of W W' hW L).2 (Localization.inverts L W))
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight fibrantObjectOpEquivalence.unitIso.symm _ ≪≫ L.op.leftUnitor)

variable {W W'}

/-- A right fraction of fibrant objects, reversed, is a left fraction of
cofibrant objects of `Cᵒᵖ`. -/
@[simps]
def rightFractionOp {X Y : FibrantObject C} (φ : W.RightFraction X Y) :
    W'.LeftFraction (fibrantObjectOpEquivalence.functor.obj (Opposite.op Y))
      (fibrantObjectOpEquivalence.functor.obj (Opposite.op X)) where
  f := fibrantObjectOpEquivalence.functor.map φ.f.op
  s := fibrantObjectOpEquivalence.functor.map φ.s.op
  hs := (hW φ.s).2 φ.hs

/-- A left fraction of cofibrant objects of `Cᵒᵖ`, reversed, is a right
fraction of fibrant objects. -/
@[simps]
def leftFractionUnop {X Y : FibrantObject C}
    (ψ : W'.LeftFraction (fibrantObjectOpEquivalence.functor.obj (Opposite.op Y))
      (fibrantObjectOpEquivalence.functor.obj (Opposite.op X))) :
    W.RightFraction X Y where
  X' := (fibrantObjectOpEquivalence.inverse.obj ψ.Y').unop
  s := (fibrantObjectOpEquivalence.inverse.map ψ.s).unop
  hs := (mem_iff_inverse_map_unop W W' hW ψ.s).1 ψ.hs
  f := (fibrantObjectOpEquivalence.inverse.map ψ.f).unop

include hW in
/-- Evaluating the reversed fraction on the transported functor gives the
opposite of the original value. -/
theorem rightFractionOp_map {D : Type*} [Category D] {X Y : FibrantObject C}
    (φ : W.RightFraction X Y) (F : FibrantObject C ⥤ D) (hF : W.IsInvertedBy F) :
    (rightFractionOp hW φ).map (fibrantObjectOpEquivalence.inverse ⋙ F.op)
        ((isInvertedBy_inverse_comp_op_iff_of W W' hW F).2 hF) =
      (φ.map F hF).op := by
  have := hF _ φ.hs
  change (F.map φ.f).op ≫ inv (F.map φ.s).op = (inv (F.map φ.s) ≫ F.map φ.f).op
  rw [op_comp, op_inv]

include hW in
/-- Evaluating the reversed left fraction gives the unopposite of the value
of the original left fraction on the transported functor. -/
theorem leftFractionUnop_map {D : Type*} [Category D] {X Y : FibrantObject C}
    (ψ : W'.LeftFraction (fibrantObjectOpEquivalence.functor.obj (Opposite.op Y))
      (fibrantObjectOpEquivalence.functor.obj (Opposite.op X)))
    (F : FibrantObject C ⥤ D) (hF : W.IsInvertedBy F) :
    (leftFractionUnop hW ψ).map F hF =
      (ψ.map (fibrantObjectOpEquivalence.inverse ⋙ F.op)
        ((isInvertedBy_inverse_comp_op_iff_of W W' hW F).2 hF)).unop := by
  have := hF _ (leftFractionUnop hW ψ).hs
  apply Quiver.Hom.op_inj
  change (inv (F.map (leftFractionUnop hW ψ).s) ≫ F.map (leftFractionUnop hW ψ).f).op =
    (F.map (leftFractionUnop hW ψ).f).op ≫ inv (F.map (leftFractionUnop hW ψ).s).op
  rw [op_comp, op_inv]

end Transport

/-- Weak equivalences correspond under the equivalence. -/
theorem weakEquivalences_functor_map_op_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    weakEquivalences (CofibrantObject Cᵒᵖ) (fibrantObjectOpEquivalence.functor.map f.op) ↔
      weakEquivalences (FibrantObject C) f :=
  (weakEquivalence_iff _).symm.trans
    ((weakEquivalence_fibrantObjectOpEquivalence_functor_map_iff f.op).trans
      (weakEquivalence_iff _))

/-- A functor on fibrant objects inverts weak equivalences exactly when its
transport to cofibrant objects of `Cᵒᵖ` does. -/
theorem isInvertedBy_inverse_comp_op_iff {D : Type*} [Category D] (F : FibrantObject C ⥤ D) :
    (weakEquivalences (CofibrantObject Cᵒᵖ)).IsInvertedBy
        (fibrantObjectOpEquivalence.inverse ⋙ F.op) ↔
      (weakEquivalences (FibrantObject C)).IsInvertedBy F :=
  isInvertedBy_inverse_comp_op_iff_of _ _ weakEquivalences_functor_map_op_iff F

/-- Any localization of fibrant objects at weak equivalences transports to
a localization of cofibrant objects of `Cᵒᵖ` at weak equivalences. -/
instance isLocalization_weakEquivalences_inverse_comp_op {D : Type*} [Category D]
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))] :
    (fibrantObjectOpEquivalence.inverse ⋙ L.op).IsLocalization
      (weakEquivalences (CofibrantObject Cᵒᵖ)) :=
  isLocalization_inverse_comp_op _ _ weakEquivalences_functor_map_op_iff L

end ABCCofibrations.ABCPrefibrationCategory

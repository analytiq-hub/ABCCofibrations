/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.RightHomotopyCategoryOpposite
public import ABCCofibrations.RightHomotopyCancellation
public import ABCCofibrations.HomotopyOre

/-!
# The right homotopy Ore condition

Theorem 6.4.3(2)(a) follows by duality from the cylinder Ore construction.
On the native right-homotopy quotient this gives a right calculus of fractions.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- Complete a cospan with a weak-equivalence right leg to a strictly
right-homotopy-commutative square, with a weak-equivalence left leg. -/
theorem exists_strict_right_homotopy_ore {A B B' : C} [IsFibrant A] [IsFibrant B]
    [IsFibrant B'] [HasBinaryProduct B B] (f : A ⟶ B) (b : B' ⟶ B)
    [WeakEquivalence b] :
    ∃ (A' : C) (a : A' ⟶ A) (bottom : A' ⟶ B'),
      IsFibrant A' ∧ WeakEquivalence a ∧ StrictRightHomotopyRel (bottom ≫ b) (a ≫ f) := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  obtain ⟨P, bottom, a, hP, ha, h⟩ :=
    ABCPrecofibrationCategory.exists_strict_homotopy_ore f.op b.op
  refine ⟨P.unop, a.unop, bottom.unop, (isFibrant_iff_isCofibrant_op P.unop).2 hP,
    (weakEquivalences_unop_iff a).2 ha, ?_⟩
  exact (strictRightHomotopy_iff_op _ _).2 h

/-- The native right-homotopy quotient has a right calculus of fractions.
Ore squares are the transported strict homotopy squares; extensionality
uses cancellation and an identity denominator. -/
instance weakEquivalences_rightHomotopyCategory_hasRightCalculusOfFractions :
    (weakEquivalences (RightHomotopyCategory C)).HasRightCalculusOfFractions where
  exists_rightFraction := by
    intro X Y φ
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨S, f, s, hs, rfl⟩ := φ.cases
    obtain ⟨S⟩ := S
    obtain ⟨s, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective s
    obtain ⟨f, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective f
    have hsw : WeakEquivalence s.hom :=
      (weakEquivalence_toRightHomotopyCategory_map_iff s).1 ((weakEquivalence_iff _).2 hs)
    let := hsw
    let := hasBinaryProduct S.obj S.obj
    obtain ⟨A', a, bottom, hA', ha, hhom⟩ := exists_strict_right_homotopy_ore f.hom s.hom
    let := hA'
    let Z := FibrantObject.mk A'
    let a' : Z ⟶ X := FibrantObject.homMk a
    let bottom' : Z ⟶ Y := FibrantObject.homMk bottom
    have hW : weakEquivalences (RightHomotopyCategory C) (toRightHomotopyCategory.map a') :=
      (weakEquivalence_iff _).1 ((weakEquivalence_toRightHomotopyCategory_map_iff a').2 ha)
    refine ⟨{
      f := toRightHomotopyCategory.map bottom'
      s := toRightHomotopyCategory.map a'
      hs := hW }, ?_⟩
    have he : toRightHomotopyCategory.map (bottom' ≫ s) =
        toRightHomotopyCategory.map (a' ≫ f) :=
      (toRightHomotopyCategory_map_eq_iff _ _).2 (RightHomotopyRel.of_strict hhom)
    exact he.symm
  ext := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Y'⟩ f₁ f₂ s hs h
    obtain ⟨f₁, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective f₂
    obtain ⟨s, rfl⟩ := (toRightHomotopyCategory (C := C)).map_surjective s
    have hsw : WeakEquivalence s.hom :=
      (weakEquivalence_toRightHomotopyCategory_map_iff s).1 ((weakEquivalence_iff _).2 hs)
    let := hsw
    let := hasBinaryProduct Y'.obj Y'.obj
    have hpost : RightHomotopyRel (f₁.hom ≫ s.hom) (f₂.hom ≫ s.hom) :=
      (toRightHomotopyCategory_map_eq_iff (f₁ ≫ s) (f₂ ≫ s)).1 h
    let := hasBinaryProduct Y.obj Y.obj
    have hcancel := RightHomotopyRel.of_postcomp_weakEquivalence s.hom hpost
    refine ⟨toRightHomotopyCategory.obj X, 𝟙 _,
      (weakEquivalences (RightHomotopyCategory C)).id_mem _, ?_⟩
    exact congrArg (𝟙 _ ≫ ·) ((toRightHomotopyCategory_map_eq_iff f₁ f₂).2 hcancel)

end ABCCofibrations.ABCPrefibrationCategory

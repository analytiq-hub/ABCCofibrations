/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReplacementComparison

/-!
# Fractions in an ambient localization

Theorems 6.4.4(1)(a,b) and 6.4.5(1)(a,b), obtained by restricting an arbitrary
ambient localization to cofibrant objects using Theorem 6.1.6. The stronger
representation has cofibration numerator and full coproduct boundary, and a
trivial-cofibration denominator. Both the general weak-equivalence-denominator
criterion of 6.4.4(1)(b) and the sharper trivial-cofibration criterion are included.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Theorem 6.4.5(1)(a): the numerator and combined coproduct map may both
be cofibrations, while the denominator is a trivial cofibration. -/
theorem exists_ambient_cofibration_fraction_with_coprod
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B : C} [IsCofibrant A] [IsCofibrant B] [HasBinaryCoproduct A B]
    (α : L.obj A ⟶ L.obj B) :
    ∃ (Z : C) (i : A ⟶ Z) (s : B ⟶ Z),
      IsCofibrant Z ∧ Cofibration i ∧ Cofibration s ∧ WeakEquivalence s ∧
        Cofibration (coprod.desc i s) ∧ α ≫ L.map s = L.map i := by
  obtain ⟨Z, i, s, hi, hs, hb, h⟩ :=
    exists_cofibration_fraction_with_coprod (CofibrantObject.ι ⋙ L)
      (X := CofibrantObject.mk A) (Y := CofibrantObject.mk B) α
  obtain ⟨hcs, hws⟩ := (mem_cofibrantTrivialCofibrations_iff s).1 hs
  exact ⟨Z.obj, i.hom, s.hom, inferInstance, hi, hcs, hws, hb, h⟩

/-- Theorem 6.4.4(1)(a), with the denominator strengthened to a trivial
cofibration. No chosen binary coproduct is required in the interface. -/
theorem exists_ambient_trivialCofibration_fraction
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B : C} [IsCofibrant A] [IsCofibrant B]
    (α : L.obj A ⟶ L.obj B) :
    ∃ (Z : C) (f : A ⟶ Z) (s : B ⟶ Z),
      IsCofibrant Z ∧ Cofibration s ∧ WeakEquivalence s ∧ α ≫ L.map s = L.map f := by
  let := hasBinaryCoproduct A B
  obtain ⟨Z, i, s, hZ, _, hs, hw, _, h⟩ :=
    exists_ambient_cofibration_fraction_with_coprod L α
  exact ⟨Z, i, s, hZ, hs, hw, h⟩

/-- Evaluate a trivial-cofibration fraction in an ambient localization. -/
noncomputable def ambientTrivialCofibrationFractionMap
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C}
    (φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y) :
    L.obj X.obj ⟶ L.obj Y.obj :=
  φ.map (CofibrantObject.ι ⋙ L)
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations _).1
      (Localization.inverts (CofibrantObject.ι ⋙ L) _))

/-- The evaluated fraction has the expected numerator after postcomposition
with its denominator. -/
theorem ambientTrivialCofibrationFractionMap_comp_denominator
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C}
    (φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y) :
    ambientTrivialCofibrationFractionMap L φ ≫ L.map φ.s.hom = L.map φ.f.hom :=
  φ.map_comp_map_s (CofibrantObject.ι ⋙ L) _

/-- Every ambient localized arrow between cofibrant objects is the image
of a trivial-cofibration fraction. -/
theorem exists_ambient_leftFraction
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C} (α : L.obj X.obj ⟶ L.obj Y.obj) :
    ∃ φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y,
      ambientTrivialCofibrationFractionMap L φ = α :=
  exists_leftFraction_of_weakEquivalence_localization (CofibrantObject.ι ⋙ L) α

/-- Equality over any fixed common trivial-cofibration denominator is detected
by left homotopy of extended numerators in ambient localization. -/
theorem ambient_trivialCofibration_fraction_map_eq_iff_leftHomotopy
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y P : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : cofibrantTrivialCofibrations i) (hj : cofibrantTrivialCofibrations j)
    (hs : φ.s ≫ i = ψ.s ≫ j) :
    ambientTrivialCofibrationFractionMap L φ = ambientTrivialCofibrationFractionMap L ψ ↔
      cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j) :=
  trivialCofibration_fraction_map_eq_iff_leftHomotopy φ ψ i j hi hj hs
    (CofibrantObject.ι ⋙ L) _

/-- Theorem 6.4.5(1)(b): equality is equivalent to common trivial-cofibration
extensions with strictly equal denominators and left-homotopic numerators. -/
theorem ambient_trivialCofibration_fraction_map_eq_iff_exists_leftHomotopy
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y) :
    ambientTrivialCofibrationFractionMap L φ = ambientTrivialCofibrationFractionMap L ψ ↔
      ∃ (P : CofibrantObject C) (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P),
        cofibrantTrivialCofibrations i ∧ cofibrantTrivialCofibrations j ∧
        φ.s ≫ i = ψ.s ≫ j ∧ cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j) :=
  trivialCofibration_fraction_map_eq_iff_exists_leftHomotopy φ ψ
    (CofibrantObject.ι ⋙ L) _

/-- Evaluate a fraction with arbitrary weak-equivalence denominator in an
ambient localization. -/
noncomputable def ambientWeakEquivalenceFractionMap
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C}
    (φ : (weakEquivalences (CofibrantObject C)).LeftFraction X Y) :
    L.obj X.obj ⟶ L.obj Y.obj :=
  φ.map (CofibrantObject.ι ⋙ L) (Localization.inverts (CofibrantObject.ι ⋙ L) _)

/-- Theorem 6.4.4(1)(b): arbitrary weak-equivalence fractions are equal
exactly when they admit common weak-equivalence extensions with left-homotopic
numerator and denominator triangles. -/
theorem ambient_weakEquivalence_fraction_map_eq_iff_exists_leftHomotopy
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C}
    (φ ψ : (weakEquivalences (CofibrantObject C)).LeftFraction X Y) :
    ambientWeakEquivalenceFractionMap L φ = ambientWeakEquivalenceFractionMap L ψ ↔
      ∃ (P : CofibrantObject C) (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P),
        weakEquivalences (CofibrantObject C) i ∧
        weakEquivalences (CofibrantObject C) j ∧
        cofibrantLeftHomotopyRel (φ.s ≫ i) (ψ.s ≫ j) ∧
        cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j) :=
  weakEquivalence_fraction_map_eq_iff_exists_leftHomotopy φ ψ (CofibrantObject.ι ⋙ L)

end ABCCofibrations.ABCPrecofibrationCategory

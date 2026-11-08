/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.TrivialCofibrationFractions
public import ABCCofibrations.HomotopyLocalization

/-!
# Comparing fractions up to left homotopy

A common extension of two cospans identifies their fractions whenever both
the numerator and denominator triangles commute up to left homotopy.
This gives a sufficient equality criterion, without asserting its converse.
-/

public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Homotopic extended numerators and denominators give equal fractions
under any functor inverting trivial cofibrations. -/
theorem trivialCofibration_fraction_map_eq_of_homotopy_extension
    {X Y P : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : cofibrantTrivialCofibrations i)
    (hs : cofibrantLeftHomotopyRel (φ.s ≫ i) (ψ.s ≫ j))
    (hf : cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j))
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF := by
  let := hF _ φ.hs
  let := hF _ hi
  have hsi := map_eq_of_cofibrant_leftHomotopy F
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).2 hF) hs
  have hfi := map_eq_of_cofibrant_leftHomotopy F
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).2 hF) hf
  have : IsIso (F.map (φ.s ≫ i)) := by rw [F.map_comp]; infer_instance
  apply (cancel_mono (F.map (φ.s ≫ i))).1
  calc
    φ.map F hF ≫ F.map (φ.s ≫ i) = F.map (φ.f ≫ i) := by
      simp only [F.map_comp]
      rw [← Category.assoc, φ.map_comp_map_s]
    _ = F.map (ψ.f ≫ j) := hfi
    _ = ψ.map F hF ≫ F.map (ψ.s ≫ j) := by
      simp only [F.map_comp]
      rw [← Category.assoc, ψ.map_comp_map_s]
    _ = ψ.map F hF ≫ F.map (φ.s ≫ i) := by rw [hsi]

/-- With strictly equal extended denominators, only the numerators need
to be left homotopic. -/
theorem trivialCofibration_fraction_map_eq_of_leftHomotopy
    {X Y P : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : cofibrantTrivialCofibrations i) (hj : cofibrantTrivialCofibrations j)
    (hs : φ.s ≫ i = ψ.s ≫ j)
    (hf : cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j))
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF :=
  (trivialCofibration_fraction_map_eq_iff φ ψ i j hi hj hs F hF).2
    (map_eq_of_cofibrant_leftHomotopy F
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).2 hF) hf)

end ABCCofibrations.ABCPrecofibrationCategory

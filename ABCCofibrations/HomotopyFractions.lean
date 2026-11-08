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
For localization of cofibrant objects, equality is also detected by left
homotopy of the numerators over any common trivial-cofibration denominator.
For arbitrary weak-equivalence denominators, the quotient's calculus of
fractions detects equality by weak-equivalence extensions and homotopies
of both the numerator and denominator triangles (Theorem 6.4.4(1)(b)).
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

/-- In a localization of cofibrant objects, equality over a fixed common
trivial-cofibration denominator is exactly left homotopy of the numerators. -/
theorem trivialCofibration_fraction_map_eq_iff_leftHomotopy
    {X Y P : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : cofibrantTrivialCofibrations i) (hj : cofibrantTrivialCofibrations j)
    (hs : φ.s ≫ i = ψ.s ≫ j)
    (F : CofibrantObject C ⥤ D)
    [F.IsLocalization (weakEquivalences (CofibrantObject C))]
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF ↔ cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j) :=
  (trivialCofibration_fraction_map_eq_iff φ ψ i j hi hj hs F hF).trans
    (map_eq_iff_cofibrant_leftHomotopy F _ _)

/-- The cofibrant-subcategory version of the trivial-cofibration fraction
equality criterion in Theorem 6.4.5(1)(b). Equal fractions admit a common
trivial-cofibration extension with strictly equal denominators and left-homotopic
numerators. -/
theorem trivialCofibration_fraction_map_eq_iff_exists_leftHomotopy
    {X Y : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (F : CofibrantObject C ⥤ D)
    [F.IsLocalization (weakEquivalences (CofibrantObject C))]
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF ↔
      ∃ (P : CofibrantObject C) (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P),
        cofibrantTrivialCofibrations i ∧ cofibrantTrivialCofibrations j ∧
        φ.s ≫ i = ψ.s ≫ j ∧ cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j) := by
  constructor
  · intro he
    obtain ⟨P, i, j, hi, hj, hs⟩ :=
      exists_common_trivialCofibration_denominator φ.s ψ.s φ.hs ψ.hs
    exact ⟨P, i, j, hi, hj, hs,
      (trivialCofibration_fraction_map_eq_iff_leftHomotopy φ ψ i j hi hj hs F hF).1 he⟩
  · rintro ⟨P, i, j, hi, hj, hs, hh⟩
    exact (trivialCofibration_fraction_map_eq_iff_leftHomotopy φ ψ i j hi hj hs F hF).2 hh

/-- Homotopic common extensions identify fractions with arbitrary
weak-equivalence denominators under every weak-equivalence-inverting functor. -/
theorem weakEquivalence_fraction_map_eq_of_homotopy_extension
    {X Y P : CofibrantObject C}
    (φ ψ : (weakEquivalences (CofibrantObject C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : weakEquivalences (CofibrantObject C) i)
    (hs : cofibrantLeftHomotopyRel (φ.s ≫ i) (ψ.s ≫ j))
    (hf : cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j))
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF := by
  let := hF _ φ.hs
  let := hF _ hi
  have hsi := map_eq_of_cofibrant_leftHomotopy F hF hs
  have hfi := map_eq_of_cofibrant_leftHomotopy F hF hf
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

set_option backward.isDefEq.respectTransparency false in
/-- The cofibrant-subcategory version of Theorem 6.4.4(1)(b). Equality of
arbitrary weak-equivalence fractions is detected by common weak-equivalence
extensions with left-homotopic numerator and denominator triangles. -/
theorem weakEquivalence_fraction_map_eq_iff_exists_leftHomotopy
    {X Y : CofibrantObject C}
    (φ ψ : (weakEquivalences (CofibrantObject C)).LeftFraction X Y)
    (F : CofibrantObject C ⥤ D)
    [F.IsLocalization (weakEquivalences (CofibrantObject C))] :
    φ.map F (Localization.inverts F _) = ψ.map F (Localization.inverts F _) ↔
      ∃ (P : CofibrantObject C) (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P),
        weakEquivalences (CofibrantObject C) i ∧
        weakEquivalences (CofibrantObject C) j ∧
        cofibrantLeftHomotopyRel (φ.s ≫ i) (ψ.s ≫ j) ∧
        cofibrantLeftHomotopyRel (φ.f ≫ i) (ψ.f ≫ j) := by
  constructor
  · intro he
    let Q := toLeftHomotopyCategory (C := C)
    let G := leftHomotopyCategoryToLocalization (C := C)
    let lift (φ : (weakEquivalences (CofibrantObject C)).LeftFraction X Y) :
        (weakEquivalences (LeftHomotopyCategory C)).LeftFraction (Q.obj X) (Q.obj Y) :=
      { f := Q.map φ.f, s := Q.map φ.s
        hs := (MorphismProperty.quotient_iff _ _ φ.s).2 φ.hs }
    have he' : (lift φ).map G (Localization.inverts G _) =
        (lift ψ).map G (Localization.inverts G _) := by
      change φ.map (weakEquivalences (CofibrantObject C)).Q
          (weakEquivalences (CofibrantObject C)).Q_inverts =
        ψ.map (weakEquivalences (CofibrantObject C)).Q
          (weakEquivalences (CofibrantObject C)).Q_inverts
      exact φ.map_eq_of_map_eq ψ F (weakEquivalences (CofibrantObject C)).Q he
    obtain ⟨P, i, j, hs, hf, hw⟩ :=
      (MorphismProperty.LeftFraction.map_eq_iff G
        (weakEquivalences (LeftHomotopyCategory C)) (lift φ) (lift ψ)).1 he'
    rcases P with ⟨P⟩
    obtain ⟨i, rfl⟩ := Q.map_surjective i
    obtain ⟨j, rfl⟩ := Q.map_surjective j
    have hwi : weakEquivalences (LeftHomotopyCategory C) (Q.map i) :=
      (weakEquivalences (LeftHomotopyCategory C)).of_precomp _ _ (lift φ).hs hw
    have hwj : weakEquivalences (LeftHomotopyCategory C) (Q.map j) :=
      (weakEquivalences (LeftHomotopyCategory C)).of_precomp _ _ (lift ψ).hs
        (hs ▸ hw)
    refine ⟨P, i, j, (MorphismProperty.quotient_iff _ _ i).1 hwi,
      (MorphismProperty.quotient_iff _ _ j).1 hwj, ?_, ?_⟩
    · apply (toLeftHomotopyCategory_map_eq_iff _ _).1
      simpa only [lift, Q, Functor.map_comp] using hs
    · apply (toLeftHomotopyCategory_map_eq_iff _ _).1
      simpa only [lift, Q, Functor.map_comp] using hf
  · rintro ⟨P, i, j, hi, _, hs, hf⟩
    exact weakEquivalence_fraction_map_eq_of_homotopy_extension φ ψ i j hi hs hf
      F (Localization.inverts F _)

end ABCCofibrations.ABCPrecofibrationCategory

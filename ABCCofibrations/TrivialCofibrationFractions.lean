/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.TrivialCofibrationLocalization
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
# Left-fraction representations

Pushouts suffice to represent localization morphisms by cospans with a
trivial-cofibration denominator. No cancellation axiom is needed here.
-/

public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Every localized arrow is represented by a cospan whose backward arrow
is a trivial cofibration. The equation avoids choosing an inverse explicitly. -/
theorem exists_trivialCofibration_fraction
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (cofibrantTrivialCofibrations (C := C))]
    {X Y : CofibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : CofibrantObject C) (f : X ⟶ Z) (s : Y ⟶ Z),
      cofibrantTrivialCofibrations s ∧ α ≫ L.map s = L.map f := by
  let T := cofibrantTrivialCofibrations (C := C)
  let P : StructuredArrow (L.obj X) L → Prop := fun a ↦
    ∃ (Z : CofibrantObject C) (f : X ⟶ Z) (s : a.right ⟶ Z),
      T s ∧ a.hom ≫ L.map s = L.map f
  change P (StructuredArrow.mk α)
  apply Localization.induction_structuredArrow L T P
  · refine ⟨X, 𝟙 X, 𝟙 X, ?_, by simp⟩
    apply (mem_cofibrantTrivialCofibrations_iff _).2
    exact ⟨cofibration_of_isIso (𝟙 X.obj), weakEquivalence_of_isIso (𝟙 X.obj)⟩
  · intro Y₁ Y₂ g β hβ
    obtain ⟨Z, f, s, hs, h⟩ := hβ
    change β ≫ L.map s = L.map f at h
    obtain ⟨Z', k, t, ht, sq⟩ := exists_trivialCofibration_ore_square s g hs
    refine ⟨Z', f ≫ k, t, ht, ?_⟩
    change (β ≫ L.map g) ≫ L.map t = L.map (f ≫ k)
    rw [Category.assoc, ← L.map_comp, ← sq, L.map_comp,
      ← Category.assoc, h, ← L.map_comp]
  · intro Y₁ Y₂ w hw β hβ
    obtain ⟨Z, f, s, hs, h⟩ := hβ
    change β ≫ L.map s = L.map f at h
    obtain ⟨hcw, hew⟩ := (mem_cofibrantTrivialCofibrations_iff w).1 hw
    obtain ⟨hcs, hes⟩ := (mem_cofibrantTrivialCofibrations_iff s).1 hs
    let := hcw
    let := hew
    let := hcs
    let := hes
    refine ⟨Z, f, w ≫ s, ?_, ?_⟩
    · apply (mem_cofibrantTrivialCofibrations_iff _).2
      change Cofibration (w.hom ≫ s.hom) ∧ WeakEquivalence (w.hom ≫ s.hom)
      exact ⟨inferInstance, inferInstance⟩
    · change (β ≫ (Localization.isoOfHom L T w hw).inv) ≫ L.map (w ≫ s) = _
      rw [L.map_comp, Category.assoc, ← Category.assoc
        (Localization.isoOfHom L T w hw).inv]
      simpa using h

/-- The cospan representation, expressed using mathlib's fraction type. -/
theorem exists_leftFraction_trivialCofibration
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (cofibrantTrivialCofibrations (C := C))]
    {X Y : CofibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y,
      φ.map L (Localization.inverts L _) = α := by
  obtain ⟨Z, f, s, hs, h⟩ := exists_trivialCofibration_fraction L α
  let φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y := ⟨f, s, hs⟩
  let := Localization.inverts L (cofibrantTrivialCofibrations (C := C)) s hs
  refine ⟨φ, (cancel_mono (L.map s)).1 ?_⟩
  rw [φ.map_comp_map_s, h]

end ABCCofibrations.ABCPrecofibrationCategory

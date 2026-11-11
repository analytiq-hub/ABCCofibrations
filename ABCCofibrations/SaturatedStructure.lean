/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyIsomorphisms

/-!
# The saturated precofibration structure (Theorem 7.2.8)

For a precofibration category `(M, W, Cof)`, the saturation `W̄` of `W` consists of
the maps which become isomorphisms in the homotopy category. Theorem 7.2.8(1)
(Cisinski): `(M, W̄, Cof)` is again a precofibration category. The only axiom
which needs proof is CF3(2); it follows from Lemma 7.2.1 by pushing out the two
auxiliary cofibrations along the given pushout square.

The saturated structure lives on a type synonym `Saturated C`, so that it does not
clash with the given weak equivalences of `C`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- The saturation `W̄`: the maps which become isomorphisms in the homotopy
category, here the localization `(weakEquivalences C).Q`. -/
def saturation : MorphismProperty C :=
  (MorphismProperty.isomorphisms _).inverseImage (weakEquivalences C).Q

variable {C} in
omit [CategoryWithCofibrations C] [HasInitial C] in
/-- Membership in the saturation can be tested in any localization. -/
theorem saturation_iff {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {X Y : C} (f : X ⟶ Y) :
    saturation C f ↔ IsIso (L.map f) := by
  let E := Localization.uniq (weakEquivalences C).Q L (weakEquivalences C)
  have e : (weakEquivalences C).Q ⋙ E.functor ≅ L :=
    Localization.compUniqFunctor _ L (weakEquivalences C)
  change IsIso ((weakEquivalences C).Q.map f) ↔ _
  rw [← NatIso.isIso_map_iff e f, Functor.comp_map]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ isIso_of_reflects_iso _ E.functor⟩

/-- A type synonym for `C`, carrying the saturated weak equivalences and the same
cofibrations and initial object. -/
def Saturated : Type u := C

instance : Category.{v} (Saturated C) := inferInstanceAs (Category.{v} C)

instance : CategoryWithCofibrations (Saturated C) := inferInstanceAs (CategoryWithCofibrations C)

instance : CategoryWithWeakEquivalences (Saturated C) where
  weakEquivalences := saturation C

instance : HasInitial (Saturated C) := inferInstanceAs (HasInitial C)

variable {C} [ABCPrecofibrationCategory C]

/-- CF3(2) for the saturation: the cobase change of a cofibration in `W̄` with
cofibrant domain, along a map to a cofibrant object, is in `W̄`. -/
theorem saturation_cobaseChange {D' : Type*} [Category D'] (L : C ⥤ D')
    [L.IsLocalization (weakEquivalences C)] {A B D E : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ E} {j : D ⟶ E} (h : IsPushout i f g j) (hA : IsCofibrant A) (hD : IsCofibrant D)
    (hi : Cofibration i) (hw : IsIso (L.map i)) : IsIso (L.map j) := by
  have : IsCofibrant B := cofibrant_target i
  have : Cofibration j := cofibration_of_isPushout h
  have : IsCofibrant E := cofibrant_target j
  obtain ⟨B', B'', i', i'', hi', hi'', hw₁, hw₂⟩ := (isIso_map_iff L i).1 hw
  have : IsCofibrant B' := cofibrant_target i'
  let sq₁ := IsPushout.of_hasPushout i' g
  have : Cofibration (pushout.inr i' g) := cofibration_of_isPushout sq₁
  have : IsCofibrant (pushout i' g) := cofibrant_target (pushout.inr i' g)
  let sq₂ := IsPushout.of_hasPushout i'' (pushout.inl i' g)
  have : Cofibration (pushout.inr i'' (pushout.inl i' g)) := cofibration_of_isPushout sq₂
  have h₁ : WeakEquivalence (j ≫ pushout.inr i' g) :=
    weakEquivalence_of_isPushout (h.paste_horiz sq₁)
  have h₂ : WeakEquivalence (pushout.inr i' g ≫ pushout.inr i'' (pushout.inl i' g)) :=
    weakEquivalence_of_isPushout (sq₁.paste_horiz sq₂)
  exact (isIso_map_iff L j).2 ⟨_, _, _, _, inferInstance, inferInstance, h₁, h₂⟩

/-- **Theorem 7.2.8(1)** (Cisinski). If `(M, W, Cof)` is a precofibration
category, so is `(M, W̄, Cof)`. -/
theorem saturated_precofibrationCategory : ABCPrecofibrationCategory (Saturated C) := by
  let L := (weakEquivalences C).Q
  have hsat {X Y : C} (f : X ⟶ Y) : WeakEquivalence (C := Saturated C) f ↔ IsIso (L.map f) :=
    ⟨fun h ↦ h.mem, fun h ↦ ⟨h⟩⟩
  exact
  { initial_cofibrant := initial_cofibrant (C := C)
    cofibrations_comp := cofibrations_comp (C := C)
    weakEquivalence_of_isIso := fun {X Y} f hf ↦ (hsat f).2 (by
      have : IsIso (C := C) f := hf
      exact Functor.map_isIso L f)
    cofibration_of_isIso := fun {X Y} f hf hX ↦ by
      have : IsIso (C := C) f := hf
      have : IsCofibrant (C := C) X := hX
      exact cofibration_of_isIso (C := C) f
    weakEquivalences_twoOutOfThree :=
      inferInstanceAs ((MorphismProperty.isomorphisms _).inverseImage L).HasTwoOutOfThreeProperty
    hasPushout := fun {A B D} i f hA hD hi ↦ by
      have : IsCofibrant (C := C) A := hA
      have : IsCofibrant (C := C) D := hD
      have : Cofibration (C := C) i := hi
      exact hasPushout (C := C) i f
    cofibration_of_isPushout := fun {A B D E i f g j} h hA hD hi ↦ by
      have : IsCofibrant (C := C) A := hA
      have : IsCofibrant (C := C) D := hD
      have : Cofibration (C := C) i := hi
      exact cofibration_of_isPushout (C := C) h
    weakEquivalence_of_isPushout := fun {A B D E i f g j} h hA hD hi hw ↦
      (hsat j).2 (saturation_cobaseChange (C := C) L h hA hD hi ((hsat i).1 hw))
    factorization := fun {A B} f hA ↦ by
      have : IsCofibrant (C := C) A := hA
      obtain ⟨Z, i, p, hi, hp, hfac⟩ := factorization (C := C) f
      exact ⟨Z, i, p, hi, (hsat p).2 (Localization.inverts L _ p hp.mem), hfac⟩ }

end ABCCofibrations.ABCPrecofibrationCategory


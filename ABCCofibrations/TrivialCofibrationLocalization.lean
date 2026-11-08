/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.BrownFunctor
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Localization at trivial cofibrations

On cofibrant objects, a functor inverts all weak equivalences if and only if
it inverts trivial cofibrations. Brown's functor lemma therefore identifies
the two localizations, compatibly with their canonical functors.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [CategoryTheory.Limits.HasInitial C]
  [ABCPrecofibrationCategory C] {D : Type u'} [Category.{v'} D]

/-- The ambient trivial cofibrations restricted to cofibrant objects. -/
def cofibrantTrivialCofibrations : MorphismProperty (CofibrantObject C) :=
  (trivialCofibrations C).inverseImage CofibrantObject.ι

omit [ABCPrecofibrationCategory C] in
/-- Membership is tested on the underlying map in the ambient category. -/
theorem mem_cofibrantTrivialCofibrations_iff {X Y : CofibrantObject C} (f : X ⟶ Y) :
    cofibrantTrivialCofibrations f ↔ Cofibration f.hom ∧ WeakEquivalence f.hom :=
  mem_trivialCofibrations_iff f.hom

omit [ABCPrecofibrationCategory C] in
/-- Restricted trivial cofibrations are weak equivalences. -/
theorem cofibrantTrivialCofibrations_le_weakEquivalences :
    cofibrantTrivialCofibrations (C := C) ≤ weakEquivalences (CofibrantObject C) :=
  fun _ _ _ hf ↦ hf.2

/-- Brown's lemma identifies the functors which invert either class. -/
theorem inverts_weakEquivalences_iff_inverts_trivialCofibrations
    (F : CofibrantObject C ⥤ D) :
    (weakEquivalences (CofibrantObject C)).IsInvertedBy F ↔
      (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F := by
  refine ⟨fun h _ _ f hf ↦ h f hf.2, fun h ↦ ?_⟩
  exact isInvertedBy_of_inverts_trivialCofibrations F
    (fun i hi hw ↦ h i ⟨hi.mem, hw.mem⟩)

/-- The canonical localization at trivial cofibrations also satisfies the
strict universal property for localization at all weak equivalences. -/
noncomputable def trivialCofibrationLocalizationUniversalProperty :
    Localization.StrictUniversalPropertyFixedTarget
      (cofibrantTrivialCofibrations (C := C)).Q
      (weakEquivalences (CofibrantObject C)) D where
  inverts := (inverts_weakEquivalences_iff_inverts_trivialCofibrations _).2
    (cofibrantTrivialCofibrations (C := C)).Q_inverts
  lift F hF := Localization.Construction.lift F
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).1 hF)
  fac _ _ := Localization.Construction.fac _ _
  uniq F₁ F₂ h := Localization.Construction.uniq F₁ F₂ h

/-- Localizing cofibrant objects at trivial cofibrations is a localization
at all weak equivalences as well. -/
instance trivialCofibrationLocalization_isLocalization :
    (cofibrantTrivialCofibrations (C := C)).Q.IsLocalization
      (weakEquivalences (CofibrantObject C)) :=
  Functor.IsLocalization.mk' _ _
    (trivialCofibrationLocalizationUniversalProperty
      (D := (cofibrantTrivialCofibrations (C := C)).Localization))
    (trivialCofibrationLocalizationUniversalProperty
      (D := (weakEquivalences (CofibrantObject C)).Localization))

/-- The canonical equivalence between localization at trivial cofibrations
and localization at all weak equivalences of cofibrant objects. -/
noncomputable def trivialCofibrationLocalizationEquivalence :
    (cofibrantTrivialCofibrations (C := C)).Localization ≌
      (weakEquivalences (CofibrantObject C)).Localization :=
  Localization.uniq (cofibrantTrivialCofibrations (C := C)).Q
    (weakEquivalences (CofibrantObject C)).Q (weakEquivalences (CofibrantObject C))

/-- The equivalence commutes with the canonical localization functors. -/
noncomputable def trivialCofibrationLocalizationEquivalence_fac :
    (cofibrantTrivialCofibrations (C := C)).Q ⋙
      (trivialCofibrationLocalizationEquivalence (C := C)).functor ≅
        (weakEquivalences (CofibrantObject C)).Q :=
  Localization.compUniqFunctor (cofibrantTrivialCofibrations (C := C)).Q
    (weakEquivalences (CofibrantObject C)).Q (weakEquivalences (CofibrantObject C))

end ABCCofibrations.ABCPrecofibrationCategory

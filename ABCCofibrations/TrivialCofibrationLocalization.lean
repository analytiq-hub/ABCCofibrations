/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.BrownFunctor
public import ABCCofibrations.LocalizationTransfer
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

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

/-- Pushing out a trivial cofibration gives the common target needed to
move an inverse past a forward arrow in a localization word. -/
theorem exists_trivialCofibration_ore_square
    {A B X : CofibrantObject C} (s : A ⟶ B) (f : A ⟶ X)
    (hs : cofibrantTrivialCofibrations s) :
    ∃ (Y : CofibrantObject C) (g : B ⟶ Y) (t : X ⟶ Y),
      cofibrantTrivialCofibrations t ∧ s ≫ g = f ≫ t := by
  obtain ⟨hs, hw⟩ := (mem_cofibrantTrivialCofibrations_iff s).1 hs
  let := hs
  let := hw
  let h := IsPushout.of_hasPushout s.hom f.hom
  let := cofibration_of_isPushout h
  let := weakEquivalence_of_isPushout h
  let := cofibrant_target (Limits.pushout.inr s.hom f.hom)
  refine ⟨CofibrantObject.mk (Limits.pushout s.hom f.hom),
    CofibrantObject.homMk (Limits.pushout.inl s.hom f.hom),
    CofibrantObject.homMk (Limits.pushout.inr s.hom f.hom), ?_, ?_⟩
  · apply (mem_cofibrantTrivialCofibrations_iff _).2
    change Cofibration (Limits.pushout.inr s.hom f.hom) ∧
      WeakEquivalence (Limits.pushout.inr s.hom f.hom)
    exact ⟨inferInstance, inferInstance⟩
  · ext
    exact h.w

/-- Every right fraction with a trivial-cofibration denominator can be
converted to a left fraction, using the pushout square. This asserts the
Ore existence condition only, without a cancellation axiom. -/
theorem exists_leftFraction_of_trivialCofibration_rightFraction
    {X Y : CofibrantObject C}
    (φ : (cofibrantTrivialCofibrations (C := C)).RightFraction X Y) :
    ∃ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y,
      φ.f ≫ ψ.s = φ.s ≫ ψ.f := by
  obtain ⟨Z, g, t, ht, h⟩ := exists_trivialCofibration_ore_square φ.s φ.f φ.hs
  exact ⟨⟨g, t, ht⟩, h.symm⟩

/-- Brown's lemma identifies the functors which invert either class. -/
theorem inverts_weakEquivalences_iff_inverts_trivialCofibrations
    (F : CofibrantObject C ⥤ D) :
    (weakEquivalences (CofibrantObject C)).IsInvertedBy F ↔
      (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F := by
  refine ⟨fun h _ _ f hf ↦ h f hf.2, fun h ↦ ?_⟩
  exact isInvertedBy_of_inverts_trivialCofibrations F
    (fun i hi hw ↦ h i ⟨hi.mem, hw.mem⟩)

omit [ABCPrecofibrationCategory C] in
/-- Localization at all weak equivalences inverts the trivial cofibrations. -/
theorem cofibrantTrivialCofibrations_isInvertedBy_weakEquivalences_Q :
    (cofibrantTrivialCofibrations (C := C)).IsInvertedBy
      (weakEquivalences (CofibrantObject C)).Q :=
  MorphismProperty.IsInvertedBy.of_le _ _ _
    (weakEquivalences (CofibrantObject C)).Q_inverts
    cofibrantTrivialCofibrations_le_weakEquivalences

/-- Localization at trivial cofibrations inverts all weak equivalences, by
Brown's lemma. -/
theorem weakEquivalences_isInvertedBy_cofibrantTrivialCofibrations_Q :
    (weakEquivalences (CofibrantObject C)).IsInvertedBy
      (cofibrantTrivialCofibrations (C := C)).Q :=
  (inverts_weakEquivalences_iff_inverts_trivialCofibrations _).2
    (cofibrantTrivialCofibrations (C := C)).Q_inverts

/-- The canonical localization at trivial cofibrations also satisfies the
strict universal property for localization at all weak equivalences. The
two classes have the same inverting functors, so this is an instance of the
shared `Localization.strictUniversalPropertyFixedTargetQOfIsInvertedBy`. -/
noncomputable def trivialCofibrationLocalizationUniversalProperty :
    Localization.StrictUniversalPropertyFixedTarget
      (cofibrantTrivialCofibrations (C := C)).Q
      (weakEquivalences (CofibrantObject C)) D :=
  Localization.strictUniversalPropertyFixedTargetQOfIsInvertedBy
    cofibrantTrivialCofibrations_isInvertedBy_weakEquivalences_Q
    weakEquivalences_isInvertedBy_cofibrantTrivialCofibrations_Q D

/-- Localizing cofibrant objects at trivial cofibrations is a localization
at all weak equivalences as well. -/
instance trivialCofibrationLocalization_isLocalization :
    (cofibrantTrivialCofibrations (C := C)).Q.IsLocalization
      (weakEquivalences (CofibrantObject C)) :=
  Localization.isLocalization_of_isInvertedBy_Q
    cofibrantTrivialCofibrations_isInvertedBy_weakEquivalences_Q
    weakEquivalences_isInvertedBy_cofibrantTrivialCofibrations_Q _

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

/-- Any localization at weak equivalences is also a localization at
trivial cofibrations, by Brown's lemma and the shared same-inverting-classes
transfer. -/
theorem isLocalization_trivialCofibrations_of_weakEquivalences
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences (CofibrantObject C))] :
    L.IsLocalization (cofibrantTrivialCofibrations (C := C)) :=
  Localization.isLocalization_of_isInvertedBy_Q
    weakEquivalences_isInvertedBy_cofibrantTrivialCofibrations_Q
    cofibrantTrivialCofibrations_isInvertedBy_weakEquivalences_Q L

end ABCCofibrations.ABCPrecofibrationCategory

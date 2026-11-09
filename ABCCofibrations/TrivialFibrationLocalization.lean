/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.BrownFibration
public import ABCCofibrations.LocalizationTransfer
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Localization at trivial fibrations

On fibrant objects, a functor inverts all weak equivalences if and only if
it inverts trivial fibrations. Brown's functor lemma therefore identifies
the two localizations, compatibly with their canonical functors.

The pullback square below is the existence half of a right calculus for
trivial fibrations. It does not include a cancellation axiom.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- The ambient trivial fibrations restricted to fibrant objects. -/
def fibrantTrivialFibrations : MorphismProperty (FibrantObject C) :=
  (trivialFibrations C).inverseImage FibrantObject.ι

omit [ABCPrefibrationCategory C] in
/-- Membership is tested on the underlying map in the ambient category. -/
theorem mem_fibrantTrivialFibrations_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    fibrantTrivialFibrations f ↔ Fibration f.hom ∧ WeakEquivalence f.hom :=
  mem_trivialFibrations_iff f.hom

omit [ABCPrefibrationCategory C] in
/-- Restricted trivial fibrations are weak equivalences. -/
theorem fibrantTrivialFibrations_le_weakEquivalences :
    fibrantTrivialFibrations (C := C) ≤ weakEquivalences (FibrantObject C) :=
  fun _ _ _ hf ↦ hf.2

/-- Pulling back a trivial fibration gives the common source needed to
move an inverse past a backward arrow in a localization word. -/
theorem exists_trivialFibration_ore_square
    {A B X : FibrantObject C} (t : B ⟶ A) (f : X ⟶ A)
    (ht : fibrantTrivialFibrations t) :
    ∃ (Y : FibrantObject C) (g : Y ⟶ B) (s : Y ⟶ X),
      fibrantTrivialFibrations s ∧ s ≫ f = g ≫ t := by
  obtain ⟨htf, htw⟩ := (mem_fibrantTrivialFibrations_iff t).1 ht
  let : Fibration t := ⟨htf.mem⟩
  let : WeakEquivalence t.hom := htw
  obtain ⟨Y, g, s, h, hhom⟩ := exists_fibrant_pullback t f
  have hs : Fibration s.hom := fibration_of_isPullback hhom
  have hsw : WeakEquivalence s.hom := weakEquivalence_of_isPullback hhom
  exact ⟨Y, g, s, (mem_fibrantTrivialFibrations_iff s).2 ⟨hs, hsw⟩, h.w.symm⟩

/-- Every left fraction with a trivial-fibration denominator can be
converted to a right fraction, using the pullback square. This asserts the
Ore existence condition only, without a cancellation axiom. -/
theorem exists_rightFraction_of_trivialFibration_leftFraction
    {X Y : FibrantObject C}
    (φ : (fibrantTrivialFibrations (C := C)).LeftFraction X Y) :
    ∃ ψ : (fibrantTrivialFibrations (C := C)).RightFraction X Y,
      ψ.s ≫ φ.f = ψ.f ≫ φ.s := by
  obtain ⟨Z, g, s, hs, h⟩ := exists_trivialFibration_ore_square φ.s φ.f φ.hs
  exact ⟨⟨s, hs, g⟩, h⟩

/-- Brown's lemma identifies the functors which invert either class. -/
theorem inverts_weakEquivalences_iff_inverts_trivialFibrations
    (F : FibrantObject C ⥤ D) :
    (weakEquivalences (FibrantObject C)).IsInvertedBy F ↔
      (fibrantTrivialFibrations (C := C)).IsInvertedBy F := by
  refine ⟨fun h _ _ f hf ↦ h f hf.2, fun h ↦ ?_⟩
  exact isInvertedBy_of_inverts_trivialFibrations F
    (fun p hp hw ↦ h p ⟨hp.mem, hw.mem⟩)

omit [ABCPrefibrationCategory C] in
/-- Localization at all weak equivalences inverts the trivial fibrations. -/
theorem fibrantTrivialFibrations_isInvertedBy_weakEquivalences_Q :
    (fibrantTrivialFibrations (C := C)).IsInvertedBy
      (weakEquivalences (FibrantObject C)).Q :=
  MorphismProperty.IsInvertedBy.of_le _ _ _
    (weakEquivalences (FibrantObject C)).Q_inverts
    fibrantTrivialFibrations_le_weakEquivalences

/-- Localization at trivial fibrations inverts all weak equivalences, by
Brown's lemma. -/
theorem weakEquivalences_isInvertedBy_fibrantTrivialFibrations_Q :
    (weakEquivalences (FibrantObject C)).IsInvertedBy
      (fibrantTrivialFibrations (C := C)).Q :=
  (inverts_weakEquivalences_iff_inverts_trivialFibrations _).2
    (fibrantTrivialFibrations (C := C)).Q_inverts

/-- The canonical localization at trivial fibrations also satisfies the
strict universal property for localization at all weak equivalences. The
two classes have the same inverting functors, so this is an instance of the
shared `Localization.strictUniversalPropertyFixedTargetQOfIsInvertedBy`. -/
noncomputable def trivialFibrationLocalizationUniversalProperty :
    Localization.StrictUniversalPropertyFixedTarget
      (fibrantTrivialFibrations (C := C)).Q
      (weakEquivalences (FibrantObject C)) D :=
  Localization.strictUniversalPropertyFixedTargetQOfIsInvertedBy
    fibrantTrivialFibrations_isInvertedBy_weakEquivalences_Q
    weakEquivalences_isInvertedBy_fibrantTrivialFibrations_Q D

/-- Localizing fibrant objects at trivial fibrations is a localization
at all weak equivalences as well. -/
instance trivialFibrationLocalization_isLocalization :
    (fibrantTrivialFibrations (C := C)).Q.IsLocalization
      (weakEquivalences (FibrantObject C)) :=
  Localization.isLocalization_of_isInvertedBy_Q
    fibrantTrivialFibrations_isInvertedBy_weakEquivalences_Q
    weakEquivalences_isInvertedBy_fibrantTrivialFibrations_Q _

/-- The canonical equivalence between localization at trivial fibrations
and localization at all weak equivalences of fibrant objects. -/
noncomputable def trivialFibrationLocalizationEquivalence :
    (fibrantTrivialFibrations (C := C)).Localization ≌
      (weakEquivalences (FibrantObject C)).Localization :=
  Localization.uniq (fibrantTrivialFibrations (C := C)).Q
    (weakEquivalences (FibrantObject C)).Q (weakEquivalences (FibrantObject C))

/-- The equivalence commutes with the canonical localization functors. -/
noncomputable def trivialFibrationLocalizationEquivalence_fac :
    (fibrantTrivialFibrations (C := C)).Q ⋙
      (trivialFibrationLocalizationEquivalence (C := C)).functor ≅
        (weakEquivalences (FibrantObject C)).Q :=
  Localization.compUniqFunctor (fibrantTrivialFibrations (C := C)).Q
    (weakEquivalences (FibrantObject C)).Q (weakEquivalences (FibrantObject C))

/-- Any localization at weak equivalences is also a localization at
trivial fibrations, by Brown's lemma and the shared same-inverting-classes
transfer. -/
theorem isLocalization_trivialFibrations_of_weakEquivalences
    (L : FibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences (FibrantObject C))] :
    L.IsLocalization (fibrantTrivialFibrations (C := C)) :=
  Localization.isLocalization_of_isInvertedBy_Q
    weakEquivalences_isInvertedBy_fibrantTrivialFibrations_Q
    fibrantTrivialFibrations_isInvertedBy_weakEquivalences_Q L

end ABCCofibrations.ABCPrefibrationCategory

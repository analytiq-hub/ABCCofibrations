/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.DerivedFunctorComparison

/-!
# Derived equivalences from the cofibrant restriction

Brown's lemma packages the cofibrant restriction as a localizer morphism.
Any total left derived functor is an equivalence exactly when this localizer
morphism is a localized equivalence. This supplies the categorical implication
used in Theorem 6.2.3(1); the general structural cofibrant-approximation
hypothesis of that theorem remains to be treated.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {E : Type u'} [Category.{v'} E] [CategoryWithWeakEquivalences E]

omit [ABCPrecofibrationCategory C] in
/-- After target localization, preservation of trivial cofibrations as weak
equivalences becomes inversion of those maps. -/
theorem inverts_cofibrant_trivialCofibrations_after_localization
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i))
    {H : Type*} [Category H] (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso ((F ⋙ R).map i.hom) := by
  intro X Y i hi hw
  let := hi
  let := hw
  exact Localization.inverts R (weakEquivalences E) (F.map i.hom) (hF i.hom).mem

variable [(weakEquivalences E).HasTwoOutOfThreeProperty]

/-- Brown's lemma makes the cofibrant restriction a morphism of localizers.
No preservation of weak equivalences with noncofibrant endpoints is assumed. -/
def cofibrantRestrictionLocalizerMorphism
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i)) :
    LocalizerMorphism (weakEquivalences (CofibrantObject C)) (weakEquivalences E) where
  functor := CofibrantObject.ι ⋙ F
  map X Y f hf := by
    let : WeakEquivalence f.hom := ⟨hf⟩
    exact (map_weakEquivalence_of_map_trivialCofibrations F hF f.hom).mem

/-- A total left derived functor is an equivalence if and only if the
cofibrant restriction is a localized equivalence. The statement is independent
of the choices of source and target localizations. -/
theorem isEquivalence_totalLeftDerivedFunctor_iff_localized_cofibrantRestriction
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i))
    {D H : Type*} [Category D] [Category H]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)]
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F ⋙ R)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)] :
    LF.IsEquivalence ↔ (cofibrantRestrictionLocalizerMorphism F hF).IsLocalizedEquivalence := by
  let Φ := cofibrantRestrictionLocalizerMorphism F hF
  let Q := (weakEquivalences (CofibrantObject C)).Q
  let hFR : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso ((F ⋙ R).map i.hom) :=
    inverts_cofibrant_trivialCofibrations_after_localization F hF R
  rw [isEquivalence_leftDerivedFunctor_iff_cofibrantRestrictionLift (F ⋙ R) hFR L LF ε]
  change (Φ.localizedFunctor Q R).IsEquivalence ↔ Φ.IsLocalizedEquivalence
  constructor
  · intro h
    let := h
    exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ Q R (Φ.localizedFunctor Q R)
  · intro h
    let := h
    infer_instance

/-- Existence of a total left derived equivalence from a localized equivalence
on the cofibrant restriction. Its counit is invertible at cofibrant objects. -/
theorem exists_totalLeftDerivedEquivalence_of_localized_cofibrantRestriction
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i))
    [(cofibrantRestrictionLocalizerMorphism F hF).IsLocalizedEquivalence]
    {D H : Type*} [Category D] [Category H]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F ⋙ R),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧ LF.IsEquivalence ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  obtain ⟨LF, ε, hLF, hε⟩ :=
    exists_totalLeftDerivedFunctor_of_map_trivialCofibrations F hF L R
  let := hLF
  exact ⟨LF, ε, hLF,
    (isEquivalence_totalLeftDerivedFunctor_iff_localized_cofibrantRestriction
      F hF L R LF ε).2 inferInstance, hε⟩

end ABCCofibrations.ABCPrecofibrationCategory

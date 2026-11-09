/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantSubcategory
public import ABCCofibrations.CofibrantApproximationDerived
public import ABCCofibrations.DerivedEquivalence

/-!
# Total derived equivalences from cofibrant approximations

Theorem 6.2.3(1), with the approximation hypothesis on the restriction to
cofibrant objects. No weak-equivalence preservation on other objects is assumed.
-/

@[expose] public section

universe v u v' u'
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {E : Type u'} [Category.{v'} E] [CategoryWithCofibrations E]
  [CategoryWithWeakEquivalences E] [HasInitial E] [ABCPrecofibrationCategory E]
  (F : C ⥤ E) [IsCofibrantApproximation (CofibrantObject.ι ⋙ F)]

/-- The structural approximation hypothesis implies the preservation condition
used by the earlier derived-equivalence criterion. -/
theorem map_trivialCofibration_of_cofibrantApproximation
    {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence (F.map i) := by
  let := cofibrant_target i
  let : WeakEquivalence (CofibrantObject.homMk i) :=
    ⟨(show WeakEquivalence i from inferInstance).mem⟩
  exact IsCofibrantApproximation.map_weakEquivalence (CofibrantObject.ι ⋙ F)
    (CofibrantObject.homMk i)

/-- Any total left derived functor of a functor whose cofibrant restriction
is an approximation is an equivalence. -/
theorem isEquivalence_totalLeftDerivedFunctor_of_cofibrantApproximation
    {D H : Type*} [Category D] [Category H]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)]
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F ⋙ R)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)] : LF.IsEquivalence := by
  apply (isEquivalence_totalLeftDerivedFunctor_iff_localized_cofibrantRestriction
    F (map_trivialCofibration_of_cofibrantApproximation F) L R LF ε).2
  change (IsCofibrantApproximation.toLocalizerMorphism
    (CofibrantObject.ι ⋙ F)).IsLocalizedEquivalence
  infer_instance

/-- Theorem 6.2.3(1): existence of a total left derived equivalence, with
invertible counit on all cofibrant objects. -/
theorem exists_totalLeftDerivedEquivalence_of_cofibrantApproximation
    {D H : Type*} [Category D] [Category H]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F ⋙ R),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧ LF.IsEquivalence ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  obtain ⟨LF, ε, hLF, hε⟩ := exists_totalLeftDerivedFunctor_of_map_trivialCofibrations
    F (map_trivialCofibration_of_cofibrantApproximation F) L R
  let := hLF
  exact ⟨LF, ε, hLF,
    isEquivalence_totalLeftDerivedFunctor_of_cofibrantApproximation F L R LF ε, hε⟩

end ABCCofibrations.ABCPrecofibrationCategory

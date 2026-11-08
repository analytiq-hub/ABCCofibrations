/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.DerivedFunctor

/-!
# Derived functors and the localized cofibrant restriction

An arbitrary left derived functor agrees, after the cofibrant localization
comparison, with the localization lift of the original functor's restriction.
Consequently it is an equivalence exactly when that lift is an equivalence.
This is the categorical step in Theorem 6.2.3(1), without yet formalizing its
general cofibrant-approximation hypothesis.
-/

@[expose] public section

universe v u v' u' v'' u''

open CategoryTheory Limits HomotopicalAlgebra CategoryTheory.Functor

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {H : Type u'} [Category.{v'} H]

/-- Localization lift of a functor's restriction to cofibrant objects.
Brown's lemma supplies inversion of weak equivalences on that restriction. -/
noncomputable def cofibrantRestrictionLift (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom)) :
    (weakEquivalences (CofibrantObject C)).Localization ⥤ H :=
  Localization.lift (CofibrantObject.ι ⋙ F)
    (isInvertedBy_of_inverts_trivialCofibrations (CofibrantObject.ι ⋙ F) hF)
    (weakEquivalences (CofibrantObject C)).Q

section

variable (F : C ⥤ H)
  (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
    Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
  {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
  [L.IsLocalization (weakEquivalences C)]

/-- The derived functor composed with the cofibrant localization comparison
is naturally isomorphic to the lifted cofibrant restriction. -/
noncomputable def leftDerivedFunctorCofibrantRestrictionIso
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)] :
    (cofibrantInclusionLocalizerMorphism (C := C)).localizedFunctor
        (weakEquivalences (CofibrantObject C)).Q L ⋙ LF ≅ cofibrantRestrictionLift F hF := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let Q := (weakEquivalences (CofibrantObject C)).Q
  let hW := isInvertedBy_of_inverts_trivialCofibrations (Φ.functor ⋙ F) hF
  let F₁ := Localization.lift (Φ.functor ⋙ F) hW Q
  let ε₁ := (Localization.fac (Φ.functor ⋙ F) hW Q).hom
  let : Φ.IsLeftDerivabilityStructure :=
    inferInstanceAs (cofibrantInclusionLocalizerMorphism (C := C)).IsLeftDerivabilityStructure
  let : F₁.IsLeftDerivedFunctor ε₁ (weakEquivalences (CofibrantObject C)) :=
    inferInstanceAs ((Localization.lift (Φ.functor ⋙ F) hW Q).IsLeftDerivedFunctor
      (Localization.fac (Φ.functor ⋙ F) hW Q).hom (weakEquivalences (CofibrantObject C)))
  let : (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor
      (weakEquivalences (CofibrantObject C)) :=
    Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW
  have hI : IsIso (Φ.leftDerivedFunctorComparison Q L F F₁ ε₁ LF ε) :=
    LocalizerMorphism.instIsIsoFunctorLeftDerivedFunctorComparison Φ Q L F F₁ ε₁ LF ε
  exact @CategoryTheory.asIso _ _ _ _ (Φ.leftDerivedFunctorComparison Q L F F₁ ε₁ LF ε) hI

/-- A left derived functor is an equivalence exactly when the lifted
cofibrant restriction is an equivalence. -/
theorem isEquivalence_leftDerivedFunctor_iff_cofibrantRestrictionLift
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)] :
    LF.IsEquivalence ↔ (cofibrantRestrictionLift F hF).IsEquivalence := by
  let K := (cofibrantInclusionLocalizerMorphism (C := C)).localizedFunctor
    (weakEquivalences (CofibrantObject C)).Q L
  let e := leftDerivedFunctorCofibrantRestrictionIso F hF L LF ε
  constructor
  · intro h
    let := h
    exact Functor.isEquivalence_of_iso e
  · intro h
    let := h
    let : (K ⋙ LF).IsEquivalence := Functor.isEquivalence_of_iso e.symm
    exact Functor.isEquivalence_of_comp_left K LF

end

/-- A criterion for existence of a derived equivalence, with its counit
invertible on cofibrant objects. The criterion is on the localized restriction. -/
theorem exists_leftDerivedEquivalence_of_cofibrantRestrictionLift
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
    [(cofibrantRestrictionLift F hF).IsEquivalence]
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧ LF.IsEquivalence ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  obtain ⟨LF, ε, hLF, hε⟩ :=
    exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations F hF L
  let := hLF
  exact ⟨LF, ε, hLF,
    (isEquivalence_leftDerivedFunctor_iff_cofibrantRestrictionLift F hF L LF ε).2
      inferInstance, hε⟩

/-- With explicit replacement choices, any left derived functor is naturally
isomorphic to the reverse localization functor followed by the lifted
cofibrant restriction. -/
noncomputable def leftDerivedFunctorIsoViaReplacements
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
    (LF : (weakEquivalences C).Localization ⥤ H)
    (ε : (weakEquivalences C).Q ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)]
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A)) :
    LF ≅ ambientLocalizationToCofibrant Q q hq ⋙ cofibrantRestrictionLift F hF :=
  (Functor.leftUnitor LF).symm ≪≫
    isoWhiskerRight (ambientLocalizationReplacementIso Q q hq).symm LF ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (ambientLocalizationToCofibrant Q q hq)
      (leftDerivedFunctorCofibrantRestrictionIso F hF (weakEquivalences C).Q LF ε)

end ABCCofibrations.ABCPrecofibrationCategory

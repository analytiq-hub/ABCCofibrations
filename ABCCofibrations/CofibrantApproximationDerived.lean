/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximationLocalization
public import ABCCofibrations.DerivedFunctor

/-!
# Derived functors computed by general cofibrant approximations

Theorem 6.2.2(1): it suffices that the composite with an approximation
sends trivial cofibrations to weak equivalences. No preservation assumption
on other cofibrant objects of the ambient category is needed.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.IsCofibrantApproximation

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D] [ABCPrecofibrationCategory D]
  (F : C ⥤ D) [IsCofibrantApproximation F]

include F in
/-- Brown's lemma on the all-cofibrant source, with an arbitrary target
category: inversion of trivial cofibrations implies inversion of all weak
equivalences. -/
theorem inverts_of_inverts_trivialCofibrations
    {H : Type*} [Category H] (G : C ⥤ H)
    (hG : ∀ {A B : C} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i],
      IsIso (G.map i)) : (weakEquivalences C).IsInvertedBy G := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  have h := isInvertedBy_of_inverts_trivialCofibrations (CofibrantObject.ι ⋙ G)
    (fun i hi hw ↦ by
      let := hi
      let := hw
      exact hG i.hom)
  intro A B f hf
  exact h (CofibrantObject.homMk f) hf

/-- A functor has a pointwise left derived functor if its composite with a
cofibrant approximation inverts trivial cofibrations. -/
theorem hasPointwiseLeftDerivedFunctor_of_inverts_trivialCofibrations
    {H : Type*} [Category H] (U : D ⥤ H)
    (hU : ∀ {A B : C} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i],
      IsIso (U.map (F.map i))) : U.HasPointwiseLeftDerivedFunctor (weakEquivalences D) := by
  let Φ := toLocalizerMorphism F
  have hW : (weakEquivalences C).IsInvertedBy (Φ.functor ⋙ U) :=
    inverts_of_inverts_trivialCofibrations F (F ⋙ U) hU
  exact (Φ.hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure U).2
    (Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW)

/-- For any left derived functor, the counit is invertible on objects in the
image of the approximation. -/
theorem isIso_leftDerivedCounit_app
    {H : Type*} [Category H] (U : D ⥤ H)
    (hU : ∀ {A B : C} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i],
      IsIso (U.map (F.map i)))
    {E : Type*} [Category E] (L : D ⥤ E) [L.IsLocalization (weakEquivalences D)]
    (LU : E ⥤ H) (ε : L ⋙ LU ⟶ U)
    [LU.IsLeftDerivedFunctor ε (weakEquivalences D)] (A : C) :
    IsIso (ε.app (F.obj A)) := by
  let Φ := toLocalizerMorphism F
  let Q := (weakEquivalences C).Q
  have hW : (weakEquivalences C).IsInvertedBy (Φ.functor ⋙ U) :=
    inverts_of_inverts_trivialCofibrations F (F ⋙ U) hU
  let : (Φ.functor ⋙ U).HasPointwiseLeftDerivedFunctor (weakEquivalences C) :=
    Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW
  let U₁ := Localization.lift (Φ.functor ⋙ U) hW Q
  let ε₁ := (Localization.fac (Φ.functor ⋙ U) hW Q).hom
  exact (Φ.isIso_iff_of_isLeftDerivabilityStructure Q L U U₁ ε₁ LU ε A).1
    (by infer_instance)

/-- Existence and the counit computation, for any source localization and
an arbitrary target category. -/
theorem exists_leftDerivedFunctor_of_inverts_trivialCofibrations
    {H : Type*} [Category H] (U : D ⥤ H)
    (hU : ∀ {A B : C} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i],
      IsIso (U.map (F.map i)))
    {E : Type*} [Category E] (L : D ⥤ E) [L.IsLocalization (weakEquivalences D)] :
    ∃ (LU : E ⥤ H) (ε : L ⋙ LU ⟶ U),
      LU.IsLeftDerivedFunctor ε (weakEquivalences D) ∧
        ∀ A : C, IsIso (ε.app (F.obj A)) := by
  let := hasPointwiseLeftDerivedFunctor_of_inverts_trivialCofibrations F U hU
  let LU := U.totalLeftDerived L (weakEquivalences D)
  let ε := U.totalLeftDerivedCounit L (weakEquivalences D)
  exact ⟨LU, ε, inferInstance, fun A ↦ isIso_leftDerivedCounit_app F U hU L LU ε A⟩

/-- Theorem 6.2.2(1). The target has only a designated weak-equivalence class;
no two-out-of-three or saturation assumption on that class is required. -/
theorem exists_totalLeftDerivedFunctor_of_map_trivialCofibrations
    {M H : Type*} [Category M] [CategoryWithWeakEquivalences M] [Category H]
    (U : D ⥤ M)
    (hU : ∀ {A B : C} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i],
      WeakEquivalence (U.map (F.map i)))
    {E : Type*} [Category E] (L : D ⥤ E) [L.IsLocalization (weakEquivalences D)]
    (R : M ⥤ H) [R.IsLocalization (weakEquivalences M)] :
    ∃ (LU : E ⥤ H) (ε : L ⋙ LU ⟶ U ⋙ R),
      LU.IsLeftDerivedFunctor ε (weakEquivalences D) ∧
        ∀ A : C, IsIso (ε.app (F.obj A)) := by
  apply exists_leftDerivedFunctor_of_inverts_trivialCofibrations F (U ⋙ R) ?_ L
  intro A B i _ _
  exact Localization.inverts R (weakEquivalences M) (U.map (F.map i)) (hU i).mem

end ABCCofibrations.IsCofibrantApproximation

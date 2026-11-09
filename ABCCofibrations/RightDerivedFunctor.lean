/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrantSubcategory

/-!
# Right derived functors and equivalences

Theorems 6.2.1(2) and 6.2.3(2), using the fibrant inclusion and general
fibrant approximations. All prefibration assumptions are F1–F4.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- Theorem 6.2.1(2), with arbitrary source and target localizations. -/
theorem exists_totalRightDerivedFunctor_of_map_trivialFibrations
    {E D H : Type*} [Category E] [CategoryWithWeakEquivalences E] [Category D] [Category H]
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (p : X ⟶ Y) [IsFibrant Y] [Fibration p] [WeakEquivalence p],
      WeakEquivalence (F.map p))
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∃ (RF : D ⥤ H) (η : F ⋙ R ⟶ L ⋙ RF),
      RF.IsRightDerivedFunctor η (weakEquivalences C) ∧
        ∀ (A : C) [IsFibrant A], IsIso (η.app A) := by
  obtain ⟨RF, η, hRF, hη⟩ :=
    IsFibrantApproximation.exists_totalRightDerivedFunctor_of_map_trivialFibrations
      (FibrantObject.ι (C := C)) F (fun p ↦ hF p.hom) L R
  exact ⟨RF, η, hRF, fun A _ ↦ hη (FibrantObject.mk A)⟩

/-- Every total right derived unit is invertible at fibrant objects, not
only the unit produced by the existence theorem. -/
theorem isIso_totalRightDerivedUnit_app_fibrant
    {E D H : Type*} [Category E] [CategoryWithWeakEquivalences E] [Category D] [Category H]
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (p : X ⟶ Y) [IsFibrant Y] [Fibration p] [WeakEquivalence p],
      WeakEquivalence (F.map p))
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)]
    (RF : D ⥤ H) (η : F ⋙ R ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor η (weakEquivalences C)]
    (A : C) [IsFibrant A] : IsIso (η.app A) := by
  apply IsFibrantApproximation.isIso_rightDerivedUnit_app
    (FibrantObject.ι (C := C)) (F ⋙ R) ?_ L RF η (FibrantObject.mk A)
  intro X Y p _ hw
  let : WeakEquivalence p.hom := ⟨hw.mem⟩
  exact Localization.inverts R (weakEquivalences E) (F.map p.hom) (hF p.hom).mem

section Equivalence

variable {E : Type*} [Category E] [CategoryWithFibrations E]
  [CategoryWithWeakEquivalences E] [HasTerminal E] [ABCPrefibrationCategory E]
  (F : C ⥤ E) [IsFibrantApproximation (FibrantObject.ι ⋙ F)]

/-- The structural approximation hypothesis implies preservation of trivial
fibrations between fibrant objects. -/
theorem map_trivialFibration_of_fibrantApproximation
    {X Y : C} (p : X ⟶ Y) [IsFibrant Y] [Fibration p] [WeakEquivalence p] :
    WeakEquivalence (F.map p) := by
  let := fibrant_source p
  let : WeakEquivalence (FibrantObject.homMk p) :=
    ⟨(show WeakEquivalence p from inferInstance).mem⟩
  exact IsFibrantApproximation.map_weakEquivalence (FibrantObject.ι ⋙ F)
    (FibrantObject.homMk p)

/-- Every total right derived functor is an equivalence under the structural
hypothesis of Theorem 6.2.3(2). -/
theorem isEquivalence_totalRightDerivedFunctor_of_fibrantApproximation
    {D H : Type*} [Category D] [Category H]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)]
    (RF : D ⥤ H) (η : F ⋙ R ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor η (weakEquivalences C)] : RF.IsEquivalence := by
  let Φ := IsFibrantApproximation.toLocalizerMorphism (FibrantObject.ι (C := C))
  let Ψ := IsFibrantApproximation.toLocalizerMorphism (FibrantObject.ι ⋙ F)
  let Q := (weakEquivalences (FibrantObject C)).Q
  have hW : (weakEquivalences (FibrantObject C)).IsInvertedBy (Φ.functor ⋙ (F ⋙ R)) := by
    intro X Y p hp
    let : WeakEquivalence p := ⟨hp⟩
    exact Localization.inverts R (weakEquivalences E) (F.map p.hom)
      (IsFibrantApproximation.map_weakEquivalence (FibrantObject.ι ⋙ F) p).mem
  let F₁ := Localization.lift (Φ.functor ⋙ (F ⋙ R)) hW Q
  let η₁ := (Localization.fac (Φ.functor ⋙ (F ⋙ R)) hW Q).inv
  let : (Φ.functor ⋙ (F ⋙ R)).HasPointwiseRightDerivedFunctor
      (weakEquivalences (FibrantObject C)) :=
    Functor.hasPointwiseRightDerivedFunctor_of_inverts _ hW
  have hI : IsIso (Φ.rightDerivedFunctorComparison Q L (F ⋙ R) F₁ η₁ RF η) :=
    LocalizerMorphism.instIsIsoFunctorRightDerivedFunctorComparison Φ Q L (F ⋙ R) F₁ η₁ RF η
  let e := @CategoryTheory.asIso _ _ _ _
    (Φ.rightDerivedFunctorComparison Q L (F ⋙ R) F₁ η₁ RF η) hI
  let : CatCommSq Ψ.functor Q R F₁ := ⟨(Localization.fac _ hW Q).symm⟩
  let : F₁.IsEquivalence := Ψ.isEquivalence Q R F₁
  let K := Φ.localizedFunctor Q L
  let : K.IsEquivalence := inferInstance
  let : (K ⋙ RF).IsEquivalence := Functor.isEquivalence_of_iso e
  exact Functor.isEquivalence_of_comp_left K RF

/-- Theorem 6.2.3(2): a total right derived equivalence exists, and its unit
is invertible on fibrant objects. -/
theorem exists_totalRightDerivedEquivalence_of_fibrantApproximation
    {D H : Type*} [Category D] [Category H]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∃ (RF : D ⥤ H) (η : F ⋙ R ⟶ L ⋙ RF),
      RF.IsRightDerivedFunctor η (weakEquivalences C) ∧ RF.IsEquivalence ∧
        ∀ (A : C) [IsFibrant A], IsIso (η.app A) := by
  obtain ⟨RF, η, hRF, hη⟩ := exists_totalRightDerivedFunctor_of_map_trivialFibrations
    F (map_trivialFibration_of_fibrantApproximation F) L R
  let := hRF
  exact ⟨RF, η, hRF,
    isEquivalence_totalRightDerivedFunctor_of_fibrantApproximation F L R RF η, hη⟩

end Equivalence
end ABCCofibrations.ABCPrefibrationCategory

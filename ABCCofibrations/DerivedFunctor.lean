/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReplacementComparison
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseLeftDerived

/-!
# Total left derived functors under CF1–CF4

Inclusion of cofibrant objects is a left derivability structure in mathlib's
sense. Thus a functor inverting trivial cofibrations between cofibrant objects
has a pointwise left derived functor, whose counit is invertible on cofibrant
objects. Applying this to a functor followed by target localization gives
Theorem 6.2.1(1). Unlike the paper's proof via general approximation functors,
we use mathlib's derivability-structure constructor for this inclusion.
-/

@[expose] public section

universe v u v' u' v'' u''

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The cofibrant inclusion is a left derivability structure. The required
connected replacement categories and arrow resolutions were proved under CF1–CF4. -/
instance cofibrantInclusion_isLeftDerivabilityStructure :
    (cofibrantInclusionLocalizerMorphism (C := C)).IsLeftDerivabilityStructure := by
  let : (weakEquivalences C).ContainsIdentities :=
    ⟨fun X ↦ (weakEquivalence_of_isIso (𝟙 X)).mem⟩
  exact LocalizerMorphism.IsLeftDerivabilityStructure.mk' _

variable {H : Type u'} [Category.{v'} H]

/-- Inversion of trivial cofibrations on cofibrant objects suffices for
existence of a pointwise left derived functor. -/
theorem hasPointwiseLeftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom)) :
    F.HasPointwiseLeftDerivedFunctor (weakEquivalences C) := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  have hW : (weakEquivalences (CofibrantObject C)).IsInvertedBy (Φ.functor ⋙ F) :=
    isInvertedBy_of_inverts_trivialCofibrations (Φ.functor ⋙ F) hF
  exact (Φ.hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure F).2
    (Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW)

/-- Every left derived functor of such a functor has invertible counit at
cofibrant objects. This applies to any choice of source localization. -/
theorem isIso_leftDerivedCounit_app_cofibrant
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)]
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)]
    (A : C) [IsCofibrant A] : IsIso (ε.app A) := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let Q := (weakEquivalences (CofibrantObject C)).Q
  let hW : (weakEquivalences (CofibrantObject C)).IsInvertedBy (Φ.functor ⋙ F) :=
    isInvertedBy_of_inverts_trivialCofibrations (Φ.functor ⋙ F) hF
  let : (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor
      (weakEquivalences (CofibrantObject C)) :=
    Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW
  let F₁ := Localization.lift (Φ.functor ⋙ F) hW Q
  let ε₁ := (Localization.fac (Φ.functor ⋙ F) hW Q).hom
  exact (Φ.isIso_iff_of_isLeftDerivabilityStructure Q L F F₁ ε₁ LF ε
    (CofibrantObject.mk A)).1 (by infer_instance)

/-- Existence and cofibrant counit property, with an arbitrary source
localization and an arbitrary target category. -/
theorem exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  let := hasPointwiseLeftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations F hF
  let LF := F.totalLeftDerived L (weakEquivalences C)
  let ε := F.totalLeftDerivedCounit L (weakEquivalences C)
  exact ⟨LF, ε, inferInstance, fun A _ ↦ isIso_leftDerivedCounit_app_cofibrant F hF L LF ε A⟩

/-- Theorem 6.2.1(1): a functor preserving trivial cofibrations between
cofibrant objects as weak equivalences admits a total left derived functor.
The target needs only a designated weak-equivalence class and its localization. -/
theorem exists_totalLeftDerivedFunctor_of_map_trivialCofibrations
    {E : Type*} [Category E] [CategoryWithWeakEquivalences E]
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i))
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F ⋙ R),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  apply exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations (F ⋙ R) ?_ L
  intro X Y i hi hw
  let := hi
  let := hw
  exact Localization.inverts R (weakEquivalences E) (F.map i.hom) (hF i.hom).mem

end ABCCofibrations.ABCPrecofibrationCategory

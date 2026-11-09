/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximationFractions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# Localization comparison for cofibrant approximations

The inverse localization construction of Theorem 6.1.7(1), with arbitrary
choices of object resolutions and no functorial factorization assumption.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra CategoryTheory.Functor

namespace ABCCofibrations.IsCofibrantApproximation

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D] [ABCPrecofibrationCategory D]
  (F : C ⥤ D) [IsCofibrantApproximation F]
  (Q : D → C) (q : ∀ A, F.obj (Q A) ⟶ A) [∀ A, WeakEquivalence (q A)]

/-- The functor in the reverse direction on localizations. -/
noncomputable def localizationInverse :
    (weakEquivalences D).Localization ⥤ (weakEquivalences C).Localization :=
  Localization.lift
    (resolutionFunctor F Q q (weakEquivalences C).Q (weakEquivalences C).Q_inverts)
    (resolutionFunctor_inverts F Q q (weakEquivalences C).Q
      (weakEquivalences C).Q_inverts) (weakEquivalences D).Q

/-- Restricting the resolution functor along the approximation recovers the
original weak-equivalence-inverting functor, up to natural isomorphism. -/
noncomputable def resolutionFunctorRestrictionIso
    {E : Type*} [Category E] (G : C ⥤ E)
    (hG : (weakEquivalences C).IsInvertedBy G) :
    F ⋙ resolutionFunctor F Q q G hG ≅ G := by
  letI (A : D) : WeakEquivalence (𝟙 A) :=
    ABCPrecofibrationCategory.weakEquivalence_of_isIso (𝟙 A)
  let β (A : C) := Classical.choice
    (ResolutionFraction.nonempty F (q (F.obj A)) (𝟙 (F.obj A)) (𝟙 (F.obj A)))
  refine NatIso.ofComponents (fun A ↦
    @CategoryTheory.asIso E _ _ _ ((β A).map G hG)
      ((β A).isIso_map_of_weakEquivalence G hG)) ?_
  intro A B f
  let φ := Classical.choice (ResolutionFraction.nonempty F
    (q (F.obj A)) (q (F.obj B)) (F.map f))
  let δ := Classical.choice (ResolutionFraction.nonempty F
    (𝟙 (F.obj A)) (𝟙 (F.obj B)) (F.map f))
  have he : (φ.comp (β B)).map G hG = ((β A).comp δ).map G hG := by
    apply fraction_map_eq_of_ambient_comparison F
      (φ.comp (β B)).fraction ((β A).comp δ).fraction
      (φ.comp (β B)).comparison ((β A).comp δ).comparison
    · calc
        _ = q (F.obj A) ≫ F.map f := by simpa using (φ.comp (β B)).numerator
        _ = _ := by simpa using ((β A).comp δ).numerator.symm
    · exact (φ.comp (β B)).denominator.trans (((β A).comp δ).denominator.symm)
  change φ.map G hG ≫ (β B).map G hG = (β A).map G hG ≫ G.map f
  rw [← φ.map_comp (β B), he, (β A).map_comp δ,
    δ.map_eq_of_hom f (by simp) G hG]

/-- The ambient comparison of a resolution extension with an ambient
weak-equivalence-inverting functor. -/
noncomputable def resolutionFunctorAmbientIso
    {E H : Type*} [Category E] [Category H]
    (G : C ⥤ E) (hG : (weakEquivalences C).IsInvertedBy G)
    (L : D ⥤ H) (hL : (weakEquivalences D).IsInvertedBy L)
    (K : E ⥤ H) (e : G ⋙ K ≅ F ⋙ L) :
    resolutionFunctor F Q q G hG ⋙ K ≅ L := by
  letI (A : D) : IsIso (L.map (q A)) := hL (q A) (inferInstance : WeakEquivalence (q A)).mem
  refine NatIso.ofComponents (fun A ↦ e.app (Q A) ≪≫ asIso (L.map (q A))) ?_
  intro A B f
  let φ := Classical.choice (ResolutionFraction.nonempty F (q A) (q B) f)
  change K.map (φ.map G hG) ≫ (e.hom.app (Q B) ≫ L.map (q B)) =
    (e.hom.app (Q A) ≫ L.map (q A)) ≫ L.map f
  have hs := e.hom.naturality φ.fraction.s
  have hf := e.hom.naturality φ.fraction.f
  change K.map (G.map φ.fraction.s) ≫ e.hom.app φ.fraction.Y' =
    e.hom.app (Q B) ≫ L.map (F.map φ.fraction.s) at hs
  change K.map (G.map φ.fraction.f) ≫ e.hom.app φ.fraction.Y' =
    e.hom.app (Q A) ≫ L.map (F.map φ.fraction.f) at hf
  have hc : (K.map (φ.map G hG) ≫ e.hom.app (Q B)) ≫ L.map (F.map φ.fraction.s) =
      e.hom.app (Q A) ≫ L.map (F.map φ.fraction.f) := by
    rw [Category.assoc, ← hs, ← Category.assoc, ← K.map_comp]
    change K.map (φ.fraction.map G hG ≫ G.map φ.fraction.s) ≫ _ = _
    rw [φ.fraction.map_comp_map_s, hf]
  calc
    K.map (φ.map G hG) ≫ (e.hom.app (Q B) ≫ L.map (q B)) =
        ((K.map (φ.map G hG) ≫ e.hom.app (Q B)) ≫ L.map (F.map φ.fraction.s)) ≫
          L.map φ.comparison := by
      simp only [Category.assoc, ← L.map_comp, φ.denominator]
    _ = (e.hom.app (Q A) ≫ L.map (F.map φ.fraction.f)) ≫ L.map φ.comparison := by rw [hc]
    _ = (e.hom.app (Q A) ≫ L.map (q A)) ≫ L.map f := by
      rw [Category.assoc, ← L.map_comp, φ.numerator, L.map_comp, Category.assoc]

/-- The inverse constructed from resolutions is a left inverse after
localization. -/
noncomputable def localizationLeftInverseIso :
    (toLocalizerMorphism F).localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q ⋙
      localizationInverse F Q q ≅ 𝟭 (weakEquivalences C).Localization := by
  let L := (weakEquivalences D).Q
  let G := (weakEquivalences C).Q
  let R := resolutionFunctor F Q q G (weakEquivalences C).Q_inverts
  let hR := resolutionFunctor_inverts F Q q G (weakEquivalences C).Q_inverts
  let H := Localization.lift R hR L
  let K := (toLocalizerMorphism F).localizedFunctor G L
  change K ⋙ H ≅ 𝟭 _
  let eK : G ⋙ K ≅ (toLocalizerMorphism F).functor ⋙ L :=
    Localization.Lifting.iso G (weakEquivalences C) _ _
  let eH : L ⋙ H ≅ R := Localization.fac R hR L
  let : Localization.Lifting G (weakEquivalences C) (F ⋙ R) (K ⋙ H) := ⟨
    (Functor.associator G K H).symm ≪≫ isoWhiskerRight eK H ≪≫
      Functor.associator F L H ≪≫ isoWhiskerLeft F eH⟩
  exact Localization.liftNatIso G (weakEquivalences C) (F ⋙ R) G (K ⋙ H) (𝟭 _)
    (resolutionFunctorRestrictionIso F Q q G (weakEquivalences C).Q_inverts)

/-- The inverse constructed from resolutions is also a right inverse. -/
noncomputable def localizationRightInverseIso :
    localizationInverse F Q q ⋙
      (toLocalizerMorphism F).localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q ≅
      𝟭 (weakEquivalences D).Localization := by
  let L := (weakEquivalences D).Q
  let G := (weakEquivalences C).Q
  let R := resolutionFunctor F Q q G (weakEquivalences C).Q_inverts
  let hR := resolutionFunctor_inverts F Q q G (weakEquivalences C).Q_inverts
  let H := Localization.lift R hR L
  change H ⋙ _ ≅ 𝟭 _
  let K := (toLocalizerMorphism F).localizedFunctor G L
  let eK : G ⋙ K ≅ (toLocalizerMorphism F).functor ⋙ L :=
    Localization.Lifting.iso G (weakEquivalences C) _ _
  exact Localization.liftNatIso L (weakEquivalences D) (R ⋙ K) L (H ⋙ K) (𝟭 _)
    (resolutionFunctorAmbientIso F Q q G (weakEquivalences C).Q_inverts
      L (weakEquivalences D).Q_inverts K eK)

/-- The localization equivalence, with prescribed resolutions as parameters. -/
noncomputable def localizationEquivalenceOfResolutions :
    (weakEquivalences C).Localization ≌ (weakEquivalences D).Localization :=
  CategoryTheory.Equivalence.mk
    ((toLocalizerMorphism F).localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q)
    (localizationInverse F Q q) (localizationLeftInverseIso F Q q).symm
    (localizationRightInverseIso F Q q)

omit Q q [∀ A, WeakEquivalence (q A)] in
/-- Theorem 6.1.7(1), the localization-equivalence part: CFA1–CFA4 imply
an equivalence, without a chosen family of resolutions in the statement. -/
instance localizedFunctor_isEquivalence :
    ((toLocalizerMorphism F).localizedFunctor (weakEquivalences C).Q
      (weakEquivalences D).Q).IsEquivalence := by
  let R (A : D) : (toLocalizerMorphism F).LeftResolution A :=
    Classical.choice (hasLeftResolutions F A)
  let Q (A : D) := (R A).X₁
  let q (A : D) : F.obj (Q A) ⟶ A := (R A).w
  let (A : D) : WeakEquivalence (q A) := ⟨(R A).hw⟩
  exact Functor.IsEquivalence.mk' (localizationInverse F Q q)
    (localizationLeftInverseIso F Q q).symm (localizationRightInverseIso F Q q)

omit Q q [∀ A, WeakEquivalence (q A)] in
/-- The general approximation determines a localized equivalence of
localizers. This is a consequence, not an additional CFA hypothesis. -/
instance toLocalizerMorphism_isLocalizedEquivalence :
    (toLocalizerMorphism F).IsLocalizedEquivalence :=
  LocalizerMorphism.IsLocalizedEquivalence.mk' (toLocalizerMorphism F)
    (weakEquivalences C).Q (weakEquivalences D).Q
    ((toLocalizerMorphism F).localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q)

omit Q q [∀ A, WeakEquivalence (q A)] in
/-- General cofibrant approximations are left derivability structures.
The localization equivalence is proved first, so the constructor is not
used circularly. -/
instance toLocalizerMorphism_isLeftDerivabilityStructure :
    (toLocalizerMorphism F).IsLeftDerivabilityStructure := by
  let : (weakEquivalences D).ContainsIdentities :=
    ⟨fun X ↦ (ABCPrecofibrationCategory.weakEquivalence_of_isIso (𝟙 X)).mem⟩
  exact LocalizerMorphism.IsLeftDerivabilityStructure.mk' _

end ABCCofibrations.IsCofibrantApproximation

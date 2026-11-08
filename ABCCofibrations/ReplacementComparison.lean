/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReplacementFunctor

/-!
# Comparison isomorphisms for cofibrant replacements

The replacement functor gives both inverse comparison isomorphisms. Thus
inclusion of cofibrant objects induces an equivalence on localizations,
Theorem 6.1.6. The proof constructs the inverse directly rather than through
the paper's general approximation theorem.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra CategoryTheory.Functor

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The reverse localization functor is a left inverse to the ambient
comparison, up to a natural isomorphism. -/
noncomputable def cofibrantLocalizationReplacementIso
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A)) :
    cofibrantLocalizationToAmbient ⋙ ambientLocalizationToCofibrant Q q hq ≅
      𝟭 (weakEquivalences (CofibrantObject C)).Localization := by
  let L := (weakEquivalences C).Q
  let F := (weakEquivalences (CofibrantObject C)).Q
  let hF := (inverts_weakEquivalences_iff_inverts_trivialCofibrations F).1
    (weakEquivalences (CofibrantObject C)).Q_inverts
  let R := replacementFunctor Q q hq F hF
  let hR := replacementFunctor_inverts Q q hq F hF
  let H := Localization.lift R hR L
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let K := Φ.localizedFunctor F L
  change K ⋙ H ≅ 𝟭 _
  let eK : F ⋙ K ≅ Φ.functor ⋙ L :=
    Localization.Lifting.iso F (weakEquivalences (CofibrantObject C)) _ _
  let eH : L ⋙ H ≅ R := Localization.fac R hR L
  let : Localization.Lifting F (weakEquivalences (CofibrantObject C))
      (CofibrantObject.ι ⋙ R) (K ⋙ H) := ⟨
    (Functor.associator F K H).symm ≪≫ isoWhiskerRight eK H ≪≫
      Functor.associator Φ.functor L H ≪≫ isoWhiskerLeft Φ.functor eH⟩
  exact Localization.liftNatIso F (weakEquivalences (CofibrantObject C))
    (CofibrantObject.ι ⋙ R) F (K ⋙ H) (𝟭 _)
    (replacementFunctorRestrictionIso Q q hq F hF)

/-- An ambient-inverting functor is recovered from a replacement extension
after a compatible comparison of functors on cofibrant objects. -/
noncomputable def replacementFunctorAmbientIso
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A))
    {D E : Type*} [Category D] [Category E]
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F)
    (L : C ⥤ E) (hL : (weakEquivalences C).IsInvertedBy L)
    (K : D ⥤ E) (e : F ⋙ K ≅ CofibrantObject.ι ⋙ L) :
    replacementFunctor Q q hq F hF ⋙ K ≅ L := by
  letI (A : C) : WeakEquivalence (q A) := hq A
  letI (A : C) : IsIso (L.map (q A)) := hL (q A) (hq A).mem
  refine NatIso.ofComponents
    (fun A ↦ e.app (Q A) ≪≫ asIso (L.map (q A))) ?_
  intro A B f
  let φ := chosenReplacementFraction (q A) (q B) f
  change K.map (φ.map F hF) ≫ (e.hom.app (Q B) ≫ L.map (q B)) =
    (e.hom.app (Q A) ≫ L.map (q A)) ≫ L.map f
  have hs := e.hom.naturality φ.fraction.s
  have hf := e.hom.naturality φ.fraction.f
  change K.map (F.map φ.fraction.s) ≫ e.hom.app φ.fraction.Y' =
    e.hom.app (Q B) ≫ L.map φ.fraction.s.hom at hs
  change K.map (F.map φ.fraction.f) ≫ e.hom.app φ.fraction.Y' =
    e.hom.app (Q A) ≫ L.map φ.fraction.f.hom at hf
  have hc : (K.map (φ.map F hF) ≫ e.hom.app (Q B)) ≫ L.map φ.fraction.s.hom =
      e.hom.app (Q A) ≫ L.map φ.fraction.f.hom := by
    rw [Category.assoc, ← hs, ← Category.assoc, ← K.map_comp]
    change K.map (φ.fraction.map F hF ≫ F.map φ.fraction.s) ≫ _ = _
    rw [φ.fraction.map_comp_map_s, hf]
  calc
    K.map (φ.map F hF) ≫ (e.hom.app (Q B) ≫ L.map (q B)) =
        ((K.map (φ.map F hF) ≫ e.hom.app (Q B)) ≫ L.map φ.fraction.s.hom) ≫
          L.map φ.comparison := by
      simp only [Category.assoc, ← L.map_comp, φ.denominator]
    _ = (e.hom.app (Q A) ≫ L.map φ.fraction.f.hom) ≫ L.map φ.comparison := by rw [hc]
    _ = (e.hom.app (Q A) ≫ L.map (q A)) ≫ L.map f := by
      rw [Category.assoc, ← L.map_comp, φ.numerator, L.map_comp, Category.assoc]

/-- The reverse functor is also a right inverse to the ambient comparison. -/
noncomputable def ambientLocalizationReplacementIso
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A)) :
    ambientLocalizationToCofibrant Q q hq ⋙ cofibrantLocalizationToAmbient ≅
      𝟭 (weakEquivalences C).Localization := by
  let L := (weakEquivalences C).Q
  let F := (weakEquivalences (CofibrantObject C)).Q
  let hF := (inverts_weakEquivalences_iff_inverts_trivialCofibrations F).1
    (weakEquivalences (CofibrantObject C)).Q_inverts
  let R := replacementFunctor Q q hq F hF
  let hR := replacementFunctor_inverts Q q hq F hF
  let H := Localization.lift R hR L
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let K := Φ.localizedFunctor F L
  change H ⋙ K ≅ 𝟭 _
  let eK : F ⋙ K ≅ Φ.functor ⋙ L :=
    Localization.Lifting.iso F (weakEquivalences (CofibrantObject C)) _ _
  exact Localization.liftNatIso L (weakEquivalences C) (R ⋙ K) L (H ⋙ K) (𝟭 _)
    (replacementFunctorAmbientIso Q q hq F hF L (weakEquivalences C).Q_inverts K eK)

/-- The ambient comparison is faithful. Cofibrant replacements exist for
every object, so the left inverse can be used without extra assumptions. -/
instance cofibrantLocalizationToAmbient_faithful :
    (cofibrantLocalizationToAmbient (C := C)).Faithful := by
  let R (A : C) : (cofibrantInclusionLocalizerMorphism (C := C)).LeftResolution A :=
    Classical.choice (cofibrantInclusion_hasLeftResolutions A)
  let Q (A : C) := (R A).X₁
  let q (A : C) : (Q A).obj ⟶ A := (R A).w
  have hq (A : C) : WeakEquivalence (q A) := ⟨(R A).hw⟩
  exact Functor.Faithful.of_comp_iso (cofibrantLocalizationReplacementIso Q q hq)

/-- Theorem 6.1.6 with explicit replacement choices and reverse functor. -/
noncomputable def cofibrantAmbientLocalizationEquivalenceOfReplacements
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A)) :
    (weakEquivalences (CofibrantObject C)).Localization ≌
      (weakEquivalences C).Localization :=
  CategoryTheory.Equivalence.mk cofibrantLocalizationToAmbient
    (ambientLocalizationToCofibrant Q q hq)
    (cofibrantLocalizationReplacementIso Q q hq).symm
    (ambientLocalizationReplacementIso Q q hq)

/-- Theorem 6.1.6: inclusion induces an equivalence on localizations. -/
instance cofibrantLocalizationToAmbient_isEquivalence :
    (cofibrantLocalizationToAmbient (C := C)).IsEquivalence := by
  let R (A : C) : (cofibrantInclusionLocalizerMorphism (C := C)).LeftResolution A :=
    Classical.choice (cofibrantInclusion_hasLeftResolutions A)
  let Q (A : C) := (R A).X₁
  let q (A : C) : (Q A).obj ⟶ A := (R A).w
  have hq (A : C) : WeakEquivalence (q A) := ⟨(R A).hw⟩
  exact Functor.IsEquivalence.mk' (ambientLocalizationToCofibrant Q q hq)
    (cofibrantLocalizationReplacementIso Q q hq).symm
    (ambientLocalizationReplacementIso Q q hq)

/-- The equivalence of localization of cofibrant objects with ambient
localization, with all choices supplied by existence of replacements. -/
noncomputable def cofibrantAmbientLocalizationEquivalence :
    (weakEquivalences (CofibrantObject C)).Localization ≌
      (weakEquivalences C).Localization :=
  (cofibrantLocalizationToAmbient (C := C)).asEquivalence

/-- Inclusion is a localized equivalence in mathlib's localizer interface. -/
instance cofibrantInclusion_isLocalizedEquivalence :
    (cofibrantInclusionLocalizerMorphism (C := C)).IsLocalizedEquivalence := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let F := (weakEquivalences (CofibrantObject C)).Q
  let L := (weakEquivalences C).Q
  let : (Φ.localizedFunctor F L).IsEquivalence :=
    inferInstanceAs (cofibrantLocalizationToAmbient (C := C)).IsEquivalence
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ F L (Φ.localizedFunctor F L)

/-- Restricting any ambient localization to cofibrant objects is itself a
localization at their weak equivalences. -/
instance cofibrantInclusion_comp_isLocalization
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)] :
    (CofibrantObject.ι ⋙ L).IsLocalization (weakEquivalences (CofibrantObject C)) :=
  inferInstanceAs (((cofibrantInclusionLocalizerMorphism (C := C)).functor ⋙ L).IsLocalization _)

/-- Theorem 6.4.4(1)(c) for ambient localization: two maps between cofibrant
objects have equal images exactly when they are left homotopic. -/
theorem ambient_map_eq_iff_cofibrant_leftHomotopy
    {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {X Y : CofibrantObject C} (f g : X ⟶ Y) :
    L.map f.hom = L.map g.hom ↔ cofibrantLeftHomotopyRel f g :=
  map_eq_iff_cofibrant_leftHomotopy (CofibrantObject.ι ⋙ L) f g

end ABCCofibrations.ABCPrecofibrationCategory

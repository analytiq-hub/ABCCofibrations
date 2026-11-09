/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.RightHomotopyOre
public import ABCCofibrations.FibrantSubcategory

/-!
# Localization of the native right-homotopy quotient

Localizing fibrant objects before or after passing to right-homotopy classes
gives equivalent categories. The fibrant approximation inclusion then gives
the comparison with ambient localization.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type*} [Category D]

/-- Every functor on fibrant objects inverting weak equivalences identifies
right-homotopic maps. -/
theorem map_eq_of_fibrant_rightHomotopy
    (F : FibrantObject C ⥤ D)
    (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F)
    {X Y : FibrantObject C} {f g : X ⟶ Y}
    (h : fibrantRightHomotopyRel f g) : F.map f = F.map g := by
  let := hasBinaryProduct Y.obj Y.obj
  change RightHomotopyRel f.hom g.hom at h
  obtain ⟨X', a, ha, haw, P, hP, ⟨H⟩⟩ := h
  let := ha
  let := hP
  let := pathObject_fibrant P
  let := fibrant_source a
  let p₀ : FibrantObject.mk P.P ⟶ Y := FibrantObject.homMk P.p₀
  let p₁ : FibrantObject.mk P.P ⟶ Y := FibrantObject.homMk P.p₁
  let i : Y ⟶ FibrantObject.mk P.P := FibrantObject.homMk P.ι
  let a' : FibrantObject.mk X' ⟶ X := FibrantObject.homMk a
  let H' : FibrantObject.mk X' ⟶ FibrantObject.mk P.P := FibrantObject.homMk H.h
  have hiw : weakEquivalences (FibrantObject C) i :=
    (show WeakEquivalence P.ι from inferInstance).mem
  let := hF i hiw
  let := hF a' haw.mem
  have hi₀ : i ≫ p₀ = 𝟙 Y := by ext; exact P.ι_p₀
  have hi₁ : i ≫ p₁ = 𝟙 Y := by ext; exact P.ι_p₁
  have hp : F.map p₀ = F.map p₁ := by
    apply (cancel_epi (F.map i)).1
    rw [← F.map_comp, ← F.map_comp, hi₀, hi₁]
  have h₀ : H' ≫ p₀ = a' ≫ f := by ext; exact H.h₀
  have h₁ : H' ≫ p₁ = a' ≫ g := by ext; exact H.h₁
  apply (cancel_epi (F.map a')).1
  rw [← F.map_comp, ← F.map_comp, ← h₀, ← h₁, F.map_comp, F.map_comp, hp]

/-- Factor a weak-equivalence-inverting functor through right-homotopy classes. -/
noncomputable def liftFromRightHomotopyCategory
    (F : FibrantObject C ⥤ D)
    (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F) :
    RightHomotopyCategory C ⥤ D :=
  CategoryTheory.Quotient.lift _ F
    (fun _ _ _ _ h ↦ map_eq_of_fibrant_rightHomotopy F hF h)

/-- The quotient factorization recovers the original functor. -/
theorem liftFromRightHomotopyCategory_fac
    (F : FibrantObject C ⥤ D)
    (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F) :
    toRightHomotopyCategory ⋙ liftFromRightHomotopyCategory F hF = F :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The quotient factorization is unique. -/
theorem liftFromRightHomotopyCategory_unique
    (F : FibrantObject C ⥤ D)
    (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F)
    (G : RightHomotopyCategory C ⥤ D) (hG : toRightHomotopyCategory ⋙ G = F) :
    G = liftFromRightHomotopyCategory F hF :=
  CategoryTheory.Quotient.lift_unique _ _ _ G hG
/-- The canonical comparison from right-homotopy classes to localization at
weak equivalences of fibrant objects. -/
noncomputable def rightHomotopyCategoryToLocalization :
    RightHomotopyCategory C ⥤ (weakEquivalences (FibrantObject C)).Localization :=
  liftFromRightHomotopyCategory _ (weakEquivalences (FibrantObject C)).Q_inverts

/-- The comparison agrees with localization on representatives. -/
theorem rightHomotopyCategoryToLocalization_fac :
    toRightHomotopyCategory ⋙ rightHomotopyCategoryToLocalization (C := C) =
      (weakEquivalences (FibrantObject C)).Q :=
  liftFromRightHomotopyCategory_fac _ _

/-- Right homotopy is killed by localization at weak equivalences, expressed in
mathlib's relation-level interface. -/
theorem fibrantRightHomotopyRel_factorsThroughLocalization :
    (fibrantRightHomotopyRel (C := C)).FactorsThroughLocalization
      (weakEquivalences (FibrantObject C)) := by
  intro X Y f g h
  rw [areEqualizedByLocalization_iff (weakEquivalences (FibrantObject C)).Q]
  exact map_eq_of_fibrant_rightHomotopy _
    (weakEquivalences (FibrantObject C)).Q_inverts h

/-- The quotient functor, with its preservation of weak equivalences recorded
as a localizer morphism. Its inverse image of the quotient weak equivalences
is exactly the original weak-equivalence class. -/
def rightHomotopyQuotientLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (FibrantObject C))
      (weakEquivalences (RightHomotopyCategory C)) :=
  LocalizerMorphism.ofEq
    (MorphismProperty.eq_inverseImage_quotientFunctor
      (weakEquivalences (FibrantObject C)) (fibrantRightHomotopyRel (C := C)))

/-- Passing to right-homotopy classes induces an equivalence on localizations.
This is weaker than identifying the quotient itself with the localization. -/
instance : (rightHomotopyQuotientLocalizerMorphism (C := C)).IsLocalizedEquivalence := by
  apply (fibrantRightHomotopyRel_factorsThroughLocalization (C := C)).isLocalizedEquivalence

/-- Following the quotient functor by a localization of the quotient gives a
localization of the original category of fibrant objects. -/
instance localization_after_rightHomotopyQuotient (L : RightHomotopyCategory C ⥤ D)
    [L.IsLocalization (weakEquivalences (RightHomotopyCategory C))] :
    (toRightHomotopyCategory ⋙ L).IsLocalization (weakEquivalences (FibrantObject C)) :=
  inferInstanceAs
    (((rightHomotopyQuotientLocalizerMorphism (C := C)).functor ⋙ L).IsLocalization _)

/-- The induced functor between the canonical localizations. -/
noncomputable def localizedRightHomotopyQuotient :
    (weakEquivalences (FibrantObject C)).Localization ⥤
      (weakEquivalences (RightHomotopyCategory C)).Localization :=
  (rightHomotopyQuotientLocalizerMorphism (C := C)).localizedFunctor
    (weakEquivalences (FibrantObject C)).Q
    (weakEquivalences (RightHomotopyCategory C)).Q

instance : (localizedRightHomotopyQuotient (C := C)).IsEquivalence :=
  inferInstanceAs
    ((rightHomotopyQuotientLocalizerMorphism (C := C)).localizedFunctor
      (weakEquivalences (FibrantObject C)).Q
      (weakEquivalences (RightHomotopyCategory C)).Q).IsEquivalence

/-- Localizing before or after passing to right-homotopy classes gives
equivalent categories. -/
noncomputable def rightHomotopyLocalizationEquivalence :
    (weakEquivalences (FibrantObject C)).Localization ≌
      (weakEquivalences (RightHomotopyCategory C)).Localization :=
  (localizedRightHomotopyQuotient (C := C)).asEquivalence

/-- The comparison inverts the weak equivalences of the homotopy quotient. -/
theorem rightHomotopyCategoryToLocalization_inverts :
    (weakEquivalences (RightHomotopyCategory C)).IsInvertedBy
      (rightHomotopyCategoryToLocalization (C := C)) := by
  rintro ⟨X⟩ ⟨Y⟩ f hf
  obtain ⟨g, hg, rfl⟩ := hf
  change IsIso ((weakEquivalences (FibrantObject C)).Q.map g)
  exact (weakEquivalences (FibrantObject C)).Q_inverts g hg

/-- The comparison has the strict localization universal property: every
functor on right-homotopy classes which inverts weak equivalences factors
uniquely through it. -/
noncomputable def rightHomotopyComparisonStrictUniversalProperty :
    Localization.StrictUniversalPropertyFixedTarget
      (rightHomotopyCategoryToLocalization (C := C))
      (weakEquivalences (RightHomotopyCategory C)) D where
  inverts := rightHomotopyCategoryToLocalization_inverts
  lift F hF := Localization.Construction.lift (toRightHomotopyCategory ⋙ F)
    (fun _ _ f hf ↦ hF (toRightHomotopyCategory.map f)
      ((MorphismProperty.quotient_iff _ _ f).2 hf))
  fac F hF := by
    apply CategoryTheory.Quotient.lift_unique' (fibrantRightHomotopyRel (C := C))
    change toRightHomotopyCategory ⋙ (rightHomotopyCategoryToLocalization ⋙
      Localization.Construction.lift (toRightHomotopyCategory ⋙ F) _) =
      toRightHomotopyCategory ⋙ F
    rw [← Functor.assoc, rightHomotopyCategoryToLocalization_fac]
    exact Localization.Construction.fac (W := weakEquivalences (FibrantObject C)) _ _
  uniq F₁ F₂ h := by
    apply Localization.Construction.uniq
    rw [← rightHomotopyCategoryToLocalization_fac, Functor.assoc, h, Functor.assoc]

/-- The comparison is a localization of the homotopy quotient at its weak
equivalences. This does not assert that the comparison is an equivalence
without localizing those weak equivalences. -/
instance rightHomotopyCategoryToLocalization_isLocalization :
    (rightHomotopyCategoryToLocalization (C := C)).IsLocalization
      (weakEquivalences (RightHomotopyCategory C)) :=
  Functor.IsLocalization.mk' _ _
    (rightHomotopyComparisonStrictUniversalProperty
      (D := (weakEquivalences (FibrantObject C)).Localization))
    (rightHomotopyComparisonStrictUniversalProperty
      (D := (weakEquivalences (RightHomotopyCategory C)).Localization))



/-- Weak equivalences act as epimorphisms on right-homotopy classes. -/
theorem epi_toRightHomotopyCategory_map
    {X Y : FibrantObject C} (f : X ⟶ Y) [WeakEquivalence f.hom] :
    Epi ((toRightHomotopyCategory (C := C)).map f) := by
  constructor
  rintro ⟨Z⟩ ⟨g⟩ ⟨h⟩ he
  change Y ⟶ Z at g h
  apply (toRightHomotopyCategory_map_eq_iff g h).2
  have hh : fibrantRightHomotopyRel (f ≫ g) (f ≫ h) := by
    apply (toRightHomotopyCategory_map_eq_iff _ _).1
    change toRightHomotopyCategory.map f ≫ toRightHomotopyCategory.map g =
      toRightHomotopyCategory.map f ≫ toRightHomotopyCategory.map h at he
    rw [← Functor.map_comp, ← Functor.map_comp] at he
    exact he
  let := hasBinaryProduct Z.obj Z.obj
  exact RightHomotopyRel.of_precomp_weakEquivalence f.hom hh

/-- Every descended weak equivalence is an epimorphism in the quotient. -/
instance epi_of_weakEquivalence_rightHomotopyCategory
    {X Y : RightHomotopyCategory C} (f : X ⟶ Y) [WeakEquivalence f] : Epi f := by
  have hw := ‹WeakEquivalence f›
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨g, hg⟩ := (toRightHomotopyCategory (C := C)).map_surjective f
  have hgw : WeakEquivalence (toRightHomotopyCategory.map g) := by rw [hg]; exact hw
  let : WeakEquivalence g.hom := (weakEquivalence_toRightHomotopyCategory_map_iff g).1 hgw
  rw [← hg]
  exact epi_toRightHomotopyCategory_map g

/-- Localization is faithful on the right-homotopy quotient: the right
calculus detects equality after a weak-equivalence precomposition, and
that denominator is already an epimorphism. -/
instance rightHomotopyCategoryToLocalization_faithful :
    (rightHomotopyCategoryToLocalization (C := C)).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨Z, s, hs, he⟩ :=
      (MorphismProperty.map_eq_iff_precomp
        (rightHomotopyCategoryToLocalization (C := C))
        (weakEquivalences (RightHomotopyCategory C)) f g).1 h
    let : WeakEquivalence s := ⟨hs⟩
    exact (cancel_epi s).1 he

/-- For any localization of the fibrant subcategory, equality of images
of representative maps is exactly native right homotopy. -/
theorem map_eq_iff_fibrant_rightHomotopy
    (F : FibrantObject C ⥤ D) [F.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ fibrantRightHomotopyRel f g := by
  constructor
  · intro h
    apply (toRightHomotopyCategory_map_eq_iff f g).1
    apply (rightHomotopyCategoryToLocalization (C := C)).map_injective
    change (weakEquivalences (FibrantObject C)).Q.map f =
      (weakEquivalences (FibrantObject C)).Q.map g
    exact AreEqualizedByLocalization.mk (weakEquivalences (FibrantObject C)) f g F h
  · exact map_eq_of_fibrant_rightHomotopy F (Localization.inverts F _)

/-- The comparison from localization of fibrant objects to ambient localization. -/
noncomputable def fibrantLocalizationToAmbient :
    (weakEquivalences (FibrantObject C)).Localization ⥤ (weakEquivalences C).Localization :=
  (IsFibrantApproximation.toLocalizerMorphism (FibrantObject.ι (C := C))).localizedFunctor
    (weakEquivalences (FibrantObject C)).Q (weakEquivalences C).Q

/-- Theorem 6.1.6(2), now with the native fibrant-object localization. -/
instance fibrantLocalizationToAmbient_isEquivalence :
    (fibrantLocalizationToAmbient (C := C)).IsEquivalence :=
  inferInstanceAs
    ((IsFibrantApproximation.toLocalizerMorphism (FibrantObject.ι (C := C))).localizedFunctor
      (weakEquivalences (FibrantObject C)).Q (weakEquivalences C).Q).IsEquivalence

/-- The fibrant inclusion gives an equivalence on the canonical localizations. -/
noncomputable def fibrantAmbientLocalizationEquivalence :
    (weakEquivalences (FibrantObject C)).Localization ≌ (weakEquivalences C).Localization :=
  fibrantLocalizationToAmbient.asEquivalence

/-- Any ambient localization restricts to a localization of fibrant objects. -/
instance fibrantInclusion_comp_isLocalization (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    (FibrantObject.ι ⋙ L).IsLocalization (weakEquivalences (FibrantObject C)) :=
  inferInstanceAs
    (((IsFibrantApproximation.toLocalizerMorphism
      (FibrantObject.ι (C := C))).functor ⋙ L).IsLocalization _)

/-- Localizing the native right-homotopy quotient gives ambient localization,
by the quotient and fibrant-inclusion equivalences. -/
noncomputable def rightHomotopyAmbientLocalizationEquivalence :
    (weakEquivalences (RightHomotopyCategory C)).Localization ≌
      (weakEquivalences C).Localization :=
  (rightHomotopyLocalizationEquivalence (C := C)).symm.trans
    (fibrantAmbientLocalizationEquivalence (C := C))

end ABCCofibrations.ABCPrefibrationCategory

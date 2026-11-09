/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyWeakEquivalences
public import ABCCofibrations.HomotopyOre
public import ABCCofibrations.TrivialCofibrationLocalization
public import Mathlib.CategoryTheory.Localization.Quotient
public import ABCCofibrations.LocalizationTransfer

/-!
# Comparing left-homotopy classes with localization

Any functor on cofibrant objects which inverts weak equivalences identifies
left-homotopic maps. Consequently it factors through `LeftHomotopyCategory`,
and the quotient category has a canonical comparison functor to localization.

The quotient functor induces an equivalence after both categories are localized
at their weak equivalences. Thus taking left-homotopy classes does not change
the localization. Weak equivalences in the quotient still need to be inverted.

The homotopy calculus of fractions and cancellation show that the comparison
is faithful: equality in localization is exactly left homotopy on maps
between cofibrant objects. We do not assert that the comparison is an
equivalence, or that the quotient functor itself is a localization.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type w} [Category D]

/-- Every weak-equivalence-inverting functor on cofibrant objects identifies
left-homotopic maps. The cylinder projection identifies its two endpoints,
and the target enlargement can then be cancelled. -/
theorem map_eq_of_cofibrant_leftHomotopy
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F)
    {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : cofibrantLeftHomotopyRel f g) : F.map f = F.map g := by
  let := hasBinaryCoproduct X.obj X.obj
  change LeftHomotopyRel f.hom g.hom at h
  obtain ⟨Y', b, hb, hbw, P, hP, ⟨H⟩⟩ := h
  let := hb
  let := hP
  let := cylinder_cofibrant P
  let := cofibrant_target b
  let i₀ : X ⟶ CofibrantObject.mk P.I := CofibrantObject.homMk P.i₀
  let i₁ : X ⟶ CofibrantObject.mk P.I := CofibrantObject.homMk P.i₁
  let p : CofibrantObject.mk P.I ⟶ X := CofibrantObject.homMk P.π
  let b' : Y ⟶ CofibrantObject.mk Y' := CofibrantObject.homMk b
  let H' : CofibrantObject.mk P.I ⟶ CofibrantObject.mk Y' :=
    CofibrantObject.homMk H.h
  have hp : weakEquivalences (CofibrantObject C) p := by
    change weakEquivalences C P.π
    exact (inferInstance : WeakEquivalence P.π).mem
  have hbw' : weakEquivalences (CofibrantObject C) b' := by
    change weakEquivalences C b
    exact hbw.mem
  let := hF p hp
  let := hF b' hbw'
  have hi₀ : i₀ ≫ p = 𝟙 X := by ext; exact P.i₀_π
  have hi₁ : i₁ ≫ p = 𝟙 X := by ext; exact P.i₁_π
  have hi : F.map i₀ = F.map i₁ := by
    apply (cancel_mono (F.map p)).1
    rw [← F.map_comp, ← F.map_comp, hi₀, hi₁]
  have h₀ : i₀ ≫ H' = f ≫ b' := by ext; exact H.h₀
  have h₁ : i₁ ≫ H' = g ≫ b' := by ext; exact H.h₁
  apply (cancel_mono (F.map b')).1
  rw [← F.map_comp, ← F.map_comp, ← h₀, ← h₁, F.map_comp, F.map_comp, hi]

/-- Equality after a weak equivalence to an arbitrary ambient object already
forces equality under every weak-equivalence-inverting functor on cofibrant
objects. The ambient target need not be cofibrant (Lemma 6.1.3(1)). -/
theorem map_eq_of_postcomp_ambient_weakEquivalence
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F)
    {X Y : CofibrantObject C} (f g : X ⟶ Y)
    {B : C} (b : Y.obj ⟶ B) [WeakEquivalence b]
    (h : f.hom ≫ b = g.hom ≫ b) : F.map f = F.map g := by
  apply map_eq_of_cofibrant_leftHomotopy F hF
  let := hasBinaryCoproduct X.obj X.obj
  change LeftHomotopyRel f.hom g.hom
  exact LeftHomotopyRel.of_postcomp_weakEquivalence_eq b h

/-- Factor a weak-equivalence-inverting functor through left-homotopy classes. -/
noncomputable def liftFromLeftHomotopyCategory
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F) :
    LeftHomotopyCategory C ⥤ D :=
  CategoryTheory.Quotient.lift _ F
    (fun _ _ _ _ h ↦ map_eq_of_cofibrant_leftHomotopy F hF h)

/-- The factorization through homotopy classes recovers the original functor. -/
theorem liftFromLeftHomotopyCategory_fac
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F) :
    toLeftHomotopyCategory ⋙ liftFromLeftHomotopyCategory F hF = F :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The factorization through homotopy classes is unique. -/
theorem liftFromLeftHomotopyCategory_unique
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F)
    (G : LeftHomotopyCategory C ⥤ D) (hG : toLeftHomotopyCategory ⋙ G = F) :
    G = liftFromLeftHomotopyCategory F hF :=
  CategoryTheory.Quotient.lift_unique _ _ _ G hG

/-- Inverting only the trivial cofibrations already ensures that a functor
identifies left-homotopic maps, by Brown's functor lemma. -/
theorem map_eq_of_leftHomotopy_of_inverts_trivialCofibrations
    (F : CofibrantObject C ⥤ D)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i))
    {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : cofibrantLeftHomotopyRel f g) : F.map f = F.map g :=
  map_eq_of_cofibrant_leftHomotopy F
    (isInvertedBy_of_inverts_trivialCofibrations F hF) h

/-- A functor inverting trivial cofibrations factors through left-homotopy
classes; Brown's lemma supplies inversion of all weak equivalences. -/
noncomputable def liftFromLeftHomotopyCategoryOfTrivialCofibrations
    (F : CofibrantObject C ⥤ D)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i)) :
    LeftHomotopyCategory C ⥤ D :=
  liftFromLeftHomotopyCategory F (isInvertedBy_of_inverts_trivialCofibrations F hF)

/-- The factorization obtained from inversion of trivial cofibrations agrees
with the original functor on representatives. -/
theorem liftFromLeftHomotopyCategoryOfTrivialCofibrations_fac
    (F : CofibrantObject C ⥤ D)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i)) :
    toLeftHomotopyCategory ⋙ liftFromLeftHomotopyCategoryOfTrivialCofibrations F hF = F :=
  liftFromLeftHomotopyCategory_fac _ _

/-- The canonical comparison from left-homotopy classes to localization at
weak equivalences of cofibrant objects. -/
noncomputable def leftHomotopyCategoryToLocalization :
    LeftHomotopyCategory C ⥤ (weakEquivalences (CofibrantObject C)).Localization :=
  liftFromLeftHomotopyCategory _ (weakEquivalences (CofibrantObject C)).Q_inverts

/-- The comparison agrees with localization on representatives. -/
theorem leftHomotopyCategoryToLocalization_fac :
    toLeftHomotopyCategory ⋙ leftHomotopyCategoryToLocalization (C := C) =
      (weakEquivalences (CofibrantObject C)).Q :=
  liftFromLeftHomotopyCategory_fac _ _

/-- Left-homotopy classes also map canonically to localization at trivial
cofibrations. Brown's lemma supplies inversion of all weak equivalences there. -/
noncomputable def leftHomotopyCategoryToTrivialCofibrationLocalization :
    LeftHomotopyCategory C ⥤ (cofibrantTrivialCofibrations (C := C)).Localization :=
  liftFromLeftHomotopyCategory _
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations _).2
      (cofibrantTrivialCofibrations (C := C)).Q_inverts)

/-- The comparison to trivial-cofibration localization agrees on representatives. -/
theorem leftHomotopyCategoryToTrivialCofibrationLocalization_fac :
    toLeftHomotopyCategory ⋙
      leftHomotopyCategoryToTrivialCofibrationLocalization (C := C) =
        (cofibrantTrivialCofibrations (C := C)).Q :=
  liftFromLeftHomotopyCategory_fac _ _

/-- Left homotopy is killed by localization at weak equivalences, expressed in
mathlib's relation-level interface. -/
theorem cofibrantLeftHomotopyRel_factorsThroughLocalization :
    (cofibrantLeftHomotopyRel (C := C)).FactorsThroughLocalization
      (weakEquivalences (CofibrantObject C)) := by
  intro X Y f g h
  rw [areEqualizedByLocalization_iff (weakEquivalences (CofibrantObject C)).Q]
  exact map_eq_of_cofibrant_leftHomotopy _
    (weakEquivalences (CofibrantObject C)).Q_inverts h

/-- The quotient functor, with its preservation of weak equivalences recorded
as a localizer morphism. Its inverse image of the quotient weak equivalences
is exactly the original weak-equivalence class. -/
def leftHomotopyQuotientLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C))
      (weakEquivalences (LeftHomotopyCategory C)) :=
  LocalizerMorphism.ofEq
    (MorphismProperty.eq_inverseImage_quotientFunctor
      (weakEquivalences (CofibrantObject C)) (cofibrantLeftHomotopyRel (C := C)))

/-- Passing to left-homotopy classes induces an equivalence on localizations.
This is weaker than identifying the quotient itself with the localization. -/
instance : (leftHomotopyQuotientLocalizerMorphism (C := C)).IsLocalizedEquivalence := by
  apply (cofibrantLeftHomotopyRel_factorsThroughLocalization (C := C)).isLocalizedEquivalence

/-- Following the quotient functor by a localization of the quotient gives a
localization of the original category of cofibrant objects. -/
instance localization_after_leftHomotopyQuotient (L : LeftHomotopyCategory C ⥤ D)
    [L.IsLocalization (weakEquivalences (LeftHomotopyCategory C))] :
    (toLeftHomotopyCategory ⋙ L).IsLocalization (weakEquivalences (CofibrantObject C)) :=
  inferInstanceAs
    (((leftHomotopyQuotientLocalizerMorphism (C := C)).functor ⋙ L).IsLocalization _)

/-- The induced functor between the canonical localizations. -/
noncomputable def localizedLeftHomotopyQuotient :
    (weakEquivalences (CofibrantObject C)).Localization ⥤
      (weakEquivalences (LeftHomotopyCategory C)).Localization :=
  (leftHomotopyQuotientLocalizerMorphism (C := C)).localizedFunctor
    (weakEquivalences (CofibrantObject C)).Q
    (weakEquivalences (LeftHomotopyCategory C)).Q

instance : (localizedLeftHomotopyQuotient (C := C)).IsEquivalence :=
  inferInstanceAs
    ((leftHomotopyQuotientLocalizerMorphism (C := C)).localizedFunctor
      (weakEquivalences (CofibrantObject C)).Q
      (weakEquivalences (LeftHomotopyCategory C)).Q).IsEquivalence

/-- Localizing before or after passing to left-homotopy classes gives
equivalent categories. -/
noncomputable def leftHomotopyLocalizationEquivalence :
    (weakEquivalences (CofibrantObject C)).Localization ≌
      (weakEquivalences (LeftHomotopyCategory C)).Localization :=
  (localizedLeftHomotopyQuotient (C := C)).asEquivalence

/-- The comparison inverts the weak equivalences of the homotopy quotient. -/
theorem leftHomotopyCategoryToLocalization_inverts :
    (weakEquivalences (LeftHomotopyCategory C)).IsInvertedBy
      (leftHomotopyCategoryToLocalization (C := C)) :=
  Localization.quotientLift_inverts
    (MorphismProperty.eq_inverseImage_quotientFunctor _ _) _
    leftHomotopyCategoryToLocalization_fac

/-- The comparison has the strict localization universal property: every
functor on left-homotopy classes which inverts weak equivalences factors
uniquely through it. This is the general quotient-lift statement of
`LocalizationTransfer.lean`, shared with the right-homotopy quotient. -/
noncomputable def leftHomotopyComparisonStrictUniversalProperty :
    Localization.StrictUniversalPropertyFixedTarget
      (leftHomotopyCategoryToLocalization (C := C))
      (weakEquivalences (LeftHomotopyCategory C)) D :=
  Localization.strictUniversalPropertyFixedTargetQuotientLift
    (MorphismProperty.eq_inverseImage_quotientFunctor _ _) _
    leftHomotopyCategoryToLocalization_fac D

/-- The comparison is a localization of the homotopy quotient at its weak
equivalences. This does not assert that the comparison is an equivalence
without localizing those weak equivalences. -/
instance leftHomotopyCategoryToLocalization_isLocalization :
    (leftHomotopyCategoryToLocalization (C := C)).IsLocalization
      (weakEquivalences (LeftHomotopyCategory C)) :=
  Localization.isLocalization_quotientLift
    (MorphismProperty.eq_inverseImage_quotientFunctor _ _) _
    leftHomotopyCategoryToLocalization_fac

/-- The comparison is faithful. The calculus of fractions detects equality
after postcomposition by a weak equivalence, which is a monomorphism in the
homotopy quotient by homotopy cancellation. -/
instance leftHomotopyCategoryToLocalization_faithful :
    (leftHomotopyCategoryToLocalization (C := C)).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨Z, s, hs, he⟩ :=
      (MorphismProperty.map_eq_iff_postcomp
        (leftHomotopyCategoryToLocalization (C := C))
        (weakEquivalences (LeftHomotopyCategory C)) f g).1 h
    let : WeakEquivalence s := (weakEquivalence_iff _).2 hs
    exact (cancel_mono s).1 he

/-- For any localization of the full subcategory of cofibrant objects,
two maps have equal images exactly when they are left homotopic. This is
the cofibrant-subcategory version of Theorem 6.4.4(1)(c). -/
theorem map_eq_iff_cofibrant_leftHomotopy
    (F : CofibrantObject C ⥤ D) [F.IsLocalization (weakEquivalences (CofibrantObject C))]
    {X Y : CofibrantObject C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ cofibrantLeftHomotopyRel f g := by
  constructor
  · intro h
    apply (toLeftHomotopyCategory_map_eq_iff f g).1
    apply (leftHomotopyCategoryToLocalization (C := C)).map_injective
    change (weakEquivalences (CofibrantObject C)).Q.map f =
      (weakEquivalences (CofibrantObject C)).Q.map g
    exact AreEqualizedByLocalization.mk (weakEquivalences (CofibrantObject C)) f g F h
  · exact map_eq_of_cofibrant_leftHomotopy F (Localization.inverts F _)

end ABCCofibrations.ABCPrecofibrationCategory

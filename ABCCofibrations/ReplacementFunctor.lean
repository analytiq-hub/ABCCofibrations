/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.AmbientFractions

/-!
# Arrows between prescribed cofibrant replacements

An ambient arrow is represented by a trivial-cofibration fraction between
prescribed replacements. Independence of fraction choice gives a functor on
the ambient category, and this functor inverts weak equivalences. It descends
to a functor in the reverse direction on localizations. The comparison
isomorphisms proving Theorem 6.1.6 are in `ReplacementComparison.lean`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- A fraction between prescribed replacements representing an ambient arrow.
The comparison from the apex to the ambient target is a weak equivalence. -/
structure ReplacementFraction {A B : C} {X Y : CofibrantObject C}
    (qX : X.obj ⟶ A) (qY : Y.obj ⟶ B) (f : A ⟶ B) where
  fraction : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y
  comparison : fraction.Y'.obj ⟶ B
  comparison_weakEquivalence : WeakEquivalence comparison
  numerator : fraction.f.hom ≫ comparison = qX ≫ f
  denominator : fraction.s.hom ≫ comparison = qY

attribute [instance] ReplacementFraction.comparison_weakEquivalence

namespace ReplacementFraction

variable {A B : C} {X Y : CofibrantObject C}
  {qX : X.obj ⟶ A} {qY : Y.obj ⟶ B} {f : A ⟶ B}

/-- CF4 applied to the coproduct map constructs a fraction while retaining
both prescribed replacements. Only the target replacement must be a weak
equivalence for this existence argument. -/
theorem nonempty (qX : X.obj ⟶ A) (qY : Y.obj ⟶ B) [WeakEquivalence qY]
    (f : A ⟶ B) : Nonempty (ReplacementFraction qX qY f) := by
  let := hasBinaryCoproduct X.obj Y.obj
  let : IsCofibrant (X.obj ⨿ Y.obj) := coprod_cofibrant
  let := cofibration_coprod_inl (A := X.obj) (B := Y.obj)
  let := cofibration_coprod_inr (A := X.obj) (B := Y.obj)
  obtain ⟨R, i, p, hi, hp, h⟩ := factorization (coprod.desc (qX ≫ f) qY)
  let := hi
  let := hp
  let := cofibrant_target i
  have hn : (coprod.inl ≫ i) ≫ p = qX ≫ f := by simp [Category.assoc, h]
  have hd : (coprod.inr ≫ i) ≫ p = qY := by simp [Category.assoc, h]
  have hw : WeakEquivalence (coprod.inr ≫ i) := weakEquivalence_of_postcomp_of_fac hd
  have hc : Cofibration (coprod.inr ≫ i) := inferInstance
  exact ⟨{
    fraction := {
      Y' := CofibrantObject.mk R
      f := CofibrantObject.homMk (coprod.inl ≫ i)
      s := CofibrantObject.homMk (coprod.inr ≫ i)
      hs := (mem_cofibrantTrivialCofibrations_iff _).2 ⟨hc, hw⟩ }
    comparison := p
    comparison_weakEquivalence := hp
    numerator := hn
    denominator := hd }⟩

variable {D : Type u'} [Category.{v'} D]

/-- The value of a replacement fraction under a functor inverting trivial
cofibrations. -/
noncomputable def map (φ : ReplacementFraction qX qY f)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    F.obj X ⟶ F.obj Y := φ.fraction.map F hF

/-- The represented arrow does not depend on the chosen fraction. -/
theorem map_eq (φ ψ : ReplacementFraction qX qY f)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF :=
  trivialCofibration_fraction_map_eq_of_ambient_comparison
    φ.fraction ψ.fraction φ.comparison ψ.comparison
    (φ.numerator.trans ψ.numerator.symm) (φ.denominator.trans ψ.denominator.symm) F hF

/-- An actual map between the replacements gives a fraction with identity
denominator whenever it lies over the given ambient arrow. -/
def ofHom [WeakEquivalence qY] (i : X ⟶ Y)
    (h : i.hom ≫ qY = qX ≫ f) : ReplacementFraction qX qY f where
  fraction := {
    f := i
    s := 𝟙 Y
    hs := (mem_cofibrantTrivialCofibrations_iff _).2
      ⟨cofibration_of_isIso (𝟙 Y.obj), weakEquivalence_of_isIso (𝟙 Y.obj)⟩ }
  comparison := qY
  comparison_weakEquivalence := inferInstance
  numerator := h
  denominator := by simp

/-- A fraction represented by an actual map has the expected value. -/
theorem map_ofHom [WeakEquivalence qY] (i : X ⟶ Y)
    (h : i.hom ≫ qY = qX ≫ f)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    (ofHom i h).map F hF = F.map i := by
  have he := (ofHom i h).fraction.map_comp_map_s F hF
  simpa [ofHom, map] using he

variable {E : C} {Z : CofibrantObject C} {qZ : Z.obj ⟶ E} {g : B ⟶ E}

/-- Pushout composition retains the comparison to the ambient target. -/
noncomputable def comp (φ : ReplacementFraction qX qY f)
    (ψ : ReplacementFraction qY qZ g) : ReplacementFraction qX qZ (f ≫ g) := by
  obtain ⟨hc, hw⟩ := (mem_cofibrantTrivialCofibrations_iff φ.fraction.s).1 φ.fraction.hs
  obtain ⟨hd, hv⟩ := (mem_cofibrantTrivialCofibrations_iff ψ.fraction.s).1 ψ.fraction.hs
  let := hc
  let := hw
  let := hd
  let := hv
  let sq := IsPushout.of_hasPushout φ.fraction.s.hom ψ.fraction.f.hom
  let := cofibration_of_isPushout sq
  let := weakEquivalence_of_isPushout sq
  let := cofibrant_target (pushout.inr φ.fraction.s.hom ψ.fraction.f.hom)
  have h : φ.fraction.s.hom ≫ (φ.comparison ≫ g) =
      ψ.fraction.f.hom ≫ ψ.comparison := by
    rw [← Category.assoc, φ.denominator, ψ.numerator]
  let r := pushout.desc (φ.comparison ≫ g) ψ.comparison h
  have hr : WeakEquivalence r := weakEquivalence_of_precomp_of_fac
    (pushout.inr_desc (φ.comparison ≫ g) ψ.comparison h)
  have hs : Cofibration (ψ.fraction.s.hom ≫ pushout.inr φ.fraction.s.hom ψ.fraction.f.hom) :=
    inferInstance
  have hsw : WeakEquivalence (ψ.fraction.s.hom ≫ pushout.inr φ.fraction.s.hom ψ.fraction.f.hom) :=
    inferInstance
  exact {
    fraction := {
      Y' := CofibrantObject.mk (pushout φ.fraction.s.hom ψ.fraction.f.hom)
      f := CofibrantObject.homMk (φ.fraction.f.hom ≫ pushout.inl _ _)
      s := CofibrantObject.homMk (ψ.fraction.s.hom ≫ pushout.inr _ _)
      hs := (mem_cofibrantTrivialCofibrations_iff _).2 ⟨hs, hsw⟩ }
    comparison := r
    comparison_weakEquivalence := hr
    numerator := by
      change (φ.fraction.f.hom ≫ pushout.inl _ _) ≫ r = qX ≫ (f ≫ g)
      simp only [r, Category.assoc, pushout.inl_desc]
      rw [← Category.assoc, φ.numerator, Category.assoc]
    denominator := by
      change (ψ.fraction.s.hom ≫ pushout.inr _ _) ≫ r = qZ
      simp only [r, Category.assoc, pushout.inr_desc, ψ.denominator] }

set_option backward.isDefEq.respectTransparency false in
/-- The pushout composite represents composition of the mapped arrows. -/
theorem map_comp (φ : ReplacementFraction qX qY f)
    (ψ : ReplacementFraction qY qZ g)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    (φ.comp ψ).map F hF = φ.map F hF ≫ ψ.map F hF := by
  let := ((mem_cofibrantTrivialCofibrations_iff φ.fraction.s).1 φ.fraction.hs).1
  let := cofibration_of_isPushout
    (IsPushout.of_hasPushout φ.fraction.s.hom ψ.fraction.f.hom)
  let := cofibrant_target (pushout.inr φ.fraction.s.hom ψ.fraction.f.hom)
  let χ := φ.comp ψ
  let := hF _ χ.fraction.hs
  apply (cancel_mono (F.map χ.fraction.s)).1
  rw [show χ.map F hF ≫ F.map χ.fraction.s = F.map χ.fraction.f from
    χ.fraction.map_comp_map_s F hF]
  let a : φ.fraction.Y' ⟶ χ.fraction.Y' := CofibrantObject.homMk (pushout.inl _ _)
  let b : ψ.fraction.Y' ⟶ χ.fraction.Y' := CofibrantObject.homMk (pushout.inr _ _)
  have hs : χ.fraction.s = ψ.fraction.s ≫ b := rfl
  have hf : χ.fraction.f = φ.fraction.f ≫ a := rfl
  have sq : φ.fraction.s ≫ a = ψ.fraction.f ≫ b := by
    ext; exact pushout.condition
  rw [hs, hf, F.map_comp, F.map_comp]
  change F.map φ.fraction.f ≫ F.map a =
    (φ.fraction.map F hF ≫ ψ.fraction.map F hF) ≫ (F.map ψ.fraction.s ≫ F.map b)
  calc
    F.map φ.fraction.f ≫ F.map a = φ.fraction.map F hF ≫ F.map (φ.fraction.s ≫ a) := by
      rw [F.map_comp, ← Category.assoc, φ.fraction.map_comp_map_s]
    _ = φ.fraction.map F hF ≫ F.map (ψ.fraction.f ≫ b) := by rw [sq]
    _ = (φ.fraction.map F hF ≫ ψ.fraction.map F hF) ≫
        (F.map ψ.fraction.s ≫ F.map b) := by
      simp only [F.map_comp, Category.assoc]
      rw [← Category.assoc (ψ.fraction.map F hF), ψ.fraction.map_comp_map_s]

/-- If the ambient arrow is a weak equivalence, the represented arrow is
invertible. Two out of three makes the numerator a weak equivalence. -/
theorem isIso_map_of_weakEquivalence [WeakEquivalence qX] [WeakEquivalence f]
    (φ : ReplacementFraction qX qY f)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    IsIso (φ.map F hF) := by
  let hw : WeakEquivalence φ.fraction.f.hom :=
    weakEquivalence_of_postcomp_of_fac φ.numerator
  let : IsIso (F.map φ.fraction.f) :=
    ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).2 hF)
      φ.fraction.f hw.mem
  let := hF _ φ.fraction.hs
  change IsIso (F.map φ.fraction.f ≫ inv (F.map φ.fraction.s))
  infer_instance

omit [ABCPrecofibrationCategory C] in
/-- When the ambient target is cofibrant, the comparison map itself lies in
the cofibrant subcategory. The fraction commutes with that comparison under
any functor inverting trivial cofibrations. -/
theorem map_comp_comparison [IsCofibrant B]
    (φ : ReplacementFraction qX qY f)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF ≫ F.map (CofibrantObject.homMk qY) =
      F.map (CofibrantObject.homMk (qX ≫ f)) := by
  let p : φ.fraction.Y' ⟶ CofibrantObject.mk B :=
    CofibrantObject.homMk φ.comparison
  have hs : φ.fraction.s ≫ p = CofibrantObject.homMk qY := by
    ext; exact φ.denominator
  have hf : φ.fraction.f ≫ p = CofibrantObject.homMk (qX ≫ f) := by
    ext; exact φ.numerator
  rw [← hs, F.map_comp, ← Category.assoc]
  change (φ.fraction.map F hF ≫ F.map φ.fraction.s) ≫ F.map p = _
  rw [φ.fraction.map_comp_map_s, ← F.map_comp, hf]

end ReplacementFraction

/-- A replacement fraction chosen independently for each ambient arrow. -/
noncomputable def chosenReplacementFraction
    {A B : C} {X Y : CofibrantObject C} (qX : X.obj ⟶ A) (qY : Y.obj ⟶ B)
    [WeakEquivalence qY] (f : A ⟶ B) : ReplacementFraction qX qY f :=
  Classical.choice (ReplacementFraction.nonempty qX qY f)

/-- Chosen object replacements extend any weak-equivalence-inverting functor
on cofibrant objects to the ambient category. Independence of fraction choices
supplies the identity and composition laws. -/
noncomputable def replacementFunctor
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A))
    {D : Type u'} [Category.{v'} D] (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) : C ⥤ D := by
  letI (A : C) : WeakEquivalence (q A) := hq A
  exact {
    obj A := F.obj (Q A)
    map {A B} f := (chosenReplacementFraction (q A) (q B) f).map F hF
    map_id A := by
      let ψ : ReplacementFraction (q A) (q A) (𝟙 A) :=
        ReplacementFraction.ofHom (𝟙 (Q A)) (by simp)
      rw [ReplacementFraction.map_eq _ ψ F hF]
      simpa [ψ] using ReplacementFraction.map_ofHom (𝟙 (Q A)) (by simp) F hF
    map_comp {A B E} f g := by
      let φ := chosenReplacementFraction (q A) (q B) f
      let ψ := chosenReplacementFraction (q B) (q E) g
      rw [ReplacementFraction.map_eq _ (φ.comp ψ) F hF]
      exact ReplacementFraction.map_comp φ ψ F hF }

/-- The extension to the ambient category inverts its weak equivalences. -/
theorem replacementFunctor_inverts
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A))
    {D : Type u'} [Category.{v'} D] (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    (weakEquivalences C).IsInvertedBy (replacementFunctor Q q hq F hF) := by
  intro A B f hf
  let (A : C) : WeakEquivalence (q A) := hq A
  let : WeakEquivalence f := ⟨hf⟩
  exact ReplacementFraction.isIso_map_of_weakEquivalence
    (chosenReplacementFraction (q A) (q B) f) F hF

/-- A functor in the reverse direction on localizations, relative to chosen
object replacements. Its inverse comparisons are in `ReplacementComparison.lean`. -/
noncomputable def ambientLocalizationToCofibrant
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A)) :
    (weakEquivalences C).Localization ⥤
      (weakEquivalences (CofibrantObject C)).Localization :=
  let F := (weakEquivalences (CofibrantObject C)).Q
  let hF := (inverts_weakEquivalences_iff_inverts_trivialCofibrations F).1
    (weakEquivalences (CofibrantObject C)).Q_inverts
  Localization.lift (replacementFunctor Q q hq F hF)
    (replacementFunctor_inverts Q q hq F hF) (weakEquivalences C).Q

/-- Restricting the replacement extension back to cofibrant objects recovers
the original functor up to a natural isomorphism. Its components are the
images of the chosen replacement weak equivalences. -/
noncomputable def replacementFunctorRestrictionIso
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A))
    {D : Type u'} [Category.{v'} D] (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    CofibrantObject.ι ⋙ replacementFunctor Q q hq F hF ≅ F := by
  letI (A : C) : WeakEquivalence (q A) := hq A
  let e (X : CofibrantObject C) : F.obj (Q X.obj) ≅ F.obj X := by
    let i : Q X.obj ⟶ X := CofibrantObject.homMk (q X.obj)
    let : IsIso (F.map i) :=
      ((inverts_weakEquivalences_iff_inverts_trivialCofibrations F).2 hF)
        i (hq X.obj).mem
    exact asIso (F.map i)
  refine NatIso.ofComponents e ?_
  intro X Y f
  change (chosenReplacementFraction (q X.obj) (q Y.obj) f.hom).map F hF ≫
    F.map (CofibrantObject.homMk (q Y.obj)) =
      F.map (CofibrantObject.homMk (q X.obj)) ≫ F.map f
  rw [ReplacementFraction.map_comp_comparison, ← F.map_comp]
  rfl

end ABCCofibrations.ABCPrecofibrationCategory

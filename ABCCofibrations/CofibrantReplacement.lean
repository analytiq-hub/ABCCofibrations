/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyLocalization
public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.IsConnected

/-!
# Cofibrant replacements and the ambient localization

First steps toward Theorem 6.1.6: inclusion of cofibrant objects induces a
comparison on localizations, and every ambient object is in its essential
image. Replacements extend across individual arrows and any two replacements
admit a common cofibrant extension. No functorial replacement is assumed.
Full faithfulness of the comparison is not asserted here.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- Inclusion of cofibrant objects preserves weak equivalences. -/
def cofibrantInclusionLocalizerMorphism :
    LocalizerMorphism (weakEquivalences (CofibrantObject C)) (weakEquivalences C) where
  functor := CofibrantObject.ι
  map _ _ _ hf := hf

/-- Cofibrant replacements are left resolutions for the inclusion. -/
instance cofibrantInclusion_hasLeftResolutions :
    (cofibrantInclusionLocalizerMorphism (C := C)).HasLeftResolutions := by
  intro X
  obtain ⟨Q, q, hQ, hq⟩ := exists_cofibrant_replacement X
  let := hQ
  exact ⟨{ X₁ := CofibrantObject.mk Q, w := q, hw := hq.mem }⟩

/-- The canonical comparison to the localization of the ambient category. -/
noncomputable def cofibrantLocalizationToAmbient :
    (weakEquivalences (CofibrantObject C)).Localization ⥤
      (weakEquivalences C).Localization :=
  (cofibrantInclusionLocalizerMorphism (C := C)).localizedFunctor
    (weakEquivalences (CofibrantObject C)).Q (weakEquivalences C).Q

/-- Every object of the ambient localization is represented by a cofibrant
object. This is the object part of Theorem 6.1.6. -/
theorem cofibrantInclusion_localization_essSurj :
    (CofibrantObject.ι ⋙ (weakEquivalences C).Q).EssSurj :=
  (cofibrantInclusionLocalizerMorphism (C := C)).essSurj_of_hasLeftResolutions _

/-- The induced comparison on localizations is essentially surjective. -/
instance cofibrantLocalizationToAmbient_essSurj :
    (cofibrantLocalizationToAmbient (C := C)).EssSurj := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let G := Φ.localizedFunctor
    (weakEquivalences (CofibrantObject C)).Q (weakEquivalences C).Q
  change G.EssSurj
  let : (Φ.functor ⋙ (weakEquivalences C).Q).EssSurj :=
    cofibrantInclusion_localization_essSurj (C := C)
  let e := CatCommSq.iso
    Φ.functor
    (weakEquivalences (CofibrantObject C)).Q (weakEquivalences C).Q
    (Φ.localizedFunctor (weakEquivalences (CofibrantObject C)).Q (weakEquivalences C).Q)
  have h := Functor.essSurj_of_iso e
  exact ⟨fun X ↦ by
    obtain ⟨Q, ⟨i⟩⟩ := h.mem_essImage X
    exact ⟨(weakEquivalences (CofibrantObject C)).Q.obj Q, ⟨i⟩⟩⟩

/-- Extend a prescribed source replacement across an arbitrary ambient arrow.
The resulting arrow between cofibrant objects can be chosen a cofibration. -/
theorem exists_cofibrant_replacement_arrow {A B Q : C} [IsCofibrant Q]
    (q : Q ⟶ A) [WeakEquivalence q] (f : A ⟶ B) :
    ∃ (R : C) (i : Q ⟶ R) (r : R ⟶ B),
      IsCofibrant R ∧ Cofibration i ∧ WeakEquivalence r ∧ i ≫ r = q ≫ f := by
  obtain ⟨R, i, r, hi, hr, h⟩ := factorization (q ≫ f)
  let := hi
  exact ⟨R, i, r, cofibrant_target i, hi, hr, h⟩

/-- Two cofibrant replacements of the same object admit a common extension
over it, with both comparison maps trivial cofibrations. -/
theorem exists_common_cofibrant_replacement {X Q₁ Q₂ : C}
    [IsCofibrant Q₁] [IsCofibrant Q₂]
    (q₁ : Q₁ ⟶ X) (q₂ : Q₂ ⟶ X) [WeakEquivalence q₁] [WeakEquivalence q₂] :
    ∃ (R : C) (i₁ : Q₁ ⟶ R) (i₂ : Q₂ ⟶ R) (r : R ⟶ X),
      IsCofibrant R ∧ Cofibration i₁ ∧ WeakEquivalence i₁ ∧
        Cofibration i₂ ∧ WeakEquivalence i₂ ∧ WeakEquivalence r ∧
        i₁ ≫ r = q₁ ∧ i₂ ≫ r = q₂ := by
  let := hasBinaryCoproduct Q₁ Q₂
  let : IsCofibrant (Q₁ ⨿ Q₂) := coprod_cofibrant
  let := cofibration_coprod_inl (A := Q₁) (B := Q₂)
  let := cofibration_coprod_inr (A := Q₁) (B := Q₂)
  obtain ⟨R, i, r, hi, hr, h⟩ := factorization (coprod.desc q₁ q₂)
  let := hi
  let := hr
  have h₁ : (coprod.inl ≫ i) ≫ r = q₁ := by simp [Category.assoc, h]
  have h₂ : (coprod.inr ≫ i) ≫ r = q₂ := by simp [Category.assoc, h]
  exact ⟨R, coprod.inl ≫ i, coprod.inr ≫ i, r, cofibrant_target i,
    inferInstance, weakEquivalence_of_postcomp_of_fac h₁,
    inferInstance, weakEquivalence_of_postcomp_of_fac h₂, hr, h₁, h₂⟩

/-- Every map over the ambient object between its cofibrant replacements is
a weak equivalence, by two out of three. -/
theorem weakEquivalence_leftResolution_hom {X : C}
    {R S : (cofibrantInclusionLocalizerMorphism (C := C)).LeftResolution X}
    (f : R ⟶ S) : WeakEquivalence f.f.hom := by
  let : WeakEquivalence (show R.X₁.obj ⟶ X from R.w) := ⟨R.hw⟩
  let : WeakEquivalence (show S.X₁.obj ⟶ X from S.w) := ⟨S.hw⟩
  have h : f.f.hom ≫ S.w = R.w := f.comm
  exact weakEquivalence_of_postcomp_of_fac h

/-- The category of cofibrant replacements over any ambient object is
connected: two replacements map to their common extension. -/
instance cofibrantInclusion_leftResolution_isConnected (X : C) :
    IsConnected ((cofibrantInclusionLocalizerMorphism (C := C)).LeftResolution X) := by
  apply zigzag_isConnected
  intro R S
  let : WeakEquivalence R.w := ⟨R.hw⟩
  let : WeakEquivalence S.w := ⟨S.hw⟩
  let : IsCofibrant ((cofibrantInclusionLocalizerMorphism (C := C)).functor.obj R.X₁) :=
    inferInstanceAs (IsCofibrant R.X₁.obj)
  let : IsCofibrant ((cofibrantInclusionLocalizerMorphism (C := C)).functor.obj S.X₁) :=
    inferInstanceAs (IsCofibrant S.X₁.obj)
  obtain ⟨T, i, j, t, hT, _, _, _, _, ht, hi, hj⟩ :=
    exists_common_cofibrant_replacement R.w S.w
  let := hT
  let U : (cofibrantInclusionLocalizerMorphism (C := C)).LeftResolution X :=
    { X₁ := CofibrantObject.mk T, w := t, hw := ht.mem }
  let a : R ⟶ U := { f := CofibrantObject.homMk i, comm := hi }
  let b : S ⟶ U := { f := CofibrantObject.homMk j, comm := hj }
  exact Zigzag.of_hom_inv a b

/-- Every arrow of the ambient category has a left resolution by an arrow
between cofibrant objects. Both vertical maps in the resolution square are
weak equivalences. -/
instance cofibrantInclusion_arrow_hasLeftResolutions :
    (cofibrantInclusionLocalizerMorphism (C := C)).arrow.HasLeftResolutions := by
  intro f
  obtain ⟨Q, q, hQ, hq⟩ := exists_cofibrant_replacement f.left
  let := hQ
  let := hq
  obtain ⟨R, i, r, hR, _, hr, h⟩ := exists_cofibrant_replacement_arrow q f.hom
  let := hR
  exact ⟨{
    X₁ := Arrow.mk (CofibrantObject.homMk i)
    w := Arrow.homMk q r h.symm
    hw := ⟨hq.mem, hr.mem⟩ }⟩

end ABCCofibrations.ABCPrecofibrationCategory

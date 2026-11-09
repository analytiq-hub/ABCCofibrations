/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximationHomotopy

/-!
# Fractions between prescribed resolutions of a cofibrant approximation

The arrow construction in Theorem 6.1.5(1): CFA4 applied to a source sum
produces a fraction over any ambient arrow. Both legs are cofibrations,
so later pushout composition uses CFA3 only in its stated scope.
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

/-- A source fraction over an ambient arrow, retaining both prescribed
resolutions. Cofibrancy of both legs permits preservation of the pushouts
used for composition without strengthening CFA3. -/
structure ResolutionFraction {A B : D} {X Y : C}
    (qX : F.obj X ⟶ A) (qY : F.obj Y ⟶ B) (f : A ⟶ B) where
  fraction : (weakEquivalences C).LeftFraction X Y
  numerator_cofibration : Cofibration fraction.f
  denominator_cofibration : Cofibration fraction.s
  comparison : F.obj fraction.Y' ⟶ B
  comparison_weakEquivalence : WeakEquivalence comparison
  numerator : F.map fraction.f ≫ comparison = qX ≫ f
  denominator : F.map fraction.s ≫ comparison = qY

attribute [instance] ResolutionFraction.numerator_cofibration
  ResolutionFraction.denominator_cofibration ResolutionFraction.comparison_weakEquivalence

namespace ResolutionFraction

/-- CFA4 on the preserved source sum gives a fraction between prescribed
resolutions. Only the target resolution needs to be a weak equivalence. -/
theorem nonempty {A B : D} {X Y : C}
    (qX : F.obj X ⟶ A) (qY : F.obj Y ⟶ B) [WeakEquivalence qY]
    (f : A ⟶ B) : Nonempty (ResolutionFraction F qX qY f) := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  let a := initial.to X
  let b := initial.to Y
  let sq := IsPushout.of_hasPushout a b
  let := cofibration_of_isPushout sq
  let := cofibration_of_isPushout sq.flip
  let fsq := map_isPushout (F := F) sq
  let h₀ := isColimitOfHasInitialOfPreservesColimit F
  have h : F.map a ≫ (qX ≫ f) = F.map b ≫ qY := h₀.hom_ext _ _
  let u := fsq.desc (qX ≫ f) qY h
  obtain ⟨Z, k, p, hk, hp, hkp⟩ := factorization (F := F) u
  let := hk
  let := hp
  have hn : F.map (pushout.inl a b ≫ k) ≫ p = qX ≫ f := by
    rw [F.map_comp, Category.assoc, hkp]
    exact fsq.inl_desc (qX ≫ f) qY h
  have hd : F.map (pushout.inr a b ≫ k) ≫ p = qY := by
    rw [F.map_comp, Category.assoc, hkp]
    exact fsq.inr_desc (qX ≫ f) qY h
  have hw : WeakEquivalence (pushout.inr a b ≫ k) :=
    (weakEquivalence_map_iff (F := F) _).1 (weakEquivalence_of_postcomp_of_fac hd)
  exact ⟨{
    fraction := { f := pushout.inl a b ≫ k, s := pushout.inr a b ≫ k, hs := hw.mem }
    numerator_cofibration := inferInstance
    denominator_cofibration := inferInstance
    comparison := p
    comparison_weakEquivalence := hp
    numerator := hn
    denominator := hd }⟩

variable {F} {A B : D} {X Y : C}
  {qX : F.obj X ⟶ A} {qY : F.obj Y ⟶ B} {f : A ⟶ B}
  {E : Type*} [Category E]

/-- The value of a resolution fraction under a source functor inverting
weak equivalences. -/
noncomputable def map (φ : ResolutionFraction F qX qY f)
    (G : C ⥤ E) (hG : (weakEquivalences C).IsInvertedBy G) :
    G.obj X ⟶ G.obj Y := φ.fraction.map G hG

/-- The value is independent of the chosen fraction, by Lemma 6.1.4(1). -/
theorem map_eq (φ ψ : ResolutionFraction F qX qY f)
    (G : C ⥤ E) (hG : (weakEquivalences C).IsInvertedBy G) :
    φ.map G hG = ψ.map G hG :=
  fraction_map_eq_of_ambient_comparison F φ.fraction ψ.fraction
    φ.comparison ψ.comparison (φ.numerator.trans ψ.numerator.symm)
    (φ.denominator.trans ψ.denominator.symm) G hG

/-- A fraction over an actual source map computes to the image of that map.
The map itself need not be a cofibration. -/
theorem map_eq_of_hom [WeakEquivalence qY] (φ : ResolutionFraction F qX qY f)
    (i : X ⟶ Y) (hi : F.map i ≫ qY = qX ≫ f)
    (G : C ⥤ E) (hG : (weakEquivalences C).IsInvertedBy G) :
    φ.map G hG = G.map i := by
  let ψ : (weakEquivalences C).LeftFraction X Y :=
    { f := i, s := 𝟙 Y, hs := (weakEquivalence_of_isIso (𝟙 Y)).mem }
  have h := fraction_map_eq_of_ambient_comparison F φ.fraction ψ
    φ.comparison qY (φ.numerator.trans hi.symm)
    (by simpa [ψ] using φ.denominator) G hG
  have he := ψ.map_comp_map_s G hG
  simpa [map, ψ] using h.trans (by simpa [ψ] using he)

variable {T : D} {Z : C} {qZ : F.obj Z ⟶ T} {g : B ⟶ T}

/-- Pushout composition of resolution fractions. Both legs of the preserved
span are cofibrations, as required by CFA3. -/
noncomputable def comp (φ : ResolutionFraction F qX qY f)
    (ψ : ResolutionFraction F qY qZ g) : ResolutionFraction F qX qZ (f ≫ g) := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  let : WeakEquivalence φ.fraction.s := ⟨φ.fraction.hs⟩
  let : WeakEquivalence ψ.fraction.s := ⟨ψ.fraction.hs⟩
  let sq := IsPushout.of_hasPushout φ.fraction.s ψ.fraction.f
  let := cofibration_of_isPushout sq
  let := weakEquivalence_of_isPushout sq
  let := cofibration_of_isPushout sq.flip
  let fsq := map_isPushout (F := F) sq
  have h : F.map φ.fraction.s ≫ (φ.comparison ≫ g) =
      F.map ψ.fraction.f ≫ ψ.comparison := by
    rw [← Category.assoc, φ.denominator, ψ.numerator]
  let r := fsq.desc (φ.comparison ≫ g) ψ.comparison h
  have hr : WeakEquivalence r := by
    let := map_weakEquivalence F (pushout.inr φ.fraction.s ψ.fraction.f)
    exact weakEquivalence_of_precomp_of_fac (fsq.inr_desc _ _ h)
  exact {
    fraction := {
      f := φ.fraction.f ≫ pushout.inl _ _
      s := ψ.fraction.s ≫ pushout.inr _ _
      hs := (show WeakEquivalence (ψ.fraction.s ≫ pushout.inr _ _) from inferInstance).mem }
    numerator_cofibration := inferInstance
    denominator_cofibration := inferInstance
    comparison := r
    comparison_weakEquivalence := hr
    numerator := by
      simp only [F.map_comp, Category.assoc, r, fsq.inl_desc]
      rw [← Category.assoc, φ.numerator, Category.assoc]
    denominator := by
      simp only [F.map_comp, Category.assoc, r, fsq.inr_desc, ψ.denominator] }

/-- The value of the pushout composite is the composite of the values. -/
theorem map_comp (φ : ResolutionFraction F qX qY f)
    (ψ : ResolutionFraction F qY qZ g)
    (G : C ⥤ E) (hG : (weakEquivalences C).IsInvertedBy G) :
    (φ.comp ψ).map G hG = φ.map G hG ≫ ψ.map G hG := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  let χ := φ.comp ψ
  let := hG _ χ.fraction.hs
  apply (cancel_mono (G.map χ.fraction.s)).1
  rw [show χ.map G hG ≫ G.map χ.fraction.s = G.map χ.fraction.f from
    χ.fraction.map_comp_map_s G hG]
  change G.map (φ.fraction.f ≫ pushout.inl _ _) =
    (φ.fraction.map G hG ≫ ψ.fraction.map G hG) ≫
      G.map (ψ.fraction.s ≫ pushout.inr _ _)
  calc
    G.map (φ.fraction.f ≫ pushout.inl _ _) =
        φ.fraction.map G hG ≫ G.map (φ.fraction.s ≫ pushout.inl _ _) := by
      rw [G.map_comp, G.map_comp, ← Category.assoc, φ.fraction.map_comp_map_s]
    _ = φ.fraction.map G hG ≫ G.map (ψ.fraction.f ≫ pushout.inr _ _) := by
      rw [(IsPushout.of_hasPushout φ.fraction.s ψ.fraction.f).w]
    _ = (φ.fraction.map G hG ≫ ψ.fraction.map G hG) ≫
        G.map (ψ.fraction.s ≫ pushout.inr _ _) := by
      simp only [G.map_comp, Category.assoc]
      rw [← Category.assoc (ψ.fraction.map G hG), ψ.fraction.map_comp_map_s]

/-- An ambient weak equivalence is represented by an invertible arrow. -/
theorem isIso_map_of_weakEquivalence [WeakEquivalence qX] [WeakEquivalence f]
    (φ : ResolutionFraction F qX qY f)
    (G : C ⥤ E) (hG : (weakEquivalences C).IsInvertedBy G) :
    IsIso (φ.map G hG) := by
  have hw : WeakEquivalence (F.map φ.fraction.f) :=
    weakEquivalence_of_postcomp_of_fac φ.numerator
  have hw' := (weakEquivalence_map_iff (F := F) φ.fraction.f).1 hw
  let := hG φ.fraction.f hw'.mem
  let := hG _ φ.fraction.hs
  change IsIso (G.map φ.fraction.f ≫ inv (G.map φ.fraction.s))
  infer_instance

end ResolutionFraction
/-- Fractions between arbitrary prescribed resolutions give a functor on the
ambient category. No functorial resolution or factorization is assumed. -/
noncomputable def resolutionFunctor
    (Q : D → C) (q : ∀ A, F.obj (Q A) ⟶ A) [∀ A, WeakEquivalence (q A)]
    {E : Type*} [Category E] (G : C ⥤ E)
    (hG : (weakEquivalences C).IsInvertedBy G) : D ⥤ E where
  obj A := G.obj (Q A)
  map {A B} f := (Classical.choice (ResolutionFraction.nonempty F (q A) (q B) f)).map G hG
  map_id A := by
    rw [ResolutionFraction.map_eq_of_hom _ (𝟙 (Q A)) (by simp) G hG, G.map_id]
  map_comp {A B T} f g := by
    let φ := Classical.choice (ResolutionFraction.nonempty F (q A) (q B) f)
    let ψ := Classical.choice (ResolutionFraction.nonempty F (q B) (q T) g)
    exact (ResolutionFraction.map_eq _ (φ.comp ψ) G hG).trans (φ.map_comp ψ G hG)

/-- The resolution functor inverts ambient weak equivalences, and can
therefore be lifted from an ambient localization. -/
theorem resolutionFunctor_inverts
    (Q : D → C) (q : ∀ A, F.obj (Q A) ⟶ A) [∀ A, WeakEquivalence (q A)]
    {E : Type*} [Category E] (G : C ⥤ E)
    (hG : (weakEquivalences C).IsInvertedBy G) :
    (weakEquivalences D).IsInvertedBy (resolutionFunctor F Q q G hG) := by
  intro A B f hf
  let : WeakEquivalence f := ⟨hf⟩
  exact ResolutionFraction.isIso_map_of_weakEquivalence _ G hG

end ABCCofibrations.IsCofibrantApproximation

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.TrivialCofibrationLocalization
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-!
# Left-fraction representations

Pushouts suffice to represent localization morphisms by cospans with a
trivial-cofibration denominator. No cancellation axiom is needed here.
-/

public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Two trivial-cofibration denominators with the same source have a
common extension, with both comparison maps again trivial cofibrations. -/
theorem exists_common_trivialCofibration_denominator
    {Y A B : CofibrantObject C} (s : Y ⟶ A) (t : Y ⟶ B)
    (hs : cofibrantTrivialCofibrations s) (ht : cofibrantTrivialCofibrations t) :
    ∃ (P : CofibrantObject C) (i : A ⟶ P) (j : B ⟶ P),
      cofibrantTrivialCofibrations i ∧ cofibrantTrivialCofibrations j ∧
        s ≫ i = t ≫ j := by
  obtain ⟨hcs, hws⟩ := (mem_cofibrantTrivialCofibrations_iff s).1 hs
  obtain ⟨hct, hwt⟩ := (mem_cofibrantTrivialCofibrations_iff t).1 ht
  let := hcs
  let := hws
  let := hct
  let := hwt
  let h := IsPushout.of_hasPushout s.hom t.hom
  let := cofibration_of_isPushout h
  let := weakEquivalence_of_isPushout h
  let := cofibration_of_isPushout h.flip
  let := weakEquivalence_of_isPushout h.flip
  let := cofibrant_target (pushout.inr s.hom t.hom)
  refine ⟨CofibrantObject.mk (pushout s.hom t.hom),
    CofibrantObject.homMk (pushout.inl s.hom t.hom),
    CofibrantObject.homMk (pushout.inr s.hom t.hom), ?_, ?_, ?_⟩
  · apply (mem_cofibrantTrivialCofibrations_iff _).2
    change Cofibration (pushout.inl s.hom t.hom) ∧ WeakEquivalence (pushout.inl s.hom t.hom)
    exact ⟨inferInstance, inferInstance⟩
  · apply (mem_cofibrantTrivialCofibrations_iff _).2
    change Cofibration (pushout.inr s.hom t.hom) ∧ WeakEquivalence (pushout.inr s.hom t.hom)
    exact ⟨inferInstance, inferInstance⟩
  · ext
    exact h.w

omit [ABCPrecofibrationCategory C] in
/-- Over a common denominator, equality of fractions is exactly equality
of the images of their extended numerators. -/
theorem trivialCofibration_fraction_map_eq_iff
    {X Y P : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : cofibrantTrivialCofibrations i) (hj : cofibrantTrivialCofibrations j)
    (sq : φ.s ≫ i = ψ.s ≫ j)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF ↔ F.map (φ.f ≫ i) = F.map (ψ.f ≫ j) := by
  let := hF _ φ.hs
  let := hF _ hi
  let := hF _ hj
  have hφ : φ.map F hF ≫ F.map (φ.s ≫ i) = F.map (φ.f ≫ i) := by
    simp only [F.map_comp]
    rw [← Category.assoc, φ.map_comp_map_s]
  have hψ : ψ.map F hF ≫ F.map (φ.s ≫ i) = F.map (ψ.f ≫ j) := by
    rw [sq]
    simp only [F.map_comp]
    rw [← Category.assoc, ψ.map_comp_map_s]
  have : IsIso (F.map (φ.s ≫ i)) := by rw [F.map_comp]; infer_instance
  rw [← cancel_mono (F.map (φ.s ≫ i)), hφ, hψ]

omit [ABCPrecofibrationCategory C] in
/-- Strict equality of extended numerators suffices to identify fractions
under every functor inverting trivial cofibrations. -/
theorem trivialCofibration_fraction_map_eq_of_common_extension
    {X Y P : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (i : φ.Y' ⟶ P) (j : ψ.Y' ⟶ P)
    (hi : cofibrantTrivialCofibrations i) (hj : cofibrantTrivialCofibrations j)
    (hs : φ.s ≫ i = ψ.s ≫ j) (hf : φ.f ≫ i = ψ.f ≫ j)
    (F : CofibrantObject C ⥤ D)
    (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF :=
  (trivialCofibration_fraction_map_eq_iff φ ψ i j hi hj hs F hF).2
    (congrArg (fun f ↦ F.map f) hf)

/-- Two composable fractions admit a composite fraction computed by an
Ore square. The formula holds for every functor inverting trivial
cofibrations, independently of a chosen localization. -/
theorem exists_trivialCofibration_fraction_comp
    {X Y Z : CofibrantObject C}
    (φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y)
    (ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction Y Z) :
    ∃ χ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Z,
      ∀ (F : CofibrantObject C ⥤ D)
        (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F),
        χ.map F hF = φ.map F hF ≫ ψ.map F hF := by
  obtain ⟨P, k, t, ht, sq⟩ := exists_trivialCofibration_ore_square φ.s ψ.f φ.hs
  obtain ⟨hcs, hws⟩ := (mem_cofibrantTrivialCofibrations_iff ψ.s).1 ψ.hs
  obtain ⟨hct, hwt⟩ := (mem_cofibrantTrivialCofibrations_iff t).1 ht
  let := hcs
  let := hws
  let := hct
  let := hwt
  have hst : cofibrantTrivialCofibrations (ψ.s ≫ t) := by
    apply (mem_cofibrantTrivialCofibrations_iff _).2
    change Cofibration (ψ.s.hom ≫ t.hom) ∧ WeakEquivalence (ψ.s.hom ≫ t.hom)
    exact ⟨inferInstance, inferInstance⟩
  let χ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Z :=
    ⟨φ.f ≫ k, ψ.s ≫ t, hst⟩
  refine ⟨χ, fun F hF ↦ ?_⟩
  let := hF _ hst
  apply (cancel_mono (F.map χ.s)).1
  rw [χ.map_comp_map_s]
  change F.map (φ.f ≫ k) = (φ.map F hF ≫ ψ.map F hF) ≫ F.map (ψ.s ≫ t)
  calc
    F.map (φ.f ≫ k) = φ.map F hF ≫ F.map (φ.s ≫ k) := by
      simp only [F.map_comp]
      rw [← Category.assoc, φ.map_comp_map_s]
    _ = φ.map F hF ≫ F.map (ψ.f ≫ t) := by rw [sq]
    _ = (φ.map F hF ≫ ψ.map F hF) ≫ F.map (ψ.s ≫ t) := by
      simp only [F.map_comp, Category.assoc]
      rw [← Category.assoc (ψ.map F hF), ψ.map_comp_map_s]

/-- Every localized arrow is represented by a cospan whose backward arrow
is a trivial cofibration. The equation avoids choosing an inverse explicitly. -/
theorem exists_trivialCofibration_fraction
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (cofibrantTrivialCofibrations (C := C))]
    {X Y : CofibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : CofibrantObject C) (f : X ⟶ Z) (s : Y ⟶ Z),
      cofibrantTrivialCofibrations s ∧ α ≫ L.map s = L.map f := by
  let T := cofibrantTrivialCofibrations (C := C)
  let P : StructuredArrow (L.obj X) L → Prop := fun a ↦
    ∃ (Z : CofibrantObject C) (f : X ⟶ Z) (s : a.right ⟶ Z),
      T s ∧ a.hom ≫ L.map s = L.map f
  change P (StructuredArrow.mk α)
  apply Localization.induction_structuredArrow L T P
  · refine ⟨X, 𝟙 X, 𝟙 X, ?_, by simp⟩
    apply (mem_cofibrantTrivialCofibrations_iff _).2
    exact ⟨cofibration_of_isIso (𝟙 X.obj), weakEquivalence_of_isIso (𝟙 X.obj)⟩
  · intro Y₁ Y₂ g β hβ
    obtain ⟨Z, f, s, hs, h⟩ := hβ
    change β ≫ L.map s = L.map f at h
    obtain ⟨Z', k, t, ht, sq⟩ := exists_trivialCofibration_ore_square s g hs
    refine ⟨Z', f ≫ k, t, ht, ?_⟩
    change (β ≫ L.map g) ≫ L.map t = L.map (f ≫ k)
    rw [Category.assoc, ← L.map_comp, ← sq, L.map_comp,
      ← Category.assoc, h, ← L.map_comp]
  · intro Y₁ Y₂ w hw β hβ
    obtain ⟨Z, f, s, hs, h⟩ := hβ
    change β ≫ L.map s = L.map f at h
    obtain ⟨hcw, hew⟩ := (mem_cofibrantTrivialCofibrations_iff w).1 hw
    obtain ⟨hcs, hes⟩ := (mem_cofibrantTrivialCofibrations_iff s).1 hs
    let := hcw
    let := hew
    let := hcs
    let := hes
    refine ⟨Z, f, w ≫ s, ?_, ?_⟩
    · apply (mem_cofibrantTrivialCofibrations_iff _).2
      change Cofibration (w.hom ≫ s.hom) ∧ WeakEquivalence (w.hom ≫ s.hom)
      exact ⟨inferInstance, inferInstance⟩
    · change (β ≫ (Localization.isoOfHom L T w hw).inv) ≫ L.map (w ≫ s) = _
      rw [L.map_comp, Category.assoc, ← Category.assoc
        (Localization.isoOfHom L T w hw).inv]
      simpa using h

/-- The cospan representation, expressed using mathlib's fraction type. -/
theorem exists_leftFraction_trivialCofibration
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (cofibrantTrivialCofibrations (C := C))]
    {X Y : CofibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y,
      φ.map L (Localization.inverts L _) = α := by
  obtain ⟨Z, f, s, hs, h⟩ := exists_trivialCofibration_fraction L α
  let φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y := ⟨f, s, hs⟩
  let := Localization.inverts L (cofibrantTrivialCofibrations (C := C)) s hs
  refine ⟨φ, (cancel_mono (L.map s)).1 ?_⟩
  rw [φ.map_comp_map_s, h]

/-- The fraction representation applies directly to any localization at
all weak equivalences of cofibrant objects. Its denominator can still be
chosen to be a trivial cofibration. -/
theorem exists_trivialCofibration_fraction_of_weakEquivalence_localization
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences (CofibrantObject C))]
    {X Y : CofibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : CofibrantObject C) (f : X ⟶ Z) (s : Y ⟶ Z),
      cofibrantTrivialCofibrations s ∧ α ≫ L.map s = L.map f := by
  let := isLocalization_trivialCofibrations_of_weakEquivalences L
  exact exists_trivialCofibration_fraction L α

/-- The same statement in the explicit left-fraction notation, for
localization at weak equivalences. -/
theorem exists_leftFraction_of_weakEquivalence_localization
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences (CofibrantObject C))]
    {X Y : CofibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ φ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y,
      φ.map L ((inverts_weakEquivalences_iff_inverts_trivialCofibrations L).1
        (Localization.inverts L (weakEquivalences (CofibrantObject C)))) = α := by
  let := isLocalization_trivialCofibrations_of_weakEquivalences L
  exact exists_leftFraction_trivialCofibration L α

/-- Parallel fractions can be put over a single trivial-cofibration
denominator. The common representation works for every inverting functor. -/
theorem exists_parallel_trivialCofibration_fractions
    {X Y : CofibrantObject C}
    (φ ψ : (cofibrantTrivialCofibrations (C := C)).LeftFraction X Y) :
    ∃ (P : CofibrantObject C) (f g : X ⟶ P) (s : Y ⟶ P),
      cofibrantTrivialCofibrations s ∧
      ∀ (F : CofibrantObject C ⥤ D)
        (hF : (cofibrantTrivialCofibrations (C := C)).IsInvertedBy F),
        (φ.map F hF ≫ F.map s = F.map f) ∧
        (ψ.map F hF ≫ F.map s = F.map g) := by
  obtain ⟨P, i, j, hi, hj, sq⟩ :=
    exists_common_trivialCofibration_denominator φ.s ψ.s φ.hs ψ.hs
  obtain ⟨hcs, hws⟩ := (mem_cofibrantTrivialCofibrations_iff φ.s).1 φ.hs
  obtain ⟨hci, hwi⟩ := (mem_cofibrantTrivialCofibrations_iff i).1 hi
  let := hcs
  let := hws
  let := hci
  let := hwi
  have hs : cofibrantTrivialCofibrations (φ.s ≫ i) := by
    apply (mem_cofibrantTrivialCofibrations_iff _).2
    change Cofibration (φ.s.hom ≫ i.hom) ∧ WeakEquivalence (φ.s.hom ≫ i.hom)
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨P, φ.f ≫ i, ψ.f ≫ j, φ.s ≫ i, hs, fun F hF ↦ ⟨?_, ?_⟩⟩
  · simp only [F.map_comp]
    rw [← Category.assoc, φ.map_comp_map_s]
  · rw [sq]
    simp only [F.map_comp]
    rw [← Category.assoc, ψ.map_comp_map_s]

/-- Two parallel arrows in a weak-equivalence localization have a common
trivial-cofibration denominator. -/
theorem exists_common_fraction_of_weakEquivalence_localization
    (L : CofibrantObject C ⥤ D)
    [L.IsLocalization (weakEquivalences (CofibrantObject C))]
    {X Y : CofibrantObject C} (α β : L.obj X ⟶ L.obj Y) :
    ∃ (P : CofibrantObject C) (f g : X ⟶ P) (s : Y ⟶ P),
      cofibrantTrivialCofibrations s ∧
        α ≫ L.map s = L.map f ∧ β ≫ L.map s = L.map g := by
  let := isLocalization_trivialCofibrations_of_weakEquivalences L
  obtain ⟨φ, hφ⟩ := exists_leftFraction_trivialCofibration L α
  obtain ⟨ψ, hψ⟩ := exists_leftFraction_trivialCofibration L β
  obtain ⟨P, f, g, s, hs, h⟩ := exists_parallel_trivialCofibration_fractions (D := D) φ ψ
  refine ⟨P, f, g, s, hs, ?_⟩
  simpa only [hφ, hψ] using h L (Localization.inverts L _)

end ABCCofibrations.ABCPrecofibrationCategory

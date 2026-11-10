/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Transport of a precofibration structure along an equivalence

If `E : D ≌ D'` is an equivalence of categories, `D'` is a precofibration
category, and the cofibrations and weak equivalences of `D` are exactly the
maps sent to cofibrations and weak equivalences of `D'`, then `D` is a
precofibration category.

This is used to deduce the fibration statements about over and under
categories (Proposition 1.7.1(2)) from the cofibration statements, through
mathlib's equivalences `(Under A)ᵒᵖ ≌ Over (op A)` and `(Over A)ᵒᵖ ≌ Under (op A)`.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {D : Type u} [Category.{v} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D]
  {D' : Type u'} [Category.{v'} D'] [CategoryWithCofibrations D']
  [CategoryWithWeakEquivalences D'] [HasInitial D'] [ABCPrecofibrationCategory D']
  (E : D ≌ D')
  (hcof : cofibrations D = (cofibrations D').inverseImage E.functor)
  (hweq : weakEquivalences D = (weakEquivalences D').inverseImage E.functor)

include hcof in
omit [CategoryWithWeakEquivalences D] [CategoryWithWeakEquivalences D'] [HasInitial D]
  [HasInitial D'] [ABCPrecofibrationCategory D'] in
theorem cofibration_iff_of_equivalence {X Y : D} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration (E.functor.map f) := by
  rw [cofibration_iff, cofibration_iff, hcof]
  rfl

include hweq in
omit [CategoryWithCofibrations D] [CategoryWithCofibrations D'] [HasInitial D]
  [HasInitial D'] [ABCPrecofibrationCategory D'] in
theorem weakEquivalence_iff_of_equivalence {X Y : D} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence (E.functor.map f) := by
  rw [weakEquivalence_iff, weakEquivalence_iff, hweq]
  rfl

include hcof in
omit [CategoryWithWeakEquivalences D] in
theorem isCofibrant_iff_of_equivalence (X : D) :
    IsCofibrant X ↔ IsCofibrant (E.functor.obj X) := by
  let hI := IsInitial.isInitialObj E.functor _ initialIsInitial
  rw [isCofibrant_iff_of_isInitial hI, show hI.to (E.functor.obj X) =
    E.functor.map (initial.to X) from hI.hom_ext _ _,
    ← cofibration_iff_of_equivalence E hcof]

include hcof hweq in
/-- A precofibration structure transported along an equivalence of categories
which identifies the cofibrations and the weak equivalences. -/
theorem of_equivalence : ABCPrecofibrationCategory D := by
  have hc : ∀ {X Y : D} (f : X ⟶ Y), Cofibration f ↔ Cofibration (E.functor.map f) :=
    fun f ↦ cofibration_iff_of_equivalence E hcof f
  have hw : ∀ {X Y : D} (f : X ⟶ Y), WeakEquivalence f ↔ WeakEquivalence (E.functor.map f) :=
    fun f ↦ weakEquivalence_iff_of_equivalence E hweq f
  have ho := isCofibrant_iff_of_equivalence E hcof
  exact
  { initial_cofibrant := by
      rw [ho]
      let e : ⊥_ D' ≅ E.functor.obj (⊥_ D) :=
        initialIsInitial.uniqueUpToIso (IsInitial.isInitialObj E.functor _ initialIsInitial)
      have := cofibration_of_isIso e.hom
      exact cofibrant_target e.hom
    cofibrations_comp := ⟨fun f g hf hg ↦ by
      have : Cofibration f := ⟨hf⟩
      have : Cofibration g := ⟨hg⟩
      have := (hc f).1 ‹_›
      have := (hc g).1 ‹_›
      have : Cofibration (f ≫ g) := (hc _).2 (by rw [Functor.map_comp]; infer_instance)
      exact this.mem⟩
    weakEquivalence_of_isIso := fun f _ ↦ (hw f).2 (weakEquivalence_of_isIso _)
    cofibration_of_isIso := fun {A _} f _ _ ↦ by
      have := (ho A).1 ‹_›
      exact (hc f).2 (cofibration_of_isIso _)
    weakEquivalences_twoOutOfThree := by
      rw [hweq]
      infer_instance
    hasPushout := fun {A _ D₀} i f _ _ _ ↦ by
      have := (ho A).1 ‹_›
      have := (ho D₀).1 ‹_›
      have := (hc i).1 ‹_›
      have : HasColimit (span i f ⋙ E.functor) := hasColimit_of_iso (spanCompIso _ _ _)
      exact Adjunction.hasColimit_of_comp_equivalence _ E.functor
    cofibration_of_isPushout := fun {A _ D₀ _ i _ _ j} h _ _ _ ↦ by
      have := (ho A).1 ‹_›
      have := (ho D₀).1 ‹_›
      have := (hc i).1 ‹_›
      exact (hc j).2 (cofibration_of_isPushout (h.map E.functor))
    weakEquivalence_of_isPushout := fun {A _ D₀ _ i _ _ j} h _ _ _ _ ↦ by
      have := (ho A).1 ‹_›
      have := (ho D₀).1 ‹_›
      have := (hc i).1 ‹_›
      have := (hw i).1 ‹_›
      exact (hw j).2 (weakEquivalence_of_isPushout (h.map E.functor))
    factorization := fun {A B} f _ ↦ by
      have := (ho A).1 ‹_›
      obtain ⟨Z, i, p, hi, hp, hip⟩ := factorization (E.functor.map f)
      have : IsCofibrant ((𝟭 D').obj Z) := cofibrant_target i
      refine ⟨E.inverse.obj Z, E.unit.app A ≫ E.inverse.map i,
        E.inverse.map p ≫ E.unitInv.app B, (hc _).2 ?_, (hw _).2 ?_, ?_⟩
      · rw [Functor.map_comp, E.fun_inv_map, E.functor_unit_comp_assoc]
        have := cofibration_of_isIso (E.counitInv.app Z)
        infer_instance
      · rw [Functor.map_comp, E.fun_inv_map]
        have := weakEquivalence_of_isIso (E.counit.app Z)
        have := weakEquivalence_of_isIso (E.counitInv.app (E.functor.obj B))
        have := weakEquivalence_of_isIso (E.functor.map (E.unitInv.app B))
        infer_instance
      · simp only [Category.assoc, ← Functor.map_comp_assoc, hip]
        simp }

end ABCCofibrations.ABCPrecofibrationCategory

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximation
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant

/-!
# The precofibration category of cofibrant objects

CF1–CF4 restrict to the full subcategory of cofibrant objects. Its inclusion
is a cofibrant approximation, using the inherited mathlib morphism classes.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

instance cofibrantObject_categoryWithCofibrations :
    CategoryWithCofibrations (CofibrantObject C) where
  cofibrations := (cofibrations C).inverseImage CofibrantObject.ι

instance cofibrantObject_hom_cofibration {A B : CofibrantObject C}
    (i : A ⟶ B) [Cofibration i] : Cofibration i.hom :=
  ⟨(show Cofibration i from inferInstance).mem⟩

/-- The ambient initial object is also initial in the full subcategory. -/
noncomputable def cofibrantInitialIsInitial :
    IsInitial (CofibrantObject.mk (⊥_ C)) :=
  IsInitial.isInitialOfObj CofibrantObject.ι _ initialIsInitial

noncomputable instance (X : CofibrantObject C) : Unique (CofibrantObject.mk (⊥_ C) ⟶ X) :=
  ⟨⟨(cofibrantInitialIsInitial (C := C)).to X⟩, fun f ↦
    (cofibrantInitialIsInitial (C := C)).hom_ext f _⟩

instance cofibrantObject_hasInitial : HasInitial (CofibrantObject C) :=
  hasInitial_of_unique (CofibrantObject.mk (⊥_ C))

/-- The inclusion preserves the initial object. -/
instance cofibrantInclusion_preservesInitial :
    PreservesColimit (Functor.empty.{0} (CofibrantObject C)) CofibrantObject.ι := by
  apply preservesColimit_of_preserves_colimit_cocone (cofibrantInitialIsInitial (C := C))
  exact (isColimitMapCoconeEmptyCoconeEquiv CofibrantObject.ι _).symm initialIsInitial

instance cofibrantObject_isCofibrant (A : CofibrantObject C) : IsCofibrant A := by
  let h := isColimitOfHasInitialOfPreservesColimit (CofibrantObject.ι (C := C))
  let e : (⊥_ (CofibrantObject C)).obj ≅ ⊥_ C := h.uniqueUpToIso initialIsInitial
  have he : Cofibration e.hom := cofibration_of_isIso e.hom
  have ht : Cofibration (initial.to A.obj) := inferInstance
  have hw : Cofibration (e.hom ≫ initial.to A.obj) := inferInstance
  constructor
  change cofibrations C ((initial.to A).hom)
  have eq : (initial.to A).hom = e.hom ≫ initial.to A.obj := h.hom_ext _ _
  rw [eq]
  exact hw.mem

/-- A restricted pushout exists and is preserved by the full inclusion. -/
theorem exists_cofibrant_pushout {A B D : CofibrantObject C}
    (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] :
    ∃ (P : CofibrantObject C) (g : B ⟶ P) (j : D ⟶ P),
      IsPushout i f g j ∧ IsPushout i.hom f.hom g.hom j.hom := by
  let : Cofibration i.hom := ⟨(show Cofibration i from inferInstance).mem⟩
  let sq := IsPushout.of_hasPushout i.hom f.hom
  let := cofibration_of_isPushout sq
  let := cofibrant_target (pushout.inr i.hom f.hom)
  let P := CofibrantObject.mk (pushout i.hom f.hom)
  let g : B ⟶ P := CofibrantObject.homMk (pushout.inl i.hom f.hom)
  let j : D ⟶ P := CofibrantObject.homMk (pushout.inr i.hom f.hom)
  exact ⟨P, g, j, IsPushout.of_map_of_faithful CofibrantObject.ι sq, sq⟩

instance cofibrantObject_hasPushout {A B D : CofibrantObject C}
    (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] : HasPushout i f := by
  obtain ⟨P, g, j, h, _⟩ := exists_cofibrant_pushout i f
  exact h.hasPushout

instance cofibrantInclusion_preservesPushout {A B D : CofibrantObject C}
    (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] :
    PreservesColimit (span i f) CofibrantObject.ι := by
  obtain ⟨P, g, j, h, h'⟩ := exists_cofibrant_pushout i f
  exact (h.preservesColimit_span_iff (F := CofibrantObject.ι)).2 h'

/-- CF1–CF4 restrict to the full subcategory of cofibrant objects. -/
instance cofibrantObject_precofibrationCategory :
    ABCPrecofibrationCategory (CofibrantObject C) where
  initial_cofibrant := inferInstance
  cofibrations_comp := inferInstanceAs
    ((cofibrations C).inverseImage CofibrantObject.ι).IsStableUnderComposition
  weakEquivalence_of_isIso f := by
    exact ⟨(weakEquivalence_of_isIso f.hom).mem⟩
  cofibration_of_isIso f := by
    intro _
    exact ⟨(cofibration_of_isIso f.hom).mem⟩
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout i f := by intro _ _ _; infer_instance
  cofibration_of_isPushout {A B D E} {i f g j} h := by
    intro _ _ hi
    let := hi
    let : Cofibration i.hom := ⟨hi.mem⟩
    have h' : IsPushout i.hom f.hom g.hom j.hom := h.map CofibrantObject.ι
    exact ⟨(cofibration_of_isPushout h').mem⟩
  weakEquivalence_of_isPushout {A B D E} {i f g j} h := by
    intro _ _ hi hw
    let := hi
    let : WeakEquivalence i.hom := ⟨hw.mem⟩
    let : Cofibration i.hom := ⟨hi.mem⟩
    have h' : IsPushout i.hom f.hom g.hom j.hom := h.map CofibrantObject.ι
    exact ⟨(weakEquivalence_of_isPushout h').mem⟩
  factorization f := by
    intro _
    obtain ⟨Z, i, p, hi, hp, hip⟩ := factorization f.hom
    let := hi
    let := cofibrant_target i
    exact ⟨CofibrantObject.mk Z, CofibrantObject.homMk i, CofibrantObject.homMk p,
      ⟨hi.mem⟩, ⟨hp.mem⟩, by ext; exact hip⟩

/-- The inclusion of cofibrant objects is a general cofibrant approximation. -/
instance cofibrantInclusion_isCofibrantApproximation :
    IsCofibrantApproximation (CofibrantObject.ι (C := C)) where
  source_cofibrant _ := inferInstance
  preservesInitial := inferInstance
  map_cofibration i := by intro hi; exact ⟨hi.mem⟩
  weakEquivalence_map_iff _ := ⟨fun h ↦ ⟨h.mem⟩, fun h ↦ ⟨h.mem⟩⟩
  map_isPushout h := h.map CofibrantObject.ι
  factorization f := by
    obtain ⟨Z, i, p, hi, hp, hip⟩ := factorization f
    let := hi
    let := cofibrant_target i
    exact ⟨CofibrantObject.mk Z, CofibrantObject.homMk i, p, ⟨hi.mem⟩, hp, hip⟩

end ABCCofibrations.ABCPrecofibrationCategory

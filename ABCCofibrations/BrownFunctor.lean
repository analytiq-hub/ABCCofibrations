/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Factorization
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# Brown's lemma for functors on cofibrant objects

Preservation of trivial cofibrations implies preservation of all weak
equivalences between cofibrant objects. The source requires only CF1–CF4;
the target weak-equivalence class only needs two-out-of-three. In particular,
a functor which inverts trivial cofibrations inverts all weak equivalences
of cofibrant objects.
-/

public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Brown's functor lemma on the full subcategory of cofibrant objects.
No cofibrations or model-category structure on the target are required. -/
theorem map_weakEquivalence_cofibrant_of_map_trivialCofibrations
    [CategoryWithWeakEquivalences D] [(weakEquivalences D).HasTwoOutOfThreeProperty]
    (F : CofibrantObject C ⥤ D)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → WeakEquivalence (F.map i))
    {X Y : CofibrantObject C} (f : X ⟶ Y) [WeakEquivalence f.hom] :
    WeakEquivalence (F.map f) := by
  obtain ⟨Z, i, p, s, hZ, hi, hp, hs, hsw, hip, hsp⟩ :=
    exists_brown_factorization f.hom
  let := hZ
  let := hp
  have hiw : WeakEquivalence i := weakEquivalence_of_postcomp_of_fac hip
  let i' : X ⟶ CofibrantObject.mk Z := CofibrantObject.homMk i
  let p' : CofibrantObject.mk Z ⟶ Y := CofibrantObject.homMk p
  let s' : Y ⟶ CofibrantObject.mk Z := CofibrantObject.homMk s
  have hip' : i' ≫ p' = f := by ext; exact hip
  have hsp' : s' ≫ p' = 𝟙 Y := by ext; exact hsp
  have hiF : WeakEquivalence (F.map i') := hF i' hi hiw
  have hsF : WeakEquivalence (F.map s') := hF s' hs hsw
  have hid : WeakEquivalence (𝟙 (F.obj Y)) := by
    simpa only [F.map_id] using hF (𝟙 Y)
      (cofibration_of_isIso (𝟙 Y.obj)) (weakEquivalence_of_isIso (𝟙 Y.obj))
  let := hiF
  let := hsF
  let := hid
  have hspF : F.map s' ≫ F.map p' = 𝟙 (F.obj Y) := by
    rw [← F.map_comp, hsp', F.map_id]
  let := weakEquivalence_of_precomp_of_fac hspF
  have h : WeakEquivalence (F.map i' ≫ F.map p') := inferInstance
  rwa [← F.map_comp, hip'] at h

/-- Brown's functor lemma for an ambient functor, restricted to cofibrant
sources and targets. -/
theorem map_weakEquivalence_of_map_trivialCofibrations
    [CategoryWithWeakEquivalences D] [(weakEquivalences D).HasTwoOutOfThreeProperty]
    (F : C ⥤ D)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i))
    {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (F.map f) := by
  let : WeakEquivalence (CofibrantObject.homMk f).hom :=
    inferInstanceAs (WeakEquivalence f)
  exact map_weakEquivalence_cofibrant_of_map_trivialCofibrations
    (CofibrantObject.ι ⋙ F)
    (fun i hi hw ↦ by
      let := hi
      let := hw
      exact hF i.hom)
    (CofibrantObject.homMk f)

/-- To invert weak equivalences of cofibrant objects, it suffices to invert
trivial cofibrations. This form applies to functors into arbitrary categories. -/
theorem isInvertedBy_of_inverts_trivialCofibrations
    (F : CofibrantObject C ⥤ D)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i)) :
    (weakEquivalences (CofibrantObject C)).IsInvertedBy F := by
  let : CategoryWithWeakEquivalences D :=
    ⟨MorphismProperty.isomorphisms D⟩
  let : (weakEquivalences D).HasTwoOutOfThreeProperty :=
    inferInstanceAs (MorphismProperty.isomorphisms D).HasTwoOutOfThreeProperty
  intro X Y f hf
  have hw : WeakEquivalence f.hom := ⟨hf⟩
  let := hw
  have h := map_weakEquivalence_cofibrant_of_map_trivialCofibrations F
    (fun i hi hw ↦ ⟨hF i hi hw⟩) f
  exact h.mem

end ABCCofibrations.ABCPrecofibrationCategory

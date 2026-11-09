/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Coproducts
public import Mathlib.CategoryTheory.Localization.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.IsConnected

/-!
# Cofibrant approximation functors

Definition 6.1.1 of Rădulescu-Banu: CFA1–CFA4, between supplied ABC
precofibration categories, with all source objects cofibrant. CFA3 is stated
as preservation of pushout squares only when both source maps are cofibrations.
No induced equivalence on localizations is assumed in the definition.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D]

/-- A cofibrant approximation in the sense of Definition 6.1.1.
The all-cofibrant source condition is included as a field, rather than as an
additional argument at every use of the structure. -/
class IsCofibrantApproximation (F : C ⥤ D)
    [ABCPrecofibrationCategory C] [ABCPrecofibrationCategory D] : Prop where
  source_cofibrant (A : C) : IsCofibrant A
  /-- CFA1: preservation of the initial object. -/
  preservesInitial : PreservesColimit (Functor.empty.{0} C) F
  /-- CFA1: preservation of cofibrations. -/
  map_cofibration {A B : C} (i : A ⟶ B) [Cofibration i] : Cofibration (F.map i)
  /-- CFA2: weak equivalences are exactly those detected by the functor. -/
  weakEquivalence_map_iff {A B : C} (f : A ⟶ B) :
    WeakEquivalence (F.map f) ↔ WeakEquivalence f
  /-- CFA3: preservation of pushouts of two cofibrations. -/
  map_isPushout {A B E P : C} {i : A ⟶ B} {j : A ⟶ E}
    {k : B ⟶ P} {l : E ⟶ P} [Cofibration i] [Cofibration j]
    (h : IsPushout i j k l) : IsPushout (F.map i) (F.map j) (F.map k) (F.map l)
  /-- CFA4: factor a map from an image through an image of a cofibration
  followed by an ambient weak equivalence. -/
  factorization {A : C} {B : D} (f : F.obj A ⟶ B) :
    ∃ (Z : C) (i : A ⟶ Z) (p : F.obj Z ⟶ B),
      Cofibration i ∧ WeakEquivalence p ∧ F.map i ≫ p = f

attribute [instance] IsCofibrantApproximation.preservesInitial

namespace IsCofibrantApproximation

open ABCPrecofibrationCategory

variable [ABCPrecofibrationCategory C]

/-- The identity of an all-cofibrant precofibration category is a cofibrant
approximation. -/
instance identity [∀ A : C, IsCofibrant A] : IsCofibrantApproximation (𝟭 C) where
  source_cofibrant _ := inferInstance
  preservesInitial := inferInstance
  map_cofibration i := by intro hi; exact hi
  weakEquivalence_map_iff _ := Iff.rfl
  map_isPushout h := h
  factorization f := ABCPrecofibrationCategory.factorization f

variable [ABCPrecofibrationCategory D]
  (F : C ⥤ D) [IsCofibrantApproximation F]

/-- A cofibrant approximation sends every object to a cofibrant object. -/
theorem obj_cofibrant (A : C) : IsCofibrant (F.obj A) := by
  let := source_cofibrant F A
  let := map_cofibration (F := F) (initial.to A)
  let := cofibration_of_isIso (initialComparison F)
  have h : initial.to (F.obj A) = initialComparison F ≫ F.map (initial.to A) :=
    Subsingleton.elim _ _
  change Cofibration (initial.to (F.obj A))
  rw [h]
  infer_instance

/-- CFA2 gives preservation of weak equivalences. -/
theorem map_weakEquivalence {A B : C} (f : A ⟶ B) [WeakEquivalence f] :
    WeakEquivalence (F.map f) :=
  (weakEquivalence_map_iff (F := F) f).2 inferInstance

/-- Cofibrant approximations preserve trivial cofibrations. -/
theorem map_trivialCofibration {A B : C} (i : A ⟶ B)
    [Cofibration i] [WeakEquivalence i] :
    Cofibration (F.map i) ∧ WeakEquivalence (F.map i) :=
  ⟨map_cofibration (F := F) i, map_weakEquivalence F i⟩

/-- CFA2 packages the approximation as a morphism of localizers. -/
def toLocalizerMorphism : LocalizerMorphism (weakEquivalences C) (weakEquivalences D) where
  functor := F
  map _ _ f hf := by
    let : WeakEquivalence f := ⟨hf⟩
    exact (map_weakEquivalence F f).mem

/-- The weak-equivalence class is induced exactly from the target. -/
instance toLocalizerMorphism_isInduced : (toLocalizerMorphism F).IsInduced where
  inverseImage_eq := by
    ext A B f
    change weakEquivalences D (F.map f) ↔ weakEquivalences C f
    exact ⟨fun h ↦ ((weakEquivalence_map_iff (F := F) f).1 ⟨h⟩).mem,
      fun h ↦ ((weakEquivalence_map_iff (F := F) f).2 ⟨h⟩).mem⟩

/-- Every target object admits a left resolution by an object of the source,
using the image of the initial object and CFA4. -/
instance hasLeftResolutions : (toLocalizerMorphism F).HasLeftResolutions := by
  intro B
  let h₀ := isColimitOfHasInitialOfPreservesColimit F
  obtain ⟨Z, i, p, _, hp, _⟩ := factorization (F := F) (h₀.to B)
  exact ⟨{ X₁ := Z, w := p, hw := hp.mem }⟩

/-- CFA4 extends any resolution of the source of an ambient arrow to a
resolution square. Thus arrows also have left resolutions. -/
instance arrow_hasLeftResolutions : (toLocalizerMorphism F).arrow.HasLeftResolutions := by
  intro f
  let R : (toLocalizerMorphism F).LeftResolution f.left :=
    Classical.choice (hasLeftResolutions F f.left)
  obtain ⟨Z, i, p, _, hp, h⟩ := factorization (F := F) (R.w ≫ f.hom)
  exact ⟨{
    X₁ := Arrow.mk i
    w := Arrow.homMk R.w p h.symm
    hw := ⟨R.hw, hp.mem⟩ }⟩

/-- Two resolutions of one target admit a common extension whose comparison
maps are trivial cofibrations in the source category. -/
theorem exists_common_resolution {X : D} {A B : C}
    (p : F.obj A ⟶ X) (q : F.obj B ⟶ X) [WeakEquivalence p] [WeakEquivalence q] :
    ∃ (Z : C) (i : A ⟶ Z) (j : B ⟶ Z) (r : F.obj Z ⟶ X),
      Cofibration i ∧ WeakEquivalence i ∧ Cofibration j ∧ WeakEquivalence j ∧
        WeakEquivalence r ∧ F.map i ≫ r = p ∧ F.map j ≫ r = q := by
  let (A : C) : IsCofibrant A := source_cofibrant F A
  let a := initial.to A
  let b := initial.to B
  let sq := IsPushout.of_hasPushout a b
  let := cofibration_of_isPushout sq
  let := cofibration_of_isPushout sq.flip
  let fsq := map_isPushout (F := F) sq
  let h₀ := isColimitOfHasInitialOfPreservesColimit F
  have h : F.map a ≫ p = F.map b ≫ q := h₀.hom_ext _ _
  let u := fsq.desc p q h
  obtain ⟨Z, k, r, hk, hr, hkr⟩ := factorization (F := F) u
  let := hk
  let := hr
  have hi : F.map (pushout.inl a b ≫ k) ≫ r = p := by
    rw [F.map_comp, Category.assoc, hkr]
    exact fsq.inl_desc p q h
  have hj : F.map (pushout.inr a b ≫ k) ≫ r = q := by
    rw [F.map_comp, Category.assoc, hkr]
    exact fsq.inr_desc p q h
  have hwi : WeakEquivalence (F.map (pushout.inl a b ≫ k)) :=
    weakEquivalence_of_postcomp_of_fac hi
  have hwj : WeakEquivalence (F.map (pushout.inr a b ≫ k)) :=
    weakEquivalence_of_postcomp_of_fac hj
  exact ⟨Z, pushout.inl a b ≫ k, pushout.inr a b ≫ k, r, inferInstance,
    (weakEquivalence_map_iff _).1 hwi, inferInstance,
    (weakEquivalence_map_iff _).1 hwj, hr, hi, hj⟩

/-- The category of resolutions of any target object is connected. -/
instance leftResolution_isConnected (X : D) :
    IsConnected ((toLocalizerMorphism F).LeftResolution X) := by
  apply zigzag_isConnected
  intro R S
  let : WeakEquivalence (show F.obj R.X₁ ⟶ X from R.w) := ⟨R.hw⟩
  let : WeakEquivalence (show F.obj S.X₁ ⟶ X from S.w) := ⟨S.hw⟩
  obtain ⟨Z, i, j, r, _, _, _, _, hr, hi, hj⟩ :=
    exists_common_resolution F (A := R.X₁) (B := S.X₁) R.w S.w
  let T : (toLocalizerMorphism F).LeftResolution X :=
    { X₁ := Z, w := r, hw := hr.mem }
  exact Zigzag.of_hom_inv
    (show R ⟶ T from { f := i, comm := hi })
    (show S ⟶ T from { f := j, comm := hj })

end IsCofibrantApproximation

end ABCCofibrations

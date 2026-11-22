/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantSubcategory

/-! # Full subcategories inheriting CF1–CF4

Let `C` be a precofibration category and `P` a property of objects which
holds at the initial object, is closed under pushouts along cofibrations
between cofibrant objects, and is closed backwards along weak equivalences
(if `Z ⟶ Y` is a weak equivalence and `P Y`, then `P Z`). Then the full
subcategory on `P`, with the induced cofibrations and weak equivalences,
is a precofibration category.

This is the pattern of Theorems 9.3.8 and 9.5.6 of *Cofibrations in Homotopy
Theory*, for restricted diagrams. CF1 and CF2 are inherited, CF3 uses closure
under pushouts, and in CF4 the middle object lies in `P` by the closure under
weak equivalences. The proof follows `CofibrantSubcategory.lean`, which is the
special case of cofibrant objects.

The subcategory is the type synonym `ClosedSubcategory P`, so that its
instances do not interact with other instances on `P.FullSubcategory`.
-/

@[expose] public section
universe v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- Closure conditions under which a full subcategory inherits CF1–CF4. -/
class IsPrecofibrationClosed (P : ObjectProperty C) : Prop where
  initial : P (⊥_ C)
  of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout i f g j) [IsCofibrant A] [IsCofibrant D] [Cofibration i] :
    P A → P B → P D → P E
  of_weakEquivalence {Z Y : C} (p : Z ⟶ Y) [WeakEquivalence p] : P Y → P Z

/-- The full subcategory on a property, to carry the induced structure. -/
def ClosedSubcategory (P : ObjectProperty C) : Type _ := P.FullSubcategory

namespace ClosedSubcategory

variable (P : ObjectProperty C)

instance : Category (ClosedSubcategory P) := inferInstanceAs (Category P.FullSubcategory)

/-- The inclusion functor. -/
def ι : ClosedSubcategory P ⥤ C := P.ι

instance : (ι P).Full := inferInstanceAs P.ι.Full

instance : (ι P).Faithful := inferInstanceAs P.ι.Faithful

/-- The object of the subcategory given by an object satisfying `P`. -/
def mk (X : C) (hX : P X) : ClosedSubcategory P := ⟨X, hX⟩

/-- A morphism of the subcategory from an ambient morphism. -/
def homMk {X Y : ClosedSubcategory P} (f : (ι P).obj X ⟶ (ι P).obj Y) : X ⟶ Y :=
  ObjectProperty.homMk (P := P) (X := X) (Y := Y) f

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C] in
@[simp] theorem ι_map_homMk {X Y : ClosedSubcategory P} (f : (ι P).obj X ⟶ (ι P).obj Y) :
    (ι P).map (homMk P f) = f :=
  rfl

instance : CategoryWithCofibrations (ClosedSubcategory P) where
  cofibrations := (cofibrations C).inverseImage (ι P)

instance : CategoryWithWeakEquivalences (ClosedSubcategory P) where
  weakEquivalences := (weakEquivalences C).inverseImage (ι P)

omit [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C] in
lemma cofibration_iff {X Y : ClosedSubcategory P} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration ((ι P).map f) :=
  ⟨fun h ↦ ⟨h.mem⟩, fun h ↦ ⟨h.mem⟩⟩

omit [CategoryWithCofibrations C] [HasInitial C] [ABCPrecofibrationCategory C] in
lemma weakEquivalence_iff {X Y : ClosedSubcategory P} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence ((ι P).map f) :=
  ⟨fun h ↦ ⟨h.mem⟩, fun h ↦ ⟨h.mem⟩⟩

instance : (weakEquivalences (ClosedSubcategory P)).HasTwoOutOfThreeProperty :=
  inferInstanceAs ((weakEquivalences C).inverseImage (ι P)).HasTwoOutOfThreeProperty

variable [IsPrecofibrationClosed P]

/-- The ambient initial object, in the subcategory. -/
noncomputable def initialObj : ClosedSubcategory P := mk P (⊥_ C) IsPrecofibrationClosed.initial

/-- It is initial in the subcategory. -/
noncomputable def initialObjIsInitial : IsInitial (initialObj P) :=
  IsInitial.isInitialOfObj (ι P) _ initialIsInitial

noncomputable instance (X : ClosedSubcategory P) : Unique (initialObj P ⟶ X) :=
  ⟨⟨(initialObjIsInitial P).to X⟩, fun f ↦ (initialObjIsInitial P).hom_ext f _⟩

instance : HasInitial (ClosedSubcategory P) := hasInitial_of_unique (initialObj P)

/-- The inclusion sends the chosen initial object to an initial object. -/
noncomputable def isInitial_ι_obj_initial : IsInitial ((ι P).obj (⊥_ (ClosedSubcategory P))) :=
  IsInitial.ofIso initialIsInitial
    ((ι P).mapIso ((initialObjIsInitial P).uniqueUpToIso initialIsInitial))

/-- Cofibrancy in the subcategory is ambient cofibrancy. -/
theorem isCofibrant_iff (X : ClosedSubcategory P) :
    IsCofibrant X ↔ IsCofibrant ((ι P).obj X) := by
  rw [isCofibrant_iff_of_isInitial (isInitial_ι_obj_initial P)]
  change Cofibration (initial.to X) ↔ _
  rw [cofibration_iff]
  have heq : (ι P).map (initial.to X) = (isInitial_ι_obj_initial P).to _ :=
    (isInitial_ι_obj_initial P).hom_ext _ _
  rw [heq]

/-- A restricted pushout exists in the subcategory and is computed in `C`. -/
theorem exists_pushout {A B D : ClosedSubcategory P} (i : A ⟶ B) (f : A ⟶ D)
    [hA : IsCofibrant A] [hD : IsCofibrant D] [hi : Cofibration i] :
    ∃ (E : ClosedSubcategory P) (g : B ⟶ E) (j : D ⟶ E),
      IsPushout i f g j ∧ IsPushout ((ι P).map i) ((ι P).map f) ((ι P).map g) ((ι P).map j) := by
  have := (isCofibrant_iff P A).1 hA
  have := (isCofibrant_iff P D).1 hD
  have := (cofibration_iff P i).1 hi
  let sq := IsPushout.of_hasPushout ((ι P).map i) ((ι P).map f)
  let E := mk P (pushout ((ι P).map i) ((ι P).map f))
    (IsPrecofibrationClosed.of_isPushout sq A.property B.property D.property)
  let g : B ⟶ E := homMk P (pushout.inl ((ι P).map i) ((ι P).map f))
  let j : D ⟶ E := homMk P (pushout.inr ((ι P).map i) ((ι P).map f))
  have sq' : IsPushout ((ι P).map i) ((ι P).map f) ((ι P).map g) ((ι P).map j) := by
    exact sq
  exact ⟨E, g, j, IsPushout.of_map_of_faithful (ι P) sq', sq'⟩

instance hasPushout' {A B D : ClosedSubcategory P} (i : A ⟶ B) (f : A ⟶ D)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] : HasPushout i f := by
  obtain ⟨E, g, j, h, _⟩ := exists_pushout P i f
  exact h.hasPushout

instance preservesPushout {A B D : ClosedSubcategory P} (i : A ⟶ B) (f : A ⟶ D)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] :
    PreservesColimit (span i f) (ι P) := by
  obtain ⟨E, g, j, h, h'⟩ := exists_pushout P i f
  exact (h.preservesColimit_span_iff (F := ι P)).2 h'

/-- **CF1–CF4 for a closed full subcategory.** -/
instance precofibrationCategory : ABCPrecofibrationCategory (ClosedSubcategory P) where
  initial_cofibrant := (isCofibrant_iff P _).2 (by
    let e : ⊥_ C ≅ (ι P).obj (⊥_ (ClosedSubcategory P)) :=
      initialIsInitial.uniqueUpToIso (isInitial_ι_obj_initial P)
    have := cofibration_of_isIso e.hom
    exact cofibrant_target e.hom)
  cofibrations_comp := inferInstanceAs
    ((cofibrations C).inverseImage (ι P)).IsStableUnderComposition
  weakEquivalence_of_isIso f _ := ⟨(weakEquivalence_of_isIso ((ι P).map f)).mem⟩
  cofibration_of_isIso f _ hX := by
    have := (isCofibrant_iff P _).1 hX
    exact ⟨(cofibration_of_isIso ((ι P).map f)).mem⟩
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout i f := by intro _ _ _; infer_instance
  cofibration_of_isPushout {A B D E} {i f g j} h hA hD hi := by
    have := (isCofibrant_iff P A).1 hA
    have := (isCofibrant_iff P D).1 hD
    have := (cofibration_iff P i).1 hi
    have h' : IsPushout ((ι P).map i) ((ι P).map f) ((ι P).map g) ((ι P).map j) := h.map (ι P)
    exact ⟨(cofibration_of_isPushout h').mem⟩
  weakEquivalence_of_isPushout {A B D E} {i f g j} h hA hD hi hw := by
    have := (isCofibrant_iff P A).1 hA
    have := (isCofibrant_iff P D).1 hD
    have := (cofibration_iff P i).1 hi
    have := (weakEquivalence_iff P i).1 hw
    have h' : IsPushout ((ι P).map i) ((ι P).map f) ((ι P).map g) ((ι P).map j) := h.map (ι P)
    exact ⟨(weakEquivalence_of_isPushout h').mem⟩
  factorization {A B} f hA := by
    have := (isCofibrant_iff P A).1 hA
    obtain ⟨Z, i, p, hi, hp, hip⟩ := factorization ((ι P).map f)
    have hZ : P Z := IsPrecofibrationClosed.of_weakEquivalence p B.property
    refine ⟨mk P Z hZ, homMk P i, homMk P p, ⟨?_⟩, ⟨?_⟩, ?_⟩
    · exact hi.mem
    · exact hp.mem
    · apply (ι P).map_injective
      exact hip

end ClosedSubcategory

end ABCCofibrations

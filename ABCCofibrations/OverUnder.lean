/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import ABCCofibrations.ToDualRegistrations
public import Mathlib.AlgebraicTopology.ModelCategory.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Over and under categories (Proposition 1.7.1(1))

For an object `A` of a precofibration category, the over category `Over A`
is a precofibration category, and so is the under category `Under A` when
`A` is cofibrant, with the induced weak equivalences and cofibrations: a map
is a weak equivalence or cofibration when its underlying map is.

Mathlib already equips `Over A` with the induced classes
(`Mathlib.AlgebraicTopology.ModelCategory.Over`). The induced cofibrations and
weak equivalences on `Under A`, which mathlib lists as a TODO, are generated
from mathlib's `Over` instances by `to_dual`: the dual of the fibrations of
`Over A` are the cofibrations of `Under A`, and weak equivalences are
self-dual. The temporary dictionary entries are in `ToDualRegistrations.lean`.
Pushouts in both categories are computed in the ambient category: the
forgetful functors create pushouts. No colimits beyond those of CF3 are
assumed.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

section UnderClasses

variable {C : Type u} [Category.{v} C] (S : C)

/- The induced classes on `Under S`, generated from mathlib's instances on
`Over S`. The bodies are `{ cofibrations := (cofibrations C).under }` and
`{ weakEquivalences := (weakEquivalences C).under }`. -/
attribute [to_dual ABCCofibrations.underCategoryWithCofibrations
  /-- Cofibrations of `Under S` are the maps whose underlying map is one. -/]
  instCategoryWithFibrationsOver
attribute [to_dual ABCCofibrations.underCategoryWithWeakEquivalences
  /-- Weak equivalences of `Under S` are the maps whose underlying map is one. -/]
  instCategoryWithWeakEquivalencesOver

variable {S}

theorem cofibration_under_iff [CategoryWithCofibrations C] {X Y : Under S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := by
  simp only [cofibration_iff]
  rfl

theorem weakEquivalence_under_iff [CategoryWithWeakEquivalences C] {X Y : Under S}
    (f : X ⟶ Y) : WeakEquivalence f ↔ WeakEquivalence f.right := by
  simp only [weakEquivalence_iff]
  rfl

instance underWeakEquivalences_twoOutOfThree [CategoryWithWeakEquivalences C]
    [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Under S)).HasTwoOutOfThreeProperty := by
  change ((weakEquivalences C).under).HasTwoOutOfThreeProperty
  rw [MorphismProperty.under_eq_inverseImage]
  infer_instance

end UnderClasses

namespace ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

section Over

variable (A : C)

/-- `⊥ → A` is an initial object of `Over A`. -/
noncomputable def overMkInitialIsInitial : IsInitial (Over.mk (initial.to A)) :=
  IsInitial.ofUniqueHom (fun Y ↦ Over.homMk (initial.to Y.left) (initialIsInitial.hom_ext _ _))
    (fun _ _ ↦ Over.OverMorphism.ext (initialIsInitial.hom_ext _ _))

/-- The underlying object of the chosen initial object of `Over A` is initial. -/
noncomputable def isInitial_initial_left : IsInitial (⊥_ (Over A)).left :=
  initialIsInitial.ofIso
    ((Over.forget A).mapIso (initialIsInitial.uniqueUpToIso (overMkInitialIsInitial A)).symm)

variable {A}

/-- An object of `Over A` is cofibrant exactly when its underlying object is. -/
theorem isCofibrant_over_iff (X : Over A) : IsCofibrant X ↔ IsCofibrant X.left := by
  rw [isCofibrant_iff_of_isInitial (isInitial_initial_left A) X.left]
  change Cofibration (initial.to X) ↔ _
  rw [cofibrations_over_iff,
    show (initial.to X).left = (isInitial_initial_left A).to X.left from
      (isInitial_initial_left A).hom_ext _ _]

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C] in
theorem hasPushout_over {X Y Z : Over A} (i : X ⟶ Y) (f : X ⟶ Z) [HasPushout i.left f.left] :
    HasPushout i f := by
  have : HasColimit (span ((span i f ⋙ Over.forget A).map WalkingSpan.Hom.fst)
      ((span i f ⋙ Over.forget A).map WalkingSpan.Hom.snd)) :=
    show HasPushout i.left f.left from inferInstance
  have : HasColimit (span i f ⋙ Over.forget A) :=
    hasColimit_of_iso (diagramIsoSpan (span i f ⋙ Over.forget A))
  exact hasColimit_of_created (span i f) (Over.forget A)

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C] in
theorem isPushout_over_left {X Y Z P : Over A} {i : X ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ P}
    {j : Z ⟶ P} (h : IsPushout i f g j) [HasPushout i.left f.left] :
    IsPushout i.left f.left g.left j.left := by
  have : HasColimit (span ((span i f ⋙ Over.forget A).map WalkingSpan.Hom.fst)
      ((span i f ⋙ Over.forget A).map WalkingSpan.Hom.snd)) :=
    show HasPushout i.left f.left from inferInstance
  have : HasColimit (span i f ⋙ Over.forget A) :=
    hasColimit_of_iso (diagramIsoSpan (span i f ⋙ Over.forget A))
  have : PreservesColimit (span i f) (Over.forget A) :=
    preservesColimit_of_createsColimit_and_hasColimit _ _
  exact h.map (Over.forget A)

/-- **Proposition 1.7.1(1)(a)**, CF1–CF4: the over category of any object
is a precofibration category with the induced structure. -/
instance overPrecofibrationCategory : ABCPrecofibrationCategory (Over A) where
  initial_cofibrant := by
    rw [isCofibrant_over_iff]
    exact (isCofibrant_iff_of_isInitial (isInitial_initial_left A) _).2 (by
      rw [show (isInitial_initial_left A).to (⊥_ (Over A)).left = 𝟙 _ from
        (isInitial_initial_left A).hom_ext _ _]
      let e : ⊥_ C ≅ (⊥_ (Over A)).left := initialIsInitial.uniqueUpToIso
        (isInitial_initial_left A)
      have : Cofibration e.hom := cofibration_of_isIso e.hom
      have := cofibrant_target e.hom
      exact cofibration_of_isIso _)
  cofibrations_comp :=
    inferInstanceAs ((cofibrations C).inverseImage (Over.forget A)).IsStableUnderComposition
  weakEquivalence_of_isIso f := by
    intro _
    have : IsIso f.left := (Over.forget A).map_isIso f
    rw [weakEquivalences_over_iff]
    exact weakEquivalence_of_isIso _
  cofibration_of_isIso := by
    intro X Y f _ hX
    have : IsIso f.left := (Over.forget A).map_isIso f
    have := (isCofibrant_over_iff X).1 hX
    rw [cofibrations_over_iff]
    exact cofibration_of_isIso _
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout := by
    intro X Y Z i f hX hZ hi
    have := (isCofibrant_over_iff X).1 hX
    have := (isCofibrant_over_iff Z).1 hZ
    have : Cofibration i.left := (cofibrations_over_iff _ i).1 hi
    exact hasPushout_over i f
  cofibration_of_isPushout := by
    intro X Y Z P i f g j h hX hZ hi
    have := (isCofibrant_over_iff X).1 hX
    have := (isCofibrant_over_iff Z).1 hZ
    have : Cofibration i.left := (cofibrations_over_iff _ i).1 hi
    rw [cofibrations_over_iff]
    exact cofibration_of_isPushout (isPushout_over_left h)
  weakEquivalence_of_isPushout := by
    intro X Y Z P i f g j h hX hZ hi hw
    have := (isCofibrant_over_iff X).1 hX
    have := (isCofibrant_over_iff Z).1 hZ
    have : Cofibration i.left := (cofibrations_over_iff _ i).1 hi
    have : WeakEquivalence i.left := (weakEquivalences_over_iff _ i).1 hw
    rw [weakEquivalences_over_iff]
    exact weakEquivalence_of_isPushout (isPushout_over_left h)
  factorization := by
    intro X Y f hX
    have := (isCofibrant_over_iff X).1 hX
    obtain ⟨Z, i, p, hi, hp, hip⟩ := factorization f.left
    refine ⟨Over.mk (p ≫ Y.hom), Over.homMk i (by simp [← Category.assoc, hip]),
      Over.homMk p rfl, (cofibrations_over_iff _ _).2 hi, (weakEquivalences_over_iff _ _).2 hp, ?_⟩
    ext
    exact hip

end Over

section Under

variable {A : C} [IsCofibrant A]

/-- For cofibrant `A`, an object `A → X` of `Under A` is cofibrant exactly
when its structure map is a cofibration. -/
theorem isCofibrant_under_iff (X : Under A) : IsCofibrant X ↔ Cofibration X.hom := by
  let e : ⊥_ (Under A) ≅ Under.mk (𝟙 A) := initialIsInitial.uniqueUpToIso Under.mkIdInitial
  have h₁ : (initial.to X).right = e.hom.right ≫ X.hom := by
    rw [show initial.to X = e.hom ≫ Under.mkIdInitial.to X from initialIsInitial.hom_ext _ _,
      Under.comp_right, Under.mkIdInitial_to_right]
  have he : e.inv.right ≫ e.hom.right = 𝟙 A := by
    rw [← Under.comp_right, e.inv_hom_id]
    rfl
  have : IsIso e.inv.right := (Under.forget A).map_isIso e.inv
  have : IsIso e.hom.right := (Under.forget A).map_isIso e.hom
  have : IsCofibrant (Under.mk (𝟙 A)).right := ‹IsCofibrant A›
  have : Cofibration e.inv.right := cofibration_of_isIso _
  have := cofibrant_target e.inv.right
  have : Cofibration e.hom.right := cofibration_of_isIso _
  change Cofibration (initial.to X) ↔ _
  rw [cofibration_under_iff, h₁]
  constructor
  · intro _
    rw [show X.hom = e.inv.right ≫ e.hom.right ≫ X.hom by
      rw [← Category.assoc, he]
      exact (Category.id_comp _).symm]
    infer_instance
  · intro _
    infer_instance

/-- The underlying object of a cofibrant object of `Under A` is cofibrant. -/
theorem isCofibrant_right_of_isCofibrant {X : Under A} (hX : IsCofibrant X) :
    IsCofibrant X.right := by
  have := (isCofibrant_under_iff X).1 hX
  exact cofibrant_target X.hom

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C] [IsCofibrant A] in
theorem hasPushout_under {X Y Z : Under A} (i : X ⟶ Y) (f : X ⟶ Z)
    [HasPushout i.right f.right] : HasPushout i f := by
  have : HasColimit (span ((span i f ⋙ Under.forget A).map WalkingSpan.Hom.fst)
      ((span i f ⋙ Under.forget A).map WalkingSpan.Hom.snd)) :=
    show HasPushout i.right f.right from inferInstance
  have : HasColimit (span i f ⋙ Under.forget A) :=
    hasColimit_of_iso (diagramIsoSpan (span i f ⋙ Under.forget A))
  exact hasColimit_of_created (span i f) (Under.forget A)

/-- **Proposition 1.7.1(1)(b)**, CF1–CF4: the under category of a cofibrant
object is a precofibration category with the induced structure. -/
instance underPrecofibrationCategory : ABCPrecofibrationCategory (Under A) where
  initial_cofibrant := by
    rw [isCofibrant_under_iff]
    let e : ⊥_ (Under A) ≅ Under.mk (𝟙 A) := initialIsInitial.uniqueUpToIso Under.mkIdInitial
    have hw : (⊥_ (Under A)).hom = e.inv.right := by
      have := Under.w e.inv
      simpa using this.symm
    have : IsIso e.inv.right := (Under.forget A).map_isIso e.inv
    have : IsCofibrant (Under.mk (𝟙 A)).right := ‹IsCofibrant A›
    rw [hw]
    exact cofibration_of_isIso _
  cofibrations_comp := by
    change ((cofibrations C).under (X := A)).IsStableUnderComposition
    rw [MorphismProperty.under_eq_inverseImage]
    infer_instance
  weakEquivalence_of_isIso f := by
    intro _
    have : IsIso f.right := (Under.forget A).map_isIso f
    rw [weakEquivalence_under_iff]
    exact weakEquivalence_of_isIso _
  cofibration_of_isIso := by
    intro X Y f _ hX
    have : IsIso f.right := (Under.forget A).map_isIso f
    have := isCofibrant_right_of_isCofibrant hX
    rw [cofibration_under_iff]
    exact cofibration_of_isIso _
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout := by
    intro X Y Z i f hX hZ hi
    have := isCofibrant_right_of_isCofibrant hX
    have := isCofibrant_right_of_isCofibrant hZ
    have : Cofibration i.right := (cofibration_under_iff i).1 hi
    exact hasPushout_under i f
  cofibration_of_isPushout := by
    intro X Y Z P i f g j h hX hZ hi
    have := isCofibrant_right_of_isCofibrant hX
    have := isCofibrant_right_of_isCofibrant hZ
    have : Cofibration i.right := (cofibration_under_iff i).1 hi
    have h' : IsPushout i.right f.right g.right j.right := h.map (Under.forget A)
    rw [cofibration_under_iff]
    exact cofibration_of_isPushout h'
  weakEquivalence_of_isPushout := by
    intro X Y Z P i f g j h hX hZ hi hw
    have := isCofibrant_right_of_isCofibrant hX
    have := isCofibrant_right_of_isCofibrant hZ
    have : Cofibration i.right := (cofibration_under_iff i).1 hi
    have : WeakEquivalence i.right := (weakEquivalence_under_iff i).1 hw
    have h' : IsPushout i.right f.right g.right j.right := h.map (Under.forget A)
    rw [weakEquivalence_under_iff]
    exact weakEquivalence_of_isPushout h'
  factorization := by
    intro X Y f hX
    have := isCofibrant_right_of_isCofibrant hX
    obtain ⟨Z, i, p, hi, hp, hip⟩ := factorization f.right
    refine ⟨Under.mk (X.hom ≫ i), Under.homMk i rfl,
      Under.homMk p (by simp [hip]), (cofibration_under_iff _).2 hi,
      (weakEquivalence_under_iff _).2 hp, ?_⟩
    ext
    exact hip

end Under

end ABCPrecofibrationCategory

end ABCCofibrations

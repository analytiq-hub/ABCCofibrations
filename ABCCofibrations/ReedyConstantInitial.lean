/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBasic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Constant diagrams on direct categories with an initial object

The initial-object step of the proposed terminal-vertex-preserving repair
requires an actual initial object, rather than contractibility alone.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u v' u'
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
variable {D : Type u} [Category.{v} D] [IsDirect D] {e : D} (he : IsInitial e)

include he

/-- The latching category of the initial object of a direct category is empty. -/
theorem latching_initial_isEmpty : IsEmpty (LatchingCategory e) := by
  obtain ⟨deg, hd⟩ := (inferInstance : IsDirect D).exists_deg
  refine ⟨fun x ↦ ?_⟩
  have h₁ : deg e ≤ deg x.obj.left := by
    rcases hd (he.to x.obj.left) with h | ⟨h, _⟩
    · exact Nat.le_of_lt h
    · simp [h]
  rcases hd x.obj.hom with h | ⟨h, _⟩
  · omega
  · exact x.property h

/-- At any other object, the initial arrow supplies an initial latching object. -/
def initialLatchingObject (d : D) (hne : e ≠ d) : LatchingCategory d :=
  ⟨Over.mk (he.to d), hne⟩

noncomputable def initialLatchingObjectIsInitial (d : D) (hne : e ≠ d) :
    IsInitial (initialLatchingObject he d hne) := by
  letI (x : LatchingCategory d) : Unique (initialLatchingObject he d hne ⟶ x) :=
    ⟨⟨ObjectProperty.homMk (Over.homMk (he.to x.obj.left) (he.hom_ext _ _))⟩,
      fun f ↦ ObjectProperty.hom_ext _ (Over.OverMorphism.ext (he.hom_ext _ _))⟩
  exact IsInitial.ofUnique _

variable {M : Type u'} [Category.{v'} M] [HasInitial M]

/-- Constant diagrams of cofibrant objects have all latching colimits when the
indexing direct category has an initial object. -/
theorem hasColimit_latching_const_initial (A : M) (d : D) :
    HasColimit (latchingDiagram ((Functor.const D).obj A) d) := by
  classical
  by_cases h : e = d
  · subst d
    have := latching_initial_isEmpty he
    let c : Cocone (latchingDiagram ((Functor.const D).obj A) e) :=
      ⟨⊥_ M, { app := fun j ↦ isEmptyElim j
               naturality := fun x _ _ ↦ False.elim ((latching_initial_isEmpty he).false x) }⟩
    refine ⟨⟨⟨c, ?_⟩⟩⟩
    exact { desc := fun s ↦ initial.to s.pt
            fac := fun _ j ↦ isEmptyElim j
            uniq := fun _ _ _ ↦ initial.hom_ext _ _ }
  · have : HasInitial (LatchingCategory d) :=
      (initialLatchingObjectIsInitial he d h).hasInitial
    have : IsConnected (LatchingCategory d) :=
      isConnected_of_isInitial _ (initialLatchingObjectIsInitial he d h)
    exact inferInstanceAs (HasColimit ((Functor.const (LatchingCategory d)).obj A))

/-- At the initial indexing object, the latching object is itself initial. -/
noncomputable def constantInitialLatchingIsInitial (A : M)
    [HasColimit (latchingDiagram ((Functor.const D).obj A) e)] :
    IsInitial (latchingObj ((Functor.const D).obj A) e) := by
  have := latching_initial_isEmpty he
  let c (B : M) : Cocone (latchingDiagram ((Functor.const D).obj A) e) :=
    { pt := B
      ι := { app := fun j ↦ isEmptyElim j
             naturality := fun x _ _ ↦ False.elim ((latching_initial_isEmpty he).false x) } }
  letI (B : M) : Unique (latchingObj ((Functor.const D).obj A) e ⟶ B) :=
    ⟨⟨colimit.desc _ (c B)⟩, fun _ ↦ colimit.hom_ext (fun j ↦ isEmptyElim j)⟩
  exact IsInitial.ofUnique _

variable [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M]
  [ABCPrecofibrationCategory M]

/-- A cofibrant constant diagram is Reedy cofibrant when the direct indexing
category has an actual initial object. Contractibility alone is insufficient. -/
theorem isReedyCofibrant_const_initial (A : M) (hA : IsCofibrant A)
    [∀ d, HasColimit (latchingDiagram ((Functor.const D).obj A) d)] :
    IsReedyCofibrant ((Functor.const D).obj A) := by
  classical
  intro d
  have := hA
  by_cases h : e = d
  · subst d
    let hI := constantInitialLatchingIsInitial he A
    let i := initialIsInitial.uniqueUpToIso hI
    have : Cofibration i.hom := ABCPrecofibrationCategory.cofibration_of_isIso i.hom
    have hL : IsCofibrant (latchingObj ((Functor.const D).obj A) e) :=
      ABCPrecofibrationCategory.cofibrant_target i.hom
    refine ⟨hL, ?_⟩
    have hc := (ABCPrecofibrationCategory.isCofibrant_iff_of_isInitial hI A).1 hA
    rwa [show hI.to A = latchingMap ((Functor.const D).obj A) e from hI.hom_ext _ _] at hc
  · have : IsConnected (LatchingCategory d) :=
      isConnected_of_isInitial _ (initialLatchingObjectIsInitial he d h)
    let hc : IsColimit (latchingCocone ((Functor.const D).obj A) d) :=
      isColimitConstCocone (LatchingCategory d) A
    let i : latchingObj ((Functor.const D).obj A) d ≅ A :=
      (colimit.isColimit _).coconePointUniqueUpToIso hc
    have hi : i.hom = latchingMap ((Functor.const D).obj A) d := rfl
    have : Cofibration i.inv := ABCPrecofibrationCategory.cofibration_of_isIso i.inv
    have hL : IsCofibrant (latchingObj ((Functor.const D).obj A) d) :=
      ABCPrecofibrationCategory.cofibrant_target i.inv
    have := hL
    refine ⟨hL, ?_⟩
    rw [← hi]
    exact ABCPrecofibrationCategory.cofibration_of_isIso i.hom

end ABCCofibrations

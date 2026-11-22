/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ClosedSubcategory
public import ABCCofibrations.PointwiseArbitraryCofibrationCategory
public import ABCCofibrations.Gluing

/-! # Restricted diagram structures (Theorems 9.3.8 and 9.5.6, CF1–CF4)

For a class `W` of maps of the indexing category, a diagram is `W`-restricted if
it sends maps of `W` to weak equivalences. The paper writes `M^(D₁,D₂)` for the
diagrams restricted by the maps of a subcategory `D₂`.

We show that `W`-restricted diagrams are closed in the sense of
`IsPrecofibrationClosed`, both for the Reedy structure (direct `D₁`) and for the
pointwise structure. The full subcategories are therefore precofibration
categories. This gives CF1–CF4 of Theorem 9.3.8(1)(a),(b) and of Theorem
9.5.6(1). The proof follows the paper: pushouts are restricted by the gluing
lemma, applied pointwise, and middle objects of factorizations by 2-out-of-3.

The case used in §9.5 is `W = ` the maps of Δ′D with identity terminal
component. Its full subcategory `RestrictedResolutionDiagram D M` has as
cofibrant objects the restricted Reedy cofibrant diagrams of Proposition 9.5.7.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

open ABCPrecofibrationCategory

section General

variable {D₁ : Type w} [SmallCategory D₁] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]

/-- A diagram is `W`-restricted if it inverts the maps of `W`. -/
def IsRestrictedBy (W : MorphismProperty D₁) (X : D₁ ⥤ M) : Prop :=
  ∀ ⦃x y : D₁⦄ (g : x ⟶ y), W g → WeakEquivalence (X.map g)

variable [ABCPrecofibrationCategory M]

theorem IsRestrictedBy.of_weakEquivalence {W : MorphismProperty D₁} {X X' : D₁ ⥤ M}
    (a : X ⟶ X') (ha : ∀ x, WeakEquivalence (a.app x)) (hX' : IsRestrictedBy W X') :
    IsRestrictedBy W X := by
  intro x y g hg
  have := ha x
  have := ha y
  have := hX' g hg
  have : WeakEquivalence (X.map g ≫ a.app y) := by
    rw [a.naturality]
    infer_instance
  exact weakEquivalence_of_postcomp _ (a.app y)

theorem isRestrictedBy_initial (W : MorphismProperty D₁) (X : D₁ ⥤ M)
    (hX : ∀ x, IsInitial (X.obj x)) : IsRestrictedBy W X := by
  intro x y g _
  have : IsIso (X.map g) := ⟨⟨(hX y).to _, (hX x).hom_ext _ _, (hX y).hom_ext _ _⟩⟩
  exact weakEquivalence_of_isIso _

/-- The gluing lemma, pointwise: a pushout of restricted diagrams along a
pointwise cofibration between pointwise cofibrant diagrams is restricted. -/
theorem IsRestrictedBy.of_isPushout {W : MorphismProperty D₁} {A B E F : D₁ ⥤ M}
    {i : A ⟶ B} {f : A ⟶ E} {g : B ⟶ F} {j : E ⟶ F}
    (hA : ∀ x, IsCofibrant (A.obj x)) (hE : ∀ x, IsCofibrant (E.obj x))
    (hi : ∀ x, Cofibration (i.app x))
    (h : ∀ x, IsPushout (i.app x) (f.app x) (g.app x) (j.app x))
    (hPA : IsRestrictedBy W A) (hPB : IsRestrictedBy W B) (hPE : IsRestrictedBy W E) :
    IsRestrictedBy W F := by
  intro x y φ hφ
  have := hA x
  have := hA y
  have := hE x
  have := hE y
  have := hi x
  have := hi y
  have := hPA φ hφ
  have := hPB φ hφ
  have := hPE φ hφ
  exact gluing_weakEquivalence (h x) (h y) (i.naturality φ).symm (f.naturality φ).symm
    (g.naturality φ).symm (j.naturality φ).symm

end General

section Pointwise

variable {D₁ : Type w} [SmallCategory D₁] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] [ABCPrecofibrationCategory (PointwiseDiagram D₁ M)]

/-- `W`-restricted diagrams, in the pointwise structure. -/
def pointwiseRestrictedProperty (W : MorphismProperty D₁) :
    ObjectProperty (PointwiseDiagram D₁ M) :=
  fun X ↦ IsRestrictedBy W (show D₁ ⥤ M from X)

instance (W : MorphismProperty D₁) :
    IsPrecofibrationClosed (pointwiseRestrictedProperty (M := M) W) where
  initial := isRestrictedBy_initial W _ (fun x ↦ PointwiseDiagram.isInitialInitialObj x)
  of_isPushout {A B E F i f g j} h hA hE hi hPA hPB hPE := by
    have hAx := (PointwiseDiagram.isCofibrant_iff A).1 hA
    have hEx := (PointwiseDiagram.isCofibrant_iff E).1 hE
    have hix (x : D₁) : Cofibration (NatTrans.app i x) := hi.mem x
    have hp (x : D₁) : HasPushout (NatTrans.app i x) (NatTrans.app f x) := by
      have := hAx x
      have := hEx x
      have := hix x
      exact hasPushout _ _
    exact IsRestrictedBy.of_isPushout hAx hEx hix (isPushout_app h hp) hPA hPB hPE
  of_weakEquivalence p hp hY := IsRestrictedBy.of_weakEquivalence p hp.mem hY

/-- **Theorems 9.3.8(1)(b) and 9.5.6(1), CF1–CF4.** `W`-restricted diagrams with
pointwise cofibrations and weak equivalences. -/
abbrev PointwiseRestrictedDiagram (W : MorphismProperty D₁) :=
  ClosedSubcategory (pointwiseRestrictedProperty (M := M) W)

example (W : MorphismProperty D₁) :
    ABCPrecofibrationCategory (PointwiseRestrictedDiagram (M := M) W) := inferInstance

end Pointwise

section Reedy

variable {D₁ : Type w} [SmallCategory D₁] [IsDirect D₁] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory.{w} M]

/-- `W`-restricted diagrams, in the Reedy structure. -/
def reedyRestrictedProperty (W : MorphismProperty D₁) :
    ObjectProperty (ReedyDiagram D₁ M) :=
  fun X ↦ IsRestrictedBy W (show D₁ ⥤ M from X)

instance (W : MorphismProperty D₁) :
    IsPrecofibrationClosed (reedyRestrictedProperty (M := M) W) where
  initial := isRestrictedBy_initial W _ (fun x ↦ ReedyDiagram.isInitialInitialObj x)
  of_isPushout {A B E F i f g j} h hA hE hi hPA hPB hPE := by
    obtain ⟨_, hAR⟩ := ReedyDiagram.isReedyCofibrant_of_isCofibrant hA
    obtain ⟨_, hER⟩ := ReedyDiagram.isReedyCofibrant_of_isCofibrant hE
    obtain ⟨_, _, hiR⟩ := (ReedyDiagram.cofibration_iff i).1 hi
    have hix (x : D₁) : Cofibration (NatTrans.app i x) :=
      (hiR.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
        ABCCofibrationCategory.sequentialCofibrationAxiom x).2
    have hp (x : D₁) : HasPushout (NatTrans.app i x) (NatTrans.app f x) := by
      have := hAR.isCofibrant_obj x
      have := hER.isCofibrant_obj x
      have := hix x
      exact hasPushout _ _
    exact IsRestrictedBy.of_isPushout hAR.isCofibrant_obj hER.isCofibrant_obj hix
      (isPushout_app h hp) hPA hPB hPE
  of_weakEquivalence p hp hY :=
    IsRestrictedBy.of_weakEquivalence p ((ReedyDiagram.weakEquivalence_iff p).1 hp) hY

/-- **Theorem 9.3.8(1)(a), CF1–CF4.** `W`-restricted diagrams with Reedy
cofibrations and pointwise weak equivalences. -/
abbrev ReedyRestrictedDiagram (W : MorphismProperty D₁) :=
  ClosedSubcategory (reedyRestrictedProperty (M := M) W)

example (W : MorphismProperty D₁) :
    ABCPrecofibrationCategory (ReedyRestrictedDiagram (M := M) W) := inferInstance

end Reedy

section Resolution

variable (D : Type) [SmallCategory D]

/-- The maps of Δ′D with identity terminal component. -/
def resolutionTerminalIdentities : MorphismProperty (SemisimplicialResolution D) :=
  fun x y f ↦ ∃ h : (resolutionTerminal D).obj x = (resolutionTerminal D).obj y,
    (resolutionTerminal D).map f = eqToHom h

variable {D} {M : Type u} [Category.{v} M] [CategoryWithWeakEquivalences M]

theorem isRestrictedBy_resolution_iff (X : SemisimplicialResolution D ⥤ M) :
    IsRestrictedBy (resolutionTerminalIdentities D) X ↔ IsResolutionRestricted X :=
  ⟨fun h _ _ f hh hf ↦ h f ⟨hh, hf⟩, fun h _ _ f ⟨hh, hf⟩ ↦ h f hh hf⟩

variable (D M) [CategoryWithCofibrations M] [HasInitial M] [ABCCofibrationCategory.{0} M]

/-- Restricted diagrams on Δ′D with the restricted Reedy structure. Its
cofibrant objects are the restricted Reedy cofibrant diagrams of 9.5.7. -/
abbrev RestrictedResolutionDiagram :=
  ReedyRestrictedDiagram (M := M) (resolutionTerminalIdentities D)

example : ABCPrecofibrationCategory (RestrictedResolutionDiagram D M) := inferInstance

end Resolution

end ABCCofibrations

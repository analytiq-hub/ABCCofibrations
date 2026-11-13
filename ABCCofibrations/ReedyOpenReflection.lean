/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyFactorization
public import ABCCofibrations.ReedyLayer

/-! # Recovering Reedy data from an open restriction

The latching inclusion is final at old objects. It therefore reflects their
latching colimits and relative cofibration comparisons. This permits layer
extensions to be checked separately at old and new objects.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)
  (hP : IsOpenDiagramSubcategory P)
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hP in
/-- At an old object, the Reedy condition is reflected from the open restriction. -/
theorem reedy_at_of_open_restriction (X : D ⥤ M) (e : P.FullSubcategory)
    [HasColimit (latchingDiagram (P.ι ⋙ X) e)]
    (he : IsCofibrant (latchingObj (P.ι ⋙ X) e) ∧
      Cofibration (latchingMap (P.ι ⋙ X) e)) :
    ∃ (_ : HasColimit (latchingDiagram X e.obj)),
      IsCofibrant (latchingObj X e.obj) ∧ Cofibration (latchingMap X e.obj) := by
  have := OpenDiagramSubcategory.latchingInclusion_final P hP e
  have : HasColimit (OpenDiagramSubcategory.latchingInclusion P e ⋙
      latchingDiagram X e.obj) := ‹HasColimit (latchingDiagram (P.ι ⋙ X) e)›
  exact transfer_desc_rev (OpenDiagramSubcategory.latchingInclusion P e)
    (latchingDiagram X e.obj) (latchingCocone X e.obj) he.1 he.2

include hP in
/-- A whole diagram is Reedy cofibrant if its old restriction and all new
latching maps satisfy the Reedy condition. -/
theorem isReedyCofibrant_of_open_restriction (X : D ⥤ M)
    [∀ e, HasColimit (latchingDiagram (P.ι ⋙ X) e)]
    (hOld : IsReedyCofibrant (P.ι ⋙ X))
    (hNew : ∀ d : ReedyLayer.Objects P, ∃ (_ : HasColimit (latchingDiagram X d.val)),
      IsCofibrant (latchingObj X d.val) ∧ Cofibration (latchingMap X d.val)) :
    ∃ (_ : ∀ d, HasColimit (latchingDiagram X d)), IsReedyCofibrant X := by
  classical
  have key (d : D) : ∃ (_ : HasColimit (latchingDiagram X d)),
      IsCofibrant (latchingObj X d) ∧ Cofibration (latchingMap X d) := by
    by_cases hd : P d
    · exact reedy_at_of_open_restriction P hP X ⟨d, hd⟩ (hOld ⟨d, hd⟩)
    · exact hNew ⟨d, hd⟩
  choose hCol hCof using key
  exact ⟨hCol, hCof⟩

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
include hP in
/-- Relative comparisons at old objects transfer back from the open restriction. -/
theorem comparison_of_open_restriction {X Y : D ⥤ M} (f : X ⟶ Y)
    (e : P.FullSubcategory) [HasColimit (latchingDiagram X e.obj)]
    [HasColimit (latchingDiagram Y e.obj)]
    [HasColimit (latchingDiagram (P.ι ⋙ X) e)]
    [HasColimit (latchingDiagram (P.ι ⋙ Y) e)]
    {Q : M} {l : X.obj e.obj ⟶ Q} {r : latchingObj (P.ι ⋙ Y) e ⟶ Q}
    {k : Q ⟶ Y.obj e.obj}
    (hQ : IsPushout (latchingMap (P.ι ⋙ X) e)
      (latchingObjMap (Functor.whiskerLeft P.ι f) e) l r)
    (hr : r ≫ k = latchingMap (P.ι ⋙ Y) e) :
    ∃ r' : latchingObj Y e.obj ⟶ Q,
      IsPushout (latchingMap X e.obj) (latchingObjMap f e.obj) l r' ∧
      r' ≫ k = latchingMap Y e.obj := by
  have := OpenDiagramSubcategory.latchingInclusion_final P hP e
  have : HasColimit (OpenDiagramSubcategory.latchingInclusion P e ⋙
      latchingDiagram X e.obj) := ‹HasColimit (latchingDiagram (P.ι ⋙ X) e)›
  have : HasColimit (OpenDiagramSubcategory.latchingInclusion P e ⋙
      latchingDiagram Y e.obj) := ‹HasColimit (latchingDiagram (P.ι ⋙ Y) e)›
  exact transfer_comparison_rev (OpenDiagramSubcategory.latchingInclusion P e)
    (latchingNat f e.obj) (latchingCocone X e.obj) (latchingCocone Y e.obj) hQ hr

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionTerminalVertex
public import ABCCofibrations.SemisimplexContraction
public import Mathlib.CategoryTheory.Limits.Final

/-! # A limit of the marked-terminal repair

Preserving the terminal mark restores an initial object, but the forgetful
functor is not final. Thus this repair does not justify ordinary reindexing
of colimits along that forgetful functor.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits
namespace ABCCofibrations

/-- A map into a marked simplex hits the marked vertex if and only if its
image under any marking-preserving map does. -/
theorem terminalVertex_mark_invariant {D : Type u} [Category.{v} D] (d : D)
    {x y : StructuredArrow (resolutionSingleton d) (terminalVertexForget d)} (f : x ⟶ y) :
    (x.hom = x.right.obj.hom) ↔ (y.hom = y.right.obj.hom) := by
  have hw : x.hom ≫ (terminalVertexForget d).map f.right = y.hom := StructuredArrow.w f
  have hm : x.right.obj.hom ≫ (terminalVertexForget d).map f.right = y.right.obj.hom :=
    Under.w f.right.hom
  constructor
  · intro h
    rw [← hw, h, hm]
  · intro h
    apply (cancel_mono ((terminalVertexForget d).map f.right)).1
    rw [hw, hm, h]

/-- The marked-terminal category cannot replace the full resolution by an
ordinary final functor, even though its singleton is initial. -/
theorem terminalVertexForget_not_final {D : Type u} [Category.{v} D] (d : D) :
    ¬ (terminalVertexForget d).Final := by
  intro hf
  have : IsConnected (StructuredArrow (resolutionSingleton d) (terminalVertexForget d)) :=
    hf.out _
  let n : SemiSimplexCategory := ⟨0⟩
  let a := (resolutionConstants d).map (semisimplexToShift.app n)
  let b := (resolutionConstants d).map (semisimplexPointToShift.app n)
  let edge : TerminalVertexResolution d := ⟨Under.mk a, rfl⟩
  let x : StructuredArrow (resolutionSingleton d) (terminalVertexForget d) :=
    StructuredArrow.mk (Y := edge) b
  let y : StructuredArrow (resolutionSingleton d) (terminalVertexForget d) :=
    StructuredArrow.mk (Y := edge) a
  let P (z : StructuredArrow (resolutionSingleton d) (terminalVertexForget d)) : Prop :=
    z.hom = z.right.obj.hom
  have hP : P x = P y := constant_of_preserves_morphisms P
    (fun _ _ f ↦ propext (terminalVertex_mark_invariant d f)) x y
  have hab : b = a := Eq.mp hP.symm (show P y from rfl)
  have h := congrArg (fun f ↦ SemiSimplexCategory.homEquiv ((resolutionOrdinal D).map f) 0) hab
  change (0 : Fin 2) = 1 at h
  exact Fin.zero_ne_one h

end ABCCofibrations

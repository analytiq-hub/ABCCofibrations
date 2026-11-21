/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SemisimplexContraction
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.WithTerminal.Basic

/-! # Adjoining a terminal vertex

Vertex insertion for labelled simplices. Unlike an initial-object argument,
this construction can contract a resolution with repeated vertices.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits
namespace ABCCofibrations
/-- Adjoining a terminal object preserves thinness of a finite ordinal. -/
instance withTerminalFin_isThin (n : ℕ) : Quiver.IsThin (WithTerminal (Fin n)) := by
  intro x y
  cases x <;> cases y
  · rename_i a b
    exact inferInstanceAs (Subsingleton (a ⟶ b))
  · exact inferInstanceAs (Subsingleton PUnit)
  · exact inferInstanceAs (Subsingleton PEmpty)
  · exact inferInstanceAs (Subsingleton PUnit)

/-- The ordinal with one new final vertex, expressed using `WithTerminal`. -/
def finAppendTerminalObj (n : ℕ) : Fin (n + 2) → WithTerminal (Fin (n + 1)) :=
  Fin.lastCases WithTerminal.star WithTerminal.of

/-- The ordinal map realizing the adjoining of a final vertex. -/
def finAppendTerminal (n : ℕ) : Fin (n + 2) ⥤ WithTerminal (Fin (n + 1)) where
  obj := finAppendTerminalObj n
  map {i j} f := by
    have h := leOfHom f
    induction j using Fin.lastCases with
    | last =>
      simpa [finAppendTerminalObj] using
        WithTerminal.starTerminal.from (finAppendTerminalObj n i)
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp at h
      | cast i =>
        simpa [finAppendTerminalObj] using
          (show WithTerminal.of i ⟶ WithTerminal.of j from
            homOfLE (Fin.castSucc_le_castSucc_iff.mp h))
  map_id i := (withTerminalFin_isThin (n + 1) _ _).elim _ _
  map_comp f g := (withTerminalFin_isThin (n + 1) _ _).elim _ _

variable {C : Type u} [Category.{v} C]

/-- Extend a labelled chain by an explicitly supplied terminal vertex. -/
def appendTerminal {n : ℕ} (X : Fin (n + 1) ⥤ C) {c : C} (hc : IsTerminal c) :
    Fin (n + 2) ⥤ C :=
  finAppendTerminal n ⋙ WithTerminal.liftToTerminal X hc

@[simp] theorem appendTerminal_obj_cast {n : ℕ} (X : Fin (n + 1) ⥤ C)
    {c : C} (hc : IsTerminal c) (i : Fin (n + 1)) :
    (appendTerminal X hc).obj i.castSucc = X.obj i := by
  simp [appendTerminal, finAppendTerminal, finAppendTerminalObj, WithTerminal.liftToTerminal]

@[simp] theorem appendTerminal_obj_last {n : ℕ} (X : Fin (n + 1) ⥤ C)
    {c : C} (hc : IsTerminal c) :
    (appendTerminal X hc).obj (Fin.last (n + 1)) = c := by
  simp [appendTerminal, finAppendTerminal, finAppendTerminalObj, WithTerminal.liftToTerminal]

end ABCCofibrations

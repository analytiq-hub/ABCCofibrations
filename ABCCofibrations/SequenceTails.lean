/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SequentialColimits
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Cofibrations from every stage of a sequential colimit -/

@[expose] public section
universe v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.ABCPrecofibrationCategory

/-- CF6 gives a cofibration from any stage of the sequence, by passing to
its final tail. -/
theorem cofibration_colimit_ι_of_sequence {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
    [ABCPrecofibrationCategory C] (h6 : SequentialCofibrationAxiom C)
    (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (succHom n))) [HasColimit F] (n : ℕ) :
    Cofibration (colimit.ι F n) := by
  let hm : Monotone (fun k : ℕ ↦ n + k) := fun _ _ h ↦ Nat.add_le_add_left h n
  let T : ℕ ⥤ ℕ := hm.functor
  have : T.Final := (Monotone.final_functor_iff hm).2
    (fun k ↦ ⟨k, Nat.le_add_left _ _⟩)
  have hT0 : IsCofibrant ((T ⋙ F).obj 0) := by
    simpa [T] using isCofibrant_obj_of_sequence F h0 hf n
  have hTf (k : ℕ) : Cofibration ((T ⋙ F).map (succHom k)) := by
    change Cofibration (F.map (homOfLE (Nat.add_le_add_left (Nat.le_succ k) n)))
    convert hf (n + k) using 1
  have := h6.hasColimit (T ⋙ F) hT0 hTf
  have := h6.cofibration (T ⋙ F) hT0 hTf
  have := isCofibrant_colimit_of_sequence h6 (T ⋙ F) hT0 hTf
  have := cofibration_of_isIso (colimit.pre F T)
  rw [show colimit.ι F n = colimit.ι (T ⋙ F) 0 ≫ colimit.pre F T by
    rw [colimit.ι_pre]
    rfl]
  infer_instance

end ABCCofibrations.ABCPrecofibrationCategory

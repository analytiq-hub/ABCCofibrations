/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallCofibrations
public import ABCCofibrations.FibrationCategory

/-!
# Limits over arbitrary small inverse categories

Theorem 9.3.5(2)(a), transported from the colimit theorem through opposites.
The conclusion uses mathlib's native chosen limit. F5(1) and F6(1) are
expressed as CF5(1) and CF6(1) on the opposite category.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] [IsInverse D] {M : Type u} [Category.{v} M]
  [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]
  [ABCPrefibrationCategory M]

/-- Theorem 9.3.5(2)(a), with no object or hom-set finiteness assumption. -/
theorem reedyFibrant_limit_small
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} Mᵒᵖ)
    (h6 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Mᵒᵖ)
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X.op d)] (hX : IsReedyFibrant X) :
    ∃ (_ : HasLimit X), IsFibrant (limit X) := by
  obtain ⟨_, hC⟩ := reedyCofibrant_colimit_small h5 h6 X.op hX
  have hL : HasLimit X := hasLimit_of_hasColimit_op X
  refine ⟨hL, (ABCPrefibrationCategory.isFibrant_iff_isCofibrant_op _).2 ?_⟩
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  exact ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit X).hom

omit [ABCPrefibrationCategory M] in
/-- Theorem 9.3.5(2)(a) for an ABC fibration category. -/
theorem reedyFibrant_limit_of_fibrationCategory [ABCFibrationCategory.{w} M]
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X.op d)] (hX : IsReedyFibrant X) :
    ∃ (_ : HasLimit X), IsFibrant (limit X) :=
  reedyFibrant_limit_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom X hX

/-- Theorem 9.3.5(2)(b), obtained entirely by duality. -/
theorem reedyFibration_limMap_small
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} Mᵒᵖ)
    (h6 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] (f : X ⟶ Y) (hf : IsReedyFibration f) :
    ∃ (_ : HasLimit X) (_ : HasLimit Y), Fibration (limMap f) := by
  obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_small h5 h6 (NatTrans.op f) hf
  obtain ⟨_, hCY⟩ := reedyCofibrant_colimit_small h5 h6 Y.op hf.1
  obtain ⟨_, hCX⟩ := reedyCofibrant_colimit_small h5 h6 X.op hf.2.1
  have hLX : HasLimit X := hasLimit_of_hasColimit_op X
  have hLY : HasLimit Y := hasLimit_of_hasColimit_op Y
  refine ⟨hLX, hLY, (cofibration_op_iff _).1 ?_⟩
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit Y).hom
  have := ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit Y).hom
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit Y).inv
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  rw [op_limMap_comparison]
  infer_instance

/-- Theorem 9.3.5(2)(c), transported from the arbitrary small direct theorem. -/
theorem reedyFibrant_limMap_weakEquivalence_small
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} Mᵒᵖ)
    (h5t : ABCPrecofibrationCategory.TrivialCoproductAxiom.{w} Mᵒᵖ)
    (h6 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Mᵒᵖ)
    (h6t : ABCPrecofibrationCategory.TrivialSequentialAxiom Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] (hX : IsReedyFibrant X)
    (hY : IsReedyFibrant Y) (f : X ⟶ Y) (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasLimit X) (_ : HasLimit Y), WeakEquivalence (limMap f) := by
  obtain ⟨_, _, hc⟩ := reedyCofibrant_colimMap_weakEquivalence_small h5 h5t h6 h6t
    hY hX (NatTrans.op f) (fun d ↦ (weakEquivalences_op_iff _).2 (hw d.unop))
  have hLX : HasLimit X := hasLimit_of_hasColimit_op X
  have hLY : HasLimit Y := hasLimit_of_hasColimit_op Y
  refine ⟨hLX, hLY, (weakEquivalences_op_iff _).1 ?_⟩
  rw [op_limMap_comparison]
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit Y).inv
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance

end ABCCofibrations

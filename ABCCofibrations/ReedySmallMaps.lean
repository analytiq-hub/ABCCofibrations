/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallColimits
public import ABCCofibrations.ReedyBoundedMaps

/-!
# Maps of arbitrary small direct diagrams

Theorem 9.3.5(1)(c), using bounded layer induction followed by CF6.
No finiteness condition is imposed on the indexing category or its hom-sets.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] [IsDirect D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- Theorem 9.3.5(1)(c) for arbitrary small direct indexing categories. -/
theorem reedyCofibrant_colimMap_weakEquivalence_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h5t : TrivialCoproductAxiom.{w} M)
    (h6 : SequentialCofibrationAxiom M) (h6t : TrivialSequentialAxiom M)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] (hX : IsReedyCofibrant X)
    (hY : IsReedyCofibrant Y) (f : X ⟶ Y) (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨hColX, hCofX, hMapX⟩ := reedyCofibrant_degreeColimits_data_small deg hdeg h5 X hX
  obtain ⟨hColY, hCofY, hMapY⟩ := reedyCofibrant_degreeColimits_data_small deg hdeg h5 Y hY
  have h0X : IsCofibrant ((degreeColimits deg X).obj 0) := hCofX 0
  have h0Y : IsCofibrant ((degreeColimits deg Y).obj 0) := hCofY 0
  have hSX : HasColimit (degreeColimits deg X) := h6.hasColimit _ h0X hMapX
  have hSY : HasColimit (degreeColimits deg Y) := h6.hasColimit _ h0Y hMapY
  have hW (n : ℕ) : WeakEquivalence ((degreeColimitsMap deg f).app n) := by
    obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) X hX
    obtain ⟨_, hRY⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) Y hY
    obtain ⟨_, _, hwn⟩ := reedyCofibrant_colimMap_weakEquivalence_bounded h5 h5t n
      (degreeBelow deg n).FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory _ deg hdeg) (fun e ↦ e.property)
      _ _ (Functor.whiskerLeft (degreeBelow deg n).ι f) hRX hRY (fun e ↦ hw e.obj)
    exact hwn
  have hSW := ABCPrecofibrationCategory.weakEquivalence_colimMap_of_sequences h6 h6t
    (degreeColimitsMap deg f) h0X hMapX h0Y hMapY hW
  have hCX : HasColimit X := hasColimit_of_degreeColimits deg X hmono
  have hCY : HasColimit Y := hasColimit_of_degreeColimits deg Y hmono
  refine ⟨hCX, hCY, ?_⟩
  let eX := degreeColimitIso deg X hmono
  let eY := degreeColimitIso deg Y hmono
  have := weakEquivalence_of_isIso eX.inv
  have := weakEquivalence_of_isIso eY.hom
  rw [show colimMap f = eX.inv ≫ colimMap (degreeColimitsMap deg f) ≫ eY.hom by
    rw [Iso.eq_inv_comp]
    exact (degreeColimitIso_naturality deg hmono f).symm]
  infer_instance

omit [ABCPrecofibrationCategory M] in
/-- Theorem 9.3.5(1)(c) for an ABC cofibration category. -/
theorem reedyCofibrant_colimMap_weakEquivalence_of_cofibrationCategory
    [ABCCofibrationCategory.{w} M] {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y)
    (f : X ⟶ Y) (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f) :=
  reedyCofibrant_colimMap_weakEquivalence_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.trivialCoproductAxiom ABCCofibrationCategory.sequentialCofibrationAxiom
    ABCCofibrationCategory.trivialSequentialAxiom hX hY f hw

end ABCCofibrations

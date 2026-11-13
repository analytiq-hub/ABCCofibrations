/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBounded
public import ABCCofibrations.ReedyInverse

/-!
# Colimits of Reedy cofibrant diagrams over arbitrary small direct categories

Theorem 9.3.5(1)(a). CF5(1) constructs each degree truncation and makes its
transition a cofibration; CF6(1) constructs their sequential colimit. Neither
finiteness of objects/hom-sets nor the trivial-map parts of CF5–CF6 are needed.
The inverse-category theorem is transported by duality to the native limit.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- Degree-colimit data with no finiteness restriction on the degree layers. -/
theorem reedyCofibrant_degreeColimits_data_small (deg : D → ℕ)
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    (h5 : CoproductCofibrationAxiom.{w} M) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)),
      (∀ n, IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X))) ∧
        ∀ n, Cofibration ((degreeColimits deg X).map (succHom n)) := by
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b f
    rcases hdeg f with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  have hStage (n : ℕ) : ∃ (_ : HasColimit ((degreeBelow deg n).ι ⋙ X)),
      IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X)) := by
    obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) X hX
    exact reedyCofibrant_colimit_bounded h5 n (degreeBelow deg n).FullSubcategory
      (fun e ↦ deg e.obj) (degreeCondition_fullSubcategory _ deg hdeg)
      (fun e ↦ e.property) _ hR
  let hCol (n : ℕ) : HasColimit ((degreeBelow deg n).ι ⋙ X) := (hStage n).choose
  have hCof (n : ℕ) : IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X)) := (hStage n).choose_spec
  refine ⟨hCol, hCof, fun n ↦ ?_⟩
  exact cofibration_degreeColimitMap_of_layer deg hdeg h5 X hX hCof n

/-- Theorem 9.3.5(1)(a), using only CF5(1) and CF6(1) beyond CF1–CF4. -/
theorem reedyCofibrant_colimit_small [IsDirect D]
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit X), IsCofibrant (colimit X) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b f
    rcases hdeg f with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨hCols, hCof, hMaps⟩ := reedyCofibrant_degreeColimits_data_small deg hdeg h5 X hX
  have h0 : IsCofibrant ((degreeColimits deg X).obj 0) := hCof 0
  have hSeq : HasColimit (degreeColimits deg X) := h6.hasColimit _ h0 hMaps
  have hSeqCof := isCofibrant_colimit_of_sequence h6 (degreeColimits deg X) h0 hMaps
  have hCol : HasColimit X := hasColimit_of_degreeColimits deg X hmono
  refine ⟨hCol, ?_⟩
  have := cofibration_of_isIso (degreeColimitIso deg X hmono).hom
  exact cofibrant_target (degreeColimitIso deg X hmono).hom

omit [ABCPrecofibrationCategory M] in
/-- Theorem 9.3.5(1)(a) for an ABC cofibration category. -/
theorem reedyCofibrant_colimit [IsDirect D] [ABCCofibrationCategory.{w} M]
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit X), IsCofibrant (colimit X) :=
  reedyCofibrant_colimit_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom X hX

end ABCCofibrations

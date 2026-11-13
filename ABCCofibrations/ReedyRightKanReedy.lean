/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyKanReedy
public import ABCCofibrations.ReedyRightKan

/-!
# Reedy fibrancy of right Kan extensions

The finite case of Theorem 9.4.3(2)(a)–(c), by duality. The results concern
mathlib's chosen right Kan extension, through the canonical comparison
with the opposite left Kan extension.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [Finite D₁]
  [∀ a b : D₂, Finite (a ⟶ b)] [IsInverse D₁] [IsInverse D₂]
  (u : D₁ ⥤ D₂) {M : Type u} [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCPrefibrationCategory M]

/-- Theorem 9.4.3(2)(a), with finite inverse source and finite hom-sets in the
inverse target, using F1–F4 only. -/
theorem reedyFibrant_rightKanExtension_reedy (X : D₁ ⥤ M)
    [∀ e, HasColimit (latchingDiagram X.op e)] (hX : IsReedyFibrant X) :
    ∃ (_ : u.HasPointwiseRightKanExtension X)
      (_ : ∀ d, HasColimit (latchingDiagram (u.rightKanExtension X).op d)),
      IsReedyFibrant (u.rightKanExtension X) := by
  obtain ⟨hK, hL, hLeft⟩ := reedyCofibrant_leftKanExtension_reedy u.op X.op hX
  have hR := hasPointwiseRightKanExtension_of_op u X
  let e : u.op.leftKanExtension X.op ≅ (u.rightKanExtension X).op :=
    leftKanExtensionIsoOpRight u
  obtain ⟨hN, hIso⟩ := isReedyCofibration_of_isIso e.hom hLeft
  exact ⟨hR, hN, hIso.2.1⟩

/-- Theorem 9.4.3(2)(b), with finite source and finite hom-sets in both inverse
indexing categories, transported from the cofibration theorem. -/
theorem reedyFibration_pointwiseRightKanMap_reedy [∀ a b : D₁, Finite (a ⟶ b)]
    {X Y : D₁ ⥤ M} [∀ e, HasColimit (latchingDiagram X.op e)]
    [∀ e, HasColimit (latchingDiagram Y.op e)] {f : X ⟶ Y} (hf : IsReedyFibration f) :
    ∃ (_ : u.HasPointwiseRightKanExtension X) (_ : u.HasPointwiseRightKanExtension Y)
      (_ : ∀ d, HasColimit (latchingDiagram (u.rightKanExtension X).op d))
      (_ : ∀ d, HasColimit (latchingDiagram (u.rightKanExtension Y).op d)),
      IsReedyFibration (pointwiseRightKanMap u f) := by
  obtain ⟨hKY, hKX, hLY, hLX, hLeft⟩ := reedyCofibration_pointwiseLeftKanMap_reedy u.op hf
  obtain ⟨hRX, hNX, hX⟩ := reedyFibrant_rightKanExtension_reedy u X hf.2.1
  obtain ⟨hRY, hNY, hY⟩ := reedyFibrant_rightKanExtension_reedy u Y hf.1
  refine ⟨hRX, hRY, hNX, hNY, ?_⟩
  change IsReedyCofibration (NatTrans.op (pointwiseRightKanMap u f))
  obtain ⟨_, hpre⟩ := isReedyCofibration_of_isIso
    (leftKanExtensionIsoOpRight u (X := Y)).inv hY
  obtain ⟨_, hpost⟩ := isReedyCofibration_of_isIso
    (leftKanExtensionIsoOpRight u (X := X)).hom hLeft.2.1
  rw [leftKanExtensionIsoOpRight_naturality]
  exact hpre.comp (hLeft.comp hpost)

/-- Theorem 9.4.3(2)(c), packaging Reedy fibrancy with the pointwise weak
equivalence transported in Theorem 9.4.2(2)(c). -/
theorem reedyFibrant_pointwiseRightKanMap_weakEquivalence_reedy
    [∀ a b : D₁, Finite (a ⟶ b)] {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X.op e)] [∀ e, HasColimit (latchingDiagram Y.op e)]
    (hX : IsReedyFibrant X) (hY : IsReedyFibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) :
    ∃ (_ : u.HasPointwiseRightKanExtension X) (_ : u.HasPointwiseRightKanExtension Y)
      (_ : ∀ d, HasColimit (latchingDiagram (u.rightKanExtension X).op d))
      (_ : ∀ d, HasColimit (latchingDiagram (u.rightKanExtension Y).op d)),
      IsReedyFibrant (u.rightKanExtension X) ∧ IsReedyFibrant (u.rightKanExtension Y) ∧
        ∀ d, WeakEquivalence ((pointwiseRightKanMap u f).app d) := by
  obtain ⟨hKX, hLX, hRX⟩ := reedyFibrant_rightKanExtension_reedy u X hX
  obtain ⟨hKY, hLY, hRY⟩ := reedyFibrant_rightKanExtension_reedy u Y hY
  obtain ⟨_, _, hmap⟩ := reedyFibrant_pointwiseRightKanMap_weakEquivalence u hX hY f hw
  exact ⟨hKX, hKY, hLX, hLY, hRX, hRY, hmap⟩

end ABCCofibrations

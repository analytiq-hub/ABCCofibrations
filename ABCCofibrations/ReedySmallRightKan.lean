/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallKan
public import ABCCofibrations.KanOpposite
public import ABCCofibrations.FibrationCategory

/-!
# Relative limits of Reedy fibrant diagrams (Theorem 9.4.2(2))

The arbitrary small inverse case, with no finiteness restrictions.
All homotopical claims are transported from `ReedySmallKan.lean` by opposites;
`KanOpposite.lean` compares the resulting extensions and maps with mathlib's
chosen right Kan extensions. F5 and F6 are supplied by the ABC fibration category.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [IsInverse D₁]
  (u : D₁ ⥤ D₂) {M : Type u₂} [Category.{v₂} M]
  [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]
  [ABCFibrationCategory.{w} M]

open ABCPrefibrationCategory

/-- Theorem 9.4.2(2)(a): for an arbitrary small inverse source, the pointwise
right Kan extension exists and is pointwise fibrant. -/
theorem reedyFibrant_rightKanExtension_small (X : D₁ ⥤ M)
    [∀ d, HasColimit (latchingDiagram X.op d)] (hX : IsReedyFibrant X) :
    ∃ (_ : u.HasPointwiseRightKanExtension X),
      ∀ d₂, IsFibrant ((u.rightKanExtension X).obj d₂) := by
  obtain ⟨hK, h⟩ := reedyCofibrant_leftKanExtension_small u.op X.op hX
  have hR := hasPointwiseRightKanExtension_of_op u X
  refine ⟨hR, fun d₂ ↦ ?_⟩
  have : IsFibrant ((u.op.leftKanExtension X.op).unop.obj d₂) :=
    (isFibrant_iff_isCofibrant_op _).2 (h (op d₂))
  have := fibration_of_isIso ((rightKanExtensionIsoUnopLeft u X).hom.app d₂)
  exact fibrant_source ((rightKanExtensionIsoUnopLeft u X).hom.app d₂)

/-- Theorem 9.4.2(2)(b), for the maps between chosen right Kan extensions,
for arbitrary small inverse source categories. -/
theorem reedyFibration_pointwiseRightKanMap_small {X Y : D₁ ⥤ M}
    [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] {f : X ⟶ Y} (hf : IsReedyFibration f) :
    ∃ (_ : u.HasPointwiseRightKanExtension X) (_ : u.HasPointwiseRightKanExtension Y),
      ∀ d₂, Fibration ((pointwiseRightKanMap u f).app d₂) := by
  obtain ⟨hKY, hKX, hc⟩ := reedyCofibration_pointwiseLeftKanMap_small u.op hf
  obtain ⟨hRX, hX⟩ := reedyFibrant_rightKanExtension_small u X hf.2.1
  obtain ⟨hRY, hY⟩ := reedyFibrant_rightKanExtension_small u Y hf.1
  refine ⟨hRX, hRY, fun d₂ ↦ ?_⟩
  rw [pointwiseRightKanMap_app_op]
  have : Fibration (((pointwiseLeftKanMap u.op (NatTrans.op f)).app (op d₂)).unop) :=
    (fibration_unop_iff _).2 (hc (op d₂))
  have := hX d₂
  have := hY d₂
  have := fibration_of_isIso ((rightKanExtensionIsoUnopLeft u X).inv.app d₂)
  have := fibrant_source ((rightKanExtensionIsoUnopLeft u X).inv.app d₂)
  have := fibration_of_isIso ((rightKanExtensionIsoUnopLeft u X).hom.app d₂)
  have := fibration_of_isIso ((rightKanExtensionIsoUnopLeft u Y).inv.app d₂)
  infer_instance

/-- Theorem 9.4.2(2)(c), for the maps between chosen right Kan extensions,
for arbitrary small inverse source categories. -/
theorem reedyFibrant_pointwiseRightKanMap_weakEquivalence_small {X Y : D₁ ⥤ M}
    [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)]
    (hX : IsReedyFibrant X) (hY : IsReedyFibrant Y) (f : X ⟶ Y)
    (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : u.HasPointwiseRightKanExtension X) (_ : u.HasPointwiseRightKanExtension Y),
      ∀ d₂, WeakEquivalence ((pointwiseRightKanMap u f).app d₂) := by
  obtain ⟨hKY, hKX, hc⟩ := reedyCofibrant_pointwiseLeftKanMap_weakEquivalence_small u.op
    hY hX (NatTrans.op f) (fun d ↦ (weakEquivalences_op_iff _).2 (hw d.unop))
  have hRX := hasPointwiseRightKanExtension_of_op u X
  have hRY := hasPointwiseRightKanExtension_of_op u Y
  refine ⟨hRX, hRY, fun d₂ ↦ ?_⟩
  rw [pointwiseRightKanMap_app_op]
  have : WeakEquivalence (((pointwiseLeftKanMap u.op (NatTrans.op f)).app (op d₂)).unop) :=
    (weakEquivalences_op_iff _).1 (hc (op d₂))
  have := weakEquivalence_of_isIso ((rightKanExtensionIsoUnopLeft u X).hom.app d₂)
  have := weakEquivalence_of_isIso ((rightKanExtensionIsoUnopLeft u Y).inv.app d₂)
  infer_instance

end ABCCofibrations

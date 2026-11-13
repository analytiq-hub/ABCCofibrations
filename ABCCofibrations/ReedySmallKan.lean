/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyKan
public import ABCCofibrations.ReedySmallCofibrations

/-!
# Pointwise Kan extensions of small direct diagrams

Theorem 9.4.2(1)(a–c), without finite-object or finite-hom assumptions.
The comma restriction proofs are reused from `ReedyKan`.
-/

@[expose] public section

universe w v₂ u₂
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory


variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [IsDirect D₁] (u : D₁ ⥤ D₂)
  {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]

/-- **Theorem 9.4.2(1)(a)**, for arbitrary small direct `D₁`. For a Reedy cofibrant
`X : D₁ ⥤ M`, the relative colimit `colim^u X` exists (pointwise) and is
pointwise cofibrant. -/
theorem reedyCofibrant_leftKanExtension_small (X : D₁ ⥤ M) [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X),
      ∀ d₂, IsCofibrant ((u.leftKanExtension X).obj d₂) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  have key (d₂ : D₂) : ∃ (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ X)),
      IsCofibrant (colimit (CostructuredArrow.proj u d₂ ⋙ X)) := by
    obtain ⟨_, h⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d₂) hX
    have : IsDirect (CostructuredArrow u d₂) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
    exact reedyCofibrant_colimit _ h
  have hK : u.HasPointwiseLeftKanExtension X := fun d₂ ↦ (key d₂).fst
  refine ⟨hK, fun d₂ ↦ ?_⟩
  have := (key d₂).snd
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit X d₂).inv
  exact cofibrant_target (u.leftKanExtensionObjIsoColimit X d₂).inv

/-- **Theorem 9.4.2(1)(b)** at the comma-colimit level, for arbitrary small direct
source categories. See `reedyCofibration_pointwiseLeftKanMap_small`
for the induced map between chosen Kan extensions. -/
theorem reedyCofibration_leftKanExtension_small {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) (d₂ : D₂) :
    ∃ (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ X))
      (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ Y)),
      Cofibration (colimMap (Functor.whiskerLeft (CostructuredArrow.proj u d₂) f)) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  obtain ⟨_, _, h⟩ := isReedyCofibration_comma u deg hdeg (d₂ := d₂) hf
  have : IsDirect (CostructuredArrow u d₂) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  exact reedyCofibration_colimMap_of_cofibrationCategory _ h

/-- **Theorem 9.4.2(1)(c)** at the comma-colimit level, for arbitrary small direct
source categories. See
`reedyCofibrant_pointwiseLeftKanMap_weakEquivalence_small` for the chosen Kan extensions. -/
theorem reedyCofibrant_leftKanExtension_weakEquivalence_small {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) (d₂ : D₂) :
    ∃ (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ X))
      (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ Y)),
      WeakEquivalence (colimMap (Functor.whiskerLeft (CostructuredArrow.proj u d₂) f)) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  obtain ⟨_, hX'⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d₂) hX
  obtain ⟨_, hY'⟩ := isReedyCofibrant_comma u deg hdeg Y (d₂ := d₂) hY
  have : IsDirect (CostructuredArrow u d₂) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  exact reedyCofibrant_colimMap_weakEquivalence_of_cofibrationCategory hX' hY' _ (fun j ↦ hw j.left)

/-- Theorem 9.4.2(1)(b) for the morphism between the chosen pointwise left Kan
extensions, for arbitrary small direct source categories. -/
theorem reedyCofibration_pointwiseLeftKanMap_small {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y),
      ∀ d₂, Cofibration ((pointwiseLeftKanMap u f).app d₂) := by
  obtain ⟨hKX, hX⟩ := reedyCofibrant_leftKanExtension_small u X hf.1
  obtain ⟨hKY, hY⟩ := reedyCofibrant_leftKanExtension_small u Y hf.2.1
  refine ⟨hKX, hKY, fun d₂ ↦ ?_⟩
  obtain ⟨_, _, hc⟩ := reedyCofibration_leftKanExtension_small u hf d₂
  rw [pointwiseLeftKanMap_app]
  have := hX d₂
  have := hY d₂
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit X d₂).hom
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit Y d₂).hom
  have := cofibrant_target (u.leftKanExtensionObjIsoColimit Y d₂).hom
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit Y d₂).inv
  infer_instance

/-- Theorem 9.4.2(1)(c) for the morphism between the chosen pointwise left Kan
extensions, for arbitrary small direct source categories. -/
theorem reedyCofibrant_pointwiseLeftKanMap_weakEquivalence_small {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y),
      ∀ d₂, WeakEquivalence ((pointwiseLeftKanMap u f).app d₂) := by
  obtain ⟨hKX, _⟩ := reedyCofibrant_leftKanExtension_small u X hX
  obtain ⟨hKY, _⟩ := reedyCofibrant_leftKanExtension_small u Y hY
  refine ⟨hKX, hKY, fun d₂ ↦ ?_⟩
  obtain ⟨_, _, hc⟩ := reedyCofibrant_leftKanExtension_weakEquivalence_small u hX hY f hw d₂
  rw [pointwiseLeftKanMap_app]
  have := weakEquivalence_of_isIso (u.leftKanExtensionObjIsoColimit X d₂).hom
  have := weakEquivalence_of_isIso (u.leftKanExtensionObjIsoColimit Y d₂).inv
  infer_instance


end ABCCofibrations

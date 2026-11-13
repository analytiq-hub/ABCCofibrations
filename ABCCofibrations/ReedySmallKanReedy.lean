/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.KanLatchingComparison
public import ABCCofibrations.ReedySmallKan
public import ABCCofibrations.ReedySmallRelativeColimits

/-! # Reedy cofibrancy of Kan extensions with arbitrary small source

Theorem 9.4.3(1)(a),(c). Part (b) still needs the unrestricted relative
cofibration comparison of Theorem 9.4.1(1)(b).
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [IsDirect D₁] [IsDirect D₂]
  (u : D₁ ⥤ D₂) {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]

open ABCPrecofibrationCategory

/-- The candidate latching object exists and its inclusion into the comma
colimit is a cofibration, in Theorem 9.4.3(1)(a). -/
theorem reedyCofibrant_kanBoundary_colimit_small (d : D₂) (X : D₁ ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X))
      (_ : HasColimit (CostructuredArrow.proj u d ⋙ X)),
      IsCofibrant (colimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)) ∧
        Cofibration (colimit.pre (CostructuredArrow.proj u d ⋙ X) (kanBoundary u d).ι) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  have : IsDirect (CostructuredArrow u d) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  obtain ⟨_, hX'⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d) hX
  obtain ⟨hB, hC, hpre⟩ := reedyCofibrant_colimit_open_small
    ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom (kanBoundary u d) (kanBoundary_isOpen u d)
    (CostructuredArrow.proj u d ⋙ X) hX'
  obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (kanBoundary u d)
    (kanBoundary_isOpen u d) (CostructuredArrow.proj u d ⋙ X) hX'
  obtain ⟨_, hBC⟩ := reedyCofibrant_colimit _ hR
  exact ⟨hB, hC, hBC, hpre⟩

/-- Theorem 9.4.3(1)(a) for arbitrary small direct source and target. -/
theorem reedyCofibrant_leftKanExtension_reedy_small (X : D₁ ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X)
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension X) d)),
      IsReedyCofibrant (u.leftKanExtension X) := by
  obtain ⟨hK, _⟩ := reedyCofibrant_leftKanExtension_small u X hX
  have hB := fun d ↦ reedyCofibrant_kanBoundary_colimit_small u d X hX
  let hL (d : D₂) : HasColimit (latchingDiagram (u.leftKanExtension X) d) := by
    have := (hB d).choose
    exact ⟨⟨⟨kanBoundaryCocone u X d, isColimitKanBoundaryCocone u X d⟩⟩⟩
  refine ⟨hK, hL, fun d ↦ ?_⟩
  obtain ⟨hBC, hCC, hBCof, hpre⟩ := hB d
  let e : colimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) ≅
      latchingObj (u.leftKanExtension X) d :=
    (isColimitKanBoundaryCocone u X d).coconePointUniqueUpToIso
    (colimit.isColimit (latchingDiagram (u.leftKanExtension X) d))
  have := cofibration_of_isIso e.hom
  have hLC : IsCofibrant (latchingObj (u.leftKanExtension X) d) := cofibrant_target e.hom
  refine ⟨hLC, ?_⟩
  have hInv := cofibration_of_isIso e.inv
  have : IsCofibrant (colimit (CostructuredArrow.proj u d ⋙ X)) :=
    cofibrant_target (colimit.pre (CostructuredArrow.proj u d ⋙ X) (kanBoundary u d).ι)
  have hObjInv : Cofibration (u.leftKanExtensionObjIsoColimit X d).inv := cofibration_of_isIso _
  have hc : Cofibration ((isColimitKanBoundaryCocone u X d).desc
      (latchingCocone (u.leftKanExtension X) d)) := by
    rw [kanBoundaryCocone_desc_latchingCocone]
    exact ⟨(cofibrations M).comp_mem _ _ hpre.mem hObjInv.mem⟩
  have he : e.inv ≫ (isColimitKanBoundaryCocone u X d).desc
      (latchingCocone (u.leftKanExtension X) d) = latchingMap (u.leftKanExtension X) d :=
    IsColimit.coconePointUniqueUpToIso_inv_desc _ _
  rw [← he]
  exact ⟨(cofibrations M).comp_mem _ _ hInv.mem hc.mem⟩

/-- Theorem 9.4.3(1)(c), packaging Reedy cofibrancy together with the pointwise
weak equivalence already established in Theorem 9.4.2(1)(c). -/
theorem reedyCofibrant_pointwiseLeftKanMap_weakEquivalence_reedy_small
    {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y)
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension X) d))
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension Y) d)),
      IsReedyCofibrant (u.leftKanExtension X) ∧ IsReedyCofibrant (u.leftKanExtension Y) ∧
        ∀ d, WeakEquivalence ((pointwiseLeftKanMap u f).app d) := by
  obtain ⟨hKX, hLX, hRX⟩ := reedyCofibrant_leftKanExtension_reedy_small u X hX
  obtain ⟨hKY, hLY, hRY⟩ := reedyCofibrant_leftKanExtension_reedy_small u Y hY
  obtain ⟨_, _, hmap⟩ := reedyCofibrant_pointwiseLeftKanMap_weakEquivalence_small u hX hY f hw
  exact ⟨hKX, hKY, hLX, hLY, hRX, hRY, hmap⟩


end ABCCofibrations

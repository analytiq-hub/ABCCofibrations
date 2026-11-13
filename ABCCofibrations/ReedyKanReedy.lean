/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.KanLatchingComparison

/-!
# Reedy cofibrancy of left Kan extensions

The finite-source, finite-target-hom case of Theorem 9.4.3(1)(a)–(c).
The map statements additionally require finite source hom-sets.
The latching object is computed as the boundary-comma colimit and its map
is the relative colimit comparison from Theorem 9.4.1(1)(a).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [Finite D₁]
  [∀ a b : D₂, Finite (a ⟶ b)] [IsDirect D₁] [IsDirect D₂]
  (u : D₁ ⥤ D₂) {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- Theorem 9.4.3(1)(a), with finite source and finite hom-sets in the direct target.
Only CF1–CF4 are used. -/
theorem reedyCofibrant_leftKanExtension_reedy (X : D₁ ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X)
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension X) d)),
      IsReedyCofibrant (u.leftKanExtension X) := by
  obtain ⟨hK, _⟩ := reedyCofibrant_leftKanExtension u X hX
  have hB := fun d ↦ reedyCofibrant_kanBoundary_colimit u d X hX
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

/-- Theorem 9.4.3(1)(b), with finite source and finite hom-sets in both direct
indexing categories. The result is about the map between chosen Kan extensions. -/
theorem reedyCofibration_pointwiseLeftKanMap_reedy [∀ a b : D₁, Finite (a ⟶ b)]
    {X Y : D₁ ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y)
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension X) d))
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension Y) d)),
      IsReedyCofibration (pointwiseLeftKanMap u f) := by
  obtain ⟨hKX, hLX, hX⟩ := reedyCofibrant_leftKanExtension_reedy u X hf.1
  obtain ⟨hKY, hLY, hY⟩ := reedyCofibrant_leftKanExtension_reedy u Y hf.2.1
  refine ⟨hKX, hKY, hLX, hLY, hX, hY, fun d ↦ ?_⟩
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  have : IsDirect (CostructuredArrow u d) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  obtain ⟨_, _, hComma⟩ := isReedyCofibration_comma u deg hdeg (d₂ := d) hf
  obtain ⟨_, _, hBX, hpreX⟩ := reedyCofibrant_kanBoundary_colimit u d X hf.1
  obtain ⟨_, _, hBY, hpreY⟩ := reedyCofibrant_kanBoundary_colimit u d Y hf.2.1
  obtain ⟨hpo, hrel⟩ := reedyCofibration_relativeColimMap (kanBoundary u d)
    (kanBoundary_isOpen u d) hComma
  let g := Functor.whiskerLeft (CostructuredArrow.proj u d) f
  let a := colimit.pre (CostructuredArrow.proj u d ⋙ X) (kanBoundary u d).ι
  let b := colimMap (Functor.whiskerLeft (kanBoundary u d).ι g)
  let eX := kanLatchingIso u X d
  let eY := kanLatchingIso u Y d
  let oX := u.leftKanExtensionObjIsoColimit X d
  let oY := u.leftKanExtensionObjIsoColimit Y d
  let c := relativeColimMap (kanBoundary u d).ι g ≫ oY.inv
  have hQ : IsPushout (latchingMap (u.leftKanExtension X) d)
      (latchingObjMap (pointwiseLeftKanMap u f) d)
      (oX.hom ≫ pushout.inl a b) (eY.inv ≫ pushout.inr a b) := by
    exact (IsPushout.of_hasPushout a b).of_iso eX oX.symm eY (Iso.refl _)
      (kanLatchingIso_hom_latchingMap u X d).symm
      (kanLatchingIso_naturality u d f).symm (by simp [oX]) (by simp [eY])
  have : IsCofibrant (colimit (CostructuredArrow.proj u d ⋙ Y)) :=
    cofibrant_target (colimit.pre (CostructuredArrow.proj u d ⋙ Y) (kanBoundary u d).ι)
  have hOI : Cofibration oY.inv := cofibration_of_isIso _
  have hc : Cofibration c := ⟨(cofibrations M).comp_mem _ _ hrel.mem hOI.mem⟩
  refine ⟨_, _, _, c, hQ, ?_, ?_, hc⟩
  · change (oX.hom ≫ pushout.inl a b) ≫
      (relativeColimMap (kanBoundary u d).ι g ≫ oY.inv) = _
    rw [Category.assoc, inl_relativeColimMap_assoc]
    exact (pointwiseLeftKanMap_app u f d).symm
  · change (eY.inv ≫ pushout.inr a b) ≫
      (relativeColimMap (kanBoundary u d).ι g ≫ oY.inv) = _
    rw [Category.assoc, inr_relativeColimMap_assoc, ← kanLatchingIso_hom_latchingMap u Y d]
    exact eY.inv_hom_id_assoc _

/-- Theorem 9.4.3(1)(c), packaging Reedy cofibrancy together with the pointwise
weak equivalence already established in Theorem 9.4.2(1)(c). -/
theorem reedyCofibrant_pointwiseLeftKanMap_weakEquivalence_reedy
    [∀ a b : D₁, Finite (a ⟶ b)] {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y)
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension X) d))
      (_ : ∀ d, HasColimit (latchingDiagram (u.leftKanExtension Y) d)),
      IsReedyCofibrant (u.leftKanExtension X) ∧ IsReedyCofibrant (u.leftKanExtension Y) ∧
        ∀ d, WeakEquivalence ((pointwiseLeftKanMap u f).app d) := by
  obtain ⟨hKX, hLX, hRX⟩ := reedyCofibrant_leftKanExtension_reedy u X hX
  obtain ⟨hKY, hLY, hRY⟩ := reedyCofibrant_leftKanExtension_reedy u Y hY
  obtain ⟨_, _, hmap⟩ := reedyCofibrant_pointwiseLeftKanMap_weakEquivalence u hX hY f hw
  exact ⟨hKX, hKY, hLX, hLY, hRX, hRY, hmap⟩

end ABCCofibrations

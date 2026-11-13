/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBounded
public import ABCCofibrations.ReedyLayerMaps

/-!
# Maps of bounded direct diagrams

The gluing argument for an arbitrary maximal degree layer. No finiteness of
objects or hom-sets is assumed; CF5 is applied to the entire layer.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory ReedyLayer

/-- Bounded-degree part of Theorem 9.3.5(1)(c), without any finiteness assumptions. -/
theorem reedyCofibrant_colimMap_weakEquivalence_bounded
    (h5 : CoproductCofibrationAxiom.{w} M) (h5t : TrivialCoproductAxiom.{w} M) (N : ℕ) :
    ∀ (D : Type w) [SmallCategory D] (deg : D → ℕ),
      (∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h) →
      (∀ d, deg d < N) → ∀ (X Y : D ⥤ M)
        [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
        (f : X ⟶ Y), IsReedyCofibrant X → IsReedyCofibrant Y →
        (∀ d, WeakEquivalence (f.app d)) →
        ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f) := by
  induction N with
  | zero =>
    intro D _ deg hdeg hbound X Y _ _ f hX hY hw
    have : IsEmpty D := ⟨fun d ↦ Nat.not_lt_zero _ (hbound d)⟩
    obtain ⟨hCX, _⟩ := reedyCofibrant_colimit_bounded h5 0 D deg hdeg hbound X hX
    obtain ⟨hCY, _⟩ := reedyCofibrant_colimit_bounded h5 0 D deg hdeg hbound Y hY
    have := isIso_colimMap_of_isEmpty f
    exact ⟨hCX, hCY, weakEquivalence_of_isIso _⟩
  | succ N ih =>
    intro D _ deg hdeg hbound X Y _ _ f hX hY hw
    have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
    have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
      intro a b g
      rcases hdeg g with h | ⟨h, _⟩
      · exact h.le
      · exact (congrArg deg h).le
    let P := degreeBelow deg N
    have hopen : IsOpenDiagramSubcategory P := degreeBelow_isOpen deg hmono N
    have hmax : ∀ (d : D), ¬ P d → ∀ (e : D) (g : d ⟶ e),
        ∃ h : d = e, g = eqToHom h := by
      intro d hd e g
      rcases hdeg g with h | h
      · have hd' : ¬ deg d < N := hd
        have he := hbound e
        omega
      · exact h
    obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant P hopen X hX
    obtain ⟨_, hRY⟩ := OpenDiagramSubcategory.isReedyCofibrant P hopen Y hY
    obtain ⟨_, hOCX⟩ := reedyCofibrant_colimit_bounded h5 N P.FullSubcategory
      (fun e ↦ deg e.obj) (degreeCondition_fullSubcategory P deg hdeg)
      (fun e ↦ e.property) (P.ι ⋙ X) hRX
    obtain ⟨_, hOCY⟩ := reedyCofibrant_colimit_bounded h5 N P.FullSubcategory
      (fun e ↦ deg e.obj) (degreeCondition_fullSubcategory P deg hdeg)
      (fun e ↦ e.property) (P.ι ⋙ Y) hRY
    obtain ⟨_, _, hOW⟩ := ih P.FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory P deg hdeg) (fun e ↦ e.property)
      (P.ι ⋙ X) (P.ι ⋙ Y) (Functor.whiskerLeft P.ι f) hRX hRY (fun e ↦ hw e.obj)
    have hLW (d : Objects P) : WeakEquivalence (latchingObjMap f d.val) := by
      obtain ⟨_, hLX⟩ := isReedyCofibrant_latching deg hdeg X (d := d.val) hX
      obtain ⟨_, hLY⟩ := isReedyCofibrant_latching deg hdeg Y (d := d.val) hY
      have hdN : deg d.val = N := by
        have hd : ¬ deg d.val < N := d.property
        have hb := hbound d.val
        omega
      obtain ⟨_, _, hW⟩ := ih (LatchingCategory d.val) (fun j ↦ deg j.obj.left)
        (hdeg_latching deg hdeg d.val)
        (fun j ↦ by simpa [hdN] using deg_latching_lt deg hdeg d.val j)
        (latchingDiagram X d.val) (latchingDiagram Y d.val) (latchingNat f d.val)
        hLX hLY (fun j ↦ hw j.obj.left)
      exact hW
    have : ∀ d : Objects P, HasColimit (latchingDiagram X d.val) := fun _ ↦ inferInstance
    have : ∀ d : Objects P, HasColimit (latchingDiagram Y d.val) := fun _ ↦ inferInstance
    obtain ⟨_, _, hCX, sqX, _, _⟩ := colimit_isPushout_layer P hmax h5 X
      (fun d ↦ (hX d.val).1) (fun d ↦ (hX d.val).2) hOCX
    obtain ⟨_, _, hCY, sqY, _, _⟩ := colimit_isPushout_layer P hmax h5 Y
      (fun d ↦ (hY d.val).1) (fun d ↦ (hY d.val).2) hOCY
    have hXO (d : Objects P) : IsCofibrant (X.obj d.val) := by
      obtain ⟨_, _⟩ := hX d.val
      exact cofibrant_target (latchingMap X d.val)
    have hYO (d : Objects P) : IsCofibrant (Y.obj d.val) := by
      obtain ⟨_, _⟩ := hY d.val
      exact cofibrant_target (latchingMap Y d.val)
    have := h5.coproduct_cofibrant (fun d : Objects P ↦ latchingObj X d.val)
      (fun d ↦ (hX d.val).1)
    have := h5.coproduct_cofibrant (fun d : Objects P ↦ latchingObj Y d.val)
      (fun d ↦ (hY d.val).1)
    have : Cofibration (attachingMap P X) := h5.coproduct_cofibration
      (fun d : Objects P ↦ latchingMap X d.val)
      (fun d ↦ (hX d.val).1) (fun d ↦ (hX d.val).2)
    have : Cofibration (attachingMap P Y) := h5.coproduct_cofibration
      (fun d : Objects P ↦ latchingMap Y d.val)
      (fun d ↦ (hY d.val).1) (fun d ↦ (hY d.val).2)
    have := weakEquivalence_coproduct_map_of_weakEquivalence h5 h5t
      (fun d : Objects P ↦ latchingObjMap f d.val)
      (fun d ↦ (hX d.val).1) (fun d ↦ (hY d.val).1) hLW
    have := weakEquivalence_coproduct_map_of_weakEquivalence h5 h5t
      (fun d : Objects P ↦ f.app d.val) hXO hYO (fun d ↦ hw d.val)
    exact ⟨hCX, hCY, gluing_weakEquivalence sqX sqY
      (attachingMap_naturality P f) (boundaryMap_naturality P hmax f)
      (sumι_naturality P f) (colimit_pre_colimMap P.ι f)⟩

/-- Bounded-degree part of Theorem 9.3.5(1)(b), using only CF5(1). -/
theorem reedyCofibration_colimMap_bounded (h5 : CoproductCofibrationAxiom.{w} M) (N : ℕ) :
    ∀ (D : Type w) [SmallCategory D] (deg : D → ℕ),
      (∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h) →
      (∀ d, deg d < N) → ∀ (X Y : D ⥤ M)
        [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
        (f : X ⟶ Y), IsReedyCofibration f →
        ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f) := by
  induction N with
  | zero =>
    intro D _ deg hdeg hbound X Y _ _ f hf
    have : IsEmpty D := ⟨fun d ↦ Nat.not_lt_zero _ (hbound d)⟩
    obtain ⟨hCX, hCof⟩ := reedyCofibrant_colimit_bounded h5 0 D deg hdeg hbound X hf.1
    obtain ⟨hCY, _⟩ := reedyCofibrant_colimit_bounded h5 0 D deg hdeg hbound Y hf.2.1
    have := isIso_colimMap_of_isEmpty f
    exact ⟨hCX, hCY, cofibration_of_isIso _⟩
  | succ N ih =>
    intro D _ deg hdeg hbound X Y _ _ f hf
    have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
    have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
      intro a b g
      rcases hdeg g with h | ⟨h, _⟩
      · exact h.le
      · exact (congrArg deg h).le
    let P := degreeBelow deg N
    have hopen : IsOpenDiagramSubcategory P := degreeBelow_isOpen deg hmono N
    have hmax : ∀ (d : D), ¬ P d → ∀ (e : D) (g : d ⟶ e),
        ∃ h : d = e, g = eqToHom h := by
      intro d hd e g
      rcases hdeg g with h | h
      · have hd' : ¬ deg d < N := hd
        have he := hbound e
        omega
      · exact h
    obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration P hopen hf
    obtain ⟨_, hOCX⟩ := reedyCofibrant_colimit_bounded h5 N P.FullSubcategory
      (fun e ↦ deg e.obj) (degreeCondition_fullSubcategory P deg hdeg)
      (fun e ↦ e.property) (P.ι ⋙ X) hR.1
    obtain ⟨_, hOCY⟩ := reedyCofibrant_colimit_bounded h5 N P.FullSubcategory
      (fun e ↦ deg e.obj) (degreeCondition_fullSubcategory P deg hdeg)
      (fun e ↦ e.property) (P.ι ⋙ Y) hR.2.1
    obtain ⟨_, _, hOld⟩ := ih P.FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory P deg hdeg) (fun e ↦ e.property)
      (P.ι ⋙ X) (P.ι ⋙ Y) (Functor.whiskerLeft P.ι f) hR
    have hLf (d : Objects P) : Cofibration (latchingObjMap f d.val) := by
      obtain ⟨_, _, hL⟩ := isReedyCofibration_latching deg hdeg (d := d.val) hf
      have hdN : deg d.val = N := by
        have hd : ¬ deg d.val < N := d.property
        have hb := hbound d.val
        omega
      obtain ⟨_, _, hc⟩ := ih (LatchingCategory d.val) (fun j ↦ deg j.obj.left)
        (hdeg_latching deg hdeg d.val)
        (fun j ↦ by simpa [hdN] using deg_latching_lt deg hdeg d.val j)
        _ _ (latchingNat f d.val) hL
      exact hc
    obtain ⟨hCX, _⟩ := reedyCofibrant_colimit_bounded h5 (N + 1) D deg hdeg hbound X hf.1
    obtain ⟨hCY, _⟩ := reedyCofibrant_colimit_bounded h5 (N + 1) D deg hdeg hbound Y hf.2.1
    have : ∀ d : Objects P, HasColimit (latchingDiagram X d.val) := fun _ ↦ inferInstance
    have : ∀ d : Objects P, HasColimit (latchingDiagram Y d.val) := fun _ ↦ inferInstance
    obtain ⟨_, hc, _⟩ := cofibration_step P hmax f h5 hf hOCX hOCY hLf hOld
    exact ⟨hCX, hCY, hc⟩

end ABCCofibrations

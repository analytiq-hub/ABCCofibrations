/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayer
public import ABCCofibrations.ReedyDegreeColimits

/-!
# Bounded direct diagrams with arbitrary degree layers

Induction on a degree bound, attaching the entire maximal layer by Lemma
9.3.2(1). The indexing category need not have finitely many objects or arrows.
Only CF1–CF4 and CF5(1) are used.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- Existence and cofibrancy of colimits over any bounded direct category. -/
theorem reedyCofibrant_colimit_bounded (h5 : CoproductCofibrationAxiom.{w} M) (N : ℕ) :
    ∀ (D : Type w) [SmallCategory D] (deg : D → ℕ),
      (∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h) →
      (∀ d, deg d < N) → ∀ (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)],
        IsReedyCofibrant X → ∃ (_ : HasColimit X), IsCofibrant (colimit X) := by
  induction N with
  | zero =>
    intro D _ deg hdeg hbound X _ hX
    have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
    have : IsEmpty D := ⟨fun d ↦ Nat.not_lt_zero _ (hbound d)⟩
    have : Fintype D := Fintype.ofIsEmpty
    exact reedyCofibrant_colimit_finite _ D rfl X hX
  | succ N ih =>
    intro D _ deg hdeg hbound X _ hX
    have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
    have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
      intro a b f
      rcases hdeg f with h | ⟨h, _⟩
      · exact h.le
      · exact (congrArg deg h).le
    let P := degreeBelow deg N
    obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant P
      (degreeBelow_isOpen deg hmono N) X hX
    obtain ⟨hC, hCof⟩ := ih P.FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory P deg hdeg) (fun e ↦ e.property) (P.ι ⋙ X) hR
    have hmax : ∀ (d : D), ¬ P d → ∀ (e : D) (g : d ⟶ e),
        ∃ h : d = e, g = eqToHom h := by
      intro d hd e f
      rcases hdeg f with h | h
      · have hd' : ¬ deg d < N := hd
        have he := hbound e
        omega
      · exact h
    have : ∀ d : ReedyLayer.Objects P, HasColimit (latchingDiagram X d.val) :=
      fun d ↦ inferInstance
    obtain ⟨_, _, hCol, _, hCofX, _⟩ := colimit_isPushout_layer P hmax h5 X
      (fun d ↦ (hX d.val).1) (fun d ↦ (hX d.val).2) hCof
    exact ⟨hCol, hCofX⟩

/-- Successive truncation colimits are related by a cofibration, even when a
whole degree layer has infinitely many objects. -/
theorem cofibration_degreeColimitMap_of_layer {D : Type w} [SmallCategory D]
    (deg : D → ℕ)
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    (h5 : CoproductCofibrationAxiom.{w} M) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X d)] [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)]
    (hX : IsReedyCofibrant X)
    (hC : ∀ n, IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X))) (n : ℕ) :
    Cofibration (degreeColimitMap deg X (Nat.le_succ n)) := by
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b f
    rcases hdeg f with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  let R := degreeBelow deg (n + 1)
  let Q : ObjectProperty R.FullSubcategory := fun e ↦ deg e.obj < n
  let Y := R.ι ⋙ X
  let F : Q.FullSubcategory ⥤ (degreeBelow deg n).FullSubcategory :=
    (degreeBelow deg n).lift (Q.ι ⋙ R.ι) (fun e ↦ e.property)
  have : F.Full := ⟨fun f ↦ ⟨⟨⟨f.hom⟩⟩, rfl⟩⟩
  have : F.Faithful := by
    constructor
    intro a b f g h
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    exact congrArg (fun k : F.obj a ⟶ F.obj b ↦ k.hom) h
  have : F.EssSurj := ⟨fun e ↦
    ⟨⟨⟨e.obj, lt_of_lt_of_le e.property (Nat.le_succ n)⟩, e.property⟩, ⟨Iso.refl _⟩⟩⟩
  have : F.IsEquivalence := { }
  have : F.Final := Functor.final_of_isRightAdjoint F
  have hQ : HasColimit (Q.ι ⋙ Y) :=
    (Functor.Final.comp_hasColimit F (G := (degreeBelow deg n).ι ⋙ X))
  have hF : HasColimit (F ⋙ (degreeBelow deg n).ι ⋙ X) := hQ
  have := hC n
  have := cofibration_of_isIso (inv (colimit.pre ((degreeBelow deg n).ι ⋙ X) F))
  have hQC : IsCofibrant (colimit (Q.ι ⋙ Y)) :=
    cofibrant_target (inv (colimit.pre ((degreeBelow deg n).ι ⋙ X) F))
  obtain ⟨hLY, hRY⟩ := OpenDiagramSubcategory.isReedyCofibrant R
    (degreeBelow_isOpen deg hmono (n + 1)) X hX
  have hmax : ∀ (d : R.FullSubcategory), ¬ Q d → ∀ (e : R.FullSubcategory) (g : d ⟶ e),
      ∃ h : d = e, g = eqToHom h := by
    intro d hd e f
    rcases degreeCondition_fullSubcategory R deg hdeg f with h | h
    · have hd' : ¬ deg d.obj < n := hd
      have he : deg e.obj < n + 1 := e.property
      omega
    · exact h
  have : ∀ d : ReedyLayer.Objects Q, HasColimit (latchingDiagram Y d.val) :=
    fun d ↦ hLY d.val
  obtain ⟨_, _, _, _, _, hpre⟩ := colimit_isPushout_layer Q hmax h5 Y
    (fun d ↦ (hRY d.val).1) (fun d ↦ (hRY d.val).2) hQC
  have hfac : colimit.pre ((degreeBelow deg n).ι ⋙ X) F ≫
      degreeColimitMap deg X (Nat.le_succ n) = colimit.pre Y Q.ι := by
    apply colimit.hom_ext (F := Q.ι ⋙ Y)
    intro e
    change colimit.ι (F ⋙ (degreeBelow deg n).ι ⋙ X) e ≫
      colimit.pre ((degreeBelow deg n).ι ⋙ X) F ≫ degreeColimitMap deg X (Nat.le_succ n) = _
    erw [colimit.ι_pre_assoc, ι_degreeColimitMap, colimit.ι_pre]
    rfl
  rw [show degreeColimitMap deg X (Nat.le_succ n) =
      inv (colimit.pre ((degreeBelow deg n).ι ⋙ X) F) ≫ colimit.pre Y Q.ι by
    rw [IsIso.eq_inv_comp]
    exact hfac]
  infer_instance

end ABCCofibrations

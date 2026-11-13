/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallMaps
public import ABCCofibrations.ColimitComparison

/-!
# Cofibrations on colimits of arbitrary small direct diagrams

Theorem 9.3.5(1)(b), with whole degree layers attached using CF5(1),
then the sequential Reedy comparison using CF6(1).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- The relative comparison between two successive degree stages is a
cofibration. No finiteness condition is needed on either stage. -/
theorem reedyCofibration_degree_step {D : Type w} [SmallCategory D]
    (deg : D → ℕ)
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    (h5 : CoproductCofibrationAxiom.{w} M) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)]
    [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ Y)]
    (f : X ⟶ Y) (hf : IsReedyCofibration f) (n : ℕ) :
    ∃ (A : M) (l : (degreeColimits deg Y).obj n ⟶ A)
      (r : (degreeColimits deg X).obj (n + 1) ⟶ A)
      (c : A ⟶ (degreeColimits deg Y).obj (n + 1)),
      IsPushout ((degreeColimitsMap deg f).app n) ((degreeColimits deg X).map (succHom n)) l r ∧
        l ≫ c = (degreeColimits deg Y).map (succHom n) ∧
        r ≫ c = (degreeColimitsMap deg f).app (n + 1) ∧ Cofibration c := by
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  let R := degreeBelow deg (n + 1)
  let Q : ObjectProperty R.FullSubcategory := fun e ↦ deg e.obj < n
  let U := R.ι ⋙ X
  let V := R.ι ⋙ Y
  let g := Functor.whiskerLeft R.ι f
  obtain ⟨_, _, hg⟩ := OpenDiagramSubcategory.isReedyCofibration R
    (degreeBelow_isOpen deg hmono (n + 1)) hf
  have hdegR : ∀ {a b : R.FullSubcategory} (f : a ⟶ b),
      deg a.obj < deg b.obj ∨ ∃ h : a = b, f = eqToHom h :=
    degreeCondition_fullSubcategory R deg hdeg
  have hQopen : IsOpenDiagramSubcategory Q := by
    intro a b hab hb
    exact lt_of_le_of_lt (hmono hab.hom) hb
  obtain ⟨_, _, hq⟩ := OpenDiagramSubcategory.isReedyCofibration Q hQopen hg
  obtain ⟨_, hQU⟩ := reedyCofibrant_colimit_bounded h5 n Q.FullSubcategory
    (fun e ↦ deg e.obj.obj) (degreeCondition_fullSubcategory Q _ hdegR)
    (fun e ↦ e.property) (Q.ι ⋙ U) hq.1
  obtain ⟨_, hQV⟩ := reedyCofibrant_colimit_bounded h5 n Q.FullSubcategory
    (fun e ↦ deg e.obj.obj) (degreeCondition_fullSubcategory Q _ hdegR)
    (fun e ↦ e.property) (Q.ι ⋙ V) hq.2.1
  obtain ⟨_, _, hOld⟩ := reedyCofibration_colimMap_bounded h5 n Q.FullSubcategory
    (fun e ↦ deg e.obj.obj) (degreeCondition_fullSubcategory Q _ hdegR)
    (fun e ↦ e.property) _ _ (Functor.whiskerLeft Q.ι g) hq
  have hmax : ∀ (d : R.FullSubcategory), ¬ Q d → ∀ e (a : d ⟶ e),
      ∃ h : d = e, a = eqToHom h := by
    intro d hd e a
    rcases hdegR a with h | h
    · have hd' : ¬ deg d.obj < n := hd
      have he : deg e.obj < n + 1 := e.property
      omega
    · exact h
  have hLf (d : ReedyLayer.Objects Q) : Cofibration (latchingObjMap g d.val) := by
    obtain ⟨_, _, hL⟩ := isReedyCofibration_latching (fun e ↦ deg e.obj) hdegR
      (d := d.val) hg
    have hd : deg d.val.obj = n := by
      have hd' : ¬ deg d.val.obj < n := d.property
      have hb : deg d.val.obj < n + 1 := d.val.property
      omega
    obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_bounded h5 n (LatchingCategory d.val)
      (fun j ↦ deg j.obj.left.obj) (hdeg_latching (fun e ↦ deg e.obj) hdegR d.val)
      (fun j ↦ by simpa [hd] using deg_latching_lt (fun e ↦ deg e.obj) hdegR d.val j)
      _ _ (latchingNat g d.val) hL
    exact hc
  have : ∀ d : ReedyLayer.Objects Q, HasColimit (latchingDiagram U d.val) :=
    fun _ ↦ inferInstance
  have : ∀ d : ReedyLayer.Objects Q, HasColimit (latchingDiagram V d.val) :=
    fun _ ↦ inferInstance
  obtain ⟨hpo, _, hc⟩ := ReedyLayer.cofibration_step Q hmax g h5 hg hQU hQV hLf hOld
  have := hpo
  let I : (degreeBelow deg n).FullSubcategory ⥤ Q.FullSubcategory :=
    { obj := fun e ↦ ⟨⟨e.obj, lt_of_lt_of_le e.property (Nat.le_succ n)⟩, e.property⟩
      map := fun a ↦ ⟨⟨a.hom⟩⟩ }
  have : I.Full := ⟨fun a ↦ ⟨⟨a.hom.hom⟩, rfl⟩⟩
  have : I.Faithful := by
    constructor
    intro a b f g h
    cases f
    cases g
    cases h
    rfl
  have : I.EssSurj := ⟨fun e ↦ ⟨⟨e.obj.obj, e.property⟩, ⟨Iso.refl _⟩⟩⟩
  have : I.IsEquivalence := { }
  have : I.Final := Functor.final_of_isRightAdjoint I
  have : HasColimit (I ⋙ Q.ι ⋙ U) := inferInstanceAs
    (HasColimit ((degreeBelow deg n).ι ⋙ X))
  have : HasColimit (I ⋙ Q.ι ⋙ V) := inferInstanceAs
    (HasColimit ((degreeBelow deg n).ι ⋙ Y))
  obtain ⟨r, hs, hr⟩ := transfer_comparison I (Functor.whiskerLeft Q.ι g)
    ((colimit.cocone U).whisker Q.ι) ((colimit.cocone V).whisker Q.ι)
    (IsPushout.of_hasPushout (colimit.pre U Q.ι) (colimMap (Functor.whiskerLeft Q.ι g)))
    (inr_relativeColimMap Q.ι g)
  exact ⟨_, r, pushout.inl (colimit.pre U Q.ι)
    (colimMap (Functor.whiskerLeft Q.ι g)), relativeColimMap Q.ι g, hs.flip, hr,
    inl_relativeColimMap Q.ι g, hc⟩

/-- Theorem 9.3.5(1)(b) for every small direct category, using CF5(1) and CF6(1). -/
theorem reedyCofibration_colimMap_small {D : Type w} [SmallCategory D] [IsDirect D]
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] (f : X ⟶ Y) (hf : IsReedyCofibration f) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨hColX, hCofX, hMapX⟩ := reedyCofibrant_degreeColimits_data_small deg hdeg h5 X hf.1
  obtain ⟨hColY, hCofY, hMapY⟩ := reedyCofibrant_degreeColimits_data_small deg hdeg h5 Y hf.2.1
  have hτ (n : ℕ) : Cofibration ((degreeColimitsMap deg f).app n) := by
    obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) hf
    obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_bounded h5 n
      (degreeBelow deg n).FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory _ deg hdeg) (fun e ↦ e.property)
      _ _ (Functor.whiskerLeft (degreeBelow deg n).ι f) hR
    exact hc
  have h0X : IsCofibrant ((degreeColimits deg X).obj 0) := hCofX 0
  have h0Y : IsCofibrant ((degreeColimits deg Y).obj 0) := hCofY 0
  have : HasColimit (degreeColimits deg X) := h6.hasColimit _ h0X hMapX
  have : HasColimit (degreeColimits deg Y) := h6.hasColimit _ h0Y hMapY
  have hSC := cofibration_colimMap_of_reedy h6 (degreeColimitsMap deg f) h0X hMapX hτ
    (reedyCofibration_degree_step deg hdeg h5 f hf)
  have hCX : HasColimit X := hasColimit_of_degreeColimits deg X hmono
  have hCY : HasColimit Y := hasColimit_of_degreeColimits deg Y hmono
  refine ⟨hCX, hCY, ?_⟩
  have := isCofibrant_colimit_of_sequence h6 (degreeColimits deg X) h0X hMapX
  have := isCofibrant_colimit_of_sequence h6 (degreeColimits deg Y) h0Y hMapY
  let eX := degreeColimitIso deg X hmono
  let eY := degreeColimitIso deg Y hmono
  have := cofibration_of_isIso eX.hom
  have := cofibrant_target eX.hom
  have := cofibration_of_isIso eX.inv
  have := cofibration_of_isIso eY.hom
  rw [show colimMap f = eX.inv ≫ colimMap (degreeColimitsMap deg f) ≫ eY.hom by
    rw [Iso.eq_inv_comp]
    exact (degreeColimitIso_naturality deg hmono f).symm]
  infer_instance

omit [ABCPrecofibrationCategory M] in
/-- Theorem 9.3.5(1)(b) for an ABC cofibration category. -/
theorem reedyCofibration_colimMap_of_cofibrationCategory
    [ABCCofibrationCategory.{w} M] {D : Type w} [SmallCategory D] [IsDirect D]
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] (f : X ⟶ Y) (hf : IsReedyCofibration f) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f) :=
  reedyCofibration_colimMap_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom f hf

end ABCCofibrations

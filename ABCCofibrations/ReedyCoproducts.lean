/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySequentialColimits
public import ABCCofibrations.DiscreteColimitCofibrations

/-! # Coproducts of Reedy cofibrant diagrams and Reedy cofibrations -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] {ι : Type w}
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]
  (A : ι → D ⥤ M) [∀ i d, HasColimit (latchingDiagram (A i) d)]
  (hA : ∀ i, IsReedyCofibrant (A i))

local instance family_hasLatching :
    ∀ (j : Discrete ι) d, HasColimit (latchingDiagram ((Discrete.functor A).obj j) d) :=
  fun j d ↦ inferInstanceAs (HasColimit (latchingDiagram (A j.as) d))

include hA in
/-- The pointwise coproducts of a Reedy cofibrant family exist. -/
lemma hasColimit_evaluation_of_reedy_family (d : D) :
    HasColimit ((Discrete.functor A).flip.obj d) :=
  hasColimit_discrete_of_cofibrant _ (fun j ↦ (hA j.as).isCofibrant_obj d)

variable [∀ d, HasColimit ((Discrete.functor A).flip.obj d)]

include hA in
/-- The coproduct of latching objects is cofibrant and the induced latching-map
coproduct is a cofibration. -/
lemma reedy_family_latching_data (d : D) :
    ∃ (_ : HasColimit (latchingColimits (Discrete.functor A) d)),
      IsCofibrant (colimit (latchingColimits (Discrete.functor A) d)) ∧
        Cofibration (colimMap (latchingMaps (Discrete.functor A) d)) := by
  have hL (j : Discrete ι) : IsCofibrant ((latchingColimits (Discrete.functor A) d).obj j) :=
    (hA j.as d).1
  have hCol := hasColimit_discrete_of_cofibrant (latchingColimits (Discrete.functor A) d) hL
  exact ⟨hCol, isCofibrant_colimit_discrete _ hL,
    cofibration_colimMap_discrete (latchingMaps (Discrete.functor A) d) hL
      (fun j ↦ (hA j.as d).2)⟩

omit [∀ d, HasColimit ((Discrete.functor A).flip.obj d)] in
include hA in
/-- CF5: coproducts of Reedy cofibrant diagrams exist and are Reedy cofibrant. -/
theorem reedy_coproduct :
    ∃ (_ : HasCoproduct A) (_ : ∀ d, HasColimit (latchingDiagram (∐ A) d)),
      IsReedyCofibrant (∐ A) := by
  have hEval : ∀ d, HasColimit ((Discrete.functor A).flip.obj d) :=
    hasColimit_evaluation_of_reedy_family A hA
  have hCol : HasCoproduct A := inferInstance
  choose hLo hLC hτ using reedy_family_latching_data A hA
  have key (d : D) := reedy_colimit_at (Discrete.functor A) d (hLC d) (hτ d)
  choose hLatch hReedy using key
  exact ⟨hCol, hLatch, hReedy⟩

omit [∀ d, HasColimit ((Discrete.functor A).flip.obj d)] in
/-- CF5 preserves Reedy cofibrations between arbitrary small families. -/
theorem reedyCofibration_coproduct {B : ι → D ⥤ M}
    [∀ i d, HasColimit (latchingDiagram (B i) d)]
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsReedyCofibration (f i)) :
    ∃ (_ : HasCoproduct A) (_ : HasCoproduct B)
      (_ : ∀ d, HasColimit (latchingDiagram (∐ A) d))
      (_ : ∀ d, HasColimit (latchingDiagram (∐ B) d)),
      IsReedyCofibration (Limits.Sigma.map f) := by
  have hAX := fun i ↦ (hf i).1
  have hBY := fun i ↦ (hf i).2.1
  have hEvalX := hasColimit_evaluation_of_reedy_family A hAX
  have hEvalY := hasColimit_evaluation_of_reedy_family B hBY
  obtain ⟨hCX, hLX, hX⟩ := reedy_coproduct A hAX
  obtain ⟨hCY, hLY, hY⟩ := reedy_coproduct B hBY
  choose hLoX hLCX hτX using reedy_family_latching_data A hAX
  choose hLoY hLCY hτY using reedy_family_latching_data B hBY
  let FX := Discrete.functor A
  let FY := Discrete.functor B
  let θ : FX ⟶ FY := Discrete.natTrans (fun j ↦ f j.as)
  have heq : colimMap θ = Limits.Sigma.map f := by
    apply Sigma.hom_ext
    intro i
    simp [θ]
    rfl
  refine ⟨hCX, hCY, hLX, hLY, ?_⟩
  rw [← heq]
  refine ⟨hX, hY, fun d ↦ ?_⟩
  choose Q l t k hQ hl ht hk using (fun i ↦ (hf i).2.2 d)
  have hQC (i : ι) : IsCofibrant (Q i) := by
    obtain ⟨hLA, hiA⟩ := (hf i).1 d
    have := ((hf i).2.1 d).1
    have := cofibration_of_isPushout (hQ i)
    exact cofibrant_target (t i)
  let QF := Discrete.functor Q
  have hColQ : HasColimit QF := hasColimit_discrete_of_cofibrant QF (fun j ↦ hQC j.as)
  let lN : FX ⋙ (evaluation D M).obj d ⟶ QF := Discrete.natTrans (fun j ↦ l j.as)
  let tN : latchingColimits FY d ⟶ QF := Discrete.natTrans (fun j ↦ t j.as)
  let kN : QF ⟶ FY ⋙ (evaluation D M).obj d := Discrete.natTrans (fun j ↦ k j.as)
  have hK : Cofibration (colimMap kN) :=
    cofibration_colimMap_discrete kN (fun j ↦ hQC j.as) (fun j ↦ hk j.as)
  have := hLCX d
  have := hLCY d
  have := hτX d
  have : HasPushout (colimMap (latchingMaps FX d))
      (colimMap (latchingColimitsMap FX d θ)) := hasPushout _ _
  obtain ⟨_, hs⟩ := colimit_isPushout_of_pointwise
    (α := latchingMaps FX d) (β := latchingColimitsMap FX d θ) (γ := lN) (δ := tN)
    (fun j ↦ hQ j.as) (IsPushout.of_hasPushout _ _)
  let eLX := latchingColimitIso FX d
  let eLY := latchingColimitIso FY d
  let eOX := preservesColimitIso ((evaluation D M).obj d) FX
  let eOY := preservesColimitIso ((evaluation D M).obj d) FY
  have hTop : colimMap (latchingMaps FX d) ≫ eOX.inv = eLX.hom ≫ latchingMap (∐ A) d :=
    (Iso.comp_inv_eq eOX).2 (by simpa only [Category.assoc] using
      (latchingColimitIso_hom_latchingMap FX d).symm)
  have hs' : IsPushout (latchingMap (∐ A) d) (latchingObjMap (colimMap θ) d)
      (eOX.hom ≫ colimMap lN) (eLY.inv ≫ colimMap tN) :=
    hs.of_iso eLX eOX.symm eLY (Iso.refl _) hTop
      (latchingColimitIso_naturality FX d θ) (by simp) (by simp)
  have := isCofibrant_colimit_discrete (FY ⋙ (evaluation D M).obj d)
    (fun j ↦ (hBY j.as).isCofibrant_obj d)
  have := cofibration_of_isIso eOY.inv
  let c := colimMap kN ≫ eOY.inv
  have hc : Cofibration c := by infer_instance
  refine ⟨colimit QF, _, _, c, hs', ?_, ?_, hc⟩
  · apply (isColimitOfPreserves ((evaluation D M).obj d) (colimit.isColimit FX)).hom_ext
    intro j
    have hEX : (colimit.ι FX j).app d ≫ eOX.hom =
        colimit.ι (FX ⋙ (evaluation D M).obj d) j :=
      ι_preservesColimitIso_hom ((evaluation D M).obj d) FX j
    have hEY : colimit.ι (FY ⋙ (evaluation D M).obj d) j ≫ eOY.inv =
        (colimit.ι FY j).app d :=
      ι_preservesColimitIso_inv ((evaluation D M).obj d) FY j
    change (colimit.ι FX j).app d ≫ (eOX.hom ≫ colimMap lN) ≫
      (colimMap kN ≫ eOY.inv) = (colimit.ι FX j).app d ≫ (colimMap θ).app d
    simp only [Category.assoc]
    erw [reassoc_of% hEX, ι_colimMap_assoc, ι_colimMap_assoc]
    change l j.as ≫ k j.as ≫ colimit.ι (FY ⋙ (evaluation D M).obj d) j ≫ eOY.inv = _
    rw [← Category.assoc (l j.as), hl, hEY]
    exact (congrArg (fun q ↦ q.app d) (ι_colimMap θ j)).symm
  · have hComp : colimMap tN ≫ colimMap kN = colimMap (latchingMaps FY d) := by
      apply colimit.hom_ext (F := latchingColimits FY d)
      intro j
      rw [ι_colimMap_assoc, ι_colimMap, ι_colimMap]
      change t j.as ≫ k j.as ≫ _ = _
      rw [← Category.assoc, ht]
      rfl
    change (eLY.inv ≫ colimMap tN) ≫ (colimMap kN ≫ eOY.inv) = _
    rw [Category.assoc, ← Category.assoc (colimMap tN), hComp]
    rw [← latchingColimitIso_hom_latchingMap FY d]
    simp [eLY, eOY]
    rfl

end ABCCofibrations

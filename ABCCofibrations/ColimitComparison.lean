/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Comparison maps for colimits

Categorical comparison maps used by Reedy restrictions and relative colimits.
No homotopical assumptions are needed.
-/

@[expose] public section

open CategoryTheory Limits
namespace ABCCofibrations

variable {M J J' : Type*} [Category M] [Category J] [Category J']
  (F : J' ⥤ J) [F.Final]

/-- Relative latching comparisons transfer along a final functor. -/
lemma transfer_comparison {K K' : J ⥤ M} [HasColimit K] [HasColimit K'] [HasColimit (F ⋙ K)]
    [HasColimit (F ⋙ K')] (α : K ⟶ K') (c : Cocone K) (c' : Cocone K') {P : M}
    {l : c.pt ⟶ P} {r : colimit K' ⟶ P} {k : P ⟶ c'.pt}
    (hP : IsPushout (colimit.desc K c) (colimMap α) l r) (hr : r ≫ k = colimit.desc K' c') :
    ∃ r' : colimit (F ⋙ K') ⟶ P, IsPushout (colimit.desc (F ⋙ K) (c.whisker F))
      (colimMap (Functor.whiskerLeft F α)) l r' ∧
        r' ≫ k = colimit.desc (F ⋙ K') (c'.whisker F) := by
  have : IsIso (colimit.pre K F) := inferInstance
  have : IsIso (colimit.pre K' F) := inferInstance
  refine ⟨colimit.pre K' F ≫ r, ?_, by rw [Category.assoc, hr, colimit.pre_desc]⟩
  refine hP.of_iso (asIso (colimit.pre K F)).symm (Iso.refl _) (asIso (colimit.pre K' F)).symm
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [← colimit.pre_desc]
  · simp only [Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    apply colimit.hom_ext
    intro j
    simp


section Relative

variable {E D C : Type*} [Category E] [Category D] [Category C]
  (i : E ⥤ D) {X Y : D ⥤ C} (f : X ⟶ Y)
  [HasColimit X] [HasColimit Y] [HasColimit (i ⋙ X)] [HasColimit (i ⋙ Y)]

/-- Naturality of restriction of a colimit. -/
theorem colimit_pre_colimMap :
    colimit.pre X i ≫ colimMap f =
      colimMap (Functor.whiskerLeft i f) ≫ colimit.pre Y i := by
  apply colimit.hom_ext
  intro e
  simp

/-- The relative colimit comparison for a map of diagrams. -/
noncomputable def relativeColimMap
    [HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f))] :
    pushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)) ⟶ colimit Y :=
  pushout.desc (colimMap f) (colimit.pre Y i) (colimit_pre_colimMap i f)

@[reassoc (attr := simp)]
lemma inl_relativeColimMap
    [HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f))] :
    pushout.inl _ _ ≫ relativeColimMap i f = colimMap f :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma inr_relativeColimMap
    [HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f))] :
    pushout.inr _ _ ≫ relativeColimMap i f = colimit.pre Y i :=
  pushout.inr_desc _ _ _

/-- A colimit map can be computed after restriction along a final functor. -/
lemma colimMap_eq_inv_pre_comp [i.Final] :
    colimMap f = inv (colimit.pre X i) ≫
      colimMap (Functor.whiskerLeft i f) ≫ colimit.pre Y i := by
  rw [IsIso.eq_inv_comp]
  exact colimit_pre_colimMap i f

end Relative

end ABCCofibrations

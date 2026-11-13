/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ColimitComparison
public import Mathlib.CategoryTheory.Limits.Opposites

/-! # Limit restriction and opposite colimit restriction -/

@[expose] public section

open CategoryTheory Limits
namespace ABCCofibrations

/-- The opposite of restriction of a limit is restriction of a colimit,
under the canonical comparison isomorphisms. -/
lemma op_limit_pre {E D M : Type*} [Category E] [Category D] [Category M]
    (i : E ⥤ D) (X : D ⥤ M) [HasLimit X] [HasLimit (i ⋙ X)] :
    letI : HasColimit (i.op ⋙ X.op) := hasColimit_of_iso (Functor.opComp i X).symm
    (limit.pre X i).op = (colimitOpIsoOpLimit (i ⋙ X)).inv ≫
      colimit.pre X.op i.op ≫ (colimitOpIsoOpLimit X).hom := by
  have : HasColimit (i.op ⋙ X.op) := hasColimit_of_iso (Functor.opComp i X).symm
  rw [Iso.eq_inv_comp]
  apply colimit.hom_ext
  intro e
  rw [ι_comp_colimitOpIsoOpLimit_hom_assoc, ← op_comp, limit.pre_π]
  change _ = colimit.ι (i.op ⋙ X.op) e ≫ colimit.pre X.op i.op ≫ _
  rw [colimit.ι_pre_assoc, ι_comp_colimitOpIsoOpLimit_hom]
  rfl

/-- A map of limits compared with the colimit map of opposite diagrams. -/
lemma op_limMap_comparison {D M : Type*} [Category D] [Category M]
    {X Y : D ⥤ M} [HasLimit X] [HasLimit Y] (f : X ⟶ Y) :
    (limMap f).op = (colimitOpIsoOpLimit Y).inv ≫ colimMap (NatTrans.op f) ≫
      (colimitOpIsoOpLimit X).hom := by
  rw [Iso.eq_inv_comp]
  apply colimit.hom_ext
  intro j
  rw [ι_comp_colimitOpIsoOpLimit_hom_assoc, ← op_comp, limMap_π, op_comp,
    ι_colimMap_assoc, ι_comp_colimitOpIsoOpLimit_hom]
  rfl

section Relative

variable {E D M : Type*} [Category E] [Category D] [Category M]
  (i : E ⥤ D) {X Y : D ⥤ M} (f : X ⟶ Y)
  [HasLimit X] [HasLimit Y] [HasLimit (i ⋙ X)] [HasLimit (i ⋙ Y)]

/-- Naturality of restriction of a limit. -/
lemma limit_pre_limMap :
    limMap f ≫ limit.pre Y i = limit.pre X i ≫ limMap (Functor.whiskerLeft i f) := by
  apply limit.hom_ext
  intro e
  simp

/-- The relative limit comparison for a map of diagrams. -/
noncomputable def relativeLimMap
    [HasPullback (limit.pre Y i) (limMap (Functor.whiskerLeft i f))] :
    limit X ⟶ pullback (limit.pre Y i) (limMap (Functor.whiskerLeft i f)) :=
  pullback.lift (limMap f) (limit.pre X i) (limit_pre_limMap i f)

@[reassoc (attr := simp)]
lemma relativeLimMap_fst
    [HasPullback (limit.pre Y i) (limMap (Functor.whiskerLeft i f))] :
    relativeLimMap i f ≫ pullback.fst _ _ = limMap f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeLimMap_snd
    [HasPullback (limit.pre Y i) (limMap (Functor.whiskerLeft i f))] :
    relativeLimMap i f ≫ pullback.snd _ _ = limit.pre X i := pullback.lift_snd _ _ _

variable [HasColimit (i.op ⋙ X.op)] [HasColimit (i.op ⋙ Y.op)]
  [HasPullback (limit.pre Y i) (limMap (Functor.whiskerLeft i f))]

omit [HasLimit X] [HasColimit (i.op ⋙ X.op)] in
/-- The opposite relative limit square, expressed in chosen colimit objects. -/
lemma relativeLimitOp_isPushout :
    IsPushout (colimit.pre Y.op i.op)
      (colimMap (NatTrans.op (Functor.whiskerLeft i f)))
      ((colimitOpIsoOpLimit Y).hom ≫ (pullback.fst (limit.pre Y i)
        (limMap (Functor.whiskerLeft i f))).op)
      ((colimitOpIsoOpLimit (i ⋙ X)).hom ≫ (pullback.snd (limit.pre Y i)
        (limMap (Functor.whiskerLeft i f))).op) := by
  refine (IsPullback.of_hasPullback (limit.pre Y i)
    (limMap (Functor.whiskerLeft i f))).op.flip.of_iso
    (colimitOpIsoOpLimit (i ⋙ Y)).symm (colimitOpIsoOpLimit Y).symm
    (colimitOpIsoOpLimit (i ⋙ X)).symm (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, op_limit_pre, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · simp only [Iso.symm_hom, op_limMap_comparison, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

variable [HasPushout (colimit.pre Y.op i.op)
  (colimMap (Functor.whiskerLeft i.op (NatTrans.op f)))]

local instance : HasPushout (colimit.pre Y.op i.op)
    (colimMap (NatTrans.op (Functor.whiskerLeft i f))) :=
  ‹HasPushout (colimit.pre Y.op i.op) (colimMap (Functor.whiskerLeft i.op (NatTrans.op f)))›

/-- The relative limit comparison is the opposite relative colimit comparison
under the canonical isomorphisms. -/
theorem op_relativeLimMap :
    (relativeLimMap i f).op = (relativeLimitOp_isPushout i f).isoPushout.hom ≫
      relativeColimMap i.op (NatTrans.op f) ≫ (colimitOpIsoOpLimit X).hom := by
  apply (relativeLimitOp_isPushout i f).hom_ext
  · rw [IsPushout.inl_isoPushout_hom_assoc]
    change ((colimitOpIsoOpLimit Y).hom ≫ (pullback.fst _ _).op) ≫
      (relativeLimMap i f).op = _
    rw [Category.assoc, ← op_comp, relativeLimMap_fst]
    change _ = pushout.inl (colimit.pre Y.op i.op)
      (colimMap (Functor.whiskerLeft i.op (NatTrans.op f))) ≫
        relativeColimMap i.op (NatTrans.op f) ≫ _
    rw [inl_relativeColimMap_assoc, op_limMap_comparison, Iso.hom_inv_id_assoc]
  · rw [IsPushout.inr_isoPushout_hom_assoc]
    change ((colimitOpIsoOpLimit (i ⋙ X)).hom ≫ (pullback.snd _ _).op) ≫
      (relativeLimMap i f).op = _
    rw [Category.assoc, ← op_comp, relativeLimMap_snd]
    change _ = pushout.inr (colimit.pre Y.op i.op)
      (colimMap (Functor.whiskerLeft i.op (NatTrans.op f))) ≫
        relativeColimMap i.op (NatTrans.op f) ≫ _
    rw [inr_relativeColimMap_assoc, op_limit_pre, Iso.hom_inv_id_assoc]

end Relative

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayer
public import ABCCofibrations.CoproductPushouts

/-! # Naturality of simultaneous layer attachment -/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ReedyLayer

variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)
  (hmax : ∀ (d : D), ¬ P d → ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
  {M : Type u} [Category.{v} M] {X Y : D ⥤ M}
  [∀ d : Objects P, HasColimit (latchingDiagram X d.val)]
  [∀ d : Objects P, HasColimit (latchingDiagram Y d.val)]
  [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)] (f : X ⟶ Y)

/-- The individual boundary map commutes with a map of source diagrams. -/
lemma boundary_naturality (d : Objects P) :
    boundary P hmax X d ≫ colimMap (Functor.whiskerLeft P.ι f) =
      latchingObjMap f d.val ≫ boundary P hmax Y d := by
  apply colimit.hom_ext
  intro j
  erw [ι_boundary_assoc, ι_colimMap, ι_latchingObjMap_assoc, ι_boundary]
  rfl

variable [HasCoproduct (fun d : Objects P ↦ latchingObj X d.val)]
  [HasCoproduct (fun d : Objects P ↦ latchingObj Y d.val)]
  [HasCoproduct (fun d : Objects P ↦ X.obj d.val)]
  [HasCoproduct (fun d : Objects P ↦ Y.obj d.val)]

omit [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)] in
/-- The square between coproducts of attaching maps commutes. -/
lemma attachingMap_naturality :
    attachingMap P X ≫ Limits.Sigma.map (fun d : Objects P ↦ f.app d.val) =
      Limits.Sigma.map (fun d : Objects P ↦ latchingObjMap f d.val) ≫ attachingMap P Y := by
  apply Sigma.hom_ext
  intro d
  simp only [attachingMap, Sigma.ι_map_assoc, Sigma.ι_map]
  simpa only [Category.assoc] using congrArg
    (· ≫ Sigma.ι (fun d : Objects P ↦ Y.obj d.val) d) (latchingObjMap_latchingMap f d.val).symm

omit [HasCoproduct (fun d : Objects P ↦ X.obj d.val)]
  [HasCoproduct (fun d : Objects P ↦ Y.obj d.val)] in
/-- The coproduct boundary maps commute with maps of diagrams. -/
lemma boundaryMap_naturality :
    boundaryMap P hmax X ≫ colimMap (Functor.whiskerLeft P.ι f) =
      Limits.Sigma.map (fun d : Objects P ↦ latchingObjMap f d.val) ≫ boundaryMap P hmax Y := by
  apply Sigma.hom_ext
  intro d
  simp only [boundaryMap, Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc]
  exact boundary_naturality P hmax f d

variable [HasColimit X] [HasColimit Y]

omit [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)]
  [HasCoproduct (fun d : Objects P ↦ latchingObj X d.val)]
  [HasCoproduct (fun d : Objects P ↦ latchingObj Y d.val)]
  [∀ d : Objects P, HasColimit (latchingDiagram X d.val)]
  [∀ d : Objects P, HasColimit (latchingDiagram Y d.val)] in
/-- The coproduct leg into the whole colimit is natural. -/
lemma sumι_naturality :
    Sigma.desc (fun d : Objects P ↦ colimit.ι X d.val) ≫ colimMap f =
      Limits.Sigma.map (fun d : Objects P ↦ f.app d.val) ≫
        Sigma.desc (fun d : Objects P ↦ colimit.ι Y d.val) := by
  apply Sigma.hom_ext
  intro d
  simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc, Sigma.ι_comp_desc, ι_colimMap]

section Cofibrations

variable [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

omit [∀ d : Objects P, HasColimit (latchingDiagram X d.val)]
  [∀ d : Objects P, HasColimit (latchingDiagram Y d.val)]
  [HasCoproduct (fun d : Objects P ↦ latchingObj X d.val)]
  [HasCoproduct (fun d : Objects P ↦ latchingObj Y d.val)]
  [HasCoproduct (fun d : Objects P ↦ X.obj d.val)]
  [HasCoproduct (fun d : Objects P ↦ Y.obj d.val)] in
include hmax in
/-- Gluing across a whole layer preserves cofibrations and gives the relative
comparison for the inclusion of the old subcategory. -/
theorem cofibration_step (h5 : CoproductCofibrationAxiom.{w} M)
    [∀ d : D, HasColimit (latchingDiagram X d)]
    [∀ d : D, HasColimit (latchingDiagram Y d)] (hf : IsReedyCofibration f)
    (hCX : IsCofibrant (colimit (P.ι ⋙ X))) (hCY : IsCofibrant (colimit (P.ι ⋙ Y)))
    (hLf : ∀ d : Objects P, Cofibration (latchingObjMap f d.val))
    (hOld : Cofibration (colimMap (Functor.whiskerLeft P.ι f))) :
    ∃ (_ : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f))),
      Cofibration (colimMap f) ∧ Cofibration (relativeColimMap P.ι f) := by
  classical
  obtain ⟨_, _, _, sqX, _, hpreX⟩ := colimit_isPushout_layer P hmax h5 X
    (fun d ↦ (hf.1 d.val).1) (fun d ↦ (hf.1 d.val).2) hCX
  obtain ⟨_, _, _, sqY, _, _⟩ := colimit_isPushout_layer P hmax h5 Y
    (fun d ↦ (hf.2.1 d.val).1) (fun d ↦ (hf.2.1 d.val).2) hCY
  choose Q l r c hQ hl hr hc using (fun d : Objects P ↦ hf.2.2 d.val)
  have hQC (d : Objects P) : IsCofibrant (Q d) := by
    obtain ⟨hL, hi⟩ := hf.1 d.val
    obtain ⟨hLY, _⟩ := hf.2.1 d.val
    have := cofibration_of_isPushout (hQ d)
    exact cofibrant_target (r d)
  have hSumQ := h5.hasCoproduct Q hQC
  have := h5.coproduct_cofibrant Q hQC
  have hsum := isPushout_sigmaMap (fun d : Objects P ↦ latchingMap X d.val)
    (fun d : Objects P ↦ latchingObjMap f d.val) l r hQ
  have hSumC := h5.coproduct_cofibration c hQC hc
  have := h5.coproduct_cofibrant (fun d : Objects P ↦ latchingObj X d.val)
    (fun d ↦ (hf.1 d.val).1)
  have := h5.coproduct_cofibrant (fun d : Objects P ↦ latchingObj Y d.val)
    (fun d ↦ (hf.2.1 d.val).1)
  have hAttach : Cofibration (attachingMap P X) := h5.coproduct_cofibration
    (fun d : Objects P ↦ latchingMap X d.val)
    (fun d ↦ (hf.1 d.val).1) (fun d ↦ (hf.1 d.val).2)
  have hSumLf := h5.coproduct_cofibration (fun d : Objects P ↦ latchingObjMap f d.val)
    (fun d ↦ (hf.1 d.val).1) hLf
  have : HasPushout (attachingMap P X) (Limits.Sigma.map (fun d : Objects P ↦
      latchingObjMap f d.val)) := hasPushout _ _
  have := cofibration_of_isPushout (IsPushout.of_hasPushout (attachingMap P X)
    (Limits.Sigma.map (fun d : Objects P ↦ latchingObjMap f d.val)))
  have := cofibrant_target (pushout.inr (attachingMap P X)
    (Limits.Sigma.map (fun d : Objects P ↦ latchingObjMap f d.val)))
  have hInv := cofibration_of_isIso hsum.isoPushout.inv
  have hfront : Cofibration (pushout.desc (Limits.Sigma.map (fun d : Objects P ↦ f.app d.val))
      (attachingMap P Y) (attachingMap_naturality P f)) := by
    rw [show pushout.desc (Limits.Sigma.map (fun d : Objects P ↦ f.app d.val))
        (attachingMap P Y) (attachingMap_naturality P f) =
        hsum.isoPushout.inv ≫ Limits.Sigma.map c by
      apply pushout.hom_ext
      · rw [pushout.inl_desc, hsum.inl_isoPushout_inv_assoc, Sigma.map_comp_map]
        simp only [hl]
      · rw [pushout.inr_desc, hsum.inr_isoPushout_inv_assoc, Sigma.map_comp_map]
        simp only [hr, attachingMap]]
    infer_instance
  have hpo : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f)) :=
    hasPushout _ _
  refine ⟨hpo, ?_⟩
  exact (gluing_cofibration sqX sqY (attachingMap_naturality P f)
    (boundaryMap_naturality P hmax f) (sumι_naturality P f)
    (colimit_pre_colimMap P.ι f)).2

end Cofibrations

end ABCCofibrations.ReedyLayer

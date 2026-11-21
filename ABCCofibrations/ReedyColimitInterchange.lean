/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBasic
public import ABCCofibrations.PointwiseColimitInterchange

/-! # Latching objects commute with individually existing pointwise colimits -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w z v u
open CategoryTheory Limits
namespace ABCCofibrations

variable {J : Type z} [SmallCategory J] {D : Type w} [SmallCategory D]
  {M : Type u} [Category.{v} M] (F : J ⥤ D ⥤ M)
  [∀ j d, HasColimit (latchingDiagram (F.obj j) d)] (d : D)

/-- Restrict a diagram to the predecessors of `d`. -/
abbrev latchingRestriction : (D ⥤ M) ⥤ LatchingCategory d ⥤ M :=
  (Functor.whiskeringLeft _ _ _).obj (ObjectProperty.ι _ ⋙ Over.forget d)

local instance hasColimit_latchingRestriction :
    ∀ j, HasColimit ((F ⋙ latchingRestriction d).obj j) :=
  fun j ↦ inferInstanceAs (HasColimit (latchingDiagram (F.obj j) d))

/-- The diagram of the individually existing latching objects. -/
noncomputable abbrev latchingColimits : J ⥤ M :=
  PointwiseColimitInterchange.colimitObjects (F ⋙ latchingRestriction d)

/-- The latching maps form a natural transformation to evaluation at `d`. -/
noncomputable def latchingMaps : latchingColimits F d ⟶ F ⋙ (evaluation D M).obj d where
  app j := latchingMap (F.obj j) d
  naturality _ _ f := latchingObjMap_latchingMap (F.map f) d


/-- A map of diagram families induces the corresponding map of latching-colimit diagrams. -/
noncomputable def latchingColimitsMap {G : J ⥤ D ⥤ M}
    [∀ j e, HasColimit (latchingDiagram (G.obj j) e)] (θ : F ⟶ G) :
    latchingColimits F d ⟶ latchingColimits G d where
  app j := latchingObjMap (θ.app j) d
  naturality j j' f := by
    apply colimit.hom_ext (F := latchingDiagram (F.obj j) d)
    intro k
    erw [ι_latchingObjMap_assoc, ι_latchingObjMap, ι_latchingObjMap_assoc, ι_latchingObjMap]
    simp only [latchingNat_app, ← Category.assoc]
    exact congrArg (fun t ↦ t.app k.obj.left ≫
      colimit.ι (latchingDiagram (G.obj j') d) k) (θ.naturality f)

variable [∀ e, HasColimit (F.flip.obj e)] [HasColimit F]
  [HasColimit (latchingColimits F d)]

/-- The restricted colimit cocone is a pointwise colimit at each predecessor. -/
noncomputable def isColimit_latching_evaluation (j : LatchingCategory d) :
    IsColimit (((evaluation (LatchingCategory d) M).obj j).mapCocone
      ((latchingRestriction d).mapCocone (colimit.cocone F))) :=
  isColimitOfPreserves ((evaluation D M).obj j.obj.left) (colimit.isColimit F)

/-- A latching cocone with vertex the colimit of the latching objects. -/
noncomputable def latchingColimitCocone : Cocone (latchingDiagram (colimit F) d) :=
  PointwiseColimitInterchange.cocone (F ⋙ latchingRestriction d)
    ((latchingRestriction d).mapCocone (colimit.cocone F)) (isColimit_latching_evaluation F d)

/-- The colimit of the latching objects is the required latching colimit. -/
noncomputable def isColimitLatchingColimitCocone : IsColimit (latchingColimitCocone F d) :=
  PointwiseColimitInterchange.isColimitCocone (F ⋙ latchingRestriction d)
    ((latchingRestriction d).mapCocone (colimit.cocone F)) (isColimit_latching_evaluation F d)

/-- Existence of the latching colimit for the whole pointwise colimit. -/
theorem hasColimit_latching_colimit : HasColimit (latchingDiagram (colimit F) d) :=
  ⟨⟨⟨_, isColimitLatchingColimitCocone F d⟩⟩⟩

variable [HasColimit (latchingDiagram (colimit F) d)]

/-- The canonical interchange isomorphism for latching objects. -/
noncomputable def latchingColimitIso : colimit (latchingColimits F d) ≅
    latchingObj (colimit F) d :=
  (isColimitLatchingColimitCocone F d).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc]
lemma ι_latchingColimitIso_hom (j : J) :
    colimit.ι (latchingColimits F d) j ≫ (latchingColimitIso F d).hom =
      latchingObjMap (colimit.ι F j) d := by
  apply colimit.hom_ext (F := latchingDiagram (F.obj j) d)
  intro k
  rw [ι_latchingObjMap]
  have h := PointwiseColimitInterchange.leg_fac (F ⋙ latchingRestriction d)
    ((latchingRestriction d).mapCocone (colimit.cocone F))
    (isColimit_latching_evaluation F d) j k
  have he := (isColimitLatchingColimitCocone F d).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (latchingDiagram (colimit F) d)) k
  change (colimit.ι F j).app k.obj.left ≫ (latchingColimitCocone F d).ι.app k =
    colimit.ι (latchingDiagram (F.obj j) d) k ≫ colimit.ι (latchingColimits F d) j at h
  erw [← Category.assoc, ← h, Category.assoc, he]
  rfl

/-- The interchange isomorphism identifies the latching map with the colimit
of the individual latching maps, including the chosen evaluation comparison. -/
lemma latchingColimitIso_hom_latchingMap :
    (latchingColimitIso F d).hom ≫ latchingMap (colimit F) d ≫
      (preservesColimitIso ((evaluation D M).obj d) F).hom = colimMap (latchingMaps F d) := by
  apply colimit.hom_ext (F := latchingColimits F d)
  intro j
  rw [ι_latchingColimitIso_hom_assoc, latchingObjMap_latchingMap_assoc]
  have hEval : (colimit.ι F j).app d ≫
      (preservesColimitIso ((evaluation D M).obj d) F).hom =
        colimit.ι (F ⋙ (evaluation D M).obj d) j :=
    ι_preservesColimitIso_hom ((evaluation D M).obj d) F j
  rw [hEval, ι_colimMap]
  rfl

/-- The interchange isomorphism is natural in maps of diagram families. -/
lemma latchingColimitIso_naturality {G : J ⥤ D ⥤ M}
    [∀ j e, HasColimit (latchingDiagram (G.obj j) e)]
    [∀ e, HasColimit (G.flip.obj e)] [HasColimit G]
    [HasColimit (latchingColimits G d)] [HasColimit (latchingDiagram (colimit G) d)]
    (θ : F ⟶ G) :
    colimMap (latchingColimitsMap F d θ) ≫ (latchingColimitIso G d).hom =
      (latchingColimitIso F d).hom ≫ latchingObjMap (colimMap θ) d := by
  apply colimit.hom_ext (F := latchingColimits F d)
  intro j
  rw [ι_colimMap_assoc, ι_latchingColimitIso_hom, ι_latchingColimitIso_hom_assoc]
  change latchingObjMap (θ.app j) d ≫ latchingObjMap (colimit.ι G j) d = _
  rw [← latchingObjMap_comp, ← latchingObjMap_comp, ι_colimMap]

variable [HomotopicalAlgebra.CategoryWithCofibrations M]
  [HomotopicalAlgebra.CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

omit [HasColimit (latchingDiagram (colimit F) d)] in
/-- The Reedy condition at the colimit follows from a cofibrant colimit of
latching objects and a cofibration on the colimits of the latching maps. -/
theorem reedy_colimit_at
    (hL : HomotopicalAlgebra.IsCofibrant (colimit (latchingColimits F d)))
    (hτ : HomotopicalAlgebra.Cofibration (colimMap (latchingMaps F d))) :
    ∃ (_ : HasColimit (latchingDiagram (colimit F) d)),
      HomotopicalAlgebra.IsCofibrant (latchingObj (colimit F) d) ∧
        HomotopicalAlgebra.Cofibration (latchingMap (colimit F) d) := by
  have hCol := hasColimit_latching_colimit F d
  let eL := latchingColimitIso F d
  let eO := preservesColimitIso ((evaluation D M).obj d) F
  have := ABCPrecofibrationCategory.cofibration_of_isIso eL.hom
  have hLC : HomotopicalAlgebra.IsCofibrant (latchingObj (colimit F) d) :=
    ABCPrecofibrationCategory.cofibrant_target eL.hom
  have := ABCPrecofibrationCategory.cofibration_of_isIso eL.inv
  have := ABCPrecofibrationCategory.cofibrant_target (colimMap (latchingMaps F d))
  have := ABCPrecofibrationCategory.cofibration_of_isIso eO.inv
  refine ⟨hCol, hLC, ?_⟩
  rw [show latchingMap (colimit F) d = eL.inv ≫ colimMap (latchingMaps F d) ≫ eO.inv by
    rw [Iso.eq_inv_comp, Iso.eq_comp_inv]
    simpa only [Category.assoc] using latchingColimitIso_hom_latchingMap F d]
  infer_instance

end ABCCofibrations

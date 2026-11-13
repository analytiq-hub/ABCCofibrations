/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyKanBoundary

/-!
# The latching cocone of a pointwise left Kan extension

The boundary-comma colimit is the latching object of the extension.
The comparison uses individual comma colimits, without assuming arbitrary
ambient colimits.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe w v u

open CategoryTheory Limits

namespace ABCCofibrations

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [IsDirect D₂]
  (u : D₁ ⥤ D₂) {M : Type u} [Category.{v} M] (X : D₁ ⥤ M)
  [u.HasPointwiseLeftKanExtension X] (d : D₂)
  [HasColimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)]

/-- The leg from a value of the left Kan extension to the boundary colimit. -/
noncomputable def kanBoundaryLeg (k : LatchingCategory d) :
    (u.leftKanExtension X).obj k.obj.left ⟶
      colimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) := by
  have : HasColimit (kanBoundaryPost u d k ⋙
      (kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) :=
    (inferInstance : HasColimit (CostructuredArrow.proj u k.obj.left ⋙ X))
  exact (u.leftKanExtensionObjIsoColimit X k.obj.left).hom ≫
    colimit.pre ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) (kanBoundaryPost u d k)

@[reassoc]
lemma unit_map_kanBoundaryLeg (k : LatchingCategory d) (j : CostructuredArrow u k.obj.left) :
    (u.leftKanExtensionUnit X).app j.left ≫ (u.leftKanExtension X).map j.hom ≫
      kanBoundaryLeg u X d k =
        colimit.ι ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)
          ((kanBoundaryPost u d k).obj j) := by
  unfold kanBoundaryLeg
  dsimp only
  rw [u.ι_leftKanExtensionObjIsoColimit_hom_assoc]
  have : HasColimit (kanBoundaryPost u d k ⋙
      (kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) :=
    (inferInstance : HasColimit (CostructuredArrow.proj u k.obj.left ⋙ X))
  exact colimit.ι_pre ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)
    (kanBoundaryPost u d k) j

/-- The candidate latching cocone, with the boundary colimit as vertex. -/
noncomputable def kanBoundaryCocone : Cocone (latchingDiagram (u.leftKanExtension X) d) where
  pt := colimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)
  ι :=
    { app := kanBoundaryLeg u X d
      naturality := fun k k' f ↦ by
        change (u.leftKanExtension X).map f.hom.left ≫ kanBoundaryLeg u X d k' =
          kanBoundaryLeg u X d k ≫ 𝟙 _
        rw [Category.comp_id]
        apply (cancel_epi (u.leftKanExtensionObjIsoColimit X k.obj.left).inv).1
        apply colimit.hom_ext
        intro j
        rw [u.ι_leftKanExtensionObjIsoColimit_inv_assoc,
          u.ι_leftKanExtensionObjIsoColimit_inv_assoc]
        change (u.leftKanExtensionUnit X).app j.left ≫
          (u.leftKanExtension X).map j.hom ≫ (u.leftKanExtension X).map f.hom.left ≫
            kanBoundaryLeg u X d k' = _
        rw [← Functor.map_comp_assoc]
        have h := unit_map_kanBoundaryLeg u X d k'
          (CostructuredArrow.mk (Y := j.left) (j.hom ≫ f.hom.left))
        change (u.leftKanExtensionUnit X).app j.left ≫
          (u.leftKanExtension X).map (j.hom ≫ f.hom.left) ≫ kanBoundaryLeg u X d k' = _ at h
        rw [h, unit_map_kanBoundaryLeg]
        congr 1
        apply ObjectProperty.FullSubcategory.ext
        change CostructuredArrow.mk ((j.hom ≫ f.hom.left) ≫ k'.obj.hom) =
          CostructuredArrow.mk (j.hom ≫ k.obj.hom)
        congr 1
        rw [Category.assoc, Over.w f.hom] }

/-- Restricting a cocone on the latching diagram along the Kan units gives a
cocone on the boundary diagram. -/
noncomputable def kanLatchingToBoundaryCocone
    (c : Cocone (latchingDiagram (u.leftKanExtension X) d)) :
    Cocone ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) where
  pt := c.pt
  ι :=
    { app := fun j ↦ (u.leftKanExtensionUnit X).app j.obj.left ≫
        c.ι.app ((kanBoundaryToLatching u d).obj j)
      naturality := fun a b f ↦ by
        change X.map f.hom.left ≫ ((u.leftKanExtensionUnit X).app b.obj.left ≫ _) = _ ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, (u.leftKanExtensionUnit X).naturality,
          Category.assoc]
        exact congrArg ((u.leftKanExtensionUnit X).app a.obj.left ≫ ·)
          (c.w ((kanBoundaryToLatching u d).map f)) }

/-- The boundary colimit is a colimit of the latching diagram of the extension. -/
noncomputable def isColimitKanBoundaryCocone : IsColimit (kanBoundaryCocone u X d) where
  desc c := colimit.desc _ (kanLatchingToBoundaryCocone u X d c)
  fac c k := by
    apply (cancel_epi (u.leftKanExtensionObjIsoColimit X k.obj.left).inv).1
    apply colimit.hom_ext
    intro j
    rw [u.ι_leftKanExtensionObjIsoColimit_inv_assoc,
      u.ι_leftKanExtensionObjIsoColimit_inv_assoc]
    change (u.leftKanExtensionUnit X).app j.left ≫ (u.leftKanExtension X).map j.hom ≫
      kanBoundaryLeg u X d k ≫ colimit.desc _ (kanLatchingToBoundaryCocone u X d c) = _
    rw [unit_map_kanBoundaryLeg_assoc, colimit.ι_desc]
    let α : (kanBoundaryToLatching u d).obj ((kanBoundaryPost u d k).obj j) ⟶ k :=
      ⟨Over.homMk j.hom (by rfl)⟩
    exact congrArg ((u.leftKanExtensionUnit X).app j.left ≫ ·) (c.w α).symm
  uniq c m hm := by
    apply colimit.hom_ext (F := (kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)
    intro j
    let k := (kanBoundaryToLatching u d).obj j
    have hleg := unit_map_kanBoundaryLeg u X d k
      (CostructuredArrow.mk (𝟙 (u.obj j.obj.left)))
    change (u.leftKanExtensionUnit X).app j.obj.left ≫ (u.leftKanExtension X).map (𝟙 _) ≫
      kanBoundaryLeg u X d k = _ at hleg
    rw [(u.leftKanExtension X).map_id] at hleg
    change (u.leftKanExtensionUnit X).app j.obj.left ≫
      𝟙 ((u.leftKanExtension X).obj k.obj.left) ≫ kanBoundaryLeg u X d k = _ at hleg
    erw [Category.id_comp] at hleg
    let t : (kanBoundaryPost u d k).obj (CostructuredArrow.mk (𝟙 (u.obj j.obj.left))) ⟶ j := by
      refine ⟨CostructuredArrow.homMk (𝟙 j.obj.left) ?_⟩
      change u.map (𝟙 _) ≫ j.obj.hom = (𝟙 _) ≫ j.obj.hom
      rw [u.map_id]
    have ht := colimit.w ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) t
    change X.map (𝟙 j.obj.left) ≫
      colimit.ι ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) j = _ at ht
    rw [X.map_id, Category.id_comp] at ht
    have hleg' := hleg.trans ht.symm
    rw [colimit.ι_desc, ← hleg', Category.assoc]
    exact congrArg ((u.leftKanExtensionUnit X).app j.obj.left ≫ ·) (hm k)

/-- The latching map is the boundary-to-comma colimit map under the comparison. -/
theorem kanBoundaryCocone_desc_latchingCocone :
    (isColimitKanBoundaryCocone u X d).desc (latchingCocone (u.leftKanExtension X) d) =
      colimit.pre (CostructuredArrow.proj u d ⋙ X) (kanBoundary u d).ι ≫
        (u.leftKanExtensionObjIsoColimit X d).inv := by
  apply (isColimitKanBoundaryCocone u X d).hom_ext
  intro k
  rw [IsColimit.fac]
  change (u.leftKanExtension X).map k.obj.hom = kanBoundaryLeg u X d k ≫ _
  apply (cancel_epi (u.leftKanExtensionObjIsoColimit X k.obj.left).inv).1
  apply colimit.hom_ext
  intro j
  rw [u.ι_leftKanExtensionObjIsoColimit_inv_assoc,
    u.ι_leftKanExtensionObjIsoColimit_inv_assoc, unit_map_kanBoundaryLeg_assoc,
    colimit.ι_pre_assoc, u.ι_leftKanExtensionObjIsoColimit_inv]
  change (u.leftKanExtensionUnit X).app j.left ≫
    (u.leftKanExtension X).map j.hom ≫ (u.leftKanExtension X).map k.obj.hom =
      (u.leftKanExtensionUnit X).app j.left ≫ (u.leftKanExtension X).map (j.hom ≫ k.obj.hom)
  rw [(u.leftKanExtension X).map_comp]

/-- The canonical boundary-colimit description of the chosen latching object. -/
noncomputable def kanLatchingIso [HasColimit (latchingDiagram (u.leftKanExtension X) d)] :
    colimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X) ≅
      latchingObj (u.leftKanExtension X) d :=
  (isColimitKanBoundaryCocone u X d).coconePointUniqueUpToIso (colimit.isColimit _)

@[reassoc]
lemma kanBoundaryLeg_kanLatchingIso_hom
    [HasColimit (latchingDiagram (u.leftKanExtension X) d)] (k : LatchingCategory d) :
    kanBoundaryLeg u X d k ≫ (kanLatchingIso u X d).hom =
      colimit.ι (latchingDiagram (u.leftKanExtension X) d) k :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitKanBoundaryCocone u X d)
    (colimit.isColimit (latchingDiagram (u.leftKanExtension X) d)) k

lemma kanLatchingIso_hom_latchingMap [HasColimit (latchingDiagram (u.leftKanExtension X) d)] :
    (kanLatchingIso u X d).hom ≫ latchingMap (u.leftKanExtension X) d =
      colimit.pre (CostructuredArrow.proj u d ⋙ X) (kanBoundary u d).ι ≫
        (u.leftKanExtensionObjIsoColimit X d).inv := by
  rw [← kanBoundaryCocone_desc_latchingCocone]
  exact IsColimit.coconePointUniqueUpToIso_hom_desc _ _

section Maps

variable {X} {Y : D₁ ⥤ M} [u.HasPointwiseLeftKanExtension Y]
  [HasColimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ Y)] (f : X ⟶ Y)

/-- Naturality of the boundary cocone with respect to a map of source diagrams. -/
lemma kanBoundaryLeg_naturality (k : LatchingCategory d) :
    kanBoundaryLeg u X d k ≫
      colimMap (Functor.whiskerLeft (kanBoundary u d).ι
        (Functor.whiskerLeft (CostructuredArrow.proj u d) f)) =
      (pointwiseLeftKanMap u f).app k.obj.left ≫ kanBoundaryLeg u Y d k := by
  apply (cancel_epi (u.leftKanExtensionObjIsoColimit X k.obj.left).inv).1
  apply colimit.hom_ext
  intro j
  rw [u.ι_leftKanExtensionObjIsoColimit_inv_assoc,
    u.ι_leftKanExtensionObjIsoColimit_inv_assoc, unit_map_kanBoundaryLeg_assoc,
    ι_colimMap]
  have hn := (pointwiseLeftKanMap u f).naturality j.hom
  change (u.leftKanExtension X).map j.hom ≫ (pointwiseLeftKanMap u f).app k.obj.left =
    (pointwiseLeftKanMap u f).app (u.obj j.left) ≫ (u.leftKanExtension Y).map j.hom at hn
  change f.app j.left ≫ colimit.ι
    ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ Y) ((kanBoundaryPost u d k).obj j) =
      (u.leftKanExtensionUnit X).app j.left ≫ (u.leftKanExtension X).map j.hom ≫
        (pointwiseLeftKanMap u f).app k.obj.left ≫ kanBoundaryLeg u Y d k
  rw [reassoc_of% hn, ← Category.assoc, pointwiseLeftKanMap_unit, Category.assoc]
  rw [unit_map_kanBoundaryLeg]

/-- The chosen latching-object comparison commutes with induced Kan-extension maps. -/
lemma kanLatchingIso_naturality
    [HasColimit (latchingDiagram (u.leftKanExtension X) d)]
    [HasColimit (latchingDiagram (u.leftKanExtension Y) d)] :
    (kanLatchingIso u X d).hom ≫ latchingObjMap (pointwiseLeftKanMap u f) d =
      colimMap (Functor.whiskerLeft (kanBoundary u d).ι
        (Functor.whiskerLeft (CostructuredArrow.proj u d) f)) ≫
        (kanLatchingIso u Y d).hom := by
  apply (isColimitKanBoundaryCocone u X d).hom_ext
  intro k
  change kanBoundaryLeg u X d k ≫ (kanLatchingIso u X d).hom ≫
    latchingObjMap (pointwiseLeftKanMap u f) d =
      kanBoundaryLeg u X d k ≫
        colimMap (Functor.whiskerLeft (kanBoundary u d).ι
          (Functor.whiskerLeft (CostructuredArrow.proj u d) f)) ≫ (kanLatchingIso u Y d).hom
  rw [← Category.assoc, kanBoundaryLeg_kanLatchingIso_hom, ι_latchingObjMap]
  rw [← Category.assoc, kanBoundaryLeg_naturality, Category.assoc,
    kanBoundaryLeg_kanLatchingIso_hom]
  rfl

end Maps

end ABCCofibrations

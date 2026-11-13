/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayer

/-!
# Extending a diagram over a whole maximal layer

A diagram on the old full subcategory and a cocone at each new maximal
object determine a diagram on the whole category. This is the categorical
extension operation needed for degree-wise Reedy factorizations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits
namespace ABCCofibrations.ReedyLayer

variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)
  (hmax : ∀ d, ¬ P d → ∀ e (f : d ⟶ e), ∃ h : d = e, f = eqToHom h)
  {M : Type u} [Category.{v} M] (F : P.FullSubcategory ⥤ M)
  (c : ∀ d : Objects P, Cocone (latchingToOld P hmax d ⋙ F))

open Classical in
/-- The extended objects. -/
noncomputable def extensionObj (d : D) : M :=
  if h : P d then F.obj ⟨d, h⟩ else (c ⟨d, h⟩).pt

/-- Comparison with the old value. -/
noncomputable def extensionObjIsoOld {d : D} (h : P d) :
    extensionObj P hmax F c d ≅ F.obj ⟨d, h⟩ :=
  eqToIso (by simp [extensionObj, h])

/-- Comparison with the prescribed new value. -/
noncomputable def extensionObjIsoNew (d : Objects P) :
    extensionObj P hmax F c d.val ≅ (c d).pt :=
  eqToIso (by simp [extensionObj, d.property])

open Classical in
/-- The maps of the extension. Arrows from new objects are identities. -/
noncomputable def extensionMap {a b : D} (f : a ⟶ b) :
    extensionObj P hmax F c a ⟶ extensionObj P hmax F c b :=
  if ha : P a then
    if hb : P b then
      (extensionObjIsoOld P hmax F c ha).hom ≫ F.map ⟨f⟩ ≫
        (extensionObjIsoOld P hmax F c hb).inv
    else
      (extensionObjIsoOld P hmax F c ha).hom ≫
        (c ⟨b, hb⟩).ι.app ⟨Over.mk f, fun h ↦ hb (Eq.mp (congrArg P h) ha)⟩ ≫
          (extensionObjIsoNew P hmax F c ⟨b, hb⟩).inv
  else eqToHom (congrArg (extensionObj P hmax F c) (hmax a ha b f).choose)

lemma extensionMap_old_old {a b : D} (ha : P a) (hb : P b) (f : a ⟶ b) :
    extensionMap P hmax F c f = (extensionObjIsoOld P hmax F c ha).hom ≫ F.map ⟨f⟩ ≫
      (extensionObjIsoOld P hmax F c hb).inv := by
  simp only [extensionMap, dite_eq_left ha, dite_eq_left hb]

lemma extensionMap_old_new {a : D} (ha : P a) (d : Objects P) (f : a ⟶ d.val) :
    extensionMap P hmax F c f = (extensionObjIsoOld P hmax F c ha).hom ≫
      (c d).ι.app ⟨Over.mk f, fun h ↦ d.property (Eq.mp (congrArg P h) ha)⟩ ≫
        (extensionObjIsoNew P hmax F c d).inv := by
  simp only [extensionMap, dite_eq_left ha, dite_eq_right d.property]

lemma extensionMap_id (d : D) : extensionMap P hmax F c (𝟙 d) = 𝟙 _ := by
  classical
  by_cases hd : P d
  · rw [extensionMap_old_old P hmax F c hd hd]
    change (extensionObjIsoOld P hmax F c hd).hom ≫ F.map (𝟙 _) ≫ _ = _
    simp
  · simp [extensionMap, hd]

lemma extensionMap_comp {a b d : D} (f : a ⟶ b) (g : b ⟶ d) :
    extensionMap P hmax F c (f ≫ g) = extensionMap P hmax F c f ≫
      extensionMap P hmax F c g := by
  classical
  by_cases ha : P a
  · by_cases hb : P b
    · by_cases hd : P d
      · rw [extensionMap_old_old P hmax F c ha hd,
          extensionMap_old_old P hmax F c ha hb, extensionMap_old_old P hmax F c hb hd]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← F.map_comp_assoc]
        rfl
      · rw [extensionMap_old_new P hmax F c ha ⟨d, hd⟩,
          extensionMap_old_old P hmax F c ha hb, extensionMap_old_new P hmax F c hb ⟨d, hd⟩]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        have hw := (c ⟨d, hd⟩).w
          (⟨Over.homMk f rfl⟩ :
            (⟨Over.mk (f ≫ g), fun h ↦ hd (Eq.mp (congrArg P h) ha)⟩ : LatchingCategory d) ⟶
              ⟨Over.mk g, fun h ↦ hd (Eq.mp (congrArg P h) hb)⟩)
        change F.map (⟨f⟩ : (⟨a, ha⟩ : P.FullSubcategory) ⟶ ⟨b, hb⟩) ≫ _ = _ at hw
        simpa only [Category.assoc] using congrArg
          (fun k : F.obj ⟨a, ha⟩ ⟶ (c ⟨d, hd⟩).pt ↦
            (extensionObjIsoOld P hmax F c ha).hom ≫ k ≫
              (extensionObjIsoNew P hmax F c ⟨d, hd⟩).inv) hw.symm
    · obtain ⟨h, hg⟩ := hmax b hb d g
      subst d
      have hg' : g = 𝟙 b := by simpa using hg
      rw [hg', Category.comp_id, extensionMap_id, Category.comp_id]
  · obtain ⟨h, hf⟩ := hmax a ha b f
    subst b
    have hf' : f = 𝟙 a := by simpa using hf
    rw [hf', Category.id_comp, extensionMap_id, Category.id_comp]

/-- Extend the old diagram by the chosen cocones at every new object. -/
noncomputable def extension : D ⥤ M where
  obj := extensionObj P hmax F c
  map := extensionMap P hmax F c
  map_id := extensionMap_id P hmax F c
  map_comp := extensionMap_comp P hmax F c

/-- Restriction of the extension recovers the old diagram canonically. -/
noncomputable def extensionRestrictIso : P.ι ⋙ extension P hmax F c ≅ F :=
  NatIso.ofComponents (fun d ↦ extensionObjIsoOld P hmax F c d.property) (fun {a b} f ↦ by
    change extensionMap P hmax F c f.hom ≫ _ = _
    rw [extensionMap_old_old P hmax F c a.property b.property]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

/-- At a new object, the latching diagram is the old diagram on its predecessors. -/
noncomputable def extensionLatchingIso (d : Objects P) :
    latchingDiagram (extension P hmax F c) d.val ≅ latchingToOld P hmax d ⋙ F :=
  NatIso.ofComponents
    (fun j ↦ extensionObjIsoOld P hmax F c (predecessor_mem P hmax d j))
    (fun {a b} f ↦ by
      change extensionMap P hmax F c f.hom.left ≫ _ = _
      rw [extensionMap_old_old P hmax F c (predecessor_mem P hmax d a)
        (predecessor_mem P hmax d b)]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)

/-- The chosen new cocone supplies the latching colimit for the extension. -/
lemma hasColimit_extension_latching_new (d : Objects P)
    [HasColimit (latchingToOld P hmax d ⋙ F)] :
    HasColimit (latchingDiagram (extension P hmax F c) d.val) :=
  hasColimit_of_iso (extensionLatchingIso P hmax F c d)

/-- The latching map at a new object is the chosen cocone map, under the
canonical comparisons of its source and target. -/
lemma extensionLatchingIso_hom_desc (d : Objects P)
    [HasColimit (latchingToOld P hmax d ⋙ F)]
    [HasColimit (latchingDiagram (extension P hmax F c) d.val)] :
    (HasColimit.isoOfNatIso (extensionLatchingIso P hmax F c d)).hom ≫
        colimit.desc _ (c d) =
      latchingMap (extension P hmax F c) d.val ≫ (extensionObjIsoNew P hmax F c d).hom := by
  apply colimit.hom_ext
  intro j
  rw [HasColimit.ι_isoOfNatIso_hom_assoc, colimit.ι_desc, ι_latchingMap_assoc]
  change (extensionObjIsoOld P hmax F c (predecessor_mem P hmax d j)).hom ≫
    (c d).ι.app j = extensionMap P hmax F c j.obj.hom ≫ _
  rw [extensionMap_old_new P hmax F c (predecessor_mem P hmax d j) d]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 2


/-- Formula for the new latching map under the source and vertex comparisons. -/
lemma latchingMap_extension (d : Objects P)
    [HasColimit (latchingToOld P hmax d ⋙ F)]
    [HasColimit (latchingDiagram (extension P hmax F c) d.val)] :
    latchingMap (extension P hmax F c) d.val =
      (HasColimit.isoOfNatIso (extensionLatchingIso P hmax F c d)).hom ≫
        colimit.desc _ (c d) ≫ (extensionObjIsoNew P hmax F c d).inv := by
  apply (cancel_mono (extensionObjIsoNew P hmax F c d).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (extensionLatchingIso_hom_desc P hmax F c d).symm


section Maps
variable {F} {c} {G : P.FullSubcategory ⥤ M}
  {c' : ∀ d : Objects P, Cocone (latchingToOld P hmax d ⋙ G)}
  (a : F ⟶ G) (z : ∀ d : Objects P, (c d).pt ⟶ (c' d).pt)
  (hz : ∀ (d : Objects P) (j : LatchingCategory d.val),
    (c d).ι.app j ≫ z d = a.app ((latchingToOld P hmax d).obj j) ≫ (c' d).ι.app j)

open Classical in
/-- Components of the map between two layer extensions. -/
noncomputable def extensionHomApp (d : D) :
    (extension P hmax F c).obj d ⟶ (extension P hmax G c').obj d :=
  if h : P d then
    (extensionObjIsoOld P hmax F c h).hom ≫ a.app ⟨d, h⟩ ≫
      (extensionObjIsoOld P hmax G c' h).inv
  else (extensionObjIsoNew P hmax F c ⟨d, h⟩).hom ≫ z ⟨d, h⟩ ≫
    (extensionObjIsoNew P hmax G c' ⟨d, h⟩).inv

lemma extensionHomApp_old {d : D} (h : P d) :
    extensionHomApp P hmax a z d = (extensionObjIsoOld P hmax F c h).hom ≫
      a.app ⟨d, h⟩ ≫ (extensionObjIsoOld P hmax G c' h).inv := by
  simp only [extensionHomApp, dite_eq_left h]

lemma extensionHomApp_new (d : Objects P) :
    extensionHomApp P hmax a z d.val = (extensionObjIsoNew P hmax F c d).hom ≫
      z d ≫ (extensionObjIsoNew P hmax G c' d).inv := by
  simp only [extensionHomApp, dite_eq_right d.property]

include hz in
/-- Naturality of a compatible family of old and new maps. -/
lemma extensionHomApp_naturality {b d : D} (f : b ⟶ d) :
    (extension P hmax F c).map f ≫ extensionHomApp P hmax a z d =
      extensionHomApp P hmax a z b ≫ (extension P hmax G c').map f := by
  classical
  change extensionMap P hmax F c f ≫ _ = _ ≫ extensionMap P hmax G c' f
  by_cases hb : P b
  · by_cases hd : P d
    · rw [extensionMap_old_old P hmax F c hb hd, extensionMap_old_old P hmax G c' hb hd,
        extensionHomApp_old P hmax a z hb, extensionHomApp_old P hmax a z hd]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← a.naturality_assoc]
    · rw [extensionMap_old_new P hmax F c hb ⟨d, hd⟩,
        extensionMap_old_new P hmax G c' hb ⟨d, hd⟩,
        extensionHomApp_old P hmax a z hb, extensionHomApp_new P hmax a z ⟨d, hd⟩]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% hz ⟨d, hd⟩ ⟨Over.mk f, fun h ↦ hd (Eq.mp (congrArg P h) hb)⟩]
      rfl
  · obtain ⟨h, hf⟩ := hmax b hb d f
    subst d
    have hf' : f = 𝟙 b := by simpa using hf
    rw [hf', extensionMap_id, extensionMap_id, Category.id_comp, Category.comp_id]

/-- A compatible family of maps determines a natural transformation of extensions. -/
noncomputable def extensionHom : extension P hmax F c ⟶ extension P hmax G c' where
  app := extensionHomApp P hmax a z
  naturality _ _ f := extensionHomApp_naturality P hmax a z hz f

end Maps

/-- The cocone at a new object supplied by an existing whole diagram. -/
noncomputable def restrictionCocone (X : D ⥤ M) (d : Objects P) :
    Cocone (latchingToOld P hmax d ⋙ P.ι ⋙ X) where
  pt := X.obj d.val
  ι :=
    { app := fun j ↦ X.map j.obj.hom
      naturality := fun j k f ↦ by
        change X.map f.hom.left ≫ X.map k.obj.hom = X.map j.obj.hom ≫ 𝟙 _
        rw [← X.map_comp, Over.w, Category.comp_id] }

/-- Extending the restriction of an existing diagram recovers that diagram. -/
noncomputable def extensionIso (X : D ⥤ M) :
    extension P hmax (P.ι ⋙ X) (restrictionCocone P hmax X) ≅ X := by
  classical
  let e (d : D) : extensionObj P hmax (P.ι ⋙ X) (restrictionCocone P hmax X) d ≅ X.obj d :=
    if h : P d then extensionObjIsoOld P hmax _ _ h
    else extensionObjIsoNew P hmax _ _ ⟨d, h⟩
  refine NatIso.ofComponents e (fun {b d} f ↦ ?_)
  change extensionMap P hmax _ _ f ≫ (e d).hom = (e b).hom ≫ X.map f
  by_cases hb : P b
  · by_cases hd : P d
    · rw [extensionMap_old_old P hmax _ _ hb hd]
      simp only [e, dite_eq_left hb, dite_eq_left hd, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      rfl
    · rw [extensionMap_old_new P hmax _ _ hb ⟨d, hd⟩]
      simp only [e, dite_eq_left hb, dite_eq_right hd, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      rfl
  · obtain ⟨h, hf⟩ := hmax b hb d f
    subst d
    have hf' : f = 𝟙 b := by simpa using hf
    rw [hf', extensionMap_id, X.map_id, Category.id_comp, Category.comp_id]

section LiftDesc
variable {F c} (X : D ⥤ M) (a : P.ι ⋙ X ⟶ F)
  (i : ∀ d : Objects P, X.obj d.val ⟶ (c d).pt)
  (hi : ∀ (d : Objects P) (j : LatchingCategory d.val),
    X.map j.obj.hom ≫ i d = a.app ((latchingToOld P hmax d).obj j) ≫ (c d).ι.app j)

/-- Lift a map to the old diagram across compatible maps at the new objects. -/
noncomputable def extensionLift : X ⟶ extension P hmax F c :=
  (extensionIso P hmax X).inv ≫ extensionHom P hmax a i hi

lemma extensionLift_app_old {d : D} (hd : P d) :
    (extensionLift P hmax X a i hi).app d =
      a.app ⟨d, hd⟩ ≫ (extensionObjIsoOld P hmax F c hd).inv := by
  simp [extensionLift, extensionHom, extensionHomApp, extensionIso, hd]

lemma extensionLift_app_new (d : Objects P) :
    (extensionLift P hmax X a i hi).app d.val =
      i d ≫ (extensionObjIsoNew P hmax F c d).inv := by
  simp [extensionLift, extensionHom, extensionHomApp, extensionIso, d.property]

end LiftDesc

section Desc
variable {F c} (Y : D ⥤ M) (r : F ⟶ P.ι ⋙ Y)
  (p : ∀ d : Objects P, (c d).pt ⟶ Y.obj d.val)
  (hp : ∀ (d : Objects P) (j : LatchingCategory d.val),
    (c d).ι.app j ≫ p d = r.app ((latchingToOld P hmax d).obj j) ≫ Y.map j.obj.hom)

/-- Descend compatible old and new maps to a map out of the extension. -/
noncomputable def extensionDesc : extension P hmax F c ⟶ Y :=
  extensionHom P hmax r p hp ≫ (extensionIso P hmax Y).hom

lemma extensionDesc_app_old {d : D} (hd : P d) :
    (extensionDesc P hmax Y r p hp).app d =
      (extensionObjIsoOld P hmax F c hd).hom ≫ r.app ⟨d, hd⟩ := by
  simp [extensionDesc, extensionHom, extensionHomApp, extensionIso, hd]

lemma extensionDesc_app_new (d : Objects P) :
    (extensionDesc P hmax Y r p hp).app d.val =
      (extensionObjIsoNew P hmax F c d).hom ≫ p d := by
  simp [extensionDesc, extensionHom, extensionHomApp, extensionIso, d.property]

end Desc

end ABCCofibrations.ReedyLayer

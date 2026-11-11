/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyStructure

/-!
# Extending a diagram over a maximal object

Let `d` be an object of `D` with no non-identity maps out of it. A diagram on
`D ∖ {d}`, an object `Z`, and a cocone from the latching diagram at `d` to `Z`
determine a diagram on `D`. This is used to construct Reedy factorizations
degree by degree.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] {M : Type u₂} [Category.{v₂} M] {d : D}
  (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
  (F : Complement d ⥤ M) (c : Cocone (latchingToComplement d ⋙ F))

open Classical in
/-- The objects of the extended diagram. -/
noncomputable def extendObj (e : D) : M := if h : e = d then c.pt else F.obj ⟨e, h⟩

lemma extendObj_self : extendObj F c d = c.pt := by simp [extendObj]

lemma extendObj_ne {e : D} (h : e ≠ d) : extendObj F c e = F.obj ⟨e, h⟩ := by
  simp [extendObj, h]

open Classical in
include hd in
/-- The maps of the extended diagram. -/
noncomputable def extendMap {e e' : D} (g : e ⟶ e') : extendObj F c e ⟶ extendObj F c e' :=
  if he' : e' = d then
    if he : e = d then eqToHom (by rw [he, he'])
    else eqToHom (extendObj_ne F c he) ≫
      c.ι.app ⟨Over.mk (g ≫ eqToHom he'), he⟩ ≫
        eqToHom ((extendObj_self F c).symm.trans (congrArg (extendObj F c) he'.symm))
  else
    if he : e = d then
      (he' ((hd e' (eqToHom he.symm ≫ g)).choose.symm.trans rfl)).elim
    else eqToHom (extendObj_ne F c he) ≫ F.map ⟨g⟩ ≫ eqToHom (extendObj_ne F c he').symm

lemma extendMap_ne_ne {e e' : D} (he : e ≠ d) (he' : e' ≠ d) (g : e ⟶ e') :
    extendMap hd F c g = eqToHom (extendObj_ne F c he) ≫ F.map ⟨g⟩ ≫
      eqToHom (extendObj_ne F c he').symm := by
  simp [extendMap, he, he']

lemma extendMap_ne_self {e : D} (he : e ≠ d) (g : e ⟶ d) :
    extendMap hd F c g = eqToHom (extendObj_ne F c he) ≫ c.ι.app ⟨Over.mk g, he⟩ ≫
      eqToHom (extendObj_self F c).symm := by
  simp only [extendMap, dite_true, he, dite_false]
  rw [eqToHom_refl, Category.comp_id]

lemma extendMap_self_self (g : d ⟶ d) : extendMap hd F c g = 𝟙 _ := by
  simp [extendMap]

lemma extendMap_id (e : D) : extendMap hd F c (𝟙 e) = 𝟙 _ := by
  by_cases he : e = d
  · subst e
    exact extendMap_self_self hd F c _
  · rw [extendMap_ne_ne hd F c he he]
    rw [show (⟨𝟙 e⟩ : (⟨e, he⟩ : Complement d) ⟶ ⟨e, he⟩) = 𝟙 (⟨e, he⟩ : Complement d) from rfl,
      F.map_id]
    simp

lemma extendMap_comp {e e' e'' : D} (g : e ⟶ e') (g' : e' ⟶ e'') :
    extendMap hd F c (g ≫ g') = extendMap hd F c g ≫ extendMap hd F c g' := by
  by_cases he'' : e'' = d
  · subst e''
    by_cases he' : e' = d
    · subst e'
      rw [extendMap_self_self hd F c g', Category.comp_id]
      obtain ⟨_, rfl⟩ := hd _ g'
      simp
    · by_cases he : e = d
      · subst e
        exact absurd (hd _ g).choose.symm he'
      · rw [extendMap_ne_self hd F c he, extendMap_ne_ne hd F c he he', extendMap_ne_self hd F c he']
        have := c.w (⟨Over.homMk g rfl⟩ : (⟨Over.mk (g ≫ g'), he⟩ : LatchingCategory d) ⟶
          ⟨Over.mk g', he'⟩)
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← this]
        exact congrArg (eqToHom _ ≫ ·) (Category.assoc _ _ _)
  · by_cases he' : e' = d
    · subst e'
      exact absurd (hd _ g').choose.symm he''
    · by_cases he : e = d
      · subst e
        exact absurd (hd _ g).choose.symm he'
      · rw [extendMap_ne_ne hd F c he he'', extendMap_ne_ne hd F c he he',
          extendMap_ne_ne hd F c he' he'']
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← F.map_comp_assoc]
        rfl

/-- The extension of `F` to `D` with value `c.pt` at `d`. -/
noncomputable def extend : D ⥤ M where
  obj := extendObj F c
  map := extendMap hd F c
  map_id := extendMap_id hd F c
  map_comp := extendMap_comp hd F c

/-- The value of the extension at `e ≠ d`. -/
noncomputable def extendObjIso {e : D} (h : e ≠ d) : extendObj F c e ≅ F.obj ⟨e, h⟩ :=
  eqToIso (extendObj_ne F c h)

/-- The value of the extension at `d`. -/
noncomputable def extendObjIsoSelf : extendObj F c d ≅ c.pt :=
  eqToIso (extendObj_self F c)

lemma extendObjIso_naturality {e e' : D} (he : e ≠ d) (he' : e' ≠ d) (g : e ⟶ e') :
    extendMap hd F c g ≫ (extendObjIso F c he').hom =
      (extendObjIso F c he).hom ≫ F.map ⟨g⟩ := by
  rw [extendMap_ne_ne hd F c he he']
  simp [extendObjIso]

lemma extend_map_self {e : D} (he : e ≠ d) (g : e ⟶ d) :
    extendMap hd F c g ≫ (extendObjIsoSelf F c).hom =
      (extendObjIso F c he).hom ≫ c.ι.app ⟨Over.mk g, he⟩ := by
  rw [extendMap_ne_self hd F c he]
  simp only [extendObjIso, extendObjIsoSelf, eqToIso.hom, Category.assoc]
  congr 1
  exact (Category.assoc _ _ _).trans ((congrArg (c.ι.app _ ≫ ·)
    ((eqToHom_trans _ _).trans (eqToHom_refl c.pt _))).trans (Category.comp_id _))

/-- The extension restricts to `F` on `D ∖ {d}`. -/
noncomputable def extendRestrictIso : (complementProp d).ι ⋙ extend hd F c ≅ F :=
  NatIso.ofComponents (fun e ↦ extendObjIso F c e.property)
    (fun {e e'} g ↦ extendObjIso_naturality hd F c e.property e'.property g.hom)

/-- The latching diagram of the extension at `d` is `F` on the latching category. -/
noncomputable def extendLatchingIso :
    latchingDiagram (extend hd F c) d ≅ latchingToComplement d ⋙ F :=
  NatIso.ofComponents (fun j ↦ extendObjIso F c j.property)
    (fun {j j'} g ↦ extendObjIso_naturality hd F c j.property j'.property g.hom.left)

section Maps

variable (G : D ⥤ M)

open Classical in
/-- The components of a map out of the extension. -/
noncomputable def extendDescApp (α : F ⟶ (complementProp d).ι ⋙ G) (z : c.pt ⟶ G.obj d)
    (e : D) : extendObj F c e ⟶ G.obj e :=
  if he : e = d then eqToHom (congrArg (extendObj F c) he) ≫ (extendObjIsoSelf F c).hom ≫ z ≫
    eqToHom (congrArg G.obj he.symm)
  else (extendObjIso F c he).hom ≫ α.app ⟨e, he⟩

variable {G}

lemma extendDescApp_self (α : F ⟶ (complementProp d).ι ⋙ G) (z : c.pt ⟶ G.obj d) :
    extendDescApp F c G α z d = (extendObjIsoSelf F c).hom ≫ z := by
  simp [extendDescApp]

lemma extendDescApp_ne (α : F ⟶ (complementProp d).ι ⋙ G) (z : c.pt ⟶ G.obj d) {e : D}
    (he : e ≠ d) : extendDescApp F c G α z e = (extendObjIso F c he).hom ≫ α.app ⟨e, he⟩ := by
  simp [extendDescApp, he]

include hd in
/-- A map out of the extension, from a map on `D ∖ {d}` and a compatible map at
`d`. -/
noncomputable def extendDesc (α : F ⟶ (complementProp d).ι ⋙ G) (z : c.pt ⟶ G.obj d)
    (h : ∀ j : LatchingCategory d,
      c.ι.app j ≫ z = α.app ((latchingToComplement d).obj j) ≫ G.map j.obj.hom) :
    extend hd F c ⟶ G where
  app := extendDescApp F c G α z
  naturality {e e'} g := by
    change extendMap hd F c g ≫ _ = _
    by_cases he' : e' = d
    · subst e'
      by_cases he : e = d
      · subst e
        obtain ⟨_, rfl⟩ := hd _ g
        rw [extendMap_self_self, Category.id_comp, eqToHom_map, eqToHom_refl]
        exact (Category.comp_id (extendDescApp F c G α z d)).symm
      · rw [extendDescApp_self, ← Category.assoc, extend_map_self hd F c he,
          extendDescApp_ne _ _ _ _ he]
        exact (Category.assoc _ _ _).trans ((congrArg ((extendObjIso F c he).hom ≫ ·)
          (h ⟨Over.mk g, he⟩)).trans (Category.assoc _ _ _).symm)
    · by_cases he : e = d
      · subst e
        exact absurd (hd _ g).choose.symm he'
      · rw [extendDescApp_ne _ _ _ _ he', ← Category.assoc, extendObjIso_naturality hd F c he he',
          extendDescApp_ne _ _ _ _ he]
        exact (Category.assoc _ _ _).trans ((congrArg ((extendObjIso F c he).hom ≫ ·)
          (α.naturality (⟨g⟩ : (⟨e, he⟩ : Complement d) ⟶ ⟨e', he'⟩))).trans
            (Category.assoc _ _ _).symm)

lemma extendDesc_app_self (α : F ⟶ (complementProp d).ι ⋙ G) (z : c.pt ⟶ G.obj d) (h) :
    (extendDesc hd F c α z h).app d = (extendObjIsoSelf F c).hom ≫ z :=
  extendDescApp_self F c α z

lemma extendDesc_app_ne (α : F ⟶ (complementProp d).ι ⋙ G) (z : c.pt ⟶ G.obj d) (h) {e : D}
    (he : e ≠ d) :
    (extendDesc hd F c α z h).app e = (extendObjIso F c he).hom ≫ α.app ⟨e, he⟩ :=
  extendDescApp_ne F c α z he

variable (G)

open Classical in
/-- The components of a map into the extension. -/
noncomputable def extendLiftApp (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt)
    (e : D) : G.obj e ⟶ extendObj F c e :=
  if he : e = d then eqToHom (congrArg G.obj he) ≫ z ≫ (extendObjIsoSelf F c).inv ≫
    eqToHom (congrArg (extendObj F c) he.symm)
  else α.app ⟨e, he⟩ ≫ (extendObjIso F c he).inv

variable {G}

lemma extendLiftApp_self (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt) :
    extendLiftApp F c G α z d = z ≫ (extendObjIsoSelf F c).inv := by
  simp [extendLiftApp]

lemma extendLiftApp_ne (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt) {e : D}
    (he : e ≠ d) : extendLiftApp F c G α z e = α.app ⟨e, he⟩ ≫ (extendObjIso F c he).inv := by
  simp [extendLiftApp, he]

include hd in
lemma extendLiftApp_naturality (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt)
    (h : ∀ j : LatchingCategory d,
      G.map j.obj.hom ≫ z = α.app ((latchingToComplement d).obj j) ≫ c.ι.app j)
    {e e' : D} (g : e ⟶ e') :
    G.map g ≫ extendLiftApp F c G α z e' = extendLiftApp F c G α z e ≫ extendMap hd F c g := by
  by_cases he' : e' = d
  · subst e'
    by_cases he : e = d
    · subst e
      obtain ⟨_, rfl⟩ := hd _ g
      rw [extendMap_self_self, Category.comp_id, eqToHom_map, eqToHom_refl, Category.id_comp]
    · have h₃ : extendMap hd F c g =
          ((extendObjIso F c he).hom ≫ c.ι.app ⟨Over.mk g, he⟩) ≫ (extendObjIsoSelf F c).inv :=
        (Iso.eq_comp_inv _).2 (extend_map_self hd F c he g)
      rw [extendLiftApp_self, extendLiftApp_ne _ _ _ _ he, h₃, ← Category.assoc]
      exact (congrArg (· ≫ (extendObjIsoSelf F c).inv) (h ⟨Over.mk g, he⟩)).trans
        (by
          have hc : c.ι.app ⟨Over.mk g, he⟩ ≫ (extendObjIsoSelf F c).inv =
              (extendObjIso F c he).inv ≫ ((extendObjIso F c he).hom ≫
                c.ι.app ⟨Over.mk g, he⟩) ≫ (extendObjIsoSelf F c).inv :=
            (Iso.inv_hom_id_assoc _ _).symm.trans
              (congrArg ((extendObjIso F c he).inv ≫ ·) (Category.assoc _ _ _).symm)
          exact (Category.assoc _ _ _).trans ((congrArg (α.app ⟨e, he⟩ ≫ ·) hc).trans
            (Category.assoc _ _ _).symm))
  · by_cases he : e = d
    · subst e
      exact absurd (hd _ g).choose.symm he'
    · have h₃ : extendMap hd F c g =
          ((extendObjIso F c he).hom ≫ F.map ⟨g⟩) ≫ (extendObjIso F c he').inv :=
        (Iso.eq_comp_inv _).2 (extendObjIso_naturality hd F c he he' g)
      rw [extendLiftApp_ne _ _ _ _ he', extendLiftApp_ne _ _ _ _ he, h₃, ← Category.assoc]
      exact (congrArg (· ≫ (extendObjIso F c he').inv)
        (α.naturality (⟨g⟩ : (⟨e, he⟩ : Complement d) ⟶ ⟨e', he'⟩))).trans
          (by simp only [Category.assoc, Iso.inv_hom_id_assoc])

include hd in
/-- A map into the extension, from a map on `D ∖ {d}` and a compatible map at `d`. -/
noncomputable def extendLift (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt)
    (h : ∀ j : LatchingCategory d,
      G.map j.obj.hom ≫ z = α.app ((latchingToComplement d).obj j) ≫ c.ι.app j) :
    G ⟶ extend hd F c where
  app := extendLiftApp F c G α z
  naturality _ _ g := extendLiftApp_naturality hd F c α z h g

lemma extendLift_app_self (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt) (h) :
    (extendLift hd F c α z h).app d = z ≫ (extendObjIsoSelf F c).inv :=
  extendLiftApp_self F c α z

lemma extendLift_app_ne (α : (complementProp d).ι ⋙ G ⟶ F) (z : G.obj d ⟶ c.pt) (h) {e : D}
    (he : e ≠ d) :
    (extendLift hd F c α z h).app e = α.app ⟨e, he⟩ ≫ (extendObjIso F c he).inv :=
  extendLiftApp_ne F c α z he

end Maps

end ABCCofibrations

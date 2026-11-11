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

end ABCCofibrations

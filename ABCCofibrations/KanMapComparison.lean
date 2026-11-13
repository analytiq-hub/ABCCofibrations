/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Maps between individually existing pointwise Kan extensions

The map is defined when the two individual extensions exist; no Kan
extension functor on the entire diagram category is assumed.
-/

@[expose] public section

open CategoryTheory Limits
namespace ABCCofibrations

variable {J K M : Type*} [Category J] [Category K] [Category M]
  (u : J ⥤ K) {X Y : J ⥤ M} [u.HasPointwiseLeftKanExtension X]
  [u.HasPointwiseLeftKanExtension Y]

/-- The canonical map between two individually existing left Kan extensions. -/
noncomputable def pointwiseLeftKanMap (f : X ⟶ Y) :
    u.leftKanExtension X ⟶ u.leftKanExtension Y :=
  (u.leftKanExtension X).descOfIsLeftKanExtension (u.leftKanExtensionUnit X)
    (u.leftKanExtension Y) (f ≫ u.leftKanExtensionUnit Y)

/-- The induced map commutes with the canonical units. -/
@[reassoc]
theorem pointwiseLeftKanMap_unit (f : X ⟶ Y) (j : J) :
    (u.leftKanExtensionUnit X).app j ≫ (pointwiseLeftKanMap u f).app (u.obj j) =
      f.app j ≫ (u.leftKanExtensionUnit Y).app j :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

/-- Evaluation of the induced map is the comma-colimit map under the
canonical pointwise comparison isomorphisms. -/
theorem pointwiseLeftKanMap_app (f : X ⟶ Y) (k : K) :
    (pointwiseLeftKanMap u f).app k =
      (u.leftKanExtensionObjIsoColimit X k).hom ≫
        colimMap (Functor.whiskerLeft (CostructuredArrow.proj u k) f) ≫
          (u.leftKanExtensionObjIsoColimit Y k).inv := by
  apply (cancel_epi (u.leftKanExtensionObjIsoColimit X k).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply colimit.hom_ext
  intro j
  rw [u.ι_leftKanExtensionObjIsoColimit_inv_assoc]
  have hn := (pointwiseLeftKanMap u f).naturality j.hom
  change (u.leftKanExtension X).map j.hom ≫ (pointwiseLeftKanMap u f).app k =
    (pointwiseLeftKanMap u f).app (u.obj j.left) ≫ (u.leftKanExtension Y).map j.hom at hn
  rw [hn, ← Category.assoc, pointwiseLeftKanMap_unit,
    Category.assoc, ι_colimMap_assoc, u.ι_leftKanExtensionObjIsoColimit_inv]
  rfl

end ABCCofibrations

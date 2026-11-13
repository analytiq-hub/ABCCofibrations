/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.KanMapComparison
public import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Kan extensions and opposites

The universal-property bridge used to transport relative colimit results to
relative limits. No homotopical axioms are used here.
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace ABCCofibrations

variable {J K M : Type*} [Category J] [Category K] [Category M]
  {u : J ⥤ K} {X : J ⥤ M}

/-- The counit obtained from a unit on opposite categories. -/
def unopLeftKanCounit {G : Kᵒᵖ ⥤ Mᵒᵖ} (η : X.op ⟶ u.op ⋙ G) : u ⋙ G.unop ⟶ X where
  app j := (η.app (op j)).unop
  naturality _ _ f := Quiver.Hom.op_inj (η.naturality f.op).symm

/-- Unoppositing a left Kan extension gives a right Kan extension. -/
theorem isRightKanExtension_unop {G : Kᵒᵖ ⥤ Mᵒᵖ} (η : X.op ⟶ u.op ⋙ G)
    [G.IsLeftKanExtension η] : G.unop.IsRightKanExtension (unopLeftKanCounit η) := by
  refine ⟨⟨IsTerminal.ofUniqueHom (fun E ↦ CostructuredArrow.homMk
    (NatTrans.unop (G.descOfIsLeftKanExtension η E.left.op (NatTrans.op E.hom))) ?_) ?_⟩⟩
  · ext j
    apply Quiver.Hom.op_inj
    exact G.descOfIsLeftKanExtension_fac_app η E.left.op (NatTrans.op E.hom) (op j)
  · intro E m
    apply CostructuredArrow.hom_ext
    have h : NatTrans.op m.left =
        G.descOfIsLeftKanExtension η E.left.op (NatTrans.op E.hom) := by
      apply G.hom_ext_of_isLeftKanExtension η
      apply NatTrans.ext
      funext j
      have hm := congr_app (CostructuredArrow.w m) j.unop
      exact (congrArg Quiver.Hom.op hm).trans
        (G.descOfIsLeftKanExtension_fac_app η E.left.op (NatTrans.op E.hom) j).symm
    ext k
    exact Quiver.Hom.op_inj (congr_app h (op k))

/-- Existence of a left extension on opposites gives existence of a right extension. -/
theorem hasRightKanExtension_of_op (u : J ⥤ K) (X : J ⥤ M)
    [u.op.HasLeftKanExtension X.op] : u.HasRightKanExtension X := by
  have := isRightKanExtension_unop (u.op.leftKanExtensionUnit X.op)
  exact Functor.HasRightKanExtension.mk _ (unopLeftKanCounit (u.op.leftKanExtensionUnit X.op))

/-- Pointwise left extensions of opposite diagrams give pointwise right extensions. -/
theorem hasPointwiseRightKanExtension_of_op (u : J ⥤ K) (X : J ⥤ M)
    [u.op.HasPointwiseLeftKanExtension X.op] : u.HasPointwiseRightKanExtension X := by
  intro k
  have : HasColimit ((structuredArrowOpEquivalence u k).functor ⋙
      CostructuredArrow.proj u.op (op k) ⋙ X.op) := inferInstance
  have : HasColimit (StructuredArrow.proj k u ⋙ X).op := this
  exact hasLimit_of_hasColimit_op _

/-- The chosen right extension is canonically isomorphic to the unopposite of
any left extension of the opposite diagram. -/
noncomputable def rightKanExtensionIsoUnopLeft (u : J ⥤ K) (X : J ⥤ M)
    [u.op.HasLeftKanExtension X.op] [u.HasRightKanExtension X] :
    u.rightKanExtension X ≅ (u.op.leftKanExtension X.op).unop := by
  have := isRightKanExtension_unop (u.op.leftKanExtensionUnit X.op)
  exact (u.rightKanExtension X).rightKanExtensionUnique (u.rightKanExtensionCounit X)
    _ (unopLeftKanCounit (u.op.leftKanExtensionUnit X.op))

@[reassoc]
theorem rightKanExtensionIsoUnopLeft_counit (u : J ⥤ K) (X : J ⥤ M)
    [u.op.HasLeftKanExtension X.op] [u.HasRightKanExtension X] (j : J) :
    (rightKanExtensionIsoUnopLeft u X).hom.app (u.obj j) ≫
      ((u.op.leftKanExtensionUnit X.op).app (op j)).unop =
      (u.rightKanExtensionCounit X).app j := by
  have := isRightKanExtension_unop (u.op.leftKanExtensionUnit X.op)
  simpa only [rightKanExtensionIsoUnopLeft, Functor.rightKanExtensionUnique,
    Functor.rightKanExtensionUniqueOfIso, Iso.refl_hom, Category.comp_id,
    unopLeftKanCounit] using
    (Functor.liftOfIsRightKanExtension_fac_app (u.op.leftKanExtension X.op).unop
      (unopLeftKanCounit (u.op.leftKanExtensionUnit X.op)) (u.rightKanExtension X)
      (u.rightKanExtensionCounit X) j)

section Maps

variable (u : J ⥤ K) {X Y : J ⥤ M}
  [u.HasPointwiseRightKanExtension X] [u.HasPointwiseRightKanExtension Y]

/-- The canonical map between two individually existing right Kan extensions. -/
noncomputable def pointwiseRightKanMap (f : X ⟶ Y) :
    u.rightKanExtension X ⟶ u.rightKanExtension Y :=
  (u.rightKanExtension Y).liftOfIsRightKanExtension (u.rightKanExtensionCounit Y)
    (u.rightKanExtension X) (u.rightKanExtensionCounit X ≫ f)

@[reassoc]
theorem pointwiseRightKanMap_counit (f : X ⟶ Y) (j : J) :
    (pointwiseRightKanMap u f).app (u.obj j) ≫ (u.rightKanExtensionCounit Y).app j =
      (u.rightKanExtensionCounit X).app j ≫ f.app j :=
  Functor.liftOfIsRightKanExtension_fac_app _ _ _ _ _

variable [u.op.HasPointwiseLeftKanExtension X.op] [u.op.HasPointwiseLeftKanExtension Y.op]

/-- The canonical comparison with opposite left extensions commutes with maps. -/
theorem rightKanExtensionIsoUnopLeft_naturality (f : X ⟶ Y) :
    pointwiseRightKanMap u f ≫ (rightKanExtensionIsoUnopLeft u Y).hom =
      (rightKanExtensionIsoUnopLeft u X).hom ≫
        NatTrans.unop (pointwiseLeftKanMap u.op (NatTrans.op f)) := by
  have := isRightKanExtension_unop (u.op.leftKanExtensionUnit Y.op)
  apply ((u.op.leftKanExtension Y.op).unop).hom_ext_of_isRightKanExtension
    (unopLeftKanCounit (u.op.leftKanExtensionUnit Y.op))
  apply NatTrans.ext
  funext j
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, unopLeftKanCounit]
  rw [Category.assoc, rightKanExtensionIsoUnopLeft_counit, pointwiseRightKanMap_counit]
  have h := congrArg Quiver.Hom.unop
    (pointwiseLeftKanMap_unit u.op (NatTrans.op f) (op j))
  dsimp at h
  dsimp
  rw [Category.assoc, h, ← Category.assoc, rightKanExtensionIsoUnopLeft_counit]

/-- Evaluation of a right-extension map, expressed through the opposite left map. -/
theorem pointwiseRightKanMap_app_op (f : X ⟶ Y) (k : K) :
    (pointwiseRightKanMap u f).app k =
      (rightKanExtensionIsoUnopLeft u X).hom.app k ≫
        ((pointwiseLeftKanMap u.op (NatTrans.op f)).app (op k)).unop ≫
          (rightKanExtensionIsoUnopLeft u Y).inv.app k := by
  have h := congr_app (rightKanExtensionIsoUnopLeft_naturality u f) k
  simpa only [NatTrans.comp_app, NatTrans.unop_app, Iso.app_inv, Category.assoc] using
    (Iso.eq_comp_inv ((rightKanExtensionIsoUnopLeft u Y).app k)).2 h

/-- The comparison with a native right extension, viewed as an opposite diagram. -/
noncomputable def leftKanExtensionIsoOpRight :
    u.op.leftKanExtension X.op ≅ (u.rightKanExtension X).op :=
  (Functor.unopOpIso (u.op.leftKanExtension X.op)).symm ≪≫
    NatIso.op (rightKanExtensionIsoUnopLeft u X)

/-- Naturality of the comparison, in the direction used to transport Reedy maps. -/
theorem leftKanExtensionIsoOpRight_naturality (f : X ⟶ Y) :
    NatTrans.op (pointwiseRightKanMap u f) =
      (leftKanExtensionIsoOpRight u (X := Y)).inv ≫
        pointwiseLeftKanMap u.op (NatTrans.op f) ≫
          (leftKanExtensionIsoOpRight u (X := X)).hom := by
  apply NatTrans.ext
  funext k
  change ((pointwiseRightKanMap u f).app k.unop).op = _
  rw [pointwiseRightKanMap_app_op]
  simp [leftKanExtensionIsoOpRight, NatIso.op, Functor.unopOpIso, op_comp, Category.assoc]

end Maps

end ABCCofibrations

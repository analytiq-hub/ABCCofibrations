/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayerExtension
public import ABCCofibrations.ReedyOpenReflection

/-! # Reedy cofibrancy of a whole-layer extension -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.ReedyLayer
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)
  (hmax : ∀ d, ¬ P d → ∀ e (f : d ⟶ e), ∃ h : d = e, f = eqToHom h)

include hmax in
/-- A maximal complementary layer has open old subcategory. -/
lemma isOpen_of_maximal_complement : IsOpenDiagramSubcategory P := by
  intro a b f hb
  by_contra ha
  obtain ⟨h, _⟩ := hmax a ha b f
  exact ha (Eq.mp (congrArg P h.symm) hb)

variable [IsDirect D] {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]
  (F : P.FullSubcategory ⥤ M) [∀ e, HasColimit (latchingDiagram F e)]
  (c : ∀ d : Objects P, Cocone (latchingToOld P hmax d ⋙ F))
  [∀ d : Objects P, HasColimit (latchingToOld P hmax d ⋙ F)]

/-- A Reedy cofibrant old diagram and cofibrant latching cocones extend to a
Reedy cofibrant whole diagram. The individual new latching colimits suffice. -/
theorem isReedyCofibrant_extension (hF : IsReedyCofibrant F)
    (hL : ∀ d : Objects P, IsCofibrant (colimit (latchingToOld P hmax d ⋙ F)))
    (hc : ∀ d : Objects P, Cofibration (colimit.desc _ (c d))) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (extension P hmax F c) e)),
      IsReedyCofibrant (extension P hmax F c) := by
  obtain ⟨_, hOld⟩ := isReedyCofibration_of_isIso (extensionRestrictIso P hmax F c).inv hF
  apply isReedyCofibrant_of_open_restriction P (isOpen_of_maximal_complement P hmax)
    (extension P hmax F c) hOld.2.1
  intro d
  have hCol := hasColimit_extension_latching_new P hmax F c d
  let eL := HasColimit.isoOfNatIso (extensionLatchingIso P hmax F c d)
  let eO := extensionObjIsoNew P hmax F c d
  have := hL d
  have := hc d
  have := cofibration_of_isIso eL.inv
  have hLC : IsCofibrant (latchingObj (extension P hmax F c) d.val) :=
    cofibrant_target eL.inv
  have := cofibration_of_isIso eL.hom
  have hOC : IsCofibrant (c d).pt := cofibrant_target (colimit.desc _ (c d))
  have := cofibration_of_isIso eO.inv
  refine ⟨hCol, hLC, ?_⟩
  rw [latchingMap_extension]
  infer_instance

omit [IsDirect D] [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M]
  [HasInitial M] [ABCPrecofibrationCategory M]
  [∀ e, HasColimit (latchingDiagram F e)] in
/-- The map on new latching objects is the old predecessor map under the
canonical latching comparison. -/
lemma extensionLift_latchingObjMap (X : D ⥤ M) [∀ e, HasColimit (latchingDiagram X e)]
    (a : P.ι ⋙ X ⟶ F) (i : ∀ d : Objects P, X.obj d.val ⟶ (c d).pt)
    (hi : ∀ (d : Objects P) (j : LatchingCategory d.val),
      X.map j.obj.hom ≫ i d = a.app ((latchingToOld P hmax d).obj j) ≫ (c d).ι.app j)
    (d : Objects P) [HasColimit (latchingDiagram (extension P hmax F c) d.val)]
    [HasColimit (latchingToOld P hmax d ⋙ P.ι ⋙ X)] :
    latchingObjMap (extensionLift P hmax X a i hi) d.val ≫
        (HasColimit.isoOfNatIso (extensionLatchingIso P hmax F c d)).hom =
      colimMap (Functor.whiskerLeft (latchingToOld P hmax d) a) := by
  apply colimit.hom_ext
  intro j
  erw [ι_latchingObjMap_assoc, HasColimit.ι_isoOfNatIso_hom, ι_colimMap]
  change (extensionLift P hmax X a i hi).app j.obj.left ≫
    (extensionObjIsoOld P hmax F c (predecessor_mem P hmax d j)).hom ≫
      colimit.ι (latchingToOld P hmax d ⋙ F) j = _
  rw [extensionLift_app_old P hmax X a i hi (predecessor_mem P hmax d j)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- A Reedy cofibration on the old subcategory and relative cofibrations at
all new objects give a Reedy cofibration into the extension. -/
theorem isReedyCofibration_extensionLift
    (X : D ⥤ M) [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X)
    (a : P.ι ⋙ X ⟶ F) [∀ e, HasColimit (latchingDiagram (P.ι ⋙ X) e)]
    (ha : IsReedyCofibration a)
    [∀ d : Objects P, HasColimit (latchingToOld P hmax d ⋙ P.ι ⋙ X)]
    (i : ∀ d : Objects P, X.obj d.val ⟶ (c d).pt)
    (hi : ∀ (d : Objects P) (j : LatchingCategory d.val),
      X.map j.obj.hom ≫ i d = a.app ((latchingToOld P hmax d).obj j) ≫ (c d).ι.app j)
    (hL : ∀ d : Objects P, IsCofibrant (colimit (latchingToOld P hmax d ⋙ F)))
    (hRel : ∀ d : Objects P, ∃ (Q : M) (l : X.obj d.val ⟶ Q)
      (t : colimit (latchingToOld P hmax d ⋙ F) ⟶ Q) (k : Q ⟶ (c d).pt),
      IsPushout (latchingMap X d.val)
        (colimMap (Functor.whiskerLeft (latchingToOld P hmax d) a)) l t ∧
      l ≫ k = i d ∧ t ≫ k = colimit.desc _ (c d) ∧ Cofibration k) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (extension P hmax F c) e)),
      IsReedyCofibration (extensionLift P hmax X a i hi) := by
  have hc (d : Objects P) : Cofibration (colimit.desc _ (c d)) := by
    obtain ⟨Q, l, t, k, hQ, hl, ht, hk⟩ := hRel d
    obtain ⟨hLX, hix⟩ := hX d.val
    have := hL d
    have := cofibration_of_isPushout hQ
    rw [← ht]
    infer_instance
  obtain ⟨hCol, hE⟩ := isReedyCofibrant_extension P hmax F c ha.2.1 hL hc
  let f := extensionLift P hmax X a i hi
  obtain ⟨_, hInv⟩ := isReedyCofibration_of_isIso (extensionRestrictIso P hmax F c).inv ha.2.1
  have hOld : IsReedyCofibration (Functor.whiskerLeft P.ι f) := by
    rw [show Functor.whiskerLeft P.ι f = a ≫ (extensionRestrictIso P hmax F c).inv by
      ext e
      exact extensionLift_app_old P hmax X a i hi e.property]
    exact ha.comp hInv
  refine ⟨hCol, hX, hE, fun e ↦ ?_⟩
  classical
  by_cases he : P e
  · obtain ⟨Q, l, t, k, hQ, hl, ht, hk⟩ := hOld.2.2 ⟨e, he⟩
    obtain ⟨t', hQ', ht'⟩ := comparison_of_open_restriction P
      (isOpen_of_maximal_complement P hmax) f ⟨e, he⟩ hQ ht
    exact ⟨Q, l, t', k, hQ', hl, ht', hk⟩
  · let d : Objects P := ⟨e, he⟩
    obtain ⟨Q, l, t, k, hQ, hl, ht, hk⟩ := hRel d
    let eL := HasColimit.isoOfNatIso (extensionLatchingIso P hmax F c d)
    let eO := extensionObjIsoNew P hmax F c d
    have hNat : latchingObjMap f e ≫ eL.hom =
        colimMap (Functor.whiskerLeft (latchingToOld P hmax d) a) :=
      extensionLift_latchingObjMap P hmax F c X a i hi d
    have hQ' : IsPushout (latchingMap X e) (latchingObjMap f e) l (eL.hom ≫ t) :=
      hQ.of_iso (Iso.refl _) (Iso.refl _) eL.symm (Iso.refl _)
        (by simp; rfl) (by simpa only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
          using ((Iso.eq_comp_inv eL).2 hNat).symm) (by simp) (by simp)
    have := hL d
    have := hc d
    have : IsCofibrant (c d).pt := cofibrant_target (colimit.desc _ (c d))
    have := cofibration_of_isIso eO.inv
    have hK : Cofibration (k ≫ eO.inv) := by infer_instance
    refine ⟨Q, l, eL.hom ≫ t, k ≫ eO.inv, hQ', ?_, ?_, hK⟩
    · rw [← Category.assoc, hl]
      exact (extensionLift_app_new P hmax X a i hi d).symm
    · rw [Category.assoc, ← Category.assoc t, ht]
      exact (latchingMap_extension P hmax F c d).symm

end ABCCofibrations.ReedyLayer

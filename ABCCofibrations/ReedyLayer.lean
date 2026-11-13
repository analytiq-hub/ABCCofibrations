/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyOpen
public import ABCCofibrations.SmallSums

/-!
# Attaching an arbitrary layer of maximal objects

Lemma 9.3.2(1): attach all objects outside an open full subcategory at once.
The categorical pushout description is proved without finiteness assumptions;
CF5(1) supplies the coproducts for cofibrant latching objects and latching maps.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations
namespace ReedyLayer

variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)

/-- The objects attached in the new layer, used as a discrete coproduct index. -/
abbrev Objects := {d : D // ¬ P d}

variable (hmax : ∀ (d : D), ¬ P d → ∀ (e : D) (g : d ⟶ e),
  ∃ h : d = e, g = eqToHom h)

include hmax in
/-- All proper predecessors of an attached maximal object lie in the old subcategory. -/
lemma predecessor_mem (d : Objects P) (j : LatchingCategory d.val) : P j.obj.left := by
  by_contra h
  obtain ⟨he, _⟩ := hmax j.obj.left h d.val j.obj.hom
  exact j.property he

/-- Forgetting a latching arrow lands in the old subcategory. -/
def latchingToOld (d : Objects P) : LatchingCategory d.val ⥤ P.FullSubcategory :=
  P.lift (ObjectProperty.ι _ ⋙ Over.forget d.val) (predecessor_mem P hmax d)

variable {M : Type u} [Category.{v} M] (X : D ⥤ M)
  [∀ d : Objects P, HasColimit (latchingDiagram X d.val)] [HasColimit (P.ι ⋙ X)]

/-- The boundary map for one object of the new layer. -/
noncomputable def boundary (d : Objects P) : latchingObj X d.val ⟶ colimit (P.ι ⋙ X) :=
  colimit.desc _
    { pt := colimit (P.ι ⋙ X)
      ι :=
        { app := fun j ↦ colimit.ι (P.ι ⋙ X) ((latchingToOld P hmax d).obj j)
          naturality := fun a b f ↦ by
            simpa [latchingDiagram, latchingToOld] using
              (colimit.w (P.ι ⋙ X) ((latchingToOld P hmax d).map f)).trans
                (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma ι_boundary (d : Objects P) (j : LatchingCategory d.val) :
    colimit.ι (latchingDiagram X d.val) j ≫ boundary P hmax X d =
      colimit.ι (P.ι ⋙ X) ((latchingToOld P hmax d).obj j) := colimit.ι_desc _ _

variable [HasCoproduct (fun d : Objects P ↦ latchingObj X d.val)]
  [HasCoproduct (fun d : Objects P ↦ X.obj d.val)]

/-- The coproduct of all attaching maps. -/
noncomputable abbrev attachingMap : (∐ fun d : Objects P ↦ latchingObj X d.val) ⟶
    ∐ fun d : Objects P ↦ X.obj d.val := Limits.Sigma.map (fun d ↦ latchingMap X d.val)

/-- The whole layer's boundary map into the old colimit. -/
noncomputable abbrev boundaryMap : (∐ fun d : Objects P ↦ latchingObj X d.val) ⟶
    colimit (P.ι ⋙ X) := Sigma.desc (boundary P hmax X)

variable {Q : M} (l : (∐ fun d : Objects P ↦ X.obj d.val) ⟶ Q)
  (r : colimit (P.ι ⋙ X) ⟶ Q)

open Classical in
/-- The cocone legs for simultaneous attachment. -/
noncomputable def leg (e : D) : X.obj e ⟶ Q :=
  if h : P e then colimit.ι (P.ι ⋙ X) ⟨e, h⟩ ≫ r
  else Sigma.ι (fun d : Objects P ↦ X.obj d.val) ⟨e, h⟩ ≫ l

omit [HasCoproduct (fun d : Objects P ↦ latchingObj X d.val)]
  [∀ d : Objects P, HasColimit (latchingDiagram X d.val)] in
lemma leg_old {e : D} (he : P e) :
    leg P X l r e = colimit.ι (P.ι ⋙ X) ⟨e, he⟩ ≫ r := by simp [leg, he]

omit [HasCoproduct (fun d : Objects P ↦ latchingObj X d.val)]
  [∀ d : Objects P, HasColimit (latchingDiagram X d.val)] in
lemma leg_new (d : Objects P) :
    leg P X l r d.val = Sigma.ι (fun d : Objects P ↦ X.obj d.val) d ≫ l := by
  simp [leg, d.property]

variable {l r} (sq : IsPushout (attachingMap P X) (boundaryMap P hmax X) l r)

include sq in
lemma leg_naturality {a b : D} (f : a ⟶ b) :
    X.map f ≫ leg P X l r b = leg P X l r a := by
  classical
  by_cases ha : P a
  · by_cases hb : P b
    · rw [leg_old P X l r ha, leg_old P X l r hb, ← Category.assoc]
      exact congrArg (· ≫ r) (colimit.w (P.ι ⋙ X) (⟨f⟩ : (⟨a, ha⟩ : P.FullSubcategory) ⟶ ⟨b, hb⟩))
    · have hab : a ≠ b := fun h ↦ hb (h ▸ ha)
      have : HasColimit (latchingDiagram X b) :=
        (inferInstance : ∀ d : Objects P, HasColimit (latchingDiagram X d.val)) ⟨b, hb⟩
      let j : LatchingCategory b := ⟨Over.mk f, hab⟩
      have h := congrArg
        ((colimit.ι (latchingDiagram X b) j ≫
          Sigma.ι (fun d : Objects P ↦ latchingObj X d.val) ⟨b, hb⟩) ≫ ·) sq.w
      simp only [attachingMap, boundaryMap, Category.assoc, Sigma.ι_map_assoc,
        Sigma.ι_comp_desc_assoc, ι_latchingMap_assoc] at h
      erw [ι_boundary_assoc P hmax X (⟨b, hb⟩ : Objects P) j] at h
      rw [leg_old P X l r ha, leg_new P X l r (⟨b, hb⟩ : Objects P)]
      exact h
  · obtain ⟨he, hf⟩ := hmax a ha b f
    subst b
    simp [hf]

/-- The cocone obtained from a pushout of the layer's attaching maps. -/
noncomputable def cocone : Cocone X where
  pt := Q
  ι :=
    { app := leg P X l r
      naturality := fun _ _ f ↦ (leg_naturality P hmax X sq f).trans (Category.comp_id _).symm }

/-- The pushout has the universal property of the whole diagram's colimit. -/
noncomputable def isColimitCocone : IsColimit (cocone P hmax X sq) where
  desc c := sq.desc (Sigma.desc (fun d : Objects P ↦ c.ι.app d.val))
    (colimit.desc (P.ι ⋙ X) (c.whisker P.ι)) (by
      apply Sigma.hom_ext
      intro d
      apply colimit.hom_ext
      intro j
      simp only [attachingMap, boundaryMap, Sigma.ι_map_assoc,
        Sigma.ι_comp_desc_assoc, ι_latchingMap_assoc, ι_boundary_assoc]
      erw [Sigma.ι_comp_desc]
      change X.map j.obj.hom ≫ c.ι.app d.val =
        colimit.ι (P.ι ⋙ X) ((latchingToOld P hmax d).obj j) ≫
          colimit.desc (P.ι ⋙ X) (c.whisker P.ι)
      rw [colimit.ι_desc]
      exact c.w j.obj.hom)
  fac c e := by
    change leg P X l r e ≫ _ = _
    by_cases he : P e
    · rw [leg_old P X l r he, Category.assoc, sq.inr_desc, colimit.ι_desc]
      rfl
    · rw [leg_new P X l r (⟨e, he⟩ : Objects P), Category.assoc, sq.inl_desc, Sigma.ι_comp_desc]
  uniq c m hm := by
    apply sq.hom_ext
    · rw [sq.inl_desc]
      apply Sigma.hom_ext
      intro d
      rw [Sigma.ι_comp_desc]
      have h := hm d.val
      change leg P X l r d.val ≫ m = _ at h
      rw [leg_new] at h
      exact (Category.assoc _ _ _).symm.trans h
    · rw [sq.inr_desc]
      apply colimit.hom_ext
      intro e
      rw [colimit.ι_desc]
      have h := hm e.obj
      change leg P X l r e.obj ≫ m = _ at h
      rw [leg_old P X l r e.property] at h
      exact (Category.assoc _ _ _).symm.trans h

end ReedyLayer
section Axioms

variable {D : Type w} [SmallCategory D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory ReedyLayer

/-- Lemma 9.3.2(1), using only CF1–CF4 and the existence/cofibration part of CF5.
The attached objects may form an infinite set. -/
theorem colimit_isPushout_layer (P : ObjectProperty D)
    (hmax : ∀ (d : D), ¬ P d → ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
    (h5 : CoproductCofibrationAxiom.{w} M) (X : D ⥤ M)
    [∀ d : Objects P, HasColimit (latchingDiagram X d.val)] [HasColimit (P.ι ⋙ X)]
    (hL : ∀ d : Objects P, IsCofibrant (latchingObj X d.val))
    (hi : ∀ d : Objects P, Cofibration (latchingMap X d.val))
    (hC : IsCofibrant (colimit (P.ι ⋙ X))) :
    ∃ (_ : HasCoproduct (fun d : Objects P ↦ latchingObj X d.val))
      (_ : HasCoproduct (fun d : Objects P ↦ X.obj d.val)) (_ : HasColimit X),
      IsPushout (attachingMap P X) (boundaryMap P hmax X)
        (Sigma.desc (fun d : Objects P ↦ colimit.ι X d.val)) (colimit.pre X P.ι) ∧
      IsCofibrant (colimit X) ∧ Cofibration (colimit.pre X P.ι) := by
  have hO (d : Objects P) : IsCofibrant (X.obj d.val) := by
    have := hL d
    have := hi d
    exact cofibrant_target (latchingMap X d.val)
  have hSumL := h5.hasCoproduct (fun d : Objects P ↦ latchingObj X d.val) hL
  have hSumX := h5.hasCoproduct (fun d : Objects P ↦ X.obj d.val) hO
  have := h5.coproduct_cofibrant (fun d : Objects P ↦ latchingObj X d.val) hL
  have hAttach : Cofibration (attachingMap P X) := h5.coproduct_cofibration _ hL hi
  have : HasPushout (attachingMap P X) (boundaryMap P hmax X) := hasPushout _ _
  let sq := IsPushout.of_hasPushout (attachingMap P X) (boundaryMap P hmax X)
  let hc := isColimitCocone P hmax X sq
  have hCol : HasColimit X := ⟨⟨⟨_, hc⟩⟩⟩
  let e : pushout (attachingMap P X) (boundaryMap P hmax X) ≅ colimit X :=
    hc.coconePointUniqueUpToIso (colimit.isColimit X)
  have hcomp (d : D) : leg P X (pushout.inl _ _) (pushout.inr _ _) d ≫ e.hom =
      colimit.ι X d := hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit X) d
  have heL : pushout.inl (attachingMap P X) (boundaryMap P hmax X) ≫ e.hom =
      Sigma.desc (fun d : Objects P ↦ colimit.ι X d.val) := by
    apply Sigma.hom_ext
    intro d
    rw [Sigma.ι_comp_desc]
    have h := hcomp d.val
    rw [leg_new, Category.assoc] at h
    exact h
  have heR : pushout.inr (attachingMap P X) (boundaryMap P hmax X) ≫ e.hom =
      colimit.pre X P.ι := by
    apply colimit.hom_ext
    intro d
    rw [colimit.ι_pre]
    have h := hcomp d.obj
    rw [leg_old P X _ _ d.property, Category.assoc] at h
    exact h
  have hsq : IsPushout (attachingMap P X) (boundaryMap P hmax X)
      (Sigma.desc (fun d : Objects P ↦ colimit.ι X d.val)) (colimit.pre X P.ι) :=
    sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (by simp) (by simp) (by simpa using heL) (by simpa using heR)
  have hpre : Cofibration (colimit.pre X P.ι) := cofibration_of_isPushout hsq
  exact ⟨hSumL, hSumX, hCol, hsq, cofibrant_target (colimit.pre X P.ι), hpre⟩

end Axioms

end ABCCofibrations

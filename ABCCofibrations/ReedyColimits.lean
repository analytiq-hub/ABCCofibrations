/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBasic

/-!
# Colimits over direct categories as pushouts (Lemma 9.3.1)

Let `d` be an object of `D` with no non-identity maps out of it (for a direct
category and `d` of maximal degree, `D ∖ {d} ⥤ D` is then an open embedding).
For `X : D ⥤ M`, the colimit of `X` is the pushout of
`X_d ⟵ LX_d ⟶ colim_{D ∖ {d}} X`. The cocone on `X` with vertex the pushout is
built by cases on whether an object is `d`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D : Type u₁} [Category.{v₁} D] {M : Type u₂} [Category.{v₂} M]

/-- The objects of `D` other than `d`. -/
def complementProp (d : D) : ObjectProperty D := fun e ↦ e ≠ d

/-- The full subcategory `D ∖ {d}`. -/
abbrev Complement (d : D) : Type u₁ := (complementProp d).FullSubcategory

/-- The functor `∂(D ↓ d) ⥤ D ∖ {d}` forgetting the map to `d`. -/
def latchingToComplement (d : D) : LatchingCategory d ⥤ Complement d :=
  (complementProp d).lift (ObjectProperty.ι _ ⋙ Over.forget d) (fun j ↦ j.property)

variable (X : D ⥤ M) (d : D)

/-- The map `f_d : LX_d ⟶ colim_{D ∖ {d}} X`. -/
noncomputable def latchingToComplementColimit [HasColimit (latchingDiagram X d)]
    [HasColimit ((complementProp d).ι ⋙ X)] :
    latchingObj X d ⟶ colimit ((complementProp d).ι ⋙ X) :=
  colimit.desc _
    { pt := colimit ((complementProp d).ι ⋙ X)
      ι :=
        { app := fun j ↦ colimit.ι ((complementProp d).ι ⋙ X) ⟨j.obj.left, j.property⟩
          naturality := fun j j' g ↦ by
            have := colimit.w ((complementProp d).ι ⋙ X)
              (show (⟨j.obj.left, j.property⟩ : Complement d) ⟶ ⟨j'.obj.left, j'.property⟩ from
                ⟨g.hom.left⟩)
            simpa [latchingDiagram] using this } }

@[reassoc (attr := simp)]
lemma ι_latchingToComplementColimit [HasColimit (latchingDiagram X d)]
    [HasColimit ((complementProp d).ι ⋙ X)] (j : LatchingCategory d) :
    colimit.ι (latchingDiagram X d) j ≫ latchingToComplementColimit X d =
      colimit.ι ((complementProp d).ι ⋙ X) ⟨j.obj.left, j.property⟩ :=
  colimit.ι_desc _ _

section Pushout

variable {X d} [HasColimit (latchingDiagram X d)] [HasColimit ((complementProp d).ι ⋙ X)]
  {P : M} {inl : X.obj d ⟶ P} {inr : colimit ((complementProp d).ι ⋙ X) ⟶ P}

open Classical in
/-- The legs `X_e ⟶ P` of the cocone with vertex the pushout. -/
noncomputable def pushoutLeg (inl : X.obj d ⟶ P) (inr : colimit ((complementProp d).ι ⋙ X) ⟶ P)
    (e : D) : X.obj e ⟶ P :=
  if h : e = d then eqToHom (by rw [h]) ≫ inl
  else colimit.ι ((complementProp d).ι ⋙ X) ⟨e, h⟩ ≫ inr

omit [HasColimit (latchingDiagram X d)] in
lemma pushoutLeg_self : pushoutLeg inl inr d = inl := by
  simp [pushoutLeg]

omit [HasColimit (latchingDiagram X d)] in
lemma pushoutLeg_ne {e : D} (h : e ≠ d) :
    pushoutLeg inl inr e = colimit.ι ((complementProp d).ι ⋙ X) ⟨e, h⟩ ≫ inr := by
  simp [pushoutLeg, h]

variable (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
  (hP : IsPushout (latchingMap X d) (latchingToComplementColimit X d) inl inr)

include hd hP

lemma pushoutLeg_naturality {e e' : D} (g : e ⟶ e') :
    X.map g ≫ pushoutLeg inl inr e' = pushoutLeg inl inr e := by
  by_cases he : e = d
  · subst he
    obtain ⟨h, rfl⟩ := hd e' g
    subst h
    simp
  · by_cases he' : e' = d
    · subst he'
      rw [pushoutLeg_self, pushoutLeg_ne he]
      have := congrArg (colimit.ι (latchingDiagram X e') ⟨Over.mk g, he⟩ ≫ ·) hP.w
      simp only [ι_latchingMap_assoc, ι_latchingToComplementColimit_assoc] at this
      exact this
    · rw [pushoutLeg_ne he, pushoutLeg_ne he']
      have := colimit.w ((complementProp d).ι ⋙ X)
        (show (⟨e, he⟩ : Complement d) ⟶ ⟨e', he'⟩ from ⟨g⟩)
      rw [← this, Category.assoc]
      rfl

/-- The cocone on `X` with vertex the pushout. -/
noncomputable def pushoutCocone' : Cocone X where
  pt := P
  ι :=
    { app := pushoutLeg inl inr
      naturality := fun _ _ g ↦
        (pushoutLeg_naturality hd hP g).trans (Category.comp_id _).symm }

/-- The pushout is a colimit of `X`. -/
noncomputable def isColimitPushoutCocone' : IsColimit (pushoutCocone' hd hP) where
  desc c := hP.desc (c.ι.app d)
    (colimit.desc ((complementProp d).ι ⋙ X) (c.whisker (complementProp d).ι))
    (by
      apply colimit.hom_ext
      intro j
      rw [ι_latchingMap_assoc, ι_latchingToComplementColimit_assoc]
      exact (c.w j.obj.hom).trans
        (colimit.ι_desc (c.whisker (complementProp d).ι) ⟨j.obj.left, j.property⟩).symm)
  fac c e := by
    change pushoutLeg inl inr e ≫ _ = _
    by_cases he : e = d
    · subst he
      rw [pushoutLeg_self, hP.inl_desc]
    · rw [pushoutLeg_ne he, Category.assoc, hP.inr_desc, colimit.ι_desc]
      rfl
  uniq c m hm := by
    refine hP.hom_ext ?_ ?_
    · rw [hP.inl_desc, ← hm d]
      change _ = pushoutLeg inl inr d ≫ m
      rw [pushoutLeg_self]
    · rw [hP.inr_desc]
      apply colimit.hom_ext
      intro e
      rw [colimit.ι_desc]
      have h := hm e.obj
      rw [show (pushoutCocone' hd hP).ι.app e.obj =
        colimit.ι ((complementProp d).ι ⋙ X) ⟨e.obj, e.property⟩ ≫ inr from
          pushoutLeg_ne e.property] at h
      exact (Category.assoc _ _ _).symm.trans h

end Pushout

open ABCPrecofibrationCategory in
/-- **Lemma 9.3.1(1).** Let `d` be an object with no non-identity maps out of it
(so `D ∖ {d} ⥤ D` is an open embedding), and `X : D ⥤ M` a diagram in a
precofibration category such that `LX_d` and `colim_{D ∖ {d}} X` exist and are
cofibrant and `i_d : LX_d ⟶ X_d` is a cofibration. Then `colim X` exists, the
square `X_d ⟵ LX_d ⟶ colim_{D ∖ {d}} X` with the colimit maps is a pushout, and
`colim X` is cofibrant and `j_d : colim_{D ∖ {d}} X ⟶ colim X` is a cofibration. -/
theorem colimit_isPushout_latching [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M]
    [HasInitial M] [ABCPrecofibrationCategory M]
    (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
    [HasColimit (latchingDiagram X d)] [HasColimit ((complementProp d).ι ⋙ X)]
    (hL : IsCofibrant (latchingObj X d)) (hC : IsCofibrant (colimit ((complementProp d).ι ⋙ X)))
    (hi : Cofibration (latchingMap X d)) :
    ∃ (_ : HasColimit X), IsPushout (latchingMap X d) (latchingToComplementColimit X d)
        (colimit.ι X d) (colimit.pre X (complementProp d).ι) ∧
      IsCofibrant (colimit X) ∧ Cofibration (colimit.pre X (complementProp d).ι) := by
  have : HasPushout (latchingMap X d) (latchingToComplementColimit X d) := hasPushout _ _
  let hP := IsPushout.of_hasPushout (latchingMap X d) (latchingToComplementColimit X d)
  let hc := isColimitPushoutCocone' hd hP
  have hX : HasColimit X := ⟨⟨⟨_, hc⟩⟩⟩
  refine ⟨hX, ?_⟩
  let e : pushout (latchingMap X d) (latchingToComplementColimit X d) ≅ colimit X :=
    hc.coconePointUniqueUpToIso (colimit.isColimit X)
  have hcomp (j : D) : pushoutLeg (pushout.inl _ _) (pushout.inr _ _) j ≫ e.hom =
      colimit.ι X j :=
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit X) j
  have he₁ : pushout.inl _ _ ≫ e.hom = colimit.ι X d := by
    have := hcomp d
    rwa [pushoutLeg_self] at this
  have he₂ : pushout.inr _ _ ≫ e.hom = colimit.pre X (complementProp d).ι := by
    apply colimit.hom_ext
    intro j
    have := hcomp j.obj
    rw [pushoutLeg_ne j.property, Category.assoc] at this
    rw [colimit.ι_pre]
    exact this
  have hsq : IsPushout (latchingMap X d) (latchingToComplementColimit X d)
      (colimit.ι X d) (colimit.pre X (complementProp d).ι) :=
    hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (by simp [he₁]) (by simp [he₂])
  refine ⟨hsq, ?_, ?_⟩
  · have := cofibration_of_isPushout hsq
    exact cofibrant_target (colimit.pre X (complementProp d).ι)
  · exact cofibration_of_isPushout hsq

end ABCCofibrations

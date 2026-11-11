/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyExtension

/-!
# Reedy factorizations (Theorem 9.2.4, axiom CF4)

Over a finite direct category, every map from a Reedy cofibrant diagram factors
as a Reedy cofibration followed by a pointwise weak equivalence. The
factorization is built object by object: remove an object `d` of maximal degree,
factor on `D ∖ {d}`, factor `X_d ⊔_{LX_d} LY'_d ⟶ Y_d` in `M`, and extend.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

open ABCPrecofibrationCategory

section Reverse

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]
  {J J' : Type*} [Category J] [Category J'] (F : J' ⥤ J) [F.Final]

/-- Cofibrancy and the cofibration property of the induced map transfer back
along a final functor. -/
lemma transfer_desc_rev (K : J ⥤ M) [HasColimit (F ⋙ K)] (c : Cocone K)
    (hK : IsCofibrant (colimit (F ⋙ K))) (hc : Cofibration (colimit.desc (F ⋙ K) (c.whisker F))) :
    ∃ (_ : HasColimit K), IsCofibrant (colimit K) ∧ Cofibration (colimit.desc K c) := by
  have : HasColimit K := Functor.Final.hasColimit_of_comp F
  refine ⟨this, ?_⟩
  have : IsIso (colimit.pre K F) := inferInstance
  have : Cofibration (colimit.pre K F) := cofibration_of_isIso _
  have hK' : IsCofibrant (colimit K) := cofibrant_target (colimit.pre K F)
  have : Cofibration (inv (colimit.pre K F)) := cofibration_of_isIso _
  refine ⟨hK', ?_⟩
  rw [show colimit.desc K c = inv (colimit.pre K F) ≫ colimit.desc (F ⋙ K) (c.whisker F) by
    rw [IsIso.eq_inv_comp, colimit.pre_desc]]
  infer_instance

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
/-- Relative latching comparisons transfer back along a final functor. -/
lemma transfer_comparison_rev {K K' : J ⥤ M} [HasColimit K] [HasColimit K'] [HasColimit (F ⋙ K)]
    [HasColimit (F ⋙ K')] (α : K ⟶ K') (c : Cocone K) (c' : Cocone K') {P : M}
    {l : c.pt ⟶ P} {r : colimit (F ⋙ K') ⟶ P} {k : P ⟶ c'.pt}
    (hP : IsPushout (colimit.desc (F ⋙ K) (c.whisker F)) (colimMap (Functor.whiskerLeft F α)) l r)
    (hr : r ≫ k = colimit.desc (F ⋙ K') (c'.whisker F)) :
    ∃ r' : colimit K' ⟶ P, IsPushout (colimit.desc K c) (colimMap α) l r' ∧
      r' ≫ k = colimit.desc K' c' := by
  have : IsIso (colimit.pre K F) := inferInstance
  have : IsIso (colimit.pre K' F) := inferInstance
  refine ⟨inv (colimit.pre K' F) ≫ r, ?_, by rw [Category.assoc, hr, IsIso.inv_comp_eq,
    colimit.pre_desc]⟩
  refine hP.of_iso (asIso (colimit.pre K F)) (Iso.refl _) (asIso (colimit.pre K' F))
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [colimit.pre_desc]
  · apply colimit.hom_ext
    intro j
    simp

end Reverse

section LatchLatchC

variable {D : Type w} [SmallCategory D] (deg : D → ℕ)
  (hdeg : ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h) {d : D}

/-- The latching category of `∂(D ↓ d)` at `j` maps to the latching category of
`D ∖ {d}` at `j`. -/
def latchLatchC (j : LatchingCategory d) :
    LatchingCategory j ⥤ LatchingCategory ((latchingToComplement d).obj j) where
  obj k := ⟨Over.mk (Y := (latchingToComplement d).obj k.obj.left) ⟨k.obj.hom.hom.left⟩,
    fun h ↦ latchLatch_ne deg hdeg j k (congrArg ObjectProperty.FullSubcategory.obj h)⟩
  map g := ⟨Over.homMk ⟨g.hom.left.hom.left⟩ (InducedCategory.hom_ext (by
    have := congrArg (fun φ ↦ φ.hom.left) (Over.w g.hom)
    exact this))⟩

instance (j : LatchingCategory d) : (latchLatchC deg hdeg j).Faithful where
  map_injective {_ _} g g' h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.hom.left.hom) h

instance (j : LatchingCategory d) : (latchLatchC deg hdeg j).Full where
  map_surjective {k k'} g := by
    have hk := Over.w k.obj.hom.hom
    have hk' := Over.w k'.obj.hom.hom
    have hg := congrArg InducedCategory.Hom.hom (Over.w g.hom)
    refine ⟨⟨Over.homMk ⟨Over.homMk g.hom.left.hom ?_⟩ ?_⟩, rfl⟩
    · exact (congrArg (g.hom.left.hom ≫ ·) hk').symm.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ j.obj.hom) hg).trans hk))
    · apply InducedCategory.hom_ext
      apply Over.OverMorphism.ext
      exact hg

lemma latchLatchC_essSurj (j : LatchingCategory d) : (latchLatchC deg hdeg j).EssSurj where
  mem_essImage m := by
    let kl : LatchingCategory d := ⟨Over.mk (m.obj.hom.hom ≫ j.obj.hom), m.obj.left.property⟩
    let kh : kl ⟶ j := ⟨Over.homMk m.obj.hom.hom rfl⟩
    have hne : kl ≠ j := fun h ↦ m.property (ObjectProperty.FullSubcategory.ext
      (congrArg (fun x ↦ x.obj.left) h))
    exact ⟨⟨Over.mk kh, hne⟩, ⟨Iso.refl _⟩⟩

lemma latchLatchC_final (j : LatchingCategory d) : (latchLatchC deg hdeg j).Final := by
  have := latchLatchC_essSurj deg hdeg j
  have : (latchLatchC deg hdeg j).IsEquivalence := { }
  exact Functor.final_of_isRightAdjoint _

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hdeg in
/-- The restriction of a Reedy cofibrant diagram on `D ∖ {d}` to the latching
category of `d` is Reedy cofibrant. -/
lemma isReedyCofibrant_latchingToComplement (Y : Complement d ⥤ M)
    [∀ e, HasColimit (latchingDiagram Y e)] (hY : IsReedyCofibrant Y) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (latchingToComplement d ⋙ Y) j)),
      IsReedyCofibrant (latchingToComplement d ⋙ Y) := by
  have hC (j : LatchingCategory d) : HasColimit (latchingDiagram (latchingToComplement d ⋙ Y) j) := by
    have := latchLatchC_final deg hdeg j
    exact Functor.Final.comp_hasColimit (latchLatchC deg hdeg j)
      (G := latchingDiagram Y ((latchingToComplement d).obj j))
  refine ⟨hC, fun j ↦ ?_⟩
  have := latchLatchC_final deg hdeg j
  have : HasColimit (latchLatchC deg hdeg j ⋙
    latchingDiagram Y ((latchingToComplement d).obj j)) := hC j
  obtain ⟨hL, hi⟩ := hY ((latchingToComplement d).obj j)
  exact transfer_desc (latchLatchC deg hdeg j) (latchingDiagram Y ((latchingToComplement d).obj j))
    (latchingCocone Y ((latchingToComplement d).obj j)) hL hi

end LatchLatchC

section FromRestriction

variable {D : Type w} [SmallCategory D] {d : D}
  (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
  {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
include hd in
lemma hasColimit_latching_of_restrict (G : D ⥤ M) {e : D} (he : e ≠ d)
    [HasColimit (latchingDiagram ((complementProp d).ι ⋙ G) ⟨e, he⟩)] :
    HasColimit (latchingDiagram G e) := by
  have := latchingRestrict_final hd (⟨e, he⟩ : Complement d)
  have : HasColimit (latchingRestrict (⟨e, he⟩ : Complement d) ⋙ latchingDiagram G e) :=
    (inferInstance : HasColimit (latchingDiagram ((complementProp d).ι ⋙ G) ⟨e, he⟩))
  exact Functor.Final.hasColimit_of_comp (latchingRestrict (⟨e, he⟩ : Complement d))

include hd in
lemma reedy_at_of_restrict (G : D ⥤ M) {e : D} (he : e ≠ d)
    [HasColimit (latchingDiagram ((complementProp d).ι ⋙ G) ⟨e, he⟩)]
    [HasColimit (latchingDiagram G e)]
    (h : IsCofibrant (latchingObj ((complementProp d).ι ⋙ G) ⟨e, he⟩) ∧
      Cofibration (latchingMap ((complementProp d).ι ⋙ G) ⟨e, he⟩)) :
    IsCofibrant (latchingObj G e) ∧ Cofibration (latchingMap G e) := by
  have := latchingRestrict_final hd (⟨e, he⟩ : Complement d)
  have : HasColimit (latchingRestrict (⟨e, he⟩ : Complement d) ⋙ latchingDiagram G e) :=
    (inferInstance : HasColimit (latchingDiagram ((complementProp d).ι ⋙ G) ⟨e, he⟩))
  obtain ⟨_, h₁, h₂⟩ := transfer_desc_rev (latchingRestrict (⟨e, he⟩ : Complement d))
    (latchingDiagram G e) (latchingCocone G e) h.1 h.2
  exact ⟨h₁, h₂⟩

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
include hd in
lemma comparison_of_restrict {X G : D ⥤ M} (f : X ⟶ G) {e : D} (he : e ≠ d)
    [HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) ⟨e, he⟩)]
    [HasColimit (latchingDiagram ((complementProp d).ι ⋙ G) ⟨e, he⟩)]
    [HasColimit (latchingDiagram X e)] [HasColimit (latchingDiagram G e)]
    {P : M} {l : X.obj e ⟶ P} {r : latchingObj ((complementProp d).ι ⋙ G) ⟨e, he⟩ ⟶ P}
    {k : P ⟶ G.obj e}
    (hP : IsPushout (latchingMap ((complementProp d).ι ⋙ X) ⟨e, he⟩)
      (latchingObjMap (Functor.whiskerLeft (complementProp d).ι f) ⟨e, he⟩) l r)
    (hr : r ≫ k = latchingMap ((complementProp d).ι ⋙ G) ⟨e, he⟩) :
    ∃ r' : latchingObj G e ⟶ P, IsPushout (latchingMap X e) (latchingObjMap f e) l r' ∧
      r' ≫ k = latchingMap G e := by
  have := latchingRestrict_final hd (⟨e, he⟩ : Complement d)
  have : HasColimit (latchingRestrict (⟨e, he⟩ : Complement d) ⋙ latchingDiagram X e) :=
    (inferInstance : HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) ⟨e, he⟩))
  have : HasColimit (latchingRestrict (⟨e, he⟩ : Complement d) ⋙ latchingDiagram G e) :=
    (inferInstance : HasColimit (latchingDiagram ((complementProp d).ι ⋙ G) ⟨e, he⟩))
  exact transfer_comparison_rev (latchingRestrict (⟨e, he⟩ : Complement d)) (latchingNat f e)
    (latchingCocone X e) (latchingCocone G e) hP hr

end FromRestriction

section Step

variable {D : Type w} [SmallCategory D] [Finite D] [∀ x y : D, Finite (x ⟶ y)] (deg : D → ℕ)
  (hdeg : ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h) {d : D}
  (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
  {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include deg hdeg hd in
/-- One step of the Reedy factorization: extend a factorization on `D ∖ {d}` to
`D`. -/
lemma factorization_step {X Y : D ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) (f : X ⟶ Y) {Y'' : Complement d ⥤ M}
    [∀ e, HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e)]
    [∀ e, HasColimit (latchingDiagram Y'' e)]
    (f'' : (complementProp d).ι ⋙ X ⟶ Y'') (r'' : Y'' ⟶ (complementProp d).ι ⋙ Y)
    (hf'' : IsReedyCofibration f'') (hr'' : ∀ e, WeakEquivalence (r''.app e))
    (hfr : f'' ≫ r'' = Functor.whiskerLeft (complementProp d).ι f) :
    ∃ (Y' : D ⥤ M) (_ : ∀ e, HasColimit (latchingDiagram Y' e)) (f' : X ⟶ Y') (r : Y' ⟶ Y),
      IsReedyCofibration f' ∧ (∀ e, WeakEquivalence (r.app e)) ∧ f' ≫ r = f := by
  -- the latching object of the new diagram at `d`
  let K := latchingToComplement d ⋙ Y''
  obtain ⟨_, hK⟩ := isReedyCofibrant_latchingToComplement deg hdeg Y'' hf''.2.1
  obtain ⟨_, hKc⟩ := colimit_cofibrant_of_deg (fun j : LatchingCategory d ↦ deg j.obj.left)
    (hdeg_latching deg hdeg d) K hK
  obtain ⟨hLX, hiX⟩ := hX d
  have : HasColimit (latchingToComplement d ⋙ (complementProp d).ι ⋙ X) :=
    (inferInstance : HasColimit (latchingDiagram X d))
  let φ : latchingObj X d ⟶ colimit K :=
    colimMap (Functor.whiskerLeft (latchingToComplement d) f'')
  have hφ (j : LatchingCategory d) : colimit.ι (latchingDiagram X d) j ≫ φ =
      f''.app ((latchingToComplement d).obj j) ≫ colimit.ι K j :=
    ι_colimMap (Functor.whiskerLeft (latchingToComplement d) f'') j
  have : HasPushout (latchingMap X d) φ := hasPushout _ _
  let cY : Cocone K :=
    { pt := Y.obj d
      ι :=
        { app := fun j ↦ r''.app ((latchingToComplement d).obj j) ≫ Y.map j.obj.hom
          naturality := fun j j' g ↦ by
            have h₁ := r''.naturality ((latchingToComplement d).map g)
            have h₂ : Y.map g.hom.left ≫ Y.map j'.obj.hom = Y.map j.obj.hom := by
              rw [← Y.map_comp, Over.w g.hom]
            exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Y.map j'.obj.hom) h₁).trans
              ((Category.assoc _ _ _).trans ((congrArg (r''.app _ ≫ ·) h₂).trans
                (Category.comp_id _).symm))) } }
  let q : pushout (latchingMap X d) φ ⟶ Y.obj d :=
    pushout.desc (f.app d) (colimit.desc K cY) (by
      apply colimit.hom_ext
      intro j
      rw [ι_latchingMap_assoc, ← Category.assoc, hφ]
      have e₁ : (f''.app ((latchingToComplement d).obj j) ≫ colimit.ι K j) ≫ colimit.desc K cY =
          f''.app _ ≫ r''.app ((latchingToComplement d).obj j) ≫ Y.map j.obj.hom :=
        (Category.assoc _ _ _).trans (congrArg (f''.app _ ≫ ·) (colimit.ι_desc cY j))
      have e₂ := congrArg (fun α ↦ α.app ((latchingToComplement d).obj j)) hfr
      exact (f.naturality j.obj.hom).trans ((congrArg (· ≫ Y.map j.obj.hom) e₂.symm).trans
        ((Category.assoc _ _ _).trans e₁.symm)))
  have hinr : Cofibration (pushout.inr (latchingMap X d) φ) :=
    cofibration_of_isPushout (IsPushout.of_hasPushout _ _)
  have : IsCofibrant (pushout (latchingMap X d) φ) := cofibrant_target (pushout.inr _ φ)
  obtain ⟨Z, h, rd, hh, hrd, hhr⟩ := factorization q
  let c : Cocone K := (colimit.cocone K).extend (pushout.inr _ φ ≫ h)
  have hfz (j : LatchingCategory d) : X.map j.obj.hom ≫ (pushout.inl _ φ ≫ h) =
      f''.app ((latchingToComplement d).obj j) ≫ c.ι.app j := by
    have e₁ := ι_latchingMap X d j
    refine (congrArg (· ≫ (pushout.inl _ φ ≫ h)) e₁.symm).trans ?_
    rw [Category.assoc, pushout.condition_assoc, ← Category.assoc, hφ]
    exact Category.assoc _ _ _
  let f' : X ⟶ extend hd Y'' c := extendLift hd Y'' c f'' (pushout.inl _ φ ≫ h) hfz
  have hrz (j : LatchingCategory d) :
      c.ι.app j ≫ rd = r''.app ((latchingToComplement d).obj j) ≫ Y.map j.obj.hom := by
    change (colimit.ι K j ≫ pushout.inr _ φ ≫ h) ≫ rd = _
    rw [Category.assoc, Category.assoc, hhr, pushout.inr_desc, colimit.ι_desc]
  let r : extend hd Y'' c ⟶ Y := extendDesc hd Y'' c r'' rd hrz
  have hcomp : f' ≫ r = f := by
    ext e
    by_cases he : e = d
    · subst e
      rw [NatTrans.comp_app, extendLift_app_self, extendDesc_app_self]
      exact (Category.assoc _ _ _).trans <| (Category.assoc (pushout.inl _ φ) h _).trans ((congrArg (pushout.inl _ φ ≫ ·)
        ((congrArg (h ≫ ·) (Iso.inv_hom_id_assoc (extendObjIsoSelf Y'' c) rd)).trans hhr)).trans
          (pushout.inl_desc _ _ _))
    · rw [NatTrans.comp_app, extendLift_app_ne _ _ _ _ _ _ he, extendDesc_app_ne _ _ _ _ _ _ he]
      exact (Category.assoc _ _ _).trans ((congrArg (f''.app _ ≫ ·)
        (Iso.inv_hom_id_assoc _ _)).trans (congrArg (fun α ↦ α.app (⟨e, he⟩ : Complement d)) hfr))
  have hrw (e : D) : WeakEquivalence (r.app e) := by
    by_cases he : e = d
    · subst e
      rw [extendDesc_app_self]
      have := weakEquivalence_of_isIso (extendObjIsoSelf Y'' c).hom
      exact ⟨(weakEquivalences M).comp_mem _ _ this.mem hrd.mem⟩
    · rw [extendDesc_app_ne _ _ _ _ _ _ he]
      have := weakEquivalence_of_isIso (extendObjIso Y'' c he).hom
      exact ⟨(weakEquivalences M).comp_mem _ _ this.mem (hr'' ⟨e, he⟩).mem⟩
  have hY'i (e : D) : HasColimit (latchingDiagram (extend hd Y'' c) e) := by
    by_cases he : e = d
    · rw [he]
      exact hasColimit_of_iso (extendLatchingIso hd Y'' c)
    · have : HasColimit (((latchingProp (⟨e, he⟩ : Complement d)).ι ⋙ Over.forget _) ⋙ Y'') :=
        (inferInstance : HasColimit (latchingDiagram Y'' ⟨e, he⟩))
      have : HasColimit (latchingDiagram ((complementProp d).ι ⋙ extend hd Y'' c) ⟨e, he⟩) :=
        hasColimit_of_iso (Functor.isoWhiskerLeft ((latchingProp _).ι ⋙ Over.forget _)
          (extendRestrictIso hd Y'' c))
      exact hasColimit_latching_of_restrict hd _ he
  refine ⟨extend hd Y'' c, hY'i, f', r, ?_, hrw, hcomp⟩
  -- the restriction of `f'` to `D ∖ {d}`
  have hg' : Functor.whiskerLeft (complementProp d).ι f' =
      f'' ≫ (extendRestrictIso hd Y'' c).inv := by
    ext ⟨e, he⟩
    exact extendLift_app_ne hd Y'' c f'' _ hfz he
  have : IsDirect (Complement d) := ⟨⟨_, hdeg_complement deg hdeg d⟩⟩
  obtain ⟨hR₁, hRiso⟩ := isReedyCofibration_of_isIso (extendRestrictIso hd Y'' c).inv hf''.2.1
  have hgR : IsReedyCofibration (Functor.whiskerLeft (complementProp d).ι f') := by
    rw [hg']
    exact IsReedyCofibration.comp hf'' hRiso
  -- the latching object of the extension at `d`
  let eL : latchingObj (extend hd Y'' c) d ≅ colimit K :=
    HasColimit.isoOfNatIso (extendLatchingIso hd Y'' c)
  have hZ : IsCofibrant Z := cofibrant_target h
  have hLY' : latchingMap (extend hd Y'' c) d =
      eL.hom ≫ pushout.inr _ φ ≫ h ≫ (extendObjIsoSelf Y'' c).inv := by
    apply colimit.hom_ext
    intro j
    have h₁ : extendMap hd Y'' c j.obj.hom =
        ((extendObjIso Y'' c j.property).hom ≫ c.ι.app ⟨Over.mk j.obj.hom, j.property⟩) ≫
          (extendObjIsoSelf Y'' c).inv :=
      (Iso.eq_comp_inv _).2 (extend_map_self hd Y'' c j.property j.obj.hom)
    have h₂ : colimit.ι (latchingDiagram (extend hd Y'' c) d) j ≫ eL.hom =
        (extendLatchingIso hd Y'' c).hom.app j ≫ colimit.ι K j :=
      HasColimit.ι_isoOfNatIso_hom _ _
    exact (ι_latchingMap _ _ j).trans (h₁.trans (((Category.assoc _ _ _).trans
      (congrArg ((extendObjIso Y'' c j.property).hom ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (colimit.ι K j ≫ ·) (Category.assoc _ _ _))))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (· ≫ (pushout.inr _ φ ≫ h ≫ (extendObjIsoSelf Y'' c).inv)) h₂.symm).trans
          (Category.assoc _ _ _)))))
  have hYd : IsCofibrant (latchingObj (extend hd Y'' c) d) ∧
      Cofibration (latchingMap (extend hd Y'' c) d) := by
    have : Cofibration eL.inv := cofibration_of_isIso _
    have hLc : IsCofibrant (latchingObj (extend hd Y'' c) d) := cofibrant_target eL.inv
    have heL : Cofibration eL.hom := cofibration_of_isIso _
    have : IsCofibrant c.pt := hZ
    have hinv : Cofibration (extendObjIsoSelf Y'' c).inv := cofibration_of_isIso _
    have : Cofibration (h ≫ (extendObjIsoSelf Y'' c).inv) :=
      ⟨(cofibrations M).comp_mem _ _ hh.mem hinv.mem⟩
    refine ⟨hLc, ?_⟩
    rw [hLY']
    exact ⟨(cofibrations M).comp_mem _ _ heL.mem ((cofibrations M).comp_mem _ _ hinr.mem this.mem)⟩
  have hY'R : IsReedyCofibrant (extend hd Y'' c) := fun e ↦ by
    by_cases he : e = d
    · subst e
      exact hYd
    · exact reedy_at_of_restrict hd _ he (hgR.2.1 ⟨e, he⟩)
  refine ⟨hX, hY'R, fun e ↦ ?_⟩
  by_cases he : e = d
  · subst e
    have hcomm : latchingObjMap f' d ≫ eL.hom = φ := by
      apply colimit.hom_ext
      intro j
      rw [ι_latchingObjMap_assoc, HasColimit.ι_isoOfNatIso_hom, hφ]
      have e₁ := extendLiftApp_ne Y'' c f'' (pushout.inl _ φ ≫ h) j.property
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ colimit.ι K j)
        ((congrArg (· ≫ (extendObjIso Y'' c j.property).hom) e₁).trans
          ((Category.assoc _ _ _).trans ((congrArg (f''.app _ ≫ ·)
            (Iso.inv_hom_id _)).trans (Category.comp_id _))))))
    have hP : IsPushout (latchingMap X d) (latchingObjMap f' d) (pushout.inl _ φ)
        (eL.hom ≫ pushout.inr _ φ) :=
      (IsPushout.of_hasPushout (latchingMap X d) φ).of_iso (Iso.refl _) (Iso.refl _) eL.symm
        (Iso.refl _) (by simp) (by simp [← hcomm]) (by simp) (by simp)
    have : IsCofibrant c.pt := hZ
    have hinv : Cofibration (extendObjIsoSelf Y'' c).inv := cofibration_of_isIso _
    refine ⟨_, _, _, h ≫ (extendObjIsoSelf Y'' c).inv, hP, ?_, ?_,
      ⟨(cofibrations M).comp_mem _ _ hh.mem hinv.mem⟩⟩
    · exact (Category.assoc _ _ _).symm.trans (extendLift_app_self hd Y'' c f'' _ hfz).symm
    · rw [hLY']
      exact Category.assoc _ _ _
  · obtain ⟨P, l, r', k, hP, hl, hr, hk⟩ := hgR.2.2 ⟨e, he⟩
    obtain ⟨r'', hP', hr''⟩ := comparison_of_restrict hd f' he hP hr
    exact ⟨P, l, r'', k, hP', hl, hr'', hk⟩

end Step

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayerLatching

/-!
# The factorization step at each new layer object

The local CF4 construction in the proof of Theorem 9.2.4(1)(a). A given
factorization on the old open subcategory determines compatible cocones,
factorizations, and relative cofibrations at each new object.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.ReedyLayer
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)
  (hmax : ∀ d, ¬ P d → ∀ e (f : d ⟶ e), ∃ h : d = e, f = eqToHom h)
  (d : Objects P) (deg : D → ℕ)
  (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hdeg in
/-- Factor at one of the new objects, retaining all compatibility equations
with the already constructed old factorization. Only CF5(1) is needed. -/
theorem exists_factorization_at_new_object
    (h5 : CoproductCofibrationAxiom.{w} M) {X Y : D ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X)
    (f : X ⟶ Y) (Z : P.FullSubcategory ⥤ M)
    [∀ e, HasColimit (latchingDiagram Z e)] (hZ : IsReedyCofibrant Z)
    (a : P.ι ⋙ X ⟶ Z) (r : Z ⟶ P.ι ⋙ Y) (har : a ≫ r = Functor.whiskerLeft P.ι f) :
    ∃ (_ : HasColimit (latchingToOld P hmax d ⋙ Z))
      (c : Cocone (latchingToOld P hmax d ⋙ Z)) (i : X.obj d.val ⟶ c.pt)
      (p : c.pt ⟶ Y.obj d.val),
      (∀ j : LatchingCategory d.val,
        X.map j.obj.hom ≫ i = a.app ((latchingToOld P hmax d).obj j) ≫ c.ι.app j) ∧
      (∀ j : LatchingCategory d.val,
        c.ι.app j ≫ p = r.app ((latchingToOld P hmax d).obj j) ≫ Y.map j.obj.hom) ∧
      i ≫ p = f.app d.val ∧ WeakEquivalence p ∧
      ∃ (Q : M) (l : X.obj d.val ⟶ Q)
        (t : colimit (latchingToOld P hmax d ⋙ Z) ⟶ Q) (k : Q ⟶ c.pt),
        IsPushout (latchingMap X d.val)
          (colimMap (Functor.whiskerLeft (latchingToOld P hmax d) a)) l t ∧
        l ≫ k = i ∧ t ≫ k = colimit.desc _ c ∧ Cofibration k := by
  obtain ⟨hLZ, hLC⟩ := colimit_latchingToOld P hmax d deg hdeg h5 Z hZ
  let K := latchingToOld P hmax d ⋙ Z
  have : HasColimit (latchingToOld P hmax d ⋙ P.ι ⋙ X) := inferInstanceAs
    (HasColimit (latchingDiagram X d.val))
  let cr : Cocone K :=
    { pt := Y.obj d.val
      ι :=
        { app := fun j ↦ r.app ((latchingToOld P hmax d).obj j) ≫ Y.map j.obj.hom
          naturality := fun j k g ↦ by
            dsimp
            erw [r.naturality_assoc, ← Y.map_comp, Over.w, Category.comp_id]
            rfl } }
  let φ := colimMap (Functor.whiskerLeft (latchingToOld P hmax d) a)
  have hw : latchingMap X d.val ≫ f.app d.val = φ ≫ colimit.desc K cr := by
    apply colimit.hom_ext
    intro j
    rw [ι_latchingMap_assoc, ι_colimMap_assoc, colimit.ι_desc]
    change X.map j.obj.hom ≫ f.app d.val =
      a.app ((latchingToOld P hmax d).obj j) ≫
        r.app ((latchingToOld P hmax d).obj j) ≫ Y.map j.obj.hom
    rw [← Category.assoc]
    rw [show a.app ((latchingToOld P hmax d).obj j) ≫
        r.app ((latchingToOld P hmax d).obj j) = f.app j.obj.left from
      congrArg (fun t ↦ t.app ((latchingToOld P hmax d).obj j)) har]
    exact f.naturality j.obj.hom
  obtain ⟨hLX, hiX⟩ := hX d.val
  have : HasPushout (latchingMap X d.val) φ := hasPushout _ _
  let sq := IsPushout.of_hasPushout (latchingMap X d.val) φ
  have := cofibration_of_isPushout sq
  have := cofibrant_target (pushout.inr (latchingMap X d.val) φ)
  let q := pushout.desc (f.app d.val) (colimit.desc K cr) hw
  obtain ⟨T, k, p, hk, hp, hkp⟩ := factorization q
  let c : Cocone K :=
    { pt := T
      ι :=
        { app := fun j ↦ colimit.ι K j ≫ pushout.inr (latchingMap X d.val) φ ≫ k
          naturality := fun j j' g ↦ by simp [← Category.assoc] } }
  refine ⟨hLZ, c, pushout.inl _ _ ≫ k, p, ?_, ?_, ?_, hp, _, _, _, k, sq, rfl, ?_, hk⟩
  · intro j
    have h := congrArg (fun t ↦ colimit.ι (latchingDiagram X d.val) j ≫ t ≫ k) sq.w
    change colimit.ι (latchingDiagram X d.val) j ≫ (latchingMap X d.val ≫
      pushout.inl _ _) ≫ k = _ at h
    erw [Category.assoc, ι_latchingMap_assoc] at h
    simp only [Category.assoc] at h
    change X.map j.obj.hom ≫ pushout.inl _ _ ≫ k =
      colimit.ι (latchingToOld P hmax d ⋙ P.ι ⋙ X) j ≫ φ ≫ pushout.inr _ _ ≫ k at h
    erw [ι_colimMap_assoc] at h
    exact h
  · intro j
    change (colimit.ι K j ≫ pushout.inr _ _ ≫ k) ≫ p = _
    rw [Category.assoc, Category.assoc, hkp, pushout.inr_desc, colimit.ι_desc]
  · rw [Category.assoc, hkp, pushout.inl_desc]
  · apply colimit.hom_ext
    intro j
    rw [colimit.ι_desc]

end ABCCofibrations.ReedyLayer

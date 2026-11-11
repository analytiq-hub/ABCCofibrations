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

end ABCCofibrations

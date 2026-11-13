/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayerExtension
public import ABCCofibrations.ReedyBoundedMaps

/-! # Reedy diagrams on the predecessors of a whole new layer

The local latching comparison is an equivalence, so restricting an old
Reedy cofibrant diagram to the predecessors of a new object remains Reedy
cofibrant. This supplies the latching colimits for layer factorizations.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.ReedyLayer
variable {D : Type w} [SmallCategory D] (P : ObjectProperty D)
  (hmax : ∀ d, ¬ P d → ∀ e (f : d ⟶ e), ∃ h : d = e, f = eqToHom h)
  (d : Objects P) (deg : D → ℕ)
  (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)

/-- The latching category of `∂(D ↓ d)` at `j` maps to the latching category of
the old full subcategory at `j`. -/
def latchLatchOld (j : LatchingCategory d.val) :
    LatchingCategory j ⥤ LatchingCategory ((latchingToOld P hmax d).obj j) where
  obj k := ⟨Over.mk (Y := (latchingToOld P hmax d).obj k.obj.left) ⟨k.obj.hom.hom.left⟩,
    fun h ↦ latchLatch_ne deg hdeg j k (congrArg ObjectProperty.FullSubcategory.obj h)⟩
  map g := ⟨Over.homMk ⟨g.hom.left.hom.left⟩ (InducedCategory.hom_ext (by
    have := congrArg (fun φ ↦ φ.hom.left) (Over.w g.hom)
    exact this))⟩

instance (j : LatchingCategory d.val) : (latchLatchOld P hmax d deg hdeg j).Faithful where
  map_injective {_ _} g g' h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.hom.left.hom) h

instance (j : LatchingCategory d.val) : (latchLatchOld P hmax d deg hdeg j).Full where
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

lemma latchLatchOld_essSurj (j : LatchingCategory d.val) :
    (latchLatchOld P hmax d deg hdeg j).EssSurj where
  mem_essImage m := by
    let kl : LatchingCategory d.val := ⟨Over.mk (m.obj.hom.hom ≫ j.obj.hom),
      fun h ↦ d.property (Eq.mp (congrArg P h) m.obj.left.property)⟩
    let kh : kl ⟶ j := ⟨Over.homMk m.obj.hom.hom rfl⟩
    have hne : kl ≠ j := fun h ↦ m.property (ObjectProperty.FullSubcategory.ext
      (congrArg (fun x ↦ x.obj.left) h))
    exact ⟨⟨Over.mk kh, hne⟩, ⟨Iso.refl _⟩⟩

lemma latchLatchOld_final (j : LatchingCategory d.val) :
    (latchLatchOld P hmax d deg hdeg j).Final := by
  have := latchLatchOld_essSurj P hmax d deg hdeg j
  have : (latchLatchOld P hmax d deg hdeg j).IsEquivalence := { }
  exact Functor.final_of_isRightAdjoint _

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hdeg in
/-- The restriction of a Reedy cofibrant diagram on the old full subcategory to the latching
category of `d` is Reedy cofibrant. -/
lemma isReedyCofibrant_latchingToOld (Y : P.FullSubcategory ⥤ M)
    [∀ e, HasColimit (latchingDiagram Y e)] (hY : IsReedyCofibrant Y) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (latchingToOld P hmax d ⋙ Y) j)),
      IsReedyCofibrant (latchingToOld P hmax d ⋙ Y) := by
  have hC (j : LatchingCategory d.val) :
      HasColimit (latchingDiagram (latchingToOld P hmax d ⋙ Y) j) := by
    have := latchLatchOld_final P hmax d deg hdeg j
    exact Functor.Final.comp_hasColimit (latchLatchOld P hmax d deg hdeg j)
      (G := latchingDiagram Y ((latchingToOld P hmax d).obj j))
  refine ⟨hC, fun j ↦ ?_⟩
  have := latchLatchOld_final P hmax d deg hdeg j
  have : HasColimit (latchLatchOld P hmax d deg hdeg j ⋙
    latchingDiagram Y ((latchingToOld P hmax d).obj j)) := hC j
  obtain ⟨hL, hi⟩ := hY ((latchingToOld P hmax d).obj j)
  exact transfer_desc (latchLatchOld P hmax d deg hdeg j)
    (latchingDiagram Y ((latchingToOld P hmax d).obj j))
    (latchingCocone Y ((latchingToOld P hmax d).obj j)) hL hi

include hdeg in
/-- Restriction to the predecessors of a new object also preserves Reedy
cofibrations, using the same final local comparisons. -/
lemma isReedyCofibration_latchingToOld {X Y : P.FullSubcategory ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (latchingToOld P hmax d ⋙ X) j))
      (_ : ∀ j, HasColimit (latchingDiagram (latchingToOld P hmax d ⋙ Y) j)),
      IsReedyCofibration (Functor.whiskerLeft (latchingToOld P hmax d) f) := by
  obtain ⟨hX, hRX⟩ := isReedyCofibrant_latchingToOld P hmax d deg hdeg X hf.1
  obtain ⟨hY, hRY⟩ := isReedyCofibrant_latchingToOld P hmax d deg hdeg Y hf.2.1
  refine ⟨hX, hY, hRX, hRY, fun j ↦ ?_⟩
  have := latchLatchOld_final P hmax d deg hdeg j
  have : HasColimit (latchLatchOld P hmax d deg hdeg j ⋙
      latchingDiagram X ((latchingToOld P hmax d).obj j)) := hX j
  have : HasColimit (latchLatchOld P hmax d deg hdeg j ⋙
      latchingDiagram Y ((latchingToOld P hmax d).obj j)) := hY j
  obtain ⟨Q, l, r, k, hQ, hl, hr, hc⟩ := hf.2.2 ((latchingToOld P hmax d).obj j)
  obtain ⟨r', hQ', hr'⟩ := transfer_comparison (latchLatchOld P hmax d deg hdeg j)
    (latchingNat f ((latchingToOld P hmax d).obj j))
    (latchingCocone X ((latchingToOld P hmax d).obj j))
    (latchingCocone Y ((latchingToOld P hmax d).obj j)) hQ hr
  exact ⟨Q, l, r', k, hQ', hl, hr', hc⟩

include hdeg in
/-- The new latching object exists and is cofibrant. Only CF5(1) is needed:
its predecessor degrees are bounded even if the old category is unbounded. -/
theorem colimit_latchingToOld
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} M)
    (Y : P.FullSubcategory ⥤ M) [∀ e, HasColimit (latchingDiagram Y e)]
    (hY : IsReedyCofibrant Y) :
    ∃ (_ : HasColimit (latchingToOld P hmax d ⋙ Y)),
      IsCofibrant (colimit (latchingToOld P hmax d ⋙ Y)) := by
  obtain ⟨_, hR⟩ := isReedyCofibrant_latchingToOld P hmax d deg hdeg Y hY
  exact reedyCofibrant_colimit_bounded h5 (deg d.val) (LatchingCategory d.val)
    (fun j ↦ deg j.obj.left) (hdeg_latching deg hdeg d.val)
    (deg_latching_lt deg hdeg d.val) _ hR

include hdeg in
/-- A Reedy cofibration of old diagrams induces a cofibration of the new
latching objects, using CF5(1) without CF6. -/
theorem cofibration_colimMap_latchingToOld
    (h5 : ABCPrecofibrationCategory.CoproductCofibrationAxiom.{w} M)
    {X Y : P.FullSubcategory ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : HasColimit (latchingToOld P hmax d ⋙ X))
      (_ : HasColimit (latchingToOld P hmax d ⋙ Y)),
      Cofibration (colimMap (Functor.whiskerLeft (latchingToOld P hmax d) f)) := by
  obtain ⟨_, _, hR⟩ := isReedyCofibration_latchingToOld P hmax d deg hdeg hf
  exact reedyCofibration_colimMap_bounded h5 (deg d.val) (LatchingCategory d.val)
    (fun j ↦ deg j.obj.left) (hdeg_latching deg hdeg d.val)
    (deg_latching_lt deg hdeg d.val) _ _ _ hR

end ABCCofibrations.ReedyLayer

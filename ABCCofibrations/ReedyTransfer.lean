/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyFinite

/-!
# Transferring latching data along final functors

If the latching diagram of a restricted diagram is `F ⋙ K` for a final `F`, its
latching object and map agree with those of `K` up to the isomorphism
`colimit.pre K F`. These lemmas transfer Reedy cofibrancy and Reedy cofibrations
to the restriction of a diagram to `D ∖ {d}`.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

open ABCPrecofibrationCategory

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]
  {J J' : Type*} [Category J] [Category J'] (F : J' ⥤ J) [F.Final]

/-- Cofibrancy and the cofibration property of the induced map transfer along a
final functor. -/
lemma transfer_desc (K : J ⥤ M) [HasColimit K] [HasColimit (F ⋙ K)] (c : Cocone K)
    (hK : IsCofibrant (colimit K)) (hc : Cofibration (colimit.desc K c)) :
    IsCofibrant (colimit (F ⋙ K)) ∧ Cofibration (colimit.desc (F ⋙ K) (c.whisker F)) := by
  have : IsIso (colimit.pre K F) := inferInstance
  have : Cofibration (inv (colimit.pre K F)) := cofibration_of_isIso _
  have hK' : IsCofibrant (colimit (F ⋙ K)) := cofibrant_target (inv (colimit.pre K F))
  have : Cofibration (colimit.pre K F) := cofibration_of_isIso _
  refine ⟨hK', ?_⟩
  rw [← colimit.pre_desc]
  infer_instance

/-- A cofibration of colimit maps can be detected after restriction along a final functor. -/
lemma cofibration_colimMap_of_final {K K' : J ⥤ M} [HasColimit K] [HasColimit K']
    [HasColimit (F ⋙ K)] [HasColimit (F ⋙ K')] (α : K ⟶ K')
    (hK : IsCofibrant (colimit K))
    (hα : Cofibration (colimMap (Functor.whiskerLeft F α))) : Cofibration (colimMap α) := by
  have := cofibration_of_isIso (inv (colimit.pre K F))
  have := cofibrant_target (inv (colimit.pre K F))
  have := cofibrant_target (colimMap (Functor.whiskerLeft F α))
  have := cofibration_of_isIso (colimit.pre K' F)
  rw [colimMap_eq_inv_pre_comp F α]
  infer_instance

/-- A weak equivalence of colimit maps can be detected after final restriction. -/
lemma weakEquivalence_colimMap_of_final {K K' : J ⥤ M} [HasColimit K] [HasColimit K']
    [HasColimit (F ⋙ K)] [HasColimit (F ⋙ K')] (α : K ⟶ K')
    (hα : WeakEquivalence (colimMap (Functor.whiskerLeft F α))) :
    WeakEquivalence (colimMap α) := by
  have := weakEquivalence_of_isIso (inv (colimit.pre K F))
  have := weakEquivalence_of_isIso (colimit.pre K' F)
  rw [colimMap_eq_inv_pre_comp F α]
  infer_instance

/-- The restriction of a Reedy cofibration to `D ∖ {d}` is a Reedy cofibration,
when no non-identity map leaves `d`. -/
lemma isReedyCofibration_restrict {D : Type u₁} [Category.{v₁} D] {d : D}
    (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h) {X Y : D ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e))
      (_ : ∀ e, HasColimit (latchingDiagram ((complementProp d).ι ⋙ Y) e)),
      IsReedyCofibration (Functor.whiskerLeft (complementProp d).ι f) := by
  obtain ⟨hX₁, hX'⟩ := isReedyCofibrant_restrict hd X hf.1
  obtain ⟨hY₁, hY'⟩ := isReedyCofibrant_restrict hd Y hf.2.1
  refine ⟨hX₁, hY₁, hX', hY', fun e ↦ ?_⟩
  have := latchingRestrict_final hd e
  have : HasColimit (latchingRestrict e ⋙ latchingDiagram X e.obj) := hX₁ e
  have : HasColimit (latchingRestrict e ⋙ latchingDiagram Y e.obj) := hY₁ e
  obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hf.2.2 e.obj
  obtain ⟨r', hP', hr'⟩ := transfer_comparison (latchingRestrict e) (latchingNat f e.obj)
    (latchingCocone X e.obj) (latchingCocone Y e.obj) hP hr
  exact ⟨P, l, r', c, hP', hl, hr', hc⟩

section LatchLatch

variable {D : Type u₁} [Category.{v₁} D] (deg : D → ℕ)
  (hdeg : ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h) {d : D}

include hdeg in
/-- In a direct category, an endomorphism after transport along an equality is the
identity: a map `x ⟶ y` with `x = y` is `eqToHom`. -/
lemma eq_eqToHom_of_eq {x y : D} (f : x ⟶ y) (h : x = y) : f = eqToHom h := by
  rcases hdeg f with hlt | ⟨_, hf⟩
  · subst h
    exact absurd hlt (lt_irrefl _)
  · exact hf

include hdeg in
lemma latchLatch_ne (j : LatchingCategory d) (k : LatchingCategory j) :
    k.obj.left.obj.left ≠ j.obj.left := by
  intro h
  apply k.property
  have hφ := eq_eqToHom_of_eq deg hdeg k.obj.hom.hom.left h
  have hk : k.obj.left = j := by
    apply ObjectProperty.FullSubcategory.ext
    apply CostructuredArrow.obj_ext _ _ h
    have := Over.w k.obj.hom.hom
    rw [hφ] at this
    exact this
  exact hk

/-- The latching category of `∂(D ↓ d)` at `j = (e, e ⟶ d)` maps to the latching
category of `D` at `e` (the paper's identification (9.1.2)). -/
def latchLatch (j : LatchingCategory d) : LatchingCategory j ⥤ LatchingCategory j.obj.left where
  obj k := ⟨Over.mk (Y := k.obj.left.obj.left) k.obj.hom.hom.left, latchLatch_ne deg hdeg j k⟩
  map g := ⟨Over.homMk g.hom.left.hom.left (by
    have := congrArg (fun φ ↦ φ.hom.left) (Over.w g.hom)
    exact this)⟩

instance (j : LatchingCategory d) : (latchLatch deg hdeg j).Faithful where
  map_injective {_ _} g g' h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.hom.left) h

instance (j : LatchingCategory d) : (latchLatch deg hdeg j).Full where
  map_surjective {k k'} g := by
    have hk := Over.w k.obj.hom.hom
    have hk' := Over.w k'.obj.hom.hom
    have hg := Over.w g.hom
    refine ⟨⟨Over.homMk ⟨Over.homMk g.hom.left ?_⟩ ?_⟩, rfl⟩
    · exact (congrArg (g.hom.left ≫ ·) hk').symm.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ j.obj.hom) hg).trans hk))
    · apply InducedCategory.hom_ext
      apply Over.OverMorphism.ext
      exact hg

include hdeg in
lemma latchLatch_essSurj (j : LatchingCategory d) : (latchLatch deg hdeg j).EssSurj where
  mem_essImage m := by
    have h₁ : deg m.obj.left < deg j.obj.left := by
      rcases hdeg m.obj.hom with h | ⟨h, -⟩
      · exact h
      · exact absurd h m.property
    have h₂ : deg j.obj.left < deg d := by
      rcases hdeg j.obj.hom with h | ⟨h, -⟩
      · exact h
      · exact absurd h j.property
    have hz : m.obj.left ≠ d := fun h ↦ by rw [h] at h₁; omega
    let kl : LatchingCategory d := ⟨Over.mk (m.obj.hom ≫ j.obj.hom), hz⟩
    let kh : kl ⟶ j := ⟨Over.homMk m.obj.hom rfl⟩
    have hne : kl ≠ j := fun h ↦ m.property (congrArg (fun x ↦ x.obj.left) h)
    exact ⟨⟨Over.mk kh, hne⟩, ⟨Iso.refl _⟩⟩

include hdeg in
lemma latchLatch_final (j : LatchingCategory d) : (latchLatch deg hdeg j).Final := by
  have := latchLatch_essSurj deg hdeg j
  have : (latchLatch deg hdeg j).IsEquivalence := { }
  exact Functor.final_of_isRightAdjoint _

variable (X : D ⥤ M)

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
include hdeg in
lemma hasColimit_latchLatch (j : LatchingCategory d) [HasColimit (latchingDiagram X j.obj.left)] :
    HasColimit (latchingDiagram (latchingDiagram X d) j) := by
  have := latchLatch_final deg hdeg j
  exact Functor.Final.comp_hasColimit (latchLatch deg hdeg j)
    (G := latchingDiagram X j.obj.left)

include hdeg in
/-- The restriction of a Reedy cofibrant diagram to a latching category is Reedy
cofibrant. -/
lemma isReedyCofibrant_latching [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (latchingDiagram X d) j)),
      IsReedyCofibrant (latchingDiagram X d) := by
  have hC (j : LatchingCategory d) := hasColimit_latchLatch deg hdeg X j
  refine ⟨hC, fun j ↦ ?_⟩
  have := latchLatch_final deg hdeg j
  have : HasColimit (latchLatch deg hdeg j ⋙ latchingDiagram X j.obj.left) := hC j
  obtain ⟨hL, hi⟩ := hX j.obj.left
  exact transfer_desc (latchLatch deg hdeg j) (latchingDiagram X j.obj.left)
    (latchingCocone X j.obj.left) hL hi

include hdeg in
/-- The restriction of a Reedy cofibration to a latching category is a Reedy
cofibration. -/
lemma isReedyCofibration_latching {X Y : D ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (latchingDiagram X d) j))
      (_ : ∀ j, HasColimit (latchingDiagram (latchingDiagram Y d) j)),
      IsReedyCofibration (latchingNat f d) := by
  obtain ⟨hX₁, hX'⟩ := isReedyCofibrant_latching deg hdeg X (d := d) hf.1
  obtain ⟨hY₁, hY'⟩ := isReedyCofibrant_latching deg hdeg Y (d := d) hf.2.1
  refine ⟨hX₁, hY₁, hX', hY', fun j ↦ ?_⟩
  have := latchLatch_final deg hdeg j
  have : HasColimit (latchLatch deg hdeg j ⋙ latchingDiagram X j.obj.left) := hX₁ j
  have : HasColimit (latchLatch deg hdeg j ⋙ latchingDiagram Y j.obj.left) := hY₁ j
  obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hf.2.2 j.obj.left
  obtain ⟨r', hP', hr'⟩ := transfer_comparison (latchLatch deg hdeg j)
    (latchingNat f j.obj.left) (latchingCocone X j.obj.left) (latchingCocone Y j.obj.left) hP hr
  exact ⟨P, l, r', c, hP', hl, hr', hc⟩

end LatchLatch

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBasic
public import ABCCofibrations.ColimitComparison

/-!
# Restriction to open full subcategories

An open full subcategory contains the source of every arrow whose target it
contains. Its latching categories agree, up to equivalence, with those in the
ambient category. This is the restriction step used in Theorem 9.4.1.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D : Type u₁} [Category.{v₁} D]

/-- A full subcategory of a direct category is direct. -/
instance isDirect_fullSubcategory (P : ObjectProperty D) [IsDirect D] :
    IsDirect P.FullSubcategory where
  exists_deg := by
    obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
    refine ⟨fun e ↦ deg e.obj, fun {a b} f ↦ ?_⟩
    rcases hdeg f.hom with h | ⟨h, hf⟩
    · exact Or.inl h
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      dsimp at h
      subst h
      exact Or.inr ⟨rfl, InducedCategory.hom_ext (by simpa using hf)⟩

/-- The objectwise form of an open full embedding: membership is closed
under taking sources of arrows. -/
def IsOpenDiagramSubcategory (P : ObjectProperty D) : Prop :=
  ∀ {a b : D}, (a ⟶ b) → P b → P a

namespace OpenDiagramSubcategory

variable (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P)

/-- The latching-category comparison for a full subcategory. -/
def latchingInclusion (e : P.FullSubcategory) : LatchingCategory e ⥤ LatchingCategory e.obj where
  obj j := ⟨Over.mk (Y := j.obj.left.obj) j.obj.hom.hom,
    fun h ↦ j.property (ObjectProperty.FullSubcategory.ext h)⟩
  map g := ⟨Over.homMk g.hom.left.hom (congrArg InducedCategory.Hom.hom (Over.w g.hom))⟩

instance (e : P.FullSubcategory) : (latchingInclusion P e).Faithful where
  map_injective {_ _} g g' h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply InducedCategory.hom_ext
    exact congrArg (fun k ↦ k.hom.left) h

instance (e : P.FullSubcategory) : (latchingInclusion P e).Full where
  map_surjective {_ _} g :=
    ⟨⟨Over.homMk ⟨g.hom.left⟩ (InducedCategory.hom_ext (Over.w g.hom))⟩, rfl⟩

include hP in
lemma latchingInclusion_essSurj (e : P.FullSubcategory) :
    (latchingInclusion P e).EssSurj where
  mem_essImage k :=
    ⟨⟨Over.mk (Y := (⟨k.obj.left, hP k.obj.hom e.property⟩ : P.FullSubcategory)) ⟨k.obj.hom⟩,
      fun h ↦ k.property (congrArg ObjectProperty.FullSubcategory.obj h)⟩, ⟨Iso.refl _⟩⟩

include hP in
lemma latchingInclusion_final (e : P.FullSubcategory) : (latchingInclusion P e).Final := by
  have := latchingInclusion_essSurj P hP e
  have : (latchingInclusion P e).IsEquivalence := { }
  exact Functor.final_of_isRightAdjoint _

variable {M : Type u₂} [Category.{v₂} M] (X : D ⥤ M)

include hP in
lemma hasColimit_latching (e : P.FullSubcategory) [HasColimit (latchingDiagram X e.obj)] :
    HasColimit (latchingDiagram (P.ι ⋙ X) e) := by
  have := latchingInclusion_final P hP e
  exact Functor.Final.comp_hasColimit (latchingInclusion P e) (G := latchingDiagram X e.obj)

lemma latchingMap_restrict (e : P.FullSubcategory) [HasColimit (latchingDiagram X e.obj)]
    [h : HasColimit (latchingInclusion P e ⋙ latchingDiagram X e.obj)] :
    @latchingMap _ _ _ _ (P.ι ⋙ X) e h =
      colimit.pre (latchingDiagram X e.obj) (latchingInclusion P e) ≫ latchingMap X e.obj := by
  let : HasColimit (latchingDiagram (P.ι ⋙ X) e) := h
  apply colimit.hom_ext
  intro j
  have h₁ := colimit.ι_desc (latchingCocone (P.ι ⋙ X) e) j
  have h₂ := colimit.ι_pre_assoc (latchingDiagram X e.obj) (latchingInclusion P e) j
    (latchingMap X e.obj)
  rw [ι_latchingMap] at h₂
  exact h₁.trans h₂.symm

variable [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

include hP in
/-- Restriction to an open full subcategory preserves Reedy cofibrancy. -/
theorem isReedyCofibrant [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (P.ι ⋙ X) e)), IsReedyCofibrant (P.ι ⋙ X) := by
  have hC (e : P.FullSubcategory) := hasColimit_latching P hP X e
  refine ⟨hC, fun e ↦ ?_⟩
  have := latchingInclusion_final P hP e
  have hh : HasColimit (latchingInclusion P e ⋙ latchingDiagram X e.obj) := hC e
  let φ := colimit.pre (latchingDiagram X e.obj) (latchingInclusion P e)
  have : IsIso φ := Functor.Final.colimit_pre_isIso _
  obtain ⟨hL, hi⟩ := hX e.obj
  have := cofibration_of_isIso (inv φ)
  have : IsCofibrant (colimit (latchingInclusion P e ⋙ latchingDiagram X e.obj)) :=
    cofibrant_target (inv φ)
  refine ⟨this, ?_⟩
  have := cofibration_of_isIso φ
  change Cofibration (@latchingMap _ _ _ _ (P.ι ⋙ X) e hh)
  rw [latchingMap_restrict]
  exact (inferInstance : Cofibration (φ ≫ latchingMap X e.obj))

include hP in
/-- Restriction to an open full subcategory preserves Reedy cofibrations. -/
theorem isReedyCofibration {X Y : D ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (P.ι ⋙ X) e))
      (_ : ∀ e, HasColimit (latchingDiagram (P.ι ⋙ Y) e)),
      IsReedyCofibration (Functor.whiskerLeft P.ι f) := by
  obtain ⟨_, hX⟩ := isReedyCofibrant P hP X hf.1
  obtain ⟨_, hY⟩ := isReedyCofibrant P hP Y hf.2.1
  refine ⟨inferInstance, inferInstance, hX, hY, fun e ↦ ?_⟩
  have := latchingInclusion_final P hP e
  obtain ⟨Q, l, r, c, hQ, hl, hr, hc⟩ := hf.2.2 e.obj
  obtain ⟨r', hQ', hr'⟩ := transfer_comparison (latchingInclusion P e) (latchingNat f e.obj)
    (latchingCocone X e.obj) (latchingCocone Y e.obj) hQ hr
  exact ⟨Q, l, r', c, hQ', hl, hr', hc⟩

end OpenDiagramSubcategory
end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyOpen
public import ABCCofibrations.ReedyTransfer

/-! # Restriction along fully faithful open functors

An injective-on-objects fully faithful functor whose image is closed under
predecessors induces equivalences of latching categories. This includes
the changes of presentation between nested degree truncations.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w z v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.OpenFunctor
variable {E : Type z} [SmallCategory E] {D : Type w} [SmallCategory D]
  (F : E ⥤ D) (hinj : Function.Injective F.obj) [F.Full] [F.Faithful]
  (hopen : ∀ {a : D} (e : E), (a ⟶ F.obj e) → ∃ e', F.obj e' = a)

/-- The local latching comparison for an open functor. -/
def latching (e : E) : LatchingCategory e ⥤ LatchingCategory (F.obj e) where
  obj j := ⟨Over.mk (F.map j.obj.hom), fun h ↦ j.property (hinj h)⟩
  map g := ⟨Over.homMk (F.map g.hom.left) (by
    change F.map g.hom.left ≫ F.map _ = F.map _
    rw [← F.map_comp, Over.w])⟩
  map_id j := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    exact F.map_id _
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    exact F.map_comp _ _

instance (e : E) : (latching F hinj e).Faithful where
  map_injective {_ _} f g h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply F.map_injective
    exact congrArg (fun k ↦ k.hom.left) h

instance (e : E) : (latching F hinj e).Full where
  map_surjective {a b} f := by
    refine ⟨⟨Over.homMk (F.preimage f.hom.left) ?_⟩, ?_⟩
    · apply F.map_injective
      rw [F.map_comp, F.map_preimage]
      exact Over.w f.hom
    · apply InducedCategory.hom_ext
      apply Over.OverMorphism.ext
      exact F.map_preimage _

omit [F.Faithful] in
include hopen in
lemma latching_essSurj (e : E) : (latching F hinj e).EssSurj where
  mem_essImage j := by
    obtain ⟨a, ha⟩ := hopen e j.obj.hom
    let f : a ⟶ e := F.preimage (eqToHom ha ≫ j.obj.hom)
    have hne : a ≠ e := fun h ↦ j.property (ha.symm.trans (congrArg F.obj h))
    refine ⟨⟨Over.mk f, hne⟩, ⟨(latchingProp (F.obj e)).isoMk (Over.isoMk (eqToIso ha) ?_)⟩⟩
    change eqToHom ha ≫ j.obj.hom = F.map (F.preimage (eqToHom ha ≫ j.obj.hom))
    exact (F.map_preimage _).symm

include hopen in
lemma latching_final (e : E) : (latching F hinj e).Final := by
  have := latching_essSurj F hinj hopen e
  have : (latching F hinj e).IsEquivalence := { }
  exact Functor.final_of_isRightAdjoint _

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hinj hopen in
/-- Open fully faithful restriction preserves Reedy cofibrancy. -/
theorem isReedyCofibrant (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (F ⋙ X) e)), IsReedyCofibrant (F ⋙ X) := by
  have hCol (e : E) : HasColimit (latchingDiagram (F ⋙ X) e) := by
    have := latching_final F hinj hopen e
    exact Functor.Final.comp_hasColimit (latching F hinj e) (G := latchingDiagram X (F.obj e))
  refine ⟨hCol, fun e ↦ ?_⟩
  have := latching_final F hinj hopen e
  have : HasColimit (latching F hinj e ⋙ latchingDiagram X (F.obj e)) := hCol e
  exact transfer_desc (latching F hinj e) (latchingDiagram X (F.obj e))
    (latchingCocone X (F.obj e)) (hX (F.obj e)).1 (hX (F.obj e)).2

include hinj hopen in
/-- Open fully faithful restriction preserves Reedy cofibrations. -/
theorem isReedyCofibration {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (F ⋙ X) e))
      (_ : ∀ e, HasColimit (latchingDiagram (F ⋙ Y) e)),
      IsReedyCofibration (Functor.whiskerLeft F f) := by
  obtain ⟨hX, hRX⟩ := isReedyCofibrant F hinj hopen X hf.1
  obtain ⟨hY, hRY⟩ := isReedyCofibrant F hinj hopen Y hf.2.1
  refine ⟨hX, hY, hRX, hRY, fun e ↦ ?_⟩
  have := latching_final F hinj hopen e
  have : HasColimit (latching F hinj e ⋙ latchingDiagram X (F.obj e)) := hX e
  have : HasColimit (latching F hinj e ⋙ latchingDiagram Y (F.obj e)) := hY e
  obtain ⟨Q, l, r, k, hQ, hl, hr, hk⟩ := hf.2.2 (F.obj e)
  obtain ⟨r', hQ', hr'⟩ := transfer_comparison (latching F hinj e)
    (latchingNat f (F.obj e)) (latchingCocone X (F.obj e)) (latchingCocone Y (F.obj e)) hQ hr
  exact ⟨Q, l, r', k, hQ', hl, hr', hk⟩

end ABCCofibrations.OpenFunctor

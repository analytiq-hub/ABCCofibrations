/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyPointwise
public import ABCCofibrations.KanMapComparison

/-!
# Relative colimits of Reedy cofibrant diagrams (Theorem 9.4.2(1))

For a functor `u : D₁ ⥤ D₂` with `D₁` finite direct, the relative colimit
`colim^u X` is computed pointwise by colimits over the comma categories
`(u ↓ d₂)` (Lemma 8.2.1). Assuming also finite hom-sets in `D₂`, these comma
categories have finitely many objects; finite hom-sets in `D₁` give finite
hom-sets in them. They are direct,
and the restriction of a Reedy cofibrant diagram to them is Reedy cofibrant (their
latching categories are those of `D₁`), so Theorem 9.3.5 applies.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

open ABCPrecofibrationCategory

section Comma

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] (u : D₁ ⥤ D₂) (deg : D₁ → ℕ)
  (hdeg : ∀ {x y : D₁} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h) {d₂ : D₂}

include hdeg in
/-- Degrees on the comma category `(u ↓ d₂)`. -/
lemma hdeg_comma {j j' : CostructuredArrow u d₂} (g : j ⟶ j') :
    deg j.left < deg j'.left ∨ ∃ h : j = j', g = eqToHom h := by
  rcases hdeg g.left with h | ⟨h, hg⟩
  · exact Or.inl h
  · right
    obtain ⟨l, ⟨⟨⟩⟩, a⟩ := j
    obtain ⟨l', ⟨⟨⟩⟩, a'⟩ := j'
    revert hg
    obtain rfl : l = l' := h
    intro hg
    have hw := CostructuredArrow.w g
    dsimp at hg hw
    rw [hg, u.map_id, Category.id_comp] at hw
    change a' = a at hw
    subst hw
    refine ⟨rfl, ?_⟩
    apply CostructuredArrow.hom_ext
    simpa using hg

include hdeg in
lemma latchComma_ne (j : CostructuredArrow u d₂) (k : LatchingCategory j) :
    k.obj.left.left ≠ j.left := by
  intro h
  apply k.property
  have hφ := eq_eqToHom_of_eq deg hdeg k.obj.hom.left h
  apply CostructuredArrow.obj_ext _ _ h
  have := CostructuredArrow.w k.obj.hom
  rw [hφ] at this
  exact this

/-- The latching category of `(u ↓ d₂)` at `j` maps to the latching category of
`D₁` at `j.left`. -/
def latchComma (j : CostructuredArrow u d₂) : LatchingCategory j ⥤ LatchingCategory j.left where
  obj k := ⟨Over.mk (Y := k.obj.left.left) k.obj.hom.left, latchComma_ne u deg hdeg j k⟩
  map g := ⟨Over.homMk g.hom.left.left (by
    have := congrArg CommaMorphism.left (Over.w g.hom)
    exact this)⟩

instance (j : CostructuredArrow u d₂) : (latchComma u deg hdeg j).Faithful where
  map_injective {_ _} g g' h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply CostructuredArrow.hom_ext
    exact congrArg (fun k ↦ k.hom.left) h

instance (j : CostructuredArrow u d₂) : (latchComma u deg hdeg j).Full where
  map_surjective {k k'} g := by
    have hk := CostructuredArrow.w k.obj.hom
    have hk' := CostructuredArrow.w k'.obj.hom
    have hg := Over.w g.hom
    refine ⟨⟨Over.homMk (CostructuredArrow.homMk g.hom.left ?_) ?_⟩, rfl⟩
    · exact (congrArg (u.map g.hom.left ≫ ·) hk').symm.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ j.hom) ((u.map_comp _ _).symm.trans (congrArg u.map hg))).trans hk))
    · apply CostructuredArrow.hom_ext
      exact hg

lemma latchComma_essSurj (j : CostructuredArrow u d₂) : (latchComma u deg hdeg j).EssSurj where
  mem_essImage m := by
    let kl : CostructuredArrow u d₂ := CostructuredArrow.mk (u.map m.obj.hom ≫ j.hom)
    let kh : kl ⟶ j := CostructuredArrow.homMk m.obj.hom rfl
    have hne : kl ≠ j := fun h ↦ m.property (congrArg CostructuredArrow.left h |>.trans rfl)
    exact ⟨⟨Over.mk kh, hne⟩, ⟨Iso.refl _⟩⟩

lemma latchComma_final (j : CostructuredArrow u d₂) : (latchComma u deg hdeg j).Final := by
  have := latchComma_essSurj u deg hdeg j
  have : (latchComma u deg hdeg j).IsEquivalence := { }
  exact Functor.final_of_isRightAdjoint _

instance [Finite D₁] [∀ x y : D₂, Finite (x ⟶ y)] : Finite (CostructuredArrow u d₂) :=
  Finite.of_injective (fun j : CostructuredArrow u d₂ ↦ (⟨j.left, j.hom⟩ : Σ e : D₁, u.obj e ⟶ d₂))
    (by
      rintro ⟨l, ⟨⟨⟩⟩, g⟩ ⟨l', ⟨⟨⟩⟩, g'⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rfl)

instance [∀ x y : D₁, Finite (x ⟶ y)] (j j' : CostructuredArrow u d₂) : Finite (j ⟶ j') :=
  Finite.of_injective (fun g : j ⟶ j' ↦ g.left) (fun _ _ h ↦ CostructuredArrow.hom_ext _ _ h)

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hdeg in
/-- The restriction of a Reedy cofibrant diagram to `(u ↓ d₂)` is Reedy cofibrant. -/
lemma isReedyCofibrant_comma (X : D₁ ⥤ M) [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (CostructuredArrow.proj u d₂ ⋙ X) j)),
      IsReedyCofibrant (CostructuredArrow.proj u d₂ ⋙ X) := by
  have hC (j : CostructuredArrow u d₂) :
      HasColimit (latchingDiagram (CostructuredArrow.proj u d₂ ⋙ X) j) := by
    have := latchComma_final u deg hdeg j
    exact Functor.Final.comp_hasColimit (latchComma u deg hdeg j) (G := latchingDiagram X j.left)
  refine ⟨hC, fun j ↦ ?_⟩
  have := latchComma_final u deg hdeg j
  have : HasColimit (latchComma u deg hdeg j ⋙ latchingDiagram X j.left) := hC j
  obtain ⟨hL, hi⟩ := hX j.left
  exact transfer_desc (latchComma u deg hdeg j) (latchingDiagram X j.left)
    (latchingCocone X j.left) hL hi

include hdeg in
/-- The restriction of a Reedy cofibration to `(u ↓ d₂)` is a Reedy cofibration. -/
lemma isReedyCofibration_comma {X Y : D₁ ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : ∀ j, HasColimit (latchingDiagram (CostructuredArrow.proj u d₂ ⋙ X) j))
      (_ : ∀ j, HasColimit (latchingDiagram (CostructuredArrow.proj u d₂ ⋙ Y) j)),
      IsReedyCofibration (Functor.whiskerLeft (CostructuredArrow.proj u d₂) f) := by
  obtain ⟨hX₁, hX'⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d₂) hf.1
  obtain ⟨hY₁, hY'⟩ := isReedyCofibrant_comma u deg hdeg Y (d₂ := d₂) hf.2.1
  refine ⟨hX₁, hY₁, hX', hY', fun j ↦ ?_⟩
  have := latchComma_final u deg hdeg j
  have : HasColimit (latchComma u deg hdeg j ⋙ latchingDiagram X j.left) := hX₁ j
  have : HasColimit (latchComma u deg hdeg j ⋙ latchingDiagram Y j.left) := hY₁ j
  obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hf.2.2 j.left
  obtain ⟨r', hP', hr'⟩ := transfer_comparison (latchComma u deg hdeg j) (latchingNat f j.left)
    (latchingCocone X j.left) (latchingCocone Y j.left) hP hr
  exact ⟨P, l, r', c, hP', hl, hr', hc⟩

end Comma

section Main

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂] [Finite D₁]
  [∀ x y : D₁, Finite (x ⟶ y)] [∀ x y : D₂, Finite (x ⟶ y)] [IsDirect D₁] (u : D₁ ⥤ D₂)
  {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

omit [∀ x y : D₁, Finite (x ⟶ y)] in
/-- **Theorem 9.4.2(1)(a)**, for finite direct `D₁`. For a Reedy cofibrant
`X : D₁ ⥤ M`, the relative colimit `colim^u X` exists (pointwise) and is
pointwise cofibrant. -/
theorem reedyCofibrant_leftKanExtension (X : D₁ ⥤ M) [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X),
      ∀ d₂, IsCofibrant ((u.leftKanExtension X).obj d₂) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  have key (d₂ : D₂) : ∃ (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ X)),
      IsCofibrant (colimit (CostructuredArrow.proj u d₂ ⋙ X)) := by
    obtain ⟨_, h⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d₂) hX
    exact colimit_cofibrant_of_deg (fun j ↦ deg j.left) (hdeg_comma u deg hdeg) _ h
  have hK : u.HasPointwiseLeftKanExtension X := fun d₂ ↦ (key d₂).fst
  refine ⟨hK, fun d₂ ↦ ?_⟩
  have := (key d₂).snd
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit X d₂).inv
  exact cofibrant_target (u.leftKanExtensionObjIsoColimit X d₂).inv

/-- **Theorem 9.4.2(1)(b)** at the comma-colimit level, under this section's
finite-source and finite-hom assumptions. See `reedyCofibration_pointwiseLeftKanMap`
for the induced map between chosen Kan extensions. -/
theorem reedyCofibration_leftKanExtension {X Y : D₁ ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) (d₂ : D₂) :
    ∃ (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ X))
      (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ Y)),
      Cofibration (colimMap (Functor.whiskerLeft (CostructuredArrow.proj u d₂) f)) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  obtain ⟨_, _, h⟩ := isReedyCofibration_comma u deg hdeg (d₂ := d₂) hf
  have : IsDirect (CostructuredArrow u d₂) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  exact reedyCofibration_colimMap h

/-- **Theorem 9.4.2(1)(c)** at the comma-colimit level, under this section's
finite-source and finite-hom assumptions. See
`reedyCofibrant_pointwiseLeftKanMap_weakEquivalence` for the chosen Kan extensions. -/
theorem reedyCofibrant_leftKanExtension_weakEquivalence {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) (d₂ : D₂) :
    ∃ (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ X))
      (_ : HasColimit (CostructuredArrow.proj u d₂ ⋙ Y)),
      WeakEquivalence (colimMap (Functor.whiskerLeft (CostructuredArrow.proj u d₂) f)) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  obtain ⟨_, hX'⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d₂) hX
  obtain ⟨_, hY'⟩ := isReedyCofibrant_comma u deg hdeg Y (d₂ := d₂) hY
  have : IsDirect (CostructuredArrow u d₂) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  exact reedyCofibrant_colimMap_weakEquivalence hX' hY' _ (fun j ↦ hw j.left)

/-- Theorem 9.4.2(1)(b) for the morphism between the chosen pointwise left Kan
extensions, under the finite-source and finite-hom assumptions of this section. -/
theorem reedyCofibration_pointwiseLeftKanMap {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y),
      ∀ d₂, Cofibration ((pointwiseLeftKanMap u f).app d₂) := by
  obtain ⟨hKX, hX⟩ := reedyCofibrant_leftKanExtension u X hf.1
  obtain ⟨hKY, hY⟩ := reedyCofibrant_leftKanExtension u Y hf.2.1
  refine ⟨hKX, hKY, fun d₂ ↦ ?_⟩
  obtain ⟨_, _, hc⟩ := reedyCofibration_leftKanExtension u hf d₂
  rw [pointwiseLeftKanMap_app]
  have := hX d₂
  have := hY d₂
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit X d₂).hom
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit Y d₂).hom
  have := cofibrant_target (u.leftKanExtensionObjIsoColimit Y d₂).hom
  have := cofibration_of_isIso (u.leftKanExtensionObjIsoColimit Y d₂).inv
  infer_instance

/-- Theorem 9.4.2(1)(c) for the morphism between the chosen pointwise left Kan
extensions, under the finite-source and finite-hom assumptions of this section. -/
theorem reedyCofibrant_pointwiseLeftKanMap_weakEquivalence {X Y : D₁ ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) :
    ∃ (_ : u.HasPointwiseLeftKanExtension X) (_ : u.HasPointwiseLeftKanExtension Y),
      ∀ d₂, WeakEquivalence ((pointwiseLeftKanMap u f).app d₂) := by
  obtain ⟨hKX, _⟩ := reedyCofibrant_leftKanExtension u X hX
  obtain ⟨hKY, _⟩ := reedyCofibrant_leftKanExtension u Y hY
  refine ⟨hKX, hKY, fun d₂ ↦ ?_⟩
  obtain ⟨_, _, hc⟩ := reedyCofibrant_leftKanExtension_weakEquivalence u hX hY f hw d₂
  rw [pointwiseLeftKanMap_app]
  have := weakEquivalence_of_isIso (u.leftKanExtensionObjIsoColimit X d₂).hom
  have := weakEquivalence_of_isIso (u.leftKanExtensionObjIsoColimit Y d₂).inv
  infer_instance

end Main

end ABCCofibrations

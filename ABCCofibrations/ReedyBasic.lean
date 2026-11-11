/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.PushoutComposition
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Direct categories, latching objects and Reedy cofibrations (§9.1–§9.2)

Definitions 9.1.1–9.1.3 and 9.2.2, and Proposition 9.2.3.

The latching category `∂(D ↓ d)` is the full subcategory of `Over d` on the
objects `(d', d' ⟶ d)` with `d' ≠ d`. In a direct category the only map
`d ⟶ d` is the identity, so this is the paper's "all objects except the
identity of `d`". The latching object `LX_d` is the colimit of `X` over it,
when it exists; we record its existence as instance hypotheses.

A Reedy cofibration `f : X ⟶ Y` asks that some pushout
`X_d ⊔_{LX_d} LY_d` has a cofibration as comparison map to `Y_d`. Reedy
fibrations for inverse categories are Reedy cofibrations in the opposite
categories.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- **Definition 9.1.1(1).** A direct category: there is a degree function to `ℕ`
which strictly increases along every non-identity map. -/
class IsDirect (D : Type u₁) [Category.{v₁} D] : Prop where
  exists_deg : ∃ deg : D → ℕ, ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h

/-- **Definition 9.1.1(2).** An inverse category: its opposite is direct. -/
abbrev IsInverse (D : Type u₁) [Category.{v₁} D] : Prop := IsDirect Dᵒᵖ

variable {D : Type u₁} [Category.{v₁} D] {M : Type u₂} [Category.{v₂} M]

/-- The objects of `Over d` other than the identity of `d`. -/
abbrev latchingProp (d : D) : ObjectProperty (Over d) := fun X ↦ X.left ≠ d

/-- **Definition 9.1.2(1).** The latching category `∂(D ↓ d)`. -/
abbrev LatchingCategory (d : D) : Type _ := (latchingProp d).FullSubcategory

/-- The diagram `∂(D ↓ d) ⥤ M` whose colimit is the latching object. -/
def latchingDiagram (X : D ⥤ M) (d : D) : LatchingCategory d ⥤ M :=
  ObjectProperty.ι _ ⋙ Over.forget d ⋙ X

/-- The cocone `X|∂(D ↓ d) ⟶ X_d`. -/
def latchingCocone (X : D ⥤ M) (d : D) : Cocone (latchingDiagram X d) where
  pt := X.obj d
  ι :=
    { app := fun Y ↦ X.map Y.obj.hom
      naturality := fun Y Y' g ↦ by
        have := congrArg X.map (Over.w g.hom)
        simp only [X.map_comp] at this
        simpa [latchingDiagram] using this }

/-- **Definition 9.1.3(1).** The latching object `LX_d`. -/
noncomputable abbrev latchingObj (X : D ⥤ M) (d : D) [HasColimit (latchingDiagram X d)] : M :=
  colimit (latchingDiagram X d)

/-- The latching map `i_d : LX_d ⟶ X_d`. -/
noncomputable def latchingMap (X : D ⥤ M) (d : D) [HasColimit (latchingDiagram X d)] :
    latchingObj X d ⟶ X.obj d :=
  colimit.desc _ (latchingCocone X d)

/-- The restriction of `f : X ⟶ Y` to the latching diagrams. -/
def latchingNat {X Y : D ⥤ M} (f : X ⟶ Y) (d : D) : latchingDiagram X d ⟶ latchingDiagram Y d :=
  Functor.whiskerLeft (ObjectProperty.ι _ ⋙ Over.forget d) f

@[simp]
lemma latchingNat_app {X Y : D ⥤ M} (f : X ⟶ Y) (d : D) (j : LatchingCategory d) :
    (latchingNat f d).app j = f.app j.obj.left := rfl

/-- The map `Lf_d : LX_d ⟶ LY_d` induced by `f : X ⟶ Y`. -/
noncomputable def latchingObjMap {X Y : D ⥤ M} (f : X ⟶ Y) (d : D)
    [HasColimit (latchingDiagram X d)] [HasColimit (latchingDiagram Y d)] :
    latchingObj X d ⟶ latchingObj Y d :=
  colimMap (latchingNat f d)

@[reassoc (attr := simp)]
lemma ι_latchingMap (X : D ⥤ M) (d : D) [HasColimit (latchingDiagram X d)]
    (j : LatchingCategory d) :
    colimit.ι (latchingDiagram X d) j ≫ latchingMap X d = (latchingCocone X d).ι.app j :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma ι_latchingObjMap {X Y : D ⥤ M} (f : X ⟶ Y) (d : D)
    [HasColimit (latchingDiagram X d)] [HasColimit (latchingDiagram Y d)]
    (j : LatchingCategory d) :
    colimit.ι (latchingDiagram X d) j ≫ latchingObjMap f d =
      (latchingNat f d).app j ≫ colimit.ι (latchingDiagram Y d) j :=
  ι_colimMap _ _

@[reassoc]
lemma latchingObjMap_latchingMap {X Y : D ⥤ M} (f : X ⟶ Y) (d : D)
    [HasColimit (latchingDiagram X d)] [HasColimit (latchingDiagram Y d)] :
    latchingObjMap f d ≫ latchingMap Y d = latchingMap X d ≫ f.app d := by
  apply colimit.hom_ext
  intro j
  rw [ι_latchingObjMap_assoc, ι_latchingMap, ι_latchingMap_assoc]
  exact (f.naturality _).symm

lemma latchingObjMap_comp {X Y Z : D ⥤ M} (f : X ⟶ Y) (g : Y ⟶ Z) (d : D)
    [HasColimit (latchingDiagram X d)] [HasColimit (latchingDiagram Y d)]
    [HasColimit (latchingDiagram Z d)] :
    latchingObjMap (f ≫ g) d = latchingObjMap f d ≫ latchingObjMap g d := by
  apply colimit.hom_ext
  intro j
  rw [ι_latchingObjMap, ι_latchingObjMap_assoc, ι_latchingObjMap, ← Category.assoc]
  rfl

section Reedy

variable [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]

/-- **Definition 9.2.2(1)(a).** A Reedy cofibrant diagram: every latching object
(assumed to exist) is cofibrant and every latching map is a cofibration. -/
def IsReedyCofibrant (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] : Prop :=
  ∀ d, IsCofibrant (latchingObj X d) ∧ Cofibration (latchingMap X d)

/-- **Definition 9.2.2(1)(b).** A Reedy cofibration: a map of Reedy cofibrant
diagrams whose relative latching maps `X_d ⊔_{LX_d} LY_d ⟶ Y_d` are cofibrations. -/
def IsReedyCofibration {X Y : D ⥤ M} (f : X ⟶ Y) [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] : Prop :=
  IsReedyCofibrant X ∧ IsReedyCofibrant Y ∧ ∀ d, ∃ (P : M) (l : X.obj d ⟶ P)
    (r : latchingObj Y d ⟶ P) (c : P ⟶ Y.obj d),
    IsPushout (latchingMap X d) (latchingObjMap f d) l r ∧ l ≫ c = f.app d ∧
      r ≫ c = latchingMap Y d ∧ Cofibration c

variable [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- **Proposition 9.2.3(1)**, composition. Reedy cofibrations are stable under
composition. -/
theorem IsReedyCofibration.comp [IsDirect D] {X Y Z : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [∀ d, HasColimit (latchingDiagram Z d)] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsReedyCofibration f) (hg : IsReedyCofibration g) : IsReedyCofibration (f ≫ g) := by
  refine ⟨hf.1, hg.2.1, fun d ↦ ?_⟩
  obtain ⟨hLX, hiX⟩ := hf.1 d
  obtain ⟨hLY, hiY⟩ := hf.2.1 d
  obtain ⟨hLZ, hiZ⟩ := hg.2.1 d
  obtain ⟨P₁, l₁, r₁, c₁, h₁, hl₁, hr₁, hc₁⟩ := hf.2.2 d
  obtain ⟨P₂, l₂, r₂, c₂, h₂, hl₂, hr₂, hc₂⟩ := hg.2.2 d
  have : IsCofibrant (X.obj d) := cofibrant_target (latchingMap X d)
  have : HasPushout (latchingMap X d) (latchingObjMap (f ≫ g) d) := hasPushout _ _
  let h₃ := IsPushout.of_hasPushout (latchingMap X d) (latchingObjMap (f ≫ g) d)
  let c₃ : pushout (latchingMap X d) (latchingObjMap (f ≫ g) d) ⟶ Z.obj d :=
    pushout.desc ((f ≫ g).app d) (latchingMap Z d) (by
      rw [latchingObjMap_latchingMap])
  refine ⟨_, _, _, c₃, h₃, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _, ?_⟩
  have h₃' : IsPushout (latchingObjMap f d ≫ latchingObjMap g d) (latchingMap X d)
      (pushout.inr (latchingMap X d) (latchingObjMap (f ≫ g) d))
      (pushout.inl (latchingMap X d) (latchingObjMap (f ≫ g) d)) := by
    rw [← latchingObjMap_comp]
    exact h₃.flip
  obtain ⟨b, c, -, hT, hfac⟩ := exists_comparison_factorization (latchingObjMap_latchingMap f d)
    h₁.flip h₂.flip h₃' hr₁ hl₁ hr₂ hl₂ (c₀₂ := c₃) (pushout.inr_desc _ _ _)
    (by rw [pushout.inl_desc]; rfl)
  have : Cofibration (pushout.inr (latchingMap X d) (latchingObjMap (f ≫ g) d)) :=
    cofibration_of_isPushout h₃
  have : IsCofibrant P₁ := by
    have := cofibration_of_isPushout h₁
    exact cofibrant_target r₁
  have : IsCofibrant (pushout (latchingMap X d) (latchingObjMap (f ≫ g) d)) :=
    cofibrant_target (pushout.inr _ _)
  have : Cofibration c := cofibration_of_isPushout hT
  rw [hfac]
  infer_instance

/-- **Proposition 9.2.3(1)**, isomorphisms. An isomorphism with Reedy cofibrant
domain has a Reedy cofibrant codomain (whose latching objects exist) and is a
Reedy cofibration. -/
theorem isReedyCofibration_of_isIso [IsDirect D] {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] (f : X ⟶ Y) [IsIso f] (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ d, HasColimit (latchingDiagram Y d)), IsReedyCofibration f := by
  have hN (d : D) : IsIso (latchingNat f d) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    rw [latchingNat_app]
    exact NatIso.isIso_app_of_isIso f _
  have hY (d : D) : HasColimit (latchingDiagram Y d) :=
    hasColimit_of_iso (asIso (latchingNat f d)).symm
  refine ⟨hY, ?_⟩
  have hLf (d : D) : IsIso (latchingObjMap f d) := by
    have := hN d
    exact inferInstanceAs (IsIso (colimMap _))
  have hYR : IsReedyCofibrant Y := fun d ↦ by
    obtain ⟨hLX, hiX⟩ := hX d
    have := hLf d
    have : IsCofibrant (X.obj d) := cofibrant_target (latchingMap X d)
    have : Cofibration (latchingObjMap f d) := cofibration_of_isIso _
    have hLY : IsCofibrant (latchingObj Y d) := cofibrant_target (latchingObjMap f d)
    refine ⟨hLY, ?_⟩
    have : Cofibration (inv (latchingObjMap f d)) := cofibration_of_isIso _
    have : Cofibration (f.app d) := cofibration_of_isIso _
    rw [show latchingMap Y d = inv (latchingObjMap f d) ≫ latchingMap X d ≫ f.app d by
      rw [← latchingObjMap_latchingMap, IsIso.inv_hom_id_assoc]]
    infer_instance
  refine ⟨hX, hYR, fun d ↦ ?_⟩
  obtain ⟨hLX, hiX⟩ := hX d
  obtain ⟨hLY, hiY⟩ := hYR d
  have := hLf d
  have : IsCofibrant (X.obj d) := cofibrant_target (latchingMap X d)
  have : HasPushout (latchingMap X d) (latchingObjMap f d) := hasPushout _ _
  let c : pushout (latchingMap X d) (latchingObjMap f d) ⟶ Y.obj d :=
    pushout.desc (f.app d) (latchingMap Y d) (latchingObjMap_latchingMap f d).symm
  have hc : pushout.inl _ _ ≫ c = f.app d := pushout.inl_desc _ _ _
  refine ⟨_, _, _, c, IsPushout.of_hasPushout _ _, hc, pushout.inr_desc _ _ _, ?_⟩
  have : Cofibration (pushout.inl (latchingMap X d) (latchingObjMap f d)) :=
    cofibration_of_isIso _
  have : IsCofibrant (pushout (latchingMap X d) (latchingObjMap f d)) :=
    cofibrant_target (pushout.inl (latchingMap X d) (latchingObjMap f d))
  have : IsIso c := by
    rw [show c = inv (pushout.inl (latchingMap X d) (latchingObjMap f d)) ≫ f.app d by
      rw [← hc, IsIso.inv_hom_id_assoc]]
    infer_instance
  exact cofibration_of_isIso c

end Reedy

section ReedyFibration

variable [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]

/-- **Definition 9.2.2(2)(a).** A Reedy fibrant diagram over an inverse category:
its opposite is Reedy cofibrant. The latching objects of `X.op` are the opposites
of the matching objects `MX_d`. -/
abbrev IsReedyFibrant (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X.op d)] : Prop :=
  IsReedyCofibrant X.op

/-- **Definition 9.2.2(2)(b).** A Reedy fibration: its opposite is a Reedy
cofibration (so the codomain is Reedy fibrant). -/
abbrev IsReedyFibration {X Y : D ⥤ M} (f : X ⟶ Y) [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] : Prop :=
  IsReedyCofibration (NatTrans.op f)

variable [ABCPrefibrationCategory M]

/-- **Proposition 9.2.3(2)**, composition. Reedy fibrations are stable under
composition. -/
theorem IsReedyFibration.comp [IsInverse D] {X Y Z : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X.op d)] [∀ d, HasColimit (latchingDiagram Y.op d)]
    [∀ d, HasColimit (latchingDiagram Z.op d)] {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsReedyFibration f) (hg : IsReedyFibration g) : IsReedyFibration (f ≫ g) := by
  change IsReedyCofibration (NatTrans.op (f ≫ g))
  rw [NatTrans.op_comp]
  exact IsReedyCofibration.comp hg hf

/-- **Proposition 9.2.3(2)**, isomorphisms. An isomorphism with Reedy fibrant
codomain has a Reedy fibrant domain and is a Reedy fibration. -/
theorem isReedyFibration_of_isIso [IsInverse D] {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram Y.op d)] (f : X ⟶ Y) [IsIso f] (hY : IsReedyFibrant Y) :
    ∃ (_ : ∀ d, HasColimit (latchingDiagram X.op d)), IsReedyFibration f := by
  have : IsIso (NatTrans.op f) := inferInstance
  exact isReedyCofibration_of_isIso (NatTrans.op f) hY

end ReedyFibration

end ABCCofibrations

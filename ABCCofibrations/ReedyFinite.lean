/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyColimits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max

/-!
# Colimits of Reedy cofibrant diagrams over finite direct categories

Theorem 9.3.5(1)(a) for direct categories with finitely many objects: the colimit
of a Reedy cofibrant diagram exists and is cofibrant.

The proof is by induction on the number of objects. Remove an object `d` of
maximal degree: no non-identity map leaves `d`, the restriction of the diagram
to `D ∖ {d}` is again Reedy cofibrant (its latching categories are those of
`D`), and Lemma 9.3.1 computes the colimit over `D` as a pushout along the
latching map at `d`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

section Restriction

variable {D : Type u₁} [Category.{v₁} D] {M : Type u₂} [Category.{v₂} M] {d : D}
  (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)

/-- The latching category of `D ∖ {d}` at `e` maps to the latching category of
`D` at `e`. -/
def latchingRestrict (e : Complement d) : LatchingCategory e ⥤ LatchingCategory e.obj where
  obj j := ⟨Over.mk (Y := j.obj.left.obj) j.obj.hom.hom, fun h ↦ j.property
    (ObjectProperty.FullSubcategory.ext h)⟩
  map g := ⟨Over.homMk g.hom.left.hom (congrArg InducedCategory.Hom.hom (Over.w g.hom))⟩

instance (e : Complement d) : (latchingRestrict e).Faithful where
  map_injective {_ _} g g' h := by
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    apply InducedCategory.hom_ext
    exact congrArg (fun k ↦ k.hom.left) h

instance (e : Complement d) : (latchingRestrict e).Full where
  map_surjective {_ _} g := ⟨⟨Over.homMk ⟨g.hom.left⟩ (InducedCategory.hom_ext (Over.w g.hom))⟩,
    rfl⟩

include hd in
lemma latchingRestrict_essSurj (e : Complement d) : (latchingRestrict e).EssSurj where
  mem_essImage k := by
    have hne : k.obj.left ≠ d := by
      intro h
      obtain ⟨h', -⟩ := hd e.obj (eqToHom h.symm ≫ k.obj.hom)
      exact e.property h'.symm
    exact ⟨⟨Over.mk (Y := (⟨k.obj.left, hne⟩ : Complement d)) ⟨k.obj.hom⟩,
      fun h ↦ k.property (congrArg ObjectProperty.FullSubcategory.obj h)⟩, ⟨Iso.refl _⟩⟩

include hd in
lemma latchingRestrict_isEquivalence (e : Complement d) : (latchingRestrict e).IsEquivalence := by
  have := latchingRestrict_essSurj hd e
  exact { }

include hd in
lemma latchingRestrict_final (e : Complement d) : (latchingRestrict e).Final := by
  have := latchingRestrict_isEquivalence hd e
  exact Functor.final_of_isRightAdjoint _

variable (X : D ⥤ M)

include hd in
lemma hasColimit_latching_restrict (e : Complement d) [HasColimit (latchingDiagram X e.obj)] :
    HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e) := by
  have := latchingRestrict_final hd e
  exact Functor.Final.comp_hasColimit (latchingRestrict e) (G := latchingDiagram X e.obj)

lemma latchingMap_restrict (e : Complement d) [HasColimit (latchingDiagram X e.obj)]
    [h : HasColimit (latchingRestrict e ⋙ latchingDiagram X e.obj)] :
    @latchingMap _ _ _ _ ((complementProp d).ι ⋙ X) e h =
      colimit.pre (latchingDiagram X e.obj) (latchingRestrict e) ≫ latchingMap X e.obj := by
  let : HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e) := h
  apply colimit.hom_ext
  intro j
  have h₁ := colimit.ι_desc (latchingCocone ((complementProp d).ι ⋙ X) e) j
  have h₂ := colimit.ι_pre_assoc (latchingDiagram X e.obj) (latchingRestrict e) j
    (latchingMap X e.obj)
  rw [ι_latchingMap] at h₂
  exact h₁.trans h₂.symm

open ABCPrecofibrationCategory in
include hd in
/-- The restriction of a Reedy cofibrant diagram to `D ∖ {d}` is Reedy
cofibrant, when no non-identity map leaves `d`. -/
lemma isReedyCofibrant_restrict [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M]
    [HasInitial M] [ABCPrecofibrationCategory M] [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e)),
      IsReedyCofibrant ((complementProp d).ι ⋙ X) := by
  have hC (e : Complement d) := hasColimit_latching_restrict hd X e
  refine ⟨hC, fun e ↦ ?_⟩
  have := latchingRestrict_final hd e
  have hh : HasColimit (latchingRestrict e ⋙ latchingDiagram X e.obj) := hC e
  let φ := colimit.pre (latchingDiagram X e.obj) (latchingRestrict e)
  have hφ : IsIso φ :=
    Functor.Final.colimit_pre_isIso (latchingRestrict e) (G := latchingDiagram X e.obj)
  obtain ⟨hL, hi⟩ := hX e.obj
  have : Cofibration (inv φ) := cofibration_of_isIso _
  have hL' : IsCofibrant (colimit (latchingRestrict e ⋙ latchingDiagram X e.obj)) :=
    cofibrant_target (inv φ)
  refine ⟨hL', ?_⟩
  have : Cofibration φ := cofibration_of_isIso _
  change Cofibration (@latchingMap _ _ _ _ ((complementProp d).ι ⋙ X) e hh)
  rw [latchingMap_restrict]
  exact (inferInstance : Cofibration (φ ≫ latchingMap X e.obj))

end Restriction

/-- `D ∖ {d}` is direct when `D` is. -/
instance {D : Type u₁} [Category.{v₁} D] [IsDirect D] (d : D) : IsDirect (Complement d) where
  exists_deg := by
    obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
    refine ⟨fun e ↦ deg e.obj, fun {x y} f ↦ ?_⟩
    rcases hdeg f.hom with h | ⟨h, hf⟩
    · exact Or.inl h
    · obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      dsimp at h
      subst h
      exact Or.inr ⟨rfl, InducedCategory.hom_ext (by simpa using hf)⟩

noncomputable instance {D : Type u₁} [Category.{v₁} D] [Fintype D] [DecidableEq D] (d : D) :
    Fintype (Complement d) :=
  Fintype.ofEquiv {e // e ≠ d}
    { toFun := fun e ↦ ⟨e.1, e.2⟩
      invFun := fun e ↦ ⟨e.obj, e.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

lemma card_complement {D : Type u₁} [Category.{v₁} D] [Fintype D] [DecidableEq D] (d : D) :
    Fintype.card (Complement d) = Fintype.card D - 1 := by
  rw [show Fintype.card (Complement d) = Fintype.card {e // e ≠ d} from
    Fintype.card_congr ⟨fun e ↦ ⟨e.obj, e.property⟩, fun e ↦ ⟨e.1, e.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩]
  rw [Fintype.card_subtype_compl (fun x ↦ x = d), Fintype.card_subtype_eq]

section Main

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- In a nonempty finite direct category there is an object with no non-identity
maps out of it (an object of maximal degree). -/
lemma exists_maximal {D : Type u₁} [Category.{v₁} D] [Finite D] [IsDirect D] [Nonempty D] :
    ∃ d : D, ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h := by
  have := Fintype.ofFinite D
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  obtain ⟨d, -, hmax⟩ := Finset.exists_max_image Finset.univ deg Finset.univ_nonempty
  refine ⟨d, fun e g ↦ ?_⟩
  rcases hdeg g with h | h
  · exact absurd (hmax e (Finset.mem_univ e)) (not_le.2 h)
  · exact h

/-- **Theorem 9.3.5(1)(a)**, for direct categories with finitely many objects. The
colimit of a Reedy cofibrant diagram exists and is cofibrant. -/
theorem reedyCofibrant_colimit_finite (n : ℕ) :
    ∀ (D : Type u₁) [Category.{v₁} D] [Fintype D] [IsDirect D], Fintype.card D = n →
      ∀ (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)], IsReedyCofibrant X →
        ∃ (_ : HasColimit X), IsCofibrant (colimit X) := by
  induction n with
  | zero =>
    intro D _ _ _ hcard X _ _
    have : IsEmpty D := Fintype.card_eq_zero_iff.1 hcard
    let c : Cocone X :=
      ⟨⊥_ M, { app := fun j ↦ isEmptyElim j, naturality := fun j ↦ isEmptyElim j }⟩
    have hc : IsColimit c := (isColimitEquivIsInitialOfIsEmpty (c := c)).symm initialIsInitial
    have : HasColimit X := ⟨⟨⟨c, hc⟩⟩⟩
    refine ⟨this, ?_⟩
    have := cofibration_of_isIso (hc.coconePointUniqueUpToIso (colimit.isColimit X)).hom
    exact cofibrant_target (hc.coconePointUniqueUpToIso (colimit.isColimit X)).hom
  | succ n ih =>
    intro D _ _ _ hcard X _ hX
    classical
    have : Nonempty D := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨d, hd⟩ := exists_maximal (D := D)
    obtain ⟨_, hX'⟩ := isReedyCofibrant_restrict hd X hX
    obtain ⟨_, hC⟩ := ih (Complement d) (by rw [card_complement, hcard]; rfl)
      ((complementProp d).ι ⋙ X) hX'
    obtain ⟨hL, hi⟩ := hX d
    obtain ⟨hcol, -, hcof, -⟩ := colimit_isPushout_latching X d hd hL hC hi
    exact ⟨hcol, hcof⟩

end Main

end ABCCofibrations

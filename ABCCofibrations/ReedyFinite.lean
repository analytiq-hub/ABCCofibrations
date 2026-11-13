/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyColimits
public import ABCCofibrations.ReedyOpen
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

include hd in
/-- The complement of a maximal object is an open full subcategory. -/
lemma complement_isOpen : IsOpenDiagramSubcategory (complementProp d) := by
  intro a b f hb h
  obtain ⟨h', -⟩ := hd b (eqToHom h.symm ≫ f)
  exact hb h'.symm

/-- The latching-category comparison for the complement of a maximal object. -/
abbrev latchingRestrict (e : Complement d) : LatchingCategory e ⥤ LatchingCategory e.obj :=
  OpenDiagramSubcategory.latchingInclusion (complementProp d) e

include hd in
lemma latchingRestrict_essSurj (e : Complement d) : (latchingRestrict e).EssSurj :=
  OpenDiagramSubcategory.latchingInclusion_essSurj _ (complement_isOpen hd) e

include hd in
lemma latchingRestrict_isEquivalence (e : Complement d) : (latchingRestrict e).IsEquivalence := by
  have := latchingRestrict_essSurj hd e
  exact { }

include hd in
lemma latchingRestrict_final (e : Complement d) : (latchingRestrict e).Final :=
  OpenDiagramSubcategory.latchingInclusion_final _ (complement_isOpen hd) e

variable (X : D ⥤ M)

include hd in
lemma hasColimit_latching_restrict (e : Complement d) [HasColimit (latchingDiagram X e.obj)] :
    HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e) :=
  OpenDiagramSubcategory.hasColimit_latching _ (complement_isOpen hd) X e

lemma latchingMap_restrict (e : Complement d) [HasColimit (latchingDiagram X e.obj)]
    [h : HasColimit (latchingRestrict e ⋙ latchingDiagram X e.obj)] :
    @latchingMap _ _ _ _ ((complementProp d).ι ⋙ X) e h =
      colimit.pre (latchingDiagram X e.obj) (latchingRestrict e) ≫ latchingMap X e.obj :=
  OpenDiagramSubcategory.latchingMap_restrict _ X e

include hd in
/-- Restriction to the complement of a maximal object preserves Reedy cofibrancy. -/
lemma isReedyCofibrant_restrict [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M]
    [HasInitial M] [ABCPrecofibrationCategory M] [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram ((complementProp d).ι ⋙ X) e)),
      IsReedyCofibrant ((complementProp d).ι ⋙ X) :=
  OpenDiagramSubcategory.isReedyCofibrant _ (complement_isOpen hd) X hX

end Restriction

/-- `D ∖ {d}` is direct when `D` is. -/
instance {D : Type u₁} [Category.{v₁} D] [IsDirect D] (d : D) : IsDirect (Complement d) :=
  isDirect_fullSubcategory (complementProp d)

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

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyKan
public import ABCCofibrations.ReedyRelativeColimits

/-!
# The boundary comma category for Theorem 9.4.3

For a direct target, the objects `u(e) ⟶ d` with `u(e) ≠ d` form an open
full subcategory of `(u ↓ d)`. Its colimit is the candidate latching object
of the left Kan extension. The comparison with that latching object is a
separate step; this module establishes the boundary colimit and cofibration.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D₁ D₂ : Type w} [SmallCategory D₁] [SmallCategory D₂]
  (u : D₁ ⥤ D₂) (d : D₂)

/-- The boundary of `(u ↓ d)` used in Theorem 9.4.3. -/
def kanBoundary : ObjectProperty (CostructuredArrow u d) := fun j ↦ u.obj j.left ≠ d

/-- The boundary comma category is open when the target category is direct. -/
lemma kanBoundary_isOpen [IsDirect D₂] : IsOpenDiagramSubcategory (kanBoundary u d) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₂)
  intro a b f hb ha
  have hb' : deg (u.obj b.left) < deg d := by
    rcases hdeg b.hom with h | ⟨h, _⟩
    · exact h
    · exact (hb h).elim
  rcases hdeg (u.map f.left) with h | ⟨h, _⟩
  · rw [ha] at h
    omega
  · exact hb (h.symm.trans ha)

/-- A proper final segment of a composable pair in a direct category forces
the entire composite to have distinct endpoints. -/
lemma IsDirect.ne_of_homs {C : Type*} [Category C] [IsDirect C] {a b c : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : b ≠ c) : a ≠ c := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := C)
  intro ha
  have hb : deg b < deg c := by
    rcases hdeg g with hg | ⟨hg, _⟩
    · exact hg
    · exact (h hg).elim
  rcases hdeg f with hf | ⟨hf, _⟩
  · rw [ha] at hf
    omega
  · exact h (hf.symm.trans ha)

/-- Composing a comma arrow with a latching arrow lands in the boundary. -/
def kanBoundaryPost [IsDirect D₂] (k : LatchingCategory d) :
    CostructuredArrow u k.obj.left ⥤ (kanBoundary u d).FullSubcategory where
  obj j := ⟨CostructuredArrow.mk (j.hom ≫ k.obj.hom),
    IsDirect.ne_of_homs j.hom k.obj.hom k.property⟩
  map {a b} f := ⟨CostructuredArrow.homMk f.left (by
    change u.map f.left ≫ (b.hom ≫ k.obj.hom) = a.hom ≫ k.obj.hom
    simpa only [Category.assoc] using congrArg (· ≫ k.obj.hom) f.w)⟩

/-- A boundary comma arrow defines a latching arrow in the target category. -/
def kanBoundaryToLatching : (kanBoundary u d).FullSubcategory ⥤ LatchingCategory d where
  obj j := ⟨Over.mk j.obj.hom, j.property⟩
  map f := ⟨Over.homMk (u.map f.hom.left) f.hom.w⟩

variable [Finite D₁] [∀ a b : D₁, Finite (a ⟶ b)]
  [∀ a b : D₂, Finite (a ⟶ b)] [IsDirect D₁] [IsDirect D₂]
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

omit [∀ a b : D₁, Finite (a ⟶ b)] in
/-- The candidate latching object exists and its inclusion into the comma
colimit is a cofibration, in the finite case of Theorem 9.4.3(1)(a). -/
theorem reedyCofibrant_kanBoundary_colimit (X : D₁ ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X))
      (_ : HasColimit (CostructuredArrow.proj u d ⋙ X)),
      IsCofibrant (colimit ((kanBoundary u d).ι ⋙ CostructuredArrow.proj u d ⋙ X)) ∧
        Cofibration (colimit.pre (CostructuredArrow.proj u d ⋙ X) (kanBoundary u d).ι) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D₁)
  have : IsDirect (CostructuredArrow u d) := ⟨⟨_, hdeg_comma u deg hdeg⟩⟩
  obtain ⟨_, hX'⟩ := isReedyCofibrant_comma u deg hdeg X (d₂ := d) hX
  obtain ⟨hB, hC, hpre⟩ := reedyCofibrant_colimit_open (kanBoundary u d) (kanBoundary_isOpen u d)
    (CostructuredArrow.proj u d ⋙ X) hX'
  obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (kanBoundary u d)
    (kanBoundary_isOpen u d) (CostructuredArrow.proj u d ⋙ X) hX'
  have : Finite (kanBoundary u d).FullSubcategory := Finite.of_injective
    (fun e : (kanBoundary u d).FullSubcategory ↦ e.obj)
    (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)
  have := Fintype.ofFinite (kanBoundary u d).FullSubcategory
  obtain ⟨_, hBC⟩ := reedyCofibrant_colimit_finite _ (kanBoundary u d).FullSubcategory rfl _ hR
  exact ⟨hB, hC, hBC, hpre⟩

end ABCCofibrations

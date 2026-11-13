/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyTruncationFactorization

/-! # Compatible towers of degree-wise Reedy factorizations -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M]

/-- A chosen factorization, retaining its middle diagram's latching data. -/
structure ReedyFactorizationData {D : Type w} [SmallCategory D]
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)] (f : X ⟶ Y) where
  middle : D ⥤ M
  hasLatching : ∀ d, HasColimit (latchingDiagram middle d)
  left : X ⟶ middle
  right : middle ⟶ Y
  reedy : letI := hasLatching; IsReedyCofibration left
  weak : ∀ d, WeakEquivalence (right.app d)
  fac : left ≫ right = f

namespace ReedyFactorizationData
variable [ABCPrecofibrationCategory M]
  {D : Type w} [SmallCategory D] (deg : D → ℕ)
  (hdeg : ∀ {a b : D} (g : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, g = eqToHom h)
  (h5 : CoproductCofibrationAxiom.{w} M)
  {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
  (hX : IsReedyCofibrant X) (f : X ⟶ Y)
  [∀ n e, HasColimit (latchingDiagram ((degreeBelow deg n).ι ⋙ X) e)]

/-- The chosen factorization data on one degree truncation. -/
abbrev Stage (n : ℕ) := ReedyFactorizationData (Functor.whiskerLeft (degreeBelow deg n).ι f)

/-- Compatibility of adjacent middle diagrams and both factorization maps. -/
structure Compatible {n : ℕ} (A : Stage deg f n) (B : Stage deg f (n + 1)) where
  iso : degreeInclusion deg (Nat.le_succ n) ⋙ B.middle ≅ A.middle
  left : Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) B.left ≫ iso.hom = A.left
  right : iso.inv ≫ Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) B.right = A.right

include hdeg h5 hX in
/-- Every chosen stage has a compatible successor. -/
theorem exists_next {n : ℕ} (A : Stage deg f n) :
    ∃ B : Stage deg f (n + 1), Nonempty (Compatible deg f A B) := by
  have := A.hasLatching
  obtain ⟨Z, hLZ, a, r, e, ha, hr, har, hl, ht⟩ := reedy_factorization_next_truncation
    deg hdeg h5 hX f n A.middle A.left A.right A.reedy A.weak A.fac
  exact ⟨⟨Z, hLZ, a, r, ha, hr, har⟩, ⟨⟨e, hl, ht⟩⟩⟩

include hdeg h5 hX in
/-- The empty first truncation has a chosen factorization. -/
theorem nonempty_zero : Nonempty (Stage deg f 0) := by
  have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg 0)
    (degreeBelow_isOpen deg hmono 0) X hX
  obtain ⟨Z, hLZ, a, r, ha, hr, har⟩ := reedy_factorization_bounded h5 0
    (degreeBelow deg 0).FullSubcategory (fun e ↦ deg e.obj)
    (degreeCondition_fullSubcategory _ deg hdeg) (fun e ↦ e.property)
    _ _ hRX (Functor.whiskerLeft (degreeBelow deg 0).ι f)
  exact ⟨⟨Z, hLZ, a, r, ha, hr, har⟩⟩

/-- One tower of factorizations, with each successor chosen relative to its predecessor. -/
noncomputable def tower : (n : ℕ) → Stage deg f n
  | 0 => Classical.choice (nonempty_zero deg hdeg h5 hX f)
  | n + 1 => Classical.choose (exists_next deg hdeg h5 hX f (tower n))

/-- The chosen comparison identifies each restriction with the preceding stage. -/
noncomputable def towerCompatibility (n : ℕ) :
    Compatible deg f (tower deg hdeg h5 hX f n) (tower deg hdeg h5 hX f (n + 1)) :=
  Classical.choice (Classical.choose_spec
    (exists_next deg hdeg h5 hX f (tower deg hdeg h5 hX f n)))

end ReedyFactorizationData
end ABCCofibrations

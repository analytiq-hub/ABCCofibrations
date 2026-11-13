/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyFactorizationTower
public import ABCCofibrations.DegreeDiagramGluing

/-!
# Reedy factorizations over arbitrary small direct categories

The CF4 construction of Theorem 9.2.4(1)(a). A compatible tower of layer
factorizations is glued objectwise. CF5(1) supplies the bounded predecessor
colimits; CF6 and functorial factorizations are not needed.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

/-- Reedy factorization over every small direct category, with only CF5(1)
beyond the precofibration axioms. -/
theorem reedy_factorization_small
    {D : Type w} [SmallCategory D] [IsDirect D] {M : Type u} [Category.{v} M]
    [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
    [ABCPrecofibrationCategory M] (h5 : CoproductCofibrationAxiom.{w} M)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    (hX : IsReedyCofibrant X) (f : X ⟶ Y) :
    ∃ (Z : D ⥤ M) (_ : ∀ d, HasColimit (latchingDiagram Z d))
      (a : X ⟶ Z) (r : Z ⟶ Y),
      IsReedyCofibration a ∧ (∀ d, WeakEquivalence (r.app d)) ∧ a ≫ r = f := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  have hStageX (n : ℕ) := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
    (degreeBelow_isOpen deg hmono n) X hX
  have hLX : ∀ n e, HasColimit (latchingDiagram ((degreeBelow deg n).ι ⋙ X) e) :=
    fun n ↦ (hStageX n).choose
  let A := ReedyFactorizationData.tower deg hdeg h5 hX f
  let C := ReedyFactorizationData.towerCompatibility deg hdeg h5 hX f
  let S (n : ℕ) := (A n).middle
  let step (n : ℕ) : degreeInclusion deg (Nat.le_succ n) ⋙ S (n + 1) ≅ S n := (C n).iso
  let a (n : ℕ) : (degreeBelow deg n).ι ⋙ X ⟶ S n := (A n).left
  let r (n : ℕ) : S n ⟶ (degreeBelow deg n).ι ⋙ Y := (A n).right
  have ha : ∀ n, Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) (a (n + 1)) ≫
      (step n).hom = a n := fun n ↦ (C n).left
  have hr : ∀ n, (step n).inv ≫
      Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) (r (n + 1)) = r n :=
    fun n ↦ (C n).right
  let Z := DegreeDiagramGluing.diagram deg S step hmono
  let a' := DegreeDiagramGluing.lift deg S step hmono X a ha
  let r' := DegreeDiagramGluing.desc deg S step hmono Y r hr
  have hRestricted (n : ℕ) :
      ∃ (_ : ∀ e, HasColimit (latchingDiagram ((degreeBelow deg n).ι ⋙ Z) e)),
        IsReedyCofibration (Functor.whiskerLeft (degreeBelow deg n).ι a') := by
    have := (A n).hasLatching
    have hA : IsReedyCofibration (a n) := (A n).reedy
    let e : (degreeBelow deg n).ι ⋙ Z ≅ S n :=
      DegreeDiagramGluing.restrictionIso deg S step hmono n
    obtain ⟨hL, hInv⟩ := isReedyCofibration_of_isIso e.inv hA.2.1
    refine ⟨hL, ?_⟩
    rw [show Functor.whiskerLeft (degreeBelow deg n).ι a' = a n ≫ e.inv by
      rw [← DegreeDiagramGluing.lift_restriction deg S step hmono X a ha n]
      change Functor.whiskerLeft (degreeBelow deg n).ι a' =
        (Functor.whiskerLeft (degreeBelow deg n).ι a' ≫ e.hom) ≫ e.inv
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]]
    exact hA.comp hInv
  choose hRC hR using hRestricted
  have hWhole (d : D) : ∃ (_ : HasColimit (latchingDiagram Z d)),
      IsCofibrant (latchingObj Z d) ∧ Cofibration (latchingMap Z d) := by
    let n := deg d + 1
    exact reedy_at_of_open_restriction (degreeBelow deg n) (degreeBelow_isOpen deg hmono n)
      Z ⟨d, Nat.lt_succ_self _⟩ ((hR n).2.1 _)
  choose hLZ hZ using hWhole
  have hReedy : IsReedyCofibration a' := by
    refine ⟨hX, hZ, fun d ↦ ?_⟩
    let n := deg d + 1
    let e : (degreeBelow deg n).FullSubcategory := ⟨d, Nat.lt_succ_self _⟩
    obtain ⟨Q, l, t, k, hQ, hl, ht, hk⟩ := (hR n).2.2 e
    obtain ⟨t', hQ', ht'⟩ := comparison_of_open_restriction (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) a' e hQ ht
    exact ⟨Q, l, t', k, hQ', hl, ht', hk⟩
  refine ⟨Z, hLZ, a', r', hReedy, ?_, ?_⟩
  · intro d
    exact (A (deg d + 1)).weak ⟨d, Nat.lt_succ_self _⟩
  · ext d
    exact congrArg (fun t ↦ t.app (⟨d, Nat.lt_succ_self _⟩ :
      (degreeBelow deg (deg d + 1)).FullSubcategory)) (A (deg d + 1)).fac

end ABCCofibrations

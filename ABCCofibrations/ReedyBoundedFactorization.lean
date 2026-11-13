/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyLayerFactorization

/-! # Reedy factorizations with bounded degree

The CF4 part of Theorem 9.2.4(1)(a), for a degree bound but arbitrarily
many objects and arrows. Only CF5(1) is used beyond CF1–CF4.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

/-- Bounded-degree Reedy factorization, without finite-object or finite-hom
assumptions. No CF6 or functorial factorization is needed. -/
theorem reedy_factorization_bounded (h5 : CoproductCofibrationAxiom.{w} M) (N : ℕ) :
    ∀ (D : Type w) [SmallCategory D] (deg : D → ℕ),
      (∀ {a b : D} (g : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, g = eqToHom h) →
      (∀ d, deg d < N) → ∀ (X Y : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)],
        IsReedyCofibrant X → ∀ f : X ⟶ Y,
        ∃ (Z : D ⥤ M) (_ : ∀ d, HasColimit (latchingDiagram Z d))
          (a : X ⟶ Z) (r : Z ⟶ Y),
          IsReedyCofibration a ∧ (∀ d, WeakEquivalence (r.app d)) ∧ a ≫ r = f := by
  induction N with
  | zero =>
    intro D _ deg hdeg hbound X Y _ hX f
    have : IsEmpty D := ⟨fun d ↦ Nat.not_lt_zero _ (hbound d)⟩
    have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
    obtain ⟨_, hId⟩ := isReedyCofibration_of_isIso (𝟙 X) hX
    exact ⟨X, inferInstance, 𝟙 X, f, hId, fun d ↦ isEmptyElim d, Category.id_comp f⟩
  | succ N ih =>
    intro D _ deg hdeg hbound X Y _ hX f
    have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
    have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
      intro a b g
      rcases hdeg g with h | ⟨h, _⟩
      · exact h.le
      · exact (congrArg deg h).le
    let P := degreeBelow deg N
    obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant P
      (degreeBelow_isOpen deg hmono N) X hX
    obtain ⟨Z, _, a, r, ha, hr, har⟩ := ih P.FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory P deg hdeg) (fun e ↦ e.property)
      (P.ι ⋙ X) (P.ι ⋙ Y) hRX (Functor.whiskerLeft P.ι f)
    have hmax : ∀ d, ¬ P d → ∀ e (g : d ⟶ e), ∃ h : d = e, g = eqToHom h := by
      intro d hd e g
      rcases hdeg g with h | h
      · have hd' : ¬ deg d < N := hd
        have he := hbound e
        omega
      · exact h
    obtain ⟨Z', hLZ', a', r', _, ha', hr', har', _, _⟩ :=
      ReedyLayer.factorization_layer P hmax deg hdeg h5 hX f Z a r ha hr har
    exact ⟨Z', hLZ', a', r', ha', hr', har'⟩

end ABCCofibrations

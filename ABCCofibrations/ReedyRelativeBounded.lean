/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallCofibrations

/-!
# Relative colimits with bounded complementary degrees

The old open subcategory may have unbounded degrees. Only the degrees of
objects outside it are bounded. This is the bounded part of Theorem 9.4.1(1)(a).
-/

@[expose] public section

universe w z v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]
open ABCPrecofibrationCategory

/-- Relative colimit existence and the restriction cofibration, assuming a
bound only on the degrees outside the fully faithful open source. -/
theorem reedyCofibrant_colimit_pre_bounded_outside
    (h5 : CoproductCofibrationAxiom.{w} M) (N : ℕ) :
    ∀ (D : Type w) [SmallCategory D] (deg : D → ℕ),
      (∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h) →
      ∀ (E : Type z) [SmallCategory E] (i : E ⥤ D) [i.Full] [i.Faithful],
        (∀ {a : D} (e : E), (a ⟶ i.obj e) → ∃ e', i.obj e' = a) →
        (∀ d, (∀ e, i.obj e ≠ d) → deg d < N) →
        ∀ (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] [HasColimit (i ⋙ X)],
          IsReedyCofibrant X → IsCofibrant (colimit (i ⋙ X)) →
          ∃ (_ : HasColimit X), Cofibration (colimit.pre X i) := by
  induction N with
  | zero =>
    intro D _ deg hdeg E _ i _ _ hopen hbound X _ _ hX hC
    classical
    have : i.EssSurj := ⟨fun d ↦ by
      have hd : ∃ e, i.obj e = d := by
        by_contra h
        exact Nat.not_lt_zero _ (hbound d (by simpa using h))
      obtain ⟨e, he⟩ := hd
      exact ⟨e, ⟨eqToIso he⟩⟩⟩
    have : i.IsEquivalence := { }
    have : i.Final := Functor.final_of_isRightAdjoint i
    have : HasColimit X := Functor.Final.hasColimit_of_comp i
    exact ⟨this, cofibration_of_isIso _⟩
  | succ N ih =>
    intro D _ deg hdeg E _ i _ _ hopen hbound X _ _ hX hC
    classical
    have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
      intro a b g
      rcases hdeg g with h | ⟨h, _⟩
      · exact h.le
      · exact (congrArg deg h).le
    let R : ObjectProperty D := fun d ↦ (∃ e, i.obj e = d) ∨ deg d < N
    have hRopen : IsOpenDiagramSubcategory R := by
      intro a b g hb
      rcases hb with ⟨e, he⟩ | hb
      · obtain ⟨e', he'⟩ := hopen e (g ≫ eqToHom he.symm)
        exact Or.inl ⟨e', he'⟩
      · exact Or.inr (lt_of_le_of_lt (hmono g) hb)
    let i' : E ⥤ R.FullSubcategory := R.lift i (fun e ↦ Or.inl ⟨e, rfl⟩)
    have hopen' : ∀ {a : R.FullSubcategory} (e : E), (a ⟶ i'.obj e) →
        ∃ e', i'.obj e' = a := by
      intro a e g
      obtain ⟨e', he'⟩ := hopen e g.hom
      exact ⟨e', ObjectProperty.FullSubcategory.ext he'⟩
    have hbound' (d : R.FullSubcategory) (hd : ∀ e, i'.obj e ≠ d) : deg d.obj < N := by
      rcases d.property with ⟨e, he⟩ | hb
      · exact False.elim (hd e (ObjectProperty.FullSubcategory.ext he))
      · exact hb
    obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant R hRopen X hX
    have : HasColimit (i' ⋙ R.ι ⋙ X) := ‹HasColimit (i ⋙ X)›
    obtain ⟨_, hi'⟩ := ih R.FullSubcategory (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory R deg hdeg) E i' hopen' hbound' (R.ι ⋙ X) hRX hC
    have : IsCofibrant (colimit (i' ⋙ R.ι ⋙ X)) := hC
    have hRC : IsCofibrant (colimit (R.ι ⋙ X)) := cofibrant_target (colimit.pre (R.ι ⋙ X) i')
    have hmax : ∀ d, ¬ R d → ∀ e (g : d ⟶ e), ∃ h : d = e, g = eqToHom h := by
      intro d hd e g
      rcases hdeg g with h | h
      · have hdN : ¬ deg d < N := fun hb ↦ hd (Or.inr hb)
        have heout : ∀ a, i.obj a ≠ e := by
          intro a he
          obtain ⟨a', ha'⟩ := hopen a (g ≫ eqToHom he.symm)
          exact hd (Or.inl ⟨a', ha'⟩)
        have he := hbound e heout
        omega
      · exact h
    have : ∀ d : ReedyLayer.Objects R, HasColimit (latchingDiagram X d.val) :=
      fun _ ↦ inferInstance
    obtain ⟨_, _, hCol, _, _, hpre⟩ := colimit_isPushout_layer R hmax h5 X
      (fun d ↦ (hX d.val).1) (fun d ↦ (hX d.val).2) hRC
    refine ⟨hCol, ?_⟩
    rw [show colimit.pre X i = colimit.pre (R.ι ⋙ X) i' ≫ colimit.pre X R.ι by
      apply colimit.hom_ext
      intro e
      rw [colimit.ι_pre]
      change colimit.ι X (i.obj e) = colimit.ι (i' ⋙ R.ι ⋙ X) e ≫
        colimit.pre (R.ι ⋙ X) i' ≫ colimit.pre X R.ι
      rw [colimit.ι_pre_assoc, colimit.ι_pre]
      rfl]
    infer_instance

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyStructure
public import ABCCofibrations.ReedySmallLimits

/-! # Pointwise consequences and pushouts for arbitrary small Reedy diagrams

Corollary 9.3.6 and CF3 for arbitrary small direct categories. The pointwise
fibration consequence is transported from the cofibration theorem.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

section Cofibrations
variable {D : Type w} [SmallCategory D] [IsDirect D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

/-- **Corollary 9.3.6(1)**, for arbitrary small direct categories. A Reedy cofibration
`f : X ⟶ Y` induces cofibrations `LX_d ⟶ LY_d` and `X_d ⟶ Y_d`; in particular
Reedy cofibrations are pointwise cofibrations. -/
theorem IsReedyCofibration.cofibration_app_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M) {X Y : D ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) (d : D) :
    Cofibration (latchingObjMap f d) ∧ Cofibration (f.app d) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  obtain ⟨hXL, hYL, hfL⟩ := isReedyCofibration_latching deg hdeg hf (d := d)
  have : IsDirect (LatchingCategory d) := ⟨⟨_, hdeg_latching deg hdeg d⟩⟩
  obtain ⟨_, _, hL⟩ := reedyCofibration_colimMap_small h5 h6 _ hfL
  have hL' : Cofibration (latchingObjMap f d) := hL
  refine ⟨hL', ?_⟩
  obtain ⟨hLX, hiX⟩ := hf.1 d
  obtain ⟨hLY, -⟩ := hf.2.1 d
  obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hf.2.2 d
  have : IsCofibrant (X.obj d) := cofibrant_target (latchingMap X d)
  have : Cofibration l := cofibration_of_isPushout hP.flip
  rw [← hl]
  infer_instance

end Cofibrations

/-- Corollary 9.3.6(2), without finiteness assumptions, by duality. -/
theorem IsReedyFibration.fibration_app_small
    {D : Type w} [SmallCategory D] [IsInverse D] {M : Type u} [Category.{v} M]
    [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]
    [ABCPrefibrationCategory M]
    (h5 : CoproductCofibrationAxiom.{w} Mᵒᵖ) (h6 : SequentialCofibrationAxiom Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] {f : X ⟶ Y}
    (hf : IsReedyFibration f) (d : D) :
    Fibration (matchingObjMap f d) ∧ Fibration (f.app d) := by
  obtain ⟨h₁, h₂⟩ := IsReedyCofibration.cofibration_app_small h5 h6 hf (Opposite.op d)
  exact ⟨(fibration_unop_iff _).2 h₁, (cofibration_op_iff _).1 h₂⟩

section Pushouts
variable {D : Type w} [SmallCategory D] [IsDirect D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory.{w} M]
/-- Pushouts of Reedy cofibrations exist pointwise. -/
lemma hasPushout_app_small {A B C : D ⥤ M} [∀ e, HasColimit (latchingDiagram A e)]
    [∀ e, HasColimit (latchingDiagram B e)] [∀ e, HasColimit (latchingDiagram C e)]
    {i : A ⟶ B} (f : A ⟶ C) (hi : IsReedyCofibration i) (hC : IsReedyCofibrant C) (e : D) :
    HasPushout (i.app e) (f.app e) := by
  have := hi.1.isCofibrant_obj e
  have := hC.isCofibrant_obj e
  have := (hi.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom e).2
  exact hasPushout _ _

/-- **Theorem 9.2.4(1)(a)**, the pushout axiom CF3(1). The pushout of a Reedy
cofibration along a map to a Reedy cofibrant diagram is a Reedy cofibration. -/
theorem IsReedyCofibration.isPushout_small {A B C E : D ⥤ M} [∀ e, HasColimit (latchingDiagram A e)]
    [∀ e, HasColimit (latchingDiagram B e)] [∀ e, HasColimit (latchingDiagram C e)]
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ E} {j : C ⟶ E} (sq : IsPushout i f g j)
    (hi : IsReedyCofibration i) (hC : IsReedyCofibrant C) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram E e)), IsReedyCofibration j := by
  have hT (e : D) := isPushout_app sq (hasPushout_app_small f hi hC) e
  have hLP (d : D) : HasPushout (latchingObjMap i d) (latchingObjMap f d) := by
    have := (hi.1 d).1
    have := (hC d).1
    have := (hi.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom d).1
    exact hasPushout _ _
  have hL (d : D) := colimit_isPushout_of_pointwise (α := latchingNat i d) (β := latchingNat f d)
    (γ := latchingNat g d) (δ := latchingNat j d) (fun k ↦ hT k.obj.left)
    (IsPushout.of_hasPushout (latchingObjMap i d) (latchingObjMap f d))
  have hE (d : D) : HasColimit (latchingDiagram E d) := (hL d).fst
  refine ⟨hE, ?_⟩
  have key (d : D) : (IsCofibrant (latchingObj E d) ∧ Cofibration (latchingMap E d)) ∧
      ∃ (P : M) (l : C.obj d ⟶ P) (r : latchingObj E d ⟶ P) (c : P ⟶ E.obj d),
        IsPushout (latchingMap C d) (latchingObjMap j d) l r ∧ l ≫ c = j.app d ∧
          r ≫ c = latchingMap E d ∧ Cofibration c := by
    have hA : IsPushout (latchingObjMap i d) (latchingObjMap f d) (latchingObjMap g d)
        (latchingObjMap j d) := (hL d).snd
    obtain ⟨hLA, hiA⟩ := hi.1 d
    obtain ⟨hLB, hiB⟩ := hi.2.1 d
    obtain ⟨hLC, hiC⟩ := hC d
    have := hi.1.isCofibrant_obj d
    have := hC.isCofibrant_obj d
    obtain ⟨hLi, hid⟩ := hi.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom d
    have hLj : Cofibration (latchingObjMap j d) := cofibration_of_isPushout hA
    have : HasPushout (latchingObjMap j d) (latchingMap C d) := hasPushout _ _
    have h₁₂ : latchingObjMap i d ≫ latchingMap B d = latchingMap A d ≫ i.app d :=
      latchingObjMap_latchingMap i d
    have : HasPushout (latchingObjMap i d) (latchingMap A d) := hasPushout _ _
    obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hi.2.2 d
    have : Cofibration (pushout.desc (latchingMap B d) (i.app d) h₁₂) := by
      have : Cofibration (pushout.inl (latchingObjMap i d) (latchingMap A d)) :=
        cofibration_of_isPushout (IsPushout.of_hasPushout _ _).flip
      have : IsCofibrant (pushout (latchingObjMap i d) (latchingMap A d)) :=
        cofibrant_target (pushout.inl (latchingObjMap i d) (latchingMap A d))
      have : Cofibration hP.flip.isoPushout.inv := cofibration_of_isIso _
      rw [show pushout.desc (latchingMap B d) (i.app d) h₁₂ = hP.flip.isoPushout.inv ≫ c by
        apply pushout.hom_ext <;> simp [hl, hr]]
      infer_instance
    obtain ⟨-, h₄, hcomp⟩ := gluing_cofibration hA (hT d) h₁₂ (latchingObjMap_latchingMap f d)
      (latchingObjMap_latchingMap g d) (latchingObjMap_latchingMap j d)
    have : IsCofibrant (latchingObj E d) := cofibrant_target (latchingObjMap j d)
    exact ⟨⟨this, h₄⟩, _, _, _, _, (IsPushout.of_hasPushout _ _).flip, pushout.inr_desc _ _ _,
      pushout.inl_desc _ _ _, hcomp⟩
  exact ⟨hC, fun d ↦ (key d).1, fun d ↦ (key d).2⟩

/-- CF3(2) for arbitrary small Reedy diagrams: a pushout of a pointwise
weak equivalence along a Reedy cofibration is a pointwise weak equivalence. -/
theorem IsReedyCofibration.weakEquivalence_isPushout_small
    {A B C E : D ⥤ M} [∀ e, HasColimit (latchingDiagram A e)]
    [∀ e, HasColimit (latchingDiagram B e)] [∀ e, HasColimit (latchingDiagram C e)]
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ E} {j : C ⟶ E} (sq : IsPushout i f g j)
    (hi : IsReedyCofibration i) (hC : IsReedyCofibrant C)
    (hw : ∀ d, WeakEquivalence (i.app d)) : ∀ d, WeakEquivalence (j.app d) := by
  intro d
  have hT := isPushout_app sq (hasPushout_app_small f hi hC) d
  have := hi.1.isCofibrant_obj d
  have := hC.isCofibrant_obj d
  have := (hi.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom d).2
  have := hw d
  exact weakEquivalence_of_isPushout hT

end Pushouts

end ABCCofibrations

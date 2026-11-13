/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallFactorization
public import ABCCofibrations.ReedySmallStructure
public import ABCCofibrations.PointwiseCofibrationCategory

/-! # Diagram precofibration structures for arbitrary small direct categories

The CF1–CF4 part of Theorem 9.2.4(1)(a),(b). The ambient ABC cofibration
category supplies the coproducts required by infinite latching categories.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory
namespace ReedyDiagram
variable (D : Type w) [SmallCategory D] [IsDirect D]
  (M : Type u) [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]

/-- **Theorem 9.2.4(1)(a)** (axioms CF1–CF4), for arbitrary small direct categories: the
diagrams over `D` in an ABC cofibration category, with pointwise weak equivalences
and Reedy cofibrations, form a precofibration category. -/
instance (priority := 100) precofibrationCategory_small :
    ABCPrecofibrationCategory (ReedyDiagram D M) where
  initial_cofibrant := isCofibrant_of_isReedyCofibrant isReedyCofibrant_initial
  cofibrations_comp := ⟨fun {X Y Z} f g hf hg ↦ by
    obtain ⟨hX, _, hf⟩ := hf
    obtain ⟨_, hZ, hg⟩ := hg
    exact ⟨hX, hZ, IsReedyCofibration.comp hf hg⟩⟩
  weakEquivalence_of_isIso {X Y} f hf := ⟨fun e ↦ by
    have : @IsIso (D ⥤ M) _ X Y f := hf
    have : IsIso (NatTrans.app f e) := NatIso.isIso_app_of_isIso f e
    exact weakEquivalence_of_isIso _⟩
  cofibration_of_isIso {X Y} f hf hA := by
    obtain ⟨_, hA⟩ := isReedyCofibrant_of_isCofibrant hA
    have : @IsIso (D ⥤ M) _ X Y f := hf
    obtain ⟨_, h⟩ := isReedyCofibration_of_isIso (D := D) (M := M) (X := X) (Y := Y) f hA
    exact ⟨⟨inferInstance, inferInstance, h⟩⟩
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout {A B C} i f hA hC hi := by
    obtain ⟨_, _, hi⟩ := (cofibration_iff i).1 hi
    obtain ⟨_, hC⟩ := isReedyCofibrant_of_isCofibrant hC
    exact hasPushout_of_pointwise i f (hasPushout_app_small f hi hC)
  cofibration_of_isPushout {A B C E i f g j} h hA hC hi := by
    obtain ⟨_, _, hi⟩ := (cofibration_iff i).1 hi
    obtain ⟨_, hC⟩ := isReedyCofibrant_of_isCofibrant hC
    obtain ⟨_, hj⟩ := IsReedyCofibration.isPushout_small h hi hC
    exact ⟨⟨inferInstance, inferInstance, hj⟩⟩
  weakEquivalence_of_isPushout {A B C E i f g j} h hA hC hi hw := by
    obtain ⟨_, _, hi⟩ := (cofibration_iff i).1 hi
    obtain ⟨_, hC⟩ := isReedyCofibrant_of_isCofibrant hC
    refine ⟨fun e ↦ ?_⟩
    have hT := isPushout_app h (hasPushout_app_small f hi hC) e
    have := hi.1.isCofibrant_obj e
    have := hC.isCofibrant_obj e
    have := (hi.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom e).2
    have : WeakEquivalence (NatTrans.app i e) := (weakEquivalence_iff i).1 hw e
    exact weakEquivalence_of_isPushout hT
  factorization {A B} f hA := by
    obtain ⟨_, hA⟩ := isReedyCofibrant_of_isCofibrant hA
    obtain ⟨Y', _, f', r, hf', hr, hfr⟩ :=
      reedy_factorization_small ABCCofibrationCategory.coproductCofibrationAxiom hA f
    exact ⟨Y', f', r, ⟨⟨inferInstance, inferInstance, hf'⟩⟩, ⟨hr⟩, hfr⟩

end ReedyDiagram

namespace PointwiseDiagram
variable {D : Type w} [SmallCategory D] [IsDirect D]
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]

/-- The factorization axiom for the pointwise structure. -/
lemma factorization_small {A B : PointwiseDiagram D M} (f : A ⟶ B) [hA : IsCofibrant A] :
    ∃ (Z : PointwiseDiagram D M) (i : A ⟶ Z) (p : Z ⟶ B),
      Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f := by
  obtain ⟨X', _, a, q, ha, hq, -⟩ :=
    reedy_factorization_small ABCCofibrationCategory.coproductCofibrationAxiom
      (X := (⊥_ (ReedyDiagram D M) : D ⥤ M))
    ReedyDiagram.isReedyCofibrant_initial (initial.to (A : ReedyDiagram D M))
  have hX' : IsReedyCofibrant X' := ha.2.1
  obtain ⟨Y', _, g, s, hg, hs, hgs⟩ :=
    reedy_factorization_small ABCCofibrationCategory.coproductCofibrationAxiom hX' (q ≫ f)
  have hp (e : D) : HasPushout (g.app e) (q.app e) := by
    have := (hg.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom e).2
    have := hX'.isCofibrant_obj e
    have := (isCofibrant_iff A).1 hA e
    exact hasPushout _ _
  have hpo : HasPushout g q := hasPushout_of_pointwise g q hp
  have hT (e : D) := isPushout_app (IsPushout.of_hasPushout g q) hp e
  let f₀ : (A : D ⥤ M) ⟶ (B : D ⥤ M) := f
  refine ⟨(pushout g q : D ⥤ M), @pushout.inr (D ⥤ M) _ _ _ _ g q hpo,
    @pushout.desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs, ⟨fun e ↦ ?_⟩, ⟨fun e ↦ ?_⟩,
    @pushout.inr_desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs⟩
  · have := (hg.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom e).2
    have := hX'.isCofibrant_obj e
    have := (isCofibrant_iff A).1 hA e
    exact cofibration_of_isPushout (hT e)
  · have := (hg.cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom e).2
    have := hX'.isCofibrant_obj e
    have := (isCofibrant_iff A).1 hA e
    have := hq e
    have := hs e
    have : WeakEquivalence ((pushout.inl g q).app e) :=
      weakEquivalence_of_isPushout_of_cofibration (hT e)
    have hw : WeakEquivalence ((pushout.inl g q ≫
        @pushout.desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs).app e) :=
      (congrArg (fun φ ↦ WeakEquivalence (NatTrans.app φ e))
        (@pushout.inl_desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs)).mpr (hs e)
    have : WeakEquivalence ((pushout.inl g q).app e ≫
        (@pushout.desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs).app e) := hw
    exact weakEquivalence_of_precomp ((pushout.inl g q).app e) _

/-- **Theorem 9.2.4(1)(b)** (axioms CF1–CF4), for arbitrary small direct categories: the
diagrams over `D` in an ABC cofibration category, with pointwise weak equivalences
and pointwise cofibrations, form a precofibration category. -/
instance (priority := 100) precofibrationCategory_small :
    ABCPrecofibrationCategory (PointwiseDiagram D M) where
  initial_cofibrant := (isCofibrant_iff _).2 fun e ↦ by
    let i := (isInitialInitialObj (M := M) e).uniqueUpToIso initialIsInitial
    have := cofibration_of_isIso i.inv
    exact cofibrant_target i.inv
  cofibrations_comp := ⟨fun f g hf hg e ↦ by
    have := hf e
    have := hg e
    change Cofibration (NatTrans.app f e ≫ NatTrans.app g e)
    infer_instance⟩
  weakEquivalence_of_isIso {X Y} f hf := ⟨fun e ↦ by
    have : @IsIso (D ⥤ M) _ X Y f := hf
    have : IsIso (NatTrans.app f e) := NatIso.isIso_app_of_isIso f e
    exact weakEquivalence_of_isIso _⟩
  cofibration_of_isIso {X Y} f hf hX := ⟨fun e ↦ by
    have : @IsIso (D ⥤ M) _ X Y f := hf
    have : IsIso (NatTrans.app f e) := NatIso.isIso_app_of_isIso f e
    have := (isCofibrant_iff X).1 hX e
    exact cofibration_of_isIso _⟩
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout i f hA hC hi := hasPushout_of_pointwise i f (hasPushout_of_cofibrant i f)
  cofibration_of_isPushout {A B C E i f g j} h hA hC hi := ⟨fun e ↦ by
    have hT := isPushout_app h (hasPushout_of_cofibrant i f) e
    have := (isCofibrant_iff A).1 hA e
    have := (isCofibrant_iff C).1 hC e
    have : Cofibration (NatTrans.app i e) := hi.mem e
    exact cofibration_of_isPushout hT⟩
  weakEquivalence_of_isPushout {A B C E i f g j} h hA hC hi hw := ⟨fun e ↦ by
    have hT := isPushout_app h (hasPushout_of_cofibrant i f) e
    have := (isCofibrant_iff A).1 hA e
    have := (isCofibrant_iff C).1 hC e
    have : Cofibration (NatTrans.app i e) := hi.mem e
    have : WeakEquivalence (NatTrans.app i e) := hw.mem e
    exact weakEquivalence_of_isPushout hT⟩
  factorization f _ := factorization_small f

end PointwiseDiagram
end ABCCofibrations

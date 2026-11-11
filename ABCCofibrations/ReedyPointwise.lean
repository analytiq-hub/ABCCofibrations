/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyFibStructure
public import ABCCofibrations.Extension

/-!
# The pointwise cofibration structure (Theorem 9.2.4(1)(b))

For a finite direct category `D` and a precofibration category `M`, diagrams
with pointwise weak equivalences and pointwise cofibrations form a
precofibration category. Everything except the factorization is pointwise; a
factorization of `f : X ⟶ Y` comes from a Reedy cofibrant replacement
`X' ⟶ X`, a Reedy factorization `X' ⟶ Y' ⟶ Y`, and the pushout
`Y' ⊔_{X'} X`.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- The category of `D`-diagrams in `M`, to carry the pointwise structure. -/
def PointwiseDiagram (D : Type*) [Category D] (M : Type*) [Category M] : Type _ := D ⥤ M

namespace PointwiseDiagram

variable (D : Type w) [SmallCategory D] (M : Type u₂) [Category.{v₂} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]

instance : Category (PointwiseDiagram D M) := inferInstanceAs (Category (D ⥤ M))

instance : HasInitial (PointwiseDiagram D M) := inferInstanceAs (HasInitial (D ⥤ M))

instance : CategoryWithWeakEquivalences (PointwiseDiagram D M) where
  weakEquivalences := fun _ _ f ↦ ∀ e, WeakEquivalence (NatTrans.app f e)

instance : CategoryWithCofibrations (PointwiseDiagram D M) where
  cofibrations := fun _ _ f ↦ ∀ e, Cofibration (NatTrans.app f e)

variable {D M} [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- The values of the initial diagram are initial. -/
noncomputable def isInitialInitialObj (e : D) :
    IsInitial ((⊥_ (PointwiseDiagram D M) : D ⥤ M).obj e) :=
  initialIsInitial.isInitialObj ((evaluation D M).obj e)

lemma isCofibrant_iff (X : PointwiseDiagram D M) :
    IsCofibrant X ↔ ∀ e, IsCofibrant ((X : D ⥤ M).obj e) := by
  have key (e : D) : Cofibration (NatTrans.app (initial.to X) e) ↔
      IsCofibrant ((X : D ⥤ M).obj e) := by
    let i := (isInitialInitialObj (M := M) e).uniqueUpToIso initialIsInitial
    have : IsCofibrant ((⊥_ (PointwiseDiagram D M) : D ⥤ M).obj e) := by
      have := cofibration_of_isIso i.inv
      exact cofibrant_target i.inv
    have hi : Cofibration i.inv := cofibration_of_isIso _
    have hfac : i.inv ≫ NatTrans.app (initial.to X) e = initial.to _ := initialIsInitial.hom_ext _ _
    constructor
    · intro h
      exact cofibrant_target (NatTrans.app (initial.to X) e)
    · intro h
      have : Cofibration (initial.to ((X : D ⥤ M).obj e)) := h
      have hj : Cofibration i.hom := cofibration_of_isIso _
      rw [show NatTrans.app (initial.to X) e = i.hom ≫ initial.to _ by
        rw [← hfac, Iso.hom_inv_id_assoc]]
      infer_instance
  exact ⟨fun h e ↦ (key e).1 (h.mem e), fun h ↦ ⟨fun e ↦ (key e).2 (h e)⟩⟩

instance : (weakEquivalences (PointwiseDiagram D M)).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg e := by
    have := hf e
    have := hg e
    change WeakEquivalence (NatTrans.app f e ≫ NatTrans.app g e)
    infer_instance
  of_postcomp f g hg hfg e := by
    have := hg e
    have : WeakEquivalence (NatTrans.app f e ≫ NatTrans.app g e) := hfg e
    exact weakEquivalence_of_postcomp _ (NatTrans.app g e)
  of_precomp f g hf hfg e := by
    have := hf e
    have : WeakEquivalence (NatTrans.app f e ≫ NatTrans.app g e) := hfg e
    exact weakEquivalence_of_precomp (NatTrans.app f e) _

lemma hasPushout_of_cofibrant {A B C : PointwiseDiagram D M} (i : A ⟶ B) (f : A ⟶ C)
    [hA : IsCofibrant A] [hC : IsCofibrant C] [hi : Cofibration i] (e : D) :
    HasPushout (NatTrans.app i e) (NatTrans.app f e) := by
  have := (isCofibrant_iff A).1 hA e
  have := (isCofibrant_iff C).1 hC e
  have : Cofibration (NatTrans.app i e) := hi.mem e
  exact hasPushout _ _

variable [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsDirect D]

/-- The factorization axiom for the pointwise structure. -/
lemma factorization' {A B : PointwiseDiagram D M} (f : A ⟶ B) [hA : IsCofibrant A] :
    ∃ (Z : PointwiseDiagram D M) (i : A ⟶ Z) (p : Z ⟶ B),
      Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f := by
  obtain ⟨X', _, a, q, ha, hq, -⟩ := reedy_factorization (X := (⊥_ (ReedyDiagram D M) : D ⥤ M))
    ReedyDiagram.isReedyCofibrant_initial (initial.to (A : ReedyDiagram D M))
  have hX' : IsReedyCofibrant X' := ha.2.1
  obtain ⟨Y', _, g, s, hg, hs, hgs⟩ := reedy_factorization hX' (q ≫ f)
  have hp (e : D) : HasPushout (g.app e) (q.app e) := by
    have := (hg.cofibration_app e).2
    have := hX'.isCofibrant_obj e
    have := (isCofibrant_iff A).1 hA e
    exact hasPushout _ _
  have hpo : HasPushout g q := hasPushout_of_pointwise g q hp
  have hT (e : D) := isPushout_app (IsPushout.of_hasPushout g q) hp e
  let f₀ : (A : D ⥤ M) ⟶ (B : D ⥤ M) := f
  refine ⟨(pushout g q : D ⥤ M), @pushout.inr (D ⥤ M) _ _ _ _ g q hpo,
    @pushout.desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs, ⟨fun e ↦ ?_⟩, ⟨fun e ↦ ?_⟩,
    @pushout.inr_desc (D ⥤ M) _ _ _ _ _ g q hpo s f₀ hgs⟩
  · have := (hg.cofibration_app e).2
    have := hX'.isCofibrant_obj e
    have := (isCofibrant_iff A).1 hA e
    exact cofibration_of_isPushout (hT e)
  · have := (hg.cofibration_app e).2
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

/-- **Theorem 9.2.4(1)(b)** (axioms CF1–CF4), for finite direct categories: the
diagrams over `D` in a precofibration category, with pointwise weak equivalences
and pointwise cofibrations, form a precofibration category. -/
instance precofibrationCategory : ABCPrecofibrationCategory (PointwiseDiagram D M) where
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
  factorization f _ := factorization' f

end PointwiseDiagram

end ABCCofibrations

namespace ABCCofibrations

/-- The category of `D`-diagrams in `M`, to carry the pointwise fibration structure. -/
def PointwiseFibDiagram (D : Type*) [Category D] (M : Type*) [Category M] : Type _ := D ⥤ M

namespace PointwiseFibDiagram

variable (D : Type w) [SmallCategory D] (M : Type u₂) [Category.{v₂} M]
  [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]

instance : Category (PointwiseFibDiagram D M) := inferInstanceAs (Category (D ⥤ M))

instance : HasTerminal (PointwiseFibDiagram D M) := inferInstanceAs (HasTerminal (D ⥤ M))

instance : CategoryWithWeakEquivalences (PointwiseFibDiagram D M) where
  weakEquivalences := fun _ _ f ↦ ∀ e, WeakEquivalence (NatTrans.app f e)

instance : CategoryWithFibrations (PointwiseFibDiagram D M) where
  fibrations := fun _ _ f ↦ ∀ e, Fibration (NatTrans.app f e)

variable [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsInverse D] [ABCPrefibrationCategory M]

/-- **Theorem 9.2.4(2)(b)** (axioms F1–F4), for finite inverse categories: the
diagrams over `D` in a prefibration category, with pointwise weak equivalences
and pointwise fibrations, form a prefibration category. -/
theorem prefibrationCategory : ABCPrefibrationCategory (PointwiseFibDiagram D M) := by
  refine ABCPrecofibrationCategory.of_equivalence (D' := PointwiseDiagram Dᵒᵖ Mᵒᵖ)
    (show (PointwiseFibDiagram D M)ᵒᵖ ≌ PointwiseDiagram Dᵒᵖ Mᵒᵖ from
      Functor.opUnopEquiv D M) ?_ ?_
  · ext X Y f
    change (∀ e, Fibration _) ↔ ∀ e, Cofibration _
    exact ⟨fun h e ↦ (cofibration_op_iff _).2 (h e.unop),
      fun h e ↦ (cofibration_op_iff _).1 (h (Opposite.op e))⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (Opposite.op e))⟩

end PointwiseFibDiagram

end ABCCofibrations

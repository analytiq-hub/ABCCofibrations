/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Factorization
public import ABCCofibrations.FibrationBasic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Order.SuccPred.Basic

/-!
# Left and right exact functors (Definition 9.7.1, Lemma 9.7.2)

A functor between precofibration categories is *left exact* if it preserves the
initial object, cofibrations and trivial cofibrations, pushouts of cofibrations
along maps to cofibrant objects, and colimits of transfinite sequences of
cofibrations. A functor between prefibration categories is *right exact* if its
opposite is left exact.

The comparison isomorphisms of the paper are expressed with mathlib's
`PreservesColimit`. The transfinite sequences are indexed by well-ordered types
`J : Type w` with a bottom element and a successor function, with cofibrations
as successor maps; the paper's continuity at limit ordinals is not required of
the sequences, so the condition here is slightly stronger than the paper's.
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

open ABCPrecofibrationCategory

section Left

variable {M₁ : Type u₁} [Category.{v₁} M₁] [CategoryWithCofibrations M₁]
  [CategoryWithWeakEquivalences M₁] [HasInitial M₁]
  {M₂ : Type u₂} [Category.{v₂} M₂] [CategoryWithCofibrations M₂]
  [CategoryWithWeakEquivalences M₂] [HasInitial M₂]
  {M₃ : Type u₃} [Category.{v₃} M₃] [CategoryWithCofibrations M₃]
  [CategoryWithWeakEquivalences M₃] [HasInitial M₃]

/-- **Definition 9.7.1(1).** A left exact functor. -/
structure LeftExact (t : M₁ ⥤ M₂) : Prop where
  /-- `t` preserves the initial object. -/
  preservesInitial : PreservesColimit (Functor.empty.{0} M₁) t
  /-- `t` preserves cofibrations. -/
  cofibration ⦃A B : M₁⦄ (f : A ⟶ B) [Cofibration f] : Cofibration (t.map f)
  /-- `t` preserves trivial cofibrations. -/
  weakEquivalence ⦃A B : M₁⦄ (f : A ⟶ B) [Cofibration f] [WeakEquivalence f] :
    WeakEquivalence (t.map f)
  /-- `t` preserves pushouts of cofibrations along maps to cofibrant objects. -/
  preservesPushout ⦃A B D : M₁⦄ (f : A ⟶ B) (g : A ⟶ D) [Cofibration f] [IsCofibrant D] :
    PreservesColimit (span f g) t
  /-- `t` preserves colimits of transfinite sequences of cofibrations. -/
  preservesSequence (J : Type w) [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
    (F : J ⥤ M₁) (hF : ∀ j, Cofibration (F.map (homOfLE (Order.le_succ j)))) :
    PreservesColimit F t

namespace LeftExact

variable [ABCPrecofibrationCategory M₂] {t : M₁ ⥤ M₂}

/-- Left exact functors preserve cofibrant objects. -/
theorem isCofibrant (ht : LeftExact.{w} t) {A : M₁} (hA : IsCofibrant A) :
    IsCofibrant (t.obj A) := by
  have : Cofibration (initial.to A) := hA
  have := ht.cofibration (initial.to A)
  have := ht.preservesInitial
  let hI : IsInitial (t.obj (⊥_ M₁)) := initialIsInitial.isInitialObj t
  have : IsIso (initial.to (t.obj (⊥_ M₁))) :=
    ⟨hI.to (⊥_ M₂), initialIsInitial.hom_ext _ _, hI.hom_ext _ _⟩
  have : Cofibration (initial.to (t.obj (⊥_ M₁))) := cofibration_of_isIso _
  have h : initial.to (t.obj A) = initial.to (t.obj (⊥_ M₁)) ≫ t.map (initial.to A) :=
    initialIsInitial.hom_ext _ _
  change Cofibration (initial.to (t.obj A))
  rw [h]
  infer_instance

variable [ABCPrecofibrationCategory M₁]

/-- **Lemma 9.7.2(2).** Left exact functors preserve weak equivalences between
cofibrant objects (by Brown factorization). -/
theorem weakEquivalence_map (ht : LeftExact.{w} t) {A B : M₁} [IsCofibrant A] [IsCofibrant B]
    (f : A ⟶ B) [WeakEquivalence f] : WeakEquivalence (t.map f) := by
  obtain ⟨Z, i, p, s, hZ, hi, hp, hs, hsw, hip, hsp⟩ := exists_brown_factorization f
  have : WeakEquivalence i := weakEquivalence_of_postcomp_of_fac hip
  have := ht.weakEquivalence i
  have := ht.weakEquivalence s
  have : WeakEquivalence (t.map s ≫ t.map p) := by
    rw [← t.map_comp, hsp, t.map_id]
    exact ABCPrecofibrationCategory.weakEquivalence_of_isIso _
  have : WeakEquivalence (t.map p) := weakEquivalence_of_precomp (t.map s) (t.map p)
  rw [← hip, t.map_comp]
  infer_instance

omit [ABCPrecofibrationCategory M₁] in
/-- **Lemma 9.7.2(1)**, left exact case. Left exact functors are stable under
composition. -/
theorem comp [ABCPrecofibrationCategory M₃] {s : M₂ ⥤ M₃} (ht : LeftExact.{w} t)
    (hs : LeftExact.{w} s) : LeftExact.{w} (t ⋙ s) where
  preservesInitial := by
    have := ht.preservesInitial
    have := hs.preservesInitial
    have : PreservesColimit (Functor.empty.{0} M₁ ⋙ t) s :=
      preservesColimit_of_iso_diagram s
        (Functor.emptyExt (Functor.empty.{0} M₂) (Functor.empty.{0} M₁ ⋙ t))
    infer_instance
  cofibration A B f _ := by
    have := ht.cofibration f
    exact hs.cofibration (t.map f)
  weakEquivalence A B f _ _ := by
    have := ht.cofibration f
    have := ht.weakEquivalence f
    exact hs.weakEquivalence (t.map f)
  preservesPushout A B D f g _ hD := by
    have := ht.preservesPushout f g
    have := ht.cofibration f
    have := ht.isCofibrant hD
    have : PreservesColimit (span ((span f g ⋙ t).map WalkingSpan.Hom.fst)
        ((span f g ⋙ t).map WalkingSpan.Hom.snd)) s := hs.preservesPushout (t.map f) (t.map g)
    have : PreservesColimit (span f g ⋙ t) s :=
      preservesColimit_of_iso_diagram s (diagramIsoSpan _).symm
    infer_instance
  preservesSequence J _ _ _ _ F hF := by
    have := ht.preservesSequence J F hF
    have := hs.preservesSequence J (F ⋙ t) fun j ↦ by
      have := hF j
      exact ht.cofibration _
    infer_instance

end LeftExact

end Left

section Right

variable {M₁ : Type u₁} [Category.{v₁} M₁] [CategoryWithFibrations M₁]
  [CategoryWithWeakEquivalences M₁] [HasTerminal M₁]
  {M₂ : Type u₂} [Category.{v₂} M₂] [CategoryWithFibrations M₂]
  [CategoryWithWeakEquivalences M₂] [HasTerminal M₂]
  {M₃ : Type u₃} [Category.{v₃} M₃] [CategoryWithFibrations M₃]
  [CategoryWithWeakEquivalences M₃] [HasTerminal M₃]

/-- **Definition 9.7.1(2).** A right exact functor between prefibration
categories: its opposite is left exact. Explicitly, it preserves the terminal
object, fibrations and trivial fibrations, pullbacks of fibrations along maps
from fibrant objects, and limits of transfinite inverse sequences of
fibrations. -/
abbrev RightExact (t : M₁ ⥤ M₂) : Prop := LeftExact.{w} t.op

namespace RightExact

/-- **Lemma 9.7.2(1)**, right exact case. Right exact functors are stable under
composition. -/
theorem comp [ABCPrefibrationCategory M₂] [ABCPrefibrationCategory M₃] {t : M₁ ⥤ M₂}
    {s : M₂ ⥤ M₃} (ht : RightExact.{w} t) (hs : RightExact.{w} s) :
    RightExact.{w} (t ⋙ s) :=
  LeftExact.comp ht hs

/-- **Lemma 9.7.2(3).** Right exact functors preserve weak equivalences between
fibrant objects. -/
theorem weakEquivalence_map [ABCPrefibrationCategory M₁] [ABCPrefibrationCategory M₂]
    {t : M₁ ⥤ M₂} (ht : RightExact.{w} t) {A B : M₁} [IsFibrant A] [IsFibrant B]
    (f : A ⟶ B) [WeakEquivalence f] : WeakEquivalence (t.map f) := by
  have : WeakEquivalence f.op := (weakEquivalences_op_iff _).2 ‹_›
  exact (weakEquivalences_op_iff _).1 (LeftExact.weakEquivalence_map ht f.op)

end RightExact

end Right

end ABCCofibrations

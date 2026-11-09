/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic

/-!
# ABC prefibration categories by duality

An ABC prefibration category is precisely an ABC precofibration category on
the opposite category, using mathlib's opposite morphism classes. Only
F1–F4 are imposed; no model category or lifting axioms are assumed.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- Axioms F1–F4, expressed as CF1–CF4 on the opposite category.
The terminal object and the ambient fibrations and weak equivalences are
supplied separately, exactly as on the cofibration side. -/
abbrev ABCPrefibrationCategory (C : Type u) [Category.{v} C]
    [CategoryWithFibrations C] [CategoryWithWeakEquivalences C] [HasTerminal C] : Prop :=
  ABCPrecofibrationCategory Cᵒᵖ

namespace ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- F1: isomorphisms are weak equivalences. -/
theorem weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] :
    WeakEquivalence f :=
  (weakEquivalences_op_iff f).1 (ABCPrecofibrationCategory.weakEquivalence_of_isIso f.op)

/-- Fibrancy is cofibrancy in the opposite category. -/
theorem isFibrant_iff_isCofibrant_op (A : C) :
    IsFibrant A ↔ IsCofibrant (Opposite.op A) := by
  change Fibration (terminal.from A) ↔ Cofibration (initial.to (Opposite.op A))
  let h := initialOpOfTerminal (terminalIsTerminal (C := C))
  let e : (⊥_ Cᵒᵖ) ≅ Opposite.op (⊤_ C) := initialIsInitial.uniqueUpToIso h
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.hom
  let := ABCPrecofibrationCategory.cofibrant_target e.hom
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.inv
  have he : e.hom ≫ (terminal.from A).op = initial.to (Opposite.op A) :=
    initialIsInitial.hom_ext _ _
  have he' : e.inv ≫ initial.to (Opposite.op A) = (terminal.from A).op := h.hom_ext _ _
  constructor
  · intro hf
    let := hf
    rw [← he]
    infer_instance
  · intro hf
    let := hf
    apply (cofibration_op_iff (terminal.from A)).1
    rw [← he']
    infer_instance

instance isCofibrant_op (A : C) [IsFibrant A] : IsCofibrant (Opposite.op A) :=
  (isFibrant_iff_isCofibrant_op A).1 inferInstance

/-- F1: the terminal object is fibrant. -/
instance terminal_fibrant : IsFibrant (⊤_ C) := by
  let h := initialOpOfTerminal (terminalIsTerminal (C := C))
  let e : (⊥_ Cᵒᵖ) ≅ Opposite.op (⊤_ C) := initialIsInitial.uniqueUpToIso h
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.hom
  exact (isFibrant_iff_isCofibrant_op (⊤_ C)).2
    (ABCPrecofibrationCategory.cofibrant_target e.hom)

/-- F1: fibrations compose, including with nonfibrant target. -/
instance fibrations_comp : (fibrations C).IsStableUnderComposition := by
  let : ((fibrations C).op).IsStableUnderComposition :=
    inferInstanceAs (cofibrations Cᵒᵖ).IsStableUnderComposition
  exact inferInstanceAs ((fibrations C).op).unop.IsStableUnderComposition

/-- F2: weak equivalences satisfy two out of three. -/
instance weakEquivalences_twoOutOfThree :
    (weakEquivalences C).HasTwoOutOfThreeProperty := by
  let : ((weakEquivalences C).op).HasTwoOutOfThreeProperty :=
    inferInstanceAs (weakEquivalences Cᵒᵖ).HasTwoOutOfThreeProperty
  exact inferInstanceAs ((weakEquivalences C).op).unop.HasTwoOutOfThreeProperty

/-- A fibration with fibrant target has fibrant source. -/
theorem fibrant_source {A B : C} (p : A ⟶ B) [Fibration p] [IsFibrant B] :
    IsFibrant A :=
  (isFibrant_iff_isCofibrant_op A).2 (ABCPrecofibrationCategory.cofibrant_target p.op)

/-- A fibrant replacement, obtained by dualizing a cofibrant replacement. -/
theorem exists_fibrant_replacement (A : C) :
    ∃ (R : C) (r : A ⟶ R), IsFibrant R ∧ WeakEquivalence r := by
  obtain ⟨Q, q, hQ, hq⟩ := ABCPrecofibrationCategory.exists_cofibrant_replacement (Opposite.op A)
  exact ⟨Q.unop, q.unop, (isFibrant_iff_isCofibrant_op Q.unop).2 hQ,
    (weakEquivalences_unop_iff q).2 hq⟩

/-- F1: an isomorphism with fibrant target is a fibration. -/
theorem fibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] [IsFibrant B] :
    Fibration f :=
  (cofibration_op_iff f).1 (ABCPrecofibrationCategory.cofibration_of_isIso f.op)

/-- F4: factor a map with fibrant target as a weak equivalence followed by
a fibration, without a functorial choice. -/
theorem factorization {A B : C} (f : A ⟶ B) [IsFibrant B] :
    ∃ (Z : C) (w : A ⟶ Z) (p : Z ⟶ B),
      WeakEquivalence w ∧ Fibration p ∧ w ≫ p = f := by
  obtain ⟨Z, i, p, hi, hp, hip⟩ := ABCPrecofibrationCategory.factorization f.op
  exact ⟨Z.unop, p.unop, i.unop, (weakEquivalences_unop_iff p).2 hp,
    (fibration_unop_iff i).2 hi, congrArg Quiver.Hom.unop hip⟩

/-- F3: pullbacks along fibrations exist when the relevant objects are fibrant. -/
instance hasPullback {A B D : C} (p : A ⟶ B) (f : D ⟶ B)
    [IsFibrant B] [IsFibrant D] [Fibration p] : HasPullback p f :=
  (IsPushout.of_hasPushout p.op f.op).unop.flip.hasPullback

/-- F3: base change preserves fibrations under the restricted fibrancy
hypotheses. -/
theorem fibration_of_isPullback {A B D E : C} {p : A ⟶ B} {f : D ⟶ B}
    {g : E ⟶ A} {j : E ⟶ D} (h : IsPullback g j p f)
    [IsFibrant B] [IsFibrant D] [Fibration p] : Fibration j :=
  (cofibration_op_iff j).1 (ABCPrecofibrationCategory.cofibration_of_isPushout h.op.flip)

/-- F3: base change preserves trivial fibrations. -/
theorem weakEquivalence_of_isPullback {A B D E : C} {p : A ⟶ B} {f : D ⟶ B}
    {g : E ⟶ A} {j : E ⟶ D} (h : IsPullback g j p f)
    [IsFibrant B] [IsFibrant D] [Fibration p] [WeakEquivalence p] : WeakEquivalence j :=
  (weakEquivalences_op_iff j).1
    (ABCPrecofibrationCategory.weakEquivalence_of_isPushout h.op.flip)

end ABCPrefibrationCategory
end ABCCofibrations

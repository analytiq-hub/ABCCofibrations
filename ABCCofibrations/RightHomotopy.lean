/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.PathObject
public import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy

/-!
# Strict right homotopy and right homotopy under F1–F4

The native definitions of §6.3 use mathlib's good path objects. Right
homotopy allows a trivial fibration of the source, exactly dual to the
trivial-cofibration enlargement in our left-homotopy relation.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {A B : C} [IsFibrant B] [HasBinaryProduct B B]

/-- Strict right homotopy through a good path object, with unchanged source. -/
def StrictRightHomotopyRel (f g : A ⟶ B) : Prop :=
  ∃ P : PathObject B, P.IsGood ∧ Nonempty (P.RightHomotopy f g)

namespace StrictRightHomotopyRel

/-- Constant path homotopies give reflexivity. -/
theorem refl (f : A ⟶ B) : StrictRightHomotopyRel f f := by
  obtain ⟨P, hP⟩ := exists_good_pathObject B
  exact ⟨P, hP, ⟨PathObject.RightHomotopy.refl P f⟩⟩

/-- Reversing a good path object reverses the homotopy. -/
theorem symm {f g : A ⟶ B} (h : StrictRightHomotopyRel f g) :
    StrictRightHomotopyRel g f := by
  obtain ⟨P, hP, ⟨H⟩⟩ := h
  let := hP
  exact ⟨P.symm, good_pathObject_symm P, ⟨H.symm⟩⟩

omit [HasTerminal C] [ABCPrefibrationCategory C] [IsFibrant B] in
/-- Strict right homotopies can be precomposed by any map. -/
theorem precomp {f g : A ⟶ B} (h : StrictRightHomotopyRel f g)
    {D : C} (k : D ⟶ A) : StrictRightHomotopyRel (k ≫ f) (k ≫ g) := by
  obtain ⟨P, hP, ⟨H⟩⟩ := h
  exact ⟨P, hP, ⟨H.precomp k⟩⟩

omit [HasTerminal C] [ABCPrefibrationCategory C] [IsFibrant B] in
/-- Forgetting goodness gives mathlib's unrestricted path homotopy relation. -/
theorem to_mathlib {f g : A ⟶ B} (h : StrictRightHomotopyRel f g) :
    HomotopicalAlgebra.RightHomotopyRel f g := by
  obtain ⟨P, _, H⟩ := h
  exact ⟨P, H⟩

omit [IsFibrant B] in
/-- Strictly right-homotopic maps are weak equivalences simultaneously. -/
theorem weakEquivalence_iff {f g : A ⟶ B} (h : StrictRightHomotopyRel f g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  obtain ⟨P, _, ⟨H⟩⟩ := h
  let : (weakEquivalences C).ContainsIdentities :=
    ⟨fun X ↦ (weakEquivalence_of_isIso (𝟙 X)).mem⟩
  exact H.weakEquivalence_iff

end StrictRightHomotopyRel

/-- Right homotopy of §6.3: strict homotopy after a trivial fibration
of the source. -/
def RightHomotopyRel (f g : A ⟶ B) : Prop :=
  ∃ (A' : C) (a : A' ⟶ A), Fibration a ∧ WeakEquivalence a ∧
    StrictRightHomotopyRel (a ≫ f) (a ≫ g)

namespace RightHomotopyRel

variable [IsFibrant A]

omit [IsFibrant B] in
/-- Strict right homotopy is right homotopy, using the identity fibration. -/
theorem of_strict {f g : A ⟶ B} (h : StrictRightHomotopyRel f g) :
    RightHomotopyRel f g :=
  ⟨A, 𝟙 A, fibration_of_isIso (𝟙 A), weakEquivalence_of_isIso (𝟙 A),
    by simpa only [Category.id_comp] using h⟩

/-- Right homotopy is reflexive on maps between fibrant objects. -/
theorem refl (f : A ⟶ B) : RightHomotopyRel f f := of_strict (.refl f)

omit [IsFibrant A] in
/-- Right homotopy is symmetric. -/
theorem symm {f g : A ⟶ B} (h : RightHomotopyRel f g) : RightHomotopyRel g f := by
  obtain ⟨A', a, ha, haw, H⟩ := h
  exact ⟨A', a, ha, haw, H.symm⟩

omit [IsFibrant B] in
/-- Precomposition transports the source change by pulling back its trivial
fibration, with exactly the restricted F3 hypotheses. -/
theorem precomp {f g : A ⟶ B} (h : RightHomotopyRel f g)
    {D : C} [IsFibrant D] (k : D ⟶ A) : RightHomotopyRel (k ≫ f) (k ≫ g) := by
  obtain ⟨A', a, ha, haw, H⟩ := h
  let := ha
  let := haw
  let sq := IsPullback.of_hasPullback a k
  refine ⟨pullback a k, pullback.snd a k, fibration_of_isPullback sq,
    weakEquivalence_of_isPullback sq, ?_⟩
  simpa only [← Category.assoc, pullback.condition] using H.precomp (pullback.fst a k)

omit [IsFibrant A] [IsFibrant B] in
/-- Right-homotopic maps are weak equivalences simultaneously. -/
theorem weakEquivalence_iff {f g : A ⟶ B} (h : RightHomotopyRel f g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  obtain ⟨A', a, ha, haw, H⟩ := h
  let := haw
  exact (weakEquivalence_precomp_iff a f).symm.trans
    (H.weakEquivalence_iff.trans (weakEquivalence_precomp_iff a g))

end RightHomotopyRel
end ABCCofibrations.ABCPrefibrationCategory

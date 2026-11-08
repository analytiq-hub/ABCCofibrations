/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Gluing

/-!
# Excision in a precofibration category

Lemma 1.4.2(1) of Rădulescu-Banu, *Cofibrations in Homotopy Theory*:
cobase change along a cofibration preserves weak equivalences between
cofibrant objects. This follows from the gluing lemma under CF1–CF4.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- Excision (Lemma 1.4.2(1)), for any representative of the pushout. -/
theorem weakEquivalence_of_isPushout_of_cofibration
    {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E}
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] [WeakEquivalence f]
    (h : IsPushout i f g j) : WeakEquivalence g := by
  let := weakEquivalence_of_isIso (𝟙 A)
  let := weakEquivalence_of_isIso (𝟙 B)
  exact gluing_weakEquivalence (u₁ := 𝟙 A) (u₂ := 𝟙 B) (u₃ := f) (u₄ := g)
    (IsPushout.of_id_snd (f := i)) h
    (by simp) (by simp) (by simp) h.w

/-- The canonical pushout map preserves a weak equivalence along a cofibration. -/
theorem weakEquivalence_pushout_inl
    {A B D : C} (i : A ⟶ B) (f : A ⟶ D)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence (pushout.inl i f) :=
  weakEquivalence_of_isPushout_of_cofibration (IsPushout.of_hasPushout i f)

end ABCCofibrations.ABCPrecofibrationCategory

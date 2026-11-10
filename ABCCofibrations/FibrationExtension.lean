/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Extension
public import ABCCofibrations.FibrationBasic

/-!
# Cogluing and excision in prefibration categories

The fibration statements of the gluing lemma (Lemma 1.4.1(2)(b)) and of
excision (Lemma 1.4.2(2)), deduced from the cofibration statements in the
opposite category. A pullback square in `C` is a pushout square in `Cᵒᵖ`
(`IsPullback.op`), fibrations with fibrant target are cofibrations with
cofibrant source there, and weak equivalences are self-dual.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations.ABCPrefibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- **Lemma 1.4.2(2)** (excision). The base change of a weak equivalence `r`
between fibrant objects along a fibration `p` with fibrant target is a weak
equivalence, for any representative of the pullback. -/
theorem weakEquivalence_of_isPullback_of_fibration {P X B D : C} {fst : P ⟶ X}
    {snd : P ⟶ D} {p : X ⟶ B} {r : D ⟶ B} [IsFibrant B] [IsFibrant D] [Fibration p]
    [WeakEquivalence r] (h : IsPullback fst snd p r) : WeakEquivalence fst := by
  have : Cofibration p.op := (cofibration_op_iff _).2 ‹_›
  have : WeakEquivalence r.op := (weakEquivalences_op_iff _).2 ‹_›
  exact (weakEquivalences_op_iff _).1 (weakEquivalence_of_isPushout_of_cofibration h.op.flip)

/-- **Lemma 1.4.1(2)(b)** (cogluing lemma for weak equivalences). Given a map
`u` from a pullback square of `A`'s to a pullback square of `B`'s, in which the
maps `f₁₂`, `g₁₂` are fibrations and `A₁, A₃, B₁, B₃` are fibrant, if `u₁`,
`u₂`, `u₃` are weak equivalences then so is the induced map `u₄` of
pullbacks. -/
theorem cogluing_weakEquivalence {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C}
    [IsFibrant A₁] [IsFibrant A₃] [IsFibrant B₁] [IsFibrant B₃]
    {f₁₂ : A₂ ⟶ A₁} {f₁₃ : A₃ ⟶ A₁} {f₂₄ : A₄ ⟶ A₂} {f₃₄ : A₄ ⟶ A₃}
    {g₁₂ : B₂ ⟶ B₁} {g₁₃ : B₃ ⟶ B₁} {g₂₄ : B₄ ⟶ B₂} {g₃₄ : B₄ ⟶ B₃}
    {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄}
    [Fibration f₁₂] [Fibration g₁₂]
    (hA : IsPullback f₂₄ f₃₄ f₁₂ f₁₃) (hB : IsPullback g₂₄ g₃₄ g₁₂ g₁₃)
    (h₁₂ : f₁₂ ≫ u₁ = u₂ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₁ = u₃ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₂ = u₄ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₃ = u₄ ≫ g₃₄)
    [WeakEquivalence u₁] [WeakEquivalence u₂] [WeakEquivalence u₃] :
    WeakEquivalence u₄ := by
  have : Cofibration f₁₂.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration g₁₂.op := (cofibration_op_iff _).2 ‹_›
  have : WeakEquivalence u₁.op := (weakEquivalences_op_iff _).2 ‹_›
  have : WeakEquivalence u₂.op := (weakEquivalences_op_iff _).2 ‹_›
  have : WeakEquivalence u₃.op := (weakEquivalences_op_iff _).2 ‹_›
  exact (weakEquivalences_op_iff _).1
    (gluing_weakEquivalence (u₁ := u₁.op) (u₂ := u₂.op) (u₃ := u₃.op) (u₄ := u₄.op)
      hB.op.flip hA.op.flip
      (by rw [← op_comp, ← op_comp, h₁₂]) (by rw [← op_comp, ← op_comp, h₁₃])
      (by rw [← op_comp, ← op_comp, h₂₄]) (by rw [← op_comp, ← op_comp, h₃₄]))

end ABCCofibrations.ABCPrefibrationCategory

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.OverUnder
public import ABCCofibrations.FibrationBasic
public import ABCCofibrations.EquivalenceTransfer
public import ABCCofibrations.OverUnderCofibrationCategory
public import ABCCofibrations.FibrationCategory

/-!
# Over and under categories of a prefibration category (Proposition 1.7.1(2))

For an object `A` of a prefibration category, the under category `Under A` is a
prefibration category, and so is the over category `Over A` when `A` is
fibrant, with the induced weak equivalences and fibrations.

A prefibration structure on `Under A` is a precofibration structure on
`(Under A)ᵒᵖ`. Mathlib's equivalence `(Under A)ᵒᵖ ≌ Over (op A)` identifies the
induced classes on both sides, so the structure is transported from
Proposition 1.7.1(1)(a) applied to `Cᵒᵖ`. Likewise `(Over A)ᵒᵖ ≌ Under (op A)`
transports Proposition 1.7.1(1)(b), and `op A` is cofibrant when `A` is fibrant.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- **Proposition 1.7.1(2)(a), F1–F4.** The under category `Under A` of a
prefibration category is a prefibration category. -/
instance underPrefibrationCategory (A : C) : ABCPrefibrationCategory (Under A) :=
  ABCPrecofibrationCategory.of_equivalence (Over.opEquivOpUnder A).symm rfl rfl

/-- **Proposition 1.7.1(2)(b), F1–F4.** The over category `Over A` of a
prefibration category is a prefibration category when `A` is fibrant. -/
instance overPrefibrationCategory (A : C) [IsFibrant A] : ABCPrefibrationCategory (Over A) :=
  ABCPrecofibrationCategory.of_equivalence (Under.opEquivOpOver A).symm rfl rfl

end ABCCofibrations.ABCPrefibrationCategory

namespace ABCCofibrations.ABCFibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCFibrationCategory.{w} C]

/-- **Proposition 1.7.1(2)(a).** The under category `Under A` of a fibration
category is a fibration category. -/
instance underFibrationCategory (A : C) : ABCFibrationCategory.{w} (Under A) :=
  ABCCofibrationCategory.of_equivalence (Over.opEquivOpUnder A).symm rfl rfl

/-- **Proposition 1.7.1(2)(b).** The over category `Over A` of a fibration
category is a fibration category when `A` is fibrant. -/
instance overFibrationCategory (A : C) [IsFibrant A] : ABCFibrationCategory.{w} (Over A) :=
  ABCCofibrationCategory.of_equivalence (Under.opEquivOpOver A).symm rfl rfl

end ABCCofibrations.ABCFibrationCategory

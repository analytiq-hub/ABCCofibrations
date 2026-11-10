/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationBasic

/-!
# ABC fibration categories by duality

An ABC fibration category (axioms F1–F6, Definition 1.1.2) is an ABC
cofibration category on the opposite category. F5 asks for small products of
fibrant objects and of fibrations with fibrant targets; F6 for limits of
countable inverse sequences of fibrations ending at a fibrant object. Both are
the opposite forms of CF5 and CF6.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- Axioms F1–F6, expressed as CF1–CF6 on the opposite category, with F5 for
families indexed by `Type w`. -/
abbrev ABCFibrationCategory (C : Type u) [Category.{v} C]
    [CategoryWithFibrations C] [CategoryWithWeakEquivalences C] [HasTerminal C] : Prop :=
  ABCCofibrationCategory.{w} Cᵒᵖ

end ABCCofibrations

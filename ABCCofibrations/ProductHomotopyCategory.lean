/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Localization.Pi

/-!
# Homotopy categories of products (Theorem 7.1.1, finite case)

For finitely many precofibration categories `M_k`, the homotopy category of the
product (with componentwise weak equivalences) is the product of the homotopy
categories: the product of localization functors is a localization functor.
This is mathlib's `Functor.IsLocalization.pi`. The paper proves the statement for
an arbitrary family; the infinite case is not formalized here.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- **Theorem 7.1.1**, finite products. For a finite family of precofibration
categories, the product of localization functors `∏ M_k ⥤ ∏ ho M_k` is a
localization for the componentwise weak equivalences, so the comparison
`ho(∏ M_k) ⥤ ∏ ho M_k` is an equivalence. -/
theorem isLocalization_pi {J : Type w} [Finite J] {C : J → Type u} [∀ j, Category.{v} (C j)]
    [∀ j, CategoryWithCofibrations (C j)] [∀ j, CategoryWithWeakEquivalences (C j)]
    [∀ j, HasInitial (C j)] [∀ j, ABCPrecofibrationCategory (C j)]
    {D : J → Type*} [∀ j, Category (D j)] (L : ∀ j, C j ⥤ D j)
    [∀ j, (L j).IsLocalization (weakEquivalences (C j))] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi fun j ↦ weakEquivalences (C j)) := by
  have (j : J) : (weakEquivalences (C j)).ContainsIdentities :=
    ⟨fun X ↦ (ABCPrecofibrationCategory.weakEquivalence_of_isIso (𝟙 X)).mem⟩
  infer_instance

end ABCCofibrations

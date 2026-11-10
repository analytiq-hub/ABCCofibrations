/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.Over

/-!
# Temporary local `to_dual` registrations

Mathlib's `to_dual` attribute generates the dual of a declaration from a
dictionary of dual constants. At the pinned mathlib version, the
model-category vocabulary, `MorphismProperty`, and `Over`/`Under` are not yet in
that dictionary. This module registers the few pairs needed to generate the
induced classes on `Under S` from mathlib's classes on `Over S`
(see `OverUnder.lean`).

The registrations are local to this project. They should be **removed** once
mathlib registers these constants itself (after the `StructuredArrow`
dualization, leanprover-community/mathlib4#40940, and a decision on how
`to_dual` treats `MorphismProperty`); a mathlib bump that registers them
differently will report the overlap.

Known limitation: the cast for `MorphismProperty` below lets `to_dual` translate
instances and definitional statements, but not proofs which pass a term such as
`cofibrations C f` through `Iff.trans`, `Iff.symm`, or `simp` rewrites. Such
lemmas are stated natively instead.

The project's main duality method remains transport through opposite
categories; these registrations are used only for the `Over`/`Under` pair.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra

/- Applying a morphism property to a reversed arrow swaps its implicit
objects; this cast tells `to_dual` how to translate such applications. -/
to_dual_insert_cast_fun MorphismProperty := fun W _ _ f ↦ W f, fun W _ _ f ↦ W f

/- Cofibrations and fibrations are dual; weak equivalences are self-dual,
which needs no registration. -/
attribute [to_dual existing CategoryWithCofibrations] CategoryWithFibrations
attribute [to_dual existing cofibrations] fibrations

/- Over and under categories, with their underlying objects and morphisms. -/
attribute [to_dual existing Over] Under
attribute [to_dual existing] Under.Hom
attribute [to_dual existing instCategoryOver] instCategoryUnder
attribute [to_dual existing Over.left] Under.right
attribute [to_dual existing] Under.hom
attribute [to_dual existing Over.Hom.left] Under.Hom.right
attribute [to_dual existing MorphismProperty.over] MorphismProperty.under

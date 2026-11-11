/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence

/-!
# The snake lemma (Lemma 3.2.3)

A short exact sequence of complexes in an abelian category induces a long exact
sequence in homology. This is mathlib's homology sequence
(`Mathlib.Algebra.Homology.HomologySequence`), obtained from the snake lemma
without Mitchell's embedding theorem; we restate it for any complex shape.
-/

@[expose] public section

open CategoryTheory

namespace ABCCofibrations

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- **Lemma 3.2.3** (snake lemma). For a short exact sequence `S` of complexes
and degrees `i`, `j` with `c.Rel i j`, the sequence
`H_i S₁ ⟶ H_i S₂ ⟶ H_i S₃ ⟶ H_j S₁ ⟶ H_j S₂` is exact, with the connecting map
`δ : H_i S₃ ⟶ H_j S₁`. -/
theorem snake_lemma (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact ∧
    (ShortComplex.mk _ _ (hS.comp_δ i j hij)).Exact ∧
    (ShortComplex.mk _ _ (hS.δ_comp i j hij)).Exact :=
  ⟨hS.homology_exact₂ i, hS.homology_exact₃ i j hij, hS.homology_exact₁ i j hij⟩

end ABCCofibrations

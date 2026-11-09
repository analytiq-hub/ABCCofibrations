/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationBasic
public import Mathlib.AlgebraicTopology.ModelCategory.PathObject
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Good path objects under F1–F4

Definition 1.5.1(2) and Lemma 1.5.2(2). We reuse mathlib's `PathObject`
and its goodness predicate, without a model-category assumption.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- Products of two fibrant objects exist, using the restricted pullback axiom. -/
theorem hasBinaryProduct (A B : C) [IsFibrant A] [IsFibrant B] : HasBinaryProduct A B := by
  let c := BinaryFan.mk (pullback.fst (terminal.from A) (terminal.from B))
    (pullback.snd (terminal.from A) (terminal.from B))
  exact ⟨⟨c, isProductOfIsTerminalIsPullback _ _ _ _ terminalIsTerminal
    (pullbackIsPullback _ _)⟩⟩

variable {A B : C} [IsFibrant A] [IsFibrant B] [HasBinaryProduct A B]

/-- The first product projection is a fibration. -/
theorem fibration_prod_fst : Fibration (prod.fst : A ⨯ B ⟶ A) :=
  fibration_of_isPullback (IsPullback.of_hasBinaryProduct' A B).flip

/-- The second product projection is a fibration. -/
theorem fibration_prod_snd : Fibration (prod.snd : A ⨯ B ⟶ B) :=
  fibration_of_isPullback (IsPullback.of_hasBinaryProduct' A B)

/-- A product of fibrant objects is fibrant. -/
theorem prod_fibrant : IsFibrant (A ⨯ B) := by
  let := fibration_prod_snd (A := A) (B := B)
  exact fibrant_source (prod.snd : A ⨯ B ⟶ B)

omit [IsFibrant B] [HasBinaryProduct A B] in
/-- Good path objects exist for any chosen binary product of a fibrant object
with itself, by F4 applied to the diagonal. -/
theorem exists_good_pathObject (A : C) [IsFibrant A] [HasBinaryProduct A A] :
    ∃ P : PathObject A, P.IsGood := by
  let := prod_fibrant (A := A) (B := A)
  obtain ⟨I, w, p, hw, hp, hfac⟩ := factorization (prod.lift (𝟙 A) (𝟙 A))
  let P : PathObject A := {
    P := I
    p₀ := p ≫ prod.fst
    p₁ := p ≫ prod.snd
    ι := w
    ι_p₀ := by simp [← Category.assoc, hfac]
    ι_p₁ := by simp [← Category.assoc, hfac]
    weakEquivalence_ι := hw }
  refine ⟨P, ⟨?_⟩⟩
  have he : P.p = p := by ext <;> simp [PrepathObject.p, P]
  rw [he]
  exact hp

variable {X : C} [IsFibrant X] [HasBinaryProduct X X] (P : PathObject X) [P.IsGood]

/-- The first projection of a good path object is a fibration. -/
theorem fibration_pathObject_p₀ : Fibration P.p₀ := by
  let := fibration_prod_fst (A := X) (B := X)
  rw [← P.p_fst]
  infer_instance

/-- The second projection of a good path object is a fibration. -/
theorem fibration_pathObject_p₁ : Fibration P.p₁ := by
  let := fibration_prod_snd (A := X) (B := X)
  rw [← P.p_snd]
  infer_instance

/-- The object underlying a good path object is fibrant. -/
theorem pathObject_fibrant : IsFibrant P.P := by
  let := fibration_pathObject_p₀ P
  exact fibrant_source P.p₀

omit [IsFibrant A] [IsFibrant B] [HasBinaryProduct A B]
  [IsFibrant X] [HasBinaryProduct X X] [P.IsGood] in
/-- Both path projections are weak equivalences by two out of three. -/
theorem weakEquivalence_pathObject_p₀ : WeakEquivalence P.p₀ := by
  let := weakEquivalence_of_isIso (𝟙 X)
  exact weakEquivalence_of_precomp_of_fac P.ι_p₀

omit [IsFibrant A] [IsFibrant B] [HasBinaryProduct A B]
  [IsFibrant X] [HasBinaryProduct X X] [P.IsGood] in
/-- The second path projection is a weak equivalence as well. -/
theorem weakEquivalence_pathObject_p₁ : WeakEquivalence P.p₁ := by
  let := weakEquivalence_of_isIso (𝟙 X)
  exact weakEquivalence_of_precomp_of_fac P.ι_p₁

/-- Reversing a good path object preserves goodness. -/
theorem good_pathObject_symm : P.symm.IsGood := by
  have he : P.symm.p = P.p ≫ (prod.braiding X X).hom := by
    apply prod.hom_ext
    · rw [P.symm.p_fst]
      change P.p₁ = (P.p ≫ prod.lift prod.snd prod.fst) ≫ prod.fst
      rw [Category.assoc, prod.lift_fst, P.p_snd]
    · rw [P.symm.p_snd]
      change P.p₀ = (P.p ≫ prod.lift prod.snd prod.fst) ≫ prod.snd
      rw [Category.assoc, prod.lift_snd, P.p_fst]
  constructor
  rw [he]
  let := prod_fibrant (A := X) (B := X)
  let := fibration_of_isIso (prod.braiding X X).hom
  exact inferInstanceAs (Fibration (P.p ≫ (prod.braiding X X).hom))

end ABCCofibrations.ABCPrefibrationCategory

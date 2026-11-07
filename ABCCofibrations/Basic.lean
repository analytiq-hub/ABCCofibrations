/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Anderson–Brown–Cisinski cofibration categories

Following Definition 1.1.1 of Rădulescu-Banu, *Cofibrations in Homotopy Theory*,
https://arxiv.org/abs/math/0610009.

`ABCPrecofibrationCategory` imposes CF1–CF4 on existing mathlib morphism classes.
`ABCCofibrationCategory` adds CF5–CF6. An initial object is supplied separately
by `[HasInitial C]`; no general cocompleteness or fibrations are required.
Coproducts are indexed by `Type w`, making the smallness universe explicit.
These are assumptions carried by typeclasses, not new Lean `axiom` declarations.
-/

public section

universe w v u

open CategoryTheory Limits

namespace ABCCofibrations

open HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- ABC axioms CF1–CF4, relative to the supplied initial object and morphism classes. -/
class ABCPrecofibrationCategory : Prop where
  /-- CF1: the initial object is cofibrant. -/
  initial_cofibrant : IsCofibrant (⊥_ C)
  /-- CF1: cofibrations compose, including those with noncofibrant source. -/
  cofibrations_comp : (cofibrations C).IsStableUnderComposition
  /-- CF1: every isomorphism is a weak equivalence. -/
  weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f
  /-- CF1: an isomorphism with cofibrant source is a cofibration. -/
  cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] [IsCofibrant A] :
    Cofibration f
  /-- CF2: weak equivalences satisfy two out of three. -/
  weakEquivalences_twoOutOfThree : (weakEquivalences C).HasTwoOutOfThreeProperty
  /-- CF3: the required pushouts exist. -/
  hasPushout {A B D : C} (i : A ⟶ B) (f : A ⟶ D)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] : HasPushout i f
  /-- CF3: cobase change preserves cofibrations for these pushouts. -/
  cofibration_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ E} {j : D ⟶ E} (h : IsPushout i f g j)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] : Cofibration j
  /-- CF3: cobase change also preserves trivial cofibrations. -/
  weakEquivalence_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ E} {j : D ⟶ E} (h : IsPushout i f g j)
    [IsCofibrant A] [IsCofibrant D] [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence j
  /-- CF4: factor maps with cofibrant source; no functorial choice is assumed. -/
  factorization {A B : C} (f : A ⟶ B) [IsCofibrant A] :
    ∃ (Z : C) (i : A ⟶ Z) (p : Z ⟶ B),
      Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f

attribute [instance] ABCPrecofibrationCategory.initial_cofibrant
  ABCPrecofibrationCategory.cofibrations_comp
  ABCPrecofibrationCategory.weakEquivalences_twoOutOfThree
  ABCPrecofibrationCategory.hasPushout

namespace ABCPrecofibrationCategory

variable {C} [ABCPrecofibrationCategory C]

/-- CF1 and composition imply that a cofibration preserves cofibrancy. -/
theorem cofibrant_target {A B : C} (i : A ⟶ B) [IsCofibrant A] [Cofibration i] :
    IsCofibrant B :=
  isCofibrant_of_cofibration i

/-- Every object admits a weak equivalence from a cofibrant object, by CF4. -/
theorem exists_cofibrant_replacement (A : C) :
    ∃ (Q : C) (q : Q ⟶ A), IsCofibrant Q ∧ WeakEquivalence q := by
  obtain ⟨Q, i, q, hi, hq, _⟩ := factorization (initial.to A)
  let := hi
  exact ⟨Q, q, cofibrant_target i, hq⟩

end ABCPrecofibrationCategory

/-- ABC axioms CF1–CF6, with CF5 for families indexed by `Type w`. -/
class ABCCofibrationCategory : Prop extends ABCPrecofibrationCategory C where
  /-- CF5: existence for each small family (not all objects must be cofibrant). -/
  hasCoproductOfCofibrant {ι : Type w} (A : ι → C) (hA : ∀ i, IsCofibrant (A i)) :
    HasCoproduct A
  /-- CF5: such coproducts are cofibrant. -/
  coproduct_cofibrant {ι : Type w} (A : ι → C) (hA : ∀ i, IsCofibrant (A i))
    [HasCoproduct A] : IsCofibrant (∐ A)
  /-- CF5: coproducts of cofibrations with cofibrant sources are cofibrations. -/
  coproduct_cofibration {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i))
    [HasCoproduct A] [HasCoproduct B] : Cofibration (Limits.Sigma.map f)
  /-- CF5: the same coproduct map is trivial when every summand is trivial. -/
  coproduct_weakEquivalence {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i))
    (hw : ∀ i, WeakEquivalence (f i)) [HasCoproduct A] [HasCoproduct B] :
    WeakEquivalence (Limits.Sigma.map f)
  /-- CF6: sequential colimits of cofibrations starting cofibrantly exist. -/
  hasSequentialColimit (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) : HasColimit F
  /-- CF6: the transfinite composite from the first object is a cofibration. -/
  sequential_cofibration (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) [HasColimit F] :
    Cofibration (colimit.ι F 0)
  /-- CF6: this composite is trivial when all successive maps are trivial. -/
  sequential_weakEquivalence (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n))))
    (hw : ∀ n, WeakEquivalence (F.map (homOfLE (Nat.le_succ n)))) [HasColimit F] :
    WeakEquivalence (colimit.ι F 0)

namespace ABCCofibrationCategory

variable {C} [ABCCofibrationCategory.{w} C]

/-- CF1 and CF5 provide coproducts of both ends of a family of cofibrations. -/
theorem hasCoproduct_target {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    (hA : ∀ i, IsCofibrant (A i)) (hf : ∀ i, Cofibration (f i)) : HasCoproduct B := by
  apply hasCoproductOfCofibrant
  intro i
  let := hA i
  let := hf i
  exact ABCPrecofibrationCategory.cofibrant_target (f i)

/-- The sequential colimit is itself cofibrant, using CF6 and CF1. -/
theorem sequential_colimit_cofibrant (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (homOfLE (Nat.le_succ n)))) [HasColimit F] :
    IsCofibrant (colimit F) := by
  let := h0
  let := sequential_cofibration F h0 hf
  exact ABCPrecofibrationCategory.cofibrant_target (colimit.ι F 0)

end ABCCofibrationCategory

end ABCCofibrations

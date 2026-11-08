/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Coproducts
public import Mathlib.AlgebraicTopology.ModelCategory.Cylinder

/-!
# Cylinders in a precofibration category

Definition 1.5.1(1) and Lemma 1.5.2(1) of Rădulescu-Banu,
*Cofibrations in Homotopy Theory*. The paper's cylinder objects are mathlib's
`Cylinder A` equipped with `Cylinder.IsGood`, for a cofibrant object `A`.

We construct good cylinders using CF4 and prove the endpoint properties using
the restricted pushout axiom. No model-category structure, global coproducts,
or unrestricted stability under cobase change is assumed.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A : C} [IsCofibrant A] [HasBinaryCoproduct A A]

/-- Good cylinders exist for cofibrant objects (Lemma 1.5.2(1)), relative to
any chosen binary coproduct. Such a coproduct exists by `hasBinaryCoproduct`. -/
theorem exists_good_cylinder (A : C) [IsCofibrant A] [HasBinaryCoproduct A A] :
    ∃ P : Cylinder A, P.IsGood := by
  let := coprod_cofibrant (A := A) (B := A)
  obtain ⟨I, j, p, hj, hp, hfac⟩ := factorization (coprod.desc (𝟙 A) (𝟙 A))
  let P : Cylinder A :=
    { I := I
      i₀ := coprod.inl ≫ j
      i₁ := coprod.inr ≫ j
      π := p
      i₀_π := by simp [Category.assoc, hfac]
      i₁_π := by simp [Category.assoc, hfac]
      weakEquivalence_π := hp }
  refine ⟨P, ⟨?_⟩⟩
  have h : P.i = j := by
    ext <;> simp [Precylinder.i, P]
  rw [h]
  exact hj

variable (P : Cylinder A) [P.IsGood]

/-- The first endpoint of a good cylinder is a cofibration under CF1–CF4. -/
theorem cofibration_cylinder_i₀ : Cofibration P.i₀ := by
  let := cofibration_coprod_inl (A := A) (B := A)
  rw [← P.inl_i]
  infer_instance

/-- The second endpoint of a good cylinder is a cofibration under CF1–CF4. -/
theorem cofibration_cylinder_i₁ : Cofibration P.i₁ := by
  let := cofibration_coprod_inr (A := A) (B := A)
  rw [← P.inr_i]
  infer_instance

/-- The underlying object of a good cylinder on a cofibrant object is cofibrant. -/
theorem cylinder_cofibrant : IsCofibrant P.I := by
  let := cofibration_cylinder_i₀ P
  exact cofibrant_target P.i₀

omit [IsCofibrant A] [HasBinaryCoproduct A A] [P.IsGood] in
/-- The first cylinder endpoint is a weak equivalence by two-out-of-three. -/
theorem weakEquivalence_cylinder_i₀ : WeakEquivalence P.i₀ := by
  let := weakEquivalence_of_isIso (𝟙 A)
  exact weakEquivalence_of_postcomp_of_fac P.i₀_π

omit [IsCofibrant A] [HasBinaryCoproduct A A] [P.IsGood] in
/-- The second cylinder endpoint is a weak equivalence by two-out-of-three. -/
theorem weakEquivalence_cylinder_i₁ : WeakEquivalence P.i₁ := by
  let := weakEquivalence_of_isIso (𝟙 A)
  exact weakEquivalence_of_postcomp_of_fac P.i₁_π

end ABCCofibrations.ABCPrecofibrationCategory

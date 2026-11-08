/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Factorization
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

/-- Relative cylinders (Lemma 1.5.3(1)). Extend a good cylinder along a map
between cofibrant objects, retaining the canonical relative comparison as a
cofibration. The chosen pushout exists by CF3, since the source endpoint
coproduct is cofibrant. -/
theorem exists_relative_good_cylinder
    {B : C} [IsCofibrant B] [HasBinaryCoproduct B B] (f : A ⟶ B)
    [HasPushout P.i (coprod.map f f)] :
    ∃ (Q : Cylinder B) (c : P.I ⟶ Q.I) (k : pushout P.i (coprod.map f f) ⟶ Q.I),
      Q.IsGood ∧ IsCofibrant Q.I ∧ Cofibration k ∧
      P.i₀ ≫ c = f ≫ Q.i₀ ∧ P.i₁ ≫ c = f ≫ Q.i₁ ∧ c ≫ Q.π = P.π ≫ f ∧
      pushout.inl P.i (coprod.map f f) ≫ k = c ∧
      pushout.inr P.i (coprod.map f f) ≫ k = Q.i := by
  let := coprod_cofibrant (A := A) (B := A)
  let := coprod_cofibrant (A := B) (B := B)
  have hsq : coprod.desc (𝟙 A) (𝟙 A) ≫ f =
      coprod.map f f ≫ coprod.desc (𝟙 B) (𝟙 B) := by
    ext <;> simp
  have hP : P.i ≫ P.π = coprod.desc (𝟙 A) (𝟙 A) := by
    ext <;> simp [Precylinder.i]
  obtain ⟨I, j, p, c, k, hI, hj, hp, hk, hjp, hleft, hright, hkinl, hkinr⟩ :=
    exists_relative_factorization (coprod.desc (𝟙 A) (𝟙 A))
      (coprod.desc (𝟙 B) (𝟙 B)) (coprod.map f f) f hsq P.i P.π hP
  let Q : Cylinder B :=
    { I := I
      i₀ := coprod.inl ≫ j
      i₁ := coprod.inr ≫ j
      π := p
      i₀_π := by simp [Category.assoc, hjp]
      i₁_π := by simp [Category.assoc, hjp]
      weakEquivalence_π := hp }
  have hQ : Q.i = j := by ext <;> simp [Precylinder.i, Q]
  have hgood : Q.IsGood := ⟨by rw [hQ]; exact hj⟩
  have h₀ : P.i₀ ≫ c = f ≫ Q.i₀ := by
    simpa [Q, Category.assoc] using
      congrArg (fun t ↦ (coprod.inl : A ⟶ A ⨿ A) ≫ t) hleft
  have h₁ : P.i₁ ≫ c = f ≫ Q.i₁ := by
    simpa [Q, Category.assoc] using
      congrArg (fun t ↦ (coprod.inr : A ⟶ A ⨿ A) ≫ t) hleft
  refine ⟨Q, c, k, hgood, hI, hk, h₀, h₁, hright, hkinl, ?_⟩
  rw [hQ]
  exact hkinr

end ABCCofibrations.ABCPrecofibrationCategory

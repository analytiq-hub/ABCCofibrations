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

@[expose] public section

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

/-- Reversing the two endpoints preserves goodness without unrestricted
isomorphism stability for cofibrations. -/
theorem good_cylinder_symm : P.symm.IsGood := by
  let := coprod_cofibrant (A := A) (B := A)
  have hb : Cofibration (coprod.braiding A A).hom :=
    cofibration_of_isIso (coprod.braiding A A).hom
  have hi : Cofibration P.i := inferInstance
  refine ⟨?_⟩
  have h : P.symm.i = (coprod.braiding A A).hom ≫ P.i := by
    ext <;> simp [Precylinder.i, Cylinder.symm, Precylinder.symm]
  rw [h]
  exact (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hb.mem hi.mem)

/-- Concatenate two good cylinders by identifying the second endpoint of the
first with the first endpoint of the second. This uses only CF1–CF4. -/
noncomputable def cylinder_trans (Q : Cylinder A) [Q.IsGood]
    [HasPushout P.i₁ Q.i₀] : Cylinder A where
  __ := P.toPrecylinder.trans Q.toPrecylinder
  weakEquivalence_π := by
    let := cylinder_cofibrant P
    let := cofibration_cylinder_i₀ Q
    let := weakEquivalence_cylinder_i₀ Q
    have hinl : WeakEquivalence (pushout.inl P.i₁ Q.i₀) :=
      weakEquivalence_of_isPushout (IsPushout.of_hasPushout P.i₁ Q.i₀).flip
    let : WeakEquivalence (pushout.inl P.i₁ Q.i₀) := hinl
    exact weakEquivalence_of_precomp_of_fac (f := pushout.inl P.i₁ Q.i₀)
      (pushout.inl_desc (f := P.i₁) (g := Q.i₀) P.π Q.π (by simp))

/-- The concatenation is again a good cylinder. -/
theorem good_cylinder_trans (Q : Cylinder A) [Q.IsGood]
    [HasPushout P.i₁ Q.i₀] : (cylinder_trans P Q).IsGood := by
  let := cylinder_cofibrant P
  let := cylinder_cofibrant Q
  let := cofibration_cylinder_i₀ P
  let := cofibration_cylinder_i₁ P
  let := hasBinaryCoproduct P.I A
  let := coprod_cofibrant (A := P.I) (B := A)
  let := coprod_cofibrant (A := A) (B := A)
  let ψ : P.I ⨿ A ⟶ pushout P.i₁ Q.i₀ :=
    coprod.desc (pushout.inl P.i₁ Q.i₀) (Q.i₁ ≫ pushout.inr P.i₁ Q.i₀)
  have fac : coprod.map P.i₁ (𝟙 A) ≫ ψ = Q.i ≫ pushout.inr P.i₁ Q.i₀ := by
    ext
    · simp [ψ, pushout.condition, Precylinder.i]
    · simp [ψ, Precylinder.i]
  have sq : IsPushout P.i₁ (coprod.inl ≫ Q.i) (coprod.inl ≫ ψ)
      (pushout.inr P.i₁ Q.i₀) := by
    simpa [ψ, Precylinder.i] using IsPushout.of_hasPushout P.i₁ Q.i₀
  have hψ : Cofibration ψ :=
    cofibration_of_isPushout
      (IsPushout.of_top sq fac (IsPushout.of_coprod_inl_with_id P.i₁ A).flip).flip
  let := hψ
  have hm := cofibration_coprod_map_id P.i₀ A
  refine ⟨?_⟩
  have h : (cylinder_trans P Q).i = coprod.map P.i₀ (𝟙 A) ≫ ψ := by
    ext <;> simp [Precylinder.i, cylinder_trans, Precylinder.trans, ψ]
  rw [h]
  exact (cofibration_iff _).2 ((cofibrations C).comp_mem _ _ hm.mem hψ.mem)

end ABCCofibrations.ABCPrecofibrationCategory

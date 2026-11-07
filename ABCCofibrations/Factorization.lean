/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Coproducts

/-!
# Factorization lemmas

Lemma 1.3.1(1) and Remark 1.3.2 of Rădulescu-Banu,
*Cofibrations in Homotopy Theory*. A map between cofibrant objects factors
through a cofibration followed by a weak equivalence admitting a trivial
cofibration section. The stronger version retains the cofibration from the
coproduct of the source and target, for use in relative constructions.

Only CF1–CF4 are assumed. The factorizations are existential, with no
functorial choice imposed.

`exists_relative_factorization` proves Lemma 1.3.3(1), extending a specified
factorization across a commutative square. Its witnesses retain the comparison
map from the pushout and both of its defining equations.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A B : C} [IsCofibrant A] [IsCofibrant B]

/-- The strengthened Brown factorization of Remark 1.3.2, relative to any chosen
binary coproduct. The map `p` has a trivial cofibration section `s`, and the
combined map `coprod.desc i s` is a cofibration. -/
theorem exists_brown_factorization_with_coprod (f : A ⟶ B) [HasBinaryCoproduct A B] :
    ∃ (Z : C) (i : A ⟶ Z) (p : Z ⟶ B) (s : B ⟶ Z),
      IsCofibrant Z ∧ Cofibration i ∧ WeakEquivalence p ∧
      Cofibration s ∧ WeakEquivalence s ∧ Cofibration (coprod.desc i s) ∧
      i ≫ p = f ∧ s ≫ p = 𝟙 B := by
  let := coprod_cofibrant (A := A) (B := B)
  obtain ⟨Z, j, p, hj, hp, hfac⟩ := factorization (coprod.desc f (𝟙 B))
  let := hj
  let := hp
  let i := (coprod.inl : A ⟶ A ⨿ B) ≫ j
  let s := (coprod.inr : B ⟶ A ⨿ B) ≫ j
  have hi : Cofibration i := by
    let := cofibration_coprod_inl (A := A) (B := B)
    dsimp [i]
    infer_instance
  have hs : Cofibration s := by
    let := cofibration_coprod_inr (A := A) (B := B)
    dsimp [s]
    infer_instance
  have hip : i ≫ p = f := by
    simp [i, Category.assoc, hfac]
  have hsp : s ≫ p = 𝟙 B := by
    simp [s, Category.assoc, hfac]
  have hsw : WeakEquivalence s := by
    let := weakEquivalence_of_isIso (𝟙 B)
    exact weakEquivalence_of_postcomp_of_fac hsp
  have hcoprod : Cofibration (coprod.desc i s) := by
    have h : coprod.desc i s = j := by
      ext <;> simp [i, s]
    rw [h]
    exact hj
  let := hi
  exact ⟨Z, i, p, s, cofibrant_target i, hi, hp, hs, hsw, hcoprod, hip, hsp⟩

/-- Brown factorization (Lemma 1.3.1(1)): the second factor is a weak equivalence
and a retraction of a trivial cofibration. No coproduct instance is required
from the caller. -/
theorem exists_brown_factorization (f : A ⟶ B) :
    ∃ (Z : C) (i : A ⟶ Z) (p : Z ⟶ B) (s : B ⟶ Z),
      IsCofibrant Z ∧ Cofibration i ∧ WeakEquivalence p ∧
      Cofibration s ∧ WeakEquivalence s ∧ i ≫ p = f ∧ s ≫ p = 𝟙 B := by
  let := hasBinaryCoproduct A B
  obtain ⟨Z, i, p, s, hZ, hi, hp, hs, hsw, _, hip, hsp⟩ :=
    exists_brown_factorization_with_coprod f
  exact ⟨Z, i, p, s, hZ, hi, hp, hs, hsw, hip, hsp⟩

/-- Relative factorization (Lemma 1.3.3(1)). Extend a specified factorization
`i₁ ≫ p₁ = f₁` across a square with cofibrant left-hand objects. No cofibrancy
of the right-hand objects, or cofibration property of `a`, is required.

The comparison map `k` is a cofibration. Its two defining equations identify it
with the canonical map from `pushout i₁ a` to the new factorization object. -/
theorem exists_relative_factorization
    {A₁ A₂ B₁ B₂ Z₁ : C} [IsCofibrant A₁] [IsCofibrant A₂]
    (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (h : f₁ ≫ b = a ≫ f₂)
    (i₁ : A₁ ⟶ Z₁) (p₁ : Z₁ ⟶ B₁) [Cofibration i₁] [WeakEquivalence p₁]
    (h₁ : i₁ ≫ p₁ = f₁) :
    ∃ (Z₂ : C) (i₂ : A₂ ⟶ Z₂) (p₂ : Z₂ ⟶ B₂) (a' : Z₁ ⟶ Z₂)
      (k : pushout i₁ a ⟶ Z₂),
      IsCofibrant Z₂ ∧ Cofibration i₂ ∧ WeakEquivalence p₂ ∧ Cofibration k ∧
      i₂ ≫ p₂ = f₂ ∧ i₁ ≫ a' = a ≫ i₂ ∧ a' ≫ p₂ = p₁ ≫ b ∧
      pushout.inl i₁ a ≫ k = a' ∧ pushout.inr i₁ a ≫ k = i₂ := by
  have hsq : i₁ ≫ (p₁ ≫ b) = a ≫ f₂ := by
    rw [← Category.assoc, h₁, h]
  let q := pushout.desc (p₁ ≫ b) f₂ hsq
  have hinr : Cofibration (pushout.inr i₁ a) :=
    cofibration_of_isPushout (IsPushout.of_hasPushout i₁ a)
  let := hinr
  let := cofibrant_target (pushout.inr i₁ a)
  obtain ⟨Z₂, k, p₂, hk, hp₂, hkp⟩ := factorization q
  let := hk
  let i₂ := pushout.inr i₁ a ≫ k
  let a' := pushout.inl i₁ a ≫ k
  have hi₂ : Cofibration i₂ := by
    dsimp [i₂]
    infer_instance
  have hi₂p₂ : i₂ ≫ p₂ = f₂ := by
    simp [i₂, Category.assoc, hkp, q]
  have hleft : i₁ ≫ a' = a ≫ i₂ := by
    dsimp [a', i₂]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  have hright : a' ≫ p₂ = p₁ ≫ b := by
    simp [a', Category.assoc, hkp, q]
  let := hi₂
  exact ⟨Z₂, i₂, p₂, a', k, cofibrant_target i₂, hi₂, hp₂, hk,
    hi₂p₂, hleft, hright, rfl, rfl⟩

end ABCCofibrations.ABCPrecofibrationCategory

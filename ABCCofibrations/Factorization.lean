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

`exists_compatible_brown_factorization` extends strengthened Brown
factorizations across squares. It retains a combined relative comparison
cofibration. The separate comparison claims of Lemma 1.3.4(1) remain unresolved;
see `docs/relative-brown-factorization.md`.
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

/-- Extend a strengthened Brown factorization across a commutative square.
The new combined coproduct map is a cofibration and the section is compatible
with the original section. The combined relative comparison map is also a
cofibration; no assertion about the two separate pushout comparisons is made.

This is a partial version of the intended relative Brown factorization target;
see `docs/relative-brown-factorization.md` for the obstruction to the additional
claims in Lemma 1.3.4(1). -/
theorem exists_compatible_brown_factorization
    {A₁ A₂ B₁ B₂ Z₁ : C} [IsCofibrant A₁] [IsCofibrant A₂]
    [IsCofibrant B₁] [IsCofibrant B₂]
    [HasBinaryCoproduct A₁ B₁] [HasBinaryCoproduct A₂ B₂]
    (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    (h : f₁ ≫ b = a ≫ f₂)
    (i₁ : A₁ ⟶ Z₁) (p₁ : Z₁ ⟶ B₁) (s₁ : B₁ ⟶ Z₁)
    [Cofibration (coprod.desc i₁ s₁)] [WeakEquivalence p₁]
    [HasPushout (coprod.desc i₁ s₁) (coprod.map a b)]
    (h₁ : i₁ ≫ p₁ = f₁) (hs₁ : s₁ ≫ p₁ = 𝟙 B₁) :
    ∃ (Z₂ : C) (i₂ : A₂ ⟶ Z₂) (p₂ : Z₂ ⟶ B₂) (s₂ : B₂ ⟶ Z₂)
      (c : Z₁ ⟶ Z₂)
      (k : pushout (coprod.desc i₁ s₁) (coprod.map a b) ⟶ Z₂),
      IsCofibrant Z₂ ∧ Cofibration i₂ ∧ WeakEquivalence p₂ ∧
      Cofibration s₂ ∧ WeakEquivalence s₂ ∧ Cofibration (coprod.desc i₂ s₂) ∧
      Cofibration k ∧ i₂ ≫ p₂ = f₂ ∧ s₂ ≫ p₂ = 𝟙 B₂ ∧
      i₁ ≫ c = a ≫ i₂ ∧ c ≫ p₂ = p₁ ≫ b ∧ s₁ ≫ c = b ≫ s₂ ∧
      pushout.inl (coprod.desc i₁ s₁) (coprod.map a b) ≫ k = c ∧
      pushout.inr (coprod.desc i₁ s₁) (coprod.map a b) ≫ k = coprod.desc i₂ s₂ := by
  let := coprod_cofibrant (A := A₁) (B := B₁)
  let := coprod_cofibrant (A := A₂) (B := B₂)
  have htop : coprod.desc i₁ s₁ ≫ p₁ = coprod.desc f₁ (𝟙 B₁) := by
    ext <;> simp [h₁, hs₁]
  have hsq : coprod.desc f₁ (𝟙 B₁) ≫ b =
      coprod.map a b ≫ coprod.desc f₂ (𝟙 B₂) := by
    ext <;> simp [h]
  obtain ⟨Z₂, j₂, p₂, c, k, hZ₂, hj₂, hp₂, hk, hjp, hleft, hright, hkinl, hkinr⟩ :=
    exists_relative_factorization (coprod.desc f₁ (𝟙 B₁)) (coprod.desc f₂ (𝟙 B₂))
      (coprod.map a b) b hsq (coprod.desc i₁ s₁) p₁ htop
  let := hj₂
  let := hp₂
  let i₂ := (coprod.inl : A₂ ⟶ A₂ ⨿ B₂) ≫ j₂
  let s₂ := (coprod.inr : B₂ ⟶ A₂ ⨿ B₂) ≫ j₂
  have hi₂ : Cofibration i₂ := by
    let := cofibration_coprod_inl (A := A₂) (B := B₂)
    dsimp [i₂]
    infer_instance
  have hs₂ : Cofibration s₂ := by
    let := cofibration_coprod_inr (A := A₂) (B := B₂)
    dsimp [s₂]
    infer_instance
  have hip : i₂ ≫ p₂ = f₂ := by simp [i₂, Category.assoc, hjp]
  have hsp : s₂ ≫ p₂ = 𝟙 B₂ := by simp [s₂, Category.assoc, hjp]
  have hsw : WeakEquivalence s₂ := by
    let := weakEquivalence_of_isIso (𝟙 B₂)
    exact weakEquivalence_of_postcomp_of_fac hsp
  have hc : coprod.desc i₂ s₂ = j₂ := by ext <;> simp [i₂, s₂]
  have hi : i₁ ≫ c = a ≫ i₂ := by
    simpa [i₂, Category.assoc] using congrArg
      (fun t ↦ (coprod.inl : A₁ ⟶ A₁ ⨿ B₁) ≫ t) hleft
  have hs : s₁ ≫ c = b ≫ s₂ := by
    simpa [s₂, Category.assoc] using congrArg
      (fun t ↦ (coprod.inr : B₁ ⟶ A₁ ⨿ B₁) ≫ t) hleft
  have hcombined : Cofibration (coprod.desc i₂ s₂) := by rw [hc]; exact hj₂
  refine ⟨Z₂, i₂, p₂, s₂, c, k, hZ₂, hi₂, hp₂, hs₂, hsw, hcombined,
    hk, hip, hsp, hi, hright, hs, hkinl, ?_⟩
  rw [hc]
  exact hkinr

end ABCCofibrations.ABCPrecofibrationCategory

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Coproducts

/-!
# Brown factorization

Lemma 1.3.1(1) and Remark 1.3.2 of Rădulescu-Banu,
*Cofibrations in Homotopy Theory*. A map between cofibrant objects factors
through a cofibration followed by a weak equivalence admitting a trivial
cofibration section. The stronger version retains the cofibration from the
coproduct of the source and target, for use in relative constructions.

Only CF1–CF4 are assumed. The factorizations are existential, with no
functorial choice imposed.
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

end ABCCofibrations.ABCPrecofibrationCategory

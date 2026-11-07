/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coproducts of cofibrant objects

The binary case of Lemma 1.2.1(1) of Rădulescu-Banu,
*Cofibrations in Homotopy Theory*, together with existence and cofibrancy
of `Fin n`-indexed coproducts. Only CF1–CF4 are assumed.
The pushout arguments retain the cofibrancy hypotheses of CF3.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The pushout over the initial object gives a coproduct of cofibrant objects. -/
theorem hasBinaryCoproduct (A B : C) [IsCofibrant A] [IsCofibrant B] :
    HasBinaryCoproduct A B := by
  let c := BinaryCofan.mk (pushout.inl (initial.to A) (initial.to B))
    (pushout.inr (initial.to A) (initial.to B))
  exact ⟨⟨c, isCoproductOfIsInitialIsPushout _ _ _ _ initialIsInitial
    (pushoutIsPushout _ _)⟩⟩

variable {A B : C} [IsCofibrant A] [IsCofibrant B] [HasBinaryCoproduct A B]

/-- The left coproduct inclusion is a cofibration, by the restricted pushout axiom. -/
theorem cofibration_coprod_inl : Cofibration (coprod.inl : A ⟶ A ⨿ B) :=
  cofibration_of_isPushout (IsPushout.of_hasBinaryCoproduct' A B).flip

/-- The right coproduct inclusion is a cofibration. -/
theorem cofibration_coprod_inr : Cofibration (coprod.inr : B ⟶ A ⨿ B) :=
  cofibration_of_isPushout (IsPushout.of_hasBinaryCoproduct' A B)

/-- A binary coproduct of cofibrant objects is cofibrant. -/
theorem coprod_cofibrant : IsCofibrant (A ⨿ B) := by
  let := cofibration_coprod_inl (A := A) (B := B)
  exact cofibrant_target (coprod.inl : A ⟶ A ⨿ B)

omit [IsCofibrant B] [HasBinaryCoproduct A B] in
/-- Adding a fixed cofibrant summand preserves cofibrations. -/
theorem cofibration_coprod_map_id (f : A ⟶ B) [Cofibration f]
    (X : C) [IsCofibrant X] [HasBinaryCoproduct A X] [HasBinaryCoproduct B X] :
    Cofibration (coprod.map f (𝟙 X)) := by
  let := coprod_cofibrant (A := A) (B := X)
  exact cofibration_of_isPushout (IsPushout.of_coprod_inl_with_id f X).flip

omit [IsCofibrant B] [HasBinaryCoproduct A B] in
/-- Adding a fixed cofibrant summand preserves trivial cofibrations. -/
theorem weakEquivalence_coprod_map_id (f : A ⟶ B) [Cofibration f]
    [WeakEquivalence f] (X : C) [IsCofibrant X]
    [HasBinaryCoproduct A X] [HasBinaryCoproduct B X] :
    WeakEquivalence (coprod.map f (𝟙 X)) := by
  let := coprod_cofibrant (A := A) (B := X)
  exact weakEquivalence_of_isPushout (IsPushout.of_coprod_inl_with_id f X).flip

section

variable {A₀ A₁ B₀ B₁ X : C}

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [HasInitial C] [ABCPrecofibrationCategory C] in
/-- The square expressing addition of a fixed left summand as a pushout. -/
private theorem isPushout_coprod_map_id_left (f : A₁ ⟶ B₁)
    [HasBinaryCoproduct X A₁] [HasBinaryCoproduct X B₁] :
    IsPushout coprod.inr f (coprod.map (𝟙 X) f) coprod.inr where
  w := by simp
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun s ↦ by
    refine ⟨coprod.desc (coprod.inl ≫ s.inl) s.inr, ?_, ?_, ?_⟩
    · ext
      · simp
      · simp [PushoutCocone.condition]
    · simp
    · intro m h₁ h₂
      dsimp at m h₁ h₂ ⊢
      ext
      · simp [← h₁]
      · simpa using h₂)⟩

/-- Adding a fixed cofibrant left summand preserves cofibrations. -/
theorem cofibration_coprod_id_map (f : A₁ ⟶ B₁) [Cofibration f]
    (X : C) [IsCofibrant A₁] [IsCofibrant X]
    [HasBinaryCoproduct X A₁] [HasBinaryCoproduct X B₁] :
    Cofibration (coprod.map (𝟙 X) f) := by
  let := coprod_cofibrant (A := X) (B := A₁)
  exact cofibration_of_isPushout (isPushout_coprod_map_id_left f).flip

/-- Adding a fixed cofibrant left summand preserves trivial cofibrations. -/
theorem weakEquivalence_coprod_id_map (f : A₁ ⟶ B₁) [Cofibration f]
    [WeakEquivalence f] (X : C) [IsCofibrant A₁] [IsCofibrant X]
    [HasBinaryCoproduct X A₁] [HasBinaryCoproduct X B₁] :
    WeakEquivalence (coprod.map (𝟙 X) f) := by
  let := coprod_cofibrant (A := X) (B := A₁)
  exact weakEquivalence_of_isPushout (isPushout_coprod_map_id_left f).flip

/-- Binary coproducts preserve cofibrations with cofibrant sources
(the binary case of Lemma 1.2.1(1)). -/
theorem cofibration_coprod_map (f : A₀ ⟶ B₀) (g : A₁ ⟶ B₁)
    [IsCofibrant A₀] [IsCofibrant A₁] [Cofibration f] [Cofibration g]
    [HasBinaryCoproduct A₀ A₁] [HasBinaryCoproduct B₀ B₁] :
    Cofibration (coprod.map f g) := by
  let := cofibrant_target f
  let := hasBinaryCoproduct B₀ A₁
  let := cofibration_coprod_map_id f A₁
  let := cofibration_coprod_id_map g B₀
  have h : coprod.map f (𝟙 A₁) ≫ coprod.map (𝟙 B₀) g = coprod.map f g := by
    ext <;> simp
  rw [← h]
  infer_instance

/-- Binary coproducts preserve trivial cofibrations with cofibrant sources
(the binary case of Lemma 1.2.1(1)). -/
theorem weakEquivalence_coprod_map (f : A₀ ⟶ B₀) (g : A₁ ⟶ B₁)
    [IsCofibrant A₀] [IsCofibrant A₁] [Cofibration f] [Cofibration g]
    [WeakEquivalence f] [WeakEquivalence g]
    [HasBinaryCoproduct A₀ A₁] [HasBinaryCoproduct B₀ B₁] :
    WeakEquivalence (coprod.map f g) := by
  let := cofibrant_target f
  let := hasBinaryCoproduct B₀ A₁
  let := weakEquivalence_coprod_map_id f A₁
  let := weakEquivalence_coprod_id_map g B₀
  have h : coprod.map f (𝟙 A₁) ≫ coprod.map (𝟙 B₀) g = coprod.map f g := by
    ext <;> simp
  rw [← h]
  infer_instance

end

/-- A finite family of cofibrant objects has a colimiting cofan with cofibrant point. -/
private theorem exists_cofibrant_cofan_fin : ∀ (n : ℕ) (A : Fin n → C),
    (∀ i, IsCofibrant (A i)) →
    ∃ c : Cofan A, Nonempty (IsColimit c) ∧ IsCofibrant c.pt
  | 0, A, _ => by
    let c : Cofan A := Cofan.mk (⊥_ C) (fun i ↦ Fin.elim0 i)
    refine ⟨c, ⟨?_⟩, (show IsCofibrant (⊥_ C) from inferInstance)⟩
    exact
      { desc := fun s ↦ initial.to s.pt
        fac := fun _ j ↦ Fin.elim0 j.as
        uniq := fun _ _ _ ↦ initial.hom_ext _ _ }
  | n + 1, A, hA => by
    obtain ⟨c, ⟨hc⟩, hcof⟩ := exists_cofibrant_cofan_fin n (fun i ↦ A i.succ)
      (fun i ↦ hA i.succ)
    let := hA 0
    let := hcof
    let := hasBinaryCoproduct (A 0) c.pt
    let b : BinaryCofan (A 0) c.pt := colimit.cocone (pair (A 0) c.pt)
    exact ⟨extendCofan c b, ⟨extendCofanIsColimit A hc (colimit.isColimit _)⟩,
      coprod_cofibrant⟩

/-- Finite coproduct existence from CF1–CF4, including the empty family. -/
theorem hasCoproduct_fin {n : ℕ} (A : Fin n → C) (hA : ∀ i, IsCofibrant (A i)) :
    HasCoproduct A := by
  obtain ⟨c, ⟨hc⟩, _⟩ := exists_cofibrant_cofan_fin n A hA
  exact ⟨⟨c, hc⟩⟩

/-- Any chosen coproduct of a finite cofibrant family is cofibrant. -/
theorem coproduct_fin_cofibrant {n : ℕ} (A : Fin n → C)
    (hA : ∀ i, IsCofibrant (A i)) [HasCoproduct A] : IsCofibrant (∐ A) := by
  obtain ⟨c, ⟨hc⟩, hcof⟩ := exists_cofibrant_cofan_fin n A hA
  let := hcof
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit _)
  let := cofibration_of_isIso e.hom
  exact cofibrant_target e.hom

end ABCCofibrations.ABCPrecofibrationCategory

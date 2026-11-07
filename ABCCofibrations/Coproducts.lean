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

Lemma 1.2.1(1) of Rădulescu-Banu, *Cofibrations in Homotopy Theory*:
finite coproducts of cofibrant objects exist and are cofibrant, and finite
coproducts preserve cofibrations and trivial cofibrations with cofibrant sources.
The indexing type may lie in any universe. Only CF1–CF4 are assumed.
The pushout arguments retain the cofibrancy hypotheses of CF3.
-/

public section

universe w v u

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

/-- Decompose a chosen finite coproduct into its head and tail. -/
private noncomputable def coproductFinSuccIso {n : ℕ} (A : Fin (n + 1) → C)
    [HasCoproduct A] [HasCoproduct (fun i : Fin n ↦ A i.succ)]
    [HasBinaryCoproduct (A 0) (∐ fun i : Fin n ↦ A i.succ)] :
    (A 0 ⨿ ∐ fun i : Fin n ↦ A i.succ) ≅ ∐ A :=
  (extendCofanIsColimit A (colimit.isColimit _)
    (colimit.isColimit (pair (A 0) (∐ fun i : Fin n ↦ A i.succ)))).coconePointUniqueUpToIso
      (colimit.isColimit _)

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [HasInitial C] [ABCPrecofibrationCategory C] in
@[reassoc (attr := simp)]
private theorem coproductFinSuccIso_zero {n : ℕ} (A : Fin (n + 1) → C)
    [HasCoproduct A] [HasCoproduct (fun i : Fin n ↦ A i.succ)]
    [HasBinaryCoproduct (A 0) (∐ fun i : Fin n ↦ A i.succ)] :
    coprod.inl ≫ (coproductFinSuccIso A).hom = Sigma.ι A 0 := by
  simpa [coproductFinSuccIso, extendCofan, BinaryCofan.inl, coprod.inl, Sigma.ι] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (extendCofanIsColimit A (colimit.isColimit _)
        (colimit.isColimit (pair (A 0) (∐ fun i : Fin n ↦ A i.succ))))
      (colimit.isColimit _) ⟨0⟩)

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [HasInitial C] [ABCPrecofibrationCategory C] in
@[reassoc (attr := simp)]
private theorem coproductFinSuccIso_succ {n : ℕ} (A : Fin (n + 1) → C)
    [HasCoproduct A] [HasCoproduct (fun i : Fin n ↦ A i.succ)]
    [HasBinaryCoproduct (A 0) (∐ fun i : Fin n ↦ A i.succ)] (i : Fin n) :
    Sigma.ι (fun j : Fin n ↦ A j.succ) i ≫ coprod.inr ≫
      (coproductFinSuccIso A).hom = Sigma.ι A i.succ := by
  simpa [coproductFinSuccIso, extendCofan, Category.assoc,
    BinaryCofan.inr, coprod.inr, Sigma.ι] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (extendCofanIsColimit A (colimit.isColimit _)
        (colimit.isColimit (pair (A 0) (∐ fun i : Fin n ↦ A i.succ))))
      (colimit.isColimit _) ⟨i.succ⟩)

/-- Simultaneous induction keeps the cofibration and trivial-cofibration
statements on the same coproduct decomposition. -/
private theorem coproduct_map_fin_properties : ∀ (n : ℕ) {A B : Fin n → C}
    (f : ∀ i, A i ⟶ B i) (_hA : ∀ i, IsCofibrant (A i))
    (_hf : ∀ i, Cofibration (f i)) [HasCoproduct A] [HasCoproduct B],
    Cofibration (Limits.Sigma.map f) ∧
      ((∀ i, WeakEquivalence (f i)) → WeakEquivalence (Limits.Sigma.map f))
  | 0, A, B, f, hA, _, _, _ => by
    let := coproduct_fin_cofibrant A hA
    let e : (∐ A) ≅ ∐ B :=
      { hom := Limits.Sigma.map f
        inv := Sigma.desc (fun i ↦ Fin.elim0 i)
        hom_inv_id := by ext i; exact Fin.elim0 i
        inv_hom_id := by ext i; exact Fin.elim0 i }
    let : IsIso (Limits.Sigma.map f) := e.isIso_hom
    exact ⟨cofibration_of_isIso e.hom, fun _ ↦ weakEquivalence_of_isIso e.hom⟩
  | n + 1, A, B, f, hA, hf, _, _ => by
    have hB (i) : IsCofibrant (B i) := by
      let := hA i
      let := hf i
      exact cofibrant_target (f i)
    let := hasCoproduct_fin (fun i : Fin n ↦ A i.succ) (fun i ↦ hA i.succ)
    let := hasCoproduct_fin (fun i : Fin n ↦ B i.succ) (fun i ↦ hB i.succ)
    let := coproduct_fin_cofibrant (fun i : Fin n ↦ A i.succ) (fun i ↦ hA i.succ)
    let := coproduct_fin_cofibrant (fun i : Fin n ↦ B i.succ) (fun i ↦ hB i.succ)
    let := hA 0
    let := hB 0
    let := hf 0
    let := hasBinaryCoproduct (A 0) (∐ fun i : Fin n ↦ A i.succ)
    let := hasBinaryCoproduct (B 0) (∐ fun i : Fin n ↦ B i.succ)
    obtain ⟨hc, hw⟩ := coproduct_map_fin_properties n (fun i ↦ f i.succ)
      (fun i ↦ hA i.succ) (fun i ↦ hf i.succ)
    let := hc
    let eA := coproductFinSuccIso A
    let eB := coproductFinSuccIso B
    let g := coprod.map (f 0) (Limits.Sigma.map (fun i : Fin n ↦ f i.succ))
    have fac : Limits.Sigma.map f = eA.inv ≫ g ≫ eB.hom := by
      apply (cancel_epi eA.hom).1
      simp only [Iso.hom_inv_id_assoc]
      apply coprod.hom_ext
      · simp [eA, eB, g]
      · apply Sigma.hom_ext
        intro i
        simp [eA, eB, g]
    let := coproduct_fin_cofibrant A hA
    let := cofibration_of_isIso eA.inv
    let := coprod_cofibrant (A := B 0) (B := ∐ fun i : Fin n ↦ B i.succ)
    let := cofibration_of_isIso eB.hom
    let := cofibration_coprod_map (f 0) (Limits.Sigma.map (fun i : Fin n ↦ f i.succ))
    refine ⟨?_, ?_⟩
    · rw [fac]
      infer_instance
    · intro hwe
      let := hwe 0
      let := hw (fun i ↦ hwe i.succ)
      let := weakEquivalence_coprod_map (f 0) (Limits.Sigma.map (fun i : Fin n ↦ f i.succ))
      let := weakEquivalence_of_isIso eA.inv
      let := weakEquivalence_of_isIso eB.hom
      rw [fac]
      infer_instance

/-- Finite coproducts preserve cofibrations with cofibrant sources. -/
theorem cofibration_coproduct_map_fin {n : ℕ} {A B : Fin n → C}
    (f : ∀ i, A i ⟶ B i) (hA : ∀ i, IsCofibrant (A i))
    (hf : ∀ i, Cofibration (f i)) [HasCoproduct A] [HasCoproduct B] :
    Cofibration (Limits.Sigma.map f) :=
  (coproduct_map_fin_properties n f hA hf).1

/-- Finite coproducts preserve trivial cofibrations with cofibrant sources. -/
theorem weakEquivalence_coproduct_map_fin {n : ℕ} {A B : Fin n → C}
    (f : ∀ i, A i ⟶ B i) (hA : ∀ i, IsCofibrant (A i))
    (hf : ∀ i, Cofibration (f i)) (hw : ∀ i, WeakEquivalence (f i))
    [HasCoproduct A] [HasCoproduct B] : WeakEquivalence (Limits.Sigma.map f) :=
  (coproduct_map_fin_properties n f hA hf).2 hw

/-- A coproduct of any finite family of cofibrant objects exists using CF1–CF4. -/
theorem hasCoproduct_finite {ι : Type w} [Finite ι] (A : ι → C)
    (hA : ∀ i, IsCofibrant (A i)) : HasCoproduct A := by
  let := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  let := hasCoproduct_fin (A ∘ e) (fun i ↦ hA (e i))
  exact hasCoproduct_of_equiv_of_iso (A ∘ e) A e.symm (fun i ↦ eqToIso (by simp))

/-- Every chosen coproduct of a finite cofibrant family is cofibrant. -/
theorem coproduct_finite_cofibrant {ι : Type w} [Finite ι] (A : ι → C)
    (hA : ∀ i, IsCofibrant (A i)) [HasCoproduct A] : IsCofibrant (∐ A) := by
  let := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  let := hasCoproduct_fin (A ∘ e) (fun i ↦ hA (e i))
  let := coproduct_fin_cofibrant (A ∘ e) (fun i ↦ hA (e i))
  let := cofibration_of_isIso (Sigma.reindex e A).hom
  exact cofibrant_target (Sigma.reindex e A).hom

/-- The cofibration assertion in Lemma 1.2.1(1), for any finite indexing type. -/
theorem cofibration_coproduct_map_finite {ι : Type w} [Finite ι] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (hA : ∀ i, IsCofibrant (A i))
    (hf : ∀ i, Cofibration (f i)) [HasCoproduct A] [HasCoproduct B] :
    Cofibration (Limits.Sigma.map f) := by
  let := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  have hB (i) : IsCofibrant (B i) := by
    let := hA i
    let := hf i
    exact cofibrant_target (f i)
  let := hasCoproduct_fin (A ∘ e) (fun i ↦ hA (e i))
  let := hasCoproduct_fin (B ∘ e) (fun i ↦ hB (e i))
  let := coproduct_finite_cofibrant A hA
  let := coproduct_fin_cofibrant (B ∘ e) (fun i ↦ hB (e i))
  let := cofibration_of_isIso (Sigma.reindex e A).inv
  let := cofibration_of_isIso (Sigma.reindex e B).hom
  let := cofibration_coproduct_map_fin (A := A ∘ e) (B := B ∘ e) (fun i ↦ f (e i))
    (fun i ↦ hA (e i)) (fun i ↦ hf (e i))
  have fac : Limits.Sigma.map f = (Sigma.reindex e A).inv ≫
      Limits.Sigma.map (f := B ∘ e) (g := A ∘ e) (fun i ↦ f (e i)) ≫ (Sigma.reindex e B).hom := by
    apply (cancel_epi (Sigma.reindex e A).hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply Sigma.hom_ext
    intro i
    simp
  rw [fac]
  infer_instance

/-- The trivial-cofibration assertion in Lemma 1.2.1(1), for any finite indexing type. -/
theorem weakEquivalence_coproduct_map_finite {ι : Type w} [Finite ι] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (hA : ∀ i, IsCofibrant (A i))
    (hf : ∀ i, Cofibration (f i)) (hw : ∀ i, WeakEquivalence (f i))
    [HasCoproduct A] [HasCoproduct B] : WeakEquivalence (Limits.Sigma.map f) := by
  let := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  have hB (i) : IsCofibrant (B i) := by
    let := hA i
    let := hf i
    exact cofibrant_target (f i)
  let := hasCoproduct_fin (A ∘ e) (fun i ↦ hA (e i))
  let := hasCoproduct_fin (B ∘ e) (fun i ↦ hB (e i))
  let := weakEquivalence_of_isIso (Sigma.reindex e A).inv
  let := weakEquivalence_of_isIso (Sigma.reindex e B).hom
  let := weakEquivalence_coproduct_map_fin (A := A ∘ e) (B := B ∘ e) (fun i ↦ f (e i))
    (fun i ↦ hA (e i)) (fun i ↦ hf (e i)) (fun i ↦ hw (e i))
  have fac : Limits.Sigma.map f = (Sigma.reindex e A).inv ≫
      Limits.Sigma.map (f := B ∘ e) (g := A ∘ e) (fun i ↦ f (e i)) ≫ (Sigma.reindex e B).hom := by
    apply (cancel_epi (Sigma.reindex e A).hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply Sigma.hom_ext
    intro i
    simp
  rw [fac]
  infer_instance

end ABCCofibrations.ABCPrecofibrationCategory

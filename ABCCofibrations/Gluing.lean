/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Factorization

/-!
# The gluing lemma

The cofibration and weak-equivalence assertions of Lemma 1.4.1(1) of
Rădulescu-Banu, *Cofibrations in Homotopy Theory*.

The proof uses the separate relative Brown comparisons only when both edges
are cofibrations, as proved here in `exists_relative_brown_of_cofibration_edges`.
Along arbitrary edges it uses `exists_compatible_brown_factorization`.
The invalid unrestricted comparison claims of Lemma 1.3.4(1) are not assumed.

The square and cube variables follow the paper: `f` denotes the top face,
`g` the bottom face, and `u` the vertical maps. The pushout faces are specified
by `IsPushout`, so the results apply to any representatives of the pushouts.
-/

public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

section Pasting

variable {C : Type u} [Category.{v} C]
  {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C}
  {f₁₂ : A₁ ⟶ A₂} {f₁₃ : A₁ ⟶ A₃} {f₂₄ : A₂ ⟶ A₄} {f₃₄ : A₃ ⟶ A₄}
  {g₁₂ : B₁ ⟶ B₂} {g₁₃ : B₁ ⟶ B₃} {g₂₄ : B₂ ⟶ B₄} {g₃₄ : B₃ ⟶ B₄}
  {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄}

/-- Pasting identifies the rear comparison as a cobase change of the front
comparison. This categorical fact has no cofibration hypotheses. -/
private theorem isPushout_gluing_comparisons
    (hA : IsPushout f₁₂ f₁₃ f₂₄ f₃₄) (hB : IsPushout g₁₂ g₁₃ g₂₄ g₃₄)
    (h₁₂ : f₁₂ ≫ u₂ = u₁ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₃ = u₁ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₄ = u₂ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₄ = u₃ ≫ g₃₄)
    [HasPushout f₁₂ u₁] [HasPushout f₃₄ u₃] :
    ∃ e : pushout f₁₂ u₁ ⟶ pushout f₃₄ u₃,
      IsPushout (pushout.desc u₂ g₁₂ h₁₂) e g₂₄
        (pushout.desc u₄ g₃₄ h₃₄) := by
  have heq : f₁₂ ≫ (f₂₄ ≫ pushout.inl f₃₄ u₃) =
      u₁ ≫ (g₁₃ ≫ pushout.inr f₃₄ u₃) := by
    rw [← Category.assoc, hA.w, Category.assoc, pushout.condition,
      ← Category.assoc, h₁₃, Category.assoc]
  let e := pushout.desc (f₂₄ ≫ pushout.inl f₃₄ u₃)
    (g₁₃ ≫ pushout.inr f₃₄ u₃) heq
  have outer : IsPushout f₁₂ (u₁ ≫ g₁₃)
      (pushout.inl f₁₂ u₁ ≫ e) (pushout.inr f₃₄ u₃) := by
    simpa [e, h₁₃] using hA.paste_vert (IsPushout.of_hasPushout f₃₄ u₃)
  have left := outer.of_top (by simp [e]) (IsPushout.of_hasPushout f₁₂ u₁)
  have right : pushout.desc u₂ g₁₂ h₁₂ ≫ g₂₄ =
      e ≫ pushout.desc u₄ g₃₄ h₃₄ := by
    apply pushout.hom_ext
    · simp [e, h₂₄]
    · simp [e, hB.w]
  have full : IsPushout (pushout.inr f₁₂ u₁ ≫ pushout.desc u₂ g₁₂ h₁₂)
      g₁₃ g₂₄ (pushout.inr f₃₄ u₃ ≫ pushout.desc u₄ g₃₄ h₃₄) := by
    simpa using hB
  exact ⟨e, full.of_left right left⟩

end Pasting

section Brown

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The separate relative comparisons needed for gluing are available when
both horizontal edges are cofibrations. This restricted result does not assert
Lemma 1.3.4(1) for arbitrary edges. -/
theorem exists_relative_brown_of_cofibration_edges
    {A₁ A₂ B₁ B₂ Z₁ : C} [IsCofibrant A₁] [IsCofibrant A₂]
    [IsCofibrant B₁] [IsCofibrant B₂]
    (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (a : A₁ ⟶ A₂) (b : B₁ ⟶ B₂)
    [Cofibration a] [Cofibration b] (h : f₁ ≫ b = a ≫ f₂)
    (i₁ : A₁ ⟶ Z₁) (p₁ : Z₁ ⟶ B₁) (s₁ : B₁ ⟶ Z₁)
    [Cofibration i₁] [WeakEquivalence p₁] [Cofibration s₁] [WeakEquivalence s₁]
    (h₁ : i₁ ≫ p₁ = f₁) (hs₁ : s₁ ≫ p₁ = 𝟙 B₁) :
    ∃ (Z₂ : C) (i₂ : A₂ ⟶ Z₂) (p₂ : Z₂ ⟶ B₂) (s₂ : B₂ ⟶ Z₂)
      (c : Z₁ ⟶ Z₂) (kA : pushout i₁ a ⟶ Z₂) (kB : pushout s₁ b ⟶ Z₂),
      IsCofibrant Z₂ ∧ Cofibration i₂ ∧ WeakEquivalence p₂ ∧
      Cofibration s₂ ∧ WeakEquivalence s₂ ∧ Cofibration c ∧
      Cofibration kA ∧ Cofibration kB ∧ WeakEquivalence kB ∧
      i₂ ≫ p₂ = f₂ ∧ s₂ ≫ p₂ = 𝟙 B₂ ∧
      i₁ ≫ c = a ≫ i₂ ∧ c ≫ p₂ = p₁ ≫ b ∧ s₁ ≫ c = b ≫ s₂ ∧
      pushout.inl i₁ a ≫ kA = c ∧ pushout.inr i₁ a ≫ kA = i₂ ∧
      pushout.inl s₁ b ≫ kB = c ∧ pushout.inr s₁ b ≫ kB = s₂ := by
  let := cofibrant_target i₁
  let := cofibration_of_isPushout (IsPushout.of_hasPushout i₁ a)
  let := cofibrant_target (pushout.inr i₁ a)
  let := cofibration_of_isPushout (IsPushout.of_hasPushout s₁ b)
  let := cofibrant_target (pushout.inr s₁ b)
  let := cofibration_of_isPushout (IsPushout.of_hasPushout i₁ a).flip
  let := cofibration_of_isPushout (IsPushout.of_hasPushout s₁ b).flip
  let l := pushout.inl i₁ a
  let r := pushout.inl s₁ b
  have hA : i₁ ≫ (p₁ ≫ b) = a ≫ f₂ := by rw [← Category.assoc, h₁, h]
  have hB : s₁ ≫ (p₁ ≫ b) = b ≫ 𝟙 B₂ := by simp [← Category.assoc, hs₁]
  let qA := pushout.desc (p₁ ≫ b) f₂ hA
  let qB := pushout.desc (p₁ ≫ b) (𝟙 B₂) hB
  have hq : l ≫ qA = r ≫ qB := by simp [l, r, qA, qB]
  let q := pushout.desc qA qB hq
  let := cofibration_of_isPushout (IsPushout.of_hasPushout l r)
  let := cofibrant_target (pushout.inr l r)
  obtain ⟨Z₂, k, p₂, hk, hp₂, hkp⟩ := factorization q
  let := hk
  let := hp₂
  let := cofibration_of_isPushout (IsPushout.of_hasPushout l r).flip
  let kA := pushout.inl l r ≫ k
  let kB := pushout.inr l r ≫ k
  have hkA : Cofibration kA := by dsimp [kA]; infer_instance
  have hkB : Cofibration kB := by dsimp [kB]; infer_instance
  let := hkA
  let := hkB
  let i₂ := pushout.inr i₁ a ≫ kA
  let s₂ := pushout.inr s₁ b ≫ kB
  let c := l ≫ kA
  have hi₂ : Cofibration i₂ := by dsimp [i₂]; infer_instance
  have hs₂ : Cofibration s₂ := by dsimp [s₂]; infer_instance
  have hc : Cofibration c := by dsimp [c]; infer_instance
  have hip : i₂ ≫ p₂ = f₂ := by simp [i₂, kA, Category.assoc, hkp, q, qA]
  have hsp : s₂ ≫ p₂ = 𝟙 B₂ := by simp [s₂, kB, Category.assoc, hkp, q, qB]
  have hsection : WeakEquivalence s₂ := by
    let := weakEquivalence_of_isIso (𝟙 B₂)
    exact weakEquivalence_of_postcomp_of_fac hsp
  have hr : l ≫ kA = r ≫ kB := by
    dsimp [kA, kB]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  have hisq : i₁ ≫ c = a ≫ i₂ := by
    dsimp [c, l, i₂]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  have hssq : s₁ ≫ c = b ≫ s₂ := by
    rw [show c = r ≫ kB from hr]
    dsimp [r, s₂]
    rw [← Category.assoc, pushout.condition, Category.assoc]
  have hcp : c ≫ p₂ = p₁ ≫ b := by
    simp [c, l, kA, Category.assoc, hkp, q, qA]
  have hinr : WeakEquivalence (pushout.inr s₁ b) :=
    weakEquivalence_of_isPushout (IsPushout.of_hasPushout s₁ b)
  let := hinr
  let := hsection
  have hkBw : WeakEquivalence kB :=
    weakEquivalence_of_precomp_of_fac (show pushout.inr s₁ b ≫ kB = s₂ from rfl)
  let := hi₂
  exact ⟨Z₂, i₂, p₂, s₂, c, kA, kB, cofibrant_target i₂,
    hi₂, hp₂, hs₂, hsection, hc, hkA, hkB, hkBw, hip, hsp, hisq, hcp, hssq,
    rfl, rfl, hr.symm, rfl⟩

/-- Transfer a comparison cofibration to the opposite orientation of its
pushout, retaining the caller's chosen pushout objects. -/
private theorem cofibration_desc_of_comparison
    {A X Y Z : C} [IsCofibrant A] [IsCofibrant X]
    (i : A ⟶ Y) (a : A ⟶ X) [Cofibration i]
    [HasPushout i a] [HasPushout a i]
    (c : Y ⟶ Z) (j : X ⟶ Z) (h : a ≫ j = i ≫ c)
    (k : pushout i a ⟶ Z) [Cofibration k]
    (hl : pushout.inl i a ≫ k = c) (hr : pushout.inr i a ≫ k = j) :
    Cofibration (pushout.desc j c h) := by
  let := cofibration_of_isPushout (IsPushout.of_hasPushout a i).flip
  let := cofibrant_target (pushout.inl a i)
  let := cofibration_of_isIso (pushoutSymmetry a i).hom
  have he : pushout.desc j c h = (pushoutSymmetry a i).hom ≫ k := by
    apply pushout.hom_ext <;> simp [hl, hr]
  rw [he]
  infer_instance

end Brown

section Cube

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C}
  [IsCofibrant A₁] [IsCofibrant A₃] [IsCofibrant B₁] [IsCofibrant B₃]
  {f₁₂ : A₁ ⟶ A₂} {f₁₃ : A₁ ⟶ A₃} {f₂₄ : A₂ ⟶ A₄} {f₃₄ : A₃ ⟶ A₄}
  {g₁₂ : B₁ ⟶ B₂} {g₁₃ : B₁ ⟶ B₃} {g₂₄ : B₂ ⟶ B₄} {g₃₄ : B₃ ⟶ B₄}
  {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄}
  [Cofibration f₁₂] [Cofibration g₁₂]

omit [Cofibration g₁₂] in
/-- The cofibration part of the gluing lemma, Lemma 1.4.1(1)(a).
The front and rear comparisons are the canonical maps out of the respective
chosen pushouts. -/
theorem gluing_cofibration
    (hA : IsPushout f₁₂ f₁₃ f₂₄ f₃₄) (hB : IsPushout g₁₂ g₁₃ g₂₄ g₃₄)
    (h₁₂ : f₁₂ ≫ u₂ = u₁ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₃ = u₁ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₄ = u₂ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₄ = u₃ ≫ g₃₄)
    [Cofibration u₁] [Cofibration u₃] [HasPushout f₃₄ u₃]
    [Cofibration (pushout.desc u₂ g₁₂ h₁₂)] :
    Cofibration u₂ ∧ Cofibration u₄ ∧ Cofibration (pushout.desc u₄ g₃₄ h₃₄) := by
  let := cofibration_of_isPushout hA
  let := cofibrant_target f₁₂
  let := cofibrant_target f₃₄
  let := cofibration_of_isPushout (IsPushout.of_hasPushout f₁₂ u₁)
  let := cofibrant_target (pushout.inr f₁₂ u₁)
  let := cofibration_of_isPushout (IsPushout.of_hasPushout f₃₄ u₃)
  let := cofibrant_target (pushout.inr f₃₄ u₃)
  obtain ⟨e, he⟩ := isPushout_gluing_comparisons hA hB h₁₂ h₁₃ h₂₄ h₃₄
  let := cofibration_of_isPushout he
  have hfront : Cofibration (pushout.inl f₁₂ u₁) :=
    cofibration_of_isPushout (IsPushout.of_hasPushout f₁₂ u₁).flip
  have hrear : Cofibration (pushout.inl f₃₄ u₃) :=
    cofibration_of_isPushout (IsPushout.of_hasPushout f₃₄ u₃).flip
  let := hfront
  let := hrear
  refine ⟨?_, ?_, inferInstance⟩
  · have h : Cofibration (pushout.inl f₁₂ u₁ ≫ pushout.desc u₂ g₁₂ h₁₂) :=
      inferInstance
    simpa using h
  · have h : Cofibration (pushout.inl f₃₄ u₃ ≫ pushout.desc u₄ g₃₄ h₃₄) :=
      inferInstance
    simpa using h

omit [Cofibration g₁₂] in
/-- The weak-equivalence gluing argument when the vertical maps and the front
comparison have the cofibration properties of part (a). -/
theorem gluing_weakEquivalence_of_cofibrations
    (hA : IsPushout f₁₂ f₁₃ f₂₄ f₃₄) (hB : IsPushout g₁₂ g₁₃ g₂₄ g₃₄)
    (h₁₂ : f₁₂ ≫ u₂ = u₁ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₃ = u₁ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₄ = u₂ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₄ = u₃ ≫ g₃₄)
    [Cofibration u₁] [Cofibration u₃] [HasPushout f₃₄ u₃]
    [Cofibration (pushout.desc u₂ g₁₂ h₁₂)]
    [WeakEquivalence u₁] [WeakEquivalence u₂] [WeakEquivalence u₃] :
    WeakEquivalence u₄ := by
  let := cofibration_of_isPushout hA
  let := cofibrant_target f₁₂
  let := cofibrant_target f₃₄
  let := cofibration_of_isPushout (IsPushout.of_hasPushout f₁₂ u₁)
  let := cofibrant_target (pushout.inr f₁₂ u₁)
  let := cofibration_of_isPushout (IsPushout.of_hasPushout f₃₄ u₃)
  let := cofibrant_target (pushout.inr f₃₄ u₃)
  have hfront : WeakEquivalence (pushout.inl f₁₂ u₁) :=
    weakEquivalence_of_isPushout (IsPushout.of_hasPushout f₁₂ u₁).flip
  let := hfront
  have hfac : pushout.inl f₁₂ u₁ ≫ pushout.desc u₂ g₁₂ h₁₂ = u₂ := by simp
  let := weakEquivalence_of_precomp_of_fac hfac
  obtain ⟨e, he⟩ := isPushout_gluing_comparisons hA hB h₁₂ h₁₃ h₂₄ h₃₄
  let := weakEquivalence_of_isPushout he
  have hrear : WeakEquivalence (pushout.inl f₃₄ u₃) :=
    weakEquivalence_of_isPushout (IsPushout.of_hasPushout f₃₄ u₃).flip
  let := hrear
  have h : WeakEquivalence (pushout.inl f₃₄ u₃ ≫ pushout.desc u₄ g₃₄ h₃₄) :=
    inferInstance
  simpa using h

/-- The weak-equivalence gluing lemma, Lemma 1.4.1(1)(b), for arbitrary
weak equivalences on the three vertices of the span. The proof uses relative
Brown comparisons only along cofibration edges. -/
theorem gluing_weakEquivalence
    (hA : IsPushout f₁₂ f₁₃ f₂₄ f₃₄) (hB : IsPushout g₁₂ g₁₃ g₂₄ g₃₄)
    (h₁₂ : f₁₂ ≫ u₂ = u₁ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₃ = u₁ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₄ = u₂ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₄ = u₃ ≫ g₃₄)
    [WeakEquivalence u₁] [WeakEquivalence u₂] [WeakEquivalence u₃] :
    WeakEquivalence u₄ := by
  let := cofibrant_target f₁₂
  let := cofibrant_target g₁₂
  let := cofibration_of_isPushout hA
  let := cofibration_of_isPushout hB
  let := cofibrant_target f₃₄
  let := cofibrant_target g₃₄
  let := hasBinaryCoproduct A₁ B₁
  obtain ⟨Z₁, i₁, p₁, s₁, hZ₁, hi₁, hp₁, hs₁, hsw₁, hj₁, hip₁, hsp₁⟩ :=
    exists_brown_factorization_with_coprod u₁
  let := hZ₁
  let := hi₁
  let := hp₁
  let := hs₁
  let := hsw₁
  let := hj₁
  have hiw₁ : WeakEquivalence i₁ := weakEquivalence_of_postcomp_of_fac hip₁
  let := hiw₁
  obtain ⟨Z₂, i₂, p₂, s₂, c₁₂, kA, kB, hZ₂, hi₂, hp₂, hs₂, hsw₂,
    hc₁₂, hkA, hkB, _hkwB, hip₂, hsp₂, hic₁₂, hpc₁₂, hsc₁₂,
    hkAl, hkAr, hkBl, hkBr⟩ :=
    exists_relative_brown_of_cofibration_edges u₁ u₂ f₁₂ g₁₂ h₁₂.symm
      i₁ p₁ s₁ hip₁ hsp₁
  let := hZ₂
  let := hi₂
  let := hp₂
  let := hs₂
  let := hsw₂
  let := hc₁₂
  let := hkA
  let := hkB
  have hiw₂ : WeakEquivalence i₂ := weakEquivalence_of_postcomp_of_fac hip₂
  let := hiw₂
  let := hasBinaryCoproduct A₃ B₃
  let := coprod_cofibrant (A := A₁) (B := B₁)
  let := coprod_cofibrant (A := A₃) (B := B₃)
  obtain ⟨Z₃, i₃, p₃, s₃, c₁₃, _, hZ₃, hi₃, hp₃, hs₃, hsw₃, _, _,
    hip₃, hsp₃, hic₁₃, hpc₁₃, hsc₁₃, _, _⟩ :=
    exists_compatible_brown_factorization u₁ u₃ f₁₃ g₁₃ h₁₃.symm
      i₁ p₁ s₁ hip₁ hsp₁
  let := hZ₃
  let := hi₃
  let := hp₃
  let := hs₃
  let := hsw₃
  have hiw₃ : WeakEquivalence i₃ := weakEquivalence_of_postcomp_of_fac hip₃
  let := hiw₃
  have hv : f₁₂ ≫ (i₂ ≫ pushout.inl c₁₂ c₁₃) =
      f₁₃ ≫ (i₃ ≫ pushout.inr c₁₂ c₁₃) := by
    rw [← Category.assoc, ← hic₁₂, Category.assoc, pushout.condition,
      ← Category.assoc, hic₁₃, Category.assoc]
  let v := hA.desc (i₂ ≫ pushout.inl c₁₂ c₁₃) (i₃ ≫ pushout.inr c₁₂ c₁₃) hv
  have hw : g₁₂ ≫ (s₂ ≫ pushout.inl c₁₂ c₁₃) =
      g₁₃ ≫ (s₃ ≫ pushout.inr c₁₂ c₁₃) := by
    rw [← Category.assoc, ← hsc₁₂, Category.assoc, pushout.condition,
      ← Category.assoc, hsc₁₃, Category.assoc]
  let w := hB.desc (s₂ ≫ pushout.inl c₁₂ c₁₃) (s₃ ≫ pushout.inr c₁₂ c₁₃) hw
  have hr : c₁₂ ≫ (p₂ ≫ g₂₄) = c₁₃ ≫ (p₃ ≫ g₃₄) := by
    rw [← Category.assoc, hpc₁₂, Category.assoc, hB.w,
      ← Category.assoc, ← hpc₁₃, Category.assoc]
  let r := pushout.desc (p₂ ≫ g₂₄) (p₃ ≫ g₃₄) hr
  have hvr : v ≫ r = u₄ := by
    apply hA.hom_ext
    · suffices h : i₂ ≫ p₂ ≫ g₂₄ = f₂₄ ≫ u₄ by simpa [v, r] using h
      rw [← Category.assoc, hip₂]
      exact h₂₄.symm
    · suffices h : i₃ ≫ p₃ ≫ g₃₄ = f₃₄ ≫ u₄ by simpa [v, r] using h
      rw [← Category.assoc, hip₃]
      exact h₃₄.symm
  have hwr : w ≫ r = 𝟙 _ := by
    apply hB.hom_ext
    · suffices h : s₂ ≫ p₂ ≫ g₂₄ = g₂₄ by simpa [w, r] using h
      rw [← Category.assoc, hsp₂, Category.id_comp]
    · suffices h : s₃ ≫ p₃ ≫ g₃₄ = g₃₄ by simpa [w, r] using h
      rw [← Category.assoc, hsp₃, Category.id_comp]
  have hvcomp : Cofibration (pushout.desc i₂ c₁₂ hic₁₂.symm) :=
    cofibration_desc_of_comparison i₁ f₁₂ c₁₂ i₂ hic₁₂.symm kA hkAl hkAr
  let := hvcomp
  have hwcomp : Cofibration (pushout.desc s₂ c₁₂ hsc₁₂.symm) :=
    cofibration_desc_of_comparison s₁ g₁₂ c₁₂ s₂ hsc₁₂.symm kB hkBl hkBr
  let := hwcomp
  have hvw : WeakEquivalence v :=
    gluing_weakEquivalence_of_cofibrations hA (IsPushout.of_hasPushout c₁₂ c₁₃)
      hic₁₂.symm hic₁₃.symm (by simp [v]) (by simp [v])
  have hww : WeakEquivalence w :=
    gluing_weakEquivalence_of_cofibrations hB (IsPushout.of_hasPushout c₁₂ c₁₃)
      hsc₁₂.symm hsc₁₃.symm (by simp [w]) (by simp [w])
  let := hvw
  let := hww
  let := weakEquivalence_of_isIso (𝟙 (B₄))
  let := weakEquivalence_of_precomp_of_fac hwr
  have h : WeakEquivalence (v ≫ r) := inferInstance
  rwa [hvr] at h

end Cube

end ABCCofibrations.ABCPrecofibrationCategory

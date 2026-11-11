/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Extension
public import ABCCofibrations.FibrationExtension

/-!
# Composing relative pushout comparisons (Lemma 9.3.3)

Given a map of composable cofibrations `A₀ ⟶ A₁ ⟶ A₂` to `B₀ ⟶ B₁ ⟶ B₂`, if the
comparison maps `B₀ ⊔_{A₀} A₁ ⟶ B₁` and `B₁ ⊔_{A₁} A₂ ⟶ B₂` are cofibrations
(resp. weak equivalences), so is `B₀ ⊔_{A₀} A₂ ⟶ B₂`. The pushouts are given by
arbitrary `IsPushout` representatives, and the fibration statements follow in
the opposite category.

Following the paper, the comparison `B₀ ⊔_{A₀} A₂ ⟶ B₂` factors as `d ∘ c`,
where `c : B₀ ⊔_{A₀} A₂ ⟶ B₁ ⊔_{A₁} A₂` is a pushout of the first comparison
along the cofibration `b : B₀ ⊔_{A₀} A₁ ⟶ B₀ ⊔_{A₀} A₂`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {A₀ A₁ A₂ B₀ B₁ B₂ : C} [IsCofibrant A₀] [IsCofibrant B₀] [IsCofibrant B₁]
  {a₀₁ : A₀ ⟶ A₁} {a₁₂ : A₁ ⟶ A₂} {f₀ : A₀ ⟶ B₀} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
  {b₀₁ : B₀ ⟶ B₁} {b₁₂ : B₁ ⟶ B₂} [Cofibration a₀₁] [Cofibration a₁₂]
  {P₀₁ P₁₂ P₀₂ : C} {l₀₁ : A₁ ⟶ P₀₁} {r₀₁ : B₀ ⟶ P₀₁} {l₁₂ : A₂ ⟶ P₁₂} {r₁₂ : B₁ ⟶ P₁₂}
  {l₀₂ : A₂ ⟶ P₀₂} {r₀₂ : B₀ ⟶ P₀₂}

omit [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C] [IsCofibrant A₀] [IsCofibrant B₀] [IsCofibrant B₁]
  [Cofibration a₀₁] [Cofibration a₁₂] in
/-- The factorization of the composite comparison through a pushout of the
first comparison along a cofibration. -/
private lemma exists_comparison_factorization
    (w₀₁ : a₀₁ ≫ f₁ = f₀ ≫ b₀₁)
    (h₀₁ : IsPushout a₀₁ f₀ l₀₁ r₀₁) (h₁₂ : IsPushout a₁₂ f₁ l₁₂ r₁₂)
    (h₀₂ : IsPushout (a₀₁ ≫ a₁₂) f₀ l₀₂ r₀₂)
    {c₀₁ : P₀₁ ⟶ B₁} (hc₀₁ : l₀₁ ≫ c₀₁ = f₁) (hc₀₁' : r₀₁ ≫ c₀₁ = b₀₁)
    {c₁₂ : P₁₂ ⟶ B₂} (hc₁₂ : l₁₂ ≫ c₁₂ = f₂) (hc₁₂' : r₁₂ ≫ c₁₂ = b₁₂)
    {c₀₂ : P₀₂ ⟶ B₂} (hc₀₂ : l₀₂ ≫ c₀₂ = f₂) (hc₀₂' : r₀₂ ≫ c₀₂ = b₀₁ ≫ b₁₂) :
    ∃ (b : P₀₁ ⟶ P₀₂) (c : P₀₂ ⟶ P₁₂), IsPushout a₁₂ l₀₁ l₀₂ b ∧
      IsPushout c₀₁ b r₁₂ c ∧ c₀₂ = c ≫ c₁₂ := by
  let b := h₀₁.desc (a₁₂ ≫ l₀₂) r₀₂ (by rw [← Category.assoc, h₀₂.w])
  have hb₁ : l₀₁ ≫ b = a₁₂ ≫ l₀₂ := h₀₁.inl_desc _ _ _
  have hb₂ : r₀₁ ≫ b = r₀₂ := h₀₁.inr_desc _ _ _
  have hS : IsPushout a₁₂ l₀₁ l₀₂ b :=
    IsPushout.of_left (by rw [hb₂]; exact h₀₂) hb₁.symm h₀₁
  let c := h₀₂.desc l₁₂ (b₀₁ ≫ r₁₂) (by
    rw [Category.assoc, h₁₂.w, ← Category.assoc, w₀₁, Category.assoc])
  have hc₁ : l₀₂ ≫ c = l₁₂ := h₀₂.inl_desc _ _ _
  have hc₂ : r₀₂ ≫ c = b₀₁ ≫ r₁₂ := h₀₂.inr_desc _ _ _
  have hbc : c₀₁ ≫ r₁₂ = b ≫ c := by
    apply h₀₁.hom_ext
    · rw [reassoc_of% hc₀₁, reassoc_of% hb₁, hc₁, h₁₂.w]
    · rw [reassoc_of% hc₀₁', reassoc_of% hb₂, hc₂]
  have hT : IsPushout c₀₁ b r₁₂ c :=
    IsPushout.of_left (by rw [hc₀₁, hc₁]; exact h₁₂.flip) hbc hS.flip
  refine ⟨b, c, hS, hT, ?_⟩
  apply h₀₂.hom_ext
  · rw [hc₀₂, reassoc_of% hc₁, hc₁₂]
  · rw [hc₀₂', reassoc_of% hc₂, hc₁₂']

omit [IsCofibrant B₁] in
/-- **Lemma 9.3.3(1)(a).** If the comparisons `B₀ ⊔_{A₀} A₁ ⟶ B₁` and
`B₁ ⊔_{A₁} A₂ ⟶ B₂` are cofibrations, so is `B₀ ⊔_{A₀} A₂ ⟶ B₂`. (The paper's
cofibrancy of `B₁` and `B₂` is not needed.) -/
theorem cofibration_comparison_comp
    (w₀₁ : a₀₁ ≫ f₁ = f₀ ≫ b₀₁)
    (h₀₁ : IsPushout a₀₁ f₀ l₀₁ r₀₁) (h₁₂ : IsPushout a₁₂ f₁ l₁₂ r₁₂)
    (h₀₂ : IsPushout (a₀₁ ≫ a₁₂) f₀ l₀₂ r₀₂)
    (c₀₁ : P₀₁ ⟶ B₁) (hc₀₁ : l₀₁ ≫ c₀₁ = f₁) (hc₀₁' : r₀₁ ≫ c₀₁ = b₀₁)
    (c₁₂ : P₁₂ ⟶ B₂) (hc₁₂ : l₁₂ ≫ c₁₂ = f₂) (hc₁₂' : r₁₂ ≫ c₁₂ = b₁₂)
    (c₀₂ : P₀₂ ⟶ B₂) (hc₀₂ : l₀₂ ≫ c₀₂ = f₂) (hc₀₂' : r₀₂ ≫ c₀₂ = b₀₁ ≫ b₁₂)
    [Cofibration c₀₁] [Cofibration c₁₂] : Cofibration c₀₂ := by
  obtain ⟨b, c, hS, hT, rfl⟩ := exists_comparison_factorization w₀₁ h₀₁ h₁₂ h₀₂
    hc₀₁ hc₀₁' hc₁₂ hc₁₂' hc₀₂ hc₀₂'
  have : IsCofibrant A₁ := cofibrant_target a₀₁
  have : Cofibration r₀₁ := cofibration_of_isPushout h₀₁
  have : IsCofibrant P₀₁ := cofibrant_target r₀₁
  have : Cofibration b := cofibration_of_isPushout hS
  have : IsCofibrant P₀₂ := cofibrant_target b
  have : Cofibration c := cofibration_of_isPushout hT
  infer_instance

/-- **Lemma 9.3.3(1)(b).** If the comparisons `B₀ ⊔_{A₀} A₁ ⟶ B₁` and
`B₁ ⊔_{A₁} A₂ ⟶ B₂` are weak equivalences, so is `B₀ ⊔_{A₀} A₂ ⟶ B₂`. -/
theorem weakEquivalence_comparison_comp
    (w₀₁ : a₀₁ ≫ f₁ = f₀ ≫ b₀₁)
    (h₀₁ : IsPushout a₀₁ f₀ l₀₁ r₀₁) (h₁₂ : IsPushout a₁₂ f₁ l₁₂ r₁₂)
    (h₀₂ : IsPushout (a₀₁ ≫ a₁₂) f₀ l₀₂ r₀₂)
    (c₀₁ : P₀₁ ⟶ B₁) (hc₀₁ : l₀₁ ≫ c₀₁ = f₁) (hc₀₁' : r₀₁ ≫ c₀₁ = b₀₁)
    (c₁₂ : P₁₂ ⟶ B₂) (hc₁₂ : l₁₂ ≫ c₁₂ = f₂) (hc₁₂' : r₁₂ ≫ c₁₂ = b₁₂)
    (c₀₂ : P₀₂ ⟶ B₂) (hc₀₂ : l₀₂ ≫ c₀₂ = f₂) (hc₀₂' : r₀₂ ≫ c₀₂ = b₀₁ ≫ b₁₂)
    [WeakEquivalence c₀₁] [WeakEquivalence c₁₂] : WeakEquivalence c₀₂ := by
  obtain ⟨b, c, hS, hT, rfl⟩ := exists_comparison_factorization w₀₁ h₀₁ h₁₂ h₀₂
    hc₀₁ hc₀₁' hc₁₂ hc₁₂' hc₀₂ hc₀₂'
  have : IsCofibrant A₁ := cofibrant_target a₀₁
  have : Cofibration r₀₁ := cofibration_of_isPushout h₀₁
  have : IsCofibrant P₀₁ := cofibrant_target r₀₁
  have : Cofibration b := cofibration_of_isPushout hS
  have : WeakEquivalence c := weakEquivalence_of_isPushout_of_cofibration hT.flip
  infer_instance

end ABCCofibrations.ABCPrecofibrationCategory

namespace ABCCofibrations.ABCPrefibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {A₀ A₁ A₂ B₀ B₁ B₂ : C} [IsFibrant A₀] [IsFibrant B₀] [IsFibrant A₁]
  {b₁₀ : B₁ ⟶ B₀} {b₂₁ : B₂ ⟶ B₁} {f₀ : A₀ ⟶ B₀} {f₁ : A₁ ⟶ B₁} {f₂ : A₂ ⟶ B₂}
  {a₁₀ : A₁ ⟶ A₀} {a₂₁ : A₂ ⟶ A₁} [Fibration b₁₀] [Fibration b₂₁]
  {P₀₁ P₁₂ P₀₂ : C} {l₀₁ : P₀₁ ⟶ B₁} {r₀₁ : P₀₁ ⟶ A₀} {l₁₂ : P₁₂ ⟶ B₂} {r₁₂ : P₁₂ ⟶ A₁}
  {l₀₂ : P₀₂ ⟶ B₂} {r₀₂ : P₀₂ ⟶ A₀}

omit [IsFibrant A₁] in
/-- **Lemma 9.3.3(2)(a).** Given a map from `A₂ ⟶ A₁ ⟶ A₀` to a sequence of
fibrations `B₂ ⟶ B₁ ⟶ B₀`, if the comparisons `A₁ ⟶ B₁ ×_{B₀} A₀` and
`A₂ ⟶ B₂ ×_{B₁} A₁` are fibrations, so is `A₂ ⟶ B₂ ×_{B₀} A₀`. -/
theorem fibration_comparison_comp
    (w₁₀ : f₁ ≫ b₁₀ = a₁₀ ≫ f₀)
    (h₀₁ : IsPullback l₀₁ r₀₁ b₁₀ f₀) (h₁₂ : IsPullback l₁₂ r₁₂ b₂₁ f₁)
    (h₀₂ : IsPullback l₀₂ r₀₂ (b₂₁ ≫ b₁₀) f₀)
    (c₀₁ : A₁ ⟶ P₀₁) (hc₀₁ : c₀₁ ≫ l₀₁ = f₁) (hc₀₁' : c₀₁ ≫ r₀₁ = a₁₀)
    (c₁₂ : A₂ ⟶ P₁₂) (hc₁₂ : c₁₂ ≫ l₁₂ = f₂) (hc₁₂' : c₁₂ ≫ r₁₂ = a₂₁)
    (c₀₂ : A₂ ⟶ P₀₂) (hc₀₂ : c₀₂ ≫ l₀₂ = f₂) (hc₀₂' : c₀₂ ≫ r₀₂ = a₂₁ ≫ a₁₀)
    [Fibration c₀₁] [Fibration c₁₂] : Fibration c₀₂ := by
  have : Cofibration b₁₀.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration b₂₁.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration c₀₁.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration c₁₂.op := (cofibration_op_iff _).2 ‹_›
  exact (cofibration_op_iff _).1 (cofibration_comparison_comp
    (by rw [← op_comp, ← op_comp, w₁₀]) h₀₁.op.flip h₁₂.op.flip h₀₂.op.flip
    c₀₁.op (by rw [← op_comp, hc₀₁]) (by rw [← op_comp, hc₀₁'])
    c₁₂.op (by rw [← op_comp, hc₁₂]) (by rw [← op_comp, hc₁₂'])
    c₀₂.op (by rw [← op_comp, hc₀₂]) (by rw [← op_comp, hc₀₂', op_comp]))

/-- **Lemma 9.3.3(2)(b).** Given a map from `A₂ ⟶ A₁ ⟶ A₀` to a sequence of
fibrations `B₂ ⟶ B₁ ⟶ B₀`, if the comparisons `A₁ ⟶ B₁ ×_{B₀} A₀` and
`A₂ ⟶ B₂ ×_{B₁} A₁` are weak equivalences, so is `A₂ ⟶ B₂ ×_{B₀} A₀`. -/
theorem weakEquivalence_comparison_comp
    (w₁₀ : f₁ ≫ b₁₀ = a₁₀ ≫ f₀)
    (h₀₁ : IsPullback l₀₁ r₀₁ b₁₀ f₀) (h₁₂ : IsPullback l₁₂ r₁₂ b₂₁ f₁)
    (h₀₂ : IsPullback l₀₂ r₀₂ (b₂₁ ≫ b₁₀) f₀)
    (c₀₁ : A₁ ⟶ P₀₁) (hc₀₁ : c₀₁ ≫ l₀₁ = f₁) (hc₀₁' : c₀₁ ≫ r₀₁ = a₁₀)
    (c₁₂ : A₂ ⟶ P₁₂) (hc₁₂ : c₁₂ ≫ l₁₂ = f₂) (hc₁₂' : c₁₂ ≫ r₁₂ = a₂₁)
    (c₀₂ : A₂ ⟶ P₀₂) (hc₀₂ : c₀₂ ≫ l₀₂ = f₂) (hc₀₂' : c₀₂ ≫ r₀₂ = a₂₁ ≫ a₁₀)
    [WeakEquivalence c₀₁] [WeakEquivalence c₁₂] : WeakEquivalence c₀₂ := by
  have : Cofibration b₁₀.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration b₂₁.op := (cofibration_op_iff _).2 ‹_›
  have : WeakEquivalence c₀₁.op := (weakEquivalences_op_iff _).2 ‹_›
  have : WeakEquivalence c₁₂.op := (weakEquivalences_op_iff _).2 ‹_›
  exact (weakEquivalences_op_iff _).1 (ABCPrecofibrationCategory.weakEquivalence_comparison_comp
    (by rw [← op_comp, ← op_comp, w₁₀]) h₀₁.op.flip h₁₂.op.flip h₀₂.op.flip
    c₀₁.op (by rw [← op_comp, hc₀₁]) (by rw [← op_comp, hc₀₁'])
    c₁₂.op (by rw [← op_comp, hc₁₂]) (by rw [← op_comp, hc₁₂'])
    c₀₂.op (by rw [← op_comp, hc₀₂]) (by rw [← op_comp, hc₀₂', op_comp]))

end ABCCofibrations.ABCPrefibrationCategory

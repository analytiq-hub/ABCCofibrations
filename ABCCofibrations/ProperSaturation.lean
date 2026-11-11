/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SaturatedStructure
public import ABCCofibrations.RightProperness

/-!
# Saturation of left proper precofibration categories (§7.2)

Lemma 7.2.10: in a left proper precofibration category, a map (between arbitrary
objects) has a left inverse in the homotopy category iff some left proper map
`f'` makes `f'f` a weak equivalence, and dually for right proper prefibration
categories. Proposition 7.2.11(1): left proper maps for `W` are left proper for
the saturation `W̄`. Theorem 7.2.12(1): the saturated precofibration structure of
a left proper precofibration category is left proper.

For Lemma 7.2.10(1) we replace `A` cofibrantly, factor, apply Lemma 7.2.1, and
push the resulting cofibration out along the weak equivalence to `B`; left
properness makes the comparison a weak equivalence.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

namespace ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  [LeftProper C] {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Lemma 7.2.10(1)(a).** In a left proper precofibration category, a map
`f : A ⟶ B` has a left inverse in the homotopy category iff there is a left
proper map `f' : B ⟶ B'` with `f'f` a weak equivalence. -/
theorem exists_leftInverse_iff_leftProper {A B : C} (f : A ⟶ B) :
    (∃ g : L.obj B ⟶ L.obj A, L.map f ≫ g = 𝟙 _) ↔
      ∃ (B' : C) (f' : B ⟶ B'), IsLeftProper f' ∧ WeakEquivalence (f ≫ f') := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨A₁, r₁, hA₁, hr₁⟩ := exists_cofibrant_replacement A
    have := hA₁
    obtain ⟨B₁, f₁, q, hf₁, hq, hfac⟩ := factorization (r₁ ≫ f)
    have := hf₁
    have := cofibrant_target f₁
    have := Localization.inverts L (weakEquivalences C) r₁ hr₁.mem
    have := Localization.inverts L (weakEquivalences C) q hq.mem
    obtain ⟨B'₁, f'₁, hf'₁, hw⟩ := (exists_leftInverse_iff L f₁).1
      ⟨L.map q ≫ g ≫ inv (L.map r₁), by
        rw [← Category.assoc, ← L.map_comp, hfac, L.map_comp, Category.assoc,
          reassoc_of% hg, IsIso.hom_inv_id]⟩
    have := hf'₁
    have hlp : IsLeftProper f'₁ := isLeftProper_of_cofibration f'₁
    have := hlp.hasPushout q
    let sq := IsPushout.of_hasPushout q f'₁
    have hq' : WeakEquivalence (pushout.inr q f'₁) := hlp.weakEquivalence IsPushout.of_id_fst sq
    refine ⟨_, pushout.inl q f'₁, hlp.of_isPushout sq, ?_⟩
    have : WeakEquivalence (r₁ ≫ f ≫ pushout.inl q f'₁) := by
      rw [← Category.assoc, ← hfac, Category.assoc, sq.w, ← Category.assoc]
      infer_instance
    exact weakEquivalence_of_precomp r₁ _
  · rintro ⟨B', f', -, hw⟩
    have := Localization.inverts L (weakEquivalences C) _ hw.mem
    exact ⟨L.map f' ≫ inv (L.map (f ≫ f')), by rw [← Category.assoc, ← L.map_comp,
      IsIso.hom_inv_id]⟩

/-- **Lemma 7.2.10(1)(b).** In a left proper precofibration category, a map
`f : A ⟶ B` is an isomorphism in the homotopy category iff there are left proper
maps `f' : B ⟶ B'` and `f'' : B' ⟶ B''` with `f'f` and `f''f'` weak equivalences. -/
theorem isIso_map_iff_leftProper {A B : C} (f : A ⟶ B) :
    IsIso (L.map f) ↔ ∃ (B' B'' : C) (f' : B ⟶ B') (f'' : B' ⟶ B''), IsLeftProper f' ∧
      IsLeftProper f'' ∧ WeakEquivalence (f ≫ f') ∧ WeakEquivalence (f' ≫ f'') := by
  constructor
  · intro _
    obtain ⟨B', f', hf', hw⟩ :=
      (exists_leftInverse_iff_leftProper L f).1 ⟨inv (L.map f), by simp⟩
    have := Localization.inverts L (weakEquivalences C) _ hw.mem
    have : IsIso (L.map f') := by
      rw [show L.map f' = inv (L.map f) ≫ L.map (f ≫ f') by simp]
      infer_instance
    obtain ⟨B'', f'', hf'', hw'⟩ :=
      (exists_leftInverse_iff_leftProper L f').1 ⟨inv (L.map f'), by simp⟩
    exact ⟨B', B'', f', f'', hf', hf'', hw, hw'⟩
  · rintro ⟨B', B'', f', f'', -, -, hw, hw'⟩
    have := Localization.inverts L (weakEquivalences C) _ hw.mem
    have := Localization.inverts L (weakEquivalences C) _ hw'.mem
    have : IsIso (L.map f ≫ L.map f') := by rw [← L.map_comp]; infer_instance
    have : IsIso (L.map f' ≫ L.map f'') := by rw [← L.map_comp]; infer_instance
    have := isIso_of_isIso_comp_of_isIso_comp (L.map f) (L.map f') (L.map f'')
    rw [show L.map f = (L.map f ≫ L.map f') ≫ inv (L.map f') by simp]
    infer_instance

/-- The core of Proposition 7.2.11(1): pushing a map in `W̄` along a left proper
map gives a map in `W̄`. -/
theorem isIso_map_of_isLeftProper {A B : C} {f : A ⟶ B} (hf : IsLeftProper f)
    {C₁ C₂ D₁ D₂ : C} {g : A ⟶ C₁} {r : C₁ ⟶ C₂} {j₁ : C₁ ⟶ D₁} {h : B ⟶ D₁} {j₂ : C₂ ⟶ D₂}
    {r' : D₁ ⟶ D₂} (sq₁ : IsPushout g f j₁ h) (sq₂ : IsPushout r j₁ j₂ r')
    (hr : IsIso (L.map r)) : IsIso (L.map r') := by
  obtain ⟨C₃, C₄, r₁, r₂, hr₁, hr₂, hw₁, hw₂⟩ := (isIso_map_iff_leftProper L r).1 hr
  -- `j₂` is a pushout of `f`, hence left proper, so `r₁` pushes out along it.
  have hj₂ : IsLeftProper j₂ := hf.of_isPushout (sq₁.paste_horiz sq₂)
  have := hj₂.hasPushout r₁
  let s₁ := IsPushout.of_hasPushout r₁ j₂
  have hj₃ : IsLeftProper (pushout.inl r₁ j₂) := hj₂.of_isPushout s₁
  have := hj₃.hasPushout r₂
  let s₂ := IsPushout.of_hasPushout r₂ (pushout.inl r₁ j₂)
  have h₁ : WeakEquivalence (r' ≫ pushout.inr r₁ j₂) :=
    hf.weakEquivalence sq₁ (sq₂.paste_horiz s₁)
  have h₂ : WeakEquivalence (pushout.inr r₁ j₂ ≫ pushout.inr r₂ (pushout.inl r₁ j₂)) :=
    hf.weakEquivalence (sq₁.paste_horiz sq₂) (s₁.paste_horiz s₂)
  have := Localization.inverts L (weakEquivalences C) _ h₁.mem
  have := Localization.inverts L (weakEquivalences C) _ h₂.mem
  have : IsIso (L.map r' ≫ L.map (pushout.inr r₁ j₂)) := by rw [← L.map_comp]; infer_instance
  have : IsIso (L.map (pushout.inr r₁ j₂) ≫ L.map (pushout.inr r₂ (pushout.inl r₁ j₂))) := by
    rw [← L.map_comp]; infer_instance
  have := isIso_of_isIso_comp_of_isIso_comp (L.map r') (L.map (pushout.inr r₁ j₂))
    (L.map (pushout.inr r₂ (pushout.inl r₁ j₂)))
  rw [show L.map r' = (L.map r' ≫ L.map (pushout.inr r₁ j₂)) ≫
    inv (L.map (pushout.inr r₁ j₂)) by simp]
  infer_instance

/-- **Proposition 7.2.11(1).** In a left proper precofibration category, a map
which is left proper for `W` is left proper for the saturation `W̄`. -/
theorem isLeftProper_saturated {A B : C} {f : A ⟶ B} (hf : IsLeftProper f) :
    IsLeftProper (C := Saturated C) f where
  hasPushout _ g := hf.hasPushout (C := C) g
  weakEquivalence {C₁ C₂ D₁ D₂ _ _ _ _ _ _} sq₁ sq₂ hr :=
    ⟨isIso_map_of_isLeftProper (weakEquivalences C).Q hf (C₁ := C₁) (C₂ := C₂) (D₁ := D₁)
      (D₂ := D₂) sq₁ sq₂ hr.mem⟩

/-- **Theorem 7.2.12(1).** If `(M, W, Cof)` is a left proper precofibration
category, so is `(M, W̄, Cof)`. -/
theorem saturated_leftProper :
    letI := saturated_precofibrationCategory (C := C)
    LeftProper (Saturated C) := by
  let := saturated_precofibrationCategory (C := C)
  exact
  { hasPushout := fun {A B D} i r hA hi ↦ by
      have : IsCofibrant (C := C) A := hA
      have : Cofibration (C := C) i := hi
      exact LeftProper.hasPushout (C := C) i r
    weakEquivalence_of_isPushout := fun {A B D E i r r' j} h hA hi hr ↦ by
      have : IsCofibrant (C := C) A := hA
      have : Cofibration (C := C) i := hi
      exact (isLeftProper_saturated (isLeftProper_of_cofibration (C := C) i)).weakEquivalence
        IsPushout.of_id_fst h.flip }

end ABCPrecofibrationCategory

namespace ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  [RightProper C] {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Lemma 7.2.10(2)(a).** In a right proper prefibration category, a map
`f : A ⟶ B` has a right inverse in the homotopy category iff there is a right
proper map `f' : A' ⟶ A` with `ff'` a weak equivalence. -/
theorem exists_rightInverse_iff_rightProper {A B : C} (f : A ⟶ B) :
    (∃ g : L.obj B ⟶ L.obj A, g ≫ L.map f = 𝟙 _) ↔
      ∃ (A' : C) (f' : A' ⟶ A), IsRightProper f' ∧ WeakEquivalence (f' ≫ f) := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  have e := ABCPrecofibrationCategory.exists_leftInverse_iff_leftProper L.op f.op
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨B', f'', hf'', hw⟩ := e.1 ⟨g.op, by
      change (L.map f).op ≫ g.op = 𝟙 _
      rw [← op_comp, hg, op_id]⟩
    exact ⟨B'.unop, f''.unop, hf'', (weakEquivalences_unop_iff (f.op ≫ f'')).2 hw⟩
  · rintro ⟨A', f', hf', hw⟩
    obtain ⟨g, hg⟩ := e.2 ⟨Opposite.op A', f'.op, hf', (weakEquivalences_op_iff (f' ≫ f)).2 hw⟩
    exact ⟨g.unop, by
      change g.unop ≫ (L.op.map f.op).unop = 𝟙 _
      rw [← unop_comp, hg, unop_id]⟩

/-- **Lemma 7.2.10(2)(b).** In a right proper prefibration category, a map
`f : A ⟶ B` is an isomorphism in the homotopy category iff there are right proper
maps `f' : A' ⟶ A` and `f'' : A'' ⟶ A'` with `ff'` and `f'f''` weak equivalences. -/
theorem isIso_map_iff_rightProper {A B : C} (f : A ⟶ B) :
    IsIso (L.map f) ↔ ∃ (A' A'' : C) (f' : A' ⟶ A) (f'' : A'' ⟶ A'), IsRightProper f' ∧
      IsRightProper f'' ∧ WeakEquivalence (f' ≫ f) ∧ WeakEquivalence (f'' ≫ f') := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  rw [← isIso_op_iff]
  change IsIso (L.op.map f.op) ↔ _
  rw [ABCPrecofibrationCategory.isIso_map_iff_leftProper L.op f.op]
  constructor
  · rintro ⟨B', B'', f', f'', hf', hf'', hw, hw'⟩
    exact ⟨B'.unop, B''.unop, f'.unop, f''.unop, hf', hf'',
      (weakEquivalences_unop_iff (f.op ≫ f')).2 hw, (weakEquivalences_unop_iff (f' ≫ f'')).2 hw'⟩
  · rintro ⟨A', A'', f', f'', hf', hf'', hw, hw'⟩
    exact ⟨Opposite.op A', Opposite.op A'', f'.op, f''.op, hf', hf'',
      (weakEquivalences_op_iff (f' ≫ f)).2 hw, (weakEquivalences_op_iff (f'' ≫ f')).2 hw'⟩

end ABCPrefibrationCategory

end ABCCofibrations

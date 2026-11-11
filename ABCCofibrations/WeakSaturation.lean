/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SaturatedStructure
public import ABCCofibrations.HomotopyCategory
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Tactic.TFAE

/-!
# Weak saturation (Definitions 7.2.5, 7.2.6, Theorem 7.2.7)

For a precofibration category, the following are equivalent: the weak
equivalences are weakly saturated (WS1–WS3), satisfy two out of six, are closed
under retracts, or are saturated.

The paper proves weak saturation ⟹ saturation through Lemma 7.2.1 in an over
category, which needs a left inverse there that the paper does not justify. We
argue directly in `M`. Let `a : A₀ ↣ A₁` be a cofibration with cofibrant source
which is an isomorphism in `ho M`. By Lemma 7.2.1 there is a cofibration
`f' : A₁ ↣ B` with `f' a` a weak equivalence. In the pushout `E` of `f' a` and
`a`, the map `j : B ⟶ E` has a retraction `h : E ⟶ B` (induced by `1_B` and
`f'`), and `j` is an isomorphism in `ho M` (Theorem 7.2.8(1)). Hence
`j h = 1` in `ho M`, so `j h` is left homotopic to `1_E` and is a weak
equivalence. WS3 makes `h` a weak equivalence, and then so are
`f' = (A₁ ⟶ E) ≫ h` and `a`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {C : Type u} [Category.{v} C]

/-- **Definition 7.2.5.** The two out of six property: if `g ≫ f`... in
diagrammatic order, if `f ≫ g` and `g ≫ h` are in `W`, so are `f`, `g`, `h` and
`f ≫ g ≫ h`. -/
def MorphismProperty.TwoOutOfSix (W : MorphismProperty C) : Prop :=
  ∀ ⦃A B D E : C⦄ (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E), W (f ≫ g) → W (g ≫ h) →
    W f ∧ W g ∧ W h ∧ W (f ≫ g ≫ h)

/-- **Definition 7.2.6.** Weak saturation: WS1 (identities), WS2 (two out of
three) and WS3 (if `i ≫ r = 1` and `r ≫ i ∈ W`, then `i, r ∈ W`). The paper's
`ri = 1_B` is a typo for `ri = 1_A`. -/
def MorphismProperty.WeaklySaturated (W : MorphismProperty C) : Prop :=
  W.ContainsIdentities ∧ W.HasTwoOutOfThreeProperty ∧
    ∀ ⦃A B : C⦄ (i : A ⟶ B) (r : B ⟶ A), i ≫ r = 𝟙 A → W (r ≫ i) → W i ∧ W r

omit [Category.{v} C] in
lemma MorphismProperty.twoOutOfSix_op_iff [Category.{v} C] (W : MorphismProperty C) :
    MorphismProperty.TwoOutOfSix W.op ↔ MorphismProperty.TwoOutOfSix W := by
  constructor
  · intro hW A B D E f g h hfg hgh
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hW h.op g.op f.op hgh hfg
    refine ⟨h₃, h₂, h₁, ?_⟩
    change W ((f ≫ g) ≫ h) at h₄
    rwa [Category.assoc] at h₄
  · intro hW A B D E f g h hfg hgh
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hW h.unop g.unop f.unop hgh hfg
    refine ⟨h₃, h₂, h₁, ?_⟩
    change W ((h.unop ≫ g.unop) ≫ f.unop)
    rwa [Category.assoc]

omit [Category.{v} C] in
lemma MorphismProperty.weaklySaturated_op_iff [Category.{v} C] (W : MorphismProperty C) :
    MorphismProperty.WeaklySaturated W.op ↔ MorphismProperty.WeaklySaturated W := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨inferInstanceAs W.op.unop.ContainsIdentities,
      inferInstanceAs W.op.unop.HasTwoOutOfThreeProperty, fun A B i r hir hri ↦ ?_⟩
    obtain ⟨hr, hi⟩ := h₃ r.op i.op (by rw [← op_comp, hir, op_id]) hri
    exact ⟨hi, hr⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨inferInstance, inferInstance, fun A B i r hir hri ↦ ?_⟩
    obtain ⟨hr, hi⟩ := h₃ r.unop i.unop (by rw [← unop_comp, hir, unop_id]) hri
    exact ⟨hi, hr⟩

namespace ABCPrecofibrationCategory

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
  [ABCPrecofibrationCategory C]

/-- Maps between cofibrant objects with equal images in `ho M` are weak
equivalences simultaneously (Theorem 6.3.1(1)). -/
lemma weakEquivalence_iff_of_map_eq {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    {u v : X ⟶ Y} (h : L.map u = L.map v) : WeakEquivalence u ↔ WeakEquivalence v := by
  have hh := (ambient_map_eq_iff_cofibrant_leftHomotopy L (X := ⟨X, ‹IsCofibrant X›⟩)
    (Y := ⟨Y, ‹IsCofibrant Y›⟩) (CofibrantObject.homMk u) (CofibrantObject.homMk v)).1 h
  let := hasBinaryCoproduct X X
  exact LeftHomotopyRel.weakEquivalence_iff hh

/-- The key step of weak saturation ⟹ saturation: under WS3, a cofibration with
cofibrant source which is an isomorphism in `ho M` is a weak equivalence. -/
lemma weakEquivalence_of_ws3 {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)]
    (ws3 : ∀ ⦃A B : C⦄ (i : A ⟶ B) (r : B ⟶ A), i ≫ r = 𝟙 A →
      WeakEquivalence (r ≫ i) → WeakEquivalence i ∧ WeakEquivalence r)
    {A₀ A₁ : C} [IsCofibrant A₀] (a : A₀ ⟶ A₁) [Cofibration a] (ha : IsIso (L.map a)) :
    WeakEquivalence a := by
  have : IsCofibrant A₁ := cofibrant_target a
  obtain ⟨B, f', hf', hw⟩ := (exists_leftInverse_iff L a).1 ⟨inv (L.map a), by simp⟩
  have : IsCofibrant B := cofibrant_target f'
  have : Cofibration (a ≫ f') := inferInstance
  let sq := IsPushout.of_hasPushout (a ≫ f') a
  have : Cofibration (pushout.inr (a ≫ f') a) := cofibration_of_isPushout sq
  have : WeakEquivalence (pushout.inr (a ≫ f') a) := weakEquivalence_of_isPushout sq
  have : Cofibration (pushout.inl (a ≫ f') a) := cofibration_of_isPushout sq.flip
  have : IsCofibrant (pushout (a ≫ f') a) := cofibrant_target (pushout.inl (a ≫ f') a)
  have hj : IsIso (L.map (pushout.inl (a ≫ f') a)) :=
    saturation_cobaseChange L sq.flip inferInstance inferInstance inferInstance ha
  let h : pushout (a ≫ f') a ⟶ B := pushout.desc (𝟙 B) f' (by simp)
  have h₁ : pushout.inl (a ≫ f') a ≫ h = 𝟙 B := pushout.inl_desc _ _ _
  have h₂ : pushout.inr (a ≫ f') a ≫ h = f' := pushout.inr_desc _ _ _
  have hL : L.map (h ≫ pushout.inl (a ≫ f') a) = L.map (𝟙 _) := by
    have h₃ : L.map (pushout.inl (a ≫ f') a) ≫ L.map h = 𝟙 _ := by
      rw [← L.map_comp, h₁, L.map_id]
    rw [L.map_comp, L.map_id, IsIso.eq_inv_of_hom_inv_id h₃, IsIso.inv_hom_id]
  have hw' : WeakEquivalence (h ≫ pushout.inl (a ≫ f') a) :=
    (weakEquivalence_iff_of_map_eq L hL).2 (weakEquivalence_of_isIso _)
  have : WeakEquivalence h := (ws3 _ h h₁ hw').2
  have : WeakEquivalence f' := by
    rw [← h₂]
    infer_instance
  exact weakEquivalence_of_postcomp a f'

variable (C) in
/-- **Theorem 7.2.7**, precofibration case. For a precofibration category, the
weak equivalences are weakly saturated, iff they satisfy two out of six, iff
they are closed under retracts, iff they are saturated. -/
theorem weakSaturation_tfae :
    List.TFAE [MorphismProperty.WeaklySaturated (weakEquivalences C),
      MorphismProperty.TwoOutOfSix (weakEquivalences C),
      (weakEquivalences C).IsStableUnderRetracts, weakEquivalences C = saturation C] := by
  have hid : (weakEquivalences C).ContainsIdentities :=
    ⟨fun X ↦ (weakEquivalence_of_isIso (𝟙 X)).mem⟩
  have h23 : (weakEquivalences C).HasTwoOutOfThreeProperty := inferInstance
  tfae_have 2 → 1 := fun h ↦ ⟨hid, h23, fun A B i r hir hri ↦ by
    have := h i r i (by rw [hir]; exact hid.id_mem A) hri
    exact ⟨this.1, this.2.1⟩⟩
  tfae_have 3 → 1 := fun h ↦ ⟨hid, h23, fun A B i r hir hri ↦ by
    let e : RetractArrow r (r ≫ i) :=
      { i := Arrow.homMk (𝟙 B) i (by simp)
        r := Arrow.homMk (𝟙 B) r (by simp [hir])
        retract := by ext <;> simp [hir] }
    have hr : WeakEquivalence r := ⟨h.of_retract e hri⟩
    have : WeakEquivalence (i ≫ r) := by rw [hir]; exact weakEquivalence_of_isIso _
    exact ⟨(weakEquivalence_of_postcomp i r).mem, hr.mem⟩⟩
  tfae_have 4 → 2 := fun h A B D E f g k hfg hgk ↦ by
    rw [h] at hfg hgk ⊢
    let L := (weakEquivalences C).Q
    change IsIso (L.map (f ≫ g)) at hfg
    change IsIso (L.map (g ≫ k)) at hgk
    rw [L.map_comp] at hfg hgk
    have : IsIso (L.map g) := isIso_of_isIso_comp_of_isIso_comp (L.map f) (L.map g) (L.map k)
    have : IsIso (L.map f) := IsIso.of_isIso_comp_right (L.map f) (L.map g)
    have : IsIso (L.map k) := IsIso.of_isIso_comp_left (L.map g) (L.map k)
    refine ⟨‹IsIso (L.map f)›, ‹IsIso (L.map g)›, ‹IsIso (L.map k)›, ?_⟩
    change IsIso (L.map (f ≫ g ≫ k))
    rw [L.map_comp, L.map_comp]
    infer_instance
  tfae_have 4 → 3 := fun h ↦ by
    rw [h]
    exact inferInstanceAs ((MorphismProperty.isomorphisms _).inverseImage _).IsStableUnderRetracts
  tfae_have 1 → 4 := fun ⟨_, _, ws3⟩ ↦ by
    let L := (weakEquivalences C).Q
    apply le_antisymm
    · intro X Y f hf
      exact Localization.inverts L (weakEquivalences C) f hf
    · intro X Y f (hf : IsIso (L.map f))
      obtain ⟨A₀, q, hA₀, hq⟩ := exists_cofibrant_replacement X
      obtain ⟨A₁, a, r, ha, hr, hfac⟩ := factorization (q ≫ f)
      have := Localization.inverts L (weakEquivalences C) q hq.mem
      have := Localization.inverts L (weakEquivalences C) r hr.mem
      have : IsIso (L.map a) := by
        rw [show L.map a = L.map (q ≫ f) ≫ inv (L.map r) by
          rw [← hfac, L.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
        simp only [L.map_comp]
        infer_instance
      have := weakEquivalence_of_ws3 L (fun A B i r h₁ h₂ ↦ by
        have := ws3 i r h₁ h₂.mem
        exact ⟨⟨this.1⟩, ⟨this.2⟩⟩) a this
      have : WeakEquivalence (q ≫ f) := by rw [← hfac]; infer_instance
      exact (weakEquivalence_of_precomp q f).mem
  tfae_finish

end ABCPrecofibrationCategory

namespace ABCPrefibrationCategory

variable [CategoryWithFibrations C] [CategoryWithWeakEquivalences C] [HasTerminal C]
  [ABCPrefibrationCategory C]

variable (C) in
/-- **Theorem 7.2.7**, prefibration case, from the precofibration case in `Cᵒᵖ`. -/
theorem weakSaturation_tfae :
    List.TFAE [MorphismProperty.WeaklySaturated (weakEquivalences C),
      MorphismProperty.TwoOutOfSix (weakEquivalences C),
      (weakEquivalences C).IsStableUnderRetracts,
      weakEquivalences C = ABCPrecofibrationCategory.saturation C] := by
  have h := ABCPrecofibrationCategory.weakSaturation_tfae Cᵒᵖ
  have e₁ := MorphismProperty.weaklySaturated_op_iff (weakEquivalences C)
  have e₂ := MorphismProperty.twoOutOfSix_op_iff (weakEquivalences C)
  have e₃ : (weakEquivalences Cᵒᵖ).IsStableUnderRetracts ↔
      (weakEquivalences C).IsStableUnderRetracts :=
    ⟨fun h ↦ by
      have : (weakEquivalences C).op.IsStableUnderRetracts := h
      exact inferInstanceAs (weakEquivalences C).op.unop.IsStableUnderRetracts,
      fun _ ↦ inferInstanceAs (weakEquivalences C).op.IsStableUnderRetracts⟩
  have e₄ : weakEquivalences Cᵒᵖ = ABCPrecofibrationCategory.saturation Cᵒᵖ ↔
      weakEquivalences C = ABCPrecofibrationCategory.saturation C := by
    rw [saturation_op]
    exact ⟨fun h ↦ congrArg MorphismProperty.unop h, fun h ↦ by
      change (weakEquivalences C).op = _
      rw [h]⟩
  change List.TFAE [MorphismProperty.WeaklySaturated (weakEquivalences C).op,
    MorphismProperty.TwoOutOfSix (weakEquivalences C).op, _, _] at h
  rwa [e₁, e₂, e₃, e₄] at h

end ABCPrefibrationCategory

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Extension
public import ABCCofibrations.FibrationBasic
public import Mathlib.Tactic.TFAE

/-!
# Equivalent forms of axiom CF3(2) (Lemma 1.4.3)

Assume CF1, CF2, CF3(1) and CF4, but not CF3(2). Then CF3(2) (cobase change
preserves trivial cofibrations), the gluing lemma for weak equivalences
(Lemma 1.4.1(1)(b)), and excision (Lemma 1.4.2(1)) are equivalent.

The axioms other than CF3(2) are packaged in `PrecofibrationAxiomsWithoutCF32`,
and the three properties are stated as standalone propositions. The fibration
statement (2) is obtained in the opposite category, with native formulations
of the three properties in terms of pullbacks.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

section Cofibration

variable (C : Type u) [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- Axioms CF1, CF2, CF3(1) and CF4: the fields of `ABCPrecofibrationCategory`
except CF3(2). -/
structure PrecofibrationAxiomsWithoutCF32 : Prop where
  initial_cofibrant : IsCofibrant (⊥_ C)
  cofibrations_comp : (cofibrations C).IsStableUnderComposition
  weakEquivalence_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : WeakEquivalence f
  cofibration_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] [IsCofibrant A] : Cofibration f
  weakEquivalences_twoOutOfThree : (weakEquivalences C).HasTwoOutOfThreeProperty
  hasPushout {A B D : C} (i : A ⟶ B) (f : A ⟶ D) [IsCofibrant A] [IsCofibrant D]
    [Cofibration i] : HasPushout i f
  cofibration_of_isPushout {A B D E : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E}
    (h : IsPushout i f g j) [IsCofibrant A] [IsCofibrant D] [Cofibration i] : Cofibration j
  factorization {A B : C} (f : A ⟶ B) [IsCofibrant A] :
    ∃ (Z : C) (i : A ⟶ Z) (p : Z ⟶ B), Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f

/-- Axiom CF3(2): cobase change along maps between cofibrant objects preserves
trivial cofibrations. -/
def TrivialCobaseChangeAxiom : Prop :=
  ∀ ⦃A B D E : C⦄ {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E},
    IsPushout i f g j → IsCofibrant A → IsCofibrant D → Cofibration i → WeakEquivalence i →
      WeakEquivalence j

/-- The conclusion of the gluing lemma for weak equivalences, Lemma 1.4.1(1)(b). -/
def GluingWeakEquivalenceProperty : Prop :=
  ∀ ⦃A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C⦄
    {f₁₂ : A₁ ⟶ A₂} {f₁₃ : A₁ ⟶ A₃} {f₂₄ : A₂ ⟶ A₄} {f₃₄ : A₃ ⟶ A₄}
    {g₁₂ : B₁ ⟶ B₂} {g₁₃ : B₁ ⟶ B₃} {g₂₄ : B₂ ⟶ B₄} {g₃₄ : B₃ ⟶ B₄}
    {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄},
    IsCofibrant A₁ → IsCofibrant A₃ → IsCofibrant B₁ → IsCofibrant B₃ →
    Cofibration f₁₂ → Cofibration g₁₂ →
    IsPushout f₁₂ f₁₃ f₂₄ f₃₄ → IsPushout g₁₂ g₁₃ g₂₄ g₃₄ →
    f₁₂ ≫ u₂ = u₁ ≫ g₁₂ → f₁₃ ≫ u₃ = u₁ ≫ g₁₃ →
    f₂₄ ≫ u₄ = u₂ ≫ g₂₄ → f₃₄ ≫ u₄ = u₃ ≫ g₃₄ →
    WeakEquivalence u₁ → WeakEquivalence u₂ → WeakEquivalence u₃ → WeakEquivalence u₄

/-- The conclusion of excision, Lemma 1.4.2(1). -/
def ExcisionProperty : Prop :=
  ∀ ⦃A B D E : C⦄ {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ E} {j : D ⟶ E},
    IsPushout i f g j → IsCofibrant A → IsCofibrant D → Cofibration i → WeakEquivalence f →
      WeakEquivalence g

variable {C}

/-- The remaining axioms together with CF3(2) form a precofibration category. -/
theorem PrecofibrationAxiomsWithoutCF32.toPrecofibrationCategory
    (h : PrecofibrationAxiomsWithoutCF32 C) (h₂ : TrivialCobaseChangeAxiom C) :
    ABCPrecofibrationCategory C where
  initial_cofibrant := h.initial_cofibrant
  cofibrations_comp := h.cofibrations_comp
  weakEquivalence_of_isIso := h.weakEquivalence_of_isIso
  cofibration_of_isIso := h.cofibration_of_isIso
  weakEquivalences_twoOutOfThree := h.weakEquivalences_twoOutOfThree
  hasPushout := h.hasPushout
  cofibration_of_isPushout := h.cofibration_of_isPushout
  weakEquivalence_of_isPushout hsq hA hD hi hw := h₂ hsq hA hD hi hw
  factorization := h.factorization

/-- **Lemma 1.4.3(1).** Under CF1, CF2, CF3(1) and CF4, the following are
equivalent: (a) CF3(2); (b) the gluing lemma for weak equivalences; (c)
excision. -/
theorem cf32_tfae (h : PrecofibrationAxiomsWithoutCF32 C) :
    List.TFAE [TrivialCobaseChangeAxiom C, GluingWeakEquivalenceProperty C,
      ExcisionProperty C] := by
  have : (cofibrations C).IsStableUnderComposition := h.cofibrations_comp
  have : (weakEquivalences C).HasTwoOutOfThreeProperty := h.weakEquivalences_twoOutOfThree
  tfae_have 1 → 2 := by
    intro h₂
    have := h.toPrecofibrationCategory h₂
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA₁ hA₃ hB₁ hB₃ hf hg hA hB
      h₁₂ h₁₃ h₂₄ h₃₄ hu₁ hu₂ hu₃
    exact ABCPrecofibrationCategory.gluing_weakEquivalence hA hB h₁₂ h₁₃ h₂₄ h₃₄
  tfae_have 2 → 3 := by
    intro hg A B D E i f g j hsq hA hD hi hf
    have := h.weakEquivalence_of_isIso (𝟙 A)
    have := h.weakEquivalence_of_isIso (𝟙 B)
    have hB : IsCofibrant B := isCofibrant_of_cofibration i
    exact hg (u₁ := 𝟙 A) (u₂ := 𝟙 B) (u₃ := f) (u₄ := g) hA hA hA hD hi hi
      (IsPushout.of_id_snd (f := i)) hsq (by simp) (by simp) (by simp) hsq.w
      inferInstance inferInstance hf
  tfae_have 3 → 1 := by
    intro hexc A B D E i f g j hsq hA hD hi hw
    obtain ⟨C', f', r, hf', hr, hfac⟩ := h.factorization f
    have hC' : IsCofibrant C' := isCofibrant_of_cofibration f'
    have hB : IsCofibrant B := isCofibrant_of_cofibration i
    have := h.hasPushout i f'
    let t := IsPushout.of_hasPushout i f'
    have hinr : Cofibration (pushout.inr i f') := h.cofibration_of_isPushout t
    -- The pushout of `i` along `f'` is a weak equivalence, by excision.
    have hw₁ : WeakEquivalence (pushout.inr i f') := hexc t.flip hA hB hf' hw
    -- The remaining square is a pushout along `pushout.inr i f'`.
    have s : IsPushout i (f' ≫ r) g j := by rw [hfac]; exact hsq
    have sq := IsPushout.of_top' s t
    have hw₂ := hexc sq hC' hD hinr hr
    have : WeakEquivalence (r ≫ j) := by
      rw [← sq.w]
      infer_instance
    exact weakEquivalence_of_precomp r j
  tfae_finish

end Cofibration

section Fibration

variable (C : Type u) [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C]

/-- Axioms F1, F2, F3(1) and F4, expressed as CF1, CF2, CF3(1), CF4 on the
opposite category. -/
abbrev PrefibrationAxiomsWithoutF32 : Prop := PrecofibrationAxiomsWithoutCF32 Cᵒᵖ

/-- Axiom F3(2): base change along maps between fibrant objects preserves
trivial fibrations. -/
def TrivialBaseChangeAxiom : Prop :=
  ∀ ⦃A B D E : C⦄ {p : B ⟶ A} {f : D ⟶ A} {g : E ⟶ B} {j : E ⟶ D},
    IsPullback g j p f → IsFibrant A → IsFibrant D → Fibration p → WeakEquivalence p →
      WeakEquivalence j

/-- The conclusion of the cogluing lemma for weak equivalences, Lemma 1.4.1(2)(b). -/
def CogluingWeakEquivalenceProperty : Prop :=
  ∀ ⦃A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C⦄
    {f₁₂ : A₂ ⟶ A₁} {f₁₃ : A₃ ⟶ A₁} {f₂₄ : A₄ ⟶ A₂} {f₃₄ : A₄ ⟶ A₃}
    {g₁₂ : B₂ ⟶ B₁} {g₁₃ : B₃ ⟶ B₁} {g₂₄ : B₄ ⟶ B₂} {g₃₄ : B₄ ⟶ B₃}
    {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄},
    IsFibrant A₁ → IsFibrant A₃ → IsFibrant B₁ → IsFibrant B₃ →
    Fibration f₁₂ → Fibration g₁₂ →
    IsPullback f₂₄ f₃₄ f₁₂ f₁₃ → IsPullback g₂₄ g₃₄ g₁₂ g₁₃ →
    f₁₂ ≫ u₁ = u₂ ≫ g₁₂ → f₁₃ ≫ u₁ = u₃ ≫ g₁₃ →
    f₂₄ ≫ u₂ = u₄ ≫ g₂₄ → f₃₄ ≫ u₃ = u₄ ≫ g₃₄ →
    WeakEquivalence u₁ → WeakEquivalence u₂ → WeakEquivalence u₃ → WeakEquivalence u₄

/-- The conclusion of excision for fibrations, Lemma 1.4.2(2). -/
def CoexcisionProperty : Prop :=
  ∀ ⦃P X B D : C⦄ {fst : P ⟶ X} {snd : P ⟶ D} {p : X ⟶ B} {r : D ⟶ B},
    IsPullback fst snd p r → IsFibrant B → IsFibrant D → Fibration p → WeakEquivalence r →
      WeakEquivalence fst

variable {C}

/-- Fibrancy is cofibrancy in the opposite category, using only the axioms
other than F3(2). -/
theorem PrecofibrationAxiomsWithoutCF32.isFibrant_iff_isCofibrant_op
    (h : PrefibrationAxiomsWithoutF32 C) (A : C) :
    IsFibrant A ↔ IsCofibrant (Opposite.op A) := by
  have := h.cofibrations_comp
  have := h.initial_cofibrant
  change Fibration (terminal.from A) ↔ Cofibration (initial.to (Opposite.op A))
  let hI := initialOpOfTerminal (terminalIsTerminal (C := C))
  let e : (⊥_ Cᵒᵖ) ≅ Opposite.op (⊤_ C) := initialIsInitial.uniqueUpToIso hI
  have := h.cofibration_of_isIso e.hom
  have : IsCofibrant (Opposite.op (⊤_ C)) := isCofibrant_of_cofibration e.hom
  have := h.cofibration_of_isIso e.inv
  have he : e.hom ≫ (terminal.from A).op = initial.to (Opposite.op A) :=
    initialIsInitial.hom_ext _ _
  have he' : e.inv ≫ initial.to (Opposite.op A) = (terminal.from A).op := hI.hom_ext _ _
  constructor
  · intro hf
    have : Cofibration (terminal.from A).op := (cofibration_op_iff _).2 hf
    rw [← he]
    infer_instance
  · intro hf
    apply (cofibration_op_iff (terminal.from A)).1
    rw [← he']
    infer_instance

theorem trivialBaseChangeAxiom_iff (h : PrefibrationAxiomsWithoutF32 C) :
    TrivialBaseChangeAxiom C ↔ TrivialCobaseChangeAxiom Cᵒᵖ := by
  constructor
  · intro hP A B D E i f g j hsq hA hD hi hw
    exact (weakEquivalences_unop_iff j).1
      (hP hsq.unop.flip ((h.isFibrant_iff_isCofibrant_op _).2 hA)
        ((h.isFibrant_iff_isCofibrant_op _).2 hD) ((fibration_unop_iff i).2 hi)
        ((weakEquivalences_unop_iff i).2 hw))
  · intro hP A B D E p f g j hsq hA hD hp hw
    exact (weakEquivalences_op_iff j).1
      (hP hsq.op.flip ((h.isFibrant_iff_isCofibrant_op _).1 hA)
        ((h.isFibrant_iff_isCofibrant_op _).1 hD) ((cofibration_op_iff p).2 hp)
        ((weakEquivalences_op_iff p).2 hw))

theorem coexcisionProperty_iff (h : PrefibrationAxiomsWithoutF32 C) :
    CoexcisionProperty C ↔ ExcisionProperty Cᵒᵖ := by
  constructor
  · intro hP A B D E i f g j hsq hA hD hi hw
    exact (weakEquivalences_unop_iff g).1
      (hP hsq.unop.flip ((h.isFibrant_iff_isCofibrant_op _).2 hA)
        ((h.isFibrant_iff_isCofibrant_op _).2 hD) ((fibration_unop_iff i).2 hi)
        ((weakEquivalences_unop_iff f).2 hw))
  · intro hP P X B D fst snd p r hsq hB hD hp hw
    exact (weakEquivalences_op_iff fst).1
      (hP hsq.op.flip ((h.isFibrant_iff_isCofibrant_op _).1 hB)
        ((h.isFibrant_iff_isCofibrant_op _).1 hD) ((cofibration_op_iff p).2 hp)
        ((weakEquivalences_op_iff r).2 hw))

theorem cogluingWeakEquivalenceProperty_iff (h : PrefibrationAxiomsWithoutF32 C) :
    CogluingWeakEquivalenceProperty C ↔ GluingWeakEquivalenceProperty Cᵒᵖ := by
  constructor
  · intro hP A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ f₁₂ f₁₃ f₂₄ f₃₄ g₁₂ g₁₃ g₂₄ g₃₄ u₁ u₂ u₃ u₄
      hA₁ hA₃ hB₁ hB₃ hf hg hA hB h₁₂ h₁₃ h₂₄ h₃₄ hu₁ hu₂ hu₃
    exact (weakEquivalences_unop_iff u₄).1
      (hP (u₁ := u₁.unop) (u₂ := u₂.unop) (u₃ := u₃.unop) (u₄ := u₄.unop)
        ((h.isFibrant_iff_isCofibrant_op _).2 hB₁) ((h.isFibrant_iff_isCofibrant_op _).2 hB₃)
        ((h.isFibrant_iff_isCofibrant_op _).2 hA₁) ((h.isFibrant_iff_isCofibrant_op _).2 hA₃)
        ((fibration_unop_iff _).2 hg) ((fibration_unop_iff _).2 hf)
        hB.unop.flip hA.unop.flip
        (by rw [← unop_comp, ← unop_comp, h₁₂]) (by rw [← unop_comp, ← unop_comp, h₁₃])
        (by rw [← unop_comp, ← unop_comp, h₂₄]) (by rw [← unop_comp, ← unop_comp, h₃₄])
        ((weakEquivalences_unop_iff _).2 hu₁) ((weakEquivalences_unop_iff _).2 hu₂)
        ((weakEquivalences_unop_iff _).2 hu₃))
  · intro hP A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ f₁₂ f₁₃ f₂₄ f₃₄ g₁₂ g₁₃ g₂₄ g₃₄ u₁ u₂ u₃ u₄
      hA₁ hA₃ hB₁ hB₃ hf hg hA hB h₁₂ h₁₃ h₂₄ h₃₄ hu₁ hu₂ hu₃
    exact (weakEquivalences_op_iff u₄).1
      (hP (u₁ := u₁.op) (u₂ := u₂.op) (u₃ := u₃.op) (u₄ := u₄.op)
        ((h.isFibrant_iff_isCofibrant_op _).1 hB₁) ((h.isFibrant_iff_isCofibrant_op _).1 hB₃)
        ((h.isFibrant_iff_isCofibrant_op _).1 hA₁) ((h.isFibrant_iff_isCofibrant_op _).1 hA₃)
        ((cofibration_op_iff _).2 hg) ((cofibration_op_iff _).2 hf)
        hB.op.flip hA.op.flip
        (by rw [← op_comp, ← op_comp, h₁₂]) (by rw [← op_comp, ← op_comp, h₁₃])
        (by rw [← op_comp, ← op_comp, h₂₄]) (by rw [← op_comp, ← op_comp, h₃₄])
        ((weakEquivalences_op_iff _).2 hu₁) ((weakEquivalences_op_iff _).2 hu₂)
        ((weakEquivalences_op_iff _).2 hu₃))

/-- **Lemma 1.4.3(2).** Under F1, F2, F3(1) and F4, the following are
equivalent: (a) F3(2); (b) the cogluing lemma for weak equivalences; (c)
excision for fibrations. -/
theorem f32_tfae (h : PrefibrationAxiomsWithoutF32 C) :
    List.TFAE [TrivialBaseChangeAxiom C, CogluingWeakEquivalenceProperty C,
      CoexcisionProperty C] := by
  have e := cf32_tfae h
  rwa [← trivialBaseChangeAxiom_iff h, ← cogluingWeakEquivalenceProperty_iff h,
    ← coexcisionProperty_iff h] at e

end Fibration

end ABCCofibrations

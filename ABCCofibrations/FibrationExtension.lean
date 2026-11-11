/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Extension
public import ABCCofibrations.FibrationBasic

/-!
# Cogluing and excision in prefibration categories

The fibration statements of the gluing lemma (Lemma 1.4.1(2)), of excision
(Lemma 1.4.2(2)) and of relative factorization (Lemma 1.3.3(2)), deduced from
the cofibration statements in the opposite category. A pullback square in `C`
is a pushout square in `Cᵒᵖ` (`IsPullback.op`), fibrations with fibrant target are cofibrations with
cofibrant source there, and weak equivalences are self-dual.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations.ABCPrefibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- **Lemma 1.4.2(2)** (excision). The base change of a weak equivalence `r`
between fibrant objects along a fibration `p` with fibrant target is a weak
equivalence, for any representative of the pullback. -/
theorem weakEquivalence_of_isPullback_of_fibration {P X B D : C} {fst : P ⟶ X}
    {snd : P ⟶ D} {p : X ⟶ B} {r : D ⟶ B} [IsFibrant B] [IsFibrant D] [Fibration p]
    [WeakEquivalence r] (h : IsPullback fst snd p r) : WeakEquivalence fst := by
  have : Cofibration p.op := (cofibration_op_iff _).2 ‹_›
  have : WeakEquivalence r.op := (weakEquivalences_op_iff _).2 ‹_›
  exact (weakEquivalences_op_iff _).1 (weakEquivalence_of_isPushout_of_cofibration h.op.flip)

/-- **Lemma 1.4.1(2)(b)** (cogluing lemma for weak equivalences). Given a map
`u` from a pullback square of `A`'s to a pullback square of `B`'s, in which the
maps `f₁₂`, `g₁₂` are fibrations and `A₁, A₃, B₁, B₃` are fibrant, if `u₁`,
`u₂`, `u₃` are weak equivalences then so is the induced map `u₄` of
pullbacks. -/
theorem cogluing_weakEquivalence {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C}
    [IsFibrant A₁] [IsFibrant A₃] [IsFibrant B₁] [IsFibrant B₃]
    {f₁₂ : A₂ ⟶ A₁} {f₁₃ : A₃ ⟶ A₁} {f₂₄ : A₄ ⟶ A₂} {f₃₄ : A₄ ⟶ A₃}
    {g₁₂ : B₂ ⟶ B₁} {g₁₃ : B₃ ⟶ B₁} {g₂₄ : B₄ ⟶ B₂} {g₃₄ : B₄ ⟶ B₃}
    {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄}
    [Fibration f₁₂] [Fibration g₁₂]
    (hA : IsPullback f₂₄ f₃₄ f₁₂ f₁₃) (hB : IsPullback g₂₄ g₃₄ g₁₂ g₁₃)
    (h₁₂ : f₁₂ ≫ u₁ = u₂ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₁ = u₃ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₂ = u₄ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₃ = u₄ ≫ g₃₄)
    [WeakEquivalence u₁] [WeakEquivalence u₂] [WeakEquivalence u₃] :
    WeakEquivalence u₄ := by
  have : Cofibration f₁₂.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration g₁₂.op := (cofibration_op_iff _).2 ‹_›
  have : WeakEquivalence u₁.op := (weakEquivalences_op_iff _).2 ‹_›
  have : WeakEquivalence u₂.op := (weakEquivalences_op_iff _).2 ‹_›
  have : WeakEquivalence u₃.op := (weakEquivalences_op_iff _).2 ‹_›
  exact (weakEquivalences_op_iff _).1
    (gluing_weakEquivalence (u₁ := u₁.op) (u₂ := u₂.op) (u₃ := u₃.op) (u₄ := u₄.op)
      hB.op.flip hA.op.flip
      (by rw [← op_comp, ← op_comp, h₁₂]) (by rw [← op_comp, ← op_comp, h₁₃])
      (by rw [← op_comp, ← op_comp, h₂₄]) (by rw [← op_comp, ← op_comp, h₃₄]))

/-- **Lemma 1.3.3(2)** (relative factorization in a prefibration category).
Extend a specified factorization `p₁ ≫ i₁ = f₁` (a weak equivalence followed by
a fibration) across a square with fibrant right-hand objects. For any pullback
`P` of `i₁` and `a`, the comparison map `k : Z₂ ⟶ P` is a fibration. -/
theorem exists_relative_factorization
    {A₁ A₂ B₁ B₂ Z₁ : C} [IsFibrant A₁] [IsFibrant A₂]
    (f₁ : B₁ ⟶ A₁) (f₂ : B₂ ⟶ A₂) (a : A₂ ⟶ A₁) (b : B₂ ⟶ B₁)
    (h : b ≫ f₁ = f₂ ≫ a)
    (p₁ : B₁ ⟶ Z₁) (i₁ : Z₁ ⟶ A₁) [Fibration i₁] [WeakEquivalence p₁]
    (h₁ : p₁ ≫ i₁ = f₁) {P : C} {fst : P ⟶ Z₁} {snd : P ⟶ A₂}
    (hP : IsPullback fst snd i₁ a) :
    ∃ (Z₂ : C) (p₂ : B₂ ⟶ Z₂) (i₂ : Z₂ ⟶ A₂) (a' : Z₂ ⟶ Z₁) (k : Z₂ ⟶ P),
      IsFibrant Z₂ ∧ Fibration i₂ ∧ WeakEquivalence p₂ ∧ Fibration k ∧
      p₂ ≫ i₂ = f₂ ∧ a' ≫ i₁ = i₂ ≫ a ∧ p₂ ≫ a' = b ≫ p₁ ∧
      k ≫ fst = a' ∧ k ≫ snd = i₂ := by
  have : Cofibration i₁.op := (cofibration_op_iff _).2 ‹_›
  have : WeakEquivalence p₁.op := (weakEquivalences_op_iff _).2 ‹_›
  obtain ⟨Z₂, i₂, p₂, a', k, hZ, hi, hp, hk, e₁, e₂, e₃, e₄, e₅⟩ :=
    ABCPrecofibrationCategory.exists_relative_factorization f₁.op f₂.op a.op b.op
      (by rw [← op_comp, ← op_comp, h]) i₁.op p₁.op (by rw [← op_comp, h₁])
  have hPo : IsPushout i₁.op a.op fst.op snd.op := hP.op.flip
  have : Fibration snd := fibration_of_isPullback hP
  have : IsFibrant P := fibrant_source snd
  have : Cofibration hPo.isoPushout.hom :=
    ABCPrecofibrationCategory.cofibration_of_isIso _
  have hk' : Cofibration (hPo.isoPushout.hom ≫ k) :=
    ⟨(cofibrations Cᵒᵖ).comp_mem _ _ this.mem hk.mem⟩
  refine ⟨Z₂.unop, p₂.unop, i₂.unop, a'.unop, (hPo.isoPushout.hom ≫ k).unop,
    (isFibrant_iff_isCofibrant_op _).2 hZ, (cofibration_op_iff _).1 hi,
    (weakEquivalences_op_iff _).1 hp, (cofibration_op_iff _).1 hk', ?_, ?_, ?_, ?_, ?_⟩
  · exact Quiver.Hom.op_inj e₁
  · exact Quiver.Hom.op_inj e₂
  · exact Quiver.Hom.op_inj e₃
  · apply Quiver.Hom.op_inj
    change fst.op ≫ hPo.isoPushout.hom ≫ k = a'
    rw [hPo.inl_isoPushout_hom_assoc, e₄]
  · apply Quiver.Hom.op_inj
    change snd.op ≫ hPo.isoPushout.hom ≫ k = i₂
    rw [hPo.inr_isoPushout_hom_assoc, e₅]

/-- **Lemma 1.4.1(2)(a)** (cogluing lemma for fibrations). Given a map `u` from a
pullback square of `A`'s to a pullback square of `B`'s, with `g₁₂` a fibration
and `A₁, A₃, B₁, B₃` fibrant, suppose `u₁, u₃` are fibrations and the comparison
`c : A₂ ⟶ P` to a pullback `P = B₂ ×_{B₁} A₁` is a fibration. Then `u₂`, `u₄` and
the comparison `d : A₄ ⟶ Q` to any pullback `Q = B₄ ×_{B₃} A₃` are fibrations. -/
theorem cogluing_fibration {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : C}
    [IsFibrant A₁] [IsFibrant A₃] [IsFibrant B₁] [IsFibrant B₃]
    {f₁₂ : A₂ ⟶ A₁} {f₁₃ : A₃ ⟶ A₁} {f₂₄ : A₄ ⟶ A₂} {f₃₄ : A₄ ⟶ A₃}
    {g₁₂ : B₂ ⟶ B₁} {g₁₃ : B₃ ⟶ B₁} {g₂₄ : B₄ ⟶ B₂} {g₃₄ : B₄ ⟶ B₃}
    {u₁ : A₁ ⟶ B₁} {u₂ : A₂ ⟶ B₂} {u₃ : A₃ ⟶ B₃} {u₄ : A₄ ⟶ B₄}
    [Fibration g₁₂] [Fibration u₁] [Fibration u₃]
    (hA : IsPullback f₂₄ f₃₄ f₁₂ f₁₃) (hB : IsPullback g₂₄ g₃₄ g₁₂ g₁₃)
    (h₁₂ : f₁₂ ≫ u₁ = u₂ ≫ g₁₂) (h₁₃ : f₁₃ ≫ u₁ = u₃ ≫ g₁₃)
    (h₂₄ : f₂₄ ≫ u₂ = u₄ ≫ g₂₄) (h₃₄ : f₃₄ ≫ u₃ = u₄ ≫ g₃₄)
    {P : C} {πB : P ⟶ B₂} {πA : P ⟶ A₁} (hP : IsPullback πB πA g₁₂ u₁)
    (c : A₂ ⟶ P) (hcB : c ≫ πB = u₂) (hcA : c ≫ πA = f₁₂) [Fibration c]
    {Q : C} {ρB : Q ⟶ B₄} {ρA : Q ⟶ A₃} (hQ : IsPullback ρB ρA g₃₄ u₃)
    (d : A₄ ⟶ Q) (hdB : d ≫ ρB = u₄) (hdA : d ≫ ρA = f₃₄) :
    Fibration u₂ ∧ Fibration u₄ ∧ Fibration d := by
  have : Cofibration g₁₂.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration u₁.op := (cofibration_op_iff _).2 ‹_›
  have : Cofibration u₃.op := (cofibration_op_iff _).2 ‹_›
  have : Fibration g₃₄ := fibration_of_isPullback hB
  have : IsFibrant B₄ := fibrant_source g₃₄
  have : Cofibration g₃₄.op := (cofibration_op_iff _).2 ‹_›
  have : Fibration ρA := fibration_of_isPullback hQ
  have : IsFibrant Q := fibrant_source ρA
  have : Fibration πA := fibration_of_isPullback hP
  have : IsFibrant P := fibrant_source πA
  have hPo : IsPushout g₁₂.op u₁.op πB.op πA.op := hP.op.flip
  have hQo : IsPushout g₃₄.op u₃.op ρB.op ρA.op := hQ.op.flip
  have : Cofibration hPo.isoPushout.inv := by
    have := cofibration_of_isPushout (IsPushout.of_hasPushout g₁₂.op u₁.op)
    have := cofibrant_target (pushout.inr g₁₂.op u₁.op)
    exact ABCPrecofibrationCategory.cofibration_of_isIso _
  have : Cofibration c.op := (cofibration_op_iff _).2 ‹_›
  have hc : pushout.desc u₂.op f₁₂.op (by rw [← op_comp, ← op_comp, h₁₂]) =
      hPo.isoPushout.inv ≫ c.op := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc, hPo.inl_isoPushout_inv_assoc, ← op_comp, hcB]
    · rw [pushout.inr_desc, hPo.inr_isoPushout_inv_assoc, ← op_comp, hcA]
  have : Cofibration (pushout.desc u₂.op f₁₂.op (by rw [← op_comp, ← op_comp, h₁₂])) := by
    rw [hc]
    exact ⟨(cofibrations Cᵒᵖ).comp_mem _ _ (by assumption : Cofibration _).mem
      (by assumption : Cofibration c.op).mem⟩
  obtain ⟨h₂, h₄, hd⟩ := ABCPrecofibrationCategory.gluing_cofibration hB.op.flip hA.op.flip
    (by rw [← op_comp, ← op_comp, h₁₂]) (by rw [← op_comp, ← op_comp, h₁₃])
    (by rw [← op_comp, ← op_comp, h₂₄]) (by rw [← op_comp, ← op_comp, h₃₄])
  refine ⟨(cofibration_op_iff _).1 h₂, (cofibration_op_iff _).1 h₄, ?_⟩
  have : Cofibration hQo.isoPushout.hom := ABCPrecofibrationCategory.cofibration_of_isIso _
  have hd' : d.op = hQo.isoPushout.hom ≫
      pushout.desc u₄.op f₃₄.op (by rw [← op_comp, ← op_comp, h₃₄]) := by
    rw [← Iso.inv_comp_eq]
    apply pushout.hom_ext
    · rw [pushout.inl_desc, hQo.inl_isoPushout_inv_assoc, ← op_comp, hdB]
    · rw [pushout.inr_desc, hQo.inr_isoPushout_inv_assoc, ← op_comp, hdA]
  apply (cofibration_op_iff _).1
  rw [hd']
  exact ⟨(cofibrations Cᵒᵖ).comp_mem _ _ (by assumption : Cofibration _).mem hd.mem⟩

end ABCCofibrations.ABCPrefibrationCategory

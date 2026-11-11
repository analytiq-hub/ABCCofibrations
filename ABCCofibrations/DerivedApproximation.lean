/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ApproximationTheorem
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Total derived functors from approximations (Theorem 5.7.1, Corollary 5.7.2)

The paper's total left derived functor `(Lu, ε)`, terminal among pairs
`(Λ, λ : Λγ₁ ⟹ γ₂u)`, is mathlib's `Functor.IsLeftDerivedFunctor` (a right Kan
extension along the localization; see `docs/mathematics/adjunctions-kan-abelian.md`
on the left/right terminology).

The paper builds `Lu` from a regular left cleavage. Here we show instead that a
left approximation `t` is a left derivability structure in the sense of Kahn and
Maltsiniotis (mathlib's `LocalizerMorphism.IsLeftDerivabilityStructure`): the
categories of resolutions are connected and arrows have resolutions, both by
LAP2(1), and `t` is a localized equivalence by the approximation theorem. Then
mathlib's `LocalizerMorphism.Derives` gives the derived functor and the
characterization by the maps `ε_{tA'}`.
-/

@[expose] public section

open CategoryTheory Category Localization

namespace ABCCofibrations

variable {M' M : Type*} [Category M'] [Category M] {W' : MorphismProperty M'}
  {W : MorphismProperty M} {Φ : LocalizerMorphism W' W}
  {H' : Type*} [Category H'] {L' : M' ⥤ H'} [L'.IsLocalization W']

namespace LeftApproximation

variable (h : LeftApproximation Φ L')

include h in
/-- The categories of left resolutions along a left approximation are
connected (LAP1 and LAP2(1)). -/
lemma isConnected_leftResolution (A : M) : IsConnected (Φ.LeftResolution A) := by
  obtain ⟨A', p, hp⟩ := h.exists_resolution A
  have : Nonempty (Φ.LeftResolution A) := ⟨⟨p, hp⟩⟩
  refine zigzag_isConnected fun R₁ R₂ ↦ ?_
  obtain ⟨d⟩ := h.nonempty_factorizationData R₁.w R₂.w R₂.hw
  let R : Φ.LeftResolution A := ⟨d.σ, d.hσ⟩
  exact (Zigzag.of_hom (⟨d.i, d.fac_i⟩ : R₁ ⟶ R)).trans
    (Zigzag.of_inv (⟨d.j, d.fac_j⟩ : R₂ ⟶ R))

include h in
/-- Arrows have left resolutions along a left approximation (LAP1 and LAP2(1)). -/
lemma arrow_hasLeftResolutions : Φ.arrow.HasLeftResolutions := fun f ↦ by
  obtain ⟨A', p, hp⟩ := h.exists_resolution f.left
  obtain ⟨B', q, hq⟩ := h.exists_resolution f.right
  obtain ⟨d⟩ := h.nonempty_factorizationData (p ≫ f.hom) q hq
  exact ⟨{ X₁ := Arrow.mk d.i
           w := Arrow.homMk p d.σ (by simp [d.fac_i])
           hw := ⟨hp, d.hσ⟩ }⟩

include h in
/-- A left approximation is a left derivability structure. -/
lemma isLeftDerivabilityStructure [W'.IsMultiplicative] [W.IsMultiplicative] :
    Φ.IsLeftDerivabilityStructure := by
  have := h.isConnected_leftResolution
  have := h.arrow_hasLeftResolutions
  have := h.isLocalizedEquivalence
  exact LocalizerMorphism.IsLeftDerivabilityStructure.mk' Φ

variable [W'.IsMultiplicative] [W.IsMultiplicative]
  {M₂ : Type*} [Category M₂] (W₂ : MorphismProperty M₂) {H₂ : Type*} [Category H₂]
  (L₂ : M₂ ⥤ H₂) [L₂.IsLocalization W₂] {u : M ⥤ M₂}
  (hu : W' ≤ W₂.inverseImage (Φ.functor ⋙ u))

include h hu

/-- **Theorem 5.7.1(1)**, existence. If `t` is a left approximation and `ut`
preserves weak equivalences, then `u` has a total left derived functor. -/
theorem hasLeftDerivedFunctor : (u ⋙ L₂).HasPointwiseLeftDerivedFunctor W := by
  have := h.isLeftDerivabilityStructure
  exact LocalizerMorphism.Derives.hasPointwiseLeftDerivedFunctor (Φ := Φ)
    (fun _ _ f hf ↦ Localization.inverts L₂ W₂ _ (hu _ hf))

/-- **Theorem 5.7.1(1)**, the comparison maps. A pair `(Lu, ε)` is a total left
derived functor of `u` iff `ε : Lu(tA') ⟶ utA'` is an isomorphism for every
object `A'` of `M'`. -/
theorem isLeftDerivedFunctor_iff {H : Type*} [Category H] (L : M ⥤ H) [L.IsLocalization W]
    (LF : H ⥤ H₂) (ε : L ⋙ LF ⟶ u ⋙ L₂) :
    LF.IsLeftDerivedFunctor ε W ↔ ∀ A' : M', IsIso (ε.app (Φ.functor.obj A')) := by
  have := h.isLeftDerivabilityStructure
  exact LocalizerMorphism.Derives.isLeftDerivedFunctor_iff_isIso (Φ := Φ) (F := u ⋙ L₂)
    (fun _ _ f hf ↦ Localization.inverts L₂ W₂ _ (hu _ hf)) ε

/-- **Corollary 5.7.2(1).** Let `T : ho M' ⥤ ho M` be induced by `t`, let
`G : ho M' ⥤ ho M₂` be induced by `ut` (so `G = ho(ut)`), and let `s` be a
quasi-inverse of `T`. Then any total left derived functor `Lu` is isomorphic
to `G ∘ s`. -/
theorem leftDerivedFunctor_iso {H : Type*} [Category H] (L : M ⥤ H) [L.IsLocalization W]
    (T : H' ⥤ H) [CatCommSq Φ.functor L' L T] (G : H' ⥤ H₂)
    (eG : L' ⋙ G ≅ Φ.functor ⋙ u ⋙ L₂) (s : H ⥤ H') (e : s ⋙ T ≅ 𝟭 H)
    (LF : H ⥤ H₂) (ε : L ⋙ LF ⟶ u ⋙ L₂) [LF.IsLeftDerivedFunctor ε W] :
    Nonempty (LF ≅ s ⋙ G) := by
  have hε := (h.isLeftDerivedFunctor_iff W₂ L₂ hu L LF ε).1 inferInstance
  have : IsIso (Functor.whiskerLeft Φ.functor ε) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hε
  let e₁ : L' ⋙ T ⋙ LF ≅ L' ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatCommSq.iso Φ.functor L' L T).symm LF ≪≫
      Functor.associator _ _ _ ≪≫ asIso (Functor.whiskerLeft Φ.functor ε) ≪≫ eG.symm
  let e₂ : T ⋙ LF ≅ G := (whiskeringLeftFunctor' L' W' H₂).preimageIso e₁
  exact ⟨(Functor.leftUnitor LF).symm ≪≫ Functor.isoWhiskerRight e.symm LF ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft s e₂⟩

end LeftApproximation

namespace RightApproximation

variable (h : RightApproximation Φ L')

include h in
/-- A right approximation is a right derivability structure. -/
lemma isRightDerivabilityStructure [W'.IsMultiplicative] [W.IsMultiplicative] :
    Φ.IsRightDerivabilityStructure := by
  have := LeftApproximation.isLeftDerivabilityStructure h
  rw [LocalizerMorphism.isRightDerivabilityStructure_iff_op]
  exact this

variable [W'.IsMultiplicative] [W.IsMultiplicative]
  {M₂ : Type*} [Category M₂] (W₂ : MorphismProperty M₂) {H₂ : Type*} [Category H₂]
  (L₂ : M₂ ⥤ H₂) [L₂.IsLocalization W₂] {u : M ⥤ M₂}
  (hu : W' ≤ W₂.inverseImage (Φ.functor ⋙ u))

include h hu

/-- **Theorem 5.7.1(2)**, existence. If `t` is a right approximation and `ut`
preserves weak equivalences, then `u` has a total right derived functor. -/
theorem hasRightDerivedFunctor : (u ⋙ L₂).HasPointwiseRightDerivedFunctor W := by
  have := h.isRightDerivabilityStructure
  exact LocalizerMorphism.Derives.hasPointwiseRightDerivedFunctor (Φ := Φ)
    (fun _ _ f hf ↦ Localization.inverts L₂ W₂ _ (hu _ hf))

/-- **Theorem 5.7.1(2)**, the comparison maps. A pair `(Ru, η)` is a total right
derived functor of `u` iff `η : utA' ⟶ Ru(tA')` is an isomorphism for every
object `A'` of `M'`. -/
theorem isRightDerivedFunctor_iff {H : Type*} [Category H] (L : M ⥤ H) [L.IsLocalization W]
    (RF : H ⥤ H₂) (η : u ⋙ L₂ ⟶ L ⋙ RF) :
    RF.IsRightDerivedFunctor η W ↔ ∀ A' : M', IsIso (η.app (Φ.functor.obj A')) := by
  have := h.isRightDerivabilityStructure
  exact LocalizerMorphism.Derives.isRightDerivedFunctor_iff_isIso (Φ := Φ) (F := u ⋙ L₂)
    (fun _ _ f hf ↦ Localization.inverts L₂ W₂ _ (hu _ hf)) η

/-- **Corollary 5.7.2(2).** With `T = ho t`, `G = ho(ut)` and `s` a quasi-inverse
of `T`, any total right derived functor `Ru` is isomorphic to `G ∘ s`. -/
theorem rightDerivedFunctor_iso {H : Type*} [Category H] (L : M ⥤ H) [L.IsLocalization W]
    (T : H' ⥤ H) [CatCommSq Φ.functor L' L T] (G : H' ⥤ H₂)
    (eG : L' ⋙ G ≅ Φ.functor ⋙ u ⋙ L₂) (s : H ⥤ H') (e : s ⋙ T ≅ 𝟭 H)
    (RF : H ⥤ H₂) (η : u ⋙ L₂ ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor η W] :
    Nonempty (RF ≅ s ⋙ G) := by
  have hη := (h.isRightDerivedFunctor_iff W₂ L₂ hu L RF η).1 inferInstance
  have : IsIso (Functor.whiskerLeft Φ.functor η) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hη
  let e₁ : L' ⋙ T ⋙ RF ≅ L' ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CatCommSq.iso Φ.functor L' L T).symm RF ≪≫
      Functor.associator _ _ _ ≪≫ (asIso (Functor.whiskerLeft Φ.functor η)).symm ≪≫ eG.symm
  let e₂ : T ⋙ RF ≅ G := (whiskeringLeftFunctor' L' W' H₂).preimageIso e₁
  exact ⟨(Functor.leftUnitor RF).symm ≪≫ Functor.isoWhiskerRight e.symm RF ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft s e₂⟩

end RightApproximation

section AbstractQuillen

variable {M₁' M₁ M₂ M₂' : Type*} [Category M₁'] [Category M₁] [Category M₂] [Category M₂']
  {W₁' : MorphismProperty M₁'} {W₁ : MorphismProperty M₁} {W₂ : MorphismProperty M₂}
  {W₂' : MorphismProperty M₂'} [W₁'.IsMultiplicative] [W₁.IsMultiplicative]
  [W₂.IsMultiplicative] [W₂'.IsMultiplicative]
  {Φ₁ : LocalizerMorphism W₁' W₁} {Φ₂ : LocalizerMorphism W₂' W₂}
  {H₁' H₂' : Type*} [Category H₁'] [Category H₂'] {L₁' : M₁' ⥤ H₁'} {L₂' : M₂' ⥤ H₂'}
  [L₁'.IsLocalization W₁'] [L₂'.IsLocalization W₂']

/-- **Theorem 5.8.1** (abstract Quillen adjunction), adjunction part. Let
`u₁ ⊣ u₂` be an adjunction between `M₁` and `M₂`, `t₁ : M₁' ⟶ M₁` a left
approximation and `t₂ : M₂' ⟶ M₂` a right approximation, with `u₁t₁` and `u₂t₂`
preserving weak equivalences. Then the total left derived functor of `u₁` is left
adjoint to the total right derived functor of `u₂`.

The derived functors exist by Theorem 5.7.1. The proof is mathlib's
`Adjunction.derived` (Maltsiniotis): the composites `Lu₁ ∘ Ru₂` and `Ru₂ ∘ Lu₁`
are again derived functors, by the derivability-structure criterion. -/
theorem derived_adjunction (h₁ : LeftApproximation Φ₁ L₁') (h₂ : RightApproximation Φ₂ L₂')
    {u₁ : M₁ ⥤ M₂} {u₂ : M₂ ⥤ M₁} (adj : u₁ ⊣ u₂)
    (hu₁ : W₁' ≤ W₂.inverseImage (Φ₁.functor ⋙ u₁))
    (hu₂ : W₂' ≤ W₁.inverseImage (Φ₂.functor ⋙ u₂))
    {H₁ H₂ : Type*} [Category H₁] [Category H₂] (L₁ : M₁ ⥤ H₁) (L₂ : M₂ ⥤ H₂)
    [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    (G' : H₁ ⥤ H₂) (α : L₁ ⋙ G' ⟶ u₁ ⋙ L₂) [G'.IsLeftDerivedFunctor α W₁]
    (F' : H₂ ⥤ H₁) (β : u₂ ⋙ L₁ ⟶ L₂ ⋙ F') [F'.IsRightDerivedFunctor β W₂] :
    Nonempty (G' ⊣ F') := by
  have := h₁.isLeftDerivabilityStructure
  have := h₂.isRightDerivabilityStructure
  have hα := (h₁.isLeftDerivedFunctor_iff W₂ L₂ hu₁ L₁ G' α).1 inferInstance
  have hβ := (h₂.isRightDerivedFunctor_iff W₁ L₁ hu₂ L₂ F' β).1 inferInstance
  have : (G' ⋙ F').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α F') W₁ :=
    LocalizerMorphism.Derives.isLeftDerivedFunctor_of_isIso (Φ := Φ₁) (F := (u₁ ⋙ L₂) ⋙ F')
      (fun _ _ f hf ↦ by
        have : IsIso (L₂.map (u₁.map (Φ₁.functor.map f))) :=
          Localization.inverts L₂ W₂ _ (hu₁ _ hf)
        exact (inferInstance : IsIso (F'.map (L₂.map (u₁.map (Φ₁.functor.map f))))))
      _ (fun X ↦ by
        have := hα X
        simp only [NatTrans.comp_app, Functor.associator_inv_app, Functor.whiskerRight_app,
          Category.id_comp]
        infer_instance)
  have : (F' ⋙ G').IsRightDerivedFunctor
      (Functor.whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂ :=
    LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso (Φ := Φ₂) (F := (u₂ ⋙ L₁) ⋙ G')
      (fun _ _ f hf ↦ by
        have : IsIso (L₁.map (u₂.map (Φ₂.functor.map f))) :=
          Localization.inverts L₁ W₁ _ (hu₂ _ hf)
        exact (inferInstance : IsIso (G'.map (L₁.map (u₂.map (Φ₂.functor.map f))))))
      _ (fun X ↦ by
        have := hβ X
        simp only [NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerRight_app,
          Category.comp_id]
        infer_instance)
  exact ⟨adj.derived W₁ W₂ α β⟩

end AbstractQuillen

end ABCCofibrations

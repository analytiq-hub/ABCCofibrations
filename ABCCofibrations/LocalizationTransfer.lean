/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.MorphismProperty.Quotient

/-!
# Shared localization transfer lemmas

Two general facts about localizations are used for both the cofibration and
the fibration theory. They are proved once here, at the level of categories,
morphism properties, and quotient categories, without any homotopical
hypotheses.

* `Localization.strictUniversalPropertyFixedTargetQuotientLift`: if a
  localization `W.Q` factors through a quotient category by a relation
  compatible with `W`, then the factorization has the strict universal
  property of localization at the induced class on the quotient.
  Mathlib's `HomRel.FactorsThroughLocalization.strictUniversalPropertyFixedTarget`
  proves the converse direction (a localization of the quotient, precomposed
  with the quotient functor), so it does not apply directly.
* `Localization.strictUniversalPropertyFixedTargetQOfIsInvertedBy`: if each
  of two morphism classes is inverted by the localization functor of the
  other, then they have the same localizations.

These are the parts of the homotopy-quotient and trivial-(co)fibration
comparisons which do not depend on cylinders, path objects, or Brown's lemma.
-/

@[expose] public section

namespace CategoryTheory.Localization

variable {C D : Type*} [Category* C] [Category* D]

section Quotient

variable {homRel : HomRel C} {W : MorphismProperty C}
  {W' : MorphismProperty (Quotient homRel)}
  (hW : W = W'.inverseImage (Quotient.functor homRel))
  (L : Quotient homRel ⥤ W.Localization) (hL : Quotient.functor homRel ⋙ L = W.Q)

include hW hL in
/-- A factorization of `W.Q` through a quotient inverts the induced class. -/
theorem quotientLift_inverts : W'.IsInvertedBy L := by
  intro X Y f hf
  obtain ⟨g, rfl⟩ := (Quotient.functor homRel).map_surjective f
  have hg : W g := by rw [hW]; exact hf
  have h := W.Q_inverts g hg
  rw [← hL] at h
  exact h

/-- If `W.Q` factors through the quotient by `homRel` as `L`, and `W` is the
inverse image of `W'`, then `L` has the strict universal property of the
localization of the quotient at `W'`. -/
noncomputable def strictUniversalPropertyFixedTargetQuotientLift
    (E : Type*) [Category* E] :
    StrictUniversalPropertyFixedTarget L W' E where
  inverts := quotientLift_inverts hW L hL
  lift F hF := Construction.lift (Quotient.functor homRel ⋙ F)
    (fun _ _ f hf ↦ hF _ (by rw [hW] at hf; exact hf))
  fac F hF := by
    apply CategoryTheory.Quotient.lift_unique' homRel
    rw [← Functor.assoc, hL]
    exact Construction.fac _ _
  uniq F₁ F₂ h := by
    apply Construction.uniq
    rw [← hL, Functor.assoc, h, Functor.assoc]

include hW hL in
/-- The quotient factorization of `W.Q` is a localization at `W'`. -/
theorem isLocalization_quotientLift : L.IsLocalization W' :=
  Functor.IsLocalization.mk' _ _
    (strictUniversalPropertyFixedTargetQuotientLift hW L hL _)
    (strictUniversalPropertyFixedTargetQuotientLift hW L hL _)

end Quotient

section SameInvertingFunctors

variable {W₁ W₂ : MorphismProperty C}
  (h₁ : W₁.IsInvertedBy W₂.Q) (h₂ : W₂.IsInvertedBy W₁.Q)

include h₁ in
/-- If `W₂.Q` inverts `W₁`, then every functor inverting `W₂` inverts `W₁`. -/
theorem isInvertedBy_of_isInvertedBy_Q {E : Type*} [Category* E]
    (F : C ⥤ E) (hF : W₂.IsInvertedBy F) : W₁.IsInvertedBy F := by
  rw [← Construction.fac F hF]
  exact MorphismProperty.IsInvertedBy.of_comp _ _ h₁ _

/-- Two classes of morphisms, each inverted by the localization functor of
the other, have the same inverting functors. The canonical localization at
`W₁` therefore satisfies the strict universal property for `W₂`. -/
noncomputable def strictUniversalPropertyFixedTargetQOfIsInvertedBy
    (E : Type*) [Category* E] :
    StrictUniversalPropertyFixedTarget W₁.Q W₂ E where
  inverts := h₂
  lift F hF := Construction.lift F (isInvertedBy_of_isInvertedBy_Q h₁ F hF)
  fac _ _ := Construction.fac _ _
  uniq F₁ F₂ h := Construction.uniq F₁ F₂ h

include h₁ h₂ in
/-- Two classes of morphisms, each inverted by the localization functor of
the other, have the same localization functors. -/
theorem isLocalization_of_isInvertedBy_Q (L : C ⥤ D) [L.IsLocalization W₁] :
    L.IsLocalization W₂ := by
  have : W₁.Q.IsLocalization W₂ :=
    Functor.IsLocalization.mk' _ _
      (strictUniversalPropertyFixedTargetQOfIsInvertedBy h₁ h₂ _)
      (strictUniversalPropertyFixedTargetQOfIsInvertedBy h₁ h₂ _)
  exact Functor.IsLocalization.of_equivalence_target W₁.Q W₂ L
    (Localization.uniq W₁.Q L W₁) (Localization.compUniqFunctor W₁.Q L W₁)

end SameInvertingFunctors

end CategoryTheory.Localization

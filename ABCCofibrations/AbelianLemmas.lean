/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Elementary lemmas on abelian categories (§3.2)

Lemma 3.2.1 (exactness criteria for pushout and pullback squares), Lemma 3.2.2
(pushouts and pullbacks of monics and epics) and Lemma 3.2.6
(adjoint functors between abelian categories are right, resp. left, exact).
Pushout and pullback squares are arbitrary representatives (`IsPushout`,
`IsPullback`).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

namespace ABCCofibrations

section

variable {C : Type u} [Category.{v} C]

/-- The pushout of an epimorphism is an epimorphism, in any category. -/
theorem IsPushout.epi_of_epi {A B D E : C} {f : A ⟶ B} {g : A ⟶ D} {g' : B ⟶ E}
    {f' : D ⟶ E} (h : IsPushout f g g' f') [Epi f] : Epi f' :=
  ⟨fun a b hab ↦ h.hom_ext ((cancel_epi f).1 (by rw [← Category.assoc, h.w,
    Category.assoc, hab, ← Category.assoc, ← h.w, Category.assoc])) hab⟩

/-- The pullback of a monomorphism is a monomorphism, in any category. -/
theorem IsPullback.mono_of_mono {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Mono f] : Mono snd :=
  ⟨fun a b hab ↦ h.hom_ext ((cancel_mono f).1 (by rw [Category.assoc, h.w,
    ← Category.assoc, hab, Category.assoc, ← h.w, ← Category.assoc])) hab⟩

end

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Lemma 3.2.2(1).** In an abelian category, the pushout `f'` of a map `f`
is epic iff `f` is epic. -/
theorem IsPushout.epi_iff {A B D E : C} {f : A ⟶ B} {g : A ⟶ D} {g' : B ⟶ E}
    {f' : D ⟶ E} (h : IsPushout f g g' f') : Epi f' ↔ Epi f := by
  refine ⟨fun _ ↦ Preadditive.epi_of_cancel_zero f fun q hq ↦ ?_,
    fun _ ↦ ABCCofibrations.IsPushout.epi_of_epi h⟩
  have w : f ≫ q = g ≫ 0 := by simp [hq]
  have hd : f' ≫ h.desc q 0 w = 0 := by simp
  have h0 : h.desc q 0 w = 0 := (cancel_epi f').1 (by rw [hd, comp_zero])
  rw [← h.inl_desc q 0 w, h0, comp_zero]

/-- **Lemma 3.2.2(2).** In an abelian category, the pushout of a monic is
monic. -/
theorem IsPushout.mono_of_mono {A B D E : C} {f : A ⟶ B} {g : A ⟶ D} {g' : B ⟶ E}
    {f' : D ⟶ E} (h : IsPushout f g g' f') [Mono f] : Mono f' := by
  rw [← h.inr_isoPushout_inv]
  infer_instance

/-- **Lemma 3.2.2(3).** In an abelian category, the pullback `snd` of a map `f`
is monic iff `f` is monic. -/
theorem IsPullback.mono_iff {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) : Mono snd ↔ Mono f := by
  refine ⟨fun _ ↦ Preadditive.mono_of_cancel_zero f fun k hk ↦ ?_,
    fun _ ↦ ABCCofibrations.IsPullback.mono_of_mono h⟩
  have w : k ≫ f = 0 ≫ g := by simp [hk]
  have hl : h.lift k 0 w ≫ snd = 0 := by simp
  have h0 : h.lift k 0 w = 0 := (cancel_mono snd).1 (by rw [hl, zero_comp])
  rw [← h.lift_fst k 0 w, h0, zero_comp]

/-- **Lemma 3.2.2(4).** In an abelian category, the pullback of an epic is
epic. -/
theorem IsPullback.epi_of_epi {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) [Epi f] : Epi snd := by
  rw [← h.isoPullback_hom_snd]
  infer_instance

section Lemma321

variable {A B D E : C} {f : A ⟶ B} {g : A ⟶ D} {g' : B ⟶ E} {f' : D ⟶ E}

/-- **Lemma 3.2.1(1).** The sequence `A ⟶ B ⊕ D ⟶ E` given by `(f, -g)` and
`(g', f')` is zero iff the square commutes. (The paper uses the signs
`(f, g)` and `(g', -f')`; mathlib's conventions are used here.) -/
theorem lemma321_one :
    biprod.lift f (-g) ≫ biprod.desc g' f' = 0 ↔ f ≫ g' = g ≫ f' := by
  simp only [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, sub_eq_zero]

/-- **Lemma 3.2.1(2).** For a commutative square, `A ⟶ B ⊕ D ⟶ E ⟶ 0` is exact
iff the square is a pushout. -/
theorem lemma321_two (sq : CommSq f g g' f') :
    (sq.shortComplex.Exact ∧ Epi sq.shortComplex.g) ↔ IsPushout f g g' f' := by
  refine ⟨fun ⟨hex, _⟩ ↦ ⟨sq, ⟨sq.isColimitEquivIsColimitCokernelCofork.symm hex.gIsCokernel⟩⟩,
    fun h ↦ ⟨h.exact_shortComplex, h.epi_shortComplex_g⟩⟩

/-- **Lemma 3.2.1(3).** For a commutative square, `0 ⟶ A ⟶ B ⊕ D ⟶ E` is exact
iff the square is a pullback. -/
theorem lemma321_three (sq : CommSq f g g' f') :
    (Mono sq.shortComplex'.f ∧ sq.shortComplex'.Exact) ↔ IsPullback f g g' f' := by
  refine ⟨fun ⟨_, hex⟩ ↦ ⟨sq, ⟨sq.isLimitEquivIsLimitKernelFork.symm hex.fIsKernel⟩⟩,
    fun h ↦ ⟨h.mono_shortComplex'_f, h.exact_shortComplex'⟩⟩

/-- The sign change on the second summand of `B ⊞ D`. -/
noncomputable def signChange (B D : C) : B ⊞ D ⟶ B ⊞ D := biprod.map (𝟙 B) (-𝟙 D)

/-- The sign change as an isomorphism. -/
noncomputable def signChangeIso (B D : C) : B ⊞ D ≅ B ⊞ D where
  hom := signChange B D
  inv := signChange B D
  hom_inv_id := by ext <;> simp [signChange]
  inv_hom_id := by ext <;> simp [signChange]

/-- The two sign conventions give isomorphic short complexes. -/
noncomputable def shortComplexIso (sq : CommSq f g g' f') : sq.shortComplex' ≅ sq.shortComplex :=
  ShortComplex.isoMk (Iso.refl _) (signChangeIso B D) (Iso.refl _)
    (by
      change 𝟙 A ≫ biprod.lift f (-g) = biprod.lift f g ≫ signChange B D
      ext <;> simp [signChange])
    (by
      change signChange B D ≫ biprod.desc g' f' = biprod.desc g' (-f') ≫ 𝟙 E
      ext <;> simp [signChange])

private lemma mono_shortComplex_f_iff (sq : CommSq f g g' f') :
    Mono sq.shortComplex.f ↔ Mono sq.shortComplex'.f := by
  have h₁ : biprod.lift f (-g) = biprod.lift f g ≫ signChange B D := by
    ext <;> simp [signChange]
  have h₂ : biprod.lift f g = biprod.lift f (-g) ≫ signChange B D := by
    ext <;> simp [signChange]
  change Mono (biprod.lift f (-g)) ↔ Mono (biprod.lift f g)
  have e : signChange B D = (signChangeIso B D).hom := rfl
  constructor
  · intro _
    rw [h₂, e]
    infer_instance
  · intro _
    rw [h₁, e]
    infer_instance

/-- **Lemma 3.2.1(4).** A commutative square is a pushout and a pullback iff
`0 ⟶ A ⟶ B ⊕ D ⟶ E ⟶ 0` is short exact. -/
theorem lemma321_four (sq : CommSq f g g' f') :
    (IsPushout f g g' f' ∧ IsPullback f g g' f') ↔ sq.shortComplex.ShortExact := by
  rw [← lemma321_two sq, ← lemma321_three sq,
    ShortComplex.exact_iff_of_iso (shortComplexIso sq), ← mono_shortComplex_f_iff]
  exact ⟨fun ⟨⟨hex, _⟩, _, _⟩ ↦ ⟨hex⟩, fun h ↦ ⟨⟨h.exact, h.epi_g⟩, h.mono_f, h.exact⟩⟩

/-- **Lemma 3.2.1(5).** A pushout square with `f` monic is a pullback square. -/
theorem lemma321_five (h : IsPushout f g g' f') [Mono f] : IsPullback f g g' f' := by
  refine ((lemma321_four h.toCommSq).2 ?_).2
  have w : biprod.lift f (-g) ≫ biprod.fst = f := by simp
  have : Mono h.toCommSq.shortComplex.f := by
    change Mono (biprod.lift f (-g))
    exact mono_of_mono_fac w
  have := h.epi_shortComplex_g
  exact ⟨h.exact_shortComplex⟩

/-- **Lemma 3.2.1(5)**, other leg: a pushout square with `g` monic is a pullback
square. -/
theorem lemma321_five' (h : IsPushout f g g' f') [Mono g] : IsPullback f g g' f' :=
  (lemma321_five h.flip).flip

/-- **Lemma 3.2.1(6).** A pullback square with `f'` epic is a pushout square. -/
theorem lemma321_six (h : IsPullback f g g' f') [Epi f'] : IsPushout f g g' f' := by
  refine ((lemma321_four h.toCommSq).2 ?_).1
  have : Mono h.toCommSq.shortComplex.f :=
    (mono_shortComplex_f_iff h.toCommSq).2 h.mono_shortComplex'_f
  have w : (biprod.inr : D ⟶ B ⊞ D) ≫ biprod.desc g' f' = f' := by simp
  have : Epi h.toCommSq.shortComplex.g := by
    change Epi (biprod.desc g' f')
    exact epi_of_epi_fac w
  exact ⟨(ShortComplex.exact_iff_of_iso (shortComplexIso h.toCommSq)).1 h.exact_shortComplex'⟩

/-- **Lemma 3.2.1(6)**, other leg: a pullback square with `g'` epic is a pushout
square. -/
theorem lemma321_six' (h : IsPullback f g g' f') [Epi g'] : IsPushout f g g' f' :=
  (lemma321_six h.flip).flip

end Lemma321

omit [Abelian C] in
/-- **Lemma 3.2.6.** If `u ⊣ v` is an adjoint pair, then `u` preserves finite
colimits (it is right exact) and `v` preserves finite limits (it is left
exact). This holds between any categories, in particular abelian ones. -/
theorem Adjunction.rightExact_leftExact {D : Type u'} [Category.{v'} D]
    {u : C ⥤ D} {w : D ⥤ C} (adj : u ⊣ w) :
    PreservesFiniteColimits u ∧ PreservesFiniteLimits w := by
  have := adj.leftAdjoint_preservesColimits
  have := adj.rightAdjoint_preservesLimits
  exact ⟨inferInstance, inferInstance⟩

end ABCCofibrations

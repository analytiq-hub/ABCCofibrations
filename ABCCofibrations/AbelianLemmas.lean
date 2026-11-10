/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Elementary lemmas on abelian categories (§3.2)

Lemma 3.2.2 (pushouts and pullbacks of monics and epics) and Lemma 3.2.6
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

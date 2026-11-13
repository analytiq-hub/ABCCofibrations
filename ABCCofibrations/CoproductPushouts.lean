/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Coproducts of chosen pushout squares

Only the four coproducts concerned are required. The ambient category need
not have arbitrary colimits.
-/

@[expose] public section

open CategoryTheory Limits

namespace ABCCofibrations

/-- A coproduct of pushout squares is a pushout square. -/
theorem isPushout_sigmaMap {ι C : Type*} [Category C]
    {A B D Q : ι → C} (i : ∀ k, A k ⟶ B k) (j : ∀ k, A k ⟶ D k)
    (l : ∀ k, B k ⟶ Q k) (r : ∀ k, D k ⟶ Q k)
    [HasCoproduct A] [HasCoproduct B] [HasCoproduct D] [HasCoproduct Q]
    (h : ∀ k, IsPushout (i k) (j k) (l k) (r k)) :
    IsPushout (Limits.Sigma.map i) (Limits.Sigma.map j)
      (Limits.Sigma.map l) (Limits.Sigma.map r) := by
  have hw : Limits.Sigma.map i ≫ Limits.Sigma.map l =
      Limits.Sigma.map j ≫ Limits.Sigma.map r := by
    apply Sigma.hom_ext
    intro k
    simp only [Sigma.ι_map_assoc, Sigma.ι_map]
    simpa only [Category.assoc] using congrArg (· ≫ Sigma.ι Q k) (h k).w
  let desc (s : PushoutCocone (Limits.Sigma.map i) (Limits.Sigma.map j)) : (∐ Q) ⟶ s.pt :=
    Sigma.desc (fun k ↦ (h k).desc (Sigma.ι B k ≫ s.inl) (Sigma.ι D k ≫ s.inr) (by
      have hs := congrArg (Sigma.ι A k ≫ ·) s.condition
      simpa only [Sigma.ι_map_assoc] using hs))
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw)
  refine PushoutCocone.IsColimit.mk hw desc ?_ ?_ ?_
  · intro s
    apply Sigma.hom_ext
    intro k
    dsimp only [desc]
    rw [Sigma.ι_map_assoc, Sigma.ι_comp_desc, (h k).inl_desc]
  · intro s
    apply Sigma.hom_ext
    intro k
    dsimp only [desc]
    rw [Sigma.ι_map_assoc, Sigma.ι_comp_desc, (h k).inr_desc]
  · intro s m hmL hmR
    apply Sigma.hom_ext
    intro k
    dsimp only [desc]
    rw [Sigma.ι_comp_desc]
    apply (h k).hom_ext
    · rw [(h k).inl_desc]
      have hs := congrArg (Sigma.ι B k ≫ ·) hmL
      simpa only [Sigma.ι_map_assoc] using hs
    · rw [(h k).inr_desc]
      have hs := congrArg (Sigma.ι D k ≫ ·) hmR
      simpa only [Sigma.ι_map_assoc] using hs

end ABCCofibrations

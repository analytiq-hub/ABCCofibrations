/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# An obstruction to the separate comparison claims in relative Brown factorization

The set-theoretic configuration described in `docs/relative-brown-factorization.md`
cannot have an injective target-side comparison map. We check the relevant
pushout and the elementary injectivity contradiction here. This module does not
construct the full ABC structure on types with injections as cofibrations.
-/

public section

universe u

open CategoryTheory

namespace ABCCofibrations.RelativeBrownObstruction

/-- With identity right vertical map, the target-side pushout is the original
factorization object. -/
theorem target_pushout :
    IsPushout (TypeCat.ofHom Sum.inr : Unit ⟶ Bool ⊕ Unit) (𝟙 Unit)
      (𝟙 (Bool ⊕ Unit)) (TypeCat.ofHom Sum.inr) :=
  IsPushout.of_id_snd

/-- Collapsing the two source points forces any compatible comparison map to
identify them; such a map cannot be injective. -/
theorem no_injective_compatible_map (Z : Type u) :
    ¬ ∃ (i₂ : Unit → Z) (c : Bool ⊕ Unit → Z),
      Function.Injective c ∧ ∀ x : Bool, c (Sum.inl x) = i₂ () := by
  rintro ⟨i₂, c, hc, h⟩
  have he : c (Sum.inl true) = c (Sum.inl false) := (h true).trans (h false).symm
  have htf : true = false := Sum.inl.inj (hc he)
  cases htf

end ABCCofibrations.RelativeBrownObstruction

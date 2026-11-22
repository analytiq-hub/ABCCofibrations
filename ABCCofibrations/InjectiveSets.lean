/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Basic
public import Mathlib.CategoryTheory.Types.Monomorphisms
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Sets with injections: a simple cofibration category

`InjSet` is the category of sets (`Type`) with injections as cofibrations and
**all** maps as weak equivalences. It satisfies CF1–CF6. Its homotopy theory is
trivial, but Reedy cofibrancy in it is the purely combinatorial condition that
latching maps are injective. This makes it a convenient source of
counterexamples about Reedy cofibrancy.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
namespace ABCCofibrations

/-- Sets, to carry the injective cofibration structure. -/
def InjSet : Type 1 := Type

namespace InjSet

instance : Category InjSet := inferInstanceAs (Category Type)

instance : HasColimits InjSet := inferInstanceAs (HasColimits Type)

instance : HasInitial InjSet := inferInstanceAs (HasInitial Type)

instance : CategoryWithCofibrations InjSet := ⟨monomorphisms Type⟩

instance : CategoryWithWeakEquivalences InjSet := ⟨⊤⟩

lemma cofibration_iff {X Y : InjSet} (f : X ⟶ Y) :
    Cofibration f ↔ Mono (C := Type) f :=
  ⟨fun h ↦ h.mem, fun h ↦ ⟨h⟩⟩

lemma weakEquivalence (X Y : InjSet) (f : X ⟶ Y) : WeakEquivalence f := ⟨trivial⟩

/-- Maps out of an initial set are injective. -/
lemma isCofibrant (X : InjSet) : IsCofibrant X := by
  change Cofibration (initial.to X)
  rw [cofibration_iff, mono_iff_injective]
  intro x
  exact (initial.to (C := Type) PEmpty x).elim

instance : (weakEquivalences InjSet).HasTwoOutOfThreeProperty where
  comp_mem _ _ _ _ := trivial
  of_postcomp _ _ _ _ := trivial
  of_precomp _ _ _ _ := trivial

instance precofibrationCategory : ABCPrecofibrationCategory InjSet where
  initial_cofibrant := isCofibrant _
  cofibrations_comp := inferInstanceAs (monomorphisms Type).IsStableUnderComposition
  weakEquivalence_of_isIso f _ := weakEquivalence _ _ f
  cofibration_of_isIso f _ _ := (cofibration_iff f).2 (inferInstanceAs (Mono (C := Type) f))
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout _ _ := inferInstanceAs (HasPushout (C := Type) _ _)
  cofibration_of_isPushout {A B D E i f g j} h hA hD hi :=
    ⟨IsStableUnderCobaseChange.of_isPushout (P := monomorphisms Type) h.flip hi.mem⟩
  weakEquivalence_of_isPushout _ := weakEquivalence _ _ _
  factorization {A B} f _ := by
    refine ⟨(A ⨿ B : Type), (coprod.inl : (A : Type) ⟶ A ⨿ B), coprod.desc f (𝟙 _),
      ?_, weakEquivalence _ _ _, coprod.inl_desc _ _⟩
    exact (cofibration_iff _).2 inferInstance

/-- In a sequence of injections, the maps from the first set are injective. -/
lemma injective_map_of_succ (F : ℕ ⥤ Type) (hf : ∀ n, Function.Injective
    (F.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    Function.Injective (F.map (homOfLE (Nat.zero_le n))) := by
  induction n with
  | zero =>
    rw [show homOfLE (Nat.zero_le 0) = 𝟙 0 from Subsingleton.elim _ _, F.map_id]
    exact fun _ _ h ↦ h
  | succ n ih =>
    have : F.map (homOfLE (Nat.zero_le (n + 1))) =
        F.map (homOfLE (Nat.zero_le n)) ≫ F.map (homOfLE (Nat.le_succ n)) := by
      rw [← F.map_comp]
      rfl
    rw [this]
    exact (hf n).comp ih

instance cofibrationCategory : ABCCofibrationCategory.{0} InjSet where
  hasCoproductOfCofibrant A _ := inferInstanceAs (HasCoproduct (C := Type) A)
  coproduct_cofibrant _ _ _ := isCofibrant _
  coproduct_cofibration {ι A B} f _ hf _ _ :=
    ⟨MorphismProperty.colimMap (W := monomorphisms Type) (J := Discrete ι)
      (X := Discrete.functor (C := Type) fun i ↦ A i)
      (Y := Discrete.functor (C := Type) fun i ↦ B i)
      (Discrete.natTrans fun i ↦ (f i.as : (A i.as : Type) ⟶ B i.as))
      (fun i ↦ (cofibration_iff (f i.as)).1 (hf i.as))⟩
  coproduct_weakEquivalence _ _ _ _ _ _ := weakEquivalence _ _ _
  hasSequentialColimit F _ _ := inferInstanceAs (HasColimit (C := Type) F)
  sequential_cofibration F _ hf _ := by
    rw [cofibration_iff, mono_iff_injective]
    intro x y h
    obtain ⟨n, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' (F := (F : ℕ ⥤ Type))
      (colimit.isColimit (C := Type) F) x y).1 h
    have hg' : g = homOfLE (Nat.zero_le n) := Subsingleton.elim _ _
    subst hg'
    exact injective_map_of_succ F (fun m ↦ (mono_iff_injective _).1 ((cofibration_iff _).1 (hf m)))
      n hg
  sequential_weakEquivalence _ _ _ _ _ := weakEquivalence _ _ _

end InjSet

end ABCCofibrations

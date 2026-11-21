/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyCoproducts

/-! # The full Reedy cofibration category

Theorem 9.2.4(1)(a), CF1–CF6, for every small direct category. The structural
coproduct and sequential-colimit statements use the checked latching
interchange and relative comparison theorems; triviality is pointwise.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.ReedyDiagram
open ABCPrecofibrationCategory

variable (D : Type w) [SmallCategory D] [IsDirect D]
  (M : Type u) [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]

/-- Theorem 9.2.4(1)(a): all six ABC axioms for small direct Reedy diagrams. -/
instance (priority := 100) cofibrationCategory_small :
    ABCCofibrationCategory.{w} (ReedyDiagram D M) where
  hasCoproductOfCofibrant A hA := by
    have h (i) := isReedyCofibrant_of_isCofibrant (hA i)
    choose hLatch hReedy using h
    exact (reedy_coproduct (fun i ↦ (A i : D ⥤ M)) hReedy).choose
  coproduct_cofibrant A hA _ := by
    have h (i) := isReedyCofibrant_of_isCofibrant (hA i)
    choose hLatch hReedy using h
    obtain ⟨_, hL, hR⟩ := reedy_coproduct (fun i ↦ (A i : D ⥤ M)) hReedy
    exact isCofibrant_of_isReedyCofibrant hR
  coproduct_cofibration {ι A B} f hA hf _ _ := by
    have h (i) := (cofibration_iff (f i)).1 (hf i)
    choose hLA hLB hR using h
    obtain ⟨_, _, hLSA, hLSB, hSum⟩ := reedyCofibration_coproduct
      (fun i ↦ (A i : D ⥤ M)) (fun i ↦ (f i : (A i : D ⥤ M) ⟶ (B i : D ⥤ M))) hR
    exact ⟨⟨hLSA, hLSB, hSum⟩⟩
  coproduct_weakEquivalence {ι A B} f hA hf hw _ _ := by
    have h (i) := (cofibration_iff (f i)).1 (hf i)
    choose hLA hLB hR using h
    let A' : ι → PointwiseDiagram D M := fun i ↦ (A i : D ⥤ M)
    let B' : ι → PointwiseDiagram D M := fun i ↦ (B i : D ⥤ M)
    let f' (i) : A' i ⟶ B' i := f i
    have hPA (i) : IsCofibrant (A' i) :=
      (PointwiseDiagram.isCofibrant_iff _).2 (hR i).1.isCofibrant_obj
    have hPf (i) : Cofibration (f' i) :=
      ⟨fun d ↦ ((hR i).cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
        ABCCofibrationCategory.sequentialCofibrationAxiom d).2⟩
    have hPw (i) : WeakEquivalence (f' i) := ⟨(hw i).mem⟩
    have : HasCoproduct A' := inferInstanceAs (HasCoproduct A)
    have : HasCoproduct B' := inferInstanceAs (HasCoproduct B)
    have hSum := ABCCofibrationCategory.coproduct_weakEquivalence
      (C := PointwiseDiagram D M) f' hPA hPf hPw
    exact ⟨hSum.mem⟩
  hasSequentialColimit F h0 hf := sequentialCofibrationAxiom_small.hasColimit F h0 hf
  sequential_cofibration F h0 hf _ := sequentialCofibrationAxiom_small.cofibration F h0 hf
  sequential_weakEquivalence F h0 hf hw _ := trivialSequentialAxiom_small F h0 hf hw

end ABCCofibrations.ReedyDiagram

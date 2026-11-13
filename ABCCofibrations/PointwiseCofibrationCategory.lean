/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyPointwise
public import ABCCofibrations.OverUnderCofibrationCategory
public import ABCCofibrations.FibrationCategory

/-!
# CF5–CF6 for pointwise diagram structures

Completes Theorem 9.2.4(1)(b) for finite direct categories. Coproducts and
sequential colimits are constructed pointwise, using CF5–CF6 only on the
cofibrant objects concerned. No unrestricted cocompleteness is assumed.
The inverse statement 9.2.4(2)(b) is obtained by duality.
-/

@[expose] public section

universe w s v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations
namespace PointwiseDiagram

variable {D : Type w} [SmallCategory D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory.{s} M]

open ABCPrecofibrationCategory

/-- Coproducts exist at each object for a family of pointwise cofibrant diagrams. -/
lemma hasCoproduct_obj {ι : Type s} (A : ι → PointwiseDiagram D M)
    (hA : ∀ i, IsCofibrant (A i)) (e : D) :
    HasCoproduct (fun i ↦ (A i : D ⥤ M).obj e) :=
  ABCCofibrationCategory.hasCoproductOfCofibrant _ (fun i ↦ (isCofibrant_iff _).1 (hA i) e)

/-- The individual coproducts needed to construct a coproduct of cofibrant diagrams. -/
lemma hasCoproduct_evaluations {ι : Type s} (A : ι → PointwiseDiagram D M)
    (hA : ∀ i, IsCofibrant (A i)) (e : D) :
    HasColimit ((Discrete.functor (fun i ↦ (A i : D ⥤ M))).flip.obj e) := by
  let : HasColimit (Discrete.functor
      (((Discrete.functor (fun i ↦ (A i : D ⥤ M))).flip.obj e).obj ∘ Discrete.mk)) :=
    hasCoproduct_obj A hA e
  exact hasColimit_of_iso Discrete.natIsoFunctor

/-- The individual sequential colimits needed for a sequence of pointwise cofibrations. -/
lemma hasSequentialColimit_evaluations (F : ℕ ⥤ PointwiseDiagram D M)
    (h0 : IsCofibrant (F.obj 0)) (hf : ∀ n, Cofibration (F.map (succHom n))) (e : D) :
    HasColimit ((show ℕ ⥤ D ⥤ M from F).flip.obj e) :=
  ABCCofibrationCategory.hasSequentialColimit _ ((isCofibrant_iff _).1 h0 e)
    (fun n ↦ (hf n).mem e)

variable [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsDirect D]

/-- Theorem 9.2.4(1)(b), CF1–CF6, for finite direct indexing categories. -/
instance cofibrationCategory : ABCCofibrationCategory.{s} (PointwiseDiagram D M) where
  hasCoproductOfCofibrant A hA := by
    let hEvalA : ∀ e, HasColimit ((Discrete.functor (fun i ↦ (A i : D ⥤ M))).flip.obj e) :=
      hasCoproduct_evaluations A hA
    exact @functorCategoryHasColimit _ _ _ _ _ _
      (Discrete.functor (fun i ↦ (A i : D ⥤ M))) hEvalA
  coproduct_cofibrant A hA _ := by
    let hEvalA : ∀ e, HasColimit ((Discrete.functor (fun i ↦ (A i : D ⥤ M))).flip.obj e) :=
      hasCoproduct_evaluations A hA
    apply (isCofibrant_iff _).2
    intro e
    let U : PointwiseDiagram D M ⥤ M := (evaluation D M).obj e
    have : HasCoproduct (fun i ↦ U.obj (A i)) := hasCoproduct_obj A hA e
    have := ABCCofibrationCategory.coproduct_cofibrant (fun i ↦ U.obj (A i))
      (fun i ↦ (isCofibrant_iff _).1 (hA i) e)
    have : PreservesColimit (Discrete.functor A) U :=
      @evaluation_preservesColimit _ _ _ _ _ _
        (Discrete.functor (fun i ↦ (A i : D ⥤ M))) hEvalA e
    have := cofibration_of_isIso (sigmaComparison U A)
    exact cofibrant_target (sigmaComparison U A)
  coproduct_cofibration {ι A B} f hA hf _ _ := by
    have hB (i) : IsCofibrant (B i) := by
      have := hA i
      have := hf i
      exact cofibrant_target (f i)
    let hEvalA : ∀ e, HasColimit ((Discrete.functor (fun i ↦ (A i : D ⥤ M))).flip.obj e) :=
      hasCoproduct_evaluations A hA
    let hEvalB : ∀ e, HasColimit ((Discrete.functor (fun i ↦ (B i : D ⥤ M))).flip.obj e) :=
      hasCoproduct_evaluations B hB
    refine ⟨fun e ↦ ?_⟩
    let U : PointwiseDiagram D M ⥤ M := (evaluation D M).obj e
    have : HasCoproduct (fun i ↦ U.obj (A i)) := hasCoproduct_obj A hA e
    have : HasCoproduct (fun i ↦ U.obj (B i)) := hasCoproduct_obj B hB e
    have : PreservesColimit (Discrete.functor A) U :=
      @evaluation_preservesColimit _ _ _ _ _ _
        (Discrete.functor (fun i ↦ (A i : D ⥤ M))) hEvalA e
    have : PreservesColimit (Discrete.functor B) U :=
      @evaluation_preservesColimit _ _ _ _ _ _
        (Discrete.functor (fun i ↦ (B i : D ⥤ M))) hEvalB e
    have := ABCCofibrationCategory.coproduct_cofibrant (fun i ↦ U.obj (A i))
      (fun i ↦ (isCofibrant_iff _).1 (hA i) e)
    have := ABCCofibrationCategory.coproduct_cofibration (fun i ↦ U.map (f i))
      (fun i ↦ (isCofibrant_iff _).1 (hA i) e) (fun i ↦ (hf i).mem e)
    have := cofibration_of_isIso (sigmaComparison U A)
    have := cofibrant_target (sigmaComparison U A)
    have := cofibration_of_isIso (inv (sigmaComparison U A))
    have := cofibrant_target (Limits.Sigma.map (fun i ↦ U.map (f i)))
    have := cofibration_of_isIso (sigmaComparison U B)
    change Cofibration (U.map (Limits.Sigma.map f))
    rw [show U.map (Limits.Sigma.map f) = inv (sigmaComparison U A) ≫
      Limits.Sigma.map (fun i ↦ U.map (f i)) ≫ sigmaComparison U B by
        rw [← sigmaComparison_map U f, IsIso.inv_hom_id_assoc]]
    infer_instance
  coproduct_weakEquivalence {ι A B} f hA hf hw _ _ := by
    have hB (i) : IsCofibrant (B i) := by
      have := hA i
      have := hf i
      exact cofibrant_target (f i)
    let hEvalA : ∀ e, HasColimit ((Discrete.functor (fun i ↦ (A i : D ⥤ M))).flip.obj e) :=
      hasCoproduct_evaluations A hA
    let hEvalB : ∀ e, HasColimit ((Discrete.functor (fun i ↦ (B i : D ⥤ M))).flip.obj e) :=
      hasCoproduct_evaluations B hB
    refine ⟨fun e ↦ ?_⟩
    let U : PointwiseDiagram D M ⥤ M := (evaluation D M).obj e
    have : HasCoproduct (fun i ↦ U.obj (A i)) := hasCoproduct_obj A hA e
    have : HasCoproduct (fun i ↦ U.obj (B i)) := hasCoproduct_obj B hB e
    have : PreservesColimit (Discrete.functor A) U :=
      @evaluation_preservesColimit _ _ _ _ _ _
        (Discrete.functor (fun i ↦ (A i : D ⥤ M))) hEvalA e
    have : PreservesColimit (Discrete.functor B) U :=
      @evaluation_preservesColimit _ _ _ _ _ _
        (Discrete.functor (fun i ↦ (B i : D ⥤ M))) hEvalB e
    have := ABCCofibrationCategory.coproduct_weakEquivalence (fun i ↦ U.map (f i))
      (fun i ↦ (isCofibrant_iff _).1 (hA i) e) (fun i ↦ (hf i).mem e)
      (fun i ↦ (hw i).mem e)
    have := weakEquivalence_of_isIso (inv (sigmaComparison U A))
    have := weakEquivalence_of_isIso (sigmaComparison U B)
    change WeakEquivalence (U.map (Limits.Sigma.map f))
    rw [show U.map (Limits.Sigma.map f) = inv (sigmaComparison U A) ≫
      Limits.Sigma.map (fun i ↦ U.map (f i)) ≫ sigmaComparison U B by
        rw [← sigmaComparison_map U f, IsIso.inv_hom_id_assoc]]
    infer_instance
  hasSequentialColimit F h0 hf := by
    have := hasSequentialColimit_evaluations F h0 hf
    exact functorCategoryHasColimit (show ℕ ⥤ D ⥤ M from F)
  sequential_cofibration F h0 hf _ := by
    have := hasSequentialColimit_evaluations F h0 hf
    refine ⟨fun e ↦ ?_⟩
    let U : PointwiseDiagram D M ⥤ M := (evaluation D M).obj e
    have : PreservesColimit F U := evaluation_preservesColimit (show ℕ ⥤ D ⥤ M from F) e
    have := ABCCofibrationCategory.sequential_cofibration (F ⋙ U)
      ((isCofibrant_iff _).1 h0 e) (fun n ↦ (hf n).mem e)
    have : IsCofibrant ((F ⋙ U).obj 0) := (isCofibrant_iff _).1 h0 e
    have := cofibrant_target (colimit.ι (F ⋙ U) 0)
    have := cofibration_of_isIso (preservesColimitIso U F).inv
    change Cofibration (U.map (colimit.ι F 0))
    rw [← ι_preservesColimitIso_inv]
    infer_instance
  sequential_weakEquivalence F h0 hf hw _ := by
    have := hasSequentialColimit_evaluations F h0 hf
    refine ⟨fun e ↦ ?_⟩
    let U : PointwiseDiagram D M ⥤ M := (evaluation D M).obj e
    have : PreservesColimit F U := evaluation_preservesColimit (show ℕ ⥤ D ⥤ M from F) e
    have := ABCCofibrationCategory.sequential_weakEquivalence (F ⋙ U)
      ((isCofibrant_iff _).1 h0 e) (fun n ↦ (hf n).mem e) (fun n ↦ (hw n).mem e)
    have := weakEquivalence_of_isIso (preservesColimitIso U F).inv
    change WeakEquivalence (U.map (colimit.ι F 0))
    rw [← ι_preservesColimitIso_inv]
    infer_instance

end PointwiseDiagram

namespace PointwiseFibDiagram

variable (D : Type w) [SmallCategory D] [Finite D] [∀ x y : D, Finite (x ⟶ y)]
  [IsInverse D] (M : Type u) [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCFibrationCategory.{s} M]

/-- Theorem 9.2.4(2)(b), F1–F6, for finite inverse indexing categories, by duality. -/
theorem fibrationCategory : ABCFibrationCategory.{s} (PointwiseFibDiagram D M) := by
  refine ABCCofibrationCategory.of_equivalence (D' := PointwiseDiagram Dᵒᵖ Mᵒᵖ)
    (show (PointwiseFibDiagram D M)ᵒᵖ ≌ PointwiseDiagram Dᵒᵖ Mᵒᵖ from
      Functor.opUnopEquiv D M) ?_ ?_
  · ext X Y f
    change (∀ e, Fibration _) ↔ ∀ e, Cofibration _
    exact ⟨fun h e ↦ (cofibration_op_iff _).2 (h e.unop),
      fun h e ↦ (cofibration_op_iff _).1 (h (Opposite.op e))⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (Opposite.op e))⟩

end PointwiseFibDiagram
end ABCCofibrations

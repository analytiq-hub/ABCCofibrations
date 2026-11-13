/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyColimitMaps
public import ABCCofibrations.FibrationBasic
public import ABCCofibrations.LimitComparison

/-!
# Limits of Reedy fibrant diagrams over finite inverse categories

Theorem 9.3.5(2) and Corollary 9.3.6(2) for finite inverse categories, from the
cofibration statements for `Dᵒᵖ` and `Mᵒᵖ`. The matching object `MX_d` is the
unopposite of the latching object of `X.op` at `op d`.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

instance {D : Type*} [Finite D] : Finite Dᵒᵖ :=
  Finite.of_injective unop (fun _ _ h ↦ unop_injective h)

instance {D : Type*} [Category D] [∀ x y : D, Finite (x ⟶ y)] (x y : Dᵒᵖ) : Finite (x ⟶ y) :=
  Finite.of_injective (fun g : x ⟶ y ↦ g.unop) (fun _ _ h ↦ Quiver.Hom.unop_inj h)

variable {M : Type u₂} [Category.{v₂} M]

/-- The matching object `MX_d`, the unopposite of the latching object of `X.op`. -/
noncomputable abbrev matchingObj {D : Type*} [Category D] (X : D ⥤ M) (d : D)
    [HasColimit (latchingDiagram X.op (op d))] : M :=
  (latchingObj X.op (op d)).unop

/-- The map `MX_d ⟶ MY_d` induced by `f : X ⟶ Y`. -/
noncomputable abbrev matchingObjMap {D : Type*} [Category D] {X Y : D ⥤ M} (f : X ⟶ Y) (d : D)
    [HasColimit (latchingDiagram X.op (op d))] [HasColimit (latchingDiagram Y.op (op d))] :
    matchingObj X d ⟶ matchingObj Y d :=
  (latchingObjMap (NatTrans.op f) (op d)).unop

variable [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]
  [ABCPrefibrationCategory M]
  {D : Type w} [SmallCategory D] [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsInverse D]

open ABCPrefibrationCategory

omit [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]
  [ABCPrefibrationCategory M] [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsInverse D] in
lemma op_limMap' {X Y : D ⥤ M} [HasLimit X] [HasLimit Y] (f : X ⟶ Y) :
    (limMap f).op = (colimitOpIsoOpLimit Y).inv ≫ colimMap (NatTrans.op f) ≫
      (colimitOpIsoOpLimit X).hom :=
  op_limMap_comparison f

omit [∀ x y : D, Finite (x ⟶ y)] in
/-- **Theorem 9.3.5(2)(a)**, for finite inverse categories. The limit of a Reedy
fibrant diagram exists and is fibrant. -/
theorem reedyFibrant_limit (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X.op d)]
    (hX : IsReedyFibrant X) : ∃ (_ : HasLimit X), IsFibrant (limit X) := by
  have := Fintype.ofFinite Dᵒᵖ
  obtain ⟨_, hc⟩ := reedyCofibrant_colimit_finite _ Dᵒᵖ rfl X.op hX
  have : HasLimit X := hasLimit_of_hasColimit_op X
  refine ⟨this, (isFibrant_iff_isCofibrant_op _).2 ?_⟩
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  exact ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit X).hom

/-- **Theorem 9.3.5(2)(b)**, for finite inverse categories. The limit of a Reedy
fibration is a fibration. -/
theorem reedyFibration_limMap {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] {f : X ⟶ Y} (hf : IsReedyFibration f) :
    ∃ (_ : HasLimit X) (_ : HasLimit Y), Fibration (limMap f) := by
  have := Fintype.ofFinite Dᵒᵖ
  obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap hf
  obtain ⟨_, hY⟩ := reedyCofibrant_colimit_finite _ Dᵒᵖ rfl Y.op hf.1
  have hX : HasLimit X := hasLimit_of_hasColimit_op X
  have hY' : HasLimit Y := hasLimit_of_hasColimit_op Y
  refine ⟨hX, hY', (cofibration_op_iff _).1 ?_⟩
  rw [op_limMap']
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit Y).hom
  have : IsCofibrant (op (limit Y)) :=
    ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit Y).hom
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit Y).inv
  have : IsCofibrant (colimit X.op) :=
    ABCPrecofibrationCategory.cofibrant_target (colimMap (NatTrans.op f))
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance

/-- **Theorem 9.3.5(2)(c)**, for finite inverse categories. The limit of a
pointwise weak equivalence of Reedy fibrant diagrams is a weak equivalence. -/
theorem reedyFibrant_limMap_weakEquivalence {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X.op d)] [∀ d, HasColimit (latchingDiagram Y.op d)]
    (hX : IsReedyFibrant X) (hY : IsReedyFibrant Y) (f : X ⟶ Y)
    (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasLimit X) (_ : HasLimit Y), WeakEquivalence (limMap f) := by
  obtain ⟨_, _, hc⟩ := reedyCofibrant_colimMap_weakEquivalence hY hX (NatTrans.op f)
    (fun d ↦ (weakEquivalences_op_iff _).2 (hw d.unop))
  have hX' : HasLimit X := hasLimit_of_hasColimit_op X
  have hY' : HasLimit Y := hasLimit_of_hasColimit_op Y
  refine ⟨hX', hY', (weakEquivalences_op_iff _).1 ?_⟩
  rw [op_limMap']
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit Y).inv
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance

/-- **Corollary 9.3.6(2)**, for finite inverse categories. A Reedy fibration
`f : X ⟶ Y` induces fibrations `MX_d ⟶ MY_d` and `X_d ⟶ Y_d`. -/
theorem IsReedyFibration.fibration_app {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X.op d)] [∀ d, HasColimit (latchingDiagram Y.op d)]
    {f : X ⟶ Y} (hf : IsReedyFibration f) (d : D) :
    Fibration (matchingObjMap f d) ∧ Fibration (f.app d) := by
  obtain ⟨h₁, h₂⟩ := IsReedyCofibration.cofibration_app hf (op d)
  exact ⟨(fibration_unop_iff _).2 h₁, (cofibration_op_iff _).1 h₂⟩

end ABCCofibrations

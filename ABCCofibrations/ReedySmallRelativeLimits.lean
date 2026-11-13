/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyRelativeLimits
public import ABCCofibrations.ReedySmallRelativeColimits
public import ABCCofibrations.FibrationCategory

/-! # Relative limits for arbitrary small inverse categories

Theorem 9.4.1(2)(a),(c), transported through opposites from the direct side.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra Opposite
namespace ABCCofibrations
variable {D : Type w} [SmallCategory D]
variable [IsInverse D] {M : Type u} [Category.{v} M]
  [CategoryWithFibrations M] [CategoryWithWeakEquivalences M] [HasTerminal M]
  [ABCFibrationCategory.{w} M]

open ABCPrefibrationCategory

/-- Cofibrant opposite colimits for a closed restriction of a Reedy fibrant diagram. -/
lemma reedyFibrant_closed_op_colimit_small (P : ObjectProperty D)
    (hP : IsClosedDiagramSubcategory P)
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X.op d)] (hX : IsReedyFibrant X) :
    ∃ (_ : HasColimit (P.ι.op ⋙ X.op)), IsCofibrant (colimit (P.ι.op ⋙ X.op)) := by
  obtain ⟨hPQ, _, _⟩ := reedyCofibrant_colimit_open_small
    ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom P.op hP.op X.op hX
  obtain ⟨_, hPC⟩ := OpenDiagramSubcategory.isReedyCofibrant P.op hP.op X.op hX
  obtain ⟨_, hCP⟩ := reedyCofibrant_colimit (P.op.ι ⋙ X.op) hPC
  have hcomp : HasColimit ((P.opEquivalence).functor ⋙ (P.ι ⋙ X).op) := hPQ
  have : HasColimit (P.ι ⋙ X).op := Functor.Final.hasColimit_of_comp (P.opEquivalence).functor
  have : IsCofibrant (colimit ((P.opEquivalence).functor ⋙ (P.ι ⋙ X).op)) := hCP
  have := ABCPrecofibrationCategory.cofibration_of_isIso
    (colimit.pre (P.ι ⋙ X).op (P.opEquivalence).functor)
  have hCP' := ABCPrecofibrationCategory.cofibrant_target
    (colimit.pre (P.ι ⋙ X).op (P.opEquivalence).functor)
  have hcol : HasColimit (P.ι.op ⋙ X.op) :=
    hasColimit_of_iso (Functor.opComp P.ι X).symm
  exact ⟨hcol, hCP'⟩

/-- Theorem 9.4.1(2)(a), for closed full subcategories of any small inverse category. -/
theorem reedyFibrant_limit_closed_small (P : ObjectProperty D) (hP : IsClosedDiagramSubcategory P)
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X.op d)] (hX : IsReedyFibrant X) :
    ∃ (_ : HasLimit (P.ι ⋙ X)) (_ : HasLimit X), Fibration (limit.pre X P.ι) := by
  obtain ⟨hPQ, hCP'⟩ := reedyFibrant_closed_op_colimit_small P hP X hX
  have hopen : ∀ {a : Dᵒᵖ} (e : P.FullSubcategoryᵒᵖ), (a ⟶ P.ι.op.obj e) →
      ∃ e', P.ι.op.obj e' = a := by
    intro a e f
    exact ⟨op ⟨a.unop, hP f.unop e.unop.property⟩, rfl⟩
  obtain ⟨_, hc'⟩ := reedyCofibrant_colimit_pre_small
    ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom
    P.ι.op hopen X.op hX hCP'
  have : HasColimit (P.ι ⋙ X).op := hasColimit_of_iso (Functor.opComp P.ι X)
  have : IsCofibrant (colimit (P.ι ⋙ X).op) := hCP'
  have hPX : HasLimit (P.ι ⋙ X) := hasLimit_of_hasColimit_op _
  have hDX' : HasLimit X := hasLimit_of_hasColimit_op _
  refine ⟨hPX, hDX', (cofibration_op_iff _).1 ?_⟩
  rw [op_limit_pre]
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit (P.ι ⋙ X)).hom
  have := ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit (P.ι ⋙ X)).hom
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit (P.ι ⋙ X)).inv
  have : IsCofibrant (colimit (P.ι.op ⋙ X.op)) := hCP'
  have : IsCofibrant (colimit X.op) :=
    ABCPrecofibrationCategory.cofibrant_target (colimit.pre X.op P.ι.op)
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance

/-- The limit over a closed full subcategory of a Reedy fibrant diagram is fibrant. -/
lemma reedyFibrant_limit_closed_isFibrant_small (P : ObjectProperty D)
    (hP : IsClosedDiagramSubcategory P) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X.op d)] [HasLimit (P.ι ⋙ X)]
    (hX : IsReedyFibrant X) : IsFibrant (limit (P.ι ⋙ X)) := by
  obtain ⟨_, hC⟩ := reedyFibrant_closed_op_colimit_small P hP X hX
  have : IsCofibrant (colimit (P.ι ⋙ X).op) := hC
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit (P.ι ⋙ X)).hom
  exact (isFibrant_iff_isCofibrant_op _).2
    (ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit (P.ι ⋙ X)).hom)

/-- Theorem 9.4.1(2)(c), for closed full subcategories of any small inverse
category. The map is compared with the opposite relative colimit map. -/
theorem reedyFibrant_relativeLimMap_weakEquivalence_small
    (P : ObjectProperty D) (hP : IsClosedDiagramSubcategory P) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X.op d)] [∀ d, HasColimit (latchingDiagram Y.op d)]
    [HasLimit X] [HasLimit Y] [HasLimit (P.ι ⋙ X)] [HasLimit (P.ι ⋙ Y)]
    (hX : IsReedyFibrant X) (hY : IsReedyFibrant Y) (f : X ⟶ Y)
    (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasPullback (limit.pre Y P.ι) (limMap (Functor.whiskerLeft P.ι f))),
      WeakEquivalence (relativeLimMap P.ι f) := by
  obtain ⟨hCX, hXc⟩ := reedyFibrant_closed_op_colimit_small P hP X hX
  obtain ⟨hCY, hYc⟩ := reedyFibrant_closed_op_colimit_small P hP Y hY
  obtain ⟨_, hQX⟩ := OpenDiagramSubcategory.isReedyCofibrant P.op hP.op X.op hX
  obtain ⟨_, hQY⟩ := OpenDiagramSubcategory.isReedyCofibrant P.op hP.op Y.op hY
  obtain ⟨hQCY, hQCX, hQf⟩ := reedyCofibrant_colimMap_weakEquivalence_of_cofibrationCategory hQY hQX
    (Functor.whiskerLeft P.op.ι (NatTrans.op f))
    (fun d ↦ (weakEquivalences_op_iff _).2 (hw d.obj.unop))
  have : HasColimit ((P.opEquivalence).functor ⋙ P.ι.op ⋙ X.op) := hQCX
  have : HasColimit ((P.opEquivalence).functor ⋙ P.ι.op ⋙ Y.op) := hQCY
  have hfi := weakEquivalence_colimMap_of_final (P.opEquivalence).functor
    (Functor.whiskerLeft P.ι.op (NatTrans.op f)) hQf
  have hopen : ∀ {a : Dᵒᵖ} (e : P.FullSubcategoryᵒᵖ), (a ⟶ P.ι.op.obj e) →
      ∃ e', P.ι.op.obj e' = a := by
    intro a e f
    exact ⟨op ⟨a.unop, hP f.unop e.unop.property⟩, rfl⟩
  obtain ⟨_, hpre⟩ := reedyCofibrant_colimit_pre_small
    ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom
    P.ι.op hopen Y.op hY hYc
  have hpo : HasPushout (colimit.pre Y.op P.ι.op)
      (colimMap (Functor.whiskerLeft P.ι.op (NatTrans.op f))) :=
    ABCPrecofibrationCategory.hasPushout _ _
  obtain ⟨_, _, hfull⟩ := reedyCofibrant_colimMap_weakEquivalence_of_cofibrationCategory
    hY hX (NatTrans.op f)
    (fun d ↦ (weakEquivalences_op_iff _).2 (hw d.unop))
  have := ABCPrecofibrationCategory.weakEquivalence_pushout_inl
    (colimit.pre Y.op P.ι.op) (colimMap (Functor.whiskerLeft P.ι.op (NatTrans.op f)))
  have hc : WeakEquivalence (relativeColimMap P.ι.op (NatTrans.op f)) :=
    weakEquivalence_of_precomp_of_fac (inl_relativeColimMap P.ι.op (NatTrans.op f))
  have := reedyFibrant_limit_closed_isFibrant_small P hP X hX
  have := reedyFibrant_limit_closed_isFibrant_small P hP Y hY
  obtain ⟨_, _, hpreY⟩ := reedyFibrant_limit_closed_small P hP Y hY
  have hp : HasPullback (limit.pre Y P.ι) (limMap (Functor.whiskerLeft P.ι f)) :=
    ABCPrefibrationCategory.hasPullback _ _
  refine ⟨hp, (weakEquivalences_op_iff _).1 ?_⟩
  rw [op_relativeLimMap]
  have : HasPushout (colimit.pre Y.op P.ι.op)
      (colimMap (NatTrans.op (Functor.whiskerLeft P.ι f))) := hpo
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso
    (relativeLimitOp_isPushout P.ι f).isoPushout.hom
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance


end ABCCofibrations

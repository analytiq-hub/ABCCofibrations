/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SmallDiagramCategories
public import ABCCofibrations.ReedyColimitInterchange

/-! # Sequential colimits of Reedy cofibrations

The CF6(1) construction in Theorem 9.2.4(1)(a). Latching objects commute
with the individually existing sequential colimits, and the sequential
relative comparison gives the Reedy condition on the initial colimit leg.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] [IsDirect D]
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{w} M]
  (F : ℕ ⥤ D ⥤ M) [∀ n d, HasColimit (latchingDiagram (F.obj n) d)]
  (hf : ∀ n, IsReedyCofibration (F.map (succHom n)))

include hf

private lemma latching_transition (d : D) (n : ℕ) :
    Cofibration ((latchingColimits F d).map (succHom n)) :=
  ((hf n).cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
    ABCCofibrationCategory.sequentialCofibrationAxiom d).1

/-- The required sequential colimits exist at every object. -/
lemma hasColimit_evaluation_of_reedy_sequence (d : D) : HasColimit (F.flip.obj d) := by
  have h0 : IsCofibrant ((F.flip.obj d).obj 0) := (hf 0).1.isCofibrant_obj d
  have hm (n : ℕ) : Cofibration ((F.flip.obj d).map (succHom n)) :=
    ((hf n).cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom d).2
  exact ABCCofibrationCategory.hasSequentialColimit _ h0 hm

variable [∀ d, HasColimit (F.flip.obj d)]

/-- The sequential diagram of latching maps is a Reedy cofibration of sequences. -/
lemma reedy_sequence_latching_data (d : D) :
    ∃ (_ : HasColimit (latchingColimits F d)),
      IsCofibrant (colimit (latchingColimits F d)) ∧ Cofibration (colimMap (latchingMaps F d)) := by
  have h0 : IsCofibrant ((latchingColimits F d).obj 0) := ((hf 0).1 d).1
  have hL := latching_transition F hf d
  have hCol := ABCCofibrationCategory.hasSequentialColimit (latchingColimits F d) h0 hL
  have hLC := isCofibrant_colimit_of_sequence ABCCofibrationCategory.sequentialCofibrationAxiom
    (latchingColimits F d) h0 hL
  have hτ (n : ℕ) : Cofibration ((latchingMaps F d).app n) := ((hf n).1 d).2
  have hk (n : ℕ) : ∃ (Q : M) (l : ((F ⋙ (evaluation D M).obj d).obj n) ⟶ Q)
      (r : (latchingColimits F d).obj (n + 1) ⟶ Q)
      (k : Q ⟶ (F ⋙ (evaluation D M).obj d).obj (n + 1)),
      IsPushout ((latchingMaps F d).app n) ((latchingColimits F d).map (succHom n)) l r ∧
        l ≫ k = (F ⋙ (evaluation D M).obj d).map (succHom n) ∧
        r ≫ k = (latchingMaps F d).app (n + 1) ∧ Cofibration k := (hf n).2.2 d
  exact ⟨hCol, hLC, cofibration_colimMap_of_reedy
    ABCCofibrationCategory.sequentialCofibrationAxiom (latchingMaps F d) h0 hL hτ hk⟩

omit [∀ d, HasColimit (F.flip.obj d)] in
/-- CF6(1): sequential colimits of Reedy cofibrations exist, and the initial
leg is a Reedy cofibration, for arbitrary small direct indexing categories. -/
theorem reedy_sequential_colimit :
    ∃ (_ : HasColimit F) (_ : ∀ d, HasColimit (latchingDiagram (colimit F) d)),
      IsReedyCofibration (colimit.ι F 0) := by
  have hEval : ∀ d, HasColimit (F.flip.obj d) := hasColimit_evaluation_of_reedy_sequence F hf
  have hCol : HasColimit F := inferInstance
  choose hLo hLC hτC using reedy_sequence_latching_data F hf
  have hReedyCol (d : D) := reedy_colimit_at F d (hLC d) (hτC d)
  choose hLatch hY using hReedyCol
  refine ⟨hCol, hLatch, (hf 0).1, hY, fun d ↦ ?_⟩
  have h0L : IsCofibrant ((latchingColimits F d).obj 0) := ((hf 0).1 d).1
  have hL := latching_transition F hf d
  have hτ (n : ℕ) : Cofibration ((latchingMaps F d).app n) := ((hf n).1 d).2
  have hk (n : ℕ) : ∃ (Q : M) (l : ((F ⋙ (evaluation D M).obj d).obj n) ⟶ Q)
      (r : (latchingColimits F d).obj (n + 1) ⟶ Q)
      (k : Q ⟶ (F ⋙ (evaluation D M).obj d).obj (n + 1)),
      IsPushout ((latchingMaps F d).app n) ((latchingColimits F d).map (succHom n)) l r ∧
        l ≫ k = (F ⋙ (evaluation D M).obj d).map (succHom n) ∧
        r ≫ k = (latchingMaps F d).app (n + 1) ∧ Cofibration k := (hf n).2.2 d
  let eL := latchingColimitIso F d
  let eO := preservesColimitIso ((evaluation D M).obj d) F
  have := ((hf 0).1 d).1
  have := ((hf 0).1 d).2
  have := (hY d).1
  have hpo : HasPushout (latchingMap (F.obj 0) d) (latchingObjMap (colimit.ι F 0) d) :=
    hasPushout _ _
  let sq := IsPushout.of_hasPushout (latchingMap (F.obj 0) d)
    (latchingObjMap (colimit.ι F 0) d)
  let c := pushout.desc ((colimit.ι F 0).app d) (latchingMap (colimit F) d)
    (latchingObjMap_latchingMap (colimit.ι F 0) d).symm
  have hs : IsPushout ((latchingMaps F d).app 0) (colimit.ι (latchingColimits F d) 0)
      (pushout.inl (latchingMap (F.obj 0) d) (latchingObjMap (colimit.ι F 0) d))
      (eL.hom ≫ pushout.inr (latchingMap (F.obj 0) d) (latchingObjMap (colimit.ι F 0) d)) := by
    refine sq.of_iso (Iso.refl _) (Iso.refl _) eL.symm (Iso.refl _) (by simp; rfl) ?_
      (by simp) (by simp)
    simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rw [← ι_latchingColimitIso_hom F d 0, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hcmp : Cofibration (c ≫ eO.hom) := by
    apply cofibration_comparison_colimit_of_reedy ABCCofibrationCategory.sequentialCofibrationAxiom
      (latchingMaps F d) h0L hL hτ hk hs
    · rw [← Category.assoc, pushout.inl_desc]
      exact ι_preservesColimitIso_hom ((evaluation D M).obj d) F 0
    · rw [Category.assoc, ← Category.assoc _ c, pushout.inr_desc]
      exact latchingColimitIso_hom_latchingMap F d
  have := cofibration_of_isPushout sq
  have := cofibrant_target (pushout.inr (latchingMap (F.obj 0) d)
    (latchingObjMap (colimit.ι F 0) d))
  have := hLC d
  have := hτC d
  have := cofibrant_target (colimMap (latchingMaps F d))
  have := cofibration_of_isIso eO.inv
  have hc : Cofibration c := by
    rw [show c = (c ≫ eO.hom) ≫ eO.inv by simp]
    infer_instance
  exact ⟨_, _, _, c, sq, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _, hc⟩

omit hf

namespace ReedyDiagram

/-- CF6(1) for the Reedy diagram structure. -/
theorem sequentialCofibrationAxiom_small : SequentialCofibrationAxiom (ReedyDiagram D M) where
  hasColimit G _ hg := by
    have h (n : ℕ) := (cofibration_iff (G.map (succHom n))).1 (hg n)
    choose hLX hLY hR using h
    exact (reedy_sequential_colimit (show ℕ ⥤ D ⥤ M from G) hR).choose
  cofibration G _ hg _ := by
    have h (n : ℕ) := (cofibration_iff (G.map (succHom n))).1 (hg n)
    choose hLX hLY hR using h
    obtain ⟨_, hLatch, hLeg⟩ := reedy_sequential_colimit (show ℕ ⥤ D ⥤ M from G) hR
    exact ⟨⟨hLX 0, hLatch, hLeg⟩⟩

/-- CF6(2) for the Reedy diagram structure, checked pointwise. -/
theorem trivialSequentialAxiom_small : TrivialSequentialAxiom (ReedyDiagram D M) := by
  intro G h0 hg hw _
  have h (n : ℕ) := (cofibration_iff (G.map (succHom n))).1 (hg n)
  choose hLX hLY hR using h
  have hEval : ∀ d, HasColimit ((show ℕ ⥤ D ⥤ M from G).flip.obj d) :=
    hasColimit_evaluation_of_reedy_sequence (show ℕ ⥤ D ⥤ M from G) hR
  refine ⟨fun d ↦ ?_⟩
  let U : ReedyDiagram D M ⥤ M := (evaluation D M).obj d
  have h0d : IsCofibrant ((G ⋙ U).obj 0) := (hR 0).1.isCofibrant_obj d
  have hgd (n : ℕ) : Cofibration ((G ⋙ U).map (succHom n)) :=
    ((hR n).cofibration_app_small ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.sequentialCofibrationAxiom d).2
  have hwd (n : ℕ) : WeakEquivalence ((G ⋙ U).map (succHom n)) := (hw n).mem d
  have : PreservesColimit G U :=
    evaluation_preservesColimit (show ℕ ⥤ D ⥤ M from G) d
  have := ABCCofibrationCategory.sequential_weakEquivalence (G ⋙ U) h0d hgd hwd
  have := weakEquivalence_of_isIso (preservesColimitIso U G).inv
  change WeakEquivalence (U.map (colimit.ι G 0))
  rw [← ι_preservesColimitIso_inv]
  infer_instance

end ReedyDiagram

end ABCCofibrations

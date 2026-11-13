/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SequentialColimits
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Cofibrations from every stage of a sequential colimit -/

@[expose] public section
universe v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations.ABCPrecofibrationCategory

/-- CF6 gives a cofibration from any stage of the sequence, by passing to
its final tail. -/
theorem cofibration_colimit_ι_of_sequence {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
    [ABCPrecofibrationCategory C] (h6 : SequentialCofibrationAxiom C)
    (F : ℕ ⥤ C) (h0 : IsCofibrant (F.obj 0))
    (hf : ∀ n, Cofibration (F.map (succHom n))) [HasColimit F] (n : ℕ) :
    Cofibration (colimit.ι F n) := by
  let hm : Monotone (fun k : ℕ ↦ n + k) := fun _ _ h ↦ Nat.add_le_add_left h n
  let T : ℕ ⥤ ℕ := hm.functor
  have : T.Final := (Monotone.final_functor_iff hm).2
    (fun k ↦ ⟨k, Nat.le_add_left _ _⟩)
  have hT0 : IsCofibrant ((T ⋙ F).obj 0) := by
    simpa [T] using isCofibrant_obj_of_sequence F h0 hf n
  have hTf (k : ℕ) : Cofibration ((T ⋙ F).map (succHom k)) := by
    change Cofibration (F.map (homOfLE (Nat.add_le_add_left (Nat.le_succ k) n)))
    convert hf (n + k) using 1
  have := h6.hasColimit (T ⋙ F) hT0 hTf
  have := h6.cofibration (T ⋙ F) hT0 hTf
  have := isCofibrant_colimit_of_sequence h6 (T ⋙ F) hT0 hTf
  have := cofibration_of_isIso (colimit.pre F T)
  rw [show colimit.ι F n = colimit.ι (T ⋙ F) 0 ≫ colimit.pre F T by
    rw [colimit.ι_pre]
    rfl]
  infer_instance

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The relative comparison from any stage pushout to the colimit is a
cofibration for a Reedy cofibration of sequences. The pushout may be any
representative, rather than the chosen categorical pushout. -/
theorem cofibration_comparison_colimit_of_reedy_at (h1 : SequentialCofibrationAxiom C)
    {F G : ℕ ⥤ C} (τ : F ⟶ G)
    (hF0 : IsCofibrant (F.obj 0)) (hF : ∀ n, Cofibration (F.map (succHom n)))
    (hτ : ∀ n, Cofibration (τ.app n))
    (hk : ∀ n, ∃ (P : C) (l : G.obj n ⟶ P) (r : F.obj (n + 1) ⟶ P) (k : P ⟶ G.obj (n + 1)),
      IsPushout (τ.app n) (F.map (succHom n)) l r ∧ l ≫ k = G.map (succHom n) ∧
        r ≫ k = τ.app (n + 1) ∧ Cofibration k)
    [HasColimit F] [HasColimit G] (n : ℕ) {P : C} {l : G.obj n ⟶ P} {r : colimit F ⟶ P}
    (hP : IsPushout (τ.app n) (colimit.ι F n) l r) (c : P ⟶ colimit G)
    (hl : l ≫ c = colimit.ι G n) (hr : r ≫ c = colimMap τ) : Cofibration c := by
  have : ∀ n, IsCofibrant (F.obj n) := isCofibrant_obj_of_sequence F hF0 hF
  have : IsCofibrant (colimit F) := isCofibrant_colimit_of_sequence h1 F hF0 hF
  have : ∀ n, Cofibration (τ.app n) := hτ
  have hs (n : ℕ) : Cofibration ((ReedyStep.seq τ).map (succHom n)) := by
    obtain ⟨Q, l, r, k, hQ, hl, hr, hc⟩ := hk n
    rw [ReedyStep.seq_map_succ]
    exact ReedyStep.map_cofibration τ n hQ k hl hr
  have h0 : IsCofibrant ((ReedyStep.seq τ).obj 0) := ReedyStep.isCofibrant_obj τ 0
  have := h1.hasColimit (ReedyStep.seq τ) h0 hs
  have : Cofibration (ReedyStep.ι' τ n) :=
    cofibration_colimit_ι_of_sequence h1 (ReedyStep.seq τ) h0 hs n
  have := isCofibrant_colimit_of_sequence h1 (ReedyStep.seq τ) h0 hs
  have := cofibration_of_isIso (inv (ReedyStep.φ τ))
  let he : P ≅ ReedyStep.obj τ n := hP.isoPushout
  have hPC : IsCofibrant P := by
    have := cofibration_of_isPushout hP
    exact cofibrant_target r
  have := cofibration_of_isIso he.hom
  rw [show c = he.hom ≫ ReedyStep.ι' τ n ≫ inv (ReedyStep.φ τ) by
    apply hP.hom_ext
    · rw [hl, ← Category.assoc, show l ≫ he.hom = ReedyStep.inl τ n from hP.inl_isoPushout_hom]
      rw [← ReedyStep.ι_φ_assoc, IsIso.hom_inv_id, Category.comp_id]
    · rw [hr, ← Category.assoc, show r ≫ he.hom = ReedyStep.inr τ n from hP.inr_isoPushout_hom]
      rw [← Category.assoc, ReedyStep.inr_ι τ n, ← ReedyStep.colimMap_φ, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]]
  infer_instance


end ABCCofibrations.ABCPrecofibrationCategory

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyRelativeDegreeMaps
public import ABCCofibrations.ReedyFactorization

/-!
# Relative cofibration comparisons for arbitrary small direct categories

Theorem 9.4.1(1)(b), using CF5(1) and CF6(1). The old open subcategory is
collapsed to degree zero; relative comparisons are reconstructed from the
sequence of whole-layer attachments.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
universe w z v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] [IsDirect D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

/-- Theorem 9.4.1(1)(b), with no finiteness restriction on the open subcategory
or its complement. The colimits exist by part (a). -/
theorem reedyCofibration_relativeColimMap_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [HasColimit X] [HasColimit Y] [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)]
    (f : X ⟶ Y) (hf : IsReedyCofibration f) :
    ∃ (_ : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f))),
      Cofibration (relativeColimMap P.ι f) := by
  classical
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  let δ : D → ℕ := fun d ↦ if P d then 0 else deg d + 1
  have hmono : ∀ {a b : D}, (a ⟶ b) → δ a ≤ δ b := by
    intro a b g
    by_cases ha : P a
    · simp [δ, ha]
    · have hb : ¬ P b := fun hb ↦ ha (hP g hb)
      simp only [δ, ite_eq_right ha, ite_eq_right hb]
      rcases hdeg g with h | ⟨h, _⟩
      · omega
      · simp [h]
  have hstrict : ∀ {a b : D} (g : a ⟶ b),
      δ a < δ b ∨ δ a = 0 ∨ ∃ h : a = b, g = eqToHom h := by
    intro a b g
    by_cases ha : P a
    · exact Or.inr (Or.inl (by simp [δ, ha]))
    · have hb : ¬ P b := fun hb ↦ ha (hP g hb)
      rcases hdeg g with h | h
      · exact Or.inl (by simpa [δ, ha, hb] using h)
      · exact Or.inr (Or.inr h)
  obtain ⟨hColX, hCofX, hMapX⟩ := reedyCofibrant_monotone_degree_data δ hmono h5 h6 X hf.1
  obtain ⟨hColY, hCofY, hMapY⟩ := reedyCofibrant_monotone_degree_data δ hmono h5 h6 Y hf.2.1
  let τ := degreeColimitsMap δ f
  let F := degreeColimits δ X
  let G := degreeColimits δ Y
  have hτ (n : ℕ) : Cofibration (τ.app n) := by
    obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration (degreeBelow δ n)
      (degreeBelow_isOpen δ hmono n) hf
    obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_small h5 h6
      (Functor.whiskerLeft (degreeBelow δ n).ι f) hR
    exact hc
  have h0X : IsCofibrant (F.obj 0) := hCofX 0
  have h0Y : IsCofibrant (G.obj 0) := hCofY 0
  have : HasColimit F := h6.hasColimit F h0X hMapX
  have : HasColimit G := h6.hasColimit G h0Y hMapY
  have := isCofibrant_colimit_of_sequence h6 F h0X hMapX
  have := isCofibrant_colimit_of_sequence h6 G h0Y hMapY
  let eX : colimit F ≅ colimit X := degreeColimitIso δ X hmono
  let eY : colimit G ≅ colimit Y := degreeColimitIso δ Y hmono
  let I : P.FullSubcategory ⥤ (degreeBelow δ 1).FullSubcategory :=
    (degreeBelow δ 1).lift P.ι (fun e ↦ by change δ e.obj < 1; simp [δ, e.property])
  have : I.Full := by dsimp [I]; infer_instance
  have : I.Faithful := by dsimp [I]; infer_instance
  have : I.EssSurj := ⟨fun e ↦ by
    have hp : P e.obj := by
      by_contra hp
      have he : δ e.obj < 1 := e.property
      simp [δ, hp] at he
    exact ⟨⟨e.obj, hp⟩, ⟨Iso.refl _⟩⟩⟩
  have : I.IsEquivalence := { }
  have : I.Final := Functor.final_of_isRightAdjoint I
  have : HasColimit (I ⋙ (degreeBelow δ 1).ι ⋙ X) := ‹HasColimit (P.ι ⋙ X)›
  have : HasColimit (I ⋙ (degreeBelow δ 1).ι ⋙ Y) := ‹HasColimit (P.ι ⋙ Y)›
  obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration P hP hf
  obtain ⟨_, hPCX⟩ := reedyCofibrant_colimit_small h5 h6 (P.ι ⋙ X) hR.1
  obtain ⟨_, hPCY⟩ := reedyCofibrant_colimit_small h5 h6 (P.ι ⋙ Y) hR.2.1
  obtain ⟨_, _, hpre⟩ := reedyCofibrant_colimit_open_small h5 h6 P hP X hf.1
  have hpo : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f)) :=
    hasPushout _ _
  refine ⟨hpo, ?_⟩
  let c := relativeColimMap P.ι f
  let B := degreeBelow δ 1
  obtain ⟨r, hs, hr⟩ := transfer_comparison_rev I (Functor.whiskerLeft B.ι f)
    ((colimit.cocone X).whisker B.ι) ((colimit.cocone Y).whisker B.ι)
    (IsPushout.of_hasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f)))
    (inr_relativeColimMap P.ι f)
  have hdescX : colimit.desc (B.ι ⋙ X) ((colimit.cocone X).whisker B.ι) =
      colimit.pre X B.ι := by
    apply colimit.hom_ext
    intro d
    simp
  rw [hdescX] at hs
  have hfacX : colimit.pre X B.ι ≫ eX.inv = colimit.ι F 1 := by
    erw [Iso.comp_inv_eq]
    apply colimit.hom_ext
    intro d
    rw [colimit.ι_pre]
    exact (ι_degreeColimitIso_hom δ X hmono 1 d).symm
  have hfacY : colimit.pre Y B.ι ≫ eY.inv = colimit.ι G 1 := by
    erw [Iso.comp_inv_eq]
    apply colimit.hom_ext
    intro d
    rw [colimit.ι_pre]
    exact (ι_degreeColimitIso_hom δ Y hmono 1 d).symm
  have hs' : IsPushout (τ.app 1) (colimit.ι F 1) r
      (eX.hom ≫ pushout.inl (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f))) := by
    exact hs.flip.of_iso (Iso.refl _) (Iso.refl _) eX.symm (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)
      (by simpa only [Iso.symm_hom, Iso.refl_hom, Category.id_comp] using hfacX)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) (by simp)
  have hc : Cofibration (c ≫ eY.inv) :=
    cofibration_comparison_colimit_of_reedy_at h6 τ h0X hMapX hτ
      (reedyCofibration_monotone_degree_steps δ hmono hstrict h5 h6 f hf) 1 hs'
      (c ≫ eY.inv) (by
        change r ≫ relativeColimMap P.ι f ≫ eY.inv = _
        erw [← Category.assoc, hr]
        exact hfacY) (by
        rw [Category.assoc, inl_relativeColimMap_assoc]
        rw [← Category.assoc]
        erw [Iso.comp_inv_eq]
        exact (degreeColimitIso_naturality δ hmono f).symm)
  have := cofibration_of_isIso eY.hom
  change Cofibration c
  rw [show c = (c ≫ eY.inv) ≫ eY.hom by simp]
  exact ⟨(cofibrations M).comp_mem _ _ hc.mem (Cofibration.mem (f := eY.hom))⟩

/-- Relative cofibration comparison for an arbitrary fully faithful open
presentation, used in particular by the opposite-category adapter. -/
theorem reedyCofibration_relativeColimMap_of_open_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    {E : Type z} [SmallCategory E] (i : E ⥤ D) [i.Full] [i.Faithful]
    (hopen : ∀ {a : D} (e : E), (a ⟶ i.obj e) → ∃ e', i.obj e' = a)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] [HasColimit X] [HasColimit Y]
    [HasColimit (i ⋙ X)] [HasColimit (i ⋙ Y)] (f : X ⟶ Y) (hf : IsReedyCofibration f)
    (hCX : IsCofibrant (colimit (i ⋙ X))) (hCY : IsCofibrant (colimit (i ⋙ Y))) :
    ∃ (_ : HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f))),
      Cofibration (relativeColimMap i f) := by
  let P : ObjectProperty D := fun d ↦ ∃ e, i.obj e = d
  have hP : IsOpenDiagramSubcategory P := by
    intro a b g hb
    obtain ⟨e, he⟩ := hb
    exact hopen e (g ≫ eqToHom he.symm)
  let Q : E ⥤ P.FullSubcategory := P.lift i (fun e ↦ ⟨e, rfl⟩)
  have : Q.Full := by dsimp [Q]; infer_instance
  have : Q.Faithful := by dsimp [Q]; infer_instance
  have : Q.EssSurj := ⟨fun d ↦ by
    obtain ⟨e, he⟩ := d.property
    exact ⟨e, ⟨eqToIso (ObjectProperty.FullSubcategory.ext he)⟩⟩⟩
  have : Q.IsEquivalence := { }
  have : Q.Final := Functor.final_of_isRightAdjoint Q
  obtain ⟨_, _, _⟩ := reedyCofibrant_colimit_open_small h5 h6 P hP X hf.1
  obtain ⟨_, _, _⟩ := reedyCofibrant_colimit_open_small h5 h6 P hP Y hf.2.1
  have : HasColimit (Q ⋙ P.ι ⋙ X) := ‹HasColimit (i ⋙ X)›
  have : HasColimit (Q ⋙ P.ι ⋙ Y) := ‹HasColimit (i ⋙ Y)›
  obtain ⟨_, hc⟩ := reedyCofibration_relativeColimMap_small h5 h6 P hP f hf
  obtain ⟨r, hs, hr⟩ := transfer_comparison Q (Functor.whiskerLeft P.ι f)
    ((colimit.cocone X).whisker P.ι) ((colimit.cocone Y).whisker P.ι)
    (IsPushout.of_hasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f)))
    (inr_relativeColimMap P.ι f)
  obtain ⟨_, hpre⟩ := reedyCofibrant_colimit_pre_small h5 h6 i hopen X hf.1 hCX
  have hpo : HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)) :=
    hasPushout _ _
  have := cofibration_of_isPushout (IsPushout.of_hasPushout
    (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)))
  have := cofibrant_target (pushout.inr (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)))
  have hdesc : colimit.desc (Q ⋙ P.ι ⋙ X)
      (((colimit.cocone X).whisker P.ι).whisker Q) = colimit.pre X i := by
    apply colimit.hom_ext
    intro e
    erw [colimit.ι_desc]
  rw [hdesc] at hs
  change IsPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)) _ _ at hs
  have := cofibration_of_isIso hs.isoPushout.inv
  refine ⟨hpo, ?_⟩
  rw [show relativeColimMap i f = hs.isoPushout.inv ≫ relativeColimMap P.ι f by
    apply pushout.hom_ext
    · rw [inl_relativeColimMap, hs.inl_isoPushout_inv_assoc, inl_relativeColimMap]
    · rw [inr_relativeColimMap, hs.inr_isoPushout_inv_assoc, hr]
      rfl]
  infer_instance

end ABCCofibrations

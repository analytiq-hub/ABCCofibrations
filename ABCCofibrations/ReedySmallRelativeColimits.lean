/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyRelativeBounded
public import ABCCofibrations.SequenceTails

/-!
# Relative colimits over arbitrary small direct categories

Theorem 9.4.1(1)(a). Collapse the open subcategory to degree zero and filter
the remaining objects by their original degrees. The collapsed degree is
monotone, which suffices for the categorical colimit reconstruction.
-/

@[expose] public section
universe w z v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] [IsDirect D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M]

/-- Theorem 9.4.1(1)(a) with no finiteness restrictions on the open subcategory
or the ambient indexing category. -/
theorem reedyCofibrant_colimit_open_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit (P.ι ⋙ X)) (_ : HasColimit X), Cofibration (colimit.pre X P.ι) := by
  classical
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  let δ : D → ℕ := fun d ↦ if P d then 0 else deg d + 1
  have hmono : ∀ {a b : D}, (a ⟶ b) → δ a ≤ δ b := by
    intro a b f
    by_cases ha : P a
    · simp [δ, ha]
    · have hb : ¬ P b := fun hb ↦ ha (hP f hb)
      simp only [δ, ite_eq_right ha, ite_eq_right hb]
      rcases hdeg f with h | ⟨h, _⟩
      · omega
      · simp [h]
  obtain ⟨_, hPX⟩ := OpenDiagramSubcategory.isReedyCofibrant P hP X hX
  obtain ⟨hPC, hPcof⟩ := reedyCofibrant_colimit_small h5 h6 (P.ι ⋙ X) hPX
  have hStages (n : ℕ) : ∃ (_ : HasColimit ((degreeBelow δ n).ι ⋙ X)),
      IsCofibrant (colimit ((degreeBelow δ n).ι ⋙ X)) := by
    obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow δ n)
      (degreeBelow_isOpen δ hmono n) X hX
    exact reedyCofibrant_colimit_small h5 h6 _ hR
  choose hCol hCof using hStages
  have hMap (n : ℕ) : Cofibration ((degreeColimits δ X).map (succHom n)) := by
    cases n with
    | zero =>
      have : IsEmpty (degreeBelow δ 0).FullSubcategory :=
        ⟨fun d ↦ Nat.not_lt_zero _ d.property⟩
      have hI : IsInitial (colimit ((degreeBelow δ 0).ι ⋙ X)) :=
        (isColimitEquivIsInitialOfIsEmpty _ _).1 (colimit.isColimit _)
      rw [show (degreeColimits δ X).map (succHom 0) = hI.to _ from hI.hom_ext _ _]
      exact (isCofibrant_iff_of_isInitial hI _).1 (hCof 1)
    | succ n =>
      let R := degreeBelow δ (n + 1 + 1)
      let i := degreeInclusion δ (Nat.le_succ (n + 1))
      have : i.Full := ObjectProperty.full_ιOfLE
        (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ (n + 1)))
      have : i.Faithful := ObjectProperty.faithful_ιOfLE
        (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ (n + 1)))
      have hopen : ∀ {a : R.FullSubcategory} (e : (degreeBelow δ (n + 1)).FullSubcategory),
          (a ⟶ i.obj e) → ∃ e', i.obj e' = a := by
        intro a e f
        exact ⟨⟨a.obj, lt_of_le_of_lt (hmono f.hom) e.property⟩,
          ObjectProperty.FullSubcategory.ext rfl⟩
      have hb (d : R.FullSubcategory) (hd : ∀ e, i.obj e ≠ d) : deg d.obj < n + 2 := by
        have hnot : ¬ P d.obj := by
          intro hp
          have hm : δ d.obj < n + 1 := by simp [δ, hp]
          exact hd ⟨d.obj, hm⟩ (ObjectProperty.FullSubcategory.ext rfl)
        have hh : δ d.obj < n + 1 + 1 := d.property
        simp only [δ, ite_eq_right hnot] at hh
        omega
      obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant R
        (degreeBelow_isOpen δ hmono _) X hX
      have : HasColimit (i ⋙ R.ι ⋙ X) := hCol (n + 1)
      have hOld : IsCofibrant (colimit (i ⋙ R.ι ⋙ X)) := hCof (n + 1)
      obtain ⟨_, hc⟩ := reedyCofibrant_colimit_pre_bounded_outside h5 (n + 2)
        R.FullSubcategory (fun e ↦ deg e.obj) (degreeCondition_fullSubcategory R deg hdeg)
        (degreeBelow δ (n + 1)).FullSubcategory i hopen hb (R.ι ⋙ X) hR hOld
      exact hc
  have h0 : IsCofibrant ((degreeColimits δ X).obj 0) := hCof 0
  have := h6.hasColimit (degreeColimits δ X) h0 hMap
  have hCX : HasColimit X := hasColimit_of_degreeColimits δ X hmono
  refine ⟨hPC, hCX, ?_⟩
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
  have : HasColimit (I ⋙ (degreeBelow δ 1).ι ⋙ X) := hPC
  have : IsCofibrant (colimit (I ⋙ (degreeBelow δ 1).ι ⋙ X)) := hPcof
  have := cofibration_of_isIso (colimit.pre ((degreeBelow δ 1).ι ⋙ X) I)
  have : IsCofibrant ((degreeColimits δ X).obj 1) := hCof 1
  have := cofibration_colimit_ι_of_sequence h6 (degreeColimits δ X) h0 hMap 1
  have := isCofibrant_colimit_of_sequence h6 (degreeColimits δ X) h0 hMap
  let e := degreeColimitIso δ X hmono
  have := cofibration_of_isIso e.hom
  have ht : Cofibration (colimit.ι (degreeColimits δ X) 1 ≫ e.hom) := by infer_instance
  have hp : Cofibration (colimit.pre ((degreeBelow δ 1).ι ⋙ X) I) := by infer_instance
  rw [show colimit.pre X P.ι = colimit.pre ((degreeBelow δ 1).ι ⋙ X) I ≫
      colimit.ι (degreeColimits δ X) 1 ≫ e.hom by
    apply colimit.hom_ext
    intro d
    rw [colimit.ι_pre]
    change colimit.ι X d.obj = colimit.ι (I ⋙ (degreeBelow δ 1).ι ⋙ X) d ≫ _
    rw [colimit.ι_pre_assoc, ι_degreeColimitIso_hom]
    rfl]
  exact ⟨(cofibrations M).comp_mem _ _ hp.mem ht.mem⟩

/-- The arbitrary small relative theorem for a fully faithful open functor.
This includes presentations of a full subcategory by an equivalent category. -/
theorem reedyCofibrant_colimit_pre_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    {E : Type z} [SmallCategory E] (i : E ⥤ D) [i.Full] [i.Faithful]
    (hopen : ∀ {a : D} (e : E), (a ⟶ i.obj e) → ∃ e', i.obj e' = a)
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] [HasColimit (i ⋙ X)]
    (hX : IsReedyCofibrant X) (hC : IsCofibrant (colimit (i ⋙ X))) :
    ∃ (_ : HasColimit X), Cofibration (colimit.pre X i) := by
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
  obtain ⟨_, hCol, hpre⟩ := reedyCofibrant_colimit_open_small h5 h6 P hP X hX
  have : HasColimit (Q ⋙ P.ι ⋙ X) := ‹HasColimit (i ⋙ X)›
  have : IsCofibrant (colimit (Q ⋙ P.ι ⋙ X)) := hC
  have := cofibration_of_isIso (colimit.pre (P.ι ⋙ X) Q)
  refine ⟨hCol, ?_⟩
  rw [show colimit.pre X i = colimit.pre (P.ι ⋙ X) Q ≫ colimit.pre X P.ι by
    apply colimit.hom_ext
    intro e
    rw [colimit.ι_pre]
    change colimit.ι X (i.obj e) = colimit.ι (Q ⋙ P.ι ⋙ X) e ≫ _
    rw [colimit.ι_pre_assoc, colimit.ι_pre]
    rfl]
  infer_instance

/-- Theorem 9.4.1(1)(c) for an arbitrary open full subcategory. -/
theorem reedyCofibrant_relativeColimMap_weakEquivalence_small
    (h5 : CoproductCofibrationAxiom.{w} M) (h5t : TrivialCoproductAxiom.{w} M)
    (h6 : SequentialCofibrationAxiom M) (h6t : TrivialSequentialAxiom M)
    (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [HasColimit X] [HasColimit Y] [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f))),
      WeakEquivalence (relativeColimMap P.ι f) := by
  obtain ⟨_, hPX⟩ := OpenDiagramSubcategory.isReedyCofibrant P hP X hX
  obtain ⟨_, hPY⟩ := OpenDiagramSubcategory.isReedyCofibrant P hP Y hY
  obtain ⟨_, hCX⟩ := reedyCofibrant_colimit_small h5 h6 (P.ι ⋙ X) hPX
  obtain ⟨_, hCY⟩ := reedyCofibrant_colimit_small h5 h6 (P.ι ⋙ Y) hPY
  obtain ⟨_, _, hi⟩ := reedyCofibrant_colimit_open_small h5 h6 P hP X hX
  obtain ⟨_, _, hPf⟩ := reedyCofibrant_colimMap_weakEquivalence_small h5 h5t h6 h6t hPX hPY
    (Functor.whiskerLeft P.ι f) (fun d ↦ hw d.obj)
  obtain ⟨_, _, hF⟩ := reedyCofibrant_colimMap_weakEquivalence_small h5 h5t h6 h6t hX hY f hw
  have hpo : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f)) :=
    hasPushout _ _
  refine ⟨hpo, ?_⟩
  have := weakEquivalence_pushout_inl (colimit.pre X P.ι)
    (colimMap (Functor.whiskerLeft P.ι f))
  exact weakEquivalence_of_precomp_of_fac (inl_relativeColimMap P.ι f)


end ABCCofibrations

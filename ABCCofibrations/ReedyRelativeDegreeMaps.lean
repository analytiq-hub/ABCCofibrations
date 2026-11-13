/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedySmallRelativeColimits

/-! # Relative comparisons for a degree with an initial zero layer

The degree may be constant on the old open subcategory. Positive layers
still consist of maximal objects in each truncation.
-/

@[expose] public section
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]
open ABCPrecofibrationCategory

/-- Colimit sequences for any monotone degree, including a collapsed open
zero layer. Directness is supplied independently of this degree. -/
theorem reedyCofibrant_monotone_degree_data {D : Type w} [SmallCategory D] [IsDirect D]
    (deg : D → ℕ) (hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b)
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)),
      (∀ n, IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X))) ∧
      ∀ n, Cofibration ((degreeColimits deg X).map (succHom n)) := by
  have hStages (n : ℕ) : ∃ (_ : HasColimit ((degreeBelow deg n).ι ⋙ X)),
      IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X)) := by
    obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) X hX
    exact reedyCofibrant_colimit_small h5 h6 _ hR
  choose hCol hCof using hStages
  refine ⟨hCol, hCof, fun n ↦ ?_⟩
  let R := degreeBelow deg (n + 1)
  let i := degreeInclusion deg (Nat.le_succ n)
  have : i.Full := ObjectProperty.full_ιOfLE
    (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ n))
  have : i.Faithful := ObjectProperty.faithful_ιOfLE
    (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ n))
  have hopen : ∀ {a : R.FullSubcategory} (e : (degreeBelow deg n).FullSubcategory),
      (a ⟶ i.obj e) → ∃ e', i.obj e' = a := by
    intro a e f
    exact ⟨⟨a.obj, lt_of_le_of_lt (hmono f.hom) e.property⟩,
      ObjectProperty.FullSubcategory.ext rfl⟩
  obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant R
    (degreeBelow_isOpen deg hmono _) X hX
  have : HasColimit (i ⋙ R.ι ⋙ X) := hCol n
  have hOld : IsCofibrant (colimit (i ⋙ R.ι ⋙ X)) := hCof n
  obtain ⟨_, hc⟩ := reedyCofibrant_colimit_pre_small h5 h6 i hopen (R.ι ⋙ X) hR hOld
  exact hc

/-- The relative comparison between two successive degree stages is a
cofibration. No finiteness condition is needed on either stage. -/
theorem reedyCofibration_monotone_degree_step_pos {D : Type w} [SmallCategory D] [IsDirect D]
    (deg : D → ℕ)
    (hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b)
    (hstrict : ∀ {a b : D} (f : a ⟶ b),
      deg a < deg b ∨ deg a = 0 ∨ ∃ h : a = b, f = eqToHom h)
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)]
    [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ Y)]
    (f : X ⟶ Y) (hf : IsReedyCofibration f) (n : ℕ) (hn : 0 < n) :
    ∃ (A : M) (l : (degreeColimits deg Y).obj n ⟶ A)
      (r : (degreeColimits deg X).obj (n + 1) ⟶ A)
      (c : A ⟶ (degreeColimits deg Y).obj (n + 1)),
      IsPushout ((degreeColimitsMap deg f).app n) ((degreeColimits deg X).map (succHom n)) l r ∧
        l ≫ c = (degreeColimits deg Y).map (succHom n) ∧
        r ≫ c = (degreeColimitsMap deg f).app (n + 1) ∧ Cofibration c := by
  let R := degreeBelow deg (n + 1)
  let Q : ObjectProperty R.FullSubcategory := fun e ↦ deg e.obj < n
  let U := R.ι ⋙ X
  let V := R.ι ⋙ Y
  let g := Functor.whiskerLeft R.ι f
  obtain ⟨_, _, hg⟩ := OpenDiagramSubcategory.isReedyCofibration R
    (degreeBelow_isOpen deg hmono (n + 1)) hf
  have hQopen : IsOpenDiagramSubcategory Q := by
    intro a b hab hb
    exact lt_of_le_of_lt (hmono hab.hom) hb
  obtain ⟨_, _, hq⟩ := OpenDiagramSubcategory.isReedyCofibration Q hQopen hg
  obtain ⟨_, hQU⟩ := reedyCofibrant_colimit_small h5 h6 (Q.ι ⋙ U) hq.1
  obtain ⟨_, hQV⟩ := reedyCofibrant_colimit_small h5 h6 (Q.ι ⋙ V) hq.2.1
  obtain ⟨_, _, hOld⟩ := reedyCofibration_colimMap_small h5 h6
    (Functor.whiskerLeft Q.ι g) hq
  have hmax : ∀ (d : R.FullSubcategory), ¬ Q d → ∀ e (a : d ⟶ e),
      ∃ h : d = e, a = eqToHom h := by
    intro d hd e a
    rcases hstrict a.hom with h | hz | ⟨he, ha⟩
    · have hd' : ¬ deg d.obj < n := hd
      have he : deg e.obj < n + 1 := e.property
      omega
    · have hd' : ¬ deg d.obj < n := hd
      omega
    · exact ⟨ObjectProperty.FullSubcategory.ext he,
        InducedCategory.hom_ext (by simpa using ha)⟩
  have hLf (d : ReedyLayer.Objects Q) : Cofibration (latchingObjMap g d.val) := by
    obtain ⟨orig, horig⟩ := IsDirect.exists_deg (D := R.FullSubcategory)
    obtain ⟨_, _, hL⟩ := isReedyCofibration_latching orig horig (d := d.val) hg
    have : IsDirect (LatchingCategory d.val) :=
      ⟨⟨_, hdeg_latching orig horig d.val⟩⟩
    obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_small h5 h6 (latchingNat g d.val) hL
    exact hc
  have : ∀ d : ReedyLayer.Objects Q, HasColimit (latchingDiagram U d.val) :=
    fun _ ↦ inferInstance
  have : ∀ d : ReedyLayer.Objects Q, HasColimit (latchingDiagram V d.val) :=
    fun _ ↦ inferInstance
  obtain ⟨hpo, _, hc⟩ := ReedyLayer.cofibration_step Q hmax g h5 hg hQU hQV hLf hOld
  have := hpo
  let I : (degreeBelow deg n).FullSubcategory ⥤ Q.FullSubcategory :=
    { obj := fun e ↦ ⟨⟨e.obj, lt_of_lt_of_le e.property (Nat.le_succ n)⟩, e.property⟩
      map := fun a ↦ ⟨⟨a.hom⟩⟩ }
  have : I.Full := ⟨fun a ↦ ⟨⟨a.hom.hom⟩, rfl⟩⟩
  have : I.Faithful := by
    constructor
    intro a b f g h
    cases f
    cases g
    cases h
    rfl
  have : I.EssSurj := ⟨fun e ↦ ⟨⟨e.obj.obj, e.property⟩, ⟨Iso.refl _⟩⟩⟩
  have : I.IsEquivalence := { }
  have : I.Final := Functor.final_of_isRightAdjoint I
  have : HasColimit (I ⋙ Q.ι ⋙ U) := inferInstanceAs
    (HasColimit ((degreeBelow deg n).ι ⋙ X))
  have : HasColimit (I ⋙ Q.ι ⋙ V) := inferInstanceAs
    (HasColimit ((degreeBelow deg n).ι ⋙ Y))
  obtain ⟨r, hs, hr⟩ := transfer_comparison I (Functor.whiskerLeft Q.ι g)
    ((colimit.cocone U).whisker Q.ι) ((colimit.cocone V).whisker Q.ι)
    (IsPushout.of_hasPushout (colimit.pre U Q.ι) (colimMap (Functor.whiskerLeft Q.ι g)))
    (inr_relativeColimMap Q.ι g)
  exact ⟨_, r, pushout.inl (colimit.pre U Q.ι)
    (colimMap (Functor.whiskerLeft Q.ι g)), relativeColimMap Q.ι g, hs.flip, hr,
    inl_relativeColimMap Q.ι g, hc⟩


/-- All the relative transition comparisons, including the empty initial
truncation, are cofibrations. -/
theorem reedyCofibration_monotone_degree_steps {D : Type w} [SmallCategory D] [IsDirect D]
    (deg : D → ℕ) (hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b)
    (hstrict : ∀ {a b : D} (f : a ⟶ b),
      deg a < deg b ∨ deg a = 0 ∨ ∃ h : a = b, f = eqToHom h)
    (h5 : CoproductCofibrationAxiom.{w} M) (h6 : SequentialCofibrationAxiom M)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)]
    [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)]
    [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ Y)]
    (f : X ⟶ Y) (hf : IsReedyCofibration f) (n : ℕ) :
    ∃ (A : M) (l : (degreeColimits deg Y).obj n ⟶ A)
      (r : (degreeColimits deg X).obj (n + 1) ⟶ A)
      (c : A ⟶ (degreeColimits deg Y).obj (n + 1)),
      IsPushout ((degreeColimitsMap deg f).app n) ((degreeColimits deg X).map (succHom n)) l r ∧
        l ≫ c = (degreeColimits deg Y).map (succHom n) ∧
        r ≫ c = (degreeColimitsMap deg f).app (n + 1) ∧ Cofibration c := by
  cases n with
  | succ n =>
    exact reedyCofibration_monotone_degree_step_pos deg hmono hstrict h5 h6
      f hf (n + 1) (Nat.zero_lt_succ n)
  | zero =>
    let τ := degreeColimitsMap deg f
    let F := degreeColimits deg X
    let G := degreeColimits deg Y
    have hτ (n : ℕ) : Cofibration (τ.app n) := by
      obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration (degreeBelow deg n)
        (degreeBelow_isOpen deg hmono n) hf
      obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_small h5 h6
        (Functor.whiskerLeft (degreeBelow deg n).ι f) hR
      exact hc
    have hFC (n : ℕ) : IsCofibrant (F.obj n) := by
      obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
        (degreeBelow_isOpen deg hmono n) X hf.1
      exact (reedyCofibrant_colimit_small h5 h6 _ hR).choose_spec
    have : IsEmpty (degreeBelow deg 0).FullSubcategory :=
      ⟨fun d ↦ Nat.not_lt_zero _ d.property⟩
    have : IsIso (τ.app 0) := isIso_colimMap_of_isEmpty _
    have := hτ 0
    have := hFC 0
    have := hFC 1
    have : HasPushout (τ.app 0) (F.map (succHom 0)) := hasPushout _ _
    let sq := IsPushout.of_hasPushout (τ.app 0) (F.map (succHom 0))
    let c := sq.desc (G.map (succHom 0)) (τ.app 1) (τ.naturality _).symm
    have := cofibration_of_isPushout sq
    have := cofibrant_target (pushout.inr (τ.app 0) (F.map (succHom 0)))
    have := cofibration_of_isIso (inv (pushout.inr (τ.app 0) (F.map (succHom 0))))
    have hc : Cofibration c := by
      rw [show c = inv (pushout.inr (τ.app 0) (F.map (succHom 0))) ≫ τ.app 1 by
        rw [IsIso.eq_inv_comp]
        exact sq.inr_desc _ _ _]
      have := hτ 1
      infer_instance
    exact ⟨_, _, _, c, sq, sq.inl_desc _ _ _, sq.inr_desc _ _ _, hc⟩

end ABCCofibrations

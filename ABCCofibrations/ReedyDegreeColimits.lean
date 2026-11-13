/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.DegreeColimits
public import ABCCofibrations.ReedyRelativeColimits
public import ABCCofibrations.SequentialColimits

/-!
# Unbounded direct diagrams with finite degree truncations

Theorem 9.3.5(1)(a)–(c) for a possibly infinite direct category whose bounded-degree
full subcategories are finite. The finite relative theorem gives a CF6 sequence
of truncation colimits, and `DegreeColimits.lean` reconstructs the whole colimit.
Parts (a) and (b) use CF1–CF4 and CF6(1); part (c) also uses CF6(2).
The map statements additionally require finite hom-sets. CF5 is not used.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] (deg : D → ℕ)

/-- Bounded-degree full subcategories are open for any degree nondecreasing on arrows. -/
lemma degreeBelow_isOpen (hdeg : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b) (n : ℕ) :
    IsOpenDiagramSubcategory (degreeBelow deg n) :=
  fun f hb ↦ lt_of_le_of_lt (hdeg f) hb

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- Cofibrant truncation colimits form a sequence of cofibrations. -/
theorem reedyCofibrant_degreeColimits_data
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory]
    (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : ∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)),
      (∀ n, IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X))) ∧
        ∀ n, Cofibration ((degreeColimits deg X).map (succHom n)) := by
  have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b f
    rcases hdeg f with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  have hStage (n : ℕ) : ∃ (_ : HasColimit ((degreeBelow deg n).ι ⋙ X)),
      IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X)) := by
    have := Fintype.ofFinite (degreeBelow deg n).FullSubcategory
    obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) X hX
    exact reedyCofibrant_colimit_finite _ (degreeBelow deg n).FullSubcategory rfl _ hR
  let hCol (n : ℕ) : HasColimit ((degreeBelow deg n).ι ⋙ X) := (hStage n).choose
  have hCof (n : ℕ) : IsCofibrant (colimit ((degreeBelow deg n).ι ⋙ X)) := (hStage n).choose_spec
  have hMap (n : ℕ) : Cofibration ((degreeColimits deg X).map (succHom n)) := by
    let i := degreeInclusion deg (Nat.le_succ n)
    have : i.Full := ObjectProperty.full_ιOfLE (P := degreeBelow deg n)
      (P' := degreeBelow deg (n + 1)) (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ n))
    have : i.Faithful := ObjectProperty.faithful_ιOfLE (P := degreeBelow deg n)
      (P' := degreeBelow deg (n + 1)) (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ n))
    have := Fintype.ofFinite (degreeBelow deg (n + 1)).FullSubcategory
    obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg (n + 1))
      (degreeBelow_isOpen deg hmono (n + 1)) X hX
    have : HasColimit (i ⋙ (degreeBelow deg (n + 1)).ι ⋙ X) := hCol n
    have hopen : ∀ {a : (degreeBelow deg (n + 1)).FullSubcategory}
        (e : (degreeBelow deg n).FullSubcategory), (a ⟶ i.obj e) → ∃ e', i.obj e' = a := by
      intro a e f
      refine ⟨⟨a.obj, lt_of_le_of_lt (hmono f.hom) e.property⟩, ?_⟩
      exact ObjectProperty.FullSubcategory.ext rfl
    obtain ⟨_, hc⟩ := reedyCofibrant_colimit_pre_aux _
      (degreeBelow deg (n + 1)).FullSubcategory rfl (degreeBelow deg n).FullSubcategory i
      hopen ((degreeBelow deg (n + 1)).ι ⋙ X) hR (hCof n)
    exact hc
  exact ⟨hCol, hCof, hMap⟩

/-- The colimit theorem for direct diagrams with finite bounded-degree truncations.
No finiteness of hom-sets or CF5 is required. -/
theorem reedyCofibrant_colimit_finite_degree_truncations
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory]
    (h6 : SequentialCofibrationAxiom M) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit X), IsCofibrant (colimit X) := by
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b f
    rcases hdeg f with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨hCol, hCof, hMap⟩ := reedyCofibrant_degreeColimits_data deg hdeg X hX
  have h0 : IsCofibrant ((degreeColimits deg X).obj 0) := hCof 0
  have hSeq : HasColimit (degreeColimits deg X) := h6.hasColimit _ h0 hMap
  have := h6.cofibration (degreeColimits deg X) h0 hMap
  have hSeqCof : IsCofibrant (colimit (degreeColimits deg X)) :=
    cofibrant_target (colimit.ι (degreeColimits deg X) 0)
  have hColX : HasColimit X := hasColimit_of_degreeColimits deg X hmono
  refine ⟨hColX, ?_⟩
  let e : colimit (degreeColimits deg X) ≅ colimit X :=
    (isColimitDegreeColimitCocone deg X hmono).coconePointUniqueUpToIso (colimit.isColimit X)
  have := cofibration_of_isIso e.hom
  exact cofibrant_target e.hom

/-- Theorem 9.3.5(1)(c) for finite bounded-degree truncations. Both parts of
CF6 are used; CF5 is not needed. -/
theorem reedyCofibrant_colimMap_weakEquivalence_finite_degree_truncations
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory] [∀ a b : D, Finite (a ⟶ b)]
    (h6 : SequentialCofibrationAxiom M) (h6t : TrivialSequentialAxiom M)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
    [∀ d, HasColimit (latchingDiagram Y d)] (hX : IsReedyCofibrant X)
    (hY : IsReedyCofibrant Y) (f : X ⟶ Y) (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f) := by
  have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨hColX, hCofX, hMapX⟩ := reedyCofibrant_degreeColimits_data deg hdeg X hX
  obtain ⟨hColY, hCofY, hMapY⟩ := reedyCofibrant_degreeColimits_data deg hdeg Y hY
  have h0X : IsCofibrant ((degreeColimits deg X).obj 0) := hCofX 0
  have h0Y : IsCofibrant ((degreeColimits deg Y).obj 0) := hCofY 0
  have hSX : HasColimit (degreeColimits deg X) := h6.hasColimit _ h0X hMapX
  have hSY : HasColimit (degreeColimits deg Y) := h6.hasColimit _ h0Y hMapY
  have hW (n : ℕ) : WeakEquivalence ((degreeColimitsMap deg f).app n) := by
    have : ∀ a b : (degreeBelow deg n).FullSubcategory, Finite (a ⟶ b) := fun _ _ ↦
      Finite.of_injective (fun g ↦ g.hom) (fun _ _ h ↦ InducedCategory.hom_ext h)
    obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) X hX
    obtain ⟨_, hRY⟩ := OpenDiagramSubcategory.isReedyCofibrant (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) Y hY
    obtain ⟨_, _, hwn⟩ := reedyCofibrant_colimMap_weakEquivalence hRX hRY
      (Functor.whiskerLeft (degreeBelow deg n).ι f) (fun e ↦ hw e.obj)
    exact hwn
  have hSW := ABCPrecofibrationCategory.weakEquivalence_colimMap_of_sequences h6 h6t
    (degreeColimitsMap deg f) h0X hMapX h0Y hMapY hW
  have hCX : HasColimit X := hasColimit_of_degreeColimits deg X hmono
  have hCY : HasColimit Y := hasColimit_of_degreeColimits deg Y hmono
  refine ⟨hCX, hCY, ?_⟩
  let eX := degreeColimitIso deg X hmono
  let eY := degreeColimitIso deg Y hmono
  have := weakEquivalence_of_isIso eX.inv
  have := weakEquivalence_of_isIso eY.hom
  rw [show colimMap f = eX.inv ≫ colimMap (degreeColimitsMap deg f) ≫ eY.hom by
    rw [Iso.eq_inv_comp]
    exact (degreeColimitIso_naturality deg hmono f).symm]
  infer_instance

/-- Theorem 9.3.5(1)(b) for finite bounded-degree truncations. Only CF6(1)
beyond the four precofibration axioms is needed. -/
theorem reedyCofibration_colimMap_finite_degree_truncations
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory] [∀ a b : D, Finite (a ⟶ b)]
    (h6 : SequentialCofibrationAxiom M) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f) := by
  have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  obtain ⟨hColX, hCofX, hMapX⟩ := reedyCofibrant_degreeColimits_data deg hdeg X hf.1
  obtain ⟨hColY, hCofY, hMapY⟩ := reedyCofibrant_degreeColimits_data deg hdeg Y hf.2.1
  have hHom (n : ℕ) : ∀ a b : (degreeBelow deg n).FullSubcategory, Finite (a ⟶ b) :=
    fun _ _ ↦ Finite.of_injective (fun g ↦ g.hom) (fun _ _ h ↦ InducedCategory.hom_ext h)
  have hτ (n : ℕ) : Cofibration ((degreeColimitsMap deg f).app n) := by
    obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration (degreeBelow deg n)
      (degreeBelow_isOpen deg hmono n) hf
    obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap hR
    exact hc
  have hk (n : ℕ) : ∃ (Q : M) (l : (degreeColimits deg Y).obj n ⟶ Q)
      (r : (degreeColimits deg X).obj (n + 1) ⟶ Q)
      (c : Q ⟶ (degreeColimits deg Y).obj (n + 1)),
      IsPushout ((degreeColimitsMap deg f).app n) ((degreeColimits deg X).map (succHom n)) l r ∧
        l ≫ c = (degreeColimits deg Y).map (succHom n) ∧
        r ≫ c = (degreeColimitsMap deg f).app (n + 1) ∧ Cofibration c := by
    let i := degreeInclusion deg (Nat.le_succ n)
    have : i.Full := ObjectProperty.full_ιOfLE (P := degreeBelow deg n)
      (P' := degreeBelow deg (n + 1)) (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ n))
    have : i.Faithful := ObjectProperty.faithful_ιOfLE (P := degreeBelow deg n)
      (P' := degreeBelow deg (n + 1)) (fun _ he ↦ lt_of_lt_of_le he (Nat.le_succ n))
    have := Fintype.ofFinite (degreeBelow deg (n + 1)).FullSubcategory
    have : HasColimit (i ⋙ (degreeBelow deg (n + 1)).ι ⋙ X) := hColX n
    have : HasColimit (i ⋙ (degreeBelow deg (n + 1)).ι ⋙ Y) := hColY n
    have hopen : ∀ {a : (degreeBelow deg (n + 1)).FullSubcategory}
        (e : (degreeBelow deg n).FullSubcategory), (a ⟶ i.obj e) → ∃ e', i.obj e' = a := by
      intro a e g
      exact ⟨⟨a.obj, lt_of_le_of_lt (hmono g.hom) e.property⟩,
        ObjectProperty.FullSubcategory.ext rfl⟩
    obtain ⟨_, _, hR⟩ := OpenDiagramSubcategory.isReedyCofibration (degreeBelow deg (n + 1))
      (degreeBelow_isOpen deg hmono (n + 1)) hf
    let g := Functor.whiskerLeft (degreeBelow deg (n + 1)).ι f
    obtain ⟨hpo, hc⟩ := reedyCofibration_relativeColimMap_aux _
      (degreeBelow deg (n + 1)).FullSubcategory rfl (degreeBelow deg n).FullSubcategory i
      hopen g hR (hCofX n) (hCofY n) (hτ n)
    exact ⟨_, _, _, relativeColimMap i g, (IsPushout.of_hasPushout
      (colimit.pre ((degreeBelow deg (n + 1)).ι ⋙ X) i)
      (colimMap (Functor.whiskerLeft i g))).flip,
      inr_relativeColimMap i g, inl_relativeColimMap i g, hc⟩
  have h0X : IsCofibrant ((degreeColimits deg X).obj 0) := hCofX 0
  have h0Y : IsCofibrant ((degreeColimits deg Y).obj 0) := hCofY 0
  have hSX : HasColimit (degreeColimits deg X) := h6.hasColimit _ h0X hMapX
  have hSY : HasColimit (degreeColimits deg Y) := h6.hasColimit _ h0Y hMapY
  have hSC := cofibration_colimMap_of_reedy h6 (degreeColimitsMap deg f) h0X hMapX hτ hk
  have hCX : HasColimit X := hasColimit_of_degreeColimits deg X hmono
  have hCY : HasColimit Y := hasColimit_of_degreeColimits deg Y hmono
  refine ⟨hCX, hCY, ?_⟩
  have := isCofibrant_colimit_of_sequence h6 (degreeColimits deg X) h0X hMapX
  have := isCofibrant_colimit_of_sequence h6 (degreeColimits deg Y) h0Y hMapY
  let eX := degreeColimitIso deg X hmono
  let eY := degreeColimitIso deg Y hmono
  have := cofibration_of_isIso eX.hom
  have := cofibrant_target eX.hom
  have := cofibration_of_isIso eX.inv
  have := cofibration_of_isIso eY.hom
  rw [show colimMap f = eX.inv ≫ colimMap (degreeColimitsMap deg f) ≫ eY.hom by
    rw [Iso.eq_inv_comp]
    exact (degreeColimitIso_naturality deg hmono f).symm]
  infer_instance

end ABCCofibrations

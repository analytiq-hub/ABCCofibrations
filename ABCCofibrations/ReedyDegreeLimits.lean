/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyDegreeColimits
public import ABCCofibrations.ReedyInverse

/-!
# Inverse diagrams with finite degree truncations

Theorem 9.3.5(2)(a)–(c), dual to the unbounded finite-truncation colimit
theorems. The results use native limits and limit maps. F6 is expressed as
CF6 on the opposite category; only (c) uses the trivial-composite clause.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] (deg : D → ℕ)
  {M : Type u} [Category.{v} M] [CategoryWithFibrations M]
  [CategoryWithWeakEquivalences M] [HasTerminal M] [ABCPrefibrationCategory M]

/-- A degree on the opposite indexing category, written using native objects. -/
def oppositeDegree : Dᵒᵖ → ℕ := fun d ↦ deg d.unop

/-- An inverse degree function becomes a direct degree function on opposites. -/
lemma inverseDegree_op
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg b < deg a ∨ ∃ h : a = b, f = eqToHom h) :
    ∀ {a b : Dᵒᵖ} (f : a ⟶ b), oppositeDegree deg a < oppositeDegree deg b ∨
      ∃ h : a = b, f = eqToHom h := by
  intro a b f
  rcases hdeg f.unop with h | ⟨h, hf⟩
  · exact Or.inl h
  · obtain rfl : a = b := unop_injective h.symm
    refine Or.inr ⟨rfl, ?_⟩
    apply Quiver.Hom.unop_inj
    simpa using hf

/-- Finiteness of bounded-degree objects is unchanged by taking opposites. -/
instance finite_degreeBelow_opposite (n : ℕ) [Finite (degreeBelow deg n).FullSubcategory] :
    Finite (degreeBelow (oppositeDegree deg) n).FullSubcategory :=
  Finite.of_injective
    (fun e : (degreeBelow (oppositeDegree deg) n).FullSubcategory ↦
      (⟨e.obj.unop, e.property⟩ : (degreeBelow deg n).FullSubcategory))
    (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext
      (unop_injective (congrArg ObjectProperty.FullSubcategory.obj h)))

/-- Theorem 9.3.5(2)(a) for possibly infinite inverse categories with finite
bounded-degree truncations. Only F1–F4 and F6(1) are used. -/
theorem reedyFibrant_limit_finite_degree_truncations
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg b < deg a ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory]
    (h6 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Mᵒᵖ) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X.op d)] (hX : IsReedyFibrant X) :
    ∃ (_ : HasLimit X), IsFibrant (limit X) := by
  obtain ⟨_, hC⟩ := reedyCofibrant_colimit_finite_degree_truncations
    (oppositeDegree deg) (inverseDegree_op deg hdeg) h6 X.op hX
  have hL : HasLimit X := hasLimit_of_hasColimit_op X
  refine ⟨hL, (ABCPrefibrationCategory.isFibrant_iff_isCofibrant_op _).2 ?_⟩
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  exact ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit X).hom

/-- Theorem 9.3.5(2)(b) for inverse diagrams with finite degree truncations,
by duality. F6(1) suffices. -/
theorem reedyFibration_limMap_finite_degree_truncations
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg b < deg a ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory] [∀ a b : D, Finite (a ⟶ b)]
    (h6 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] {f : X ⟶ Y} (hf : IsReedyFibration f) :
    ∃ (_ : HasLimit X) (_ : HasLimit Y), Fibration (limMap f) := by
  obtain ⟨_, _, hc⟩ := reedyCofibration_colimMap_finite_degree_truncations
    (oppositeDegree deg) (inverseDegree_op deg hdeg) h6 hf
  obtain ⟨_, hX⟩ := reedyCofibrant_colimit_finite_degree_truncations
    (oppositeDegree deg) (inverseDegree_op deg hdeg) h6 X.op hf.2.1
  obtain ⟨_, hY⟩ := reedyCofibrant_colimit_finite_degree_truncations
    (oppositeDegree deg) (inverseDegree_op deg hdeg) h6 Y.op hf.1
  have hLX : HasLimit X := hasLimit_of_hasColimit_op X
  have hLY : HasLimit Y := hasLimit_of_hasColimit_op Y
  refine ⟨hLX, hLY, (cofibration_op_iff _).1 ?_⟩
  rw [op_limMap_comparison]
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit Y).hom
  have := ABCPrecofibrationCategory.cofibrant_target (colimitOpIsoOpLimit Y).hom
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit Y).inv
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance

/-- Theorem 9.3.5(2)(c) for inverse diagrams with finite degree truncations,
by duality, using both parts of F6. -/
theorem reedyFibrant_limMap_weakEquivalence_finite_degree_truncations
    (hdeg : ∀ {a b : D} (f : a ⟶ b), deg b < deg a ∨ ∃ h : a = b, f = eqToHom h)
    [∀ n, Finite (degreeBelow deg n).FullSubcategory] [∀ a b : D, Finite (a ⟶ b)]
    (h6 : ABCPrecofibrationCategory.SequentialCofibrationAxiom Mᵒᵖ)
    (h6t : ABCPrecofibrationCategory.TrivialSequentialAxiom Mᵒᵖ)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X.op d)]
    [∀ d, HasColimit (latchingDiagram Y.op d)] (hX : IsReedyFibrant X)
    (hY : IsReedyFibrant Y) (f : X ⟶ Y) (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasLimit X) (_ : HasLimit Y), WeakEquivalence (limMap f) := by
  obtain ⟨_, _, hc⟩ := reedyCofibrant_colimMap_weakEquivalence_finite_degree_truncations
    (oppositeDegree deg) (inverseDegree_op deg hdeg) h6 h6t hY hX (NatTrans.op f)
    (fun d ↦ (weakEquivalences_op_iff _).2 (hw d.unop))
  have hLX : HasLimit X := hasLimit_of_hasColimit_op X
  have hLY : HasLimit Y := hasLimit_of_hasColimit_op Y
  refine ⟨hLX, hLY, (weakEquivalences_op_iff _).1 ?_⟩
  rw [op_limMap_comparison]
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit Y).inv
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitOpIsoOpLimit X).hom
  infer_instance

end ABCCofibrations

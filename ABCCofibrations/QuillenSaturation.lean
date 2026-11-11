/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.QuillenModelCategory
public import ABCCofibrations.Saturation
public import ABCCofibrations.LocalSmallness
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
public import Mathlib.Tactic.TFAE

/-!
# Quillen model categories have saturated weak equivalences (Theorem 7.2.4)

A (mathlib) model category with sequential colimits satisfies CF6, because
cofibrations and trivial cofibrations are defined by a left lifting property and
hence are stable under transfinite composition. Lemma 7.2.2 then shows that its
weak equivalences are saturated. (The paper's axiom M1 provides all colimits.)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace ABCCofibrations.QuillenModelCategory

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasColimitsOfShape ℕ C]

/-- CF6(1) for a model category with sequential colimits. -/
theorem sequentialCofibrationAxiom :
    letI := precofibrationCategory C
    ABCPrecofibrationCategory.SequentialCofibrationAxiom C := by
  let := precofibrationCategory C
  have hcof : (cofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← trivialFibrations_llp]
    infer_instance
  exact ⟨fun _ _ _ ↦ inferInstance, fun F _ hf _ ↦
    ⟨transfiniteCompositionsOfShape_le _ ℕ _
      ⟨transfiniteCompositionOfShapeNat _ F fun n ↦ (hf n).mem⟩⟩⟩

omit [HasColimitsOfShape ℕ C] in
/-- CF6(2) for a model category with sequential colimits. -/
theorem trivialSequentialAxiom :
    letI := precofibrationCategory C
    ABCPrecofibrationCategory.TrivialSequentialAxiom C := by
  let := precofibrationCategory C
  have htriv : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← fibrations_llp]
    infer_instance
  intro F _ hf hw _
  exact ⟨(transfiniteCompositionsOfShape_le _ ℕ _
    ⟨transfiniteCompositionOfShapeNat (trivialCofibrations C) F
      fun n ↦ ⟨(hf n).mem, (hw n).mem⟩⟩).2⟩

/-- **Theorem 7.2.4.** A model category with sequential colimits has saturated
weak equivalences: a map is a weak equivalence iff it becomes an isomorphism in
the homotopy category. -/
theorem weakEquivalence_iff_isIso_map {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {X Y : C} (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsIso (L.map f) := by
  let := precofibrationCategory C
  exact ABCPrecofibrationCategory.weakEquivalence_iff_isIso_map L sequentialCofibrationAxiom
    trivialSequentialAxiom f

omit [HasColimitsOfShape ℕ C] in
/-- In a model category, a fibrant object is a fibrant model (Definition 7.3.1(1)). -/
theorem isFibrantModel_of_isFibrant (X : C) [IsFibrant X] :
    letI := precofibrationCategory C
    ABCPrecofibrationCategory.IsFibrantModel X := by
  let := precofibrationCategory C
  intro A B f i _ hi hw
  have : Fibration (terminal.from X) := (isFibrant_iff X).1 inferInstance
  have sq : CommSq f i (terminal.from X) (terminal.from B) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

omit [HasColimitsOfShape ℕ C] in
/-- **Corollary 7.3.5(5).** The homotopy category of a locally small model category
is locally small. -/
theorem locallySmall_homotopyCategory [LocallySmall.{w} C] {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] : LocallySmall.{w} D := by
  let := precofibrationCategory C
  refine ABCPrecofibrationCategory.locallySmall_of_fibrantModels L fun A _ ↦ ?_
  let h := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from A)
  have : Fibration h.p := ⟨h.hp⟩
  have : IsFibrant h.Z := (isFibrant_iff h.Z).2 (by
    rw [show terminal.from h.Z = h.p from terminal.hom_ext _ _]
    infer_instance)
  exact ⟨h.Z, h.i, ⟨h.hi.2⟩, isFibrantModel_of_isFibrant h.Z⟩

omit [HasColimitsOfShape ℕ C] in
/-- **Lemma 7.4.1.** For `A` cofibrant and `B` fibrant in a model category, two maps
`f g : A ⟶ B` are Quillen left homotopic iff they are Quillen right homotopic iff
they have the same image in the homotopy category. This is mathlib's fundamental
lemma of homotopical algebra. -/
theorem quillen_homotopy_tfae {D : Type*} [Category D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] {A B : C} [IsCofibrant A] [IsFibrant B]
    (f g : A ⟶ B) :
    List.TFAE [LeftHomotopyRel f g, RightHomotopyRel f g, L.map f = L.map g] := by
  tfae_have 1 ↔ 2 := leftHomotopyRel_iff_rightHomotopyRel
  tfae_have 1 ↔ 3 := LeftHomotopyRel.iff_map_eq L A B
  tfae_finish

end ABCCofibrations.QuillenModelCategory

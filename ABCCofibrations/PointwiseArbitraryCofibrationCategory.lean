/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionColimitEquivalences
public import ABCCofibrations.ReedySmallKan
public import ABCCofibrations.KanMapComparison
public import ABCCofibrations.PointwiseCofibrationCategory
public import ABCCofibrations.Extension
public import ABCCofibrations.SmallDiagramCategories

/-! # Theorem 9.5.5(1): pointwise cofibration structure for arbitrary small `D`

For a cofibration category `M` and any small category `D` (in `Type`), the
diagrams `D ⥤ M` with pointwise weak equivalences and pointwise cofibrations
form a cofibration category. This is Cisinski's theorem, as presented in
Theorem 9.5.5 of *Cofibrations in Homotopy Theory*.

CF1–CF3 and CF5–CF6 are pointwise. CF4 follows the paper's argument through the
direct resolution Δ′D. For `f : A ⟶ B` with `A` pointwise cofibrant:

1. take a Reedy cofibrant replacement `a : X₁ ⟶ pₜ* A`, and factor
   `X₁ ⟶ pₜ* B` as a Reedy cofibration `f₁ : X₁ ⟶ Y₁` followed by a levelwise
   weak equivalence `r₁`;
2. `X₁` and `Y₁` are restricted, by 2-out-of-3 (no restricted Reedy structure
   is needed);
3. the left Kan extensions along `pₜ` give a pointwise cofibration
   `Lan f₁ : Lan X₁ ⟶ Lan Y₁` and adjoint maps `a' : Lan X₁ ⟶ A`,
   `r₁' : Lan Y₁ ⟶ B`, which are pointwise weak equivalences by the repaired
   Proposition 9.5.4(1)(a);
4. push out `Lan f₁` along `a'`. The cobase change `A ⟶ P` is a pointwise
   cofibration, and `P ⟶ B` is a pointwise weak equivalence by excision.

The paper's 9.5.4 is used only through the repaired key step, which avoids
Lemma 9.5.3.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations

open ABCPrecofibrationCategory

variable {D : Type} [SmallCategory D] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory.{0} M]

/-- Pulled-back diagrams `pₜ* A` are restricted. -/
theorem isResolutionRestricted_terminal_comp (A : D ⥤ M) :
    IsResolutionRestricted (resolutionTerminal D ⋙ A) := by
  intro x y g h hg
  change WeakEquivalence (A.map ((resolutionTerminal D).map g))
  rw [hg, eqToHom_map]
  exact weakEquivalence_of_isIso _

/-- A diagram levelwise weakly equivalent to a restricted diagram is restricted. -/
theorem isResolutionRestricted_of_weakEquivalence {X X' : SemisimplicialResolution D ⥤ M}
    (a : X ⟶ X') (ha : ∀ x, WeakEquivalence (a.app x)) (hX' : IsResolutionRestricted X') :
    IsResolutionRestricted X := by
  intro x y g h hg
  have := ha x
  have := ha y
  have := hX' g h hg
  have : WeakEquivalence (X.map g ≫ a.app y) := by
    rw [a.naturality]
    infer_instance
  exact weakEquivalence_of_postcomp _ (a.app y)

section Lan

variable {X : SemisimplicialResolution D ⥤ M}
  [(resolutionTerminal D).HasPointwiseLeftKanExtension X]

/-- The adjoint `colim_{pₜ} X ⟶ Y` of a map `X ⟶ pₜ* Y`. -/
noncomputable def resolutionLanDesc {Y : D ⥤ M} (a : X ⟶ resolutionTerminal D ⋙ Y) :
    (resolutionTerminal D).leftKanExtension X ⟶ Y :=
  ((resolutionTerminal D).leftKanExtension X).descOfIsLeftKanExtension
    ((resolutionTerminal D).leftKanExtensionUnit X) Y a

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory M] in
@[reassoc]
theorem resolutionLanDesc_unit {Y : D ⥤ M} (a : X ⟶ resolutionTerminal D ⋙ Y)
    (x : SemisimplicialResolution D) :
    ((resolutionTerminal D).leftKanExtensionUnit X).app x ≫
      (resolutionLanDesc a).app ((resolutionTerminal D).obj x) = a.app x :=
  Functor.descOfIsLeftKanExtension_fac_app _ _ _ _ _

end Lan

/-- For Reedy cofibrant restricted `X`, the adjoint of a levelwise weak
equivalence `X ⟶ pₜ* Y` is a pointwise weak equivalence (Proposition 9.5.4(1)(a)). -/
theorem weakEquivalence_resolutionLanDesc (X : SemisimplicialResolution D ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hXR : IsReedyCofibrant X)
    (hX : IsResolutionRestricted X) [(resolutionTerminal D).HasPointwiseLeftKanExtension X]
    {Y : D ⥤ M} (a : X ⟶ resolutionTerminal D ⋙ Y) (ha : ∀ x, WeakEquivalence (a.app x))
    (d : D) : WeakEquivalence ((resolutionLanDesc a).app d) := by
  obtain ⟨_, hu⟩ := weakEquivalence_resolution_leftKanExtensionUnit X hXR hX
  have := hu d
  have := ha (resolutionSingleton d)
  have : WeakEquivalence (((resolutionTerminal D).leftKanExtensionUnit X).app
      (resolutionSingleton d) ≫ (resolutionLanDesc a).app
        ((resolutionTerminal D).obj (resolutionSingleton d))) := by
    rw [resolutionLanDesc_unit a (resolutionSingleton d)]
    infer_instance
  have h2 : WeakEquivalence ((resolutionLanDesc a).app
      ((resolutionTerminal D).obj (resolutionSingleton d))) :=
    weakEquivalence_of_precomp
      (((resolutionTerminal D).leftKanExtensionUnit X).app (resolutionSingleton d)) _
  exact h2

namespace PointwiseDiagram

/-- **Theorem 9.5.5(1), CF4.** Factorization in the pointwise structure on
`D ⥤ M`, for an arbitrary small `D`. -/
theorem factorization_resolution {A B : PointwiseDiagram D M} (f : A ⟶ B)
    [hA : IsCofibrant A] :
    ∃ (Z : PointwiseDiagram D M) (i : A ⟶ Z) (p : Z ⟶ B),
      Cofibration i ∧ WeakEquivalence p ∧ i ≫ p = f := by
  let pt := resolutionTerminal D
  let A₀ : D ⥤ M := A
  let B₀ : D ⥤ M := B
  let f₀ : A₀ ⟶ B₀ := f
  let R := ReedyDiagram (SemisimplicialResolution D) M
  let PA : R := pt ⋙ A₀
  let PB : R := pt ⋙ B₀
  let Pf : PA ⟶ PB := Functor.whiskerLeft pt f₀
  obtain ⟨X₁, a, hX₁, ha⟩ := exists_cofibrant_replacement PA
  have := hX₁
  have ha' := (ReedyDiagram.weakEquivalence_iff a).1 ha
  obtain ⟨Y₁, f₁, r₁, hf₁, hr₁, hfac⟩ := factorization (C := R) (a ≫ Pf)
  have hr₁' := (ReedyDiagram.weakEquivalence_iff r₁).1 hr₁
  obtain ⟨hLX, hLY, hf₁R⟩ := (ReedyDiagram.cofibration_iff f₁).1 hf₁
  have hX₁R : IsReedyCofibrant (X₁ : SemisimplicialResolution D ⥤ M) := hf₁R.1
  have hY₁R : IsReedyCofibrant (Y₁ : SemisimplicialResolution D ⥤ M) := hf₁R.2.1
  have hXres : IsResolutionRestricted (X₁ : SemisimplicialResolution D ⥤ M) :=
    isResolutionRestricted_of_weakEquivalence (X' := pt ⋙ A₀) a ha'
    (isResolutionRestricted_terminal_comp A₀)
  have hYres : IsResolutionRestricted (Y₁ : SemisimplicialResolution D ⥤ M) :=
    isResolutionRestricted_of_weakEquivalence (X' := pt ⋙ B₀) r₁ hr₁'
    (isResolutionRestricted_terminal_comp B₀)
  obtain ⟨hKX, hKY, hcofL⟩ := reedyCofibration_pointwiseLeftKanMap_small pt hf₁R
  obtain ⟨hKX', hLXcof⟩ := reedyCofibrant_leftKanExtension_small pt
    (X₁ : SemisimplicialResolution D ⥤ M) hX₁R
  let gL := pointwiseLeftKanMap pt f₁
  let a' : pt.leftKanExtension X₁ ⟶ A₀ := resolutionLanDesc (Y := A₀) a
  let r₁' : pt.leftKanExtension Y₁ ⟶ B₀ := resolutionLanDesc (Y := B₀) r₁
  have ha'w (d : D) : WeakEquivalence (a'.app d) :=
    weakEquivalence_resolutionLanDesc (X₁ : SemisimplicialResolution D ⥤ M) hX₁R hXres
      (Y := A₀) a ha' d
  have hr₁'w (d : D) : WeakEquivalence (r₁'.app d) :=
    weakEquivalence_resolutionLanDesc (Y₁ : SemisimplicialResolution D ⥤ M) hY₁R hYres
      (Y := B₀) r₁ hr₁' d
  have hw : gL ≫ r₁' = a' ≫ f₀ := by
    apply (pt.leftKanExtension X₁).hom_ext_of_isLeftKanExtension (pt.leftKanExtensionUnit X₁)
    ext x
    change (pt.leftKanExtensionUnit X₁).app x ≫ gL.app (pt.obj x) ≫ r₁'.app (pt.obj x) =
      (pt.leftKanExtensionUnit X₁).app x ≫ a'.app (pt.obj x) ≫ f₀.app (pt.obj x)
    rw [pointwiseLeftKanMap_unit_assoc, resolutionLanDesc_unit, resolutionLanDesc_unit_assoc]
    exact congrArg (fun φ ↦ NatTrans.app φ x) hfac
  have hp (e : D) : HasPushout (gL.app e) (a'.app e) := by
    have := hcofL e
    have := hLXcof e
    have := (isCofibrant_iff A).1 hA e
    exact hasPushout _ _
  have hpo : HasPushout gL a' := hasPushout_of_pointwise gL a' hp
  have hT (e : D) := isPushout_app (IsPushout.of_hasPushout gL a') hp e
  refine ⟨(pushout gL a' : D ⥤ M), @pushout.inr (D ⥤ M) _ _ _ _ gL a' hpo,
    @pushout.desc (D ⥤ M) _ _ _ _ _ gL a' hpo r₁' f₀ hw, ⟨fun e ↦ ?_⟩, ⟨fun e ↦ ?_⟩,
    @pushout.inr_desc (D ⥤ M) _ _ _ _ _ gL a' hpo r₁' f₀ hw⟩
  · have := hcofL e
    have := hLXcof e
    have := (isCofibrant_iff A).1 hA e
    exact cofibration_of_isPushout (hT e)
  · have := hcofL e
    have := hLXcof e
    have := (isCofibrant_iff A).1 hA e
    have := ha'w e
    have : WeakEquivalence ((pushout.inl gL a').app e) :=
      weakEquivalence_of_isPushout_of_cofibration (hT e)
    have : WeakEquivalence ((pushout.inl gL a').app e ≫
        (@pushout.desc (D ⥤ M) _ _ _ _ _ gL a' hpo r₁' f₀ hw).app e) := by
      rw [← NatTrans.comp_app, @pushout.inl_desc (D ⥤ M) _ _ _ _ _ gL a' hpo r₁' f₀ hw]
      exact hr₁'w e
    exact weakEquivalence_of_precomp ((pushout.inl gL a').app e) _

/-- **Theorem 9.5.5(1)**, CF1–CF4, for an arbitrary small indexing category. -/
instance (priority := 50) precofibrationCategory_arbitrary :
    ABCPrecofibrationCategory (PointwiseDiagram D M) where
  initial_cofibrant := (isCofibrant_iff _).2 fun e ↦ by
    let i := (isInitialInitialObj (M := M) e).uniqueUpToIso initialIsInitial
    have := cofibration_of_isIso i.inv
    exact cofibrant_target i.inv
  cofibrations_comp := ⟨fun f g hf hg e ↦ by
    have := hf e
    have := hg e
    change Cofibration (NatTrans.app f e ≫ NatTrans.app g e)
    infer_instance⟩
  weakEquivalence_of_isIso {X Y} f hf := ⟨fun e ↦ by
    have : @IsIso (D ⥤ M) _ X Y f := hf
    have : IsIso (NatTrans.app f e) := NatIso.isIso_app_of_isIso f e
    exact weakEquivalence_of_isIso _⟩
  cofibration_of_isIso {X Y} f hf hX := ⟨fun e ↦ by
    have : @IsIso (D ⥤ M) _ X Y f := hf
    have : IsIso (NatTrans.app f e) := NatIso.isIso_app_of_isIso f e
    have := (isCofibrant_iff X).1 hX e
    exact cofibration_of_isIso _⟩
  weakEquivalences_twoOutOfThree := inferInstance
  hasPushout i f hA hC hi := hasPushout_of_pointwise i f (hasPushout_of_cofibrant i f)
  cofibration_of_isPushout {A B C E i f g j} h hA hC hi := ⟨fun e ↦ by
    have hT := isPushout_app h (hasPushout_of_cofibrant i f) e
    have := (isCofibrant_iff A).1 hA e
    have := (isCofibrant_iff C).1 hC e
    have : Cofibration (NatTrans.app i e) := hi.mem e
    exact cofibration_of_isPushout hT⟩
  weakEquivalence_of_isPushout {A B C E i f g j} h hA hC hi hw := ⟨fun e ↦ by
    have hT := isPushout_app h (hasPushout_of_cofibrant i f) e
    have := (isCofibrant_iff A).1 hA e
    have := (isCofibrant_iff C).1 hC e
    have : Cofibration (NatTrans.app i e) := hi.mem e
    have : WeakEquivalence (NatTrans.app i e) := hw.mem e
    exact weakEquivalence_of_isPushout hT⟩
  factorization f _ := factorization_resolution f

/-- **Theorem 9.5.5(1)** (Cisinski). For any small category `D` and any
cofibration category `M`, the diagrams `D ⥤ M` with pointwise weak
equivalences and pointwise cofibrations form a cofibration category. -/
instance (priority := 50) cofibrationCategory_arbitrary :
    ABCCofibrationCategory.{0} (PointwiseDiagram D M) :=
  cofibrationCategory_of_precofibrationCategory

end PointwiseDiagram

namespace PointwiseFibDiagram

variable (D : Type) [SmallCategory D] (N : Type u) [Category.{v} N] [CategoryWithFibrations N]
  [CategoryWithWeakEquivalences N] [HasTerminal N] [ABCFibrationCategory.{0} N]

/-- **Theorem 9.5.5(2)**, by duality: for any small `D` and any fibration
category `N`, diagrams `D ⥤ N` with pointwise weak equivalences and pointwise
fibrations form a fibration category. -/
theorem fibrationCategory_arbitrary : ABCFibrationCategory.{0} (PointwiseFibDiagram D N) := by
  refine ABCCofibrationCategory.of_equivalence (D' := PointwiseDiagram Dᵒᵖ Nᵒᵖ)
    (show (PointwiseFibDiagram D N)ᵒᵖ ≌ PointwiseDiagram Dᵒᵖ Nᵒᵖ from
      Functor.opUnopEquiv D N) ?_ ?_
  · ext X Y f
    change (∀ e, Fibration _) ↔ ∀ e, Cofibration _
    exact ⟨fun h e ↦ (cofibration_op_iff _).2 (h e.unop),
      fun h e ↦ (cofibration_op_iff _).1 (h (Opposite.op e))⟩
  · ext X Y f
    change (∀ e, WeakEquivalence _) ↔ ∀ e, WeakEquivalence _
    exact ⟨fun h e ↦ (weakEquivalences_op_iff _).2 (h e.unop),
      fun h e ↦ (weakEquivalences_op_iff _).1 (h (Opposite.op e))⟩

end PointwiseFibDiagram

end ABCCofibrations

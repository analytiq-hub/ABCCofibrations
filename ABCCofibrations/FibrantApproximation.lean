/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationBasic
public import ABCCofibrations.CofibrantApproximationDerived
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseRightDerived

/-!
# Fibrant approximations and right derived functors

Definition 6.1.2 and Theorem 6.2.2(2), obtained from the opposite cofibrant
approximation and mathlib's right derivability structures.
-/

@[expose] public section

universe v u v' u'
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- A fibrant approximation is a cofibrant approximation on opposite
categories. This is the dual of CFA1–CFA4, with all source objects fibrant. -/
abbrev IsFibrantApproximation
    {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
    [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
    {D : Type u'} [Category.{v'} D] [CategoryWithFibrations D]
    [CategoryWithWeakEquivalences D] [HasTerminal D] [ABCPrefibrationCategory D]
    (F : C ⥤ D) : Prop := IsCofibrantApproximation F.op

namespace IsFibrantApproximation

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type u'} [Category.{v'} D] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences D] [HasTerminal D] [ABCPrefibrationCategory D]
  (F : C ⥤ D) [IsFibrantApproximation F]

include F in
/-- Every source object is fibrant. -/
theorem source_fibrant (A : C) : IsFibrant A :=
  (ABCPrefibrationCategory.isFibrant_iff_isCofibrant_op A).2
    (IsCofibrantApproximation.source_cofibrant F.op (Opposite.op A))

/-- Image objects are fibrant. -/
theorem obj_fibrant (A : C) : IsFibrant (F.obj A) :=
  (ABCPrefibrationCategory.isFibrant_iff_isCofibrant_op (F.obj A)).2
    (IsCofibrantApproximation.obj_cofibrant F.op (Opposite.op A))

/-- Fibrant approximations preserve fibrations. -/
theorem map_fibration {A B : C} (p : A ⟶ B) [Fibration p] : Fibration (F.map p) :=
  (cofibration_op_iff (F.map p)).1
    (IsCofibrantApproximation.map_cofibration (F := F.op) p.op)

/-- Weak equivalences are detected exactly by a fibrant approximation. -/
theorem weakEquivalence_map_iff {A B : C} (f : A ⟶ B) :
    WeakEquivalence (F.map f) ↔ WeakEquivalence f := by
  rw [← weakEquivalences_op_iff (F.map f), ← weakEquivalences_op_iff f]
  exact IsCofibrantApproximation.weakEquivalence_map_iff (F := F.op) f.op

/-- Fibrant approximations preserve weak equivalences. -/
theorem map_weakEquivalence {A B : C} (f : A ⟶ B) [WeakEquivalence f] :
    WeakEquivalence (F.map f) := (weakEquivalence_map_iff F f).2 inferInstance

/-- Pullbacks of two fibrations are preserved, exactly the dual scope of CFA3. -/
theorem map_isPullback {A B E P : C} {f : A ⟶ P} {g : B ⟶ P}
    {i : E ⟶ A} {j : E ⟶ B} [Fibration f] [Fibration g]
    (h : IsPullback i j f g) :
    IsPullback (F.map i) (F.map j) (F.map f) (F.map g) :=
  (IsCofibrantApproximation.map_isPushout (F := F.op) h.op).unop

/-- Fibrant factorization: an ambient map into an image factors through the
image of a source fibration. -/
theorem factorization {A : C} {B : D} (f : B ⟶ F.obj A) :
    ∃ (Z : C) (w : B ⟶ F.obj Z) (p : Z ⟶ A),
      WeakEquivalence w ∧ Fibration p ∧ w ≫ F.map p = f := by
  obtain ⟨Z, i, p, hi, hp, hip⟩ := IsCofibrantApproximation.factorization (F := F.op) f.op
  exact ⟨Z.unop, p.unop, i.unop, (weakEquivalences_unop_iff p).2 hp,
    (fibration_unop_iff i).2 hi, congrArg Quiver.Hom.unop hip⟩

/-- The associated morphism of localizers, in the original direction. -/
def toLocalizerMorphism : LocalizerMorphism (weakEquivalences C) (weakEquivalences D) where
  functor := F
  map _ _ f hf := by
    let : WeakEquivalence f := ⟨hf⟩
    exact (map_weakEquivalence F f).mem

/-- The general localization equivalence transports from the opposite. -/
instance toLocalizerMorphism_isLocalizedEquivalence :
    (toLocalizerMorphism F).IsLocalizedEquivalence := by
  let Φ := toLocalizerMorphism F
  have : Φ.op.IsLocalizedEquivalence := by
    change (IsCofibrantApproximation.toLocalizerMorphism F.op).IsLocalizedEquivalence
    infer_instance
  let G := Φ.localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q
  let : CatCommSq Φ.op.functor (weakEquivalences C).Q.op
      (weakEquivalences D).Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor (weakEquivalences C).Q
      (weakEquivalences D).Q G).symm⟩
  have : G.op.IsEquivalence := Φ.op.isEquivalence
    (weakEquivalences C).Q.op (weakEquivalences D).Q.op G.op
  let : G.IsEquivalence := G.op.asEquivalence.unop.isEquivalence_functor
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ
    (weakEquivalences C).Q (weakEquivalences D).Q G

/-- Fibrant approximations are right derivability structures. -/
instance toLocalizerMorphism_isRightDerivabilityStructure :
    (toLocalizerMorphism F).IsRightDerivabilityStructure := by
  rw [LocalizerMorphism.isRightDerivabilityStructure_iff_op]
  change (IsCofibrantApproximation.toLocalizerMorphism F.op).IsLeftDerivabilityStructure
  infer_instance

include F in
/-- Brown's lemma on the all-fibrant source follows from its opposite form. -/
theorem inverts_of_inverts_trivialFibrations
    {H : Type*} [Category H] (G : C ⥤ H)
    (hG : ∀ {A B : C} (p : A ⟶ B) [Fibration p] [WeakEquivalence p],
      IsIso (G.map p)) : (weakEquivalences C).IsInvertedBy G := by
  have h := IsCofibrantApproximation.inverts_of_inverts_trivialCofibrations F.op G.op
    (fun i _ _ ↦ by
      let := hG i.unop
      exact inferInstanceAs (IsIso (G.map i.unop).op))
  intro A B f hf
  let : IsIso (G.map f).op := h f.op hf
  exact isIso_of_op (G.map f)

/-- Inverting trivial fibrations after an approximation suffices for
pointwise right-derived existence. -/
theorem hasPointwiseRightDerivedFunctor_of_inverts_trivialFibrations
    {H : Type*} [Category H] (U : D ⥤ H)
    (hU : ∀ {A B : C} (p : A ⟶ B) [Fibration p] [WeakEquivalence p],
      IsIso (U.map (F.map p))) : U.HasPointwiseRightDerivedFunctor (weakEquivalences D) := by
  let Φ := toLocalizerMorphism F
  have hW : (weakEquivalences C).IsInvertedBy (Φ.functor ⋙ U) :=
    inverts_of_inverts_trivialFibrations F (F ⋙ U) hU
  exact (Φ.hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure U).2
    (Functor.hasPointwiseRightDerivedFunctor_of_inverts _ hW)

/-- Any right derived unit is invertible on image objects. -/
theorem isIso_rightDerivedUnit_app
    {H : Type*} [Category H] (U : D ⥤ H)
    (hU : ∀ {A B : C} (p : A ⟶ B) [Fibration p] [WeakEquivalence p],
      IsIso (U.map (F.map p)))
    {E : Type*} [Category E] (L : D ⥤ E) [L.IsLocalization (weakEquivalences D)]
    (RU : E ⥤ H) (η : U ⟶ L ⋙ RU)
    [RU.IsRightDerivedFunctor η (weakEquivalences D)] (A : C) :
    IsIso (η.app (F.obj A)) := by
  let Φ := toLocalizerMorphism F
  let Q := (weakEquivalences C).Q
  have hW : (weakEquivalences C).IsInvertedBy (Φ.functor ⋙ U) :=
    inverts_of_inverts_trivialFibrations F (F ⋙ U) hU
  let : (Φ.functor ⋙ U).HasPointwiseRightDerivedFunctor (weakEquivalences C) :=
    Functor.hasPointwiseRightDerivedFunctor_of_inverts _ hW
  let U₁ := Localization.lift (Φ.functor ⋙ U) hW Q
  let η₁ := (Localization.fac (Φ.functor ⋙ U) hW Q).inv
  exact (Φ.isIso_iff_of_isRightDerivabilityStructure Q L U U₁ η₁ RU η A).1
    (by infer_instance)

/-- Right-derived existence and computation on approximation image objects,
with arbitrary target category and source localization. -/
theorem exists_rightDerivedFunctor_of_inverts_trivialFibrations
    {H : Type*} [Category H] (U : D ⥤ H)
    (hU : ∀ {A B : C} (p : A ⟶ B) [Fibration p] [WeakEquivalence p],
      IsIso (U.map (F.map p)))
    {E : Type*} [Category E] (L : D ⥤ E) [L.IsLocalization (weakEquivalences D)] :
    ∃ (RU : E ⥤ H) (η : U ⟶ L ⋙ RU),
      RU.IsRightDerivedFunctor η (weakEquivalences D) ∧
        ∀ A : C, IsIso (η.app (F.obj A)) := by
  let := hasPointwiseRightDerivedFunctor_of_inverts_trivialFibrations F U hU
  let RU := U.totalRightDerived L (weakEquivalences D)
  let η := U.totalRightDerivedUnit L (weakEquivalences D)
  exact ⟨RU, η, inferInstance, fun A ↦ isIso_rightDerivedUnit_app F U hU L RU η A⟩

/-- Theorem 6.2.2(2): total right-derived existence under the hypothesis on
the composite with a fibrant approximation. No saturation is assumed. -/
theorem exists_totalRightDerivedFunctor_of_map_trivialFibrations
    {M H : Type*} [Category M] [CategoryWithWeakEquivalences M] [Category H]
    (U : D ⥤ M)
    (hU : ∀ {A B : C} (p : A ⟶ B) [Fibration p] [WeakEquivalence p],
      WeakEquivalence (U.map (F.map p)))
    {E : Type*} [Category E] (L : D ⥤ E) [L.IsLocalization (weakEquivalences D)]
    (R : M ⥤ H) [R.IsLocalization (weakEquivalences M)] :
    ∃ (RU : E ⥤ H) (η : U ⋙ R ⟶ L ⋙ RU),
      RU.IsRightDerivedFunctor η (weakEquivalences D) ∧
        ∀ A : C, IsIso (η.app (F.obj A)) := by
  apply exists_rightDerivedFunctor_of_inverts_trivialFibrations F (U ⋙ R) ?_ L
  intro A B p _ _
  exact Localization.inverts R (weakEquivalences M) (U.map (F.map p)) (hU p).mem

end IsFibrantApproximation
end ABCCofibrations

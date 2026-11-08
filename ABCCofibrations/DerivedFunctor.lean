/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReplacementComparison
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.PointwiseLeftDerived

/-!
# Total left derived functors under CF1–CF4

Inclusion of cofibrant objects is a left derivability structure in mathlib's
sense. Thus a functor inverting trivial cofibrations between cofibrant objects
has a pointwise left derived functor, whose counit is invertible on cofibrant
objects. Applying this to a functor followed by target localization gives
Theorem 6.2.1(1). Unlike the paper's proof via general approximation functors,
we use mathlib's derivability-structure constructor for this inclusion.

For any derived functor with its counit, the value at an ambient object is
computed by any cofibrant replacement. These computation isomorphisms are
natural for replacement squares, recover the counit, and give coherent
comparisons between different replacements.
-/

@[expose] public section

universe v u v' u' v'' u''

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The cofibrant inclusion is a left derivability structure. The required
connected replacement categories and arrow resolutions were proved under CF1–CF4. -/
instance cofibrantInclusion_isLeftDerivabilityStructure :
    (cofibrantInclusionLocalizerMorphism (C := C)).IsLeftDerivabilityStructure := by
  let : (weakEquivalences C).ContainsIdentities :=
    ⟨fun X ↦ (weakEquivalence_of_isIso (𝟙 X)).mem⟩
  exact LocalizerMorphism.IsLeftDerivabilityStructure.mk' _

variable {H : Type u'} [Category.{v'} H]

/-- Inversion of trivial cofibrations on cofibrant objects suffices for
existence of a pointwise left derived functor. -/
theorem hasPointwiseLeftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom)) :
    F.HasPointwiseLeftDerivedFunctor (weakEquivalences C) := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  have hW : (weakEquivalences (CofibrantObject C)).IsInvertedBy (Φ.functor ⋙ F) :=
    isInvertedBy_of_inverts_trivialCofibrations (Φ.functor ⋙ F) hF
  exact (Φ.hasPointwiseLeftDerivedFunctor_iff_of_isLeftDerivabilityStructure F).2
    (Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW)

/-- Every left derived functor of such a functor has invertible counit at
cofibrant objects. This applies to any choice of source localization. -/
theorem isIso_leftDerivedCounit_app_cofibrant
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)]
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F)
    [LF.IsLeftDerivedFunctor ε (weakEquivalences C)]
    (A : C) [IsCofibrant A] : IsIso (ε.app A) := by
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let Q := (weakEquivalences (CofibrantObject C)).Q
  let hW : (weakEquivalences (CofibrantObject C)).IsInvertedBy (Φ.functor ⋙ F) :=
    isInvertedBy_of_inverts_trivialCofibrations (Φ.functor ⋙ F) hF
  let : (Φ.functor ⋙ F).HasPointwiseLeftDerivedFunctor
      (weakEquivalences (CofibrantObject C)) :=
    Functor.hasPointwiseLeftDerivedFunctor_of_inverts _ hW
  let F₁ := Localization.lift (Φ.functor ⋙ F) hW Q
  let ε₁ := (Localization.fac (Φ.functor ⋙ F) hW Q).hom
  exact (Φ.isIso_iff_of_isLeftDerivabilityStructure Q L F F₁ ε₁ LF ε
    (CofibrantObject.mk A)).1 (by infer_instance)

/-- Existence and cofibrant counit property, with an arbitrary source
localization and an arbitrary target category. -/
theorem exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations
    (F : C ⥤ H)
    (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
      Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  let := hasPointwiseLeftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations F hF
  let LF := F.totalLeftDerived L (weakEquivalences C)
  let ε := F.totalLeftDerivedCounit L (weakEquivalences C)
  exact ⟨LF, ε, inferInstance, fun A _ ↦ isIso_leftDerivedCounit_app_cofibrant F hF L LF ε A⟩

/-- Theorem 6.2.1(1): a functor preserving trivial cofibrations between
cofibrant objects as weak equivalences admits a total left derived functor.
The target needs only a designated weak-equivalence class and its localization. -/
theorem exists_totalLeftDerivedFunctor_of_map_trivialCofibrations
    {E : Type*} [Category E] [CategoryWithWeakEquivalences E]
    (F : C ⥤ E)
    (hF : ∀ {X Y : C} (i : X ⟶ Y) [IsCofibrant X] [Cofibration i]
      [WeakEquivalence i], WeakEquivalence (F.map i))
    {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
    [L.IsLocalization (weakEquivalences C)]
    (R : E ⥤ H) [R.IsLocalization (weakEquivalences E)] :
    ∃ (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F ⋙ R),
      LF.IsLeftDerivedFunctor ε (weakEquivalences C) ∧
        ∀ (A : C) [IsCofibrant A], IsIso (ε.app A) := by
  apply exists_leftDerivedFunctor_of_inverts_cofibrant_trivialCofibrations (F ⋙ R) ?_ L
  intro X Y i hi hw
  let := hi
  let := hw
  exact Localization.inverts R (weakEquivalences E) (F.map i.hom) (hF i.hom).mem

section Computation

variable (F : C ⥤ H)
  (hF : ∀ {X Y : CofibrantObject C} (i : X ⟶ Y),
    Cofibration i.hom → WeakEquivalence i.hom → IsIso (F.map i.hom))
  {D : Type u''} [Category.{v''} D] (L : C ⥤ D)
  [L.IsLocalization (weakEquivalences C)]
  (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F)
  [LF.IsLeftDerivedFunctor ε (weakEquivalences C)]

/-- A left derived functor is computed by any cofibrant replacement. The
isomorphism uses the inverse of the derived image of the replacement, followed
by the counit at its cofibrant source. -/
noncomputable def leftDerivedObjIsoOfCofibrantReplacement
    {A Q : C} [IsCofibrant Q] (q : Q ⟶ A) [WeakEquivalence q] :
    LF.obj (L.obj A) ≅ F.obj Q := by
  let := isIso_leftDerivedCounit_app_cofibrant F hF L LF ε Q
  exact (LF.mapIso (Localization.isoOfHom L (weakEquivalences C) q
    (inferInstance : WeakEquivalence q).mem)).symm ≪≫ asIso (ε.app Q)

/-- The computation isomorphism recovers the counit after precomposition
with the derived image of the replacement. -/
@[reassoc (attr := simp)]
theorem map_comp_leftDerivedObjIsoOfCofibrantReplacement_hom
    {A Q : C} [IsCofibrant Q] (q : Q ⟶ A) [WeakEquivalence q] :
    LF.map (L.map q) ≫ (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε q).hom =
      ε.app Q := by
  let e := LF.mapIso (Localization.isoOfHom L (weakEquivalences C) q
    (inferInstance : WeakEquivalence q).mem)
  change e.hom ≫ (e.inv ≫ ε.app Q) = ε.app Q
  simp

/-- The ambient counit is computed by the replacement formula and the
original functor applied to the replacement map. -/
@[reassoc]
theorem leftDerivedObjIsoOfCofibrantReplacement_hom_comp_map
    {A Q : C} [IsCofibrant Q] (q : Q ⟶ A) [WeakEquivalence q] :
    (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε q).hom ≫ F.map q =
      ε.app A := by
  let := Localization.inverts L (weakEquivalences C) q
    (inferInstance : WeakEquivalence q).mem
  apply (cancel_epi (LF.map (L.map q))).1
  rw [← Category.assoc, map_comp_leftDerivedObjIsoOfCofibrantReplacement_hom]
  exact (ε.naturality q).symm

/-- Naturality of the replacement computation for a commutative square.
No functorial choice of replacements or cofibration hypothesis on the
comparison map is required. -/
@[reassoc]
theorem leftDerivedObjIsoOfCofibrantReplacement_naturality
    {A B Q R : C} [IsCofibrant Q] [IsCofibrant R]
    (q : Q ⟶ A) (r : R ⟶ B) [WeakEquivalence q] [WeakEquivalence r]
    (f : A ⟶ B) (a : Q ⟶ R) (h : a ≫ r = q ≫ f) :
    LF.map (L.map f) ≫ (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε r).hom =
      (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε q).hom ≫ F.map a := by
  let := Localization.inverts L (weakEquivalences C) q
    (inferInstance : WeakEquivalence q).mem
  have hs : LF.map (L.map q) ≫ LF.map (L.map f) =
      LF.map (L.map a) ≫ LF.map (L.map r) := by
    simp only [← LF.map_comp, ← L.map_comp]
    rw [h]
  apply (cancel_epi (LF.map (L.map q))).1
  calc
    LF.map (L.map q) ≫ (LF.map (L.map f) ≫
        (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε r).hom) =
        LF.map (L.map a) ≫ (LF.map (L.map r) ≫
          (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε r).hom) := by
      rw [← Category.assoc, hs, Category.assoc]
    _ = LF.map (L.map a) ≫ ε.app R := by
      rw [map_comp_leftDerivedObjIsoOfCofibrantReplacement_hom]
    _ = ε.app Q ≫ F.map a := ε.naturality a
    _ = LF.map (L.map q) ≫
        ((leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε q).hom ≫ F.map a) := by
      rw [← Category.assoc, map_comp_leftDerivedObjIsoOfCofibrantReplacement_hom]

/-- Any two replacements compute canonically isomorphic values, relative to
the given derived functor and counit. -/
noncomputable def leftDerivedReplacementComparisonIso
    {A Q R : C} [IsCofibrant Q] [IsCofibrant R]
    (q : Q ⟶ A) (r : R ⟶ A) [WeakEquivalence q] [WeakEquivalence r] :
    F.obj Q ≅ F.obj R :=
  (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε q).symm ≪≫
    leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε r

/-- A comparison map over the same ambient object computes the canonical
comparison isomorphism under the original functor. -/
theorem leftDerivedReplacementComparisonIso_hom_eq_map
    {A Q R : C} [IsCofibrant Q] [IsCofibrant R]
    (q : Q ⟶ A) (r : R ⟶ A) [WeakEquivalence q] [WeakEquivalence r]
    (a : Q ⟶ R) (h : a ≫ r = q) :
    (leftDerivedReplacementComparisonIso F hF L LF ε q r).hom = F.map a := by
  have hn := leftDerivedObjIsoOfCofibrantReplacement_naturality F hF L LF ε
    q r (𝟙 A) a (by simpa using h)
  simp only [L.map_id, LF.map_id, Category.id_comp] at hn
  apply (cancel_epi (leftDerivedObjIsoOfCofibrantReplacement F hF L LF ε q).hom).1
  simpa [leftDerivedReplacementComparisonIso] using hn

/-- Comparing a replacement with itself gives the identity isomorphism. -/
@[simp]
theorem leftDerivedReplacementComparisonIso_refl
    {A Q : C} [IsCofibrant Q] (q : Q ⟶ A) [WeakEquivalence q] :
    leftDerivedReplacementComparisonIso F hF L LF ε q q = Iso.refl (F.obj Q) := by
  simp [leftDerivedReplacementComparisonIso]

/-- Comparison isomorphisms between replacement computations compose
consistently. -/
@[simp]
theorem leftDerivedReplacementComparisonIso_trans
    {A Q R S : C} [IsCofibrant Q] [IsCofibrant R] [IsCofibrant S]
    (q : Q ⟶ A) (r : R ⟶ A) (s : S ⟶ A)
    [WeakEquivalence q] [WeakEquivalence r] [WeakEquivalence s] :
    leftDerivedReplacementComparisonIso F hF L LF ε q r ≪≫
        leftDerivedReplacementComparisonIso F hF L LF ε r s =
      leftDerivedReplacementComparisonIso F hF L LF ε q s := by
  simp [leftDerivedReplacementComparisonIso]

end Computation

end ABCCofibrations.ABCPrecofibrationCategory

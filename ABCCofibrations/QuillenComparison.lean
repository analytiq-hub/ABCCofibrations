/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.QuillenAdjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Comparison formulas and criteria for Quillen adjunctions

The comparison equations for the derived unit and counit, and the
one-sided weak-equivalence criteria of Theorem 6.2.5(2).
-/

@[expose] public section

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {C' : Type u₁} [Category.{v₁} C'] [CategoryWithCofibrations C']
  [CategoryWithWeakEquivalences C'] [HasInitial C'] [ABCPrecofibrationCategory C']
  {C : Type u₂} [Category.{v₂} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D' : Type u₃} [Category.{v₃} D'] [CategoryWithFibrations D']
  [CategoryWithWeakEquivalences D'] [HasTerminal D'] [ABCPrefibrationCategory D']
  {D : Type u₄} [Category.{v₄} D] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences D] [HasTerminal D] [ABCPrefibrationCategory D]
  (tC : C' ⥤ C) [IsCofibrantApproximation tC]
  (tD : D' ⥤ D) [IsFibrantApproximation tD]
  {G : C ⥤ D} {F : D ⥤ C}

variable (adj : G ⊣ F) [IsQuillenAdjunction tC tD adj]
  {HC HD : Type*} [Category HC] [Category HD]
  (LC : C ⥤ HC) [LC.IsLocalization (weakEquivalences C)]
  (LD : D ⥤ HD) [LD.IsLocalization (weakEquivalences D)]


variable (LG : HC ⥤ HD) (ε : LC ⋙ LG ⟶ G ⋙ LD)
  [LG.IsLeftDerivedFunctor ε (weakEquivalences C)]
  (RF : HD ⥤ HC) (η : F ⋙ LC ⟶ LD ⋙ RF)
  [RF.IsRightDerivedFunctor η (weakEquivalences D)]

/-- The derived unit recovers the original unit after the derived comparisons. -/
theorem quillenDerivedAdjunction_unit_fac_app (X : C) :
    (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).unit.app (LC.obj X) ≫
      RF.map (ε.app X) = LC.map (adj.unit.app X) ≫ η.app (G.obj X) := by
  let Φ := IsCofibrantApproximation.toLocalizerMorphism tC
  let Ψ := IsFibrantApproximation.toLocalizerMorphism tD
  have hG : Φ.Derives (G ⋙ LD) :=
    IsCofibrantApproximation.inverts_of_inverts_trivialCofibrations tC (tC ⋙ G ⋙ LD)
      (fun i ↦ Localization.inverts LD (weakEquivalences D) _
        (IsQuillenAdjunction.map_trivialCofibration (tC := tC) (tD := tD) (adj := adj) i).mem)
  have hF : Ψ.Derives (F ⋙ LC) :=
    IsFibrantApproximation.inverts_of_inverts_trivialFibrations tD (tD ⋙ F ⋙ LC)
      (fun p ↦ Localization.inverts LC (weakEquivalences C) _
        (IsQuillenAdjunction.map_trivialFibration (tC := tC) (tD := tD) (adj := adj) p).mem)
  let := isLeftDerivedFunctor_postcomp_of_derives Φ (G ⋙ LD) hG LC LG ε RF
  let := isRightDerivedFunctor_postcomp_of_derives Ψ (F ⋙ LC) hF LD RF η LG
  unfold quillenDerivedAdjunction
  exact adj.derivedη_fac_app (weakEquivalences C) ε η X

/-- The derived counit recovers the original counit after the derived comparisons. -/
theorem quillenDerivedAdjunction_counit_fac_app (Y : D) :
    LG.map (η.app Y) ≫
      (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).counit.app (LD.obj Y) =
        ε.app (F.obj Y) ≫ LD.map (adj.counit.app Y) := by
  let Φ := IsCofibrantApproximation.toLocalizerMorphism tC
  let Ψ := IsFibrantApproximation.toLocalizerMorphism tD
  have hG : Φ.Derives (G ⋙ LD) :=
    IsCofibrantApproximation.inverts_of_inverts_trivialCofibrations tC (tC ⋙ G ⋙ LD)
      (fun i ↦ Localization.inverts LD (weakEquivalences D) _
        (IsQuillenAdjunction.map_trivialCofibration (tC := tC) (tD := tD) (adj := adj) i).mem)
  have hF : Ψ.Derives (F ⋙ LC) :=
    IsFibrantApproximation.inverts_of_inverts_trivialFibrations tD (tD ⋙ F ⋙ LC)
      (fun p ↦ Localization.inverts LC (weakEquivalences C) _
        (IsQuillenAdjunction.map_trivialFibration (tC := tC) (tD := tD) (adj := adj) p).mem)
  let := isLeftDerivedFunctor_postcomp_of_derives Φ (G ⋙ LD) hG LC LG ε RF
  let := isRightDerivedFunctor_postcomp_of_derives Ψ (F ⋙ LC) hF LD RF η LG
  unfold quillenDerivedAdjunction
  exact adj.derivedε_fac_app (weakEquivalences D) ε η Y

/-- Localization of adjoint arrows is compatible with the derived hom-set
adjunction, including comparison maps at arbitrary objects. -/
theorem quillenDerivedAdjunction_homEquiv (X : C) (Y : D) (f : G.obj X ⟶ Y) :
    (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).homEquiv _ _
      (ε.app X ≫ LD.map f) = LC.map (adj.homEquiv X Y f) ≫ η.app Y := by
  have hn : LC.map (F.map f) ≫ η.app Y = η.app (G.obj X) ≫ RF.map (LD.map f) :=
    η.naturality f
  rw [Adjunction.homEquiv_unit, RF.map_comp, ← Category.assoc,
    quillenDerivedAdjunction_unit_fac_app, Category.assoc,
    ← hn, ← Category.assoc, ← LC.map_comp, adj.homEquiv_unit]

/-- The companion equation for arrows written in the adjoint direction. -/
theorem quillenDerivedAdjunction_homEquiv_symm (X : C) (Y : D) (g : X ⟶ F.obj Y) :
    ((quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).homEquiv _ _).symm
      (LC.map g ≫ η.app Y) = ε.app X ≫ LD.map ((adj.homEquiv X Y).symm g) := by
  have hn : LG.map (LC.map g) ≫ ε.app (F.obj Y) = ε.app X ≫ LD.map (G.map g) :=
    ε.naturality g
  rw [Adjunction.homEquiv_counit, LG.map_comp, Category.assoc,
    quillenDerivedAdjunction_counit_fac_app, ← Category.assoc, hn, Category.assoc,
    ← LD.map_comp, adj.homEquiv_counit]

/-- The (4l) direction: a weak equivalence into a fibrant approximation
has a weak-equivalence adjoint. This makes the derived unit invertible. -/
theorem isIso_quillenDerivedUnit_of_map_weakEquivalence
    (h : ∀ (A : C') (B : D') (f : G.obj (tC.obj A) ⟶ tD.obj B),
      WeakEquivalence f → WeakEquivalence (adj.homEquiv _ _ f)) :
    IsIso (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).unit := by
  let Φ := IsCofibrantApproximation.toLocalizerMorphism tC
  let Ψ := IsFibrantApproximation.toLocalizerMorphism tD
  apply (Φ.isIso_iff_of_hasLeftResolutions LC _).2
  intro A
  let T : Ψ.RightResolution (G.obj (tC.obj A)) := Classical.arbitrary _
  let w : G.obj (tC.obj A) ⟶ tD.obj T.X₁ := T.w
  have hw : WeakEquivalence w := ⟨T.hw⟩
  let : IsIso (LD.map w) := Localization.inverts LD (weakEquivalences D) w hw.mem
  have hw' := h A T.X₁ w hw
  let : IsIso (LC.map (adj.homEquiv _ _ w)) :=
    Localization.inverts LC (weakEquivalences C) _ hw'.mem
  let : IsIso (ε.app (tC.obj A)) := IsCofibrantApproximation.isIso_leftDerivedCounit_app
    tC (G ⋙ LD) (fun i ↦ Localization.inverts LD (weakEquivalences D) _
      (IsQuillenAdjunction.map_trivialCofibration (tC := tC) (tD := tD) (adj := adj) i).mem)
    LC LG ε A
  let : IsIso (η.app (tD.obj T.X₁)) := IsFibrantApproximation.isIso_rightDerivedUnit_app
    tD (F ⋙ LC) (fun p ↦ Localization.inverts LC (weakEquivalences C) _
      (IsQuillenAdjunction.map_trivialFibration (tC := tC) (tD := tD) (adj := adj) p).mem)
    LD RF η T.X₁
  have he := quillenDerivedAdjunction_homEquiv tC tD adj LC LD LG ε RF η
    (tC.obj A) (tD.obj T.X₁) w
  rw [Adjunction.homEquiv_unit] at he
  have hi : IsIso ((quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).unit.app
      (LC.obj (tC.obj A)) ≫ RF.map (ε.app (tC.obj A) ≫ LD.map w)) := by
    rw [he]
    infer_instance
  exact (isIso_comp_right_iff _ (RF.map (ε.app (tC.obj A) ≫ LD.map w))).1 hi

/-- The left fully faithful conclusion of Theorem 6.2.5(2). -/
noncomputable def fullyFaithful_quillenLeftDerived_of_map_weakEquivalence
    (h : ∀ (A : C') (B : D') (f : G.obj (tC.obj A) ⟶ tD.obj B),
      WeakEquivalence f → WeakEquivalence (adj.homEquiv _ _ f)) : LG.FullyFaithful := by
  let := isIso_quillenDerivedUnit_of_map_weakEquivalence tC tD adj LC LD LG ε RF η h
  exact (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).fullyFaithfulLOfIsIsoUnit

/-- The (4r) direction: if an adjoint is a weak equivalence, then so is
the original arrow. This makes the derived counit invertible. -/
theorem isIso_quillenDerivedCounit_of_adjoint_weakEquivalence
    (h : ∀ (A : C') (B : D') (f : G.obj (tC.obj A) ⟶ tD.obj B),
      WeakEquivalence (adj.homEquiv _ _ f) → WeakEquivalence f) :
    IsIso (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).counit := by
  let Φ := IsCofibrantApproximation.toLocalizerMorphism tC
  let Ψ := IsFibrantApproximation.toLocalizerMorphism tD
  apply (Ψ.isIso_iff_of_hasRightResolutions LD _).2
  intro B
  let T : Φ.LeftResolution (F.obj (tD.obj B)) := Classical.arbitrary _
  let p : tC.obj T.X₁ ⟶ F.obj (tD.obj B) := T.w
  have hp : WeakEquivalence p := ⟨T.hw⟩
  let : IsIso (LC.map p) := Localization.inverts LC (weakEquivalences C) p hp.mem
  let f := (adj.homEquiv _ _).symm p
  have hf : WeakEquivalence f := h T.X₁ B f (by simpa [f] using hp)
  let : IsIso (LD.map f) := Localization.inverts LD (weakEquivalences D) f hf.mem
  let : IsIso (ε.app (tC.obj T.X₁)) := IsCofibrantApproximation.isIso_leftDerivedCounit_app
    tC (G ⋙ LD) (fun i ↦ Localization.inverts LD (weakEquivalences D) _
      (IsQuillenAdjunction.map_trivialCofibration (tC := tC) (tD := tD) (adj := adj) i).mem)
    LC LG ε T.X₁
  let : IsIso (η.app (tD.obj B)) := IsFibrantApproximation.isIso_rightDerivedUnit_app
    tD (F ⋙ LC) (fun p ↦ Localization.inverts LC (weakEquivalences C) _
      (IsQuillenAdjunction.map_trivialFibration (tC := tC) (tD := tD) (adj := adj) p).mem)
    LD RF η B
  have he := quillenDerivedAdjunction_homEquiv_symm tC tD adj LC LD LG ε RF η
    (tC.obj T.X₁) (tD.obj B) p
  rw [Adjunction.homEquiv_counit] at he
  have hi : IsIso (LG.map (LC.map p ≫ η.app (tD.obj B)) ≫
      (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).counit.app
        (LD.obj (tD.obj B))) := by
    rw [he]
    exact inferInstanceAs (IsIso (ε.app (tC.obj T.X₁) ≫ LD.map f))
  exact (isIso_comp_left_iff (LG.map (LC.map p ≫ η.app (tD.obj B))) _).1 hi

/-- The right fully faithful conclusion of Theorem 6.2.5(2). -/
noncomputable def fullyFaithful_quillenRightDerived_of_adjoint_weakEquivalence
    (h : ∀ (A : C') (B : D') (f : G.obj (tC.obj A) ⟶ tD.obj B),
      WeakEquivalence (adj.homEquiv _ _ f) → WeakEquivalence f) : RF.FullyFaithful := by
  let := isIso_quillenDerivedCounit_of_adjoint_weakEquivalence tC tD adj LC LD LG ε RF η h
  exact (quillenDerivedAdjunction tC tD adj LC LD LG ε RF η).fullyFaithfulROfIsIsoCounit

/-- Definition 6.2.4(4), in addition to the specified Quillen adjunction:
weak equivalences between approximation images correspond under adjunction. -/
class IsQuillenEquivalence : Prop where
  weakEquivalence_iff (A : C') (B : D') (f : G.obj (tC.obj A) ⟶ tD.obj B) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv _ _ f)

/-- Theorem 6.2.5(3): the two derived functors of a Quillen equivalence
are inverse equivalences of categories. -/
noncomputable def quillenDerivedEquivalence [IsQuillenEquivalence tC tD adj] : HC ≌ HD := by
  let d := quillenDerivedAdjunction tC tD adj LC LD LG ε RF η
  let : IsIso d.unit := isIso_quillenDerivedUnit_of_map_weakEquivalence
    tC tD adj LC LD LG ε RF η
    (fun A B f ↦ (IsQuillenEquivalence.weakEquivalence_iff
      (tC := tC) (tD := tD) (adj := adj) A B f).1)
  let : IsIso d.counit := isIso_quillenDerivedCounit_of_adjoint_weakEquivalence
    tC tD adj LC LD LG ε RF η
    (fun A B f ↦ (IsQuillenEquivalence.weakEquivalence_iff
      (tC := tC) (tD := tD) (adj := adj) A B f).2)
  exact d.toEquivalence

include tC tD adj LC LD ε RF η in
/-- The total left derived functor in a Quillen equivalence is an equivalence. -/
theorem isEquivalence_quillenLeftDerived [IsQuillenEquivalence tC tD adj] :
    LG.IsEquivalence :=
  (quillenDerivedEquivalence tC tD adj LC LD LG ε RF η).isEquivalence_functor

include tC tD adj LC LD LG ε η in
/-- The total right derived functor in a Quillen equivalence is an equivalence. -/
theorem isEquivalence_quillenRightDerived [IsQuillenEquivalence tC tD adj] :
    RF.IsEquivalence :=
  (quillenDerivedEquivalence tC tD adj LC LD LG ε RF η).isEquivalence_inverse

end ABCCofibrations

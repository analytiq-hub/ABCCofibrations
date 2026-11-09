/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.DerivedAbsoluteness
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Quillen adjunctions relative to approximations

Definition 6.2.4(1)–(3) and Theorem 6.2.5(1). The derived adjunction uses
mathlib's implementation of Maltsiniotis's argument, after proving the
required preservation of derived functors under postcomposition.
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

/-- Definition 6.2.4(1)–(3), relative to specified approximations. The
adjunction and approximation hypotheses are parameters; the two preservation
conditions are the additional requirements. -/
class IsQuillenAdjunction (adj : G ⊣ F) : Prop where
  map_trivialCofibration {A B : C'} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i] :
    WeakEquivalence (G.map (tC.map i))
  map_trivialFibration {A B : D'} (p : A ⟶ B) [Fibration p] [WeakEquivalence p] :
    WeakEquivalence (F.map (tD.map p))

variable (adj : G ⊣ F) [IsQuillenAdjunction tC tD adj]
  {HC HD : Type*} [Category HC] [Category HD]
  (LC : C ⥤ HC) [LC.IsLocalization (weakEquivalences C)]
  (LD : D ⥤ HD) [LD.IsLocalization (weakEquivalences D)]

/-- Theorem 6.2.5(1) for arbitrary choices of the two total derived functors.
The postcomposition assumptions required by Maltsiniotis's argument are
consequences of the Quillen hypotheses. -/
noncomputable def quillenDerivedAdjunction
    (LG : HC ⥤ HD) (ε : LC ⋙ LG ⟶ G ⋙ LD)
    [LG.IsLeftDerivedFunctor ε (weakEquivalences C)]
    (RF : HD ⥤ HC) (η : F ⋙ LC ⟶ LD ⋙ RF)
    [RF.IsRightDerivedFunctor η (weakEquivalences D)] : LG ⊣ RF := by
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
  exact adj.derived (weakEquivalences C) (weakEquivalences D) ε η

include tC tD adj in
/-- Existence of a pair of total derived functors forming an adjunction. -/
theorem exists_quillenDerivedAdjunction :
    ∃ (LG : HC ⥤ HD) (ε : LC ⋙ LG ⟶ G ⋙ LD)
      (RF : HD ⥤ HC) (η : F ⋙ LC ⟶ LD ⋙ RF),
      LG.IsLeftDerivedFunctor ε (weakEquivalences C) ∧
      RF.IsRightDerivedFunctor η (weakEquivalences D) ∧ Nonempty (LG ⊣ RF) := by
  obtain ⟨LG, ε, hLG, _⟩ :=
    IsCofibrantApproximation.exists_totalLeftDerivedFunctor_of_map_trivialCofibrations
      tC G (fun i ↦ IsQuillenAdjunction.map_trivialCofibration
        (tC := tC) (tD := tD) (adj := adj) i) LC LD
  obtain ⟨RF, η, hRF, _⟩ :=
    IsFibrantApproximation.exists_totalRightDerivedFunctor_of_map_trivialFibrations
      tD F (fun p ↦ IsQuillenAdjunction.map_trivialFibration
        (tC := tC) (tD := tD) (adj := adj) p) LD LC
  let := hLG
  let := hRF
  exact ⟨LG, ε, RF, η, hLG, hRF, ⟨quillenDerivedAdjunction tC tD adj LC LD LG ε RF η⟩⟩

end ABCCofibrations

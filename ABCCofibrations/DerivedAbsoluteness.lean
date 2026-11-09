/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximationDerived
public import ABCCofibrations.FibrantApproximation
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Preservation of derived functors under arbitrary postcomposition

A derivability structure on which the original functor inverts weak
equivalences makes any derived functor absolute. This supplies the precise
postcomposition hypotheses in Maltsiniotis's derived-adjunction argument.
-/

@[expose] public section

open CategoryTheory

namespace ABCCofibrations

variable {C₁ C₂ D H E : Type*} [Category C₁] [Category C₂] [Category D]
  [Category H] [Category E] {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂) (F : C₂ ⥤ H) (hF : Φ.Derives F)
  (L : C₂ ⥤ D) [L.IsLocalization W₂]

include hF

/-- A left derived functor computed by a left derivability structure is
preserved by any postcomposition, with its whiskered counit. -/
theorem isLeftDerivedFunctor_postcomp_of_derives [Φ.IsLeftDerivabilityStructure]
    (LF : D ⥤ H) (ε : L ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor ε W₂]
    (K : H ⥤ E) : (LF ⋙ K).IsLeftDerivedFunctor
      ((Functor.associator L LF K).inv ≫ Functor.whiskerRight ε K) W₂ := by
  have hK : Φ.Derives (F ⋙ K) := by
    intro X Y f hf
    let := hF f hf
    exact inferInstanceAs (IsIso (K.map ((Φ.functor ⋙ F).map f)))
  apply hK.isLeftDerivedFunctor_of_isIso
  intro X
  let := hF.isIso' ε X
  simpa only [NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp] using
      (inferInstanceAs (IsIso (K.map (ε.app (Φ.functor.obj X)))))

/-- The dual statement: right derived functors computed by a right
derivability structure are preserved by arbitrary postcomposition. -/
theorem isRightDerivedFunctor_postcomp_of_derives [Φ.IsRightDerivabilityStructure]
    (RF : D ⥤ H) (η : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor η W₂]
    (K : H ⥤ E) : (RF ⋙ K).IsRightDerivedFunctor
      (Functor.whiskerRight η K ≫ (Functor.associator L RF K).hom) W₂ := by
  have hK : Φ.Derives (F ⋙ K) := by
    intro X Y f hf
    let := hF f hf
    exact inferInstanceAs (IsIso (K.map ((Φ.functor ⋙ F).map f)))
  apply hK.isRightDerivedFunctor_of_isIso
  intro X
  let := hF.isIso_of_isRightDerivedFunctor η X
  simpa only [NatTrans.comp_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Category.comp_id] using
      (inferInstanceAs (IsIso (K.map (η.app (Φ.functor.obj X)))))

end ABCCofibrations

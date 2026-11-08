/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReplacementFunctor

/-!
# Comparison isomorphisms for cofibrant replacements

The replacement functor restricted to cofibrant objects recovers their
localization. Lifting this isomorphism gives a left inverse to the ambient
comparison. The comparison in the other direction remains to be proved.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra CategoryTheory.Functor

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- The reverse localization functor is a left inverse to the ambient
comparison, up to a natural isomorphism. -/
noncomputable def cofibrantLocalizationReplacementIso
    (Q : C → CofibrantObject C) (q : ∀ A, (Q A).obj ⟶ A)
    (hq : ∀ A, WeakEquivalence (q A)) :
    cofibrantLocalizationToAmbient ⋙ ambientLocalizationToCofibrant Q q hq ≅
      𝟭 (weakEquivalences (CofibrantObject C)).Localization := by
  let L := (weakEquivalences C).Q
  let F := (weakEquivalences (CofibrantObject C)).Q
  let hF := (inverts_weakEquivalences_iff_inverts_trivialCofibrations F).1
    (weakEquivalences (CofibrantObject C)).Q_inverts
  let R := replacementFunctor Q q hq F hF
  let hR := replacementFunctor_inverts Q q hq F hF
  let H := Localization.lift R hR L
  let Φ := cofibrantInclusionLocalizerMorphism (C := C)
  let K := Φ.localizedFunctor F L
  change K ⋙ H ≅ 𝟭 _
  let eK : F ⋙ K ≅ Φ.functor ⋙ L :=
    Localization.Lifting.iso F (weakEquivalences (CofibrantObject C)) _ _
  let eH : L ⋙ H ≅ R := Localization.fac R hR L
  let : Localization.Lifting F (weakEquivalences (CofibrantObject C))
      (CofibrantObject.ι ⋙ R) (K ⋙ H) := ⟨
    (Functor.associator F K H).symm ≪≫ isoWhiskerRight eK H ≪≫
      Functor.associator Φ.functor L H ≪≫ isoWhiskerLeft Φ.functor eH⟩
  exact Localization.liftNatIso F (weakEquivalences (CofibrantObject C))
    (CofibrantObject.ι ⋙ R) F (K ⋙ H) (𝟭 _)
    (replacementFunctorRestrictionIso Q q hq F hF)

/-- The ambient comparison is faithful. Cofibrant replacements exist for
every object, so the left inverse can be used without extra assumptions. -/
instance cofibrantLocalizationToAmbient_faithful :
    (cofibrantLocalizationToAmbient (C := C)).Faithful := by
  let R (A : C) : (cofibrantInclusionLocalizerMorphism (C := C)).LeftResolution A :=
    Classical.choice (cofibrantInclusion_hasLeftResolutions A)
  let Q (A : C) := (R A).X₁
  let q (A : C) : (Q A).obj ⟶ A := (R A).w
  have hq (A : C) : WeakEquivalence (q A) := ⟨(R A).hw⟩
  exact Functor.Faithful.of_comp_iso (cofibrantLocalizationReplacementIso Q q hq)

end ABCCofibrations.ABCPrecofibrationCategory

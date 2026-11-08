/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.HomotopyCategory
public import Mathlib.CategoryTheory.Localization.Quotient

/-!
# Comparing left-homotopy classes with localization

Any functor on cofibrant objects which inverts weak equivalences identifies
left-homotopic maps. Consequently it factors through `LeftHomotopyCategory`,
and the quotient category has a canonical comparison functor to localization.

This construction does not assert that the comparison is faithful or an
equivalence, or that the quotient functor itself is a localization.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type w} [Category D]

/-- Every weak-equivalence-inverting functor on cofibrant objects identifies
left-homotopic maps. The cylinder projection identifies its two endpoints,
and the target enlargement can then be cancelled. -/
theorem map_eq_of_cofibrant_leftHomotopy
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F)
    {X Y : CofibrantObject C} {f g : X ⟶ Y}
    (h : cofibrantLeftHomotopyRel f g) : F.map f = F.map g := by
  let := hasBinaryCoproduct X.obj X.obj
  change LeftHomotopyRel f.hom g.hom at h
  obtain ⟨Y', b, hb, hbw, P, hP, ⟨H⟩⟩ := h
  let := hb
  let := hP
  let := cylinder_cofibrant P
  let := cofibrant_target b
  let i₀ : X ⟶ CofibrantObject.mk P.I := CofibrantObject.homMk P.i₀
  let i₁ : X ⟶ CofibrantObject.mk P.I := CofibrantObject.homMk P.i₁
  let p : CofibrantObject.mk P.I ⟶ X := CofibrantObject.homMk P.π
  let b' : Y ⟶ CofibrantObject.mk Y' := CofibrantObject.homMk b
  let H' : CofibrantObject.mk P.I ⟶ CofibrantObject.mk Y' :=
    CofibrantObject.homMk H.h
  have hp : weakEquivalences (CofibrantObject C) p := by
    change weakEquivalences C P.π
    exact (inferInstance : WeakEquivalence P.π).mem
  have hbw' : weakEquivalences (CofibrantObject C) b' := by
    change weakEquivalences C b
    exact hbw.mem
  let := hF p hp
  let := hF b' hbw'
  have hi₀ : i₀ ≫ p = 𝟙 X := by ext; exact P.i₀_π
  have hi₁ : i₁ ≫ p = 𝟙 X := by ext; exact P.i₁_π
  have hi : F.map i₀ = F.map i₁ := by
    apply (cancel_mono (F.map p)).1
    rw [← F.map_comp, ← F.map_comp, hi₀, hi₁]
  have h₀ : i₀ ≫ H' = f ≫ b' := by ext; exact H.h₀
  have h₁ : i₁ ≫ H' = g ≫ b' := by ext; exact H.h₁
  apply (cancel_mono (F.map b')).1
  rw [← F.map_comp, ← F.map_comp, ← h₀, ← h₁, F.map_comp, F.map_comp, hi]

/-- Factor a weak-equivalence-inverting functor through left-homotopy classes. -/
noncomputable def liftFromLeftHomotopyCategory
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F) :
    LeftHomotopyCategory C ⥤ D :=
  CategoryTheory.Quotient.lift _ F
    (fun _ _ _ _ h ↦ map_eq_of_cofibrant_leftHomotopy F hF h)

/-- The factorization through homotopy classes recovers the original functor. -/
theorem liftFromLeftHomotopyCategory_fac
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F) :
    toLeftHomotopyCategory ⋙ liftFromLeftHomotopyCategory F hF = F :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The factorization through homotopy classes is unique. -/
theorem liftFromLeftHomotopyCategory_unique
    (F : CofibrantObject C ⥤ D)
    (hF : (weakEquivalences (CofibrantObject C)).IsInvertedBy F)
    (G : LeftHomotopyCategory C ⥤ D) (hG : toLeftHomotopyCategory ⋙ G = F) :
    G = liftFromLeftHomotopyCategory F hF :=
  CategoryTheory.Quotient.lift_unique _ _ _ G hG

/-- The canonical comparison from left-homotopy classes to localization at
weak equivalences of cofibrant objects. -/
noncomputable def leftHomotopyCategoryToLocalization :
    LeftHomotopyCategory C ⥤ (weakEquivalences (CofibrantObject C)).Localization :=
  liftFromLeftHomotopyCategory _ (weakEquivalences (CofibrantObject C)).Q_inverts

/-- The comparison agrees with localization on representatives. -/
theorem leftHomotopyCategoryToLocalization_fac :
    toLeftHomotopyCategory ⋙ leftHomotopyCategoryToLocalization (C := C) =
      (weakEquivalences (CofibrantObject C)).Q :=
  liftFromLeftHomotopyCategory_fac _ _

end ABCCofibrations.ABCPrecofibrationCategory

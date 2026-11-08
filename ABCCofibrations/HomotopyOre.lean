/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Cylinder
public import ABCCofibrations.HomotopyCancellation
public import ABCCofibrations.HomotopyWeakEquivalences
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# The homotopy Ore condition

Theorem 6.4.3(1)(a): a weak equivalence out of a cofibrant object can be
completed to a strictly homotopy-commutative square whose new leg is a weak
equivalence. On the left-homotopy quotient this is an honest Ore square, and
with the cancellation already proved it gives a left calculus of fractions.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]

/-- Complete a span `A ⟶ B`, `A ⟶ A'` in which the second leg is a weak
equivalence (Theorem 6.4.3(1)(a)). The resulting square is strictly left
homotopic, and the new leg out of `B` is a weak equivalence. -/
theorem exists_strict_homotopy_ore {A A' B : C} [IsCofibrant A] [IsCofibrant A']
    [IsCofibrant B] [HasBinaryCoproduct A A] (f : A ⟶ B) (a : A ⟶ A') [WeakEquivalence a] :
    ∃ (B' : C) (bottom : A' ⟶ B') (b : B ⟶ B'),
      IsCofibrant B' ∧ WeakEquivalence b ∧
      StrictLeftHomotopyRel (a ≫ bottom) (f ≫ b) := by
  obtain ⟨P, hP⟩ := exists_good_cylinder A
  let := hP
  let := coprod_cofibrant (A := A) (B := A)
  let := hasBinaryCoproduct A B
  let := coprod_cofibrant (A := A) (B := B)
  let := cofibration_cylinder_i₁ P
  let := weakEquivalence_cylinder_i₁ P
  let := cylinder_cofibrant P
  let F := pushout.inl P.i₁ f
  let b₁ := pushout.inr P.i₁ f
  have hcomm : P.i₁ ≫ F = f ≫ b₁ := pushout.condition
  let Fi₀ := P.i₀ ≫ F
  let := cofibration_cylinder_pushout_inl_i₁ P f
  let := cofibrant_target Fi₀
  let b₂ := pushout.inl Fi₀ a
  let bottom := pushout.inr Fi₀ a
  let := weakEquivalence_pushout_inl Fi₀ a
  let := weakEquivalence_of_isPushout (IsPushout.of_hasPushout P.i₁ f)
  let := cofibration_of_isPushout (IsPushout.of_hasPushout Fi₀ a)
  let := cofibrant_target bottom
  let b := b₁ ≫ b₂
  refine ⟨pushout Fi₀ a, bottom, b, inferInstance, inferInstance, ?_⟩
  refine ⟨P, hP, ⟨?_⟩⟩
  exact
    { h := F ≫ b₂
      h₀ := by rw [← Category.assoc, pushout.condition]
      h₁ := by
        change P.i₁ ≫ (F ≫ b₂) = f ≫ (b₁ ≫ b₂)
        rw [← Category.assoc, hcomm, Category.assoc] }

/-- The weak equivalences of the left-homotopy quotient satisfy the left
calculus of fractions. Ore squares come from Theorem 6.4.3(1)(a), and the
extensionality axiom is precomposition cancellation with an identity denominator. -/
instance weakEquivalences_leftHomotopyCategory_hasLeftCalculusOfFractions :
    (weakEquivalences (LeftHomotopyCategory C)).HasLeftCalculusOfFractions where
  exists_leftFraction := by
    intro X Y φ
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨S, s, hs, f, rfl⟩ := φ.cases
    obtain ⟨S⟩ := S
    obtain ⟨s, rfl⟩ := (toLeftHomotopyCategory (C := C)).map_surjective s
    obtain ⟨f, rfl⟩ := (toLeftHomotopyCategory (C := C)).map_surjective f
    have hsw : WeakEquivalence s.hom :=
      (weakEquivalence_toLeftHomotopyCategory_map_iff s).1 ((weakEquivalence_iff _).2 hs)
    let := hsw
    let := hasBinaryCoproduct S.obj S.obj
    obtain ⟨B', bottom, b, hB', hb, hhom⟩ := exists_strict_homotopy_ore f.hom s.hom
    let := hB'
    let Z : CofibrantObject C := CofibrantObject.mk B'
    let bottom' : X ⟶ Z := CofibrantObject.homMk bottom
    let b' : Y ⟶ Z := CofibrantObject.homMk b
    have hW : weakEquivalences (LeftHomotopyCategory C)
        ((toLeftHomotopyCategory (C := C)).map b') :=
      (weakEquivalence_iff _).1 ((weakEquivalence_toLeftHomotopyCategory_map_iff b').2 hb)
    refine ⟨⟨(toLeftHomotopyCategory (C := C)).map bottom',
      (toLeftHomotopyCategory (C := C)).map b', hW⟩, ?_⟩
    have he : (toLeftHomotopyCategory (C := C)).map (s ≫ bottom') =
        (toLeftHomotopyCategory (C := C)).map (f ≫ b') :=
      (toLeftHomotopyCategory_map_eq_iff _ _).2 (LeftHomotopyRel.of_strict hhom)
    exact he.symm
  ext := by
    rintro ⟨X'⟩ ⟨X⟩ ⟨Y⟩ f₁ f₂ s hs h
    obtain ⟨f₁, rfl⟩ := (toLeftHomotopyCategory (C := C)).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (toLeftHomotopyCategory (C := C)).map_surjective f₂
    obtain ⟨s, rfl⟩ := (toLeftHomotopyCategory (C := C)).map_surjective s
    have hsw : WeakEquivalence s.hom :=
      (weakEquivalence_toLeftHomotopyCategory_map_iff s).1 ((weakEquivalence_iff _).2 hs)
    let := hsw
    let := hasBinaryCoproduct X'.obj X'.obj
    have hpre : LeftHomotopyRel (s.hom ≫ f₁.hom) (s.hom ≫ f₂.hom) :=
      (toLeftHomotopyCategory_map_eq_iff (s ≫ f₁) (s ≫ f₂)).1 h
    let := hasBinaryCoproduct X.obj X.obj
    have hcancel :=
      LeftHomotopyRel.of_precomp_weakEquivalence (f := f₁.hom) (g := f₂.hom) s.hom hpre
    refine ⟨(toLeftHomotopyCategory (C := C)).obj Y, 𝟙 _,
      (weakEquivalences (LeftHomotopyCategory C)).id_mem _, ?_⟩
    have he := (toLeftHomotopyCategory_map_eq_iff f₁ f₂).2 hcancel
    exact congrArg (· ≫ 𝟙 _) he


end ABCCofibrations.ABCPrecofibrationCategory

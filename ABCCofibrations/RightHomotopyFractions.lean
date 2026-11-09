/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.RightHomotopyCancellation
public import ABCCofibrations.AmbientHomotopyFractions

/-!
# Fractions in a prefibration-category localization

Right fractions between fibrant objects are obtained by dualizing the
ambient left-fraction representation. Common-denominator equality is
expressed using native right homotopy.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type*} [Category D]

/-- The mixed-object version of the chosen opposite coproduct/product
comparison, used for full fraction boundaries. -/
noncomputable def oppositeCoprodProductIsoPair (X Y : C) [HasBinaryProduct X Y]
    [HasBinaryCoproduct (Opposite.op X) (Opposite.op Y)] :
    (Opposite.op X ⨿ Opposite.op Y).unop ≅ X ⨯ Y where
  hom := prod.lift
    (coprod.inl : Opposite.op X ⟶ Opposite.op X ⨿ Opposite.op Y).unop
    (coprod.inr : Opposite.op Y ⟶ Opposite.op X ⨿ Opposite.op Y).unop
  inv := (coprod.desc (prod.fst : X ⨯ Y ⟶ X).op (prod.snd : X ⨯ Y ⟶ Y).op).unop
  hom_inv_id := by
    apply Quiver.Hom.op_inj
    rw [op_comp]
    apply coprod.hom_ext <;> simp [← op_comp]
  inv_hom_id := by
    apply prod.hom_ext <;> simp [← unop_comp]

/-- Theorem 6.4.5(2)(a): the numerator and the full product boundary can
both be fibrations, and the denominator a trivial fibration. -/
theorem exists_ambient_fibration_fraction_with_prod
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B : C} [IsFibrant A] [IsFibrant B] [HasBinaryProduct B A]
    (α : L.obj A ⟶ L.obj B) :
    ∃ (Z : C) (s : Z ⟶ A) (f : Z ⟶ B),
      IsFibrant Z ∧ Fibration s ∧ WeakEquivalence s ∧ Fibration f ∧
        Fibration (prod.lift f s) ∧ L.map s ≫ α = L.map f := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op A)
  let : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  obtain ⟨Z, f, s, hZ, hf, hs, hw, hb, he⟩ :=
    ABCPrecofibrationCategory.exists_ambient_cofibration_fraction_with_coprod L.op α.op
  let e := oppositeCoprodProductIsoPair B A
  let := prod_fibrant (A := B) (B := A)
  let := fibration_of_isIso e.hom
  let : Fibration (coprod.desc f s).unop := (fibration_unop_iff _).2 hb
  have hp : Fibration (prod.lift f.unop s.unop) := by
    have eq : (coprod.desc f s).unop ≫ e.hom = prod.lift f.unop s.unop := by
      apply prod.hom_ext <;> simp [e, oppositeCoprodProductIsoPair, ← unop_comp]
    rw [← eq]
    exact inferInstanceAs (Fibration ((coprod.desc f s).unop ≫ e.hom))
  refine ⟨Z.unop, s.unop, f.unop, (isFibrant_iff_isCofibrant_op Z.unop).2 hZ,
    (fibration_unop_iff s).2 hs, (weakEquivalences_unop_iff s).2 hw,
    (fibration_unop_iff f).2 hf, hp, ?_⟩
  simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op] using
    congrArg Quiver.Hom.unop he

/-- Theorem 6.4.4(2)(a), with a trivial-fibration denominator: every localized
arrow between fibrant objects is represented by a right fraction. -/
theorem exists_ambient_trivialFibration_fraction
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B : C} [IsFibrant A] [IsFibrant B] (α : L.obj A ⟶ L.obj B) :
    ∃ (Z : C) (s : Z ⟶ A) (f : Z ⟶ B),
      IsFibrant Z ∧ Fibration s ∧ WeakEquivalence s ∧ L.map s ≫ α = L.map f := by
  let : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  obtain ⟨Z, f, s, hZ, hs, hw, he⟩ :=
    ABCPrecofibrationCategory.exists_ambient_trivialCofibration_fraction L.op α.op
  refine ⟨Z.unop, s.unop, f.unop, (isFibrant_iff_isCofibrant_op Z.unop).2 hZ,
    (fibration_unop_iff s).2 hs, (weakEquivalences_unop_iff s).2 hw, ?_⟩
  simpa only [unop_comp, Functor.op_map, Quiver.Hom.unop_op] using
    congrArg Quiver.Hom.unop he

/-- For a fixed common weak-equivalence denominator, equality of right
fractions is detected by right homotopy of their numerators. -/
theorem ambient_common_rightFraction_eq_iff_rightHomotopy
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B Z : C} [IsFibrant B] [IsFibrant Z] [HasBinaryProduct B B]
    (s : Z ⟶ A) [WeakEquivalence s] (f g : Z ⟶ B)
    (α β : L.obj A ⟶ L.obj B)
    (hα : L.map s ≫ α = L.map f) (hβ : L.map s ≫ β = L.map g) :
    α = β ↔ RightHomotopyRel f g := by
  let := Localization.inverts L (weakEquivalences C) s
    (show WeakEquivalence s from inferInstance).mem
  rw [← cancel_epi (L.map s), hα, hβ]
  exact ambient_map_eq_iff_fibrant_rightHomotopy L f g

/-- Theorem 6.4.4(2)(b): two fractions with arbitrary weak-equivalence
denominators agree exactly when they have common weak-equivalence
refinements with both triangles commuting up to right homotopy. -/
theorem ambient_rightFraction_eq_iff_exists_rightHomotopy
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]
    {A B Z₁ Z₂ : C} [IsFibrant A] [IsFibrant B] [IsFibrant Z₁] [IsFibrant Z₂]
    [HasBinaryProduct A A] [HasBinaryProduct B B]
    (s : Z₁ ⟶ A) (t : Z₂ ⟶ A) [WeakEquivalence s] [WeakEquivalence t]
    (f : Z₁ ⟶ B) (g : Z₂ ⟶ B) (α β : L.obj A ⟶ L.obj B)
    (hα : L.map s ≫ α = L.map f) (hβ : L.map t ≫ β = L.map g) :
    α = β ↔ ∃ (P : C) (i : P ⟶ Z₁) (j : P ⟶ Z₂),
      IsFibrant P ∧ WeakEquivalence i ∧ WeakEquivalence j ∧
        RightHomotopyRel (i ≫ s) (j ≫ t) ∧ RightHomotopyRel (i ≫ f) (j ≫ g) := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op A) (Opposite.op A)
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  let : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  let φ : (weakEquivalences (CofibrantObject Cᵒᵖ)).LeftFraction
      (CofibrantObject.mk (Opposite.op B)) (CofibrantObject.mk (Opposite.op A)) := {
    Y' := CofibrantObject.mk (Opposite.op Z₁)
    f := CofibrantObject.homMk f.op
    s := CofibrantObject.homMk s.op
    hs := (show WeakEquivalence s.op from inferInstance).mem }
  let ψ : (weakEquivalences (CofibrantObject Cᵒᵖ)).LeftFraction
      (CofibrantObject.mk (Opposite.op B)) (CofibrantObject.mk (Opposite.op A)) := {
    Y' := CofibrantObject.mk (Opposite.op Z₂)
    f := CofibrantObject.homMk g.op
    s := CofibrantObject.homMk t.op
    hs := (show WeakEquivalence t.op from inferInstance).mem }
  let H := CofibrantObject.ι ⋙ L.op
  let hH := Localization.inverts H (weakEquivalences (CofibrantObject Cᵒᵖ))
  have hφ : ABCPrecofibrationCategory.ambientWeakEquivalenceFractionMap L.op φ = α.op := by
    change φ.map H hH = α.op
    let := hH _ φ.hs
    apply (cancel_mono (H.map φ.s)).1
    rw [φ.map_comp_map_s H hH]
    exact (congrArg Quiver.Hom.op hα).symm
  have hψ : ABCPrecofibrationCategory.ambientWeakEquivalenceFractionMap L.op ψ = β.op := by
    change ψ.map H hH = β.op
    let := hH _ ψ.hs
    apply (cancel_mono (H.map ψ.s)).1
    rw [ψ.map_comp_map_s H hH]
    exact (congrArg Quiver.Hom.op hβ).symm
  have he := ABCPrecofibrationCategory.ambient_weakEquivalence_fraction_map_eq_iff_exists_leftHomotopy
    L.op φ ψ
  rw [hφ, hψ] at he
  constructor
  · intro h
    obtain ⟨P, i, j, hi, hj, hs, hf⟩ := he.1 (congrArg Quiver.Hom.op h)
    refine ⟨P.obj.unop, i.hom.unop, j.hom.unop,
      (isFibrant_iff_isCofibrant_op P.obj.unop).2 P.property,
      (weakEquivalences_unop_iff i.hom).2 ⟨hi⟩,
      (weakEquivalences_unop_iff j.hom).2 ⟨hj⟩, ?_, ?_⟩
    · exact (rightHomotopy_iff_op _ _).2 hs
    · exact (rightHomotopy_iff_op _ _).2 hf
  · rintro ⟨P, i, j, hP, hi, hj, hs, hf⟩
    let := hP
    apply Quiver.Hom.op_inj
    apply he.2
    refine ⟨CofibrantObject.mk (Opposite.op P), CofibrantObject.homMk i.op,
      CofibrantObject.homMk j.op, (weakEquivalences_op_iff i).2 hi |>.mem,
      (weakEquivalences_op_iff j).2 hj |>.mem, ?_, ?_⟩
    · exact (rightHomotopy_iff_op _ _).1 hs
    · exact (rightHomotopy_iff_op _ _).1 hf

end ABCCofibrations.ABCPrefibrationCategory

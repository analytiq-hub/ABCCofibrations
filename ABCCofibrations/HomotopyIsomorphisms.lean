/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.AmbientHomotopyFractions
public import ABCCofibrations.ReplacementComparison
public import ABCCofibrations.FibrationBasic
public import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Isomorphisms in the homotopy category (Lemma 7.2.1, Proposition 7.2.9)

Lemma 7.2.1(1) (Cisinski): a map `f : A ⟶ B` between cofibrant objects has a left
inverse in the homotopy category iff some cofibration `f' : B ⟶ B'` makes `f'f`
a weak equivalence, and is an isomorphism there iff two such cofibrations exist
in succession. The proof writes a left inverse as a fraction (Theorem 6.4.5(1)),
compares in the homotopy category of cofibrant objects (Theorem 6.4.4(1)(c)),
and uses homotopy invariance of weak equivalences.

Proposition 7.2.9(1): in a precofibration category, a map with the right lifting
property with respect to all cofibrations becomes an isomorphism in the
homotopy category. The fibration statements (2) follow in the opposite category.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- Two out of six for isomorphisms: if `a ≫ b` and `b ≫ c` are isomorphisms, so
is `b`. -/
theorem isIso_of_isIso_comp_of_isIso_comp {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) [IsIso (a ≫ b)] [IsIso (b ≫ c)] : IsIso b := by
  have hx : (inv (a ≫ b) ≫ a) ≫ b = 𝟙 _ := by rw [Category.assoc, IsIso.inv_hom_id]
  have hy : b ≫ (c ≫ inv (b ≫ c)) = 𝟙 _ := by rw [← Category.assoc, IsIso.hom_inv_id]
  have hxy : inv (a ≫ b) ≫ a = c ≫ inv (b ≫ c) :=
    calc inv (a ≫ b) ≫ a = (inv (a ≫ b) ≫ a) ≫ (b ≫ (c ≫ inv (b ≫ c))) := by
          rw [hy, Category.comp_id]
      _ = ((inv (a ≫ b) ≫ a) ≫ b) ≫ (c ≫ inv (b ≫ c)) := by simp only [Category.assoc]
      _ = c ≫ inv (b ≫ c) := by rw [hx, Category.id_comp]
  exact ⟨c ≫ inv (b ≫ c), hy, by rw [← hxy, hx]⟩

namespace ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Proposition 7.2.9(1).** A map with the right lifting property with respect
to all cofibrations becomes an isomorphism in the homotopy category. -/
theorem isIso_map_of_hasLiftingProperty {X Y : C} (p : X ⟶ Y)
    (hp : ∀ ⦃A B : C⦄ (i : A ⟶ B), Cofibration i → HasLiftingProperty i p) :
    IsIso (L.map p) := by
  obtain ⟨A, r, hA, hr⟩ := exists_cofibrant_replacement X
  have := hA
  obtain ⟨B, i, r', hi, hr', hfac⟩ := factorization (r ≫ p)
  have := hp i hi
  have sq : CommSq r i p r' := ⟨hfac.symm⟩
  have := Localization.inverts L (weakEquivalences C) r hr.mem
  have := Localization.inverts L (weakEquivalences C) r' hr'.mem
  have : IsIso (L.map i ≫ L.map sq.lift) := by rw [← L.map_comp, sq.fac_left]; infer_instance
  have : IsIso (L.map sq.lift ≫ L.map p) := by rw [← L.map_comp, sq.fac_right]; infer_instance
  have := isIso_of_isIso_comp_of_isIso_comp (L.map i) (L.map sq.lift) (L.map p)
  rw [show L.map p = inv (L.map sq.lift) ≫ (L.map sq.lift ≫ L.map p) by simp]
  infer_instance

/-- **Lemma 7.2.1(1)(a)** (Cisinski). A map `f : A ⟶ B` between cofibrant objects
has a left inverse in the homotopy category iff there is a cofibration
`f' : B ⟶ B'` with `f'f` a weak equivalence. -/
theorem exists_leftInverse_iff {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B) :
    (∃ g : L.obj B ⟶ L.obj A, L.map f ≫ g = 𝟙 _) ↔
      ∃ (B' : C) (f' : B ⟶ B'), Cofibration f' ∧ WeakEquivalence (f ≫ f') := by
  constructor
  · rintro ⟨g, hg⟩
    let := hasBinaryCoproduct B A
    obtain ⟨Z, i, s, hZ, hi, -, hs, -, h⟩ := exists_ambient_cofibration_fraction_with_coprod L g
    have := hZ
    have heq : L.map (f ≫ i) = L.map s := by rw [L.map_comp, ← h, ← Category.assoc, hg,
      Category.id_comp]
    have hrel := (ambient_map_eq_iff_cofibrant_leftHomotopy L
      (X := CofibrantObject.mk A) (Y := CofibrantObject.mk Z)
      (CofibrantObject.homMk (f ≫ i)) (CofibrantObject.homMk s)).1 heq
    let := hasBinaryCoproduct A A
    exact ⟨Z, i, hi, (LeftHomotopyRel.weakEquivalence_iff hrel).2 hs⟩
  · rintro ⟨B', f', -, hw⟩
    have := Localization.inverts L (weakEquivalences C) _ hw.mem
    exact ⟨L.map f' ≫ inv (L.map (f ≫ f')), by rw [← Category.assoc, ← L.map_comp,
      IsIso.hom_inv_id]⟩

/-- **Lemma 7.2.1(1)(b)** (Cisinski). A map `f : A ⟶ B` between cofibrant objects
is an isomorphism in the homotopy category iff there are cofibrations
`f' : B ⟶ B'` and `f'' : B' ⟶ B''` with `f'f` and `f''f'` weak equivalences. -/
theorem isIso_map_iff {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B) :
    IsIso (L.map f) ↔ ∃ (B' B'' : C) (f' : B ⟶ B') (f'' : B' ⟶ B''), Cofibration f' ∧
      Cofibration f'' ∧ WeakEquivalence (f ≫ f') ∧ WeakEquivalence (f' ≫ f'') := by
  constructor
  · intro _
    obtain ⟨B', f', hf', hw⟩ := (exists_leftInverse_iff L f).1 ⟨inv (L.map f), by simp⟩
    have := hf'
    have := cofibrant_target f'
    have := Localization.inverts L (weakEquivalences C) _ hw.mem
    have : IsIso (L.map f') := by
      rw [show L.map f' = inv (L.map f) ≫ L.map (f ≫ f') by simp]
      infer_instance
    obtain ⟨B'', f'', hf'', hw'⟩ := (exists_leftInverse_iff L f').1 ⟨inv (L.map f'), by simp⟩
    exact ⟨B', B'', f', f'', hf', hf'', hw, hw'⟩
  · rintro ⟨B', B'', f', f'', -, -, hw, hw'⟩
    have := Localization.inverts L (weakEquivalences C) _ hw.mem
    have := Localization.inverts L (weakEquivalences C) _ hw'.mem
    have : IsIso (L.map f ≫ L.map f') := by rw [← L.map_comp]; infer_instance
    have : IsIso (L.map f' ≫ L.map f'') := by rw [← L.map_comp]; infer_instance
    have := isIso_of_isIso_comp_of_isIso_comp (L.map f) (L.map f') (L.map f'')
    rw [show L.map f = (L.map f ≫ L.map f') ≫ inv (L.map f') by simp]
    infer_instance

end ABCPrecofibrationCategory

namespace ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Proposition 7.2.9(2).** A map with the left lifting property with respect
to all fibrations becomes an isomorphism in the homotopy category. -/
theorem isIso_map_of_hasLiftingProperty {X Y : C} (p : X ⟶ Y)
    (hp : ∀ ⦃A B : C⦄ (q : A ⟶ B), Fibration q → HasLiftingProperty p q) :
    IsIso (L.map p) := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  have := ABCPrecofibrationCategory.isIso_map_of_hasLiftingProperty L.op p.op
    fun A B i hi ↦ HasLiftingProperty.op (hp i.unop ((fibration_unop_iff i).2 hi))
  exact (isIso_op_iff _).1 this

/-- **Lemma 7.2.1(2)(a).** A map `f : A ⟶ B` between fibrant objects has a right
inverse in the homotopy category iff there is a fibration `f' : A' ⟶ A` with
`ff'` a weak equivalence. -/
theorem exists_rightInverse_iff {A B : C} [IsFibrant A] [IsFibrant B] (f : A ⟶ B) :
    (∃ g : L.obj B ⟶ L.obj A, g ≫ L.map f = 𝟙 _) ↔
      ∃ (A' : C) (f' : A' ⟶ A), Fibration f' ∧ WeakEquivalence (f' ≫ f) := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  have e := ABCPrecofibrationCategory.exists_leftInverse_iff L.op f.op
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨B', f'', hf'', hw⟩ := e.1 ⟨g.op, by
      change (L.map f).op ≫ g.op = 𝟙 _
      rw [← op_comp, hg, op_id]⟩
    exact ⟨B'.unop, f''.unop, (fibration_unop_iff f'').2 hf'',
      (weakEquivalences_unop_iff (f.op ≫ f'')).2 hw⟩
  · rintro ⟨A', f', hf', hw⟩
    obtain ⟨g, hg⟩ := e.2 ⟨Opposite.op A', f'.op, (cofibration_op_iff f').2 hf',
      (weakEquivalences_op_iff (f' ≫ f)).2 hw⟩
    exact ⟨g.unop, by
      change g.unop ≫ (L.op.map f.op).unop = 𝟙 _
      rw [← unop_comp, hg, unop_id]⟩

/-- **Lemma 7.2.1(2)(b).** A map `f : A ⟶ B` between fibrant objects is an
isomorphism in the homotopy category iff there are fibrations `f' : A' ⟶ A` and
`f'' : A'' ⟶ A'` with `ff'` and `f'f''` weak equivalences. -/
theorem isIso_map_iff {A B : C} [IsFibrant A] [IsFibrant B] (f : A ⟶ B) :
    IsIso (L.map f) ↔ ∃ (A' A'' : C) (f' : A' ⟶ A) (f'' : A'' ⟶ A'), Fibration f' ∧
      Fibration f'' ∧ WeakEquivalence (f' ≫ f) ∧ WeakEquivalence (f'' ≫ f') := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  rw [← isIso_op_iff]
  change IsIso (L.op.map f.op) ↔ _
  rw [ABCPrecofibrationCategory.isIso_map_iff L.op f.op]
  constructor
  · rintro ⟨B', B'', f', f'', hf', hf'', hw, hw'⟩
    exact ⟨B'.unop, B''.unop, f'.unop, f''.unop, (fibration_unop_iff f').2 hf',
      (fibration_unop_iff f'').2 hf'', (weakEquivalences_unop_iff (f.op ≫ f')).2 hw,
      (weakEquivalences_unop_iff (f' ≫ f'')).2 hw'⟩
  · rintro ⟨A', A'', f', f'', hf', hf'', hw, hw'⟩
    exact ⟨Opposite.op A', Opposite.op A'', f'.op, f''.op, (cofibration_op_iff f').2 hf',
      (cofibration_op_iff f'').2 hf'', (weakEquivalences_op_iff (f' ≫ f)).2 hw,
      (weakEquivalences_op_iff (f'' ≫ f')).2 hw'⟩

end ABCPrefibrationCategory

end ABCCofibrations

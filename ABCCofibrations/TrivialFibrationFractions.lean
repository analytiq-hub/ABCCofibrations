/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.TrivialFibrationLocalization
public import ABCCofibrations.TrivialCofibrationFractions
public import ABCCofibrations.FibrantOpposite
public import ABCCofibrations.RightHomotopyFractions

/-!
# Right-fraction representations with trivial-fibration denominators

Morphisms in a localization of fibrant objects are represented by right
fractions `X ← Z → Y` whose backward arrow is a trivial fibration. Two such
denominators have a common refinement, fractions compose, finite families
share one denominator, and the numerators can be chosen to be fibrations,
with fibrant product boundary.

None of these results is proved again. Each is the corresponding statement
of `TrivialCofibrationFractions.lean`, applied in `Cᵒᵖ` and transported along
`fibrantObjectOpEquivalence : (FibrantObject C)ᵒᵖ ≌ CofibrantObject Cᵒᵖ`.
Under that equivalence, trivial fibrations of fibrant objects are exactly the
trivial cofibrations of the opposite cofibrant objects, localizations
transport to localizations, and right fractions to left fractions.
-/

public section

universe v u v' u' w

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Trivial fibrations of fibrant objects are exactly the trivial
cofibrations of the opposite cofibrant objects. -/
theorem trivialCofibrations_functor_map_op_iff {X Y : FibrantObject C} (f : X ⟶ Y) :
    ABCPrecofibrationCategory.cofibrantTrivialCofibrations (C := Cᵒᵖ)
      (fibrantObjectOpEquivalence.functor.map f.op) ↔
      fibrantTrivialFibrations f :=
  Iff.rfl

/-- Any localization at trivial fibrations transports to a localization of
opposite cofibrant objects at trivial cofibrations. -/
instance isLocalization_trivialFibrations_inverse_comp_op
    (L : FibrantObject C ⥤ D) [L.IsLocalization (fibrantTrivialFibrations (C := C))] :
    (fibrantObjectOpEquivalence.inverse ⋙ L.op).IsLocalization
      (ABCPrecofibrationCategory.cofibrantTrivialCofibrations (C := Cᵒᵖ)) :=
  isLocalization_inverse_comp_op _ _ trivialCofibrations_functor_map_op_iff L

/-- A cofibrant-side trivial cofibration transports to a trivial fibration. -/
theorem fibrantTrivialFibrations_inverse_map_unop {X Y : CofibrantObject Cᵒᵖ} (g : X ⟶ Y)
    (hg : ABCPrecofibrationCategory.cofibrantTrivialCofibrations g) :
    fibrantTrivialFibrations (fibrantObjectOpEquivalence.inverse.map g).unop :=
  (mem_iff_inverse_map_unop _ _ trivialCofibrations_functor_map_op_iff g).1 hg

/-- Two trivial-fibration denominators with the same target have a common
refinement, with both comparison maps again trivial fibrations. -/
theorem exists_common_trivialFibration_denominator
    {Y A B : FibrantObject C} (s : A ⟶ Y) (t : B ⟶ Y)
    (hs : fibrantTrivialFibrations s) (ht : fibrantTrivialFibrations t) :
    ∃ (P : FibrantObject C) (i : P ⟶ A) (j : P ⟶ B),
      fibrantTrivialFibrations i ∧ fibrantTrivialFibrations j ∧ i ≫ s = j ≫ t := by
  obtain ⟨P, i, j, hi, hj, sq⟩ :=
    ABCPrecofibrationCategory.exists_common_trivialCofibration_denominator
      (fibrantObjectOpEquivalence.functor.map s.op)
        (fibrantObjectOpEquivalence.functor.map t.op) hs ht
  exact ⟨(fibrantObjectOpEquivalence.inverse.obj P).unop,
    (fibrantObjectOpEquivalence.inverse.map i).unop,
    (fibrantObjectOpEquivalence.inverse.map j).unop,
    fibrantTrivialFibrations_inverse_map_unop i hi,
    fibrantTrivialFibrations_inverse_map_unop j hj,
    Quiver.Hom.op_inj (congrArg (fun x ↦ fibrantObjectOpEquivalence.inverse.map x) sq)⟩

/-- Over a common refinement of their denominators, equality of two right
fractions is exactly equality of the images of their restricted numerators. -/
theorem trivialFibration_fraction_map_eq_iff
    {X Y P : FibrantObject C}
    (φ ψ : (fibrantTrivialFibrations (C := C)).RightFraction X Y)
    (i : P ⟶ φ.X') (j : P ⟶ ψ.X')
    (hi : fibrantTrivialFibrations i) (hj : fibrantTrivialFibrations j)
    (sq : i ≫ φ.s = j ≫ ψ.s)
    (F : FibrantObject C ⥤ D)
    (hF : (fibrantTrivialFibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF ↔ F.map (i ≫ φ.f) = F.map (j ≫ ψ.f) := by
  have h := ABCPrecofibrationCategory.trivialCofibration_fraction_map_eq_iff
    (rightFractionOp trivialCofibrations_functor_map_op_iff φ)
    (rightFractionOp trivialCofibrations_functor_map_op_iff ψ)
    (fibrantObjectOpEquivalence.functor.map i.op)
      (fibrantObjectOpEquivalence.functor.map j.op) hi hj
    (congrArg (fun x : P ⟶ X ↦ fibrantObjectOpEquivalence.functor.map x.op) sq)
    (fibrantObjectOpEquivalence.inverse ⋙ F.op)
    ((isInvertedBy_inverse_comp_op_iff_of _ _ trivialCofibrations_functor_map_op_iff F).2 hF)
  rw [rightFractionOp_map trivialCofibrations_functor_map_op_iff φ F hF,
    rightFractionOp_map trivialCofibrations_functor_map_op_iff ψ F hF] at h
  exact Quiver.Hom.op_inj.eq_iff.symm.trans
    (h.trans (Quiver.Hom.op_inj.eq_iff (a := F.map (i ≫ φ.f)) (b := F.map (j ≫ ψ.f))))

/-- Strict equality of restricted numerators suffices to identify right
fractions under every functor inverting trivial fibrations. -/
theorem trivialFibration_fraction_map_eq_of_common_refinement
    {X Y P : FibrantObject C}
    (φ ψ : (fibrantTrivialFibrations (C := C)).RightFraction X Y)
    (i : P ⟶ φ.X') (j : P ⟶ ψ.X')
    (hi : fibrantTrivialFibrations i) (hj : fibrantTrivialFibrations j)
    (hs : i ≫ φ.s = j ≫ ψ.s) (hf : i ≫ φ.f = j ≫ ψ.f)
    (F : FibrantObject C ⥤ D)
    (hF : (fibrantTrivialFibrations (C := C)).IsInvertedBy F) :
    φ.map F hF = ψ.map F hF :=
  (trivialFibration_fraction_map_eq_iff φ ψ i j hi hj hs F hF).2
    (congrArg (fun f ↦ F.map f) hf)

/-- Two composable right fractions admit a composite right fraction,
computed by a pullback square, simultaneously for every functor inverting
trivial fibrations. -/
theorem exists_trivialFibration_fraction_comp
    {X Y Z : FibrantObject C}
    (φ : (fibrantTrivialFibrations (C := C)).RightFraction X Y)
    (ψ : (fibrantTrivialFibrations (C := C)).RightFraction Y Z) :
    ∃ χ : (fibrantTrivialFibrations (C := C)).RightFraction X Z,
      ∀ (F : FibrantObject C ⥤ D)
        (hF : (fibrantTrivialFibrations (C := C)).IsInvertedBy F),
        χ.map F hF = φ.map F hF ≫ ψ.map F hF := by
  obtain ⟨χ, hχ⟩ := ABCPrecofibrationCategory.exists_trivialCofibration_fraction_comp
    (D := Dᵒᵖ) (rightFractionOp trivialCofibrations_functor_map_op_iff ψ)
    (rightFractionOp trivialCofibrations_functor_map_op_iff φ)
  refine ⟨leftFractionUnop trivialCofibrations_functor_map_op_iff χ, fun F hF ↦ ?_⟩
  have hF' := (isInvertedBy_inverse_comp_op_iff_of _ _
    trivialCofibrations_functor_map_op_iff F).2 hF
  rw [leftFractionUnop_map trivialCofibrations_functor_map_op_iff χ F hF, hχ _ hF',
    rightFractionOp_map trivialCofibrations_functor_map_op_iff φ F hF,
    rightFractionOp_map trivialCofibrations_functor_map_op_iff ψ F hF]
  rfl

/-- Every arrow of a localization at trivial fibrations is represented by a
right fraction whose denominator is a trivial fibration. -/
theorem exists_trivialFibration_fraction
    (L : FibrantObject C ⥤ D) [L.IsLocalization (fibrantTrivialFibrations (C := C))]
    {X Y : FibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : FibrantObject C) (s : Z ⟶ X) (f : Z ⟶ Y),
      fibrantTrivialFibrations s ∧ L.map s ≫ α = L.map f := by
  obtain ⟨Z, f, s, hs, h⟩ := ABCPrecofibrationCategory.exists_trivialCofibration_fraction
    (fibrantObjectOpEquivalence.inverse ⋙ L.op) (X := fibrantObjectOpEquivalence.functor.obj (op Y))
      (Y := fibrantObjectOpEquivalence.functor.obj (op X)) α.op
  exact ⟨(fibrantObjectOpEquivalence.inverse.obj Z).unop,
    (fibrantObjectOpEquivalence.inverse.map s).unop,
    (fibrantObjectOpEquivalence.inverse.map f).unop,
    fibrantTrivialFibrations_inverse_map_unop s hs, congrArg Quiver.Hom.unop h⟩

/-- The right-fraction representation, using mathlib's fraction type. -/
theorem exists_rightFraction_trivialFibration
    (L : FibrantObject C ⥤ D) [L.IsLocalization (fibrantTrivialFibrations (C := C))]
    {X Y : FibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ φ : (fibrantTrivialFibrations (C := C)).RightFraction X Y,
      φ.map L (Localization.inverts L _) = α := by
  obtain ⟨ψ, hψ⟩ := ABCPrecofibrationCategory.exists_leftFraction_trivialCofibration
    (fibrantObjectOpEquivalence.inverse ⋙ L.op) (X := fibrantObjectOpEquivalence.functor.obj (op Y))
      (Y := fibrantObjectOpEquivalence.functor.obj (op X)) α.op
  refine ⟨leftFractionUnop trivialCofibrations_functor_map_op_iff ψ, ?_⟩
  rw [leftFractionUnop_map trivialCofibrations_functor_map_op_iff ψ L (Localization.inverts L _)]
  exact congrArg Quiver.Hom.unop hψ

/-- The representation applies to any localization at all weak equivalences
of fibrant objects; the denominator can still be a trivial fibration. -/
theorem exists_trivialFibration_fraction_of_weakEquivalence_localization
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : FibrantObject C) (s : Z ⟶ X) (f : Z ⟶ Y),
      fibrantTrivialFibrations s ∧ L.map s ≫ α = L.map f := by
  let := isLocalization_trivialFibrations_of_weakEquivalences L
  exact exists_trivialFibration_fraction L α

/-- The same statement in mathlib's right-fraction notation. -/
theorem exists_rightFraction_of_weakEquivalence_localization
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ φ : (fibrantTrivialFibrations (C := C)).RightFraction X Y,
      φ.map L ((inverts_weakEquivalences_iff_inverts_trivialFibrations L).1
        (Localization.inverts L (weakEquivalences (FibrantObject C)))) = α := by
  let := isLocalization_trivialFibrations_of_weakEquivalences L
  exact exists_rightFraction_trivialFibration L α

/-- Parallel right fractions can be put over a single trivial-fibration
denominator, simultaneously for every inverting functor. -/
theorem exists_parallel_trivialFibration_fractions
    {X Y : FibrantObject C}
    (φ ψ : (fibrantTrivialFibrations (C := C)).RightFraction X Y) :
    ∃ (P : FibrantObject C) (s : P ⟶ X) (f g : P ⟶ Y),
      fibrantTrivialFibrations s ∧
      ∀ (F : FibrantObject C ⥤ D)
        (hF : (fibrantTrivialFibrations (C := C)).IsInvertedBy F),
        (F.map s ≫ φ.map F hF = F.map f) ∧ (F.map s ≫ ψ.map F hF = F.map g) := by
  obtain ⟨P, f, g, s, hs, h⟩ :=
    ABCPrecofibrationCategory.exists_parallel_trivialCofibration_fractions (D := Dᵒᵖ)
      (rightFractionOp trivialCofibrations_functor_map_op_iff φ)
      (rightFractionOp trivialCofibrations_functor_map_op_iff ψ)
  refine ⟨(fibrantObjectOpEquivalence.inverse.obj P).unop,
    (fibrantObjectOpEquivalence.inverse.map s).unop,
    (fibrantObjectOpEquivalence.inverse.map f).unop,
    (fibrantObjectOpEquivalence.inverse.map g).unop, fibrantTrivialFibrations_inverse_map_unop s hs,
      fun F hF ↦ ?_⟩
  have hF' := (isInvertedBy_inverse_comp_op_iff_of _ _
    trivialCofibrations_functor_map_op_iff F).2 hF
  obtain ⟨h₁, h₂⟩ := h _ hF'
  rw [rightFractionOp_map trivialCofibrations_functor_map_op_iff φ F hF] at h₁
  rw [rightFractionOp_map trivialCofibrations_functor_map_op_iff ψ F hF] at h₂
  exact ⟨congrArg Quiver.Hom.unop h₁, congrArg Quiver.Hom.unop h₂⟩

/-- Two parallel arrows of a weak-equivalence localization have a common
trivial-fibration denominator. -/
theorem exists_common_fraction_of_weakEquivalence_localization
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (α β : L.obj X ⟶ L.obj Y) :
    ∃ (P : FibrantObject C) (s : P ⟶ X) (f g : P ⟶ Y),
      fibrantTrivialFibrations s ∧ L.map s ≫ α = L.map f ∧ L.map s ≫ β = L.map g := by
  obtain ⟨P, f, g, s, hs, hα, hβ⟩ :=
    ABCPrecofibrationCategory.exists_common_fraction_of_weakEquivalence_localization
      (fibrantObjectOpEquivalence.inverse ⋙ L.op)
        (X := fibrantObjectOpEquivalence.functor.obj (op Y))
        (Y := fibrantObjectOpEquivalence.functor.obj (op X)) α.op β.op
  exact ⟨(fibrantObjectOpEquivalence.inverse.obj P).unop,
    (fibrantObjectOpEquivalence.inverse.map s).unop,
    (fibrantObjectOpEquivalence.inverse.map f).unop,
    (fibrantObjectOpEquivalence.inverse.map g).unop, fibrantTrivialFibrations_inverse_map_unop s hs,
    congrArg Quiver.Hom.unop hα, congrArg Quiver.Hom.unop hβ⟩

/-- Every family of parallel localized arrows indexed by a finite type has a
single trivial-fibration denominator. -/
theorem exists_common_fraction_of_finite_family
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} {ι : Type w} [Finite ι] (α : ι → (L.obj X ⟶ L.obj Y)) :
    ∃ (P : FibrantObject C) (s : P ⟶ X) (f : ι → (P ⟶ Y)),
      fibrantTrivialFibrations s ∧ ∀ a, L.map s ≫ α a = L.map (f a) := by
  obtain ⟨P, f, s, hs, h⟩ :=
    ABCPrecofibrationCategory.exists_common_fraction_of_finite_family
      (fibrantObjectOpEquivalence.inverse ⋙ L.op)
        (X := fibrantObjectOpEquivalence.functor.obj (op Y))
        (Y := fibrantObjectOpEquivalence.functor.obj (op X))
      (fun a ↦ (α a).op)
  exact ⟨(fibrantObjectOpEquivalence.inverse.obj P).unop,
    (fibrantObjectOpEquivalence.inverse.map s).unop,
    fun a ↦ (fibrantObjectOpEquivalence.inverse.map (f a)).unop,
    fibrantTrivialFibrations_inverse_map_unop s hs, fun a ↦ congrArg Quiver.Hom.unop (h a)⟩

/-- The finite common-denominator theorem for families indexed by `Fin n`. -/
theorem exists_finite_common_fraction_of_weakEquivalence_localization
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (n : ℕ) (α : Fin n → (L.obj X ⟶ L.obj Y)) :
    ∃ (P : FibrantObject C) (s : P ⟶ X) (f : Fin n → (P ⟶ Y)),
      fibrantTrivialFibrations s ∧ ∀ a, L.map s ≫ α a = L.map (f a) :=
  exists_common_fraction_of_finite_family L α

/-- A localized arrow admits a right fraction whose numerator, denominator,
and combined map to the product of its endpoints are fibrations, with
trivial-fibration denominator. Any chosen product `Y ⨯ X` is allowed; it is
compared with the opposite coproduct by `oppositeCoprodProductIsoPair`. -/
theorem exists_fibration_fraction_with_prod
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} [HasBinaryProduct Y.obj X.obj] (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : FibrantObject C) (s : Z ⟶ X) (p : Z ⟶ Y),
      Fibration p.hom ∧ fibrantTrivialFibrations s ∧
        Fibration (prod.lift p.hom s.hom) ∧ L.map s ≫ α = L.map p := by
  let : HasBinaryCoproduct (fibrantObjectOpEquivalence.functor.obj (op Y)).obj
      (fibrantObjectOpEquivalence.functor.obj (op X)).obj :=
    ABCPrecofibrationCategory.hasBinaryCoproduct (op Y.obj) (op X.obj)
  obtain ⟨Z, i, s, hi, hs, hb, h⟩ :=
    ABCPrecofibrationCategory.exists_cofibration_fraction_with_coprod
      (fibrantObjectOpEquivalence.inverse ⋙ L.op)
        (X := fibrantObjectOpEquivalence.functor.obj (op Y))
        (Y := fibrantObjectOpEquivalence.functor.obj (op X)) α.op
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (op Y.obj) (op X.obj)
  let e := oppositeCoprodProductIsoPair Y.obj X.obj
  let := prod_fibrant (A := Y.obj) (B := X.obj)
  let := fibration_of_isIso e.hom
  let : Fibration (coprod.desc i.hom s.hom).unop := (fibration_unop_iff _).2 hb
  let p : _ ⟶ Y := (fibrantObjectOpEquivalence.inverse.map i).unop
  let t : _ ⟶ X := (fibrantObjectOpEquivalence.inverse.map s).unop
  have hp : Fibration (prod.lift p.hom t.hom) := by
    have eq : (coprod.desc i.hom s.hom).unop ≫ e.hom = prod.lift p.hom t.hom := by
      apply prod.hom_ext <;> simp [e, oppositeCoprodProductIsoPair, ← unop_comp, p, t] <;> rfl
    rw [← eq]
    exact ⟨(fibrations C).comp_mem _ _ (show Fibration (coprod.desc i.hom s.hom).unop from
      inferInstance).mem (fibration_of_isIso e.hom).mem⟩
  exact ⟨(fibrantObjectOpEquivalence.inverse.obj Z).unop, t, p,
    (fibration_unop_iff i.hom).2 hi, fibrantTrivialFibrations_inverse_map_unop s hs, hp,
    congrArg Quiver.Hom.unop h⟩

/-- Every localized arrow admits a right fraction with a fibration numerator
and a trivial-fibration denominator. -/
theorem exists_fibration_fraction_of_weakEquivalence_localization
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (α : L.obj X ⟶ L.obj Y) :
    ∃ (Z : FibrantObject C) (s : Z ⟶ X) (p : Z ⟶ Y),
      Fibration p.hom ∧ fibrantTrivialFibrations s ∧ L.map s ≫ α = L.map p := by
  let := hasBinaryProduct Y.obj X.obj
  obtain ⟨Z, s, p, hp, hs, _, h⟩ := exists_fibration_fraction_with_prod L α
  exact ⟨Z, s, p, hp, hs, h⟩

/-- A family of parallel localized arrows indexed by a finite type has one
trivial-fibration denominator and simultaneous fibration numerators. -/
theorem exists_common_fibration_fraction_of_finite_family
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} {ι : Type w} [Finite ι] (α : ι → (L.obj X ⟶ L.obj Y)) :
    ∃ (P : FibrantObject C) (s : P ⟶ X) (f : ι → (P ⟶ Y)),
      fibrantTrivialFibrations s ∧
        ∀ a, Fibration (f a).hom ∧ L.map s ≫ α a = L.map (f a) := by
  obtain ⟨P, f, s, hs, h⟩ :=
    ABCPrecofibrationCategory.exists_common_cofibration_fraction_of_finite_family
      (fibrantObjectOpEquivalence.inverse ⋙ L.op)
        (X := fibrantObjectOpEquivalence.functor.obj (op Y))
        (Y := fibrantObjectOpEquivalence.functor.obj (op X))
      (fun a ↦ (α a).op)
  exact ⟨(fibrantObjectOpEquivalence.inverse.obj P).unop,
    (fibrantObjectOpEquivalence.inverse.map s).unop,
    fun a ↦ (fibrantObjectOpEquivalence.inverse.map (f a)).unop,
    fibrantTrivialFibrations_inverse_map_unop s hs,
    fun a ↦ ⟨(fibration_unop_iff (f a).hom).2 (h a).1, congrArg Quiver.Hom.unop (h a).2⟩⟩

/-- Simultaneous fibration numerators for a family indexed by `Fin n`. -/
theorem exists_finite_common_fibration_fraction
    (L : FibrantObject C ⥤ D) [L.IsLocalization (weakEquivalences (FibrantObject C))]
    {X Y : FibrantObject C} (n : ℕ) (α : Fin n → (L.obj X ⟶ L.obj Y)) :
    ∃ (P : FibrantObject C) (s : P ⟶ X) (f : Fin n → (P ⟶ Y)),
      fibrantTrivialFibrations s ∧
        ∀ a, Fibration (f a).hom ∧ L.map s ≫ α a = L.map (f a) :=
  exists_common_fibration_fraction_of_finite_family L α

end ABCCofibrations.ABCPrefibrationCategory

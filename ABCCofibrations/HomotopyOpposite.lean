/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.RightHomotopy
public import ABCCofibrations.LeftHomotopy
public import ABCCofibrations.ReplacementComparison
public import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Native right homotopy and opposite left homotopy

The comparison retains arbitrary choices of binary products and coproducts.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {B : C} [IsFibrant B] [HasBinaryProduct B B]
  [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)]

/-- The opposite coproduct represents the chosen native product, with its
canonical projections. No equality between the choices is assumed. -/
noncomputable def oppositeCoprodProductIso :
    (Opposite.op B ⨿ Opposite.op B).unop ≅ B ⨯ B where
  hom := prod.lift
    (coprod.inl : Opposite.op B ⟶ Opposite.op B ⨿ Opposite.op B).unop
    (coprod.inr : Opposite.op B ⟶ Opposite.op B ⨿ Opposite.op B).unop
  inv := (coprod.desc (prod.fst : B ⨯ B ⟶ B).op (prod.snd : B ⨯ B ⟶ B).op).unop
  hom_inv_id := by
    apply Quiver.Hom.op_inj
    rw [op_comp]
    apply coprod.hom_ext <;> simp [← op_comp]
  inv_hom_id := by
    apply prod.hom_ext <;> simp [← unop_comp]

/-- Turn a native path object into a cylinder on the opposite object. -/
def pathObjectOp (P : PathObject B) : Cylinder (Opposite.op B) where
  I := Opposite.op P.P
  i₀ := P.p₀.op
  i₁ := P.p₁.op
  π := P.ι.op
  i₀_π := congrArg Quiver.Hom.op P.ι_p₀
  i₁_π := congrArg Quiver.Hom.op P.ι_p₁
  weakEquivalence_π := (weakEquivalences_op_iff P.ι).2 inferInstance

/-- Turn an opposite cylinder into a native path object. -/
def cylinderUnop (P : Cylinder (Opposite.op B)) : PathObject B where
  P := P.I.unop
  p₀ := P.i₀.unop
  p₁ := P.i₁.unop
  ι := P.π.unop
  ι_p₀ := congrArg Quiver.Hom.unop P.i₀_π
  ι_p₁ := congrArg Quiver.Hom.unop P.i₁_π
  weakEquivalence_ι := (weakEquivalences_unop_iff P.π).2 inferInstance

/-- Goodness is preserved by the path-object/opposite-cylinder comparison. -/
theorem pathObjectOp_isGood_iff (P : PathObject B) :
    (pathObjectOp P).IsGood ↔ P.IsGood := by
  let e := oppositeCoprodProductIso (B := B)
  let := prod_fibrant (A := B) (B := B)
  let := fibration_of_isIso e.hom
  let := fibrant_source e.hom
  let := fibration_of_isIso e.inv
  have he : (coprod.desc P.p₀.op P.p₁.op).unop ≫ e.hom = P.p := by
    apply prod.hom_ext <;> simp [e, oppositeCoprodProductIso, ← unop_comp, PrepathObject.p]
  constructor
  · intro h
    let := h
    have hc : Cofibration (coprod.desc P.p₀.op P.p₁.op) :=
      inferInstanceAs (Cofibration (pathObjectOp P).i)
    let := (fibration_unop_iff (coprod.desc P.p₀.op P.p₁.op)).2 hc
    constructor
    change Fibration P.p
    rw [← he]
    exact inferInstanceAs (Fibration ((coprod.desc P.p₀.op P.p₁.op).unop ≫ e.hom))
  · intro h
    let := h
    have he' : (coprod.desc P.p₀.op P.p₁.op).unop = P.p ≫ e.inv := by
      rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
    constructor
    change Cofibration (coprod.desc P.p₀.op P.p₁.op)
    apply (fibration_unop_iff (coprod.desc P.p₀.op P.p₁.op)).1
    rw [he']
    exact inferInstanceAs (Fibration (P.p ≫ e.inv))

/-- An opposite good cylinder gives a good native path object. -/
theorem cylinderUnop_isGood (P : Cylinder (Opposite.op B)) [P.IsGood] :
    (cylinderUnop P).IsGood := by
  apply (pathObjectOp_isGood_iff (cylinderUnop P)).1
  exact inferInstanceAs P.IsGood

/-- Native strict right homotopy is exactly strict left homotopy on the
opposite arrows, with arbitrary product and coproduct choices. -/
theorem strictRightHomotopy_iff_op {A : C} (f g : A ⟶ B) :
    StrictRightHomotopyRel f g ↔ ABCPrecofibrationCategory.StrictLeftHomotopyRel f.op g.op := by
  constructor
  · rintro ⟨P, hP, ⟨H⟩⟩
    exact ⟨pathObjectOp P, (pathObjectOp_isGood_iff P).2 hP, ⟨{
      h := H.h.op
      h₀ := congrArg Quiver.Hom.op H.h₀
      h₁ := congrArg Quiver.Hom.op H.h₁ }⟩⟩
  · rintro ⟨P, hP, ⟨H⟩⟩
    let := hP
    exact ⟨cylinderUnop P, cylinderUnop_isGood P, ⟨{
      h := H.h.unop
      h₀ := congrArg Quiver.Hom.unop H.h₀
      h₁ := congrArg Quiver.Hom.unop H.h₁ }⟩⟩

/-- Native right homotopy is exactly left homotopy of opposite arrows. -/
theorem rightHomotopy_iff_op {A : C} (f g : A ⟶ B) :
    RightHomotopyRel f g ↔ ABCPrecofibrationCategory.LeftHomotopyRel f.op g.op := by
  constructor
  · rintro ⟨A', a, ha, haw, H⟩
    let := ha
    let := haw
    exact ⟨Opposite.op A', a.op, inferInstance, inferInstance,
      by simpa only [op_comp] using (strictRightHomotopy_iff_op _ _).1 H⟩
  · rintro ⟨A', a, ha, haw, H⟩
    exact ⟨A'.unop, a.unop, (fibration_unop_iff a).2 ha,
      (weakEquivalences_unop_iff a).2 haw,
      by simpa only [unop_comp, Quiver.Hom.unop_op] using (strictRightHomotopy_iff_op _ _).2 H⟩

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- Transitivity is transported from strict left homotopy, without a second
concatenation proof for native path objects. -/
theorem StrictRightHomotopyRel.trans {A : C} {f g h : A ⟶ B}
    (hfg : StrictRightHomotopyRel f g) (hgh : StrictRightHomotopyRel g h) :
    StrictRightHomotopyRel f h := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  exact (strictRightHomotopy_iff_op f h).2
    (((strictRightHomotopy_iff_op f g).1 hfg).trans ((strictRightHomotopy_iff_op g h).1 hgh))

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- Transitivity of general right homotopy follows from opposite left homotopy. -/
theorem RightHomotopyRel.trans {A : C} [IsFibrant A] {f g h : A ⟶ B}
    (hfg : RightHomotopyRel f g) (hgh : RightHomotopyRel g h) : RightHomotopyRel f h := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  exact (rightHomotopy_iff_op f h).2
    (((rightHomotopy_iff_op f g).1 hfg).trans ((rightHomotopy_iff_op g h).1 hgh))

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- Postcomposition follows from precomposition of opposite left homotopies. -/
theorem RightHomotopyRel.postcomp {A : C} [IsFibrant A] {f g : A ⟶ B}
    (h : RightHomotopyRel f g) {D : C} [IsFibrant D] [HasBinaryProduct D D]
    (k : B ⟶ D) : RightHomotopyRel (f ≫ k) (g ≫ k) := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op D) (Opposite.op D)
  apply (rightHomotopy_iff_op _ _).2
  simpa only [op_comp] using ((rightHomotopy_iff_op f g).1 h).precomp k.op

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- Strict right homotopy is an equivalence relation. -/
theorem StrictRightHomotopyRel.equivalence {A : C} :
    Equivalence (StrictRightHomotopyRel (A := A) (B := B)) := ⟨refl, symm, trans⟩

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- General right homotopy is an equivalence relation between fibrant objects. -/
theorem RightHomotopyRel.equivalence {A : C} [IsFibrant A] :
    Equivalence (RightHomotopyRel (A := A) (B := B)) := ⟨refl, symm, trans⟩

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- Theorem 6.3.1(2): maps between fibrant objects have equal images in
localization exactly when they are right homotopic. -/
theorem ambient_map_eq_iff_fibrant_rightHomotopy
    {A : C} [IsFibrant A] {D : Type*} [Category D]
    (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)] (f g : A ⟶ B) :
    L.map f = L.map g ↔ RightHomotopyRel f g := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  rw [rightHomotopy_iff_op]
  let : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  have he := ABCPrecofibrationCategory.ambient_map_eq_iff_cofibrant_leftHomotopy L.op
    (CofibrantObject.homMk f.op) (CofibrantObject.homMk g.op)
  change L.op.map f.op = L.op.map g.op ↔
    ABCPrecofibrationCategory.LeftHomotopyRel f.op g.op at he
  constructor
  · intro h
    exact he.1 (congrArg Quiver.Hom.op h)
  · intro h
    exact Quiver.Hom.op_inj (he.2 h)

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- **Lemma 6.3.2(2).** A right homotopy between maps of fibrant objects can be
represented on any given good path object, after replacing the source by a
trivial fibration. -/
theorem RightHomotopyRel.exists_on_pathObject {A : C} [IsFibrant A] {f g : A ⟶ B}
    (h : RightHomotopyRel f g) (Q : PathObject B) [Q.IsGood] :
    ∃ (A' : C) (a : A' ⟶ A), Fibration a ∧ WeakEquivalence a ∧
      Nonempty (Q.RightHomotopy (a ≫ f) (a ≫ g)) := by
  let := ABCPrecofibrationCategory.hasBinaryCoproduct (Opposite.op B) (Opposite.op B)
  have : (pathObjectOp Q).IsGood := (pathObjectOp_isGood_iff Q).2 inferInstance
  obtain ⟨A', b, hb, hbw, ⟨H⟩⟩ :=
    ((rightHomotopy_iff_op f g).1 h).exists_on_cylinder (pathObjectOp Q)
  refine ⟨A'.unop, b.unop, (fibration_unop_iff b).2 hb, (weakEquivalences_unop_iff b).2 hbw,
    ⟨{ h := H.h.unop
       h₀ := by
         have e := congrArg Quiver.Hom.unop H.h₀
         simp only [unop_comp, Quiver.Hom.unop_op] at e
         exact e
       h₁ := by
         have e := congrArg Quiver.Hom.unop H.h₁
         simp only [unop_comp, Quiver.Hom.unop_op] at e
         exact e }⟩⟩

omit [HasBinaryCoproduct (Opposite.op B) (Opposite.op B)] in
/-- **Theorem 6.3.3(2).** Right homotopy is an equivalence relation on maps
between fibrant objects, compatible with postcomposition and precomposition by
maps of fibrant objects. -/
theorem rightHomotopy_equivalence_comp {A : C} [IsFibrant A] :
    Equivalence (RightHomotopyRel (A := A) (B := B)) ∧
      (∀ {f g : A ⟶ B}, RightHomotopyRel f g → ∀ {D : C} [IsFibrant D] [HasBinaryProduct D D]
        (k : B ⟶ D), RightHomotopyRel (f ≫ k) (g ≫ k)) ∧
      ∀ {f g : A ⟶ B}, RightHomotopyRel f g → ∀ {D : C} [IsFibrant D] (k : D ⟶ A),
        RightHomotopyRel (k ≫ f) (k ≫ g) :=
  ⟨RightHomotopyRel.equivalence, fun h _ _ _ k ↦ h.postcomp k, fun h _ _ k ↦ h.precomp k⟩

end ABCCofibrations.ABCPrefibrationCategory

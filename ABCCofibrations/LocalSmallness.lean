/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.AmbientHomotopyFractions
public import ABCCofibrations.ReplacementComparison
public import ABCCofibrations.HomotopyOpposite
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Maps of the homotopy category as homotopy classes (Propositions 7.3.2, 7.3.4)

Definition 7.3.1: a *fibrant model* in a precofibration category is an object
with the extension property against trivial cofibrations with cofibrant domain;
dually a *cofibrant model*. Proposition 7.3.2 (Cisinski): every map of the
homotopy category from a cofibrant object to a fibrant model comes from a map of
the category. Proposition 7.3.4: under the Baues axiom BCF6, the maps of the
homotopy category between cofibrant objects are the homotopy classes of maps.
These are the key steps for local smallness of the homotopy category
(Proposition 7.3.3, Corollary 7.3.5).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

/-- A localization is locally small if every pair of objects is isomorphic to a
pair whose maps in the localization all come from maps of a locally small
category. -/
theorem locallySmall_of_surjective {C : Type u} [Category.{v} C] {D : Type*} [Category D]
    (L : C ⥤ D) [L.EssSurj] [LocallySmall.{w} C]
    (h : ∀ A B : C, ∃ (A' B' : C) (_ : L.obj A ≅ L.obj A') (_ : L.obj B ≅ L.obj B'),
      Function.Surjective (fun g : A' ⟶ B' ↦ L.map g)) : LocallySmall.{w} D where
  hom_small X Y := by
    obtain ⟨A', B', e₁, e₂, hs⟩ := h (L.objPreimage X) (L.objPreimage Y)
    have : Small.{w} (L.obj A' ⟶ L.obj B') := small_of_surjective hs
    have : Small.{w} (L.obj (L.objPreimage X) ⟶ L.obj (L.objPreimage Y)) :=
      small_map (e₁.homCongr e₂)
    exact small_map ((L.objObjPreimageIso X).homCongr (L.objObjPreimageIso Y)).symm

namespace ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Definition 7.3.1(1).** An object `X` is a fibrant model if every map from a
cofibrant object extends along every trivial cofibration. -/
def IsFibrantModel (X : C) : Prop :=
  ∀ ⦃A B : C⦄ (f : A ⟶ X) (i : A ⟶ B), IsCofibrant A → Cofibration i → WeakEquivalence i →
    ∃ h : B ⟶ X, i ≫ h = f

/-- **Proposition 7.3.2(1)** (Cisinski). For `A` cofibrant and `B` a fibrant model,
every map `A ⟶ B` of the homotopy category is the image of a map of `C`. -/
theorem map_surjective_of_isFibrantModel {A B : C} [IsCofibrant A] (hB : IsFibrantModel B)
    (φ : L.obj A ⟶ L.obj B) : ∃ g : A ⟶ B, L.map g = φ := by
  obtain ⟨B', t, hB', ht⟩ := exists_cofibrant_replacement B
  have := hB'
  have := Localization.inverts L (weakEquivalences C) t ht.mem
  obtain ⟨Z, i, s, -, hs, hsw, h⟩ :=
    exists_ambient_trivialCofibration_fraction L (φ ≫ inv (L.map t))
  obtain ⟨k, hk⟩ := hB t s hB' hs hsw
  refine ⟨i ≫ k, ?_⟩
  rw [L.map_comp, ← h, Category.assoc, ← L.map_comp, hk, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]

/-- The Baues axiom BCF6: every object has a trivial cofibration into an object
on which every trivial cofibration has a retraction. -/
def BauesAxiom : Prop :=
  ∀ X : C, ∃ (Y : C) (s : X ⟶ Y), Cofibration s ∧ WeakEquivalence s ∧
    ∀ ⦃Z : C⦄ (j : Z ⟶ Y), Cofibration j → WeakEquivalence j → ∃ r : Y ⟶ Z, j ≫ r = 𝟙 Z

/-- **Proposition 7.3.4(1).** Under BCF6, for cofibrant `A` and `B`, every map
`A ⟶ B` of the homotopy category is the image of a map, and two maps have the same
image exactly when they are left homotopic. -/
theorem map_surjective_of_bauesAxiom (h6 : BauesAxiom (C := C)) {A B : C} [IsCofibrant A]
    [IsCofibrant B] (φ : L.obj A ⟶ L.obj B) : ∃ g : A ⟶ B, L.map g = φ := by
  let := hasBinaryCoproduct A B
  obtain ⟨Z, i, s, hZ, hi, hs, hsw, -, h⟩ := exists_ambient_cofibration_fraction_with_coprod L φ
  obtain ⟨Y, s', hs', hsw', hret⟩ := h6 Z
  obtain ⟨r, hr⟩ := hret (s ≫ s') inferInstance inferInstance
  refine ⟨i ≫ s' ≫ r, ?_⟩
  rw [L.map_comp, ← h, Category.assoc, ← L.map_comp, ← Category.assoc s, hr, L.map_id,
    Category.comp_id]

/-- **Proposition 7.3.4(1)**, injectivity: between cofibrant objects, two maps have
the same image in the homotopy category iff they are left homotopic. -/
theorem map_eq_iff_leftHomotopy {A B : C} [IsCofibrant A] [IsCofibrant B]
    [HasBinaryCoproduct A A] (g g' : A ⟶ B) :
    L.map g = L.map g' ↔ LeftHomotopyRel g g' :=
  ambient_map_eq_iff_cofibrant_leftHomotopy L (X := CofibrantObject.mk A)
    (Y := CofibrantObject.mk B) (CofibrantObject.homMk g) (CofibrantObject.homMk g')

include L in
/-- **Proposition 7.3.3(1).** If every cofibrant object admits a weak equivalence to
a fibrant model, the homotopy category of a locally small precofibration category
is locally small. -/
theorem locallySmall_of_fibrantModels [LocallySmall.{w} C]
    (h : ∀ A : C, IsCofibrant A → ∃ (A' : C) (a : A ⟶ A'), WeakEquivalence a ∧ IsFibrantModel A') :
    LocallySmall.{w} D := by
  have := Localization.essSurj L (weakEquivalences C)
  refine locallySmall_of_surjective L fun A B ↦ ?_
  obtain ⟨A₁, q, hA₁, hq⟩ := exists_cofibrant_replacement A
  obtain ⟨B₁, q', hB₁, hq'⟩ := exists_cofibrant_replacement B
  obtain ⟨B₂, b, hb, hB₂⟩ := h B₁ hB₁
  have := hA₁
  exact ⟨A₁, B₂, (Localization.isoOfHom L _ q hq.mem).symm,
    (Localization.isoOfHom L _ q' hq'.mem).symm ≪≫ Localization.isoOfHom L _ b hb.mem,
    fun φ ↦ map_surjective_of_isFibrantModel L hB₂ φ⟩

include L in
/-- **Corollary 7.3.5(1)**, Baues form: under BCF6, the homotopy category of a
locally small precofibration category is locally small. -/
theorem locallySmall_of_bauesAxiom [LocallySmall.{w} C] (h6 : BauesAxiom (C := C)) :
    LocallySmall.{w} D := by
  have := Localization.essSurj L (weakEquivalences C)
  refine locallySmall_of_surjective L fun A B ↦ ?_
  obtain ⟨A₁, q, hA₁, hq⟩ := exists_cofibrant_replacement A
  obtain ⟨B₁, q', hB₁, hq'⟩ := exists_cofibrant_replacement B
  have := hA₁
  have := hB₁
  exact ⟨A₁, B₁, (Localization.isoOfHom L _ q hq.mem).symm,
    (Localization.isoOfHom L _ q' hq'.mem).symm, fun φ ↦ map_surjective_of_bauesAxiom L h6 φ⟩

end ABCPrecofibrationCategory

namespace ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization (weakEquivalences C)]

/-- **Definition 7.3.1(2).** An object `X` is a cofibrant model if every map to a
fibrant object lifts along every trivial fibration. -/
def IsCofibrantModel (X : C) : Prop :=
  ∀ ⦃E D : C⦄ (g : X ⟶ D) (p : E ⟶ D), IsFibrant D → Fibration p → WeakEquivalence p →
    ∃ h : X ⟶ E, h ≫ p = g

/-- **Proposition 7.3.2(2).** For `A` a cofibrant model and `B` fibrant, every map
`A ⟶ B` of the homotopy category is the image of a map of `C`. -/
theorem map_surjective_of_isCofibrantModel {A B : C} [IsFibrant B] (hA : IsCofibrantModel A)
    (φ : L.obj A ⟶ L.obj B) : ∃ g : A ⟶ B, L.map g = φ := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  have hA' : ABCPrecofibrationCategory.IsFibrantModel (Opposite.op A) := by
    intro E D f i hE hi hw
    obtain ⟨h, hh⟩ := hA f.unop i.unop ((isFibrant_iff_isCofibrant_op _).2 hE)
      ((fibration_unop_iff i).2 hi) ((weakEquivalences_unop_iff i).2 hw)
    exact ⟨h.op, Quiver.Hom.unop_inj hh⟩
  obtain ⟨g, hg⟩ :=
    ABCPrecofibrationCategory.map_surjective_of_isFibrantModel L.op hA' φ.op
  exact ⟨g.unop, Quiver.Hom.op_inj hg⟩

/-- **Proposition 7.3.4(2).** Under BF6 (BCF6 in the opposite category), for fibrant
`A` and `B`, every map `A ⟶ B` of the homotopy category is the image of a map. -/
theorem map_surjective_of_bauesAxiom
    (h6 : ABCPrecofibrationCategory.BauesAxiom (C := Cᵒᵖ)) {A B : C} [IsFibrant A]
    [IsFibrant B] (φ : L.obj A ⟶ L.obj B) : ∃ g : A ⟶ B, L.map g = φ := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  obtain ⟨g, hg⟩ := ABCPrecofibrationCategory.map_surjective_of_bauesAxiom L.op h6
    (A := Opposite.op B) (B := Opposite.op A) φ.op
  exact ⟨g.unop, Quiver.Hom.op_inj hg⟩

include L in
/-- **Proposition 7.3.3(2).** If every fibrant object admits a weak equivalence from
a cofibrant model, the homotopy category of a locally small prefibration category
is locally small. -/
theorem locallySmall_of_cofibrantModels [LocallySmall.{w} C]
    (h : ∀ A : C, IsFibrant A → ∃ (A' : C) (a : A' ⟶ A), WeakEquivalence a ∧ IsCofibrantModel A') :
    LocallySmall.{w} D := by
  have := Localization.essSurj L (weakEquivalences C)
  refine locallySmall_of_surjective L fun A B ↦ ?_
  obtain ⟨A₁, q, hA₁, hq⟩ := exists_fibrant_replacement A
  obtain ⟨A₂, a, ha, hA₂⟩ := h A₁ hA₁
  obtain ⟨B₁, q', hB₁, hq'⟩ := exists_fibrant_replacement B
  have := hB₁
  exact ⟨A₂, B₁, Localization.isoOfHom L _ q hq.mem ≪≫ (Localization.isoOfHom L _ a ha.mem).symm,
    Localization.isoOfHom L _ q' hq'.mem, fun φ ↦ map_surjective_of_isCofibrantModel L hA₂ φ⟩

include L in
/-- **Corollary 7.3.5(2)**, Baues form: under BF6, the homotopy category of a
locally small prefibration category is locally small. -/
theorem locallySmall_of_bauesAxiom [LocallySmall.{w} C]
    (h6 : ABCPrecofibrationCategory.BauesAxiom (C := Cᵒᵖ)) : LocallySmall.{w} D := by
  have := Localization.essSurj L (weakEquivalences C)
  refine locallySmall_of_surjective L fun A B ↦ ?_
  obtain ⟨A₁, q, hA₁, hq⟩ := exists_fibrant_replacement A
  obtain ⟨B₁, q', hB₁, hq'⟩ := exists_fibrant_replacement B
  have := hA₁
  have := hB₁
  exact ⟨A₁, B₁, Localization.isoOfHom L _ q hq.mem, Localization.isoOfHom L _ q' hq'.mem,
    fun φ ↦ map_surjective_of_bauesAxiom L h6 φ⟩

end ABCPrefibrationCategory

end ABCCofibrations

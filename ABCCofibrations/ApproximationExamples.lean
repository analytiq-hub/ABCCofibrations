/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.CofibrantApproximationFractions
public import ABCCofibrations.ApproximationTheorem
public import ABCCofibrations.FibrantApproximation

/-!
# Cofibrant and fibrant approximations are approximations (Theorem 6.1.5)

A cofibrant approximation (Definition 6.1.1) is a left approximation in the
sense of Definition 5.4.1, and a fibrant approximation is a right approximation.
For cofibrant approximations, LAP1 comes from CFA4 applied to the image of the
initial object, LAP2(1) from CFA4 applied to a source sum, and LAP2(2) is Lemma
6.1.4(1). The fibration statements, including Lemma 6.1.3(2), follow in the
opposite categories.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits HomotopicalAlgebra Localization

namespace ABCCofibrations

namespace IsCofibrantApproximation

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D] [ABCPrecofibrationCategory D]
  (F : C ⥤ D) [IsCofibrantApproximation F]

/-- **Theorem 6.1.5(1).** A cofibrant approximation is a left approximation. -/
theorem leftApproximation {H : Type*} [Category H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] :
    LeftApproximation (toLocalizerMorphism F) L where
  exists_resolution B := by
    let h₀ := isColimitOfHasInitialOfPreservesColimit F
    obtain ⟨Z, -, p, -, hp, -⟩ := factorization (F := F) (h₀.desc (asEmptyCocone B))
    exact ⟨Z, p, hp.mem⟩
  nonempty_factorizationData {A' B' B} f p hp := by
    let p' : F.obj B' ⟶ B := p
    have : WeakEquivalence p' := ⟨hp⟩
    obtain ⟨φ⟩ := ResolutionFraction.nonempty F (𝟙 (F.obj A')) p' f
    exact ⟨⟨φ.fraction.Y', φ.fraction.f, φ.fraction.s, φ.comparison, φ.fraction.hs,
      φ.comparison_weakEquivalence.mem, φ.numerator.trans (Category.id_comp _), φ.denominator⟩⟩
  hom_eq {A' B' B f p} d₁ d₂ := by
    let σ₁ : F.obj d₁.D ⟶ B := d₁.σ
    let σ₂ : F.obj d₂.D ⟶ B := d₂.σ
    have : WeakEquivalence σ₁ := ⟨d₁.hσ⟩
    have : WeakEquivalence σ₂ := ⟨d₂.hσ⟩
    exact fraction_map_eq_of_ambient_comparison F ⟨d₁.i, d₁.j, d₁.hj⟩ ⟨d₂.i, d₂.j, d₂.hj⟩
      σ₁ σ₂ (d₁.fac_i.trans d₂.fac_i.symm) (d₁.fac_j.trans d₂.fac_j.symm) L
      (Localization.inverts L _)

end IsCofibrantApproximation

namespace IsFibrantApproximation

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type u'} [Category.{v'} D] [CategoryWithFibrations D]
  [CategoryWithWeakEquivalences D] [HasTerminal D] [ABCPrefibrationCategory D]
  (F : C ⥤ D) [IsFibrantApproximation F]

/-- **Theorem 6.1.5(2).** A fibrant approximation is a right approximation. -/
theorem rightApproximation {H : Type*} [Category H] (L : C ⥤ H)
    [L.IsLocalization (weakEquivalences C)] :
    RightApproximation (toLocalizerMorphism F) L := by
  have : L.op.IsLocalization (weakEquivalences Cᵒᵖ) :=
    inferInstanceAs (L.op.IsLocalization (weakEquivalences C).op)
  exact IsCofibrantApproximation.leftApproximation F.op L.op

/-- **Lemma 6.1.3(2).** For a fibrant approximation `t`, maps `f, g : A ⟶ B` of
the source with `t(f) ∘ a = t(g) ∘ a` for a weak equivalence `a : A' ⟶ tA` have
the same image under every functor inverting weak equivalences. -/
theorem map_eq_of_map_precomp_eq {E : Type*} [Category E] (G : C ⥤ E)
    (hG : (weakEquivalences C).IsInvertedBy G) {A B : C} (f g : A ⟶ B) {X : D}
    (a : X ⟶ F.obj A) [WeakEquivalence a] (h : a ≫ F.map f = a ≫ F.map g) :
    G.map f = G.map g := by
  have : WeakEquivalence a.op := (weakEquivalences_op_iff a).2 inferInstance
  have hG' : (weakEquivalences Cᵒᵖ).IsInvertedBy G.op := fun _ _ w hw ↦ by
    have := hG w.unop hw
    change IsIso (G.map w.unop).op
    infer_instance
  have := IsCofibrantApproximation.map_eq_of_map_postcomp_eq (F := F.op) G.op hG' f.op g.op
    a.op (by
      change (F.map f).op ≫ a.op = (F.map g).op ≫ a.op
      rw [← op_comp, h, op_comp])
  exact Quiver.Hom.op_inj this

end IsFibrantApproximation

end ABCCofibrations

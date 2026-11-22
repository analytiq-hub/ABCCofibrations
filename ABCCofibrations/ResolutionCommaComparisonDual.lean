/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionCommaComparison
public import ABCCofibrations.ResolutionSliceContraction

/-! # The inverse-side comma comparison of Lemma 9.5.1(2)

The paper asserts (d₂ ↓ u pᵢ) ≅ Δ′ᵒᵖ(d₂ ↓ u). We obtain it from Lemma 9.5.1(1)
for `u.op` by duality.

Δ′ is functorial in the labelling category, but it is **not** invariant under
equivalences of categories: its morphisms commute with labels strictly. The
duality therefore uses that mathlib's functors

  (d₂ ↓ u)ᵒᵖ ⇄ (u.op ↓ op d₂)

are inverse to each other on the nose. `resolutionMapEquivOfInverse` turns such
a strict pair into an equivalence of resolutions. The remaining steps are
ordinary equivalences of comma categories.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v₁ v₂ u₁ u₂
open CategoryTheory Limits Opposite
namespace ABCCofibrations

section Functoriality

variable {D : Type*} [Category D] {E : Type*} [Category E] {F : Type*} [Category F]

theorem resolutionMap_comp (G : D ⥤ E) (H : E ⥤ F) :
    resolutionMap (G ⋙ H) = resolutionMap G ⋙ resolutionMap H :=
  rfl

theorem resolutionMap_id : resolutionMap (𝟭 D) = 𝟭 (SemisimplicialResolution D) :=
  rfl

/-- Strictly inverse functors induce an equivalence of direct resolutions.
(A mere equivalence `D ≌ E` does not suffice.) -/
def resolutionMapEquivOfInverse (G : D ⥤ E) (H : E ⥤ D) (h₁ : G ⋙ H = 𝟭 D)
    (h₂ : H ⋙ G = 𝟭 E) : SemisimplicialResolution D ≌ SemisimplicialResolution E :=
  CategoryTheory.Equivalence.mk (resolutionMap G) (resolutionMap H)
    (eqToIso (by rw [← resolutionMap_comp, h₁, resolutionMap_id]))
    (eqToIso (by rw [← resolutionMap_comp, h₂, resolutionMap_id]))

end Functoriality

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]
  (u : D₁ ⥤ D₂) (d₂ : D₂)

theorem structuredArrow_toCostructuredArrow_comp :
    StructuredArrow.toCostructuredArrow u d₂ ⋙
      (CostructuredArrow.toStructuredArrow' u d₂).rightOp = 𝟭 _ :=
  rfl

theorem costructuredArrow_toStructuredArrow'_comp :
    (CostructuredArrow.toStructuredArrow' u d₂).rightOp ⋙
      StructuredArrow.toCostructuredArrow u d₂ = 𝟭 _ :=
  rfl

/-- Δ′ applied to the strict isomorphism (d₂ ↓ u)ᵒᵖ ≅ (u.op ↓ op d₂). -/
def resolutionStructuredArrowOpEquivalence :
    SemisimplicialResolution (StructuredArrow d₂ u)ᵒᵖ ≌
      SemisimplicialResolution (CostructuredArrow u.op (op d₂)) :=
  resolutionMapEquivOfInverse _ _ (structuredArrow_toCostructuredArrow_comp u d₂)
    (costructuredArrow_toStructuredArrow'_comp u d₂)

/-- The comma categories of the two projections are dual:
(pₜ u.op ↓ op d₂)ᵒᵖ ≌ (d₂ ↓ u pᵢ). -/
noncomputable def resolutionTerminalCommaOpEquivalence :
    (CostructuredArrow (resolutionTerminal D₁ᵒᵖ ⋙ u.op) (op d₂))ᵒᵖ ≌
      StructuredArrow d₂ (resolutionInitial D₁ ⋙ u) :=
  (costructuredArrowOpEquivalence (resolutionTerminal D₁ᵒᵖ ⋙ u.op) (op d₂)).trans
    (StructuredArrow.post (op (op d₂)) (resolutionTerminal D₁ᵒᵖ ⋙ u.op).op
      (opOpEquivalence D₂).functor).asEquivalence

/-- Lemma 9.5.1(2): Δ′ᵒᵖ(d₂ ↓ u) ≌ (d₂ ↓ u pᵢ), by duality from 9.5.1(1). -/
noncomputable def resolutionStructuredCommaEquivalence :
    CosemisimplicialResolution (StructuredArrow d₂ u) ≌
      StructuredArrow d₂ (resolutionInitial D₁ ⋙ u) :=
  ((resolutionStructuredArrowOpEquivalence u d₂).trans
    (resolutionCommaEquivalence u.op (op d₂))).op.trans
    (resolutionTerminalCommaOpEquivalence u d₂)

/-! ### The dual contraction of (d ↓ pᵢ), Lemma 9.5.2(2)(b) -/

section Coslice

variable {D : Type u₁} [Category.{v₁} D] (d : D)

/-- The initial object `(d, 1_d)` of the coslice `d/D`. -/
noncomputable def cosliceInitial :
    IsInitial (StructuredArrow.mk (𝟙 d) : StructuredArrow d (𝟭 D)) :=
  StructuredArrow.mkIdInitial (T := 𝟭 D) (Y := d)

/-- Dual of aᵈ: prepend `d` to every chain under `d`, transported along 9.5.1(2). -/
noncomputable def resolutionCoslicePrepend :
    StructuredArrow d (resolutionInitial D ⋙ 𝟭 D) ⥤ StructuredArrow d (resolutionInitial D ⋙ 𝟭 D) :=
  (resolutionStructuredCommaEquivalence (𝟭 D) d).inverse ⋙
    coresolutionPrepend (cosliceInitial d) ⋙ (resolutionStructuredCommaEquivalence (𝟭 D) d).functor

/-- Dual of α: the projection from the prepended chain onto the original one. -/
noncomputable def resolutionCoslicePrependToId : resolutionCoslicePrepend d ⟶ 𝟭 _ :=
  Functor.whiskerLeft (resolutionStructuredCommaEquivalence (𝟭 D) d).inverse
    (Functor.whiskerRight (coresolutionPrependToId (cosliceInitial d))
      (resolutionStructuredCommaEquivalence (𝟭 D) d).functor) ≫
    (resolutionStructuredCommaEquivalence (𝟭 D) d).counitIso.hom

/-- The object `d →1 (d)` of `(d ↓ pᵢ)`. -/
noncomputable def resolutionCosliceCenter : StructuredArrow d (resolutionInitial D ⋙ 𝟭 D) :=
  (resolutionStructuredCommaEquivalence (𝟭 D) d).functor.obj
    (op (resolutionSingleton (op (StructuredArrow.mk (𝟙 d) : StructuredArrow d (𝟭 D)))))

/-- Dual of β: the projection onto the new initial vertex. -/
noncomputable def resolutionCoslicePrependToCenter :
    resolutionCoslicePrepend d ⟶ (Functor.const _).obj (resolutionCosliceCenter d) :=
  Functor.whiskerLeft (resolutionStructuredCommaEquivalence (𝟭 D) d).inverse
    (Functor.whiskerRight (coresolutionPrependToSingleton (cosliceInitial d))
      (resolutionStructuredCommaEquivalence (𝟭 D) d).functor ≫ (Functor.constComp _ _ _).hom)

end Coslice

end ABCCofibrations

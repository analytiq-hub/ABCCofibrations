/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.AdjunctionKan
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Grothendieck
public import Mathlib.CategoryTheory.Limits.Fubini
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Limits.Opposites
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
# Relative colimits, cofinality and the Grothendieck construction (Chapter 8)

Lemmas 8.2.1, 8.2.2, 8.5.2, Propositions 8.5.3, 8.5.4, 8.6.1(1), 8.6.2 and
Corollary 8.6.3.
These are classical facts about diagrams; mathlib proves them, and we restate
them in the paper's form.

The relative colimit `colim^u X` of the paper is the (pointwise) left Kan
extension of `X` along `u`, and `lim^u X` the right Kan extension. A *right
cofinal* functor (colimits) is mathlib's `Functor.Final`, a *left cofinal* one
mathlib's `Functor.Initial`.
-/

@[expose] public section

open CategoryTheory Limits Functor

namespace ABCCofibrations

section RelativeColimits

variable {D₁ D₂ M : Type*} [Category D₁] [Category D₂] [Category M] (u : D₁ ⥤ D₂) (X : D₁ ⥤ M)

/-- **Lemma 8.2.1(1).** If the colimits of `X` over the comma categories `(u ↓ d)`
exist, the relative colimit `colim^u X` exists and is computed by them. -/
theorem hasLeftKanExtension_of_hasColimit_comma
    [∀ d, HasColimit (CostructuredArrow.proj u d ⋙ X)] :
    HasLeftKanExtension u X ∧
      ∀ d, Nonempty ((u.leftKanExtension X).obj d ≅ colimit (CostructuredArrow.proj u d ⋙ X)) :=
  ⟨inferInstance, fun d ↦ ⟨leftKanExtensionObjIsoColimit u X d⟩⟩

/-- **Lemma 8.2.1(2).** If the limits of `X` over the comma categories `(d ↓ u)`
exist, the relative limit `lim^u X` exists and is computed by them. -/
theorem hasRightKanExtension_of_hasLimit_comma
    [∀ d, HasLimit (StructuredArrow.proj d u ⋙ X)] :
    HasRightKanExtension u X ∧
      ∀ d, Nonempty ((u.rightKanExtension X).obj d ≅ limit (StructuredArrow.proj d u ⋙ X)) :=
  ⟨inferInstance, fun d ↦ ⟨(isPointwiseRightKanExtensionOfIsRightKanExtension _
    (u.rightKanExtensionCounit X) d).isoLimit⟩⟩

variable {D₃ : Type*} [Category D₃] (v : D₂ ⥤ D₃)

/-- **Lemma 8.2.2(1).** If `colim^u X` exists, then `colim^v colim^u X` exists iff
`colim^{vu} X` does, and then they are canonically isomorphic. -/
theorem leftKanExtension_comp [HasLeftKanExtension u X] :
    (HasLeftKanExtension v (u.leftKanExtension X) ↔ HasLeftKanExtension (u ⋙ v) X) ∧
      ∀ [HasLeftKanExtension v (u.leftKanExtension X)] [HasLeftKanExtension (u ⋙ v) X],
        Nonempty ((u ⋙ v).leftKanExtension X ≅ v.leftKanExtension (u.leftKanExtension X)) := by
  refine ⟨hasLeftKanExtension_comp_iff (u.leftKanExtensionUnit X), ?_⟩
  intro _ _
  have := (isLeftKanExtension_comp_iff (u.leftKanExtensionUnit X)
    (v.leftKanExtensionUnit (u.leftKanExtension X))).1 inferInstance
  exact ⟨leftKanExtensionUnique _ ((u ⋙ v).leftKanExtensionUnit X) _
    (u.leftKanExtensionUnit X ≫ whiskerLeft u (v.leftKanExtensionUnit (u.leftKanExtension X)) ≫
      (associator u v _).inv)⟩

/-- **Lemma 8.2.2(2).** If `lim^u X` exists, then `lim^v lim^u X` exists iff
`lim^{vu} X` does, and then they are canonically isomorphic. -/
theorem rightKanExtension_comp [HasRightKanExtension u X] :
    (HasRightKanExtension v (u.rightKanExtension X) ↔ HasRightKanExtension (u ⋙ v) X) ∧
      ∀ [HasRightKanExtension v (u.rightKanExtension X)] [HasRightKanExtension (u ⋙ v) X],
        Nonempty ((u ⋙ v).rightKanExtension X ≅ v.rightKanExtension (u.rightKanExtension X)) := by
  refine ⟨hasRightKanExtension_comp_iff (u.rightKanExtensionCounit X), ?_⟩
  intro _ _
  have := (isRightKanExtension_comp_iff (u.rightKanExtensionCounit X)
    (v.rightKanExtensionCounit (u.rightKanExtension X))).1 inferInstance
  exact ⟨rightKanExtensionUnique _ ((u ⋙ v).rightKanExtensionCounit X) _
    ((associator u v _).hom ≫ whiskerLeft u (v.rightKanExtensionCounit (u.rightKanExtension X)) ≫
      u.rightKanExtensionCounit X)⟩

end RelativeColimits

section Cofinality

/-- **Lemma 8.5.2.** For an adjunction `u ⊣ v`, `u` is left cofinal and `v` is
right cofinal. The paper's *homotopy* cofinality (contractible nerves of the
comma categories) is witnessed by the terminal objects of the comma categories
`(u ↓ d₂)` and the initial objects of `(d₁ ↓ v)`. -/
theorem adjunction_cofinal {D₁ D₂ : Type*} [Category D₁] [Category D₂] {u : D₁ ⥤ D₂}
    {v : D₂ ⥤ D₁} (adj : u ⊣ v) :
    u.Initial ∧ v.Final ∧
      (∀ d₂, Nonempty (IsTerminal (CostructuredArrow.mk (adj.counit.app d₂) :
        CostructuredArrow u d₂))) ∧
      ∀ d₁, Nonempty (IsInitial (StructuredArrow.mk (adj.unit.app d₁) :
        StructuredArrow d₁ v)) :=
  ⟨initial_of_adjunction adj, final_of_adjunction adj,
    fun d₂ ↦ ⟨mkTerminalOfRightAdjoint _ adj d₂⟩, fun d₁ ↦ ⟨mkInitialOfLeftAdjoint _ adj d₁⟩⟩

/-- **Proposition 8.5.3(1).** A functor between small categories is right cofinal
iff, for every cocomplete category, restriction along it preserves colimits. -/
theorem final_iff_isIso_colimit_pre {D₁ D₂ : Type v} [SmallCategory D₁] [SmallCategory D₂]
    (u : D₁ ⥤ D₂) :
    u.Final ↔ ∀ (M : Type (v + 1)) [Category.{v} M] [HasColimitsOfSize.{v, v} M] (X : D₂ ⥤ M),
      IsIso (colimit.pre X u) :=
  ⟨fun _ _ _ _ _ ↦ inferInstance,
    fun h ↦ (Functor.final_iff_isIso_colimit_pre u).2 fun G ↦ h (Type v) G⟩

/-- **Proposition 8.5.3(2).** A functor between small categories is left cofinal
iff, for every complete category, restriction along it preserves limits. For
the converse, the test category `(Type v)ᵒᵖ` turns the criterion into the
colimit criterion for `u.op`. -/
theorem initial_iff_isIso_limit_pre {D₁ D₂ : Type v} [SmallCategory D₁] [SmallCategory D₂]
    (u : D₁ ⥤ D₂) :
    u.Initial ↔ ∀ (M : Type (v + 1)) [Category.{v} M] [HasLimitsOfSize.{v, v} M] (X : D₂ ⥤ M),
      IsIso (limit.pre X u) := by
  refine ⟨fun _ _ _ _ _ ↦ inferInstance, fun h ↦ ?_⟩
  have : u.op.Final := (Functor.final_iff_isIso_colimit_pre u.op).2 fun G ↦ by
    have := h (Type v)ᵒᵖ G.rightOp
    have key : (colimit.pre G u.op).op = (limitRightOpIsoOpColimit G).inv ≫
        limit.pre G.rightOp u ≫ (limitRightOpIsoOpColimit (u.op ⋙ G)).hom := by
      apply Quiver.Hom.unop_inj
      apply colimit.hom_ext
      intro j
      apply Quiver.Hom.op_inj
      simp only [op_comp, Quiver.Hom.op_unop, Category.assoc,
        limitRightOpIsoOpColimit_hom_comp_ι]
      change _ = _ ≫ limit.pre G.rightOp u ≫ limit.π (u ⋙ G.rightOp) j.unop
      rw [limit.pre_π, limitRightOpIsoOpColimit_inv_comp_π, ← op_comp, colimit.ι_pre]
      rfl
    have : IsIso (colimit.pre G u.op).op := by
      rw [key]
      infer_instance
    exact (isIso_op_iff _).1 this
  exact initial_of_final_op u

variable {D₁ D₂ M : Type*} [Category D₁] [Category D₂] [Category M] (u : D₁ ⥤ D₂) (X : D₂ ⥤ M)

/-- **Proposition 8.5.4(1).** For a right cofinal functor `u`, the colimit of `X`
exists iff that of `u*X` does, and then the comparison is an isomorphism. -/
theorem final_hasColimit_iff [u.Final] :
    (HasColimit (u ⋙ X) ↔ HasColimit X) ∧ ∀ [HasColimit X], IsIso (colimit.pre X u) :=
  ⟨⟨fun _ ↦ Functor.Final.hasColimit_of_comp u, fun _ ↦ inferInstance⟩, fun {_} ↦ inferInstance⟩

/-- **Proposition 8.5.4(2).** For a left cofinal functor `u`, the limit of `X`
exists iff that of `u*X` does, and then the comparison is an isomorphism. -/
theorem initial_hasLimit_iff [u.Initial] :
    (HasLimit (u ⋙ X) ↔ HasLimit X) ∧ ∀ [HasLimit X], IsIso (limit.pre X u) :=
  ⟨⟨fun _ ↦ Functor.Initial.hasLimit_of_comp u, fun _ ↦ inferInstance⟩, fun {_} ↦ inferInstance⟩

end Cofinality

section GrothendieckAdjoint

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (F : C ⥤ Cat.{v₂, u₂}) (d : C)

/-- The inclusion of the fiber `p⁻¹d = F(d)` into the comma category `(p ↓ d)` of
the projection `p : ∫ F ⥤ C`. -/
def fiberInclusion : F.obj d ⥤ CostructuredArrow (Grothendieck.forget F) d :=
  (Grothendieck.ι F d).toCostructuredArrow (Grothendieck.forget F) d (fun _ ↦ 𝟙 d)
    (fun _ ↦ Category.id_comp _)

variable {F d} in
lemma fiberInclusion_base {X : CostructuredArrow (Grothendieck.forget F) d} {y : F.obj d}
    (g : X ⟶ (fiberInclusion F d).obj y) : g.left.base = X.hom :=
  (Category.comp_id _).symm.trans (CostructuredArrow.w g)

omit [Category.{v₁} C] in
private lemma eqToHom_comp_eq {𝒞 : Type*} [Category 𝒞] {A B B' Y Y' Y'' Z : 𝒞} (p : A = B)
    (q : A = B') (r : B' = B) (h : B ⟶ Y) (s : Y = Y') (t : Y' = Y'') (g : Y'' ⟶ Z)
    (st : Y = Y'') (g' : Y ⟶ Z) (hg : g' = eqToHom st ≫ g) :
    eqToHom p ≫ h ≫ g' = eqToHom q ≫ eqToHom r ≫ h ≫ eqToHom s ≫ eqToHom t ≫ g := by
  subst q r s t hg
  simp

/-- The hom-equivalence of the left adjoint of `fiberInclusion`. -/
def fiberInclusionHomEquiv (X : CostructuredArrow (Grothendieck.forget F) d) (y : F.obj d) :
    ((F.map X.hom).toFunctor.obj X.left.fiber ⟶ y) ≃ (X ⟶ (fiberInclusion F d).obj y) where
  toFun φ := CostructuredArrow.homMk (⟨X.hom, φ⟩ : X.left ⟶ ⟨d, y⟩) (Category.comp_id _)
  invFun g := eqToHom (congrArg (fun b ↦ (F.map b).toFunctor.obj X.left.fiber)
    (fiberInclusion_base g).symm) ≫ g.left.fiber
  left_inv φ := by
    change eqToHom rfl ≫ φ = φ
    rw [eqToHom_refl, Category.id_comp]
  right_inv g := by
    have hb := fiberInclusion_base g
    obtain ⟨⟨b, φ⟩, ⟨⟨⟩⟩, w⟩ := g
    change b = X.hom at hb
    subst hb
    apply CostructuredArrow.hom_ext
    refine Grothendieck.ext _ _ rfl ?_
    change eqToHom _ ≫ (eqToHom _ ≫ φ) = φ
    simp

/-- **Proposition 8.6.1(1).** For `F : C ⥤ Cat` with projection
`p : ∫ F ⥤ C`, the inclusion of the fiber `p⁻¹d = F(d)` into `(p ↓ d)` has a left
adjoint, sending `((d₁, x₁), f₁ : d₁ ⟶ d)` to `F(f₁)(x₁)`. -/
theorem fiberInclusion_isRightAdjoint : (fiberInclusion F d).IsRightAdjoint :=
  (Adjunction.adjunctionOfEquivLeft (fiberInclusionHomEquiv F d) (by
    intro X y y' g h
    apply CostructuredArrow.hom_ext
    refine Grothendieck.ext _ _ (Category.comp_id X.hom).symm ?_
    change eqToHom _ ≫ (h ≫ g) = eqToHom _ ≫ (F.map (𝟙 d)).toFunctor.map h ≫ (eqToHom _ ≫ g)
    rw [Functor.congr_hom (congrArg Cat.Hom.toFunctor (F.map_id d)) h]
    simp only [Cat.Hom.id_toFunctor, Functor.id_map, Category.assoc]
    exact eqToHom_comp_eq (𝒞 := F.obj d) _ _ _ _ _ _ _ rfl _ (by simp))).isRightAdjoint

end GrothendieckAdjoint

section Grothendieck

variable {C : Type*} [Category C] {F : C ⥤ Cat} {M : Type*} [Category M]
  (G : Grothendieck F ⥤ M)
  [∀ {X Y : C} (f : X ⟶ Y), HasColimit ((F.map f).toFunctor ⋙ Grothendieck.ι F Y ⋙ G)]

/-- **Proposition 8.6.2(1).** If the colimits over the fibers exist (in mathlib's
form: the restrictions along the transition functors have colimits), the colimit
over the Grothendieck construction exists iff the colimit of the fiberwise
colimits does, and then they agree. -/
theorem grothendieck_colimit :
    (HasColimit G ↔ HasColimit (fiberwiseColimit G)) ∧
      ∀ [HasColimit G], Nonempty (@colimit _ _ _ _ (fiberwiseColimit G)
        (hasColimit_fiberwiseColimit G) ≅ colimit G) := by
  refine ⟨⟨fun _ ↦ ?_, fun _ ↦ ?_⟩, ?_⟩
  · exact hasColimit_fiberwiseColimit G
  · exact hasColimit_of_hasColimit_fiberwiseColimit_of_hasColimit G
  intro _
  let _ := hasColimit_fiberwiseColimit G
  exact ⟨colimitFiberwiseColimitIso G⟩

end Grothendieck

section ContravariantGrothendieck

variable {D : Type*} [Category D] {H : Dᵒᵖ ⥤ Cat} {M : Type*} [Category M]
  (X : (Grothendieck (H ⋙ Cat.opFunctor))ᵒᵖ ⥤ M)
  [∀ {x y : Dᵒᵖ} (f : x ⟶ y),
    HasColimit (((H ⋙ Cat.opFunctor).map f).toFunctor ⋙ Grothendieck.ι _ y ⋙ X.rightOp)]

/-- **Proposition 8.6.2(2).** For `H : Dᵒᵖ ⥤ Cat`, the contravariant
Grothendieck construction is `∫^D H = (∫_{Dᵒᵖ} Hᵒᵖ)ᵒᵖ`. If the limits over the
fibers exist (mathlib's hypothesis for `X.rightOp`), the limit of `X` over
`∫^D H` exists iff the limit over `D` of the fiberwise limits does, and then
they agree. The fiberwise limits are the unopposites of the fiberwise colimits
of `X.rightOp` in `Mᵒᵖ`. -/
theorem grothendieck_limit :
    (HasLimit X ↔ HasLimit (fiberwiseColimit X.rightOp).unop) ∧
      ∀ [HasLimit X], ∃ (_ : HasLimit (fiberwiseColimit X.rightOp).unop),
        Nonempty (limit X ≅ limit (fiberwiseColimit X.rightOp).unop) := by
  have e₁ : HasLimit X ↔ HasColimit X.rightOp :=
    ⟨fun _ ↦ inferInstance, fun _ ↦ (inferInstance : HasLimit X.rightOp.leftOp)⟩
  have e₂ : HasColimit (fiberwiseColimit X.rightOp) ↔ HasLimit (fiberwiseColimit X.rightOp).unop :=
    ⟨fun _ ↦ inferInstance, fun _ ↦ hasColimit_of_hasLimit_unop _⟩
  refine ⟨e₁.trans ((grothendieck_colimit X.rightOp).1.trans e₂), ?_⟩
  intro hX
  have := e₁.1 hX
  have := hasColimit_fiberwiseColimit X.rightOp
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact (limitLeftOpIsoUnopColimit X.rightOp :) ≪≫
    (colimitFiberwiseColimitIso X.rightOp).unop ≪≫
    (limitUnopIsoUnopColimit (fiberwiseColimit X.rightOp)).symm

end ContravariantGrothendieck

section Fubini

variable {J K M : Type*} [Category J] [Category K] [Category M] (G : J × K ⥤ M)

/-- **Corollary 8.6.3(1)** (Fubini). The colimit over a product is the iterated
colimit, when the inner colimits are given by `colim` (mathlib's hypotheses). -/
theorem colimit_prod [HasColimitsOfShape K M] [HasColimit (curry.obj G ⋙ colim)] :
    ∃ (_ : HasColimit G), Nonempty (colimit G ≅ colimit (curry.obj G ⋙ colim)) :=
  ⟨inferInstance, ⟨colimitIsoColimitCurryCompColim G⟩⟩

/-- **Corollary 8.6.3(2)** (Fubini). The limit over a product is the iterated
limit. -/
theorem limit_prod [HasLimitsOfShape K M] [HasLimit (curry.obj G ⋙ lim)] :
    ∃ (_ : HasLimit G), Nonempty (limit G ≅ limit (curry.obj G ⋙ lim)) :=
  ⟨inferInstance, ⟨limitIsoLimitCurryCompLim G⟩⟩

end Fubini

end ABCCofibrations

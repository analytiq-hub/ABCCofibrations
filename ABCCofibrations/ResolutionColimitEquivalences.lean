/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionCommaColimit
public import ABCCofibrations.ResolutionFiberReedyCounterexample

/-! # Proposition 9.5.4(1), repaired

Let `D : Type` be small, `M` a cofibration category, and `X, X′` Reedy cofibrant
restricted diagrams on Δ′D. The relative colimit `colim_{pₜ} X` is computed
pointwise by `colim_{(pₜ ↓ d)} X` (`resolutionCommaDiagram d X`).

* (a) For `Y : D ⥤ M` and `f : X ⟶ pₜ* Y`, `f` is a pointwise weak equivalence
  iff each adjoint map `colim_{(pₜ ↓ d)} X ⟶ Y_d` is a weak equivalence
  (`resolution_adjoint_weakEquivalence_iff`).
* (b) For `f : X ⟶ X′`, `f` is a pointwise weak equivalence iff each induced
  map `colim_{(pₜ ↓ d)} X ⟶ colim_{(pₜ ↓ d)} X′` is a weak equivalence
  (`resolution_colimMap_weakEquivalence_iff`).

The proof follows the paper's final step, but its input
`X_(d) ≃ colim_{(pₜ ↓ d)} X` is now `weakEquivalence_resolutionComma_colimit_ι`,
which does not use the false Lemma 9.5.3. A restricted diagram inverts the
selection of the last vertex `(xₙ) ⟶ x`, so every value of `X` is weakly
equivalent to a value at a singleton.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite HomotopicalAlgebra
namespace ABCCofibrations

variable {D : Type} [SmallCategory D]

/-- The selection of the last vertex `(xₙ) ⟶ x`. -/
def resolutionLastVertex (x : SemisimplicialResolution D) :
    resolutionSingleton ((resolutionTerminal D).obj x) ⟶ x :=
  resolutionSelect x (Fin.last _) rfl

/-- The selection of the last vertex has identity terminal component. -/
theorem resolutionTerminal_map_lastVertex (x : SemisimplicialResolution D) :
    (resolutionTerminal D).map (resolutionLastVertex x) = 𝟙 _ := by
  change eqToHom _ ≫ (resolutionLabel x).map (homOfLE (Fin.le_last _)) = 𝟙 _
  rw [show (homOfLE (Fin.le_last (resolutionOrd (resolutionLastVertex x) (Fin.last 0))) :
      Fin.last _ ⟶ Fin.last _) = 𝟙 _ from Subsingleton.elim _ _]
  simp only [eqToHom_refl]
  exact (Category.id_comp _).trans ((resolutionLabel x).map_id _)

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{0} M]

omit [CategoryWithCofibrations M] [HasInitial M] [ABCCofibrationCategory M] in
/-- A restricted diagram inverts the selection of the last vertex. -/
theorem weakEquivalence_map_lastVertex (X : SemisimplicialResolution D ⥤ M)
    (hX : IsResolutionRestricted X) (x : SemisimplicialResolution D) :
    WeakEquivalence (X.map (resolutionLastVertex x)) :=
  hX _ rfl (resolutionTerminal_map_lastVertex x)

/-- A map out of a restricted diagram is a pointwise weak equivalence as soon
as it is one at all singletons. -/
theorem weakEquivalence_app_of_singletons {X X' : SemisimplicialResolution D ⥤ M}
    (hX : IsResolutionRestricted X) (f : X ⟶ X')
    (hX' : ∀ x, WeakEquivalence (X'.map (resolutionLastVertex x)))
    (hs : ∀ d : D, WeakEquivalence (f.app (resolutionSingleton d)))
    (x : SemisimplicialResolution D) : WeakEquivalence (f.app x) := by
  have := weakEquivalence_map_lastVertex X hX x
  have := hs ((resolutionTerminal D).obj x)
  have := hX' x
  have : WeakEquivalence (X.map (resolutionLastVertex x) ≫ f.app x) := by
    rw [f.naturality]
    infer_instance
  exact weakEquivalence_of_precomp (X.map (resolutionLastVertex x)) _

/-- The adjoint of `f : X ⟶ pₜ* Y` at `d`, on the pointwise relative colimit. -/
noncomputable def resolutionAdjointCocone {X : SemisimplicialResolution D ⥤ M} {Y : D ⥤ M}
    (f : X ⟶ resolutionTerminal D ⋙ Y) (d : D) : Cocone (resolutionCommaDiagram d X) where
  pt := Y.obj d
  ι :=
    { app := fun x ↦ f.app x.left ≫ Y.map x.hom
      naturality := fun x x' g ↦ by
        change X.map g.left ≫ f.app x'.left ≫ Y.map x'.hom = (f.app x.left ≫ Y.map x.hom) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, f.naturality, Category.assoc,
          CategoryTheory.Functor.comp_map, ← Y.map_comp]
        exact congrArg (f.app x.left ≫ Y.map ·) (CostructuredArrow.w g) }

/-- **Proposition 9.5.4(1)(a).** For Reedy cofibrant restricted `X`, a map
`f : X ⟶ pₜ* Y` is a pointwise weak equivalence iff all its adjoint maps
`colim_{(pₜ ↓ d)} X ⟶ Y_d` are weak equivalences. -/
theorem resolution_adjoint_weakEquivalence_iff (X : SemisimplicialResolution D ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hXR : IsReedyCofibrant X)
    (hX : IsResolutionRestricted X) {Y : D ⥤ M} (f : X ⟶ resolutionTerminal D ⋙ Y) :
    ∃ _ : ∀ d, HasColimit (resolutionCommaDiagram d X),
      ((∀ x, WeakEquivalence (f.app x)) ↔
        ∀ d, WeakEquivalence (colimit.desc _ (resolutionAdjointCocone f d))) := by
  choose hc hι using fun d ↦ weakEquivalence_resolutionComma_colimit_ι d X hXR hX
  refine ⟨hc, ?_⟩
  have key (d : D) : colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d) ≫
      colimit.desc _ (resolutionAdjointCocone f d) = f.app (resolutionSingleton d) := by
    rw [colimit.ι_desc]
    change f.app (resolutionSingleton d) ≫ Y.map (𝟙 d) = _
    simp
  constructor
  · intro hf d
    have := hι d
    have : WeakEquivalence (colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d) ≫
        colimit.desc _ (resolutionAdjointCocone f d)) := by
      rw [key]
      exact hf _
    exact weakEquivalence_of_precomp
      (colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d)) _
  · intro hd
    refine weakEquivalence_app_of_singletons hX f
      (fun x ↦ ?_) (fun d ↦ ?_)
    · change WeakEquivalence (Y.map ((resolutionTerminal D).map (resolutionLastVertex x)))
      rw [resolutionTerminal_map_lastVertex, Y.map_id]
      exact ABCPrecofibrationCategory.weakEquivalence_of_isIso _
    · have := hι d
      have := hd d
      rw [← key]
      infer_instance

/-- **Proposition 9.5.4(1)(b).** For Reedy cofibrant restricted `X, X′`, a map
`f : X ⟶ X′` is a pointwise weak equivalence iff the induced maps
`colim_{(pₜ ↓ d)} X ⟶ colim_{(pₜ ↓ d)} X′` are weak equivalences. -/
theorem resolution_colimMap_weakEquivalence_iff (X X' : SemisimplicialResolution D ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram X' e)]
    (hXR : IsReedyCofibrant X) (hX'R : IsReedyCofibrant X')
    (hX : IsResolutionRestricted X) (hX' : IsResolutionRestricted X') (f : X ⟶ X') :
    ∃ (_ : ∀ d, HasColimit (resolutionCommaDiagram d X))
      (_ : ∀ d, HasColimit (resolutionCommaDiagram d X')),
      ((∀ x, WeakEquivalence (f.app x)) ↔
        ∀ d, WeakEquivalence
          (colimMap (Functor.whiskerLeft
            (CostructuredArrow.proj (resolutionTerminal D ⋙ 𝟭 D) d) f))) := by
  choose hc hι using fun d ↦ weakEquivalence_resolutionComma_colimit_ι d X hXR hX
  choose hc' hι' using fun d ↦ weakEquivalence_resolutionComma_colimit_ι d X' hX'R hX'
  refine ⟨hc, hc', ?_⟩
  have key (d : D) : colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d) ≫
      colimMap (Functor.whiskerLeft (CostructuredArrow.proj (resolutionTerminal D ⋙ 𝟭 D) d) f) =
      f.app (resolutionSingleton d) ≫
        colimit.ι (resolutionCommaDiagram d X') (resolutionSliceCenter d) := by
    rw [ι_colimMap]
    rfl
  constructor
  · intro hf d
    have := hι d
    have := hι' d
    have := hf (resolutionSingleton d)
    have : WeakEquivalence (colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d) ≫
        colimMap (Functor.whiskerLeft
          (CostructuredArrow.proj (resolutionTerminal D ⋙ 𝟭 D) d) f)) := by
      rw [key]
      infer_instance
    exact weakEquivalence_of_precomp
      (colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d)) _
  · intro hd
    refine weakEquivalence_app_of_singletons hX f
      (weakEquivalence_map_lastVertex X' hX') (fun d ↦ ?_)
    have := hι d
    have := hι' d
    have := hd d
    have : WeakEquivalence (f.app (resolutionSingleton d) ≫
        colimit.ι (resolutionCommaDiagram d X') (resolutionSliceCenter d)) := by
      rw [← key]
      infer_instance
    exact weakEquivalence_of_postcomp _
      (colimit.ι (resolutionCommaDiagram d X') (resolutionSliceCenter d))

/-- The key step of 9.5.4 in Kan extension form: for Reedy cofibrant restricted
`X`, the pointwise left Kan extension `colim_{pₜ} X` exists, and its unit
`X_(d) ⟶ (colim_{pₜ} X)_d` is a weak equivalence. -/
theorem weakEquivalence_resolution_leftKanExtensionUnit (X : SemisimplicialResolution D ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hXR : IsReedyCofibrant X)
    (hX : IsResolutionRestricted X) :
    ∃ _ : (resolutionTerminal D).HasPointwiseLeftKanExtension X, ∀ d : D,
      WeakEquivalence (((resolutionTerminal D).leftKanExtensionUnit X).app
        (resolutionSingleton d)) := by
  choose hc hι using fun d ↦ weakEquivalence_resolutionComma_colimit_ι d X hXR hX
  have hK : (resolutionTerminal D).HasPointwiseLeftKanExtension X := fun d ↦ hc d
  refine ⟨hK, fun d ↦ ?_⟩
  have h := (resolutionTerminal D).leftKanExtensionUnit_leftKanExtensionObjIsoColimit_hom X
    (resolutionSingleton d)
  have : WeakEquivalence (((resolutionTerminal D).leftKanExtensionUnit X).app
      (resolutionSingleton d) ≫
      ((resolutionTerminal D).leftKanExtensionObjIsoColimit X
      ((resolutionTerminal D).obj (resolutionSingleton d))).hom) := by
    rw [h]
    exact hι d
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso
    ((resolutionTerminal D).leftKanExtensionObjIsoColimit X
      ((resolutionTerminal D).obj (resolutionSingleton d))).hom
  exact weakEquivalence_of_postcomp _ ((resolutionTerminal D).leftKanExtensionObjIsoColimit X
      ((resolutionTerminal D).obj (resolutionSingleton d))).hom

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionSliceContraction
public import Mathlib.CategoryTheory.Limits.Final

/-! # Finality of the fiber inclusion, Lemma 9.5.2(1)(c), repaired

The paper's fiber pₜ⁻¹(d) has the objects of Δ′D with terminal label `d` and the
maps whose terminal component is `1_d`. It is the full subcategory of
(pₜ ↓ d) on objects whose structure map is an identity, and `i_d` is that full
inclusion. Here the fiber is `ResolutionStrictFiber d`, defined directly as this
full subcategory of (pₜ ↓ d).

The paper proves that `i_d` is homotopy right cofinal by claiming that
(aᵈx, α_x) is initial in (x ↓ i_d). That claim is false (see
`ResolutionFiberCounterexample.lean`). We instead prove that `i_d` is final in
mathlib's sense: every (x ↓ i_d) is connected. Any object (y, g) is joined to
(aᵈx, α_x) by

  (y, g) ⟶ (aᵈy, g ≫ α_y) ⟵ (aᵈx, α_x),

via α_y and aᵈg, using only the naturality of α and the fact that aᵈ lands in
the fiber. In particular colimits over pₜ⁻¹(d) and over (pₜ ↓ d) agree, which
is the use made of 9.5.2(1)(c) in the proof of Proposition 9.5.4.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite
namespace ABCCofibrations

variable {D : Type u} [Category.{v} D] (d : D)

/-- Objects of (pₜ ↓ d) whose structure map is an identity. -/
def resolutionFiberProperty :
    ObjectProperty (CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d) :=
  fun p ↦ ∃ h : (resolutionTerminal D).obj p.left = d, p.hom = eqToHom h

/-- The paper's fiber pₜ⁻¹(d), as a full subcategory of (pₜ ↓ d). -/
abbrev ResolutionStrictFiber := (resolutionFiberProperty d).FullSubcategory

theorem eq_eqToHom_of_heq_id {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (h : X = Y)
    (hf : HEq f (𝟙 Y)) : f = eqToHom h := by
  subst h
  simpa using eq_of_heq hf

/-- aᵈ lands in the fiber. -/
theorem resolutionSliceAppend_mem (p : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d) :
    resolutionFiberProperty d ((resolutionSliceAppend d).obj p) :=
  ⟨resolutionSliceAppend_obj_last d p,
    eq_eqToHom_of_heq_id _ _ (resolutionSliceAppend_hom d p)⟩

/-- aᵈ as a functor into the fiber. -/
noncomputable def resolutionSliceAppendFiber :
    CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d ⥤ ResolutionStrictFiber d :=
  ObjectProperty.lift _ (resolutionSliceAppend d) (resolutionSliceAppend_mem d)

/-- The object (aᵈx, α_x) of (x ↓ i_d). -/
noncomputable def resolutionFiberCenter (x : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d) :
    StructuredArrow x (resolutionFiberProperty d).ι :=
  StructuredArrow.mk (T := (resolutionFiberProperty d).ι)
    (Y := (resolutionSliceAppendFiber d).obj x) ((resolutionSliceToAppend d).app x)

/-- For `f : x ⟶ i_d y`, the object (aᵈy, f ≫ α_y) of (x ↓ i_d). -/
noncomputable def resolutionFiberCenterOf {x y : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d}
    (f : x ⟶ y) : StructuredArrow x (resolutionFiberProperty d).ι :=
  StructuredArrow.mk (T := (resolutionFiberProperty d).ι)
    (Y := (resolutionSliceAppendFiber d).obj y) (f ≫ (resolutionSliceToAppend d).app y)

/-- Every object of (x ↓ i_d) is joined to (aᵈx, α_x). -/
theorem resolutionFiber_zigzag (x : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d)
    (j : StructuredArrow x (resolutionFiberProperty d).ι) :
    Zigzag j (resolutionFiberCenter d x) :=
  Zigzag.of_hom_inv (j₂ := resolutionFiberCenterOf d j.hom)
    (StructuredArrow.homMk ⟨(resolutionSliceToAppend d).app j.right.obj⟩ rfl)
    (StructuredArrow.homMk ⟨(resolutionSliceAppend d).map j.hom⟩
      ((resolutionSliceToAppend d).naturality j.hom).symm)

/-- Lemma 9.5.2(1)(c), repaired: the inclusion of the fiber pₜ⁻¹(d) into (pₜ ↓ d)
is final. -/
instance resolutionFiber_final : (resolutionFiberProperty d).ι.Final where
  out x :=
    have : Nonempty (StructuredArrow x (resolutionFiberProperty d).ι) :=
      ⟨resolutionFiberCenter d x⟩
    zigzag_isConnected fun j₁ j₂ ↦
      (resolutionFiber_zigzag d x j₁).trans (resolutionFiber_zigzag d x j₂).symm

/-- Colimits over the fiber and over (pₜ ↓ d) agree. -/
noncomputable def resolutionFiberColimitIso {M : Type*} [Category M]
    (G : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d ⥤ M) [HasColimit G] :
    colimit ((resolutionFiberProperty d).ι ⋙ G) ≅ colimit G :=
  Functor.Final.colimitIso _ G

end ABCCofibrations

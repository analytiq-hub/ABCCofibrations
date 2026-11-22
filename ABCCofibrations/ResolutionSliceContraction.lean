/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionCommaComparison

/-! # The contraction of (pₜ ↓ d) in Lemma 9.5.2(1)(b)

The slice `D/d = (𝟭 D ↓ d)` has the terminal object `(d, 1_d)`. Labelled
insertion of this object (`resolutionAppend`) contracts Δ′(D/d). Transported
along the comparison of Lemma 9.5.1(1) with `u = 𝟭 D`, it becomes the paper's
contraction of `(pₜ ↓ d)`:

  aᵈ : (d₀ → ⋯ → dₙ) → d   ↦   (d₀ → ⋯ → dₙ → d) →1 d,

with natural maps `α : 𝟭 ⟶ aᵈ` (the old vertices) and `β : cᵈ ⟶ aᵈ` (the new
vertex), where `cᵈ` is constant at `(d) →1 d`.

We use `CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d` for `(pₜ ↓ d)`. It is
definitionally the comma category of `resolutionTerminal D` itself.

This is the categorical zigzag only. It is not by itself the cofinality or
homotopy-colimit comparison needed for Proposition 9.5.4, and the paper's
Lemma 9.5.2(1)(a),(c) still rely on the refuted initial-object claim.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite
namespace ABCCofibrations

variable {D : Type u} [Category.{v} D] (d : D)

/-- The terminal object `(d, 1_d)` of the slice `D/d`. -/
noncomputable def sliceTerminal :
    IsTerminal (CostructuredArrow.mk (𝟙 d) : CostructuredArrow (𝟭 D) d) :=
  CostructuredArrow.mkIdTerminal (S := 𝟭 D) (Y := d)

/-- The paper's aᵈ: append `d`, with identity structure map, to every chain over `d`. -/
noncomputable def resolutionSliceAppend :
    CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d ⥤
      CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d :=
  resolutionCommaInverse (𝟭 D) d ⋙ resolutionAppend (sliceTerminal d) ⋙
    resolutionCommaCompare (𝟭 D) d

/-- The paper's α : 𝟭 ⟶ aᵈ, including the old vertices. -/
noncomputable def resolutionSliceToAppend : 𝟭 _ ⟶ resolutionSliceAppend d :=
  (resolutionCommaCounitIso (𝟭 D) d).inv ≫
    Functor.whiskerLeft (resolutionCommaInverse (𝟭 D) d)
      (Functor.whiskerRight (resolutionToAppend (sliceTerminal d))
        (resolutionCommaCompare (𝟭 D) d))

/-- The object `(d) →1 d` of `(pₜ ↓ d)`. -/
noncomputable def resolutionSliceCenter : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d :=
  (resolutionCommaCompare (𝟭 D) d).obj
    (resolutionSingleton (CostructuredArrow.mk (𝟙 d) : CostructuredArrow (𝟭 D) d))

@[simp] theorem resolutionSliceCenter_left :
    (resolutionSliceCenter d).left = resolutionSingleton d :=
  rfl

/-- The paper's β : cᵈ ⟶ aᵈ, selecting the new vertex. -/
noncomputable def resolutionSliceCenterToAppend :
    (Functor.const _).obj (resolutionSliceCenter d) ⟶ resolutionSliceAppend d :=
  Functor.whiskerLeft (resolutionCommaInverse (𝟭 D) d)
    ((Functor.constComp _ _ _).inv ≫
      Functor.whiskerRight (resolutionSingletonToAppend (sliceTerminal d))
        (resolutionCommaCompare (𝟭 D) d))

/-! ### The objects aᵈ(x) explicitly -/

section Objects

variable (p : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d)

/-- aᵈ adds exactly one vertex. -/
@[simp] theorem resolutionSliceAppend_len :
    ((resolutionSliceAppend d).obj p).left.unop.obj.unop.len = p.left.unop.obj.unop.len + 1 :=
  rfl

/-- aᵈ keeps the old vertices. -/
theorem resolutionSliceAppend_obj_castSucc (i : Fin (p.left.unop.obj.unop.len + 1)) :
    (resolutionLabel ((resolutionSliceAppend d).obj p).left).obj i.castSucc =
      (resolutionLabel p.left).obj i := by
  change ((appendTerminal (resolutionCommaLabel (𝟭 D) d p) (sliceTerminal d)).obj
    i.castSucc).left = _
  rw [appendTerminal_obj_cast]
  rfl

/-- aᵈ ends at `d`. -/
theorem resolutionSliceAppend_obj_last :
    (resolutionLabel ((resolutionSliceAppend d).obj p).left).obj
      (Fin.last (p.left.unop.obj.unop.len + 1)) = d := by
  change ((appendTerminal (resolutionCommaLabel (𝟭 D) d p) (sliceTerminal d)).obj
    (Fin.last _)).left = _
  rw [appendTerminal_obj_last]
  rfl

/-- The structure map of aᵈ(x) is the identity of `d`. -/
theorem resolutionSliceAppend_hom :
    HEq ((resolutionSliceAppend d).obj p).hom (𝟙 d) := by
  change HEq ((appendTerminal (resolutionCommaLabel (𝟭 D) d p) (sliceTerminal d)).obj
    (Fin.last _)).hom (CostructuredArrow.mk (𝟙 d) : CostructuredArrow (𝟭 D) d).hom
  rw [appendTerminal_obj_last]

end Objects

end ABCCofibrations

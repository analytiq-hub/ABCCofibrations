/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionFiberFinal

/-! # The initial-object step in the proof of Lemma 9.5.2(1)(c) fails

For `x = (d₀ → ⋯ → dₙ) → d` whose structure map is not an identity, the paper
asserts that (aᵈx, α_x) is initial in (x ↓ i_d). Take `D = Fin 2 = {0 → 1}`,
`d = 1`, and `x = (0) → 1`. Then aᵈx = (0 → 1) →1 1. With
`y = (0 → 1 →1 1) →1 1` and `g : x ⟶ y` selecting vertex 0, the new vertex of
aᵈx can go to either copy of `1`. This gives two distinct maps
(aᵈx, α_x) ⟶ (y, g) in (x ↓ i_d).

The conclusion of 9.5.2(1)(c) still holds in the form needed: see
`resolutionFiber_final`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite
namespace ABCCofibrations

namespace FiberCounterexample

/-- The base object `x = (0) → 1`. -/
def x : CostructuredArrow (resolutionTerminal (Fin 2) ⋙ 𝟭 (Fin 2)) 1 :=
  CostructuredArrow.mk (Y := resolutionSingleton (0 : Fin 2)) (homOfLE (by decide))

/-- The simplex `0 → 1 →1 1`. -/
def yLeft : SemisimplicialResolution (Fin 2) :=
  op ((semisimplicialNerve (Fin 2)).elementsMk (op (SemiSimplexCategory.mk 2))
    (ComposableArrows.mk₂ (homOfLE (by decide) : (0 : Fin 2) ⟶ 1) (𝟙 1)))

/-- The fiber object `(0 → 1 →1 1) →1 1`. -/
def y : ResolutionStrictFiber (1 : Fin 2) :=
  ⟨CostructuredArrow.mk (Y := yLeft) (𝟙 (1 : Fin 2)), rfl, rfl⟩

/-- The vertex `0 ↦ 0` from `[0]` to `[2]`. -/
def gOrd : SemiSimplexCategory.mk 0 ⟶ SemiSimplexCategory.mk 2 :=
  SemiSimplexCategory.homEquiv.symm
    (OrderEmbedding.ofStrictMono (fun _ ↦ (0 : Fin 3))
      (fun i j h ↦ by fin_cases i; fin_cases j; simp at h))

/-- `g : x ⟶ y`, selecting vertex 0. -/
def g : x ⟶ (resolutionFiberProperty (1 : Fin 2)).ι.obj y :=
  CostructuredArrow.homMk (Quiver.Hom.op ⟨gOrd.op, ComposableArrows.ext₀ rfl⟩)
    (Subsingleton.elim _ _)

/-- The object (y, g) of (x ↓ i_d). -/
def j : StructuredArrow x (resolutionFiberProperty (1 : Fin 2)).ι :=
  StructuredArrow.mk g

/-- The object (aᵈx, α_x) of (x ↓ i_d). -/
noncomputable def c : StructuredArrow x (resolutionFiberProperty (1 : Fin 2)).ι :=
  StructuredArrow.mk (T := (resolutionFiberProperty (1 : Fin 2)).ι)
    (Y := (resolutionSliceAppendFiber 1).obj x) ((resolutionSliceToAppend 1).app x)

/-- The two embeddings `[1] → [2]` fixing vertex 0. -/
def eOrd (k : Fin 2) : SemiSimplexCategory.mk 1 ⟶ SemiSimplexCategory.mk 2 :=
  SemiSimplexCategory.homEquiv.symm
    (if k = 0 then Fin.castSuccOrderEmb else Fin.succAboveOrderEmb 1)

/-- The two maps (aᵈx, α_x) ⟶ (y, g), sending the new vertex to 1 or to 2. -/
noncomputable def m (k : Fin 2) : c ⟶ j :=
  StructuredArrow.homMk
    ⟨CostructuredArrow.homMk
      (Quiver.Hom.op ⟨(eOrd k).op,
        CategoryTheory.Functor.ext (fun i ↦ by fin_cases k <;> fin_cases i <;> rfl)
          (fun _ _ _ ↦ Subsingleton.elim _ _)⟩)
      (Subsingleton.elim _ _)⟩
    (CostructuredArrow.hom_ext _ _ (resolution_hom_ext (by
      apply SemiSimplexCategory.hom_ext
      ext i
      fin_cases i
      fin_cases k <;> rfl)))

theorem m_ne : m 0 ≠ m 1 := by
  intro h
  have h' := congrArg
    (fun f ↦ SemiSimplexCategory.homEquiv ((resolutionOrdinal (Fin 2)).map f.right.hom.left) 1) h
  exact absurd h' (by decide)

/-- The paper's claimed initial object of (x ↓ i_d) is not initial. -/
theorem not_isInitial : IsInitial c → False :=
  fun hi ↦ m_ne (hi.hom_ext _ _)

end FiberCounterexample

end ABCCofibrations

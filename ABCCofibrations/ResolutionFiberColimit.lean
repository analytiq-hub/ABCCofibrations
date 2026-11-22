/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionFiberFinal
public import ABCCofibrations.ContractibleColimits
public import ABCCofibrations.ReedyKan

/-! # The fiber colimit step of Proposition 9.5.4, without an initial object

For a small category `D` (in `Type`), a cofibration category `M`, and a
restricted diagram `X : Δ′D ⥤ M` (one sending maps with identity terminal
component to weak equivalences), we prove that

  X_(d) ⟶ colim_{pₜ⁻¹(d)} X   and   X_(d) ⟶ colim_{(pₜ ↓ d)} X

are weak equivalences, provided the restriction of `X` to the fiber is Reedy
cofibrant. The paper's Lemma 9.5.3 asserts that this always holds. That
assertion appears to be false (see `docs/mathematics/semisimplicial-resolution.md`,
"Lemma 9.5.3 fails"), so the hypothesis is kept explicit here.

The paper obtains this from an initial object `e(d)` of the fiber, which does
not exist. Here it follows from Lemma K (`weakEquivalence_colimit_ι_of_contraction`)
applied to the contraction aᵈ, α, β, together with finality of the fiber
inclusion (`resolutionFiber_final`).

We work with `D : Type`, so that Δ′D and the fiber are small categories.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite HomotopicalAlgebra
namespace ABCCofibrations

variable {D : Type} [SmallCategory D] (d : D)

/-- The fiber pₜ⁻¹(d) is direct, with degree the simplex length. -/
instance resolutionStrictFiber_isDirect : IsDirect (ResolutionStrictFiber d) := by
  obtain ⟨deg, hdeg⟩ := (resolution_isDirect D).exists_deg
  refine ⟨⟨fun x ↦ deg x.obj.left, fun {x y} f ↦ ?_⟩⟩
  rcases hdeg_comma (resolutionTerminal D ⋙ 𝟭 D) deg hdeg f.hom with h | ⟨h, hf⟩
  · exact Or.inl h
  · right
    have hxy : x = y := ObjectProperty.FullSubcategory.ext h
    subst hxy
    refine ⟨rfl, ?_⟩
    apply ObjectProperty.hom_ext
    simpa using hf

/-- Maps in the fiber have identity terminal component. -/
theorem resolutionStrictFiber_terminal_map {p q : ResolutionStrictFiber d} (g : p ⟶ q) :
    ∃ h, (resolutionTerminal D).map g.hom.left = eqToHom h := by
  obtain ⟨hp, hp'⟩ := p.property
  obtain ⟨hq, hq'⟩ := q.property
  have w := CostructuredArrow.w g.hom
  rw [hp', hq'] at w
  refine ⟨hp.trans hq.symm, ?_⟩
  calc (resolutionTerminal D).map g.hom.left
      = ((resolutionTerminal D).map g.hom.left ≫ eqToHom hq) ≫ eqToHom hq.symm := by simp
    _ = eqToHom hp ≫ eqToHom hq.symm := by rw [← w]; rfl
    _ = eqToHom (hp.trans hq.symm) := by simp

/-- The object `(d) →1 d` of the fiber. -/
noncomputable def resolutionFiberBase : ResolutionStrictFiber d :=
  ⟨resolutionSliceCenter d, rfl, rfl⟩

/-- The contraction aᵈ, restricted to the fiber. -/
noncomputable def resolutionFiberAppend : ResolutionStrictFiber d ⥤ ResolutionStrictFiber d :=
  (resolutionFiberProperty d).ι ⋙ resolutionSliceAppendFiber d

/-- α, restricted to the fiber. -/
noncomputable def resolutionFiberToAppend : 𝟭 _ ⟶ resolutionFiberAppend d where
  app y := ⟨(resolutionSliceToAppend d).app y.obj⟩
  naturality _ _ f := ObjectProperty.hom_ext _ ((resolutionSliceToAppend d).naturality f.hom)

/-- β, restricted to the fiber. -/
noncomputable def resolutionFiberBaseToAppend :
    (Functor.const _).obj (resolutionFiberBase d) ⟶ resolutionFiberAppend d where
  app y := ⟨(resolutionSliceCenterToAppend d).app y.obj⟩
  naturality _ _ f :=
    ObjectProperty.hom_ext _ ((resolutionSliceCenterToAppend d).naturality f.hom)

/-- A diagram on Δ′D is restricted if it inverts maps with identity terminal
component. -/
def IsResolutionRestricted {M : Type u} [Category.{v} M] [CategoryWithWeakEquivalences M]
    (X : SemisimplicialResolution D ⥤ M) : Prop :=
  ∀ {x y : SemisimplicialResolution D} (f : x ⟶ y) (h : (resolutionTerminal D).obj x =
    (resolutionTerminal D).obj y), (resolutionTerminal D).map f = eqToHom h →
      WeakEquivalence (X.map f)

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{0} M]

/-- The diagram `X` on (pₜ ↓ d). -/
abbrev resolutionCommaDiagram (X : SemisimplicialResolution D ⥤ M) :
    CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d ⥤ M :=
  CostructuredArrow.proj _ _ ⋙ X

/-- The restriction of `X` to the fiber pₜ⁻¹(d). -/
abbrev resolutionFiberDiagram (X : SemisimplicialResolution D ⥤ M) :
    ResolutionStrictFiber d ⥤ M :=
  (resolutionFiberProperty d).ι ⋙ resolutionCommaDiagram d X

/-- The fiber step of 9.5.4: for a restricted `X` whose restriction to the fiber
is Reedy cofibrant, `X_(d) ⟶ colim_{pₜ⁻¹(d)} X` is a weak equivalence. The
Reedy hypothesis is not automatic (the paper's Lemma 9.5.3 is false). -/
theorem weakEquivalence_resolutionFiber_colimit (X : SemisimplicialResolution D ⥤ M)
    (hX : IsResolutionRestricted X)
    [∀ j, HasColimit (latchingDiagram (resolutionFiberDiagram d X) j)]
    (hR : IsReedyCofibrant (resolutionFiberDiagram d X)) :
    ∃ _ : HasColimit (resolutionFiberDiagram d X),
      WeakEquivalence (colimit.ι (resolutionFiberDiagram d X) (resolutionFiberBase d)) := by
  have hall {p q : ResolutionStrictFiber d} (g : p ⟶ q) :
      WeakEquivalence ((resolutionFiberDiagram d X).map g) := by
    obtain ⟨h, hg⟩ := resolutionStrictFiber_terminal_map d g
    exact hX g.hom.left h hg
  exact weakEquivalence_colimit_ι_of_contraction (resolutionFiberAppend d)
    (resolutionFiberBase d) (resolutionFiberToAppend d) (resolutionFiberBaseToAppend d)
    (resolutionFiberDiagram d X) hR (fun j ↦ hall _) (fun j ↦ hall _)

/-- The same weak equivalence into the colimit over (pₜ ↓ d), using finality of
the fiber inclusion. -/
theorem weakEquivalence_resolutionComma_colimit (X : SemisimplicialResolution D ⥤ M)
    (hX : IsResolutionRestricted X)
    [∀ j, HasColimit (latchingDiagram (resolutionFiberDiagram d X) j)]
    (hR : IsReedyCofibrant (resolutionFiberDiagram d X))
    [HasColimit (resolutionCommaDiagram d X)] :
    WeakEquivalence
      (colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d)) := by
  obtain ⟨_, hw⟩ := weakEquivalence_resolutionFiber_colimit d X hX hR
  change WeakEquivalence (colimit.ι (resolutionCommaDiagram d X)
    ((resolutionFiberProperty d).ι.obj (resolutionFiberBase d)))
  rw [← Functor.Final.ι_colimitIso_hom (resolutionFiberProperty d).ι
    (resolutionCommaDiagram d X) (resolutionFiberBase d)]
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso
    (Functor.Final.colimitIso (resolutionFiberProperty d).ι (resolutionCommaDiagram d X)).hom
  exact ⟨MorphismProperty.comp_mem _ _ _ hw.mem this.mem⟩

end ABCCofibrations

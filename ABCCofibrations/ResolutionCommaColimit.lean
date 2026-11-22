/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionFiberColimit

/-! # The key step of Proposition 9.5.4, repaired

For a small category `D` and a Reedy cofibrant, restricted diagram
`X : Δ′D ⥤ M` in a cofibration category, the map

  X_(d) ⟶ colim_{(pₜ ↓ d)} X = (colim_{pₜ} X)_d

is a weak equivalence.

The paper derives this by restricting `X` to the fiber pₜ⁻¹(d). That needs
Lemma 9.5.3, which is false (`FiberReedyCounterexample.not_isReedyCofibrant`),
and an initial object of the fiber, which does not exist. Here we work on
(pₜ ↓ d) directly. Restriction to (pₜ ↓ d) preserves Reedy cofibrancy
(`isReedyCofibrant_comma`), and Lemma K′
(`weakEquivalence_colimit_ι_of_weakContraction`) applies to the contraction
aᵈ, α, β. Its hypotheses concern only maps between objects with identity
structure map, which a restricted diagram inverts.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite HomotopicalAlgebra
namespace ABCCofibrations

variable {D : Type} [SmallCategory D] (d : D)
variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCCofibrationCategory.{0} M]

omit [CategoryWithCofibrations M] [HasInitial M] [ABCCofibrationCategory M] in
/-- A restricted diagram inverts every map of (pₜ ↓ d) between objects with
identity structure map. -/
theorem weakEquivalence_resolutionComma_map_of_fiber (X : SemisimplicialResolution D ⥤ M)
    (hX : IsResolutionRestricted X) {p q : CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d}
    (hp : resolutionFiberProperty d p) (hq : resolutionFiberProperty d q) (g : p ⟶ q) :
    WeakEquivalence ((resolutionCommaDiagram d X).map g) := by
  obtain ⟨h, hg⟩ := resolutionStrictFiber_terminal_map d (p := ⟨p, hp⟩) (q := ⟨q, hq⟩) ⟨g⟩
  exact hX g.left h hg

/-- **Proposition 9.5.4, key step (repaired).** For a Reedy cofibrant restricted
diagram `X` on Δ′D, the colimit over (pₜ ↓ d) exists and
`X_(d) ⟶ colim_{(pₜ ↓ d)} X` is a weak equivalence. -/
theorem weakEquivalence_resolutionComma_colimit_ι (X : SemisimplicialResolution D ⥤ M)
    [∀ e, HasColimit (latchingDiagram X e)] (hXR : IsReedyCofibrant X)
    (hX : IsResolutionRestricted X) :
    ∃ _ : HasColimit (resolutionCommaDiagram d X),
      WeakEquivalence (colimit.ι (resolutionCommaDiagram d X) (resolutionSliceCenter d)) := by
  obtain ⟨deg, hdeg⟩ := (resolution_isDirect D).exists_deg
  have : IsDirect (CostructuredArrow (resolutionTerminal D ⋙ 𝟭 D) d) :=
    ⟨⟨_, hdeg_comma _ deg hdeg⟩⟩
  obtain ⟨hL, hR⟩ := isReedyCofibrant_comma (resolutionTerminal D ⋙ 𝟭 D) deg hdeg X
    (d₂ := d) hXR
  have hc : resolutionFiberProperty d (resolutionSliceCenter d) := ⟨rfl, rfl⟩
  have hA := resolutionSliceAppend_mem d
  exact weakEquivalence_colimit_ι_of_weakContraction (resolutionSliceAppend d)
    (resolutionSliceCenter d) (resolutionSliceToAppend d) (resolutionSliceCenterToAppend d)
    (resolutionCommaDiagram d X) hR
    (fun _ ↦ weakEquivalence_resolutionComma_map_of_fiber d X hX (hA _) (hA _) _)
    (fun _ ↦ weakEquivalence_resolutionComma_map_of_fiber d X hX (hA _) (hA _) _)
    (weakEquivalence_resolutionComma_map_of_fiber d X hX hc (hA _) _)
    (weakEquivalence_resolutionComma_map_of_fiber d X hX (hA _) (hA _) _)

end ABCCofibrations

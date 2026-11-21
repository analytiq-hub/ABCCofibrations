/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SemisimplicialResolution

/-! # An obstruction to the initial-object assertion in Lemma 9.5.2

The semisimplex category has no initial object. In particular the category
Δ′ of all simplices of the terminal category cannot have the initial object
claimed in the paper. This does not refute its contractibility.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits
namespace ABCCofibrations

/-- Two different face inclusions out of every semisimplex. -/
theorem semisimplex_parallel_maps (x : SemiSimplexCategory) :
    ∃ (y : SemiSimplexCategory) (f g : x ⟶ y), f ≠ g := by
  cases x with | mk n =>
  refine ⟨⟨n + 1⟩,
    SemiSimplexCategory.homOfMono (SimplexCategory.δ (0 : Fin (n + 2))),
    SemiSimplexCategory.homOfMono (SimplexCategory.δ (Fin.last (n + 1))), ?_⟩
  intro h
  have hh := congrArg (fun f ↦ SemiSimplexCategory.toSimplexCategory.map f) h
  simp only [SemiSimplexCategory.toSimplexCategory_map_homOfMono] at hh
  have hi := SimplexCategory.δ_injective hh
  have := congrArg Fin.val hi
  simp at this

/-- Δ′ has no initial object, despite its contractible nerve. -/
theorem semisimplex_not_isInitial (x : SemiSimplexCategory) : IsInitial x → False := by
  intro hx
  obtain ⟨y, f, g, hfg⟩ := semisimplex_parallel_maps x
  exact hfg (hx.hom_ext f g)

/-- The full inverse-image category used for the fiber in §9.5. -/
abbrev ResolutionTerminalFiber {D : Type*} [Category D] (d : D) :=
  (show ObjectProperty (SemisimplicialResolution D) from
    fun x ↦ (resolutionTerminal D).obj x = d).FullSubcategory

/-- Constant simplices lie in the full terminal-projection fiber. -/
def resolutionFiberConstants {D : Type*} [Category D] (d : D) :
    SemiSimplexCategory ⥤ ResolutionTerminalFiber d :=
  ObjectProperty.lift _ (resolutionConstants d) (fun _ ↦ rfl)

/-- None of the constant simplices is initial in the full fiber.
In particular this disproves the paper's assertion about the singleton (d). -/
theorem resolutionFiber_constant_not_isInitial {D : Type*} [Category D] (d : D)
    (n : SemiSimplexCategory) :
    IsInitial ((resolutionFiberConstants d).obj n) → False := by
  intro hi
  obtain ⟨y, f, g, hfg⟩ := semisimplex_parallel_maps n
  have h := hi.hom_ext ((resolutionFiberConstants d).map f)
    ((resolutionFiberConstants d).map g)
  apply hfg
  apply (resolutionConstants d).map_injective
  exact congrArg (fun k ↦ k.hom) h

/-- In a one-object thin category every simplex is constant, so the entire
resolution has no initial object. This includes the terminal category. -/
theorem resolution_not_isInitial_of_subsingleton {D : Type*} [Category D]
    [Subsingleton D] [Quiver.IsThin D] (d : D) (x : SemisimplicialResolution D) :
    IsInitial x → False := by
  let n := (resolutionOrdinal D).obj x
  have hx : x = resolutionConstant d n := by
    have hu : x.unop = (resolutionConstant d n).unop := by
      refine Functor.Elements.ext x.unop (resolutionConstant d n).unop (by rfl) ?_
      change x.unop.val = (Functor.const (Fin (n.len + 1))).obj d
      exact CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)
        (fun _ _ _ ↦ Subsingleton.elim _ _)
    exact congrArg Opposite.op hu
  rw [hx]
  intro hi
  obtain ⟨y, f, g, hfg⟩ := semisimplex_parallel_maps n
  exact hfg ((resolutionConstants d).map_injective
    (hi.hom_ext ((resolutionConstants d).map f) ((resolutionConstants d).map g)))

/-- The terminal-category instance refutes the existence assertion in 9.5.2(1)(a). -/
theorem terminal_resolution_not_isInitial
    (x : SemisimplicialResolution (Discrete PUnit)) : IsInitial x → False :=
  resolution_not_isInitial_of_subsingleton (Discrete.mk PUnit.unit) x

end ABCCofibrations

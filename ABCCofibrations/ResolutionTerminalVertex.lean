/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.SemisimplicialResolution
public import ABCCofibrations.ReedyOpen
public import ABCCofibrations.ReedyConstantInitial
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Terminal-vertex-preserving simplices

A candidate repair for the initial-object argument in §9.5: mark the terminal
vertex by a map from the singleton. Maps in this category must preserve that
marking. This is not the full fiber of the terminal projection.
-/

@[expose] public section
universe v u
open CategoryTheory Limits
namespace ABCCofibrations
variable {D : Type u} [Category.{v} D]

/-- A marked vertex is terminal in the ordinal indexing the simplex. -/
def terminalVertexProp (d : D) : ObjectProperty (Under (resolutionSingleton d)) :=
  fun x ↦ SemiSimplexCategory.homEquiv ((resolutionOrdinal D).map x.hom) 0 =
    Fin.last ((resolutionOrdinal D).obj x.right).len

/-- Simplices whose terminal vertex is marked d, with marking-preserving maps. -/
abbrev TerminalVertexResolution (d : D) := (terminalVertexProp d).FullSubcategory

/-- The singleton, marked by its identity map. -/
def terminalVertexSingleton (d : D) : TerminalVertexResolution d :=
  ⟨Under.mk (𝟙 (resolutionSingleton d)), rfl⟩

/-- The marked singleton is initial, unlike the singleton in the full fiber. -/
noncomputable def terminalVertexSingletonIsInitial (d : D) :
    IsInitial (terminalVertexSingleton d) := by
  letI (x : TerminalVertexResolution d) : Unique (terminalVertexSingleton d ⟶ x) :=
    ⟨⟨ObjectProperty.homMk (Under.mkIdInitial.to x.obj)⟩,
      fun f ↦ ObjectProperty.hom_ext _ (Under.mkIdInitial.hom_ext _ _)⟩
  exact IsInitial.ofUnique _

/-- Forget the marked vertex. This functor need not be full. -/
def terminalVertexForget (d : D) : TerminalVertexResolution d ⥤ SemisimplicialResolution D :=
  ObjectProperty.ι _ ⋙ Under.forget _

/-- The label of a vertex selected by a singleton map. -/
theorem resolutionSingleton_vertex_label {d : D} {x : SemisimplicialResolution D}
    (f : resolutionSingleton d ⟶ x) :
    x.unop.val.obj (SemiSimplexCategory.homEquiv f.unop.hom.unop 0) = d := by
  exact congrArg (fun X ↦ X.obj 0) f.unop.map_val

/-- The forgotten simplex really does end at d. -/
theorem terminalVertex_label (d : D) (x : TerminalVertexResolution d) :
    (resolutionTerminal D).obj ((terminalVertexForget d).obj x) = d := by
  have h := resolutionSingleton_vertex_label x.obj.hom
  change x.obj.right.unop.val.obj _ = d at h ⊢
  rw [show SemiSimplexCategory.homEquiv x.obj.hom.unop.hom.unop 0 =
    Fin.last x.obj.right.unop.obj.unop.len from x.property] at h
  exact h

private theorem under_object_ext {E : Type*} [Category E] {a : E}
    {X Y : Under a} (h : X.right = Y.right)
    (hh : X.hom ≫ eqToHom h = Y.hom) : X = Y := by
  rcases X with ⟨⟨⟨⟩⟩, x, f⟩
  rcases Y with ⟨⟨⟨⟩⟩, y, g⟩
  change x = y at h
  subst y
  simp only [eqToHom_refl, Category.comp_id] at hh
  cases hh
  rfl

/-- The terminal-vertex-preserving category is still direct. -/
instance terminalVertex_isDirect (d : D) : IsDirect (TerminalVertexResolution d) := by
  let E := SemisimplicialResolution D
  obtain ⟨deg, hd⟩ := (resolution_isDirect D).exists_deg
  refine ⟨⟨fun x ↦ deg x.obj.right, fun {x y} f ↦ ?_⟩⟩
  rcases hd f.hom.right with hlt | ⟨heq, hf⟩
  · exact Or.inl hlt
  · right
    have hxy : x = y := by
      apply ObjectProperty.FullSubcategory.ext
      exact under_object_ext heq (by simpa [hf] using (Under.w f.hom))
    refine ⟨hxy, ?_⟩
    subst y
    apply ObjectProperty.hom_ext _
    apply Under.UnderMorphism.ext
    simpa using hf

/-- The marked vertices give a natural map from the constant singleton diagram.
Such a natural map is precisely what fails for the full unmarked fiber. -/
def terminalVertexPointToForget (d : D) :
    (Functor.const (TerminalVertexResolution d)).obj (resolutionSingleton d) ⟶
      terminalVertexForget d where
  app x := x.obj.hom
  naturality x y f := by
    change 𝟙 _ ≫ y.obj.hom = x.obj.hom ≫ f.hom.right
    rw [Category.id_comp]
    exact (Under.w f.hom).symm

/-- A constant cofibrant diagram on the marked category has latching colimits. -/
theorem terminalVertex_hasColimit_latching_const (d : D)
    {M : Type*} [Category M] [HomotopicalAlgebra.CategoryWithCofibrations M]
    [HomotopicalAlgebra.CategoryWithWeakEquivalences M] [HasInitial M]
    [ABCPrecofibrationCategory M] (A : M) (x : TerminalVertexResolution d) :
    HasColimit (latchingDiagram ((Functor.const (TerminalVertexResolution d)).obj A) x) :=
  hasColimit_latching_const_initial (terminalVertexSingletonIsInitial d) A x

/-- The constant-diagram Reedy step of the marked-vertex repair. -/
theorem terminalVertex_const_isReedyCofibrant (d : D)
    {M : Type*} [Category M] [HomotopicalAlgebra.CategoryWithCofibrations M]
    [HomotopicalAlgebra.CategoryWithWeakEquivalences M] [HasInitial M]
    [ABCPrecofibrationCategory M] (A : M) (hA : HomotopicalAlgebra.IsCofibrant A)
    [∀ x, HasColimit (latchingDiagram ((Functor.const (TerminalVertexResolution d)).obj A) x)] :
    IsReedyCofibrant ((Functor.const (TerminalVertexResolution d)).obj A) :=
  isReedyCofibrant_const_initial (terminalVertexSingletonIsInitial d) A hA

end ABCCofibrations

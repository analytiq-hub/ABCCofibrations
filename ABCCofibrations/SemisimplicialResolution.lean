/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBasic
public import Mathlib.AlgebraicTopology.SimplexCategory.SemiSimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # The direct resolution category of §9.5

The category Δ′D is the opposite category of elements of the nerve restricted
to injective ordinal maps. In particular all simplices, including degenerate
ones, are retained. Its degree is the length of the underlying simplex.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Limits Opposite
namespace ABCCofibrations

/-- The semisimplicial nerve: the nerve restricted to injective ordinal maps. -/
def semisimplicialNerve (D : Type u) [Category.{v} D] :
    SemiSimplexCategoryᵒᵖ ⥤ Type (max u v) :=
  SemiSimplexCategory.toSimplexCategory.op ⋙ nerve D

/-- The direct resolution category Δ′D of §9.5, retaining degenerate simplices. -/
abbrev SemisimplicialResolution (D : Type u) [Category.{v} D] :=
  (semisimplicialNerve D).Elementsᵒᵖ

/-- Forget the labels of a simplex, retaining its ordinal and injective maps. -/
def resolutionOrdinal (D : Type u) [Category.{v} D] :
    SemisimplicialResolution D ⥤ SemiSimplexCategory where
  obj x := x.unop.obj.unop
  map f := f.unop.hom.unop

instance (D : Type u) [Category.{v} D] : (resolutionOrdinal D).Faithful where
  map_injective h := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.Hom.ext
    exact Quiver.Hom.unop_inj h

instance {D : Type u} [Category.{v} D] {x y : SemisimplicialResolution D} (f : x ⟶ y) :
    Mono f := (resolutionOrdinal D).mono_of_mono_map inferInstance

instance semiSimplex_isDirect : IsDirect SemiSimplexCategory where
  exists_deg := by
    refine ⟨SemiSimplexCategory.len, fun {x y} f ↦ ?_⟩
    have hle := SimplexCategory.len_le_of_mono
      (SemiSimplexCategory.toSimplexCategory.map f)
    change x.len ≤ y.len at hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl hlt
    · right
      have hxy : x = y := SemiSimplexCategory.ext heq
      subst y
      refine ⟨rfl, ?_⟩
      apply SemiSimplexCategory.toSimplexCategory.map_injective
      simpa using SimplexCategory.eq_id_of_mono
        (SemiSimplexCategory.toSimplexCategory.map f)

/-- Every resolution category Δ′D is direct, independently of the arrows of D. -/
instance resolution_isDirect (D : Type u) [Category.{v} D] :
    IsDirect (SemisimplicialResolution D) where
  exists_deg := by
    refine ⟨fun x ↦ x.unop.obj.unop.len, fun {x y} f ↦ ?_⟩
    induction x using Opposite.rec with | _ x =>
      induction y using Opposite.rec with | _ y =>
        rcases x with @⟨a, x⟩
        rcases y with @⟨b, y⟩
        have hle := SimplexCategory.len_le_of_mono
          (SemiSimplexCategory.toSimplexCategory.map f.unop.hom.unop)
        change a.unop.len ≤ b.unop.len at hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact Or.inl hlt
        · right
          have ho : a = b := congrArg Opposite.op (SemiSimplexCategory.ext heq)
          subst b
          have hf : f.unop.hom = 𝟙 a := by
            apply Quiver.Hom.unop_inj
            apply SemiSimplexCategory.toSimplexCategory.map_injective
            simpa using SimplexCategory.eq_id_of_mono
              (SemiSimplexCategory.toSimplexCategory.map f.unop.hom.unop)
          have hv : y = x := by
            simpa [hf] using f.unop.map_val
          subst y
          refine ⟨rfl, ?_⟩
          apply Quiver.Hom.unop_inj
          apply Functor.Elements.Hom.ext
          exact hf

/-- The final vertex of a labelled simplex. -/
def resolutionTerminalObject {D : Type u} [Category.{v} D]
    (x : SemisimplicialResolution D) : D :=
  x.unop.val.obj (Fin.last x.unop.obj.unop.len)

/-- The terminal-vertex map associated to an injective simplex map. -/
def resolutionTerminalMap {D : Type u} [Category.{v} D]
    {x y : SemisimplicialResolution D} (f : x ⟶ y) :
    resolutionTerminalObject x ⟶ resolutionTerminalObject y :=
  eqToHom (congrArg (fun z ↦ z.obj (Fin.last x.unop.obj.unop.len)) f.unop.map_val.symm) ≫
    y.unop.val.map (homOfLE (Fin.le_last
      (SemiSimplexCategory.homEquiv f.unop.hom.unop (Fin.last x.unop.obj.unop.len))))

@[simp]
theorem resolutionTerminalMap_id {D : Type u} [Category.{v} D]
    (x : SemisimplicialResolution D) : resolutionTerminalMap (𝟙 x) = 𝟙 _ := by
  change eqToHom (rfl : resolutionTerminalObject x = _) ≫
    x.unop.val.map (𝟙 _) = 𝟙 _
  simp
  rfl

attribute [local semireducible] SemiSimplexCategory.Hom

@[simp]
theorem resolutionTerminalMap_comp {D : Type u} [Category.{v} D]
    {x y z : SemisimplicialResolution D} (f : x ⟶ y) (g : y ⟶ z) :
    resolutionTerminalMap (f ≫ g) = resolutionTerminalMap f ≫ resolutionTerminalMap g := by
  induction x using Opposite.rec with | _ x =>
    induction y using Opposite.rec with | _ y =>
      induction z using Opposite.rec with | _ z =>
        rcases x with @⟨a, X⟩
        rcases y with @⟨b, Y⟩
        rcases z with @⟨c, Z⟩
        rcases f with ⟨⟨ff, hf⟩⟩
        rcases g with ⟨⟨gg, hg⟩⟩
        change b ⟶ a at ff
        change c ⟶ b at gg
        change (SimplexCategory.toCat.map
          (SemiSimplexCategory.toSimplexCategory.map ff.unop)).toFunctor ⋙ Y = X at hf
        change (SimplexCategory.toCat.map
          (SemiSimplexCategory.toSimplexCategory.map gg.unop)).toFunctor ⋙ Z = Y at hg
        subst X
        subst Y
        simp only [resolutionTerminalMap]
        simp only [eqToHom_refl, Category.id_comp]
        erw [← Z.map_comp]
        exact congrArg Z.map (Subsingleton.elim _ _)

/-- The terminal projection pₜ : Δ′D ⥤ D of §9.5. -/
def resolutionTerminal (D : Type u) [Category.{v} D] : SemisimplicialResolution D ⥤ D where
  obj := resolutionTerminalObject
  map := resolutionTerminalMap

/-- A functor acts on the labels of all simplices of the direct resolution. -/
def resolutionMap {D E : Type u} [Category.{v} D] [Category.{v} E] (F : D ⥤ E) :
    SemisimplicialResolution D ⥤ SemisimplicialResolution E :=
  (NatTrans.mapElements (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op
    (nerveMap F))).op

/-- The terminal projection is natural in the category being resolved. -/
theorem resolutionMap_terminal {D E : Type u} [Category.{v} D] [Category.{v} E]
    (F : D ⥤ E) : resolutionMap F ⋙ resolutionTerminal E = resolutionTerminal D ⋙ F := by
  refine CategoryTheory.Functor.ext (F := resolutionMap F ⋙ resolutionTerminal E)
    (G := resolutionTerminal D ⋙ F) (fun _ ↦ rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change eqToHom _ ≫ F.map (y.unop.val.map _) =
    F.map (eqToHom _ ≫ y.unop.val.map _)
  rw [F.map_comp, eqToHom_map]

/-- The one-vertex simplex with label d. -/
def resolutionSingleton {D : Type u} [Category.{v} D] (d : D) :
    SemisimplicialResolution D :=
  op ((semisimplicialNerve D).elementsMk (op (SemiSimplexCategory.mk 0))
    (ComposableArrows.mk₀ d))

@[simp]
theorem resolutionTerminal_singleton {D : Type u} [Category.{v} D] (d : D) :
    (resolutionTerminal D).obj (resolutionSingleton d) = d := rfl

/-- The constant labelled simplex of any ordinal length. -/
def resolutionConstant {D : Type u} [Category.{v} D] (d : D)
    (n : SemiSimplexCategory) : SemisimplicialResolution D :=
  op ((semisimplicialNerve D).elementsMk (op n)
    ((Functor.const (Fin (n.len + 1))).obj d))

/-- The degenerate simplices at d include a faithful copy of Δ′ in Δ′D. -/
def resolutionConstants {D : Type u} [Category.{v} D] (d : D) :
    SemiSimplexCategory ⥤ SemisimplicialResolution D where
  obj := resolutionConstant d
  map f := Quiver.Hom.op ⟨f.op, rfl⟩

instance {D : Type u} [Category.{v} D] (d : D) : (resolutionConstants d).Faithful where
  map_injective h := by
    have hh := congrArg (fun f ↦ f.unop.hom.unop) h
    exact hh

@[simp]
theorem resolutionOrdinal_constants {D : Type u} [Category.{v} D] (d : D) :
    resolutionConstants d ⋙ resolutionOrdinal D = 𝟭 _ := rfl

@[simp]
theorem resolutionTerminal_constant {D : Type u} [Category.{v} D] (d : D)
    (n : SemiSimplexCategory) : (resolutionTerminal D).obj (resolutionConstant d n) = d := rfl

/-- The inverse resolution, obtained from the direct resolution of Dᵒᵖ by duality. -/
abbrev CosemisimplicialResolution (D : Type u) [Category.{v} D] :=
  (SemisimplicialResolution Dᵒᵖ)ᵒᵖ

instance coresolution_isInverse (D : Type u) [Category.{v} D] :
    IsInverse (CosemisimplicialResolution D) := by
  obtain ⟨deg, hdeg⟩ := (resolution_isDirect Dᵒᵖ).exists_deg
  refine ⟨⟨fun x ↦ deg x.unop.unop, fun {x y} f ↦ ?_⟩⟩
  rcases hdeg f.unop.unop with hlt | ⟨heq, hf⟩
  · exact Or.inl hlt
  · right
    have hxy : x = y := congrArg (fun z ↦ op (op z)) heq
    refine ⟨hxy, ?_⟩
    subst y
    apply Quiver.Hom.unop_inj
    apply Quiver.Hom.unop_inj
    simpa using hf

/-- The native initial projection, dual to the terminal projection on Dᵒᵖ. -/
def resolutionInitial (D : Type u) [Category.{v} D] : CosemisimplicialResolution D ⥤ D :=
  (resolutionTerminal Dᵒᵖ).op ⋙ CategoryTheory.unopUnop _

end ABCCofibrations

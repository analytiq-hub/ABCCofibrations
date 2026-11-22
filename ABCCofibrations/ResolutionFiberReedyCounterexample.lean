/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ResolutionFiberColimit
public import ABCCofibrations.ResolutionFiberCounterexample
public import ABCCofibrations.InjectiveSets

/-! # Lemma 9.5.3 is false

Lemma 9.5.3(1) of *Cofibrations in Homotopy Theory* asserts that the
restriction of a Reedy cofibrant diagram on Δ′D to a fiber pₜ⁻¹(d) is Reedy
cofibrant. We disprove it.

Take `M = InjSet` (sets, injections, all maps weak equivalences),
`D = Fin 2 = {0 → 1}`, `d = 1`, and `X = vertices`, which sends a chain to its
set of vertices. `X` is Reedy cofibrant and (trivially) restricted. At the fiber
object `y = (0 → 1 →1 1)` the fiber latching category contains the faces
`{0,1}` and `{0,2}` but not `{0}`. So the two copies of vertex `0` remain
distinct in the latching object, and the latching map is not injective.

The paper's proof treats the fiber latching category as the faces containing the
last vertex. Here `{0,1}` is a fiber face whose last vertex is the *other*
copy of `1`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits Opposite HomotopicalAlgebra
namespace ABCCofibrations

section General

variable {D : Type} [SmallCategory D]

/-- The underlying ordinal embedding of a map of Δ′D. -/
abbrev resolutionOrd {x y : SemisimplicialResolution D} (f : x ⟶ y) :=
  SemiSimplexCategory.homEquiv ((resolutionOrdinal D).map f)

/-- Maps of Δ′D between simplices of the same length are identities. -/
theorem resolution_eq_of_len_eq {x z : SemisimplicialResolution D} (f : x ⟶ z)
    (h : x.unop.obj.unop.len = z.unop.obj.unop.len) : x = z := by
  induction x using Opposite.rec with | _ x =>
  induction z using Opposite.rec with | _ z =>
  rcases x with @⟨a, X⟩
  rcases z with @⟨b, Y⟩
  have ho : a = b := congrArg Opposite.op (SemiSimplexCategory.ext h)
  subst b
  have hf : f.unop.hom = 𝟙 a := by
    apply Quiver.Hom.unop_inj
    apply SemiSimplexCategory.toSimplexCategory.map_injective
    simpa using SimplexCategory.eq_id_of_mono
      (SemiSimplexCategory.toSimplexCategory.map f.unop.hom.unop)
  have hv : Y = X := by simpa [hf] using f.unop.map_val
  subst Y
  rfl

theorem resolution_len_le {x z : SemisimplicialResolution D} (f : x ⟶ z) :
    x.unop.obj.unop.len ≤ z.unop.obj.unop.len :=
  SimplexCategory.len_le_of_mono (SemiSimplexCategory.toSimplexCategory.map f.unop.hom.unop)

/-- The label of a vertex is the label of its image. -/
theorem resolutionLabel_map {x z : SemisimplicialResolution D} (f : x ⟶ z)
    (i : Fin (x.unop.obj.unop.len + 1)) :
    (resolutionLabel x).obj i = (resolutionLabel z).obj (resolutionOrd f i) :=
  (congrArg (fun F : Fin (x.unop.obj.unop.len + 1) ⥤ D ↦ F.obj i) f.unop.map_val).symm

/-- Select one vertex of a simplex. -/
def resolutionSelect (z : SemisimplicialResolution D) (v : Fin (z.unop.obj.unop.len + 1))
    {c : D} (h : (resolutionLabel z).obj v = c) : resolutionSingleton c ⟶ z :=
  Quiver.Hom.op ⟨(SemiSimplexCategory.homEquiv.symm
    (OrderEmbedding.ofStrictMono (fun _ : Fin 1 ↦ v)
      (fun i j hij ↦ by fin_cases i; fin_cases j; simp at hij))).op,
    ComposableArrows.ext₀ h⟩

@[simp] theorem resolutionOrd_select (z : SemisimplicialResolution D)
    (v : Fin (z.unop.obj.unop.len + 1)) {c : D} (h : (resolutionLabel z).obj v = c)
    (i : Fin 1) : resolutionOrd (resolutionSelect z v h) i = v :=
  rfl

/-- The vertex functor on Δ′. -/
def semisimplexVertices : SemiSimplexCategory ⥤ Type where
  obj n := Fin (n.len + 1)
  map f := TypeCat.ofHom (SemiSimplexCategory.homEquiv f)

/-- The vertex diagram on Δ′D. -/
abbrev resolutionVertices (D : Type) [SmallCategory D] :
    SemisimplicialResolution D ⥤ Type :=
  resolutionOrdinal D ⋙ semisimplexVertices

theorem resolutionOrd_comp {x y z : SemisimplicialResolution D} (f : x ⟶ y) (g : y ⟶ z)
    (i : Fin (x.unop.obj.unop.len + 1)) :
    resolutionOrd (f ≫ g) i = resolutionOrd g (resolutionOrd f i) := by
  simp [resolutionOrd, Functor.map_comp, SemiSimplexCategory.homEquiv_comp]

/-- A singleton face of a simplex of positive length, as a latching object. -/
def resolutionSingletonFace (z : SemisimplicialResolution D) (hz : 0 < z.unop.obj.unop.len)
    (v : Fin (z.unop.obj.unop.len + 1)) : LatchingCategory z :=
  ⟨Over.mk (resolutionSelect z v rfl), fun h ↦ by
    have := congrArg (fun x : SemisimplicialResolution D ↦ x.unop.obj.unop.len) h
    change 0 = z.unop.obj.unop.len at this
    omega⟩

/-- Every latching element of the vertex diagram comes from a singleton face. -/
theorem resolutionVertices_latching_eq (z : SemisimplicialResolution D)
    (hz : 0 < z.unop.obj.unop.len) (j : LatchingCategory z)
    (x : (resolutionVertices D).obj j.obj.left) :
    colimit.ι (latchingDiagram (resolutionVertices D) z) j x =
      colimit.ι (latchingDiagram (resolutionVertices D) z)
        (resolutionSingletonFace z hz (resolutionOrd j.obj.hom x)) (0 : Fin 1) := by
  let g := resolutionSelect j.obj.left x (resolutionLabel_map j.obj.hom x)
  have w : g ≫ j.obj.hom = resolutionSelect z (resolutionOrd j.obj.hom x) rfl := by
    apply resolution_hom_ext
    apply SemiSimplexCategory.hom_ext
    refine DFunLike.ext _ _ (fun i ↦ ?_)
    exact (resolutionOrd_comp g j.obj.hom i).trans rfl
  let φ : resolutionSingletonFace z hz (resolutionOrd j.obj.hom x) ⟶ j := ⟨Over.homMk g w⟩
  rw [← colimit.w (latchingDiagram (resolutionVertices D) z) φ]
  rfl

/-- The length of a latching object is smaller. -/
theorem resolution_latching_len_lt {z : SemisimplicialResolution D} (j : LatchingCategory z) :
    j.obj.left.unop.obj.unop.len < z.unop.obj.unop.len :=
  lt_of_le_of_ne (resolution_len_le j.obj.hom)
    (fun h ↦ j.property (resolution_eq_of_len_eq j.obj.hom h))

/-- The vertex diagram, valued in `InjSet`. -/
abbrev resolutionVerticesInj (D : Type) [SmallCategory D] :
    SemisimplicialResolution D ⥤ InjSet :=
  resolutionVertices D

/-- The vertex diagram is Reedy cofibrant: its latching maps are injective. -/
theorem resolutionVertices_isReedyCofibrant : IsReedyCofibrant (resolutionVerticesInj D) := by
  intro z
  refine ⟨InjSet.isCofibrant _, ?_⟩
  rw [InjSet.cofibration_iff, mono_iff_injective]
  change Function.Injective (latchingMap (resolutionVertices D) z)
  intro a b hab
  obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (latchingDiagram (resolutionVertices D) z)) a
  obtain ⟨k, y, rfl⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (latchingDiagram (resolutionVertices D) z)) b
  have hz : 0 < z.unop.obj.unop.len :=
    lt_of_le_of_lt (Nat.zero_le _) (resolution_latching_len_lt j)
  have e1 := ConcreteCategory.congr_hom (ι_latchingMap (resolutionVertices D) z j) x
  have e2 := ConcreteCategory.congr_hom (ι_latchingMap (resolutionVertices D) z k) y
  have h1 : resolutionOrd j.obj.hom x = resolutionOrd k.obj.hom y :=
    e1.symm.trans (hab.trans e2)
  change colimit.ι (latchingDiagram (resolutionVertices D) z) j x =
    colimit.ι (latchingDiagram (resolutionVertices D) z) k y
  rw [resolutionVertices_latching_eq z hz j x, resolutionVertices_latching_eq z hz k y, h1]

end General

namespace FiberReedyCounterexample

open FiberCounterexample

/-- The edge `0 → 1`. -/
def zLeft : SemisimplicialResolution (Fin 2) :=
  op ((semisimplicialNerve (Fin 2)).elementsMk (op (SemiSimplexCategory.mk 1))
    (ComposableArrows.mk₁ (homOfLE (by decide) : (0 : Fin 2) ⟶ 1)))

/-- The fiber object `(0 → 1) →1 1`. -/
def z : ResolutionStrictFiber (1 : Fin 2) :=
  ⟨CostructuredArrow.mk (Y := zLeft) (𝟙 (1 : Fin 2)), rfl, rfl⟩

/-- The faces `{0,1}` (`k = 0`) and `{0,2}` (`k = 1`) of `y = (0 → 1 →1 1)`. -/
def m (k : Fin 2) : z ⟶ y :=
  ⟨CostructuredArrow.homMk
    (Quiver.Hom.op ⟨(eOrd k).op,
      CategoryTheory.Functor.ext (fun i ↦ by fin_cases k <;> fin_cases i <;> rfl)
        (fun _ _ _ ↦ Subsingleton.elim _ _)⟩)
    (Subsingleton.elim _ _)⟩

/-- The two faces as objects of the fiber latching category at `y`. -/
def face (k : Fin 2) : LatchingCategory y :=
  ⟨Over.mk (m k), fun h ↦ by
    have := congrArg (fun p : ResolutionStrictFiber (1 : Fin 2) ↦ p.obj.left.unop.obj.unop.len) h
    change 1 = 2 at this
    omega⟩

/-- The fiber restriction of the vertex diagram, valued in `Type`. -/
abbrev FY : ResolutionStrictFiber (1 : Fin 2) ⥤ Type :=
  (resolutionFiberProperty (1 : Fin 2)).ι ⋙ CostructuredArrow.proj _ _ ⋙
    resolutionVertices (Fin 2)

/-- Fiber objects are determined by their underlying simplices. -/
theorem fiber_obj_ext {d : Fin 2} {p q : ResolutionStrictFiber d}
    (h : p.obj.left = q.obj.left) : p = q := by
  obtain ⟨hp, hp'⟩ := p.property
  obtain ⟨hq, hq'⟩ := q.property
  apply ObjectProperty.FullSubcategory.ext
  refine costructuredArrow_obj_ext h ?_
  rw [hp', hq']
  simp [eqToHom_map]

/-- The separating invariant: the element maps to vertex `0` of `y`, and the
face also contains vertex `1` of `y`. -/
noncomputable def sepCocone : Cocone (latchingDiagram FY y) where
  pt := Bool
  ι :=
    { app := fun k ↦ TypeCat.ofHom fun x ↦
        decide (resolutionOrd k.obj.hom.hom.left x = 0 ∧
          ∃ i, resolutionOrd k.obj.hom.hom.left i = 1)
      naturality := fun k k' φ ↦ by
        ext x
        change Fin (k.obj.left.obj.left.unop.obj.unop.len + 1) at x
        have hcomp : ∀ i, resolutionOrd k'.obj.hom.hom.left (resolutionOrd φ.hom.left.hom.left i) =
            resolutionOrd k.obj.hom.hom.left i := fun i ↦ by
          have := congrArg (fun g : k.obj.left ⟶ y ↦ resolutionOrd g.hom.left i) (Over.w φ.hom)
          simp only [ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left,
            resolutionOrd_comp] at this
          exact this
        change decide (resolutionOrd k'.obj.hom.hom.left (resolutionOrd φ.hom.left.hom.left x) = 0 ∧
            ∃ i, resolutionOrd k'.obj.hom.hom.left i = 1) =
          decide (resolutionOrd k.obj.hom.hom.left x = 0 ∧
            ∃ i, resolutionOrd k.obj.hom.hom.left i = 1)
        rw [hcomp]
        by_cases hx : resolutionOrd k.obj.hom.hom.left x = 0
        · -- Then the map φ is a bijection on vertices.
          have hK : 1 ≤ k.obj.left.obj.left.unop.obj.unop.len := by
            by_contra hlen
            rw [not_le] at hlen
            obtain ⟨ht, -⟩ := k.obj.left.property
            have hl := resolutionLabel_map k.obj.hom.hom.left x
            rw [hx] at hl
            have hxl : x = Fin.last _ := Fin.ext (by have := x.isLt; simp; omega)
            rw [hxl] at hl
            have : (1 : Fin 2) = 0 := ht.symm.trans hl
            exact absurd this (by decide)
          have hK' : k'.obj.left.obj.left.unop.obj.unop.len ≤ 1 := by
            by_contra hlen
            rw [not_le] at hlen
            have hle : k'.obj.left.obj.left.unop.obj.unop.len ≤ 2 :=
              resolution_len_le k'.obj.hom.hom.left
            have heq : k'.obj.left.obj.left.unop.obj.unop.len =
                y.obj.left.unop.obj.unop.len := by
              change _ = 2
              omega
            exact k'.property (fiber_obj_ext (resolution_eq_of_len_eq k'.obj.hom.hom.left heq))
          have hle : k.obj.left.obj.left.unop.obj.unop.len ≤
              k'.obj.left.obj.left.unop.obj.unop.len := resolution_len_le φ.hom.left.hom.left
          have hbij : Function.Bijective (resolutionOrd φ.hom.left.hom.left) := by
            rw [Fintype.bijective_iff_injective_and_card]
            refine ⟨(resolutionOrd φ.hom.left.hom.left).injective, ?_⟩
            change Fintype.card (Fin (k.obj.left.obj.left.unop.obj.unop.len + 1)) =
              Fintype.card (Fin (k'.obj.left.obj.left.unop.obj.unop.len + 1))
            simp only [Fintype.card_fin]
            omega
          have hiff : (∃ i, resolutionOrd k'.obj.hom.hom.left i = 1) ↔
              ∃ i, resolutionOrd k.obj.hom.hom.left i = 1 := by
            constructor
            · rintro ⟨i', hi'⟩
              obtain ⟨i, rfl⟩ := hbij.2 i'
              exact ⟨i, (hcomp i).symm.trans hi'⟩
            · rintro ⟨i, hi⟩
              exact ⟨resolutionOrd φ.hom.left.hom.left i, (hcomp i).trans hi⟩
          simp only [hiff]
        · simp [hx] }

theorem resolutionOrd_m (k : Fin 2) (i : Fin 2) :
    resolutionOrd (m k).hom.left i =
      (if k = 0 then Fin.castSuccOrderEmb else Fin.succAboveOrderEmb 1) i :=
  rfl

theorem sep_face0 : (show Bool from sepCocone.ι.app (face 0) (0 : Fin 2)) = true := by
  change decide (resolutionOrd (m 0).hom.left 0 = 0 ∧
    ∃ i, resolutionOrd (m 0).hom.left i = 1) = true
  simp only [resolutionOrd_m]
  decide

theorem sep_face1 : (show Bool from sepCocone.ι.app (face 1) (0 : Fin 2)) = false := by
  change decide (resolutionOrd (m 1).hom.left 0 = 0 ∧
    ∃ i, resolutionOrd (m 1).hom.left i = 1) = false
  simp only [resolutionOrd_m]
  decide

/-- **Lemma 9.5.3 is false.** The restriction of the Reedy cofibrant vertex
diagram to the fiber pₜ⁻¹(1) of Δ′{0 → 1} is not Reedy cofibrant. -/
theorem not_isReedyCofibrant :
    ¬ IsReedyCofibrant (resolutionFiberDiagram (1 : Fin 2) (resolutionVerticesInj (Fin 2))) := by
  intro h
  have hinj := (h y).2
  rw [InjSet.cofibration_iff, mono_iff_injective] at hinj
  change Function.Injective (latchingMap FY y) at hinj
  have e (k : Fin 2) := ConcreteCategory.congr_hom (ι_latchingMap FY y (face k)) (0 : Fin 2)
  have hab : colimit.ι (latchingDiagram FY y) (face 0) (0 : Fin 2) =
      colimit.ι (latchingDiagram FY y) (face 1) (0 : Fin 2) :=
    hinj ((e 0).trans ((e 1).trans rfl).symm)
  have hsep := congrArg (colimit.desc (latchingDiagram FY y) sepCocone) hab
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc,
    colimit.ι_desc] at hsep
  have hft : true = false := sep_face0.symm.trans (hsep.trans sep_face1)
  exact absurd hft (by decide)

/-- The vertex diagram is restricted, as every map of `InjSet` is a weak equivalence. -/
theorem isResolutionRestricted : IsResolutionRestricted (resolutionVerticesInj (Fin 2)) :=
  fun _ _ _ ↦ InjSet.weakEquivalence _ _ _

end FiberReedyCounterexample


end ABCCofibrations

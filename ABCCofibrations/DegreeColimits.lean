/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyOpen
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# Colimits of degree truncations

Categorical reconstruction of a diagram colimit from the sequential colimit
of its bounded-degree restrictions. Only the individual colimits concerned
are assumed.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe w v u

open CategoryTheory Limits

namespace ABCCofibrations

variable {D : Type w} [SmallCategory D] (deg : D → ℕ)

/-- The full subcategory of objects of degree strictly less than `n`. -/
def degreeBelow (n : ℕ) : ObjectProperty D := fun e ↦ deg e < n

/-- Inclusion of one degree truncation into a later one. -/
abbrev degreeInclusion {n m : ℕ} (h : n ≤ m) :
    (degreeBelow deg n).FullSubcategory ⥤ (degreeBelow deg m).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ he ↦ lt_of_lt_of_le he h)

variable {M : Type u} [Category.{v} M] (X : D ⥤ M)
  [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ X)]

/-- The colimit map between two degree truncations. -/
noncomputable def degreeColimitMap {n m : ℕ} (h : n ≤ m) :
    colimit ((degreeBelow deg n).ι ⋙ X) ⟶ colimit ((degreeBelow deg m).ι ⋙ X) := by
  have : HasColimit (degreeInclusion deg h ⋙ (degreeBelow deg m).ι ⋙ X) :=
    (inferInstance : HasColimit ((degreeBelow deg n).ι ⋙ X))
  exact colimit.pre ((degreeBelow deg m).ι ⋙ X) (degreeInclusion deg h)

@[reassoc (attr := simp)]
lemma ι_degreeColimitMap {n m : ℕ} (h : n ≤ m) (e : (degreeBelow deg n).FullSubcategory) :
    colimit.ι ((degreeBelow deg n).ι ⋙ X) e ≫ degreeColimitMap deg X h =
      colimit.ι ((degreeBelow deg m).ι ⋙ X) ((degreeInclusion deg h).obj e) := by
  have : HasColimit (degreeInclusion deg h ⋙ (degreeBelow deg m).ι ⋙ X) :=
    (inferInstance : HasColimit ((degreeBelow deg n).ι ⋙ X))
  exact colimit.ι_pre ((degreeBelow deg m).ι ⋙ X) (degreeInclusion deg h) e

/-- The sequence of colimits of bounded-degree restrictions. -/
noncomputable def degreeColimits : ℕ ⥤ M where
  obj n := colimit ((degreeBelow deg n).ι ⋙ X)
  map f := degreeColimitMap deg X (leOfHom f)
  map_id n := by
    apply colimit.hom_ext
    intro e
    rw [ι_degreeColimitMap, Category.comp_id]
    rfl
  map_comp f g := by
    apply colimit.hom_ext
    intro e
    erw [ι_degreeColimitMap, ι_degreeColimitMap_assoc, ι_degreeColimitMap]
    rfl

variable [HasColimit (degreeColimits deg X)]

/-- The map from an object into the sequential colimit of the truncation colimits. -/
noncomputable def degreeColimitLeg (e : D) : X.obj e ⟶ colimit (degreeColimits deg X) :=
  colimit.ι ((degreeBelow deg (deg e + 1)).ι ⋙ X) ⟨e, Nat.lt_succ_self _⟩ ≫
    colimit.ι (degreeColimits deg X) (deg e + 1)

/-- A leg can be computed in any truncation which contains the object. -/
lemma degreeColimitLeg_eq (n : ℕ) (e : (degreeBelow deg n).FullSubcategory) :
    degreeColimitLeg deg X e.obj = colimit.ι ((degreeBelow deg n).ι ⋙ X) e ≫
      colimit.ι (degreeColimits deg X) n := by
  let h : deg e.obj + 1 ≤ n := e.property
  have hw := colimit.w (degreeColimits deg X) (homOfLE h)
  have hι := ι_degreeColimitMap_assoc deg X h
    (⟨e.obj, Nat.lt_succ_self _⟩ : (degreeBelow deg (deg e.obj + 1)).FullSubcategory)
    (colimit.ι (degreeColimits deg X) n)
  change colimit.ι _ _ ≫ (degreeColimits deg X).map (homOfLE h) ≫ _ = _ at hι
  erw [hw] at hι
  exact hι

variable (hdeg : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b)

/-- The cocone on the whole diagram obtained from its truncation colimits. -/
noncomputable def degreeColimitCocone : Cocone X where
  pt := colimit (degreeColimits deg X)
  ι :=
    { app := degreeColimitLeg deg X
      naturality := fun a b f ↦ by
        let a' : (degreeBelow deg (deg b + 1)).FullSubcategory :=
          ⟨a, lt_of_le_of_lt (hdeg f) (Nat.lt_succ_self _)⟩
        let b' : (degreeBelow deg (deg b + 1)).FullSubcategory := ⟨b, Nat.lt_succ_self _⟩
        change X.map f ≫ degreeColimitLeg deg X b = degreeColimitLeg deg X a ≫ 𝟙 _
        rw [degreeColimitLeg_eq deg X _ a', degreeColimitLeg_eq deg X _ b',
          Category.comp_id, ← Category.assoc]
        exact congrArg (· ≫ colimit.ι (degreeColimits deg X) (deg b + 1))
          (colimit.w ((degreeBelow deg (deg b + 1)).ι ⋙ X) (⟨f⟩ : a' ⟶ b')) }

/-- A cocone on the whole diagram restricts to a cocone on the truncation colimits. -/
noncomputable def degreeCoconeOfCocone (c : Cocone X) : Cocone (degreeColimits deg X) where
  pt := c.pt
  ι :=
    { app := fun n ↦ colimit.desc ((degreeBelow deg n).ι ⋙ X) (c.whisker (degreeBelow deg n).ι)
      naturality := fun n m f ↦ by
        change degreeColimitMap deg X (leOfHom f) ≫
          colimit.desc ((degreeBelow deg m).ι ⋙ X) (c.whisker (degreeBelow deg m).ι) =
            colimit.desc ((degreeBelow deg n).ι ⋙ X) (c.whisker (degreeBelow deg n).ι) ≫ 𝟙 _
        rw [Category.comp_id]
        apply colimit.hom_ext
        intro e
        erw [ι_degreeColimitMap_assoc, colimit.ι_desc, colimit.ι_desc]
        rfl }

/-- Sequential reconstruction of a colimit from its bounded-degree colimits. -/
noncomputable def isColimitDegreeColimitCocone : IsColimit (degreeColimitCocone deg X hdeg) where
  desc c := colimit.desc _ (degreeCoconeOfCocone deg X c)
  fac c e := by
    change degreeColimitLeg deg X e ≫ _ = c.ι.app e
    unfold degreeColimitLeg
    rw [Category.assoc, colimit.ι_desc]
    exact colimit.ι_desc _ _
  uniq c m hm := by
    apply colimit.hom_ext (F := degreeColimits deg X)
    intro n
    apply colimit.hom_ext (F := (degreeBelow deg n).ι ⋙ X)
    intro e
    change colimit.ι ((degreeBelow deg n).ι ⋙ X) e ≫
      colimit.ι (degreeColimits deg X) n ≫ m = _
    erw [← Category.assoc, ← degreeColimitLeg_eq, hm]
    erw [colimit.ι_desc]
    exact (colimit.ι_desc (c.whisker (degreeBelow deg n).ι) e).symm

include hdeg in
/-- Existence of the sequential colimit of bounded-degree colimits implies
existence of the colimit of the whole diagram. -/
theorem hasColimit_of_degreeColimits : HasColimit X :=
  ⟨⟨⟨degreeColimitCocone deg X hdeg, isColimitDegreeColimitCocone deg X hdeg⟩⟩⟩

/-- The canonical comparison between the sequential colimit and the whole colimit. -/
noncomputable def degreeColimitIso [HasColimit X] :
    colimit (degreeColimits deg X) ≅ colimit X :=
  (isColimitDegreeColimitCocone deg X hdeg).coconePointUniqueUpToIso (colimit.isColimit X)

@[reassoc]
lemma ι_degreeColimitIso_hom [HasColimit X] (n : ℕ) (e : (degreeBelow deg n).FullSubcategory) :
    colimit.ι ((degreeBelow deg n).ι ⋙ X) e ≫ colimit.ι (degreeColimits deg X) n ≫
      (degreeColimitIso deg X hdeg).hom = colimit.ι X e.obj := by
  rw [← Category.assoc, ← degreeColimitLeg_eq]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitDegreeColimitCocone deg X hdeg) (colimit.isColimit X) e.obj

section Maps

variable {X} {Y : D ⥤ M} [∀ n, HasColimit ((degreeBelow deg n).ι ⋙ Y)]

/-- Maps of diagrams induce maps of their truncation-colimit sequences. -/
noncomputable def degreeColimitsMap (f : X ⟶ Y) : degreeColimits deg X ⟶ degreeColimits deg Y where
  app n := colimMap (Functor.whiskerLeft (degreeBelow deg n).ι f)
  naturality n m h := by
    change degreeColimitMap deg X (leOfHom h) ≫ colimMap _ =
      colimMap _ ≫ degreeColimitMap deg Y (leOfHom h)
    apply colimit.hom_ext
    intro e
    erw [ι_degreeColimitMap_assoc, ι_colimMap, ι_colimMap_assoc, ι_degreeColimitMap]
    rfl

variable [HasColimit (degreeColimits deg Y)] [HasColimit X] [HasColimit Y]

/-- Naturality of sequential reconstruction. -/
lemma degreeColimitIso_naturality (f : X ⟶ Y) :
    colimMap (degreeColimitsMap deg f) ≫ (degreeColimitIso deg Y hdeg).hom =
      (degreeColimitIso deg X hdeg).hom ≫ colimMap f := by
  apply colimit.hom_ext
  intro n
  apply colimit.hom_ext (F := (degreeBelow deg n).ι ⋙ X)
  intro e
  rw [ι_colimMap_assoc]
  change colimit.ι ((degreeBelow deg n).ι ⋙ X) e ≫
    colimMap (Functor.whiskerLeft (degreeBelow deg n).ι f) ≫
      colimit.ι (degreeColimits deg Y) n ≫ (degreeColimitIso deg Y hdeg).hom = _
  erw [ι_colimMap_assoc, ι_degreeColimitIso_hom]
  change f.app e.obj ≫ colimit.ι Y e.obj =
    colimit.ι ((degreeBelow deg n).ι ⋙ X) e ≫ colimit.ι (degreeColimits deg X) n ≫
      (degreeColimitIso deg X hdeg).hom ≫ colimMap f
  rw [ι_degreeColimitIso_hom_assoc, ι_colimMap]

end Maps

end ABCCofibrations

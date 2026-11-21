/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Interchanging individually existing pointwise colimits

Unlike the chosen `colim` functor interface, the constructions here assume
only the particular colimits involved, not all colimits of either shape.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w z v u
open CategoryTheory Limits
namespace ABCCofibrations.PointwiseColimitInterchange
variable {J : Type w} [SmallCategory J] {K : Type z} [SmallCategory K]
  {M : Type u} [Category.{v} M] (F : J ⥤ K ⥤ M) [∀ j, HasColimit (F.obj j)]

/-- The functor of the individually existing inner colimits. -/
noncomputable def colimitObjects : J ⥤ M where
  obj j := colimit (F.obj j)
  map f := colimMap (F.map f)
  map_id j := by
    apply colimit.hom_ext
    intro k
    simp
  map_comp f g := by
    apply colimit.hom_ext
    intro k
    simp [Category.assoc]

variable (c : Cocone F) (hc : ∀ k, IsColimit (((evaluation K M).obj k).mapCocone c))
  [HasColimit (colimitObjects F)]

/-- At a fixed inner object, the maps to the colimit of inner colimits form a cocone. -/
noncomputable def objectCocone (k : K) : Cocone (F.flip.obj k) where
  pt := colimit (colimitObjects F)
  ι :=
    { app := fun j ↦ colimit.ι (F.obj j) k ≫ colimit.ι (colimitObjects F) j
      naturality := fun j j' f ↦ by
        change (F.map f).app k ≫ (colimit.ι (F.obj j') k ≫ _) = _ ≫ 𝟙 _
        rw [Category.comp_id, ← ι_colimMap_assoc]
        exact congrArg (colimit.ι (F.obj j) k ≫ ·) (colimit.w (colimitObjects F) f) }

/-- The leg from a pointwise colimit into the colimit of inner colimits. -/
noncomputable def leg (k : K) : c.pt.obj k ⟶ colimit (colimitObjects F) :=
  (hc k).desc (objectCocone F k)

@[reassoc (attr := simp)]
lemma leg_fac (j : J) (k : K) :
    (c.ι.app j).app k ≫ leg F c hc k =
      colimit.ι (F.obj j) k ≫ colimit.ι (colimitObjects F) j :=
  (hc k).fac _ j

/-- The interchange cocone on the pointwise colimit diagram. -/
noncomputable def cocone : Cocone c.pt where
  pt := colimit (colimitObjects F)
  ι :=
    { app := leg F c hc
      naturality := fun k k' g ↦ by
        dsimp only [Functor.const_obj_map]
        apply (hc k).hom_ext
        intro j
        erw [Category.comp_id]
        change (c.ι.app j).app k ≫ c.pt.map g ≫ leg F c hc k' =
          (c.ι.app j).app k ≫ leg F c hc k
        erw [← (c.ι.app j).naturality_assoc, leg_fac, leg_fac]
        exact colimit.w_assoc (F.obj j) g _ }

/-- A cocone on the pointwise colimit induces a cocone on the inner colimits. -/
noncomputable def coconeOfCocone (s : Cocone c.pt) : Cocone (colimitObjects F) where
  pt := s.pt
  ι :=
    { app := fun j ↦ colimit.desc (F.obj j) ⟨s.pt, c.ι.app j ≫ s.ι⟩
      naturality := fun j j' f ↦ by
        dsimp only [Functor.const_obj_map]
        apply colimit.hom_ext
        intro k
        erw [Category.comp_id]
        change colimit.ι (F.obj j) k ≫ colimMap (F.map f) ≫ _ = _
        erw [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc]
        change (F.map f).app k ≫ ((c.ι.app j').app k ≫ s.ι.app k) =
          (c.ι.app j).app k ≫ s.ι.app k
        rw [← Category.assoc]
        exact congrArg (fun t ↦ t.app k ≫ s.ι.app k) (c.w f) }

/-- The interchange cocone is a colimit, assuming only the individual inner,
pointwise outer, and final outer colimits. -/
noncomputable def isColimitCocone : IsColimit (cocone F c hc) where
  desc s := colimit.desc (colimitObjects F) (coconeOfCocone F c s)
  fac s k := by
    apply (hc k).hom_ext
    intro j
    change (c.ι.app j).app k ≫ leg F c hc k ≫ _ = _
    rw [leg_fac_assoc, colimit.ι_desc]
    change colimit.ι (F.obj j) k ≫ colimit.desc (F.obj j) ⟨s.pt, c.ι.app j ≫ s.ι⟩ = _
    rw [colimit.ι_desc]
    rfl
  uniq s m hm := by
    apply colimit.hom_ext (F := colimitObjects F)
    intro j
    apply colimit.hom_ext
    intro k
    change colimit.ι (F.obj j) k ≫ colimit.ι (colimitObjects F) j ≫ m = _
    rw [← leg_fac_assoc, show leg F c hc k ≫ m = s.ι.app k from hm k]
    rw [colimit.ι_desc]
    change _ = colimit.ι (F.obj j) k ≫ colimit.desc (F.obj j) ⟨s.pt, c.ι.app j ≫ s.ι⟩
    rw [colimit.ι_desc]
    rfl

include hc in
/-- Colimits of the pointwise colimit diagram exist under these restricted hypotheses. -/
theorem hasColimit : HasColimit c.pt := ⟨⟨⟨_, isColimitCocone F c hc⟩⟩⟩

end ABCCofibrations.PointwiseColimitInterchange

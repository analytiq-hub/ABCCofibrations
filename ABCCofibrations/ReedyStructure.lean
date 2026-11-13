/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyInverse
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The Reedy cofibration structure (Theorem 9.2.4)

Colimits commute with pointwise pushouts of diagrams; this computes the latching
objects of a pushout of diagrams.
-/

@[expose] public section

universe w v₂ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

section ColimitPushout

variable {M : Type u₂} [Category.{v₂} M] {J : Type*} [Category J] {X Y Z T : J ⥤ M}
  {α : X ⟶ Y} {β : X ⟶ Z} {γ : Y ⟶ T} {δ : Z ⟶ T}
  (hT : ∀ j, IsPushout (α.app j) (β.app j) (γ.app j) (δ.app j))
  [HasColimit X] [HasColimit Y] [HasColimit Z] {P : M} {l : colimit Y ⟶ P} {r : colimit Z ⟶ P}
  (hP : IsPushout (colimMap α) (colimMap β) l r)

include hT hP

/-- The cocone on the pointwise pushout with vertex the pushout of colimits. -/
noncomputable def pushoutColimitCocone : Cocone T where
  pt := P
  ι :=
    { app := fun j ↦ (hT j).desc (colimit.ι Y j ≫ l) (colimit.ι Z j ≫ r) (by
        rw [← ι_colimMap_assoc, hP.w, ι_colimMap_assoc])
      naturality := fun j j' u ↦ by
        apply (hT j).hom_ext
        · rw [← γ.naturality_assoc, (hT j').inl_desc, (hT j).inl_desc_assoc, colimit.w_assoc]
          simp
        · rw [← δ.naturality_assoc, (hT j').inr_desc, (hT j).inr_desc_assoc, colimit.w_assoc]
          simp }

/-- The pushout of colimits is a colimit of the pointwise pushout. -/
noncomputable def isColimitPushoutColimitCocone : IsColimit (pushoutColimitCocone hT hP) where
  desc s := hP.desc (colimit.desc Y ⟨s.pt, γ ≫ s.ι⟩) (colimit.desc Z ⟨s.pt, δ ≫ s.ι⟩) (by
      apply colimit.hom_ext
      intro j
      simp only [ι_colimMap_assoc, colimit.ι_desc, NatTrans.comp_app]
      rw [← Category.assoc, (hT j).w, Category.assoc])
  fac s j := by
    apply (hT j).hom_ext
    · simp [pushoutColimitCocone]
    · simp [pushoutColimitCocone]
  uniq s m hm := by
    refine hP.hom_ext ?_ ?_
    · rw [hP.inl_desc]
      apply colimit.hom_ext
      intro j
      rw [colimit.ι_desc, NatTrans.comp_app, ← hm j]
      exact (((hT j).inl_desc_assoc _ _ _ m).trans (Category.assoc _ _ _)).symm
    · rw [hP.inr_desc]
      apply colimit.hom_ext
      intro j
      rw [colimit.ι_desc, NatTrans.comp_app, ← hm j]
      exact (((hT j).inr_desc_assoc _ _ _ m).trans (Category.assoc _ _ _)).symm

/-- Colimits commute with pointwise pushouts. -/
lemma colimit_isPushout_of_pointwise :
    ∃ (_ : HasColimit T), IsPushout (colimMap α) (colimMap β) (colimMap γ) (colimMap δ) := by
  let hc := isColimitPushoutColimitCocone hT hP
  have : HasColimit T := ⟨⟨⟨_, hc⟩⟩⟩
  refine ⟨this, ?_⟩
  let e : P ≅ colimit T := hc.coconePointUniqueUpToIso (colimit.isColimit T)
  have hlr (j : J) : (pushoutColimitCocone hT hP).ι.app j ≫ e.hom = colimit.ι T j :=
    hc.comp_coconePointUniqueUpToIso_hom (colimit.isColimit T) j
  have hl : l ≫ e.hom = colimMap γ := by
    apply colimit.hom_ext
    intro j
    have h₁ : γ.app j ≫ (pushoutColimitCocone hT hP).ι.app j = colimit.ι Y j ≫ l :=
      (hT j).inl_desc _ _ _
    rw [ι_colimMap, ← hlr, ← Category.assoc, ← h₁]
    exact Category.assoc _ _ _
  have hr : r ≫ e.hom = colimMap δ := by
    apply colimit.hom_ext
    intro j
    have h₁ : δ.app j ≫ (pushoutColimitCocone hT hP).ι.app j = colimit.ι Z j ≫ r :=
      (hT j).inr_desc _ _ _
    rw [ι_colimMap, ← hlr, ← Category.assoc, ← h₁]
    exact Category.assoc _ _ _
  exact hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
    (by simp [hl]) (by simp [hr])

end ColimitPushout

section Pointwise

variable {M : Type u₂} [Category.{v₂} M] {D : Type*} [Category D]

/-- Pushouts of diagrams exist when they exist pointwise. -/
lemma hasPushout_of_pointwise {X Y Z : D ⥤ M} (f : X ⟶ Y) (g : X ⟶ Z)
    (h : ∀ e, HasPushout (f.app e) (g.app e)) : HasPushout f g := by
  have (e : D) : HasColimit ((span f g).flip.obj e) := by
    have := h e
    exact hasColimit_of_iso (F := span (f.app e) (g.app e)) (diagramIsoSpan _)
  infer_instance

/-- A pushout square of diagrams with pointwise pushouts is pointwise a pushout
square. -/
lemma isPushout_app {X Y Z T : D ⥤ M} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ T} {k : Z ⟶ T}
    (sq : IsPushout f g h k) (hp : ∀ e, HasPushout (f.app e) (g.app e)) (e : D) :
    IsPushout (f.app e) (g.app e) (h.app e) (k.app e) := by
  have (e : D) : HasColimit ((span f g).flip.obj e) := by
    have := hp e
    exact hasColimit_of_iso (F := span (f.app e) (g.app e)) (diagramIsoSpan _)
  exact sq.map ((evaluation D M).obj e)

end Pointwise

/-- The category of `D`-diagrams in `M`, to carry the Reedy structure. -/
def ReedyDiagram (D : Type*) [Category D] (M : Type*) [Category M] : Type _ := D ⥤ M

namespace ReedyDiagram

variable (D : Type w) [SmallCategory D] (M : Type u₂) [Category.{v₂} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]

instance : Category (ReedyDiagram D M) := inferInstanceAs (Category (D ⥤ M))

instance : HasInitial (ReedyDiagram D M) := inferInstanceAs (HasInitial (D ⥤ M))

instance : CategoryWithWeakEquivalences (ReedyDiagram D M) where
  weakEquivalences := fun _ _ f ↦ ∀ e, WeakEquivalence (NatTrans.app f e)

instance : CategoryWithCofibrations (ReedyDiagram D M) where
  cofibrations := fun X Y f ↦ ∃ (_ : ∀ e, HasColimit (latchingDiagram (D := D) (M := M) X e))
    (_ : ∀ e, HasColimit (latchingDiagram (D := D) (M := M) Y e)), IsReedyCofibration f

variable {D M}

omit [CategoryWithCofibrations M] [HasInitial M] in
lemma weakEquivalence_iff {X Y : ReedyDiagram D M} (f : X ⟶ Y) :
    WeakEquivalence f ↔ ∀ e, WeakEquivalence (NatTrans.app f e) :=
  ⟨fun h ↦ h.mem, fun h ↦ ⟨h⟩⟩

omit [CategoryWithWeakEquivalences M] in
lemma cofibration_iff {X Y : ReedyDiagram D M} (f : X ⟶ Y) :
    Cofibration f ↔ ∃ (_ : ∀ e, HasColimit (latchingDiagram (D := D) (M := M) X e))
      (_ : ∀ e, HasColimit (latchingDiagram (D := D) (M := M) Y e)), IsReedyCofibration f :=
  ⟨fun h ↦ h.mem, fun h ↦ ⟨h⟩⟩

variable [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- The values of the initial diagram are initial. -/
noncomputable def isInitialInitialObj (e : D) :
    IsInitial ((⊥_ (ReedyDiagram D M) : D ⥤ M).obj e) :=
  initialIsInitial.isInitialObj ((evaluation D M).obj e)

/-- The cocone on a latching diagram of the initial diagram with vertex `⊥`. -/
noncomputable def initialLatchingCocone (d : D) :
    Cocone (latchingDiagram (⊥_ (ReedyDiagram D M) : D ⥤ M) d) where
  pt := ⊥_ M
  ι :=
    { app := fun j ↦ (isInitialInitialObj j.obj.left).to _
      naturality := fun _ _ _ ↦ (isInitialInitialObj _).hom_ext _ _ }

/-- Latching diagrams of the initial diagram have initial colimits. -/
noncomputable def isColimitInitialLatching (d : D) :
    IsColimit (initialLatchingCocone (M := M) d) where
  desc s := initial.to s.pt
  fac _ j := (isInitialInitialObj j.obj.left).hom_ext _ _
  uniq _ _ _ := initialIsInitial.hom_ext _ _

instance hasColimit_initialLatching (d : D) :
    HasColimit (latchingDiagram (⊥_ (ReedyDiagram D M) : D ⥤ M) d) :=
  ⟨⟨⟨_, isColimitInitialLatching d⟩⟩⟩

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M]
  [ABCPrecofibrationCategory M] in
lemma isInitial_latchingObj_initial (d : D) :
    Nonempty (IsInitial (latchingObj (⊥_ (ReedyDiagram D M) : D ⥤ M) d)) :=
  ⟨IsInitial.ofIso initialIsInitial
    ((isColimitInitialLatching d).coconePointUniqueUpToIso (colimit.isColimit _))⟩

instance isIso_latchingMap_initial (d : D) :
    IsIso (latchingMap (⊥_ (ReedyDiagram D M) : D ⥤ M) d) := by
  obtain ⟨hL⟩ := isInitial_latchingObj_initial (M := M) d
  exact ⟨(isInitialInitialObj d).to _, hL.hom_ext _ _, (isInitialInitialObj d).hom_ext _ _⟩

/-- The initial diagram is Reedy cofibrant. -/
lemma isReedyCofibrant_initial : IsReedyCofibrant (⊥_ (ReedyDiagram D M) : D ⥤ M) := by
  intro d
  have hL : IsInitial (latchingObj (⊥_ (ReedyDiagram D M) : D ⥤ M) d) :=
    IsInitial.ofIso initialIsInitial
      ((isColimitInitialLatching d).coconePointUniqueUpToIso (colimit.isColimit _))
  have e₁ : latchingObj (⊥_ (ReedyDiagram D M) : D ⥤ M) d ≅ ⊥_ M :=
    hL.uniqueUpToIso initialIsInitial
  have : IsCofibrant (latchingObj (⊥_ (ReedyDiagram D M) : D ⥤ M) d) := by
    have := cofibration_of_isIso e₁.inv
    exact cofibrant_target e₁.inv
  refine ⟨this, ?_⟩
  have : IsIso (latchingMap (⊥_ (ReedyDiagram D M) : D ⥤ M) d) :=
    ⟨(isInitialInitialObj d).to _, hL.hom_ext _ _, (isInitialInitialObj d).hom_ext _ _⟩
  exact cofibration_of_isIso _

omit [CategoryWithWeakEquivalences M] [ABCPrecofibrationCategory M] in
/-- A cofibrant object of the Reedy structure is a Reedy cofibrant diagram. -/
lemma isReedyCofibrant_of_isCofibrant {X : ReedyDiagram D M} (hX : IsCofibrant X) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram (D := D) (M := M) X e)), IsReedyCofibrant X := by
  obtain ⟨_, h, hf⟩ := (cofibration_iff (initial.to X)).1 hX
  exact ⟨h, hf.2.1⟩

/-- A Reedy cofibrant diagram is a cofibrant object of the Reedy structure. -/
lemma isCofibrant_of_isReedyCofibrant {X : ReedyDiagram D M}
    [∀ e, HasColimit (latchingDiagram (D := D) (M := M) X e)] (hX : IsReedyCofibrant X) :
    IsCofibrant X := by
  refine (cofibration_iff (initial.to X)).2 ⟨inferInstance, inferInstance,
    isReedyCofibrant_initial, hX, fun d ↦ ?_⟩
  obtain ⟨hL⟩ := isInitial_latchingObj_initial (M := M) d
  have hsq : IsPushout (latchingMap (⊥_ (ReedyDiagram D M) : D ⥤ M) d)
      (latchingObjMap (initial.to X : (⊥_ (ReedyDiagram D M) : D ⥤ M) ⟶ X) d)
      ((isInitialInitialObj d).to _) (𝟙 _) :=
    IsPushout.of_horiz_isIso ⟨hL.hom_ext _ _⟩
  refine ⟨_, _, _, latchingMap X d, hsq, (isInitialInitialObj d).hom_ext _ _,
    Category.id_comp _, (hX d).2⟩

end ReedyDiagram

section CF3

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]
  {D : Type w} [SmallCategory D] [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsDirect D]

open ABCPrecofibrationCategory

omit [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsDirect D] in
lemma IsReedyCofibrant.isCofibrant_obj {X : D ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    (hX : IsReedyCofibrant X) (e : D) : IsCofibrant (X.obj e) := by
  obtain ⟨_, _⟩ := hX e
  exact cofibrant_target (latchingMap X e)

/-- Pushouts of Reedy cofibrations exist pointwise. -/
lemma hasPushout_app {A B C : D ⥤ M} [∀ e, HasColimit (latchingDiagram A e)]
    [∀ e, HasColimit (latchingDiagram B e)] [∀ e, HasColimit (latchingDiagram C e)]
    {i : A ⟶ B} (f : A ⟶ C) (hi : IsReedyCofibration i) (hC : IsReedyCofibrant C) (e : D) :
    HasPushout (i.app e) (f.app e) := by
  have := hi.1.isCofibrant_obj e
  have := hC.isCofibrant_obj e
  have := (hi.cofibration_app e).2
  exact hasPushout _ _

/-- **Theorem 9.2.4(1)(a)**, the pushout axiom CF3(1). The pushout of a Reedy
cofibration along a map to a Reedy cofibrant diagram is a Reedy cofibration. -/
theorem IsReedyCofibration.isPushout {A B C E : D ⥤ M} [∀ e, HasColimit (latchingDiagram A e)]
    [∀ e, HasColimit (latchingDiagram B e)] [∀ e, HasColimit (latchingDiagram C e)]
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ E} {j : C ⟶ E} (sq : IsPushout i f g j)
    (hi : IsReedyCofibration i) (hC : IsReedyCofibrant C) :
    ∃ (_ : ∀ e, HasColimit (latchingDiagram E e)), IsReedyCofibration j := by
  have hT (e : D) := isPushout_app sq (hasPushout_app f hi hC) e
  have hLP (d : D) : HasPushout (latchingObjMap i d) (latchingObjMap f d) := by
    have := (hi.1 d).1
    have := (hC d).1
    have := (hi.cofibration_app d).1
    exact hasPushout _ _
  have hL (d : D) := colimit_isPushout_of_pointwise (α := latchingNat i d) (β := latchingNat f d)
    (γ := latchingNat g d) (δ := latchingNat j d) (fun k ↦ hT k.obj.left)
    (IsPushout.of_hasPushout (latchingObjMap i d) (latchingObjMap f d))
  have hE (d : D) : HasColimit (latchingDiagram E d) := (hL d).fst
  refine ⟨hE, ?_⟩
  have key (d : D) : (IsCofibrant (latchingObj E d) ∧ Cofibration (latchingMap E d)) ∧
      ∃ (P : M) (l : C.obj d ⟶ P) (r : latchingObj E d ⟶ P) (c : P ⟶ E.obj d),
        IsPushout (latchingMap C d) (latchingObjMap j d) l r ∧ l ≫ c = j.app d ∧
          r ≫ c = latchingMap E d ∧ Cofibration c := by
    have hA : IsPushout (latchingObjMap i d) (latchingObjMap f d) (latchingObjMap g d)
        (latchingObjMap j d) := (hL d).snd
    obtain ⟨hLA, hiA⟩ := hi.1 d
    obtain ⟨hLB, hiB⟩ := hi.2.1 d
    obtain ⟨hLC, hiC⟩ := hC d
    have := hi.1.isCofibrant_obj d
    have := hC.isCofibrant_obj d
    obtain ⟨hLi, hid⟩ := hi.cofibration_app d
    have hLj : Cofibration (latchingObjMap j d) := cofibration_of_isPushout hA
    have : HasPushout (latchingObjMap j d) (latchingMap C d) := hasPushout _ _
    have h₁₂ : latchingObjMap i d ≫ latchingMap B d = latchingMap A d ≫ i.app d :=
      latchingObjMap_latchingMap i d
    have : HasPushout (latchingObjMap i d) (latchingMap A d) := hasPushout _ _
    obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hi.2.2 d
    have : Cofibration (pushout.desc (latchingMap B d) (i.app d) h₁₂) := by
      have : Cofibration (pushout.inl (latchingObjMap i d) (latchingMap A d)) :=
        cofibration_of_isPushout (IsPushout.of_hasPushout _ _).flip
      have : IsCofibrant (pushout (latchingObjMap i d) (latchingMap A d)) :=
        cofibrant_target (pushout.inl (latchingObjMap i d) (latchingMap A d))
      have : Cofibration hP.flip.isoPushout.inv := cofibration_of_isIso _
      rw [show pushout.desc (latchingMap B d) (i.app d) h₁₂ = hP.flip.isoPushout.inv ≫ c by
        apply pushout.hom_ext <;> simp [hl, hr]]
      infer_instance
    obtain ⟨-, h₄, hcomp⟩ := gluing_cofibration hA (hT d) h₁₂ (latchingObjMap_latchingMap f d)
      (latchingObjMap_latchingMap g d) (latchingObjMap_latchingMap j d)
    have : IsCofibrant (latchingObj E d) := cofibrant_target (latchingObjMap j d)
    exact ⟨⟨this, h₄⟩, _, _, _, _, (IsPushout.of_hasPushout _ _).flip, pushout.inr_desc _ _ _,
      pushout.inl_desc _ _ _, hcomp⟩
  exact ⟨hC, fun d ↦ (key d).1, fun d ↦ (key d).2⟩

end CF3

end ABCCofibrations

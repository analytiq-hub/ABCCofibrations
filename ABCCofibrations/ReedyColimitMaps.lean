/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyTransfer
public import ABCCofibrations.Gluing
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Basic.Finite.Sigma

/-!
# Colimits of Reedy cofibrations over finite direct categories

Theorem 9.3.5(1)(b),(c) for finite direct categories (finitely many objects and
morphisms): the colimit of a Reedy cofibration is a cofibration, and the colimit
of a pointwise weak equivalence of Reedy cofibrant diagrams is a weak
equivalence.

The induction is on a bound `N` for the degrees, and then on the number of
objects. An object of degree `N` has no non-identity maps out of it; removing it
gives a smaller category, and its latching category has degrees `< N`. The
colimit is a pushout (Lemma 9.3.1), and the gluing lemma (1.4.1(1)) applies.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

section Bookkeeping

variable {D : Type u₁} [Category.{v₁} D]

instance [Finite D] (d : D) : Finite (Complement d) :=
  Finite.of_injective (fun e : Complement d ↦ e.obj)
    (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)

instance [∀ x y : D, Finite (x ⟶ y)] (d : D) (x y : Complement d) : Finite (x ⟶ y) :=
  Finite.of_injective (fun g : x ⟶ y ↦ g.hom) (fun _ _ h ↦ InducedCategory.hom_ext h)

instance [Finite D] [∀ x y : D, Finite (x ⟶ y)] (d : D) : Finite (LatchingCategory d) :=
  Finite.of_injective (fun j : LatchingCategory d ↦ (⟨j.obj.left, j.obj.hom⟩ : Σ e : D, e ⟶ d))
    (by
      rintro ⟨⟨l, ⟨⟨⟩⟩, g⟩, p⟩ ⟨⟨l', ⟨⟨⟩⟩, g'⟩, p'⟩ h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      rfl)

instance [∀ x y : D, Finite (x ⟶ y)] (d : D) (j j' : LatchingCategory d) : Finite (j ⟶ j') :=
  Finite.of_injective (fun g : j ⟶ j' ↦ g.hom.left)
    (fun _ _ h ↦ InducedCategory.hom_ext (Over.OverMorphism.ext h))

lemma natCard_complement [Finite D] (d : D) :
    Nat.card (Complement d) = Nat.card D - 1 := by
  classical
  have := Fintype.ofFinite D
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_complement]

variable (deg : D → ℕ) (hdeg : ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h)

include hdeg in
/-- Degrees on `D ∖ {d}`. -/
lemma hdeg_complement (d : D) {x y : Complement d} (f : x ⟶ y) :
    deg x.obj < deg y.obj ∨ ∃ h : x = y, f = eqToHom h := by
  rcases hdeg f.hom with h | ⟨h, hf⟩
  · exact Or.inl h
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    dsimp at h
    subst h
    exact Or.inr ⟨rfl, InducedCategory.hom_ext (by simpa using hf)⟩

include hdeg in
/-- Degrees on a latching category. -/
lemma hdeg_latching (d : D) {j j' : LatchingCategory d} (g : j ⟶ j') :
    deg j.obj.left < deg j'.obj.left ∨ ∃ h : j = j', g = eqToHom h := by
  rcases hdeg g.hom.left with h | ⟨h, hg⟩
  · exact Or.inl h
  · right
    obtain ⟨⟨l, ⟨⟨⟩⟩, a⟩, p⟩ := j
    obtain ⟨⟨l', ⟨⟨⟩⟩, a'⟩, p'⟩ := j'
    revert hg
    obtain rfl : l = l' := h
    intro hg
    have hw := Over.w g.hom
    dsimp at hg hw
    rw [hg, Category.id_comp] at hw
    change a' = a at hw
    subst hw
    refine ⟨rfl, ?_⟩
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    simpa using hg

include hdeg in
lemma deg_latching_lt (d : D) (j : LatchingCategory d) : deg j.obj.left < deg d := by
  rcases hdeg j.obj.hom with h | ⟨h, -⟩
  · exact h
  · exact absurd h j.property

end Bookkeeping

section Step

variable {D : Type u₁} [Category.{v₁} D] {M : Type u₂} [Category.{v₂} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] {d : D}
  (hd : ∀ (e : D) (g : d ⟶ e), ∃ h : d = e, g = eqToHom h)
  {X Y : D ⥤ M} [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
  (f : X ⟶ Y) [HasColimit ((complementProp d).ι ⋙ X)] [HasColimit ((complementProp d).ι ⋙ Y)]

open ABCPrecofibrationCategory

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
lemma latchingToComplementColimit_naturality :
    latchingToComplementColimit X d ≫ colimMap (Functor.whiskerLeft (complementProp d).ι f) =
      latchingObjMap f d ≫ latchingToComplementColimit Y d := by
  apply colimit.hom_ext
  intro j
  have h₁ := ι_latchingToComplementColimit_assoc X d j
    (colimMap (Functor.whiskerLeft (complementProp d).ι f))
  have h₂ := ι_colimMap (Functor.whiskerLeft (complementProp d).ι f)
    ((latchingToComplement d).obj j)
  have h₃ := ι_latchingObjMap_assoc f d j (latchingToComplementColimit Y d)
  have h₄ := ι_latchingToComplementColimit Y d j
  exact h₁.trans (h₂.trans (h₃.trans (congrArg ((latchingNat f d).app j ≫ ·) h₄)).symm)

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] [∀ e, HasColimit (latchingDiagram X e)]
  [∀ e, HasColimit (latchingDiagram Y e)] in
lemma colimit_pre_naturality [HasColimit X] [HasColimit Y] :
    colimit.pre X (complementProp d).ι ≫ colimMap f =
      colimMap (Functor.whiskerLeft (complementProp d).ι f) ≫
        colimit.pre Y (complementProp d).ι := by
  apply colimit.hom_ext
  intro j
  simp

include hd in
/-- One step of Theorem 9.3.5(1)(b): the gluing lemma at an object `d` with no
non-identity maps out of it. -/
lemma step_cofibration (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y)
    (hc : ∃ (P : M) (l : X.obj d ⟶ P) (r : latchingObj Y d ⟶ P) (c : P ⟶ Y.obj d),
      IsPushout (latchingMap X d) (latchingObjMap f d) l r ∧ l ≫ c = f.app d ∧
        r ≫ c = latchingMap Y d ∧ Cofibration c)
    (hX' : IsCofibrant (colimit ((complementProp d).ι ⋙ X)))
    (hY' : IsCofibrant (colimit ((complementProp d).ι ⋙ Y)))
    (hL : Cofibration (latchingObjMap f d))
    (h' : Cofibration (colimMap (Functor.whiskerLeft (complementProp d).ι f))) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f) := by
  obtain ⟨hLX, hiX⟩ := hX d
  obtain ⟨hLY, hiY⟩ := hY d
  obtain ⟨hcX, hsqX, -, hpX⟩ := colimit_isPushout_latching X d hd hLX hX' hiX
  obtain ⟨hcY, hsqY, -, hpY⟩ := colimit_isPushout_latching Y d hd hLY hY' hiY
  refine ⟨hcX, hcY, ?_⟩
  obtain ⟨P, l, r, c, hP, hl, hr, hcc⟩ := hc
  have : HasPushout (latchingMap X d) (latchingObjMap f d) := hasPushout _ _
  have : HasPushout (colimit.pre X (complementProp d).ι)
      (colimMap (Functor.whiskerLeft (complementProp d).ι f)) := hasPushout _ _
  have h₁₂ : latchingMap X d ≫ f.app d = latchingObjMap f d ≫ latchingMap Y d :=
    (latchingObjMap_latchingMap f d).symm
  have : Cofibration (pushout.desc (f.app d) (latchingMap Y d) h₁₂) := by
    have : IsCofibrant (X.obj d) := cofibrant_target (latchingMap X d)
    have : Cofibration (pushout.inr (latchingMap X d) (latchingObjMap f d)) :=
      cofibration_of_isPushout (IsPushout.of_hasPushout _ _)
    have : IsCofibrant (pushout (latchingMap X d) (latchingObjMap f d)) :=
      cofibrant_target (pushout.inr (latchingMap X d) (latchingObjMap f d))
    have : Cofibration hP.isoPushout.inv := cofibration_of_isIso _
    rw [show pushout.desc (f.app d) (latchingMap Y d) h₁₂ = hP.isoPushout.inv ≫ c by
      apply pushout.hom_ext <;> simp [hl, hr]]
    infer_instance
  exact (gluing_cofibration hsqX hsqY h₁₂ (latchingToComplementColimit_naturality f)
    (by simp) (colimit_pre_naturality f)).2.1

include hd in
/-- One step of Theorem 9.3.5(1)(c). -/
lemma step_weakEquivalence (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y)
    (hX' : IsCofibrant (colimit ((complementProp d).ι ⋙ X)))
    (hY' : IsCofibrant (colimit ((complementProp d).ι ⋙ Y)))
    (hw : WeakEquivalence (f.app d)) (hL : WeakEquivalence (latchingObjMap f d))
    (h' : WeakEquivalence (colimMap (Functor.whiskerLeft (complementProp d).ι f))) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f) := by
  obtain ⟨hLX, hiX⟩ := hX d
  obtain ⟨hLY, hiY⟩ := hY d
  obtain ⟨hcX, hsqX, -, hpX⟩ := colimit_isPushout_latching X d hd hLX hX' hiX
  obtain ⟨hcY, hsqY, -, hpY⟩ := colimit_isPushout_latching Y d hd hLY hY' hiY
  refine ⟨hcX, hcY, ?_⟩
  exact gluing_weakEquivalence hsqX hsqY (latchingObjMap_latchingMap f d).symm
    (latchingToComplementColimit_naturality f) (by simp) (colimit_pre_naturality f)

end Step

section Main

universe w

variable {M : Type u₂} [Category.{v₂} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- The colimit of a Reedy cofibrant diagram over a finite direct category exists
and is cofibrant (Theorem 9.3.5(1)(a), with a degree function given). -/
lemma colimit_cofibrant_of_deg {D : Type w} [SmallCategory D] [Finite D] (deg : D → ℕ)
    (hdeg : ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h)
    (X : D ⥤ M) [∀ e, HasColimit (latchingDiagram X e)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit X), IsCofibrant (colimit X) := by
  have := Fintype.ofFinite D
  have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
  exact reedyCofibrant_colimit_finite _ D rfl X hX

omit [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCPrecofibrationCategory M] in
/-- Over an empty category, every map of colimits is an isomorphism. -/
lemma isIso_colimMap_of_isEmpty {D : Type w} [SmallCategory D] [IsEmpty D] {X Y : D ⥤ M}
    [HasColimit X] [HasColimit Y] (f : X ⟶ Y) : IsIso (colimMap f) := by
  have hX : IsInitial (colimit X) :=
    (isColimitEquivIsInitialOfIsEmpty (c := colimit.cocone X)) (colimit.isColimit X)
  have hY : IsInitial (colimit Y) :=
    (isColimitEquivIsInitialOfIsEmpty (c := colimit.cocone Y)) (colimit.isColimit Y)
  exact ⟨hY.to _, hX.hom_ext _ _, hY.hom_ext _ _⟩

/-- The induction behind Theorem 9.3.5(1)(b),(c), over finite direct small
categories with degrees bounded by `N` and `n` objects. -/
theorem reedy_colimMap_aux (N : ℕ) : ∀ (n : ℕ) (D : Type w) [SmallCategory D] [Finite D]
    [∀ x y : D, Finite (x ⟶ y)] (deg : D → ℕ)
    (_ : ∀ {x y : D} (f : x ⟶ y), deg x < deg y ∨ ∃ h : x = y, f = eqToHom h),
    (∀ e, deg e < N) → Nat.card D = n →
    ∀ (X Y : D ⥤ M) [∀ e, HasColimit (latchingDiagram X e)]
      [∀ e, HasColimit (latchingDiagram Y e)] (f : X ⟶ Y),
      (IsReedyCofibration f → ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f)) ∧
      (IsReedyCofibrant X → IsReedyCofibrant Y → (∀ e, WeakEquivalence (f.app e)) →
        ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f)) := by
  induction N with
  | zero =>
    intro n D _ _ _ deg hdeg hN _ X Y _ _ f
    have : IsEmpty D := ⟨fun e ↦ Nat.not_lt_zero _ (hN e)⟩
    have hR (Z : D ⥤ M) [∀ e, HasColimit (latchingDiagram Z e)] : IsReedyCofibrant Z :=
      fun e ↦ isEmptyElim e
    obtain ⟨hcX, hX⟩ := colimit_cofibrant_of_deg deg hdeg X (hR X)
    obtain ⟨hcY, -⟩ := colimit_cofibrant_of_deg deg hdeg Y (hR Y)
    have := isIso_colimMap_of_isEmpty f
    exact ⟨fun _ ↦ ⟨hcX, hcY, cofibration_of_isIso _⟩,
      fun _ _ _ ↦ ⟨hcX, hcY, weakEquivalence_of_isIso _⟩⟩
  | succ N ihN =>
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    intro D _ _ _ deg hdeg hN hn X Y _ _ f
    by_cases hex : ∃ e, deg e = N
    swap
    · simp only [not_exists] at hex
      exact ihN n D deg hdeg (fun e ↦ lt_of_le_of_ne (Nat.lt_succ_iff.1 (hN e)) (hex e)) hn
        X Y f
    obtain ⟨e₀, he₀⟩ := hex
    have hd : ∀ (e : D) (g : e₀ ⟶ e), ∃ h : e₀ = e, g = eqToHom h := fun e g ↦ by
      rcases hdeg g with h | h
      · have := hN e
        omega
      · exact h
    have hcard : Nat.card (Complement e₀) < n := by
      have : 0 < Nat.card D := Nat.card_pos_iff.2 ⟨⟨e₀⟩, inferInstance⟩
      rw [natCard_complement]
      omega
    have ihD := ihn _ hcard (Complement e₀) (fun e ↦ deg e.obj) (hdeg_complement deg hdeg e₀)
      (fun e ↦ hN e.obj) rfl
    have ihL := ihN _ (LatchingCategory e₀) (fun j ↦ deg j.obj.left)
      (hdeg_latching deg hdeg e₀) (fun j ↦ he₀ ▸ deg_latching_lt deg hdeg e₀ j) rfl
    refine ⟨fun hf ↦ ?_, fun hX hY hw ↦ ?_⟩
    · obtain ⟨hX₁, hY₁, hf'⟩ := isReedyCofibration_restrict hd hf
      obtain ⟨hcX', hcY', hc'⟩ := (ihD _ _ _).1 hf'
      obtain ⟨_, hX'⟩ := colimit_cofibrant_of_deg _ (hdeg_complement deg hdeg e₀) _ hf'.1
      obtain ⟨_, hY'⟩ := colimit_cofibrant_of_deg _ (hdeg_complement deg hdeg e₀) _ hf'.2.1
      obtain ⟨hXL, hYL, hfL⟩ := isReedyCofibration_latching deg hdeg hf (d := e₀)
      obtain ⟨_, _, hL⟩ := (ihL _ _ _).1 hfL
      exact step_cofibration hd f hf.1 hf.2.1 (hf.2.2 e₀) hX' hY' hL hc'
    · obtain ⟨hX₁, hX'⟩ := isReedyCofibrant_restrict hd X hX
      obtain ⟨hY₁, hY'⟩ := isReedyCofibrant_restrict hd Y hY
      obtain ⟨hcX', hcY', hc'⟩ := (ihD _ _ (Functor.whiskerLeft (complementProp e₀).ι f)).2
        hX' hY' (fun e ↦ hw e.obj)
      obtain ⟨_, hXc⟩ := colimit_cofibrant_of_deg _ (hdeg_complement deg hdeg e₀) _ hX'
      obtain ⟨_, hYc⟩ := colimit_cofibrant_of_deg _ (hdeg_complement deg hdeg e₀) _ hY'
      obtain ⟨hXL, hXL'⟩ := isReedyCofibrant_latching deg hdeg X (d := e₀) hX
      obtain ⟨hYL, hYL'⟩ := isReedyCofibrant_latching deg hdeg Y (d := e₀) hY
      obtain ⟨_, _, hL⟩ := (ihL _ _ (latchingNat f e₀)).2 hXL' hYL' (fun j ↦ hw j.obj.left)
      exact step_weakEquivalence hd f hX hY hXc hYc (hw e₀) hL hc'

variable {D : Type w} [SmallCategory D] [Finite D] [∀ x y : D, Finite (x ⟶ y)] [IsDirect D]

/-- **Theorem 9.3.5(1)(b)**, for finite direct categories. The colimit of a Reedy
cofibration is a cofibration. -/
theorem reedyCofibration_colimMap {X Y : D ⥤ M} [∀ e, HasColimit (latchingDiagram X e)]
    [∀ e, HasColimit (latchingDiagram Y e)] {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), Cofibration (colimMap f) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  have := Fintype.ofFinite D
  obtain ⟨N, hN⟩ : ∃ N, ∀ e, deg e < N :=
    ⟨Finset.univ.sup deg + 1, fun e ↦ Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e))⟩
  exact (reedy_colimMap_aux N _ D deg hdeg hN rfl X Y f).1 hf

/-- **Theorem 9.3.5(1)(c)**, for finite direct categories. The colimit of a
pointwise weak equivalence of Reedy cofibrant diagrams is a weak equivalence. -/
theorem reedyCofibrant_colimMap_weakEquivalence {X Y : D ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ e, WeakEquivalence (f.app e)) :
    ∃ (_ : HasColimit X) (_ : HasColimit Y), WeakEquivalence (colimMap f) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  have := Fintype.ofFinite D
  obtain ⟨N, hN⟩ : ∃ N, ∀ e, deg e < N :=
    ⟨Finset.univ.sup deg + 1, fun e ↦ Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ e))⟩
  exact (reedy_colimMap_aux N _ D deg hdeg hN rfl X Y f).2 hX hY hw

/-- **Corollary 9.3.6(1)**, for finite direct categories. A Reedy cofibration
`f : X ⟶ Y` induces cofibrations `LX_d ⟶ LY_d` and `X_d ⟶ Y_d`; in particular
Reedy cofibrations are pointwise cofibrations. -/
theorem IsReedyCofibration.cofibration_app {X Y : D ⥤ M}
    [∀ e, HasColimit (latchingDiagram X e)] [∀ e, HasColimit (latchingDiagram Y e)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) (d : D) :
    Cofibration (latchingObjMap f d) ∧ Cofibration (f.app d) := by
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  obtain ⟨hXL, hYL, hfL⟩ := isReedyCofibration_latching deg hdeg hf (d := d)
  have : IsDirect (LatchingCategory d) := ⟨⟨_, hdeg_latching deg hdeg d⟩⟩
  obtain ⟨_, _, hL⟩ := reedyCofibration_colimMap hfL
  have hL' : Cofibration (latchingObjMap f d) := hL
  refine ⟨hL', ?_⟩
  obtain ⟨hLX, hiX⟩ := hf.1 d
  obtain ⟨hLY, -⟩ := hf.2.1 d
  obtain ⟨P, l, r, c, hP, hl, hr, hc⟩ := hf.2.2 d
  have : IsCofibrant (X.obj d) := cofibrant_target (latchingMap X d)
  have : Cofibration l := cofibration_of_isPushout hP.flip
  rw [← hl]
  infer_instance

end Main

end ABCCofibrations

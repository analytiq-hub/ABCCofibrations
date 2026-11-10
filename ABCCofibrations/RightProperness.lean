/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.Properness
public import ABCCofibrations.FibrationBasic

/-!
# Right properness (§1.8, fibration statements)

A map `f : A ⟶ B` is *right proper* (Definition 1.8.3(2)) if pullbacks along
`f` exist and pulling a weak equivalence `r : C₂ ⟶ C₁` over `B` back along `f`
gives a weak equivalence: in the diagram of pullback squares

```
D₂ --r'-> D₁ --h--> A
|j₂       |j₁       |f
C₂ --r--> C₁ --g--> B
```

`r'` is a weak equivalence whenever `r` is. A prefibration category is *right
proper* (axiom PF, Definition 1.8.1(2)) if pullbacks of fibrations with fibrant
target exist along arbitrary maps and preserve weak equivalences.

Both notions are defined as their left counterparts in the opposite category,
and the native pullback formulations are proved as lemmas. The statements (2)
of Theorem 1.8.4 and Proposition 1.8.5 then follow from the statements (1) in
`Cᵒᵖ`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

section RightProperMap

variable {C : Type u} [Category.{v} C] [CategoryWithWeakEquivalences C]

/-- A map is *right proper* (Definition 1.8.3(2)) if it is left proper in the
opposite category. See `IsRightProper.mk`, `IsRightProper.hasPullback` and
`IsRightProper.weakEquivalence` for the formulation with pullbacks. -/
def IsRightProper {A B : C} (f : A ⟶ B) : Prop := IsLeftProper f.op

theorem isRightProper_iff_isLeftProper_op {A B : C} (f : A ⟶ B) :
    IsRightProper f ↔ IsLeftProper f.op := Iff.rfl

theorem isLeftProper_iff_isRightProper_unop {A B : Cᵒᵖ} (f : A ⟶ B) :
    IsLeftProper f ↔ IsRightProper f.unop := Iff.rfl

namespace IsRightProper

/-- Pullbacks along a right proper map exist. -/
theorem hasPullback {A B : C} {f : A ⟶ B} (hf : IsRightProper f) ⦃D : C⦄ (g : D ⟶ B) :
    HasPullback f g := by
  have := IsLeftProper.hasPushout hf g.op
  exact (IsPushout.of_hasPushout g.op f.op).unop.hasPullback

/-- Pulling a weak equivalence back along a right proper map gives a weak
equivalence. -/
theorem weakEquivalence {A B : C} {f : A ⟶ B} (hf : IsRightProper f)
    ⦃C₁ C₂ D₁ D₂ : C⦄ {g : C₁ ⟶ B} {r : C₂ ⟶ C₁} {h : D₁ ⟶ A} {j₁ : D₁ ⟶ C₁}
    {r' : D₂ ⟶ D₁} {j₂ : D₂ ⟶ C₂} (sq₁ : IsPullback h j₁ f g) (sq₂ : IsPullback r' j₂ j₁ r)
    [WeakEquivalence r] : WeakEquivalence r' := by
  have := (weakEquivalences_op_iff r).2 ‹_›
  exact (weakEquivalences_op_iff r').1 (IsLeftProper.weakEquivalence hf sq₁.op sq₂.op)

/-- The formulation of Definition 1.8.3(2) with pullbacks. -/
theorem mk {A B : C} {f : A ⟶ B} (hasPullback : ∀ ⦃D : C⦄ (g : D ⟶ B), HasPullback f g)
    (weakEquivalence : ∀ ⦃C₁ C₂ D₁ D₂ : C⦄ {g : C₁ ⟶ B} {r : C₂ ⟶ C₁} {h : D₁ ⟶ A}
      {j₁ : D₁ ⟶ C₁} {r' : D₂ ⟶ D₁} {j₂ : D₂ ⟶ C₂}, IsPullback h j₁ f g →
        IsPullback r' j₂ j₁ r → WeakEquivalence r → WeakEquivalence r') :
    IsRightProper f where
  hasPushout D g := by
    have := hasPullback g.unop
    exact (IsPullback.of_hasPullback f g.unop).op.hasPushout
  weakEquivalence {C₁ C₂ D₁ D₂ g r j₁ h j₂ r'} sq₁ sq₂ hr :=
    (weakEquivalences_unop_iff r').1
      (weakEquivalence sq₁.unop sq₂.unop ((weakEquivalences_unop_iff r).2 hr))

/-- Right proper maps are stable under pullback. -/
theorem of_isPullback {A A' B B' : C} {f : A ⟶ B} (hf : IsRightProper f) {u : B' ⟶ B}
    {j : A' ⟶ B'} {h : A' ⟶ A} (sq : IsPullback h j f u) : IsRightProper j :=
  IsLeftProper.of_isPushout hf sq.op

/-- Right proper maps are stable under composition. -/
theorem comp {A B B' : C} {f : A ⟶ B} {f₂ : B ⟶ B'} (hf : IsRightProper f)
    (hf₂ : IsRightProper f₂) : IsRightProper (f ≫ f₂) := by
  rw [isRightProper_iff_isLeftProper_op, op_comp]
  exact IsLeftProper.comp hf₂ hf

/-- **Proposition 1.8.7(2).** If the weak equivalences are stable under
retracts, a retract of a right proper map is right proper, provided its
pullbacks exist. -/
theorem of_retract [(weakEquivalences C).IsStableUnderRetracts] {A B A' B' : C}
    {f : A ⟶ B} {f' : A' ⟶ B'} (h : RetractArrow f' f) (hf : IsRightProper f)
    (hex : ∀ ⦃D : C⦄ (u : D ⟶ B'), HasPullback f' u) : IsRightProper f' := by
  have : (weakEquivalences Cᵒᵖ).IsStableUnderRetracts :=
    inferInstanceAs (weakEquivalences C).op.IsStableUnderRetracts
  refine IsLeftProper.of_retract h.op hf fun D u ↦ ?_
  have := hex u.unop
  exact (IsPullback.of_hasPullback f' u.unop).op.hasPushout

/-- **Proposition 1.8.7(2), trivial right proper maps.** If the weak
equivalences are stable under retracts, a retract of a right proper weak
equivalence is a right proper weak equivalence, provided its pullbacks exist. -/
theorem of_retract_of_weakEquivalence [(weakEquivalences C).IsStableUnderRetracts]
    {A B A' B' : C} {f : A ⟶ B} {f' : A' ⟶ B'} (h : RetractArrow f' f)
    (hf : IsRightProper f) [WeakEquivalence f]
    (hex : ∀ ⦃D : C⦄ (u : D ⟶ B'), HasPullback f' u) :
    IsRightProper f' ∧ WeakEquivalence f' :=
  ⟨hf.of_retract h hex, ⟨(weakEquivalences C).of_retract h (inferInstance : WeakEquivalence f).mem⟩⟩

end IsRightProper

end RightProperMap

namespace ABCPrefibrationCategory

variable (C : Type u) [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- Axiom PF (Definition 1.8.1(2)): axiom PCF in the opposite category. See
`RightProper.mk`, `RightProper.hasPullback` and
`RightProper.weakEquivalence_of_isPullback` for the formulation with pullbacks.
Compared with F3, the other corner need not be fibrant. -/
abbrev RightProper : Prop := ABCPrecofibrationCategory.LeftProper Cᵒᵖ

variable {C}

/-- PF: pullbacks of fibrations with fibrant target exist along arbitrary maps. -/
theorem RightProper.hasPullback [RightProper C] {A B D : C} (p : B ⟶ A) (r : D ⟶ A)
    [IsFibrant A] [Fibration p] : HasPullback p r := by
  have : Cofibration p.op := (cofibration_op_iff p).2 ‹_›
  have := ABCPrecofibrationCategory.LeftProper.hasPushout p.op r.op
  exact (IsPushout.of_hasPushout p.op r.op).unop.flip.hasPullback

/-- PF: the pullback of a weak equivalence along a fibration with fibrant
target is a weak equivalence. -/
theorem RightProper.weakEquivalence_of_isPullback [RightProper C] {A B D E : C}
    {p : B ⟶ A} {r : D ⟶ A} {r' : E ⟶ B} {j : E ⟶ D} (h : IsPullback r' j p r)
    [IsFibrant A] [Fibration p] [WeakEquivalence r] : WeakEquivalence r' := by
  have : Cofibration p.op := (cofibration_op_iff p).2 ‹_›
  have := (weakEquivalences_op_iff r).2 ‹_›
  exact (weakEquivalences_op_iff r').1
    (ABCPrecofibrationCategory.LeftProper.weakEquivalence_of_isPushout h.op.flip)

/-- The formulation of axiom PF with pullbacks. -/
theorem RightProper.mk
    (hasPullback : ∀ {A B D : C} (p : B ⟶ A) (r : D ⟶ A) [IsFibrant A] [Fibration p],
      HasPullback p r)
    (weakEquivalence_of_isPullback : ∀ {A B D E : C} {p : B ⟶ A} {r : D ⟶ A} {r' : E ⟶ B}
      {j : E ⟶ D}, IsPullback r' j p r → ∀ [IsFibrant A] [Fibration p] [WeakEquivalence r],
        WeakEquivalence r') :
    RightProper C where
  hasPushout {A B D} i r _ _ := by
    have : IsFibrant A.unop := (isFibrant_iff_isCofibrant_op A.unop).2 ‹_›
    have : Fibration i.unop := (fibration_unop_iff i).2 ‹_›
    have := hasPullback i.unop r.unop
    exact (IsPullback.of_hasPullback i.unop r.unop).op.flip.hasPushout
  weakEquivalence_of_isPushout {A B D E i r r' j} h _ _ _ := by
    have : IsFibrant A.unop := (isFibrant_iff_isCofibrant_op A.unop).2 ‹_›
    have : Fibration i.unop := (fibration_unop_iff i).2 ‹_›
    have : WeakEquivalence r.unop := (weakEquivalences_unop_iff r).2 ‹_›
    exact (weakEquivalences_unop_iff r').1 (weakEquivalence_of_isPullback h.flip.unop)

/-- A prefibration category in which every object is fibrant is right proper. -/
theorem rightProper_of_forall_isFibrant [∀ X : C, IsFibrant X] : RightProper C := by
  have : ∀ X : Cᵒᵖ, IsCofibrant X := fun X ↦ (isFibrant_iff_isCofibrant_op X.unop).1 inferInstance
  exact ABCPrecofibrationCategory.leftProper_of_forall_isCofibrant

/-- **Theorem 1.8.4(2)(a).** In a right proper prefibration category, a
fibration with fibrant target is a right proper map. -/
theorem isRightProper_of_fibration [RightProper C] {A B : C} [IsFibrant B]
    (p : A ⟶ B) [Fibration p] : IsRightProper p := by
  have : Cofibration p.op := (cofibration_op_iff p).2 ‹_›
  exact ABCPrecofibrationCategory.isLeftProper_of_cofibration p.op

/-- Isomorphisms are right proper maps. -/
theorem isRightProper_of_isIso {A B : C} (f : A ⟶ B) [IsIso f] : IsRightProper f :=
  ABCPrecofibrationCategory.isLeftProper_of_isIso f.op

/-- **Theorem 1.8.4(2)(b).** In a right proper prefibration category, every map
factors as a weak equivalence followed by a right proper map. -/
theorem exists_rightProper_factorization [RightProper C] {A B : C} (f : A ⟶ B) :
    ∃ (Y : C) (w : A ⟶ Y) (p : Y ⟶ B), WeakEquivalence w ∧ IsRightProper p ∧ w ≫ p = f := by
  obtain ⟨Y, f', r, hf', hr, hfac⟩ :=
    ABCPrecofibrationCategory.exists_leftProper_factorization f.op
  exact ⟨Y.unop, r.unop, f'.unop, (weakEquivalences_unop_iff r).2 hr, hf',
    congrArg Quiver.Hom.unop hfac⟩

/-- **Theorem 1.8.4(2)(c).** In a right proper prefibration category, trivial
right proper maps are stable under pullback. (The paper says "pushout", a
typo.) -/
theorem _root_.ABCCofibrations.IsRightProper.weakEquivalence_of_isPullback [RightProper C]
    {A B D E : C} {p : A ⟶ B} (hp : IsRightProper p) [WeakEquivalence p]
    {f : D ⟶ B} {j : E ⟶ D} {g : E ⟶ A}
    (h : IsPullback g j p f) : IsRightProper j ∧ WeakEquivalence j := by
  have := (weakEquivalences_op_iff p).2 ‹_›
  obtain ⟨hj, hj'⟩ := IsLeftProper.weakEquivalence_of_isPushout hp h.op
  exact ⟨hj, (weakEquivalences_op_iff j).1 hj'⟩

/-- **Proposition 1.8.5(2).** In a right proper prefibration category, a weak
equivalence is right proper exactly when its pullbacks along all maps exist and
are weak equivalences. -/
theorem isRightProper_iff_of_weakEquivalence [RightProper C] {A B : C} (p : A ⟶ B)
    [WeakEquivalence p] :
    IsRightProper p ↔ (∀ ⦃D : C⦄ (g : D ⟶ B), HasPullback p g) ∧
      ∀ ⦃D E : C⦄ {g : D ⟶ B} {j : E ⟶ D} {k : E ⟶ A}, IsPullback k j p g →
        WeakEquivalence j := by
  constructor
  · intro hp
    exact ⟨hp.hasPullback, fun _ _ _ _ _ h ↦ (hp.weakEquivalence_of_isPullback h).2⟩
  · rintro ⟨hex, hwe⟩
    have := (weakEquivalences_op_iff p).2 ‹_›
    refine (ABCPrecofibrationCategory.isLeftProper_iff_of_weakEquivalence p.op).2
      ⟨fun D g ↦ ?_, fun D E g j k h ↦ (weakEquivalences_unop_iff j).1 (hwe h.unop)⟩
    have := hex g.unop
    exact (IsPullback.of_hasPullback p g.unop).op.hasPushout

/-- **Proposition 1.8.6(2).** In a right proper prefibration category, if
`q ≫ p` is right proper and `q` is a right proper weak equivalence, then `p` is
right proper, provided the pullbacks along `p` exist. (The paper's statement
repeats "left proper" from part (1); this is the dual statement.) -/
theorem _root_.ABCCofibrations.IsRightProper.of_comp [RightProper C] {A₁ A₂ A₃ : C}
    {p : A₂ ⟶ A₁} {q : A₃ ⟶ A₂} (hqp : IsRightProper (q ≫ p)) (hq : IsRightProper q)
    [WeakEquivalence q] (hex : ∀ ⦃D : C⦄ (u : D ⟶ A₁), HasPullback p u) :
    IsRightProper p := by
  have := (weakEquivalences_op_iff q).2 ‹_›
  refine IsLeftProper.of_comp (f := p.op) (g := q.op) (by rw [← op_comp]; exact hqp) hq
    fun D u ↦ ?_
  have := hex u.unop
  exact (IsPullback.of_hasPullback p u.unop).op.hasPushout

section RightProperFibrations

variable (C) in
/-- A type synonym for `C`, carrying the right proper maps as fibrations
(and the same weak equivalences and terminal object). -/
def RightProperFibrations : Type u := C

instance : Category.{v} (RightProperFibrations C) := inferInstanceAs (Category.{v} C)

instance : CategoryWithFibrations (RightProperFibrations C) where
  fibrations _ _ f := IsRightProper (C := C) f

instance : CategoryWithWeakEquivalences (RightProperFibrations C) where
  weakEquivalences := weakEquivalences C

instance : HasTerminal (RightProperFibrations C) := inferInstanceAs (HasTerminal C)

/-- **Theorem 1.8.4(2)(d).** If `C` is a right proper prefibration category,
then `C` with the same weak equivalences and the right proper maps as
fibrations is again a prefibration category. In the opposite category this is
literally Theorem 1.8.4(1)(d). -/
theorem rightProperFibrations_prefibrationCategory [RightProper C] :
    ABCPrefibrationCategory (RightProperFibrations C) :=
  ABCPrecofibrationCategory.leftProperCofibrations_precofibrationCategory (C := Cᵒᵖ)

end RightProperFibrations

end ABCPrefibrationCategory

end ABCCofibrations

/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyBoundedFactorization
public import ABCCofibrations.ReedyOpenFunctor

/-! # Extending factorizations through successive degree truncations -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

variable {D : Type w} [SmallCategory D] (deg : D → ℕ)
  (hdeg : ∀ {a b : D} (g : a ⟶ b), deg a < deg b ∨ ∃ h : a = b, g = eqToHom h)
  {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

include hdeg in
/-- Extend a chosen factorization to the next truncation, with an isomorphism
and equations comparing both maps on the preceding truncation. -/
theorem reedy_factorization_next_truncation (h5 : CoproductCofibrationAxiom.{w} M)
    {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X)
    (f : X ⟶ Y) (n : ℕ) (Z : (degreeBelow deg n).FullSubcategory ⥤ M)
    [∀ e, HasColimit (latchingDiagram Z e)]
    [∀ e, HasColimit (latchingDiagram ((degreeBelow deg n).ι ⋙ X) e)]
    [∀ e, HasColimit (latchingDiagram ((degreeBelow deg (n + 1)).ι ⋙ X) e)]
    (a : (degreeBelow deg n).ι ⋙ X ⟶ Z) (r : Z ⟶ (degreeBelow deg n).ι ⋙ Y)
    (ha : IsReedyCofibration a) (hr : ∀ e, WeakEquivalence (r.app e))
    (har : a ≫ r = Functor.whiskerLeft (degreeBelow deg n).ι f) :
    ∃ (Z' : (degreeBelow deg (n + 1)).FullSubcategory ⥤ M)
      (_ : ∀ e, HasColimit (latchingDiagram Z' e))
      (a' : (degreeBelow deg (n + 1)).ι ⋙ X ⟶ Z')
      (r' : Z' ⟶ (degreeBelow deg (n + 1)).ι ⋙ Y)
      (e : degreeInclusion deg (Nat.le_succ n) ⋙ Z' ≅ Z),
      IsReedyCofibration a' ∧ (∀ d, WeakEquivalence (r'.app d)) ∧
      a' ≫ r' = Functor.whiskerLeft (degreeBelow deg (n + 1)).ι f ∧
      Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) a' ≫ e.hom = a ∧
      e.inv ≫ Functor.whiskerLeft (degreeInclusion deg (Nat.le_succ n)) r' = r := by
  have : IsDirect D := ⟨⟨deg, hdeg⟩⟩
  have hmono : ∀ {a b : D}, (a ⟶ b) → deg a ≤ deg b := by
    intro a b g
    rcases hdeg g with h | ⟨h, _⟩
    · exact h.le
    · exact (congrArg deg h).le
  let R := degreeBelow deg (n + 1)
  let Q : ObjectProperty R.FullSubcategory := fun e ↦ deg e.obj < n
  let F : Q.FullSubcategory ⥤ (degreeBelow deg n).FullSubcategory :=
    (degreeBelow deg n).lift (Q.ι ⋙ R.ι) (fun e ↦ e.property)
  have : F.Full := ⟨fun g ↦ ⟨⟨⟨g.hom⟩⟩, rfl⟩⟩
  have : F.Faithful := by
    constructor
    intro a b f g h
    apply InducedCategory.hom_ext
    apply InducedCategory.hom_ext
    exact congrArg (fun k : F.obj a ⟶ F.obj b ↦ k.hom) h
  have hinj : Function.Injective F.obj := by
    intro a b h
    apply ObjectProperty.FullSubcategory.ext
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg (fun e : (degreeBelow deg n).FullSubcategory ↦ e.obj) h
  have hopen : ∀ {a : (degreeBelow deg n).FullSubcategory} (e : Q.FullSubcategory),
      (a ⟶ F.obj e) → ∃ e', F.obj e' = a := by
    intro a e g
    exact ⟨⟨⟨a.obj, lt_of_lt_of_le a.property (Nat.le_succ n)⟩, a.property⟩,
      ObjectProperty.FullSubcategory.ext rfl⟩
  obtain ⟨_, _, hOld⟩ := OpenFunctor.isReedyCofibration F hinj hopen ha
  obtain ⟨_, hRX⟩ := OpenDiagramSubcategory.isReedyCofibrant R
    (degreeBelow_isOpen deg hmono (n + 1)) X hX
  have : ∀ e, HasColimit (latchingDiagram (Q.ι ⋙ R.ι ⋙ X) e) :=
    inferInstanceAs (∀ e, HasColimit (latchingDiagram (F ⋙ (degreeBelow deg n).ι ⋙ X) e))
  have hmax : ∀ d, ¬ Q d → ∀ e (g : d ⟶ e), ∃ h : d = e, g = eqToHom h := by
    intro d hd e g
    rcases degreeCondition_fullSubcategory R deg hdeg g with h | h
    · have hd' : ¬ deg d.obj < n := hd
      have he : deg e.obj < n + 1 := e.property
      omega
    · exact h
  have hfac : Functor.whiskerLeft F a ≫ Functor.whiskerLeft F r =
      Functor.whiskerLeft Q.ι (Functor.whiskerLeft R.ι f) := by
    rw [← Functor.whiskerLeft_comp, har]
    rfl
  obtain ⟨Z', hLZ', a', r', eQ, ha', hr', har', hLeft, hRight⟩ :=
    ReedyLayer.factorization_layer Q hmax (fun e ↦ deg e.obj)
      (degreeCondition_fullSubcategory R deg hdeg) h5 hRX (Functor.whiskerLeft R.ι f)
      (F ⋙ Z) (Functor.whiskerLeft F a) (Functor.whiskerLeft F r) hOld
      (fun e ↦ hr (F.obj e)) hfac
  let I : (degreeBelow deg n).FullSubcategory ⥤ Q.FullSubcategory :=
    { obj := fun e ↦ ⟨⟨e.obj, lt_of_lt_of_le e.property (Nat.le_succ n)⟩, e.property⟩
      map := fun g ↦ ⟨⟨g.hom⟩⟩ }
  let e : degreeInclusion deg (Nat.le_succ n) ⋙ Z' ≅ Z := Functor.isoWhiskerLeft I eQ
  refine ⟨Z', hLZ', a', r', e, ha', hr', har', ?_, ?_⟩
  · ext j
    exact congrArg (fun t ↦ t.app (I.obj j)) hLeft
  · ext j
    exact congrArg (fun t ↦ t.app (I.obj j)) hRight

end ABCCofibrations

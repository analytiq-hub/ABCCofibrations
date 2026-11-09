/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrantApproximation
public import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# The prefibration category of fibrant objects

F1–F4 restrict to the full subcategory of fibrant objects. Its inclusion
is a fibrant approximation, using the inherited mathlib morphism classes.
-/

@[expose] public section

universe v u
open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

instance fibrantObject_categoryWithFibrations :
    CategoryWithFibrations (FibrantObject C) where
  fibrations := (fibrations C).inverseImage FibrantObject.ι

instance fibrantObject_hom_fibration {A B : FibrantObject C}
    (i : A ⟶ B) [Fibration i] : Fibration i.hom :=
  ⟨(show Fibration i from inferInstance).mem⟩

/-- The ambient terminal object is also terminal in the full subcategory. -/
noncomputable def fibrantTerminalIsTerminal :
    IsTerminal (FibrantObject.mk (⊤_ C)) :=
  IsTerminal.isTerminalOfObj FibrantObject.ι _ terminalIsTerminal

noncomputable instance (X : FibrantObject C) : Unique (X ⟶ FibrantObject.mk (⊤_ C)) :=
  ⟨⟨(fibrantTerminalIsTerminal (C := C)).from X⟩, fun f ↦
    (fibrantTerminalIsTerminal (C := C)).hom_ext f _⟩

instance fibrantObject_hasTerminal : HasTerminal (FibrantObject C) :=
  hasTerminal_of_unique (FibrantObject.mk (⊤_ C))

/-- The inclusion preserves the terminal object. -/
instance fibrantInclusion_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (FibrantObject C)) FibrantObject.ι := by
  apply preservesLimit_of_preserves_limit_cone (fibrantTerminalIsTerminal (C := C))
  exact (isLimitMapConeEmptyConeEquiv FibrantObject.ι _).symm terminalIsTerminal

instance fibrantObject_isFibrant (A : FibrantObject C) : IsFibrant A := by
  let h := isLimitOfHasTerminalOfPreservesLimit (FibrantObject.ι (C := C))
  let e : (⊤_ (FibrantObject C)).obj ≅ ⊤_ C := h.uniqueUpToIso terminalIsTerminal
  let := fibration_of_isIso e.inv
  have hw : Fibration (terminal.from A.obj ≫ e.inv) := inferInstance
  constructor
  change fibrations C ((terminal.from A).hom)
  have eq : (terminal.from A).hom = terminal.from A.obj ≫ e.inv := h.hom_ext _ _
  rw [eq]
  exact hw.mem

/-- A restricted pullback exists and is preserved by the full inclusion. -/
theorem exists_fibrant_pullback {A B D : FibrantObject C}
    (p : A ⟶ B) (f : D ⟶ B) [Fibration p] :
    ∃ (P : FibrantObject C) (g : P ⟶ A) (j : P ⟶ D),
      IsPullback g j p f ∧ IsPullback g.hom j.hom p.hom f.hom := by
  let sq := IsPullback.of_hasPullback p.hom f.hom
  let := fibration_of_isPullback sq
  let := fibrant_source (pullback.snd p.hom f.hom)
  let P := FibrantObject.mk (pullback p.hom f.hom)
  let g : P ⟶ A := FibrantObject.homMk (pullback.fst p.hom f.hom)
  let j : P ⟶ D := FibrantObject.homMk (pullback.snd p.hom f.hom)
  exact ⟨P, g, j, IsPullback.of_map_of_faithful FibrantObject.ι sq, sq⟩

instance fibrantObject_hasPullback {A B D : FibrantObject C}
    (p : A ⟶ B) (f : D ⟶ B) [Fibration p] : HasPullback p f := by
  obtain ⟨P, g, j, h, _⟩ := exists_fibrant_pullback p f
  exact h.hasPullback

instance fibrantInclusion_preservesPullback {A B D : FibrantObject C}
    (p : A ⟶ B) (f : D ⟶ B) [Fibration p] :
    PreservesLimit (cospan p f) FibrantObject.ι := by
  obtain ⟨P, g, j, h, h'⟩ := exists_fibrant_pullback p f
  exact (h.preservesLimit_cospan_iff (F := FibrantObject.ι)).2 h'

instance fibrantInclusion_op_preservesInitial :
    PreservesColimit (Functor.empty.{0} (FibrantObject C)ᵒᵖ) FibrantObject.ι.op := by
  apply preservesColimit_of_preserves_colimit_cocone
    (initialOpOfTerminal (fibrantTerminalIsTerminal (C := C)))
  exact (isColimitMapCoconeEmptyCoconeEquiv FibrantObject.ι.op _).symm
    (initialOpOfTerminal (terminalIsTerminal (C := C)))

instance fibrantObject_op_isCofibrant (A : (FibrantObject C)ᵒᵖ) : IsCofibrant A := by
  let J := (FibrantObject.ι (C := C)).op
  let (A : (FibrantObject C)ᵒᵖ) : IsCofibrant (J.obj A) := by
    change IsCofibrant (Opposite.op A.unop.obj)
    infer_instance
  let h := isColimitOfHasInitialOfPreservesColimit J
  let e : J.obj (⊥_ (FibrantObject C)ᵒᵖ) ≅ ⊥_ Cᵒᵖ :=
    h.uniqueUpToIso initialIsInitial
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.hom
  let := ABCPrecofibrationCategory.cofibration_of_isIso e.inv
  have hw : Cofibration (e.hom ≫ initial.to (J.obj A)) := inferInstance
  constructor
  change cofibrations Cᵒᵖ (J.map (initial.to A))
  have eq : J.map (initial.to A) = e.hom ≫ initial.to (J.obj A) := h.hom_ext _ _
  rw [eq]
  exact hw.mem

instance fibrantObject_op_hasPushout {A B D : (FibrantObject C)ᵒᵖ}
    (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] : HasPushout i f := by
  let : Fibration i.unop := (fibration_unop_iff i).2 inferInstance
  exact (IsPullback.of_hasPullback i.unop f.unop).op.flip.hasPushout

instance fibrantInclusion_op_preservesPushout {A B D : (FibrantObject C)ᵒᵖ}
    (i : A ⟶ B) (f : A ⟶ D) [Cofibration i] :
    PreservesColimit (span i f) (FibrantObject.ι (C := C)).op := by
  let : Fibration i.unop := (fibration_unop_iff i).2 inferInstance
  let h := IsPullback.of_hasPullback i.unop f.unop
  exact (h.op.flip.preservesColimit_span_iff (F := FibrantObject.ι.op)).2
    (h.map FibrantObject.ι).op.flip

/-- F1–F4 restrict to mathlib's full subcategory of fibrant objects. -/
instance fibrantObject_prefibrationCategory : ABCPrefibrationCategory (FibrantObject C) where
  initial_cofibrant := inferInstance
  cofibrations_comp := by
    let : (fibrations C).IsStableUnderComposition := fibrations_comp
    let : (fibrations (FibrantObject C)).IsStableUnderComposition :=
      inferInstanceAs ((fibrations C).inverseImage FibrantObject.ι).IsStableUnderComposition
    exact inferInstanceAs ((fibrations (FibrantObject C)).op).IsStableUnderComposition
  weakEquivalence_of_isIso f := by
    exact ⟨(ABCPrecofibrationCategory.weakEquivalence_of_isIso f.unop.hom.op).mem⟩
  cofibration_of_isIso f := by
    intro _
    exact ⟨(ABCPrecofibrationCategory.cofibration_of_isIso f.unop.hom.op).mem⟩
  weakEquivalences_twoOutOfThree := by
    let : (weakEquivalences C).HasTwoOutOfThreeProperty := weakEquivalences_twoOutOfThree
    let : (weakEquivalences (FibrantObject C)).HasTwoOutOfThreeProperty := inferInstance
    exact inferInstanceAs ((weakEquivalences (FibrantObject C)).op).HasTwoOutOfThreeProperty
  hasPushout i f := by intro _ _ _; infer_instance
  cofibration_of_isPushout {A B D E} {i f g j} h := by
    intro _ _ hi
    let : Cofibration i.unop.hom.op := ⟨hi.mem⟩
    let := hi
    have h' : IsPushout i.unop.hom.op f.unop.hom.op g.unop.hom.op j.unop.hom.op :=
      h.map FibrantObject.ι.op
    exact ⟨(ABCPrecofibrationCategory.cofibration_of_isPushout h').mem⟩
  weakEquivalence_of_isPushout {A B D E} {i f g j} h := by
    intro _ _ hi hw
    let : Cofibration i.unop.hom.op := ⟨hi.mem⟩
    let : WeakEquivalence i.unop.hom.op := ⟨hw.mem⟩
    let := hi
    have h' : IsPushout i.unop.hom.op f.unop.hom.op g.unop.hom.op j.unop.hom.op :=
      h.map FibrantObject.ι.op
    exact ⟨(ABCPrecofibrationCategory.weakEquivalence_of_isPushout h').mem⟩
  factorization f := by
    intro _
    obtain ⟨Z, w, p, hw, hp, hwp⟩ := factorization f.unop.hom
    let := hp
    let := fibrant_source p
    exact ⟨Opposite.op (FibrantObject.mk Z), (FibrantObject.homMk p).op,
      (FibrantObject.homMk w).op, ⟨hp.mem⟩, ⟨hw.mem⟩, by
        apply Quiver.Hom.unop_inj
        ext
        exact hwp⟩

/-- The inclusion of fibrant objects is a fibrant approximation. -/
instance fibrantInclusion_isFibrantApproximation :
    IsFibrantApproximation (FibrantObject.ι (C := C)) where
  source_cofibrant _ := inferInstance
  preservesInitial := inferInstance
  map_cofibration i := by intro hi; exact ⟨hi.mem⟩
  weakEquivalence_map_iff _ := ⟨fun h ↦ ⟨h.mem⟩, fun h ↦ ⟨h.mem⟩⟩
  map_isPushout h := h.map FibrantObject.ι.op
  factorization {A B} f := by
    let ff : B.unop ⟶ A.unop.obj := f.unop
    obtain ⟨Z, w, p, hw, hp, hwp⟩ := factorization ff
    let := hp
    let := fibrant_source p
    exact ⟨Opposite.op (FibrantObject.mk Z), (FibrantObject.homMk p).op,
      w.op, ⟨hp.mem⟩, (weakEquivalences_op_iff w).2 hw, by
        apply Quiver.Hom.unop_inj
        simpa [Functor.op, ff] using hwp⟩

end ABCCofibrations.ABCPrefibrationCategory

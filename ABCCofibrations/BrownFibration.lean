/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.BrownFunctor
public import ABCCofibrations.FibrantSubcategory

/-!
# Brown's lemma for functors on fibrant objects

Preservation of trivial fibrations implies preservation of all weak
equivalences between fibrant objects. The source requires only F1–F4;
the target weak-equivalence class only needs two-out-of-three. In particular,
a functor which inverts trivial fibrations inverts all weak equivalences
of fibrant objects.

The argument is the opposite of the cofibrant Brown lemma, using that a
prefibration category is a precofibration category on the opposite. This is
the dual of the factorization step in the proof of Theorem 6.2.2(1),
corresponding to Brown factorization 1.3.1(2).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory HomotopicalAlgebra

namespace ABCCofibrations.ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [Limits.HasTerminal C] [ABCPrefibrationCategory C]
  {D : Type u'} [Category.{v'} D]

/-- Brown's functor lemma. No fibrations or model-category structure on the
target are required. -/
theorem map_weakEquivalence_of_map_trivialFibrations
    [CategoryWithWeakEquivalences D] [(weakEquivalences D).HasTwoOutOfThreeProperty]
    (F : C ⥤ D)
    (hF : ∀ {X Y : C} (p : X ⟶ Y) [IsFibrant Y] [Fibration p] [WeakEquivalence p],
      WeakEquivalence (F.map p))
    {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (F.map f) := by
  have h2o3 : (weakEquivalences Dᵒᵖ).HasTwoOutOfThreeProperty := by
    rw [weakEquivalences_op]
    infer_instance
  let := h2o3
  have h :=
    ABCPrecofibrationCategory.map_weakEquivalence_of_map_trivialCofibrations
      (C := Cᵒᵖ) F.op
      (fun {A _} i _ _ _ ↦ by
        have : IsFibrant A.unop := (isFibrant_iff_isCofibrant_op A.unop).2 inferInstance
        have hmap : WeakEquivalence (F.map i.unop) := hF i.unop
        simpa [Functor.op_map] using (weakEquivalences_op_iff (F.map i.unop)).2 hmap)
      f.op
  have h' : WeakEquivalence (F.map f).op := by simpa [Functor.op_map] using h
  exact (weakEquivalences_op_iff (F.map f)).1 h'

/-- Brown's functor lemma on the full subcategory of fibrant objects. -/
theorem map_weakEquivalence_fibrant_of_map_trivialFibrations
    [CategoryWithWeakEquivalences D] [(weakEquivalences D).HasTwoOutOfThreeProperty]
    (F : FibrantObject C ⥤ D)
    (hF : ∀ {X Y : FibrantObject C} (p : X ⟶ Y),
      Fibration p.hom → WeakEquivalence p.hom → WeakEquivalence (F.map p))
    {X Y : FibrantObject C} (f : X ⟶ Y) [WeakEquivalence f.hom] :
    WeakEquivalence (F.map f) := by
  have hw : WeakEquivalence f.hom := inferInstance
  let : WeakEquivalence f := ⟨hw.mem⟩
  exact map_weakEquivalence_of_map_trivialFibrations (C := FibrantObject C) F
    (fun p _ hp hw ↦ by
      let := hp
      let := hw
      exact hF p inferInstance inferInstance)
    f

/-- To invert weak equivalences of fibrant objects, it suffices to invert
trivial fibrations. This form applies to functors into arbitrary categories. -/
theorem isInvertedBy_of_inverts_trivialFibrations
    (F : FibrantObject C ⥤ D)
    (hF : ∀ {X Y : FibrantObject C} (p : X ⟶ Y),
      Fibration p.hom → WeakEquivalence p.hom → IsIso (F.map p)) :
    (weakEquivalences (FibrantObject C)).IsInvertedBy F := by
  let : CategoryWithWeakEquivalences D := ⟨MorphismProperty.isomorphisms D⟩
  let : (weakEquivalences D).HasTwoOutOfThreeProperty :=
    inferInstanceAs (MorphismProperty.isomorphisms D).HasTwoOutOfThreeProperty
  intro X Y f hf
  have hw : WeakEquivalence f.hom := ⟨hf⟩
  let := hw
  have h := map_weakEquivalence_fibrant_of_map_trivialFibrations F
    (fun p hp hw ↦ ⟨hF p hp hw⟩) f
  exact h.mem

end ABCCofibrations.ABCPrefibrationCategory

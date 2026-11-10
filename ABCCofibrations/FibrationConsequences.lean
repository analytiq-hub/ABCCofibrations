/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.FibrationCategory
public import ABCCofibrations.SmallSums
public import ABCCofibrations.SequentialColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Opposites

/-!
# Products and inverse sequences in (pre)fibration categories

The fibration statements (2) of Lemmas 1.2.1, 1.6.2 and 1.6.4, deduced from the
cofibration statements (1) in the opposite category.

Products in `C` are compared with coproducts in `Cᵒᵖ` through mathlib's
`opProductIsoCoproduct`, under which `(Pi.map f).op` is a conjugate of
`Sigma.map (fun i ↦ (f i).op)`. Limits of inverse sequences `F : ℕᵒᵖ ⥤ C` are
compared with colimits of `F.rightOp : ℕ ⥤ Cᵒᵖ` through
`colimitRightOpIsoUnopLimit`, under which `(limMap τ).op` is a conjugate of
`colimMap (NatTrans.rightOp τ)`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace ABCCofibrations

section OpComparisons

variable {C : Type u} [Category.{v} C]

/-- A product exists if the coproduct of the opposite family exists. -/
theorem hasProduct_of_hasCoproduct_op {ι : Type w} (B : ι → C)
    [HasCoproduct fun i ↦ op (B i)] : HasProduct B :=
  ⟨⟨⟨Fan.mk (unop (∐ fun i ↦ op (B i))) fun i ↦ (Sigma.ι (fun i ↦ op (B i)) i).unop,
    Fan.IsLimit.mk _ (fun s ↦ (Sigma.desc fun i ↦ (s.proj i).op).unop)
      (fun s i ↦ by
        change (Sigma.desc fun i ↦ (s.proj i).op).unop ≫ (Sigma.ι (fun i ↦ op (B i)) i).unop = _
        rw [← unop_comp, Sigma.ι_comp_desc]
        rfl)
      (fun s m hm ↦ by
        apply Quiver.Hom.op_inj
        rw [Quiver.Hom.op_unop]
        apply Sigma.hom_ext
        intro i
        rw [Sigma.ι_comp_desc, ← hm i]
        change _ = (m ≫ (Sigma.ι (fun i ↦ op (B i)) i).unop).op
        rw [op_comp, Quiver.Hom.op_unop])⟩⟩⟩

/-- The opposite of a product map is a conjugate of the coproduct of the
opposite maps. -/
theorem op_piMap {ι : Type w} {A B : ι → C} (f : ∀ i, A i ⟶ B i)
    [HasProduct A] [HasProduct B] :
    (Limits.Pi.map f).op = (opProductIsoCoproduct B).hom ≫
      Limits.Sigma.map (fun i ↦ (f i).op) ≫ (opProductIsoCoproduct A).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.inv_comp_eq]
  apply Sigma.hom_ext
  intro i
  have hB : Sigma.ι (fun i ↦ op (B i)) i ≫ (opProductIsoCoproduct B).inv = (Pi.π B i).op := by
    rw [Iso.comp_inv_eq, π_comp_opProductIsoCoproduct_hom]
  rw [reassoc_of% hB, ← Category.assoc, ← op_comp, Pi.map_π, op_comp, Category.assoc,
    π_comp_opProductIsoCoproduct_hom]
  simp

/-- The opposite of a map of limits of inverse sequences is a conjugate of the
map of colimits of the opposite sequences. -/
theorem op_limMap {J : Type*} [Category J] {F G : Jᵒᵖ ⥤ C} (τ : F ⟶ G)
    [HasLimit F] [HasLimit G] :
    (limMap τ).op = (colimitRightOpIsoUnopLimit G).inv ≫ colimMap (NatTrans.rightOp τ) ≫
      (colimitRightOpIsoUnopLimit F).hom := by
  rw [Iso.eq_inv_comp]
  apply colimit.hom_ext
  intro j
  rw [ι_comp_colimitRightOpIsoUnopLimit_hom_assoc, ← op_comp, limMap_π, op_comp,
    ι_colimMap_assoc, ι_comp_colimitRightOpIsoUnopLimit_hom]
  rfl

end OpComparisons

namespace ABCPrefibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCPrefibrationCategory C]

/-- **Lemma 1.2.1(2)**, existence: finite families of fibrant objects have
products. -/
theorem hasProduct_finite {ι : Type w} [Finite ι] (B : ι → C) (hB : ∀ i, IsFibrant (B i)) :
    HasProduct B := by
  have := hasCoproduct_finite (fun i ↦ op (B i)) fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hB i)
  exact hasProduct_of_hasCoproduct_op B

/-- **Lemma 1.2.1(2)**: finite products of fibrant objects are fibrant. -/
theorem product_finite_fibrant {ι : Type w} [Finite ι] (B : ι → C)
    (hB : ∀ i, IsFibrant (B i)) [HasProduct B] : IsFibrant (∏ᶜ B) := by
  have := coproduct_finite_cofibrant (fun i ↦ op (B i))
    fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hB i)
  have := cofibration_of_isIso (opProductIsoCoproduct B).inv
  exact (isFibrant_iff_isCofibrant_op _).2 (cofibrant_target (opProductIsoCoproduct B).inv)

/-- **Lemma 1.2.1(2)**: a finite product of fibrations with fibrant targets is a
fibration. -/
theorem fibration_product_map_finite {ι : Type w} [Finite ι] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (hB : ∀ i, IsFibrant (B i)) (hf : ∀ i, Fibration (f i))
    [HasProduct A] [HasProduct B] : Fibration (Limits.Pi.map f) := by
  have hB' (i) : IsCofibrant (op (B i)) := (isFibrant_iff_isCofibrant_op _).1 (hB i)
  have hf' (i) : Cofibration (f i).op := (cofibration_op_iff _).2 (hf i)
  have := cofibration_coproduct_map_finite (fun i ↦ (f i).op) hB' hf'
  have := (isFibrant_iff_isCofibrant_op _).1 (product_finite_fibrant B hB)
  have := cofibration_of_isIso (opProductIsoCoproduct B).hom
  have := cofibrant_target (opProductIsoCoproduct B).hom
  have := cofibrant_target (Limits.Sigma.map fun i ↦ (f i).op)
  have := cofibration_of_isIso (opProductIsoCoproduct A).inv
  rw [← cofibration_op_iff, op_piMap]
  infer_instance

/-- **Lemma 1.2.1(2)**: a finite product of trivial fibrations with fibrant
targets is a trivial fibration. -/
theorem weakEquivalence_product_map_finite {ι : Type w} [Finite ι] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (hB : ∀ i, IsFibrant (B i)) (hf : ∀ i, Fibration (f i))
    (hw : ∀ i, WeakEquivalence (f i)) [HasProduct A] [HasProduct B] :
    WeakEquivalence (Limits.Pi.map f) := by
  have hB' (i) : IsCofibrant (op (B i)) := (isFibrant_iff_isCofibrant_op _).1 (hB i)
  have hf' (i) : Cofibration (f i).op := (cofibration_op_iff _).2 (hf i)
  have hw' (i) : WeakEquivalence (f i).op := (weakEquivalences_op_iff _).2 (hw i)
  have := weakEquivalence_coproduct_map_finite (fun i ↦ (f i).op) hB' hf' hw'
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct B).hom
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct A).inv
  rw [← weakEquivalences_op_iff, op_piMap]
  infer_instance

/-- **Lemma 1.6.2(2)**, finite case: a finite product of weak equivalences between
fibrant objects is a weak equivalence. -/
theorem weakEquivalence_product_map_finite_of_weakEquivalence {ι : Type w} [Finite ι]
    {A B : ι → C} (f : ∀ i, A i ⟶ B i) [HasProduct A] [HasProduct B]
    (hA : ∀ i, IsFibrant (A i)) (hB : ∀ i, IsFibrant (B i))
    (hw : ∀ i, WeakEquivalence (f i)) : WeakEquivalence (Limits.Pi.map f) := by
  have := weakEquivalence_coproduct_map_finite_of_weakEquivalence (fun i ↦ (f i).op)
    (fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hB i))
    (fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hA i))
    fun i ↦ (weakEquivalences_op_iff _).2 (hw i)
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct B).hom
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct A).inv
  rw [← weakEquivalences_op_iff, op_piMap]
  infer_instance

/-- **Lemma 1.6.3(2)** (equivalent formulation of F5). Assume F1–F4 and that
small families of fibrant objects have products. Then small products of trivial
fibrations with fibrant targets are weak equivalences (F5(2)) if and only if
weak equivalences between fibrant objects are stable under small products.

The forward direction is the common argument of Lemmas 1.6.2(1) and 1.6.3(1),
applied in the opposite category. -/
theorem f5_trivial_iff
    (hex : ∀ {ι : Type w} (X : ι → C), (∀ i, IsFibrant (X i)) → HasProduct X) :
    (∀ {ι : Type w} {X Y : ι → C} (g : ∀ i, X i ⟶ Y i) [HasProduct X] [HasProduct Y],
        (∀ i, IsFibrant (Y i)) → (∀ i, Fibration (g i)) →
          (∀ i, WeakEquivalence (g i)) → WeakEquivalence (Limits.Pi.map g)) ↔
      (∀ {ι : Type w} {X Y : ι → C} (g : ∀ i, X i ⟶ Y i) [HasProduct X] [HasProduct Y],
        (∀ i, IsFibrant (X i)) → (∀ i, IsFibrant (Y i)) →
          (∀ i, WeakEquivalence (g i)) → WeakEquivalence (Limits.Pi.map g)) := by
  constructor
  · intro h ι X Y g _ _ hX hY hw
    have hex' : ∀ Z : ι → Cᵒᵖ, (∀ i, IsCofibrant (Z i)) → HasCoproduct Z := fun Z hZ ↦ by
      have := hex (fun i ↦ unop (Z i)) fun i ↦ (isFibrant_iff_isCofibrant_op _).2 (hZ i)
      exact (inferInstance : HasCoproduct fun i ↦ op (unop (Z i)))
    have htriv : ∀ {Z W : ι → Cᵒᵖ} (g' : ∀ i, Z i ⟶ W i) [HasCoproduct Z] [HasCoproduct W],
        (∀ i, IsCofibrant (Z i)) → (∀ i, Cofibration (g' i)) →
          (∀ i, WeakEquivalence (g' i)) → WeakEquivalence (Limits.Sigma.map g') := by
      intro Z W g' _ _ hZ hg' hw'
      have hZ' (i) : IsFibrant (unop (Z i)) := (isFibrant_iff_isCofibrant_op _).2 (hZ i)
      have hW' (i) : IsFibrant (unop (W i)) := by
        have := hZ i
        have := hg' i
        exact (isFibrant_iff_isCofibrant_op _).2 (cofibrant_target (g' i))
      have := hex (fun i ↦ unop (Z i)) hZ'
      have := hex (fun i ↦ unop (W i)) hW'
      have hp := h (fun i ↦ (g' i).unop) hZ' (fun i ↦ (fibration_unop_iff _).2 (hg' i))
        fun i ↦ (weakEquivalences_unop_iff _).2 (hw' i)
      have := (weakEquivalences_op_iff _).2 hp
      have := ABCPrecofibrationCategory.weakEquivalence_of_isIso
        (opProductIsoCoproduct fun i ↦ unop (Z i)).inv
      have := ABCPrecofibrationCategory.weakEquivalence_of_isIso
        (opProductIsoCoproduct fun i ↦ unop (W i)).hom
      have key : WeakEquivalence ((opProductIsoCoproduct fun i ↦ unop (Z i)).inv ≫
          (Limits.Pi.map fun i ↦ (g' i).unop).op ≫
            (opProductIsoCoproduct fun i ↦ unop (W i)).hom) := inferInstance
      rw [op_piMap] at key
      simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Quiver.Hom.op_unop] at key
      exact key
    have := weakEquivalence_sigmaMap_of_trivialCofibrations hex' htriv (fun i ↦ (g i).op)
      (fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hY i))
      (fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hX i))
      fun i ↦ (weakEquivalences_op_iff _).2 (hw i)
    have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct Y).hom
    have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct X).inv
    rw [← weakEquivalences_op_iff, op_piMap]
    infer_instance
  · intro h ι X Y g _ _ hY hg hw
    refine h g (fun i ↦ ?_) hY hw
    have := hY i
    have := hg i
    exact fibrant_source (g i)

end ABCPrefibrationCategory

namespace ABCFibrationCategory

open ABCPrecofibrationCategory ABCPrefibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C] [HasTerminal C] [ABCFibrationCategory.{w} C]

/-- F5: small families of fibrant objects have products. -/
theorem hasProduct_of_fibrant {ι : Type w} (B : ι → C) (hB : ∀ i, IsFibrant (B i)) :
    HasProduct B := by
  have := ABCCofibrationCategory.hasCoproductOfCofibrant (fun i ↦ op (B i))
    fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hB i)
  exact hasProduct_of_hasCoproduct_op B

/-- F5: small products of fibrant objects are fibrant. -/
theorem product_fibrant {ι : Type w} (B : ι → C) (hB : ∀ i, IsFibrant (B i))
    [HasProduct B] : IsFibrant (∏ᶜ B) := by
  have := ABCCofibrationCategory.coproduct_cofibrant (fun i ↦ op (B i))
    fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hB i)
  have := ABCPrecofibrationCategory.cofibration_of_isIso (opProductIsoCoproduct B).inv
  exact (isFibrant_iff_isCofibrant_op _).2 (cofibrant_target (opProductIsoCoproduct B).inv)

/-- **Lemma 1.6.2(2)**, small case: in a fibration category, a small product of
weak equivalences between fibrant objects is a weak equivalence. -/
theorem weakEquivalence_product_map_of_weakEquivalence {ι : Type w} {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) [HasProduct A] [HasProduct B]
    (hA : ∀ i, IsFibrant (A i)) (hB : ∀ i, IsFibrant (B i))
    (hw : ∀ i, WeakEquivalence (f i)) : WeakEquivalence (Limits.Pi.map f) := by
  have := ABCCofibrationCategory.weakEquivalence_coproduct_map_of_weakEquivalence
    (fun i ↦ (f i).op) (fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hB i))
    (fun i ↦ (isFibrant_iff_isCofibrant_op _).1 (hA i))
    fun i ↦ (weakEquivalences_op_iff _).2 (hw i)
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct B).hom
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (opProductIsoCoproduct A).inv
  rw [← weakEquivalences_op_iff, op_piMap]
  infer_instance

/-- F6: limits of inverse sequences of fibrations ending at a fibrant object
exist. -/
theorem hasLimit_of_sequence (F : ℕᵒᵖ ⥤ C) (h0 : IsFibrant (F.obj (op 0)))
    (hf : ∀ n, Fibration (F.map (succHom n).op)) : HasLimit F := by
  have := ABCCofibrationCategory.hasSequentialColimit F.rightOp
    ((isFibrant_iff_isCofibrant_op _).1 h0) fun n ↦ (cofibration_op_iff _).2 (hf n)
  exact hasLimit_of_hasColimit_rightOp F

/-- F6: the limit of an inverse sequence of fibrations ending at a fibrant object
is fibrant. -/
theorem isFibrant_limit_of_sequence (F : ℕᵒᵖ ⥤ C) (h0 : IsFibrant (F.obj (op 0)))
    (hf : ∀ n, Fibration (F.map (succHom n).op)) [HasLimit F] : IsFibrant (limit F) := by
  have := isCofibrant_colimit_of_sequence ABCCofibrationCategory.sequentialCofibrationAxiom
    F.rightOp ((isFibrant_iff_isCofibrant_op _).1 h0) fun n ↦ (cofibration_op_iff _).2 (hf n)
  have := ABCPrecofibrationCategory.cofibration_of_isIso (colimitRightOpIsoUnopLimit F).hom
  exact (isFibrant_iff_isCofibrant_op _).2 (cofibrant_target (colimitRightOpIsoUnopLimit F).hom)

/-- **Lemma 1.6.4(2).** In a fibration category, for a map `τ : F ⟶ G` of
inverse sequences of fibrations ending at fibrant objects, with every `τ_n` a
weak equivalence, the limit map is a weak equivalence between fibrant objects. -/
theorem weakEquivalence_limMap_of_sequences {F G : ℕᵒᵖ ⥤ C} (τ : F ⟶ G)
    (hF0 : IsFibrant (F.obj (op 0))) (hF : ∀ n, Fibration (F.map (succHom n).op))
    (hG0 : IsFibrant (G.obj (op 0))) (hG : ∀ n, Fibration (G.map (succHom n).op))
    (hw : ∀ n, WeakEquivalence (τ.app (op n))) [HasLimit F] [HasLimit G] :
    WeakEquivalence (limMap τ) := by
  have := ABCCofibrationCategory.weakEquivalence_colimMap_of_sequences (NatTrans.rightOp τ)
    ((isFibrant_iff_isCofibrant_op _).1 hG0) (fun n ↦ (cofibration_op_iff _).2 (hG n))
    ((isFibrant_iff_isCofibrant_op _).1 hF0) (fun n ↦ (cofibration_op_iff _).2 (hF n))
    fun n ↦ (weakEquivalences_op_iff _).2 (hw n)
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitRightOpIsoUnopLimit G).inv
  have := ABCPrecofibrationCategory.weakEquivalence_of_isIso (colimitRightOpIsoUnopLimit F).hom
  rw [← weakEquivalences_op_iff, op_limMap]
  infer_instance

end ABCFibrationCategory

end ABCCofibrations

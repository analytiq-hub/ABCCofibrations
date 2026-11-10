/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.OverUnder
public import ABCCofibrations.SmallSums
public import ABCCofibrations.SequentialColimits
public import ABCCofibrations.EquivalenceTransfer

/-!
# Over and under categories of a cofibration category (Proposition 1.7.1(1))

For an object `A` of a cofibration category, the over category `Over A` is a
cofibration category, and so is the under category `Under A` when `A` is
cofibrant. `OverUnder.lean` proves the CF1–CF4 part; this module adds CF5 and
CF6.

* CF6, and CF5 for `Over A`: the forgetful functor creates the colimits
  involved (sequential colimits are connected, and `Over.forget` creates all
  colimits), and detects cofibrations and weak equivalences. This is packaged
  as a transfer along any such functor.
* CF5 for `Under A`: a coproduct of `A → X_i` in `Under A` is not computed in
  the ambient category. It is the pushout of `∐ X_i ← ∐ A → A` along the fold
  map, which exists by CF5 and CF3 since `A` is cofibrant. A sum of maps
  `X_i → Y_i` in `Under A` is then a cobase change of the ambient sum
  `∐ X_i → ∐ Y_i`, so CF5 for `Under A` follows from CF5 and CF3.
-/

@[expose] public section

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

namespace ABCCofibrationCategory

open ABCPrecofibrationCategory

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

/-- A precofibration category satisfying CF5 and CF6 in the standalone forms is a
cofibration category. -/
theorem of_axioms [ABCPrecofibrationCategory C] (h1 : CoproductCofibrationAxiom.{w} C)
    (h2 : TrivialCoproductAxiom.{w} C) (h3 : SequentialCofibrationAxiom C)
    (h4 : TrivialSequentialAxiom C) : ABCCofibrationCategory.{w} C where
  hasCoproductOfCofibrant := h1.hasCoproduct
  coproduct_cofibrant := h1.coproduct_cofibrant
  coproduct_cofibration := h1.coproduct_cofibration
  coproduct_weakEquivalence f hA hf hw := by
    unfold TrivialCoproductAxiom at h2
    exact h2 f hA hf hw
  hasSequentialColimit := h3.hasColimit
  sequential_cofibration F h0 hf _ := h3.cofibration F h0 hf
  sequential_weakEquivalence F h0 hf hw _ := by
    unfold TrivialSequentialAxiom at h4
    exact h4 F h0 hf hw

end ABCCofibrationCategory

namespace ABCPrecofibrationCategory

section Transfer

variable {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D] [ABCPrecofibrationCategory D]
  {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C] [ABCPrecofibrationCategory C]
  (U : D ⥤ C)
  (hcof : ∀ {X Y : D} (f : X ⟶ Y), Cofibration f ↔ Cofibration (U.map f))
  (hweq : ∀ {X Y : D} (f : X ⟶ Y), WeakEquivalence f ↔ WeakEquivalence (U.map f))

include hcof in
omit [CategoryWithWeakEquivalences D] [ABCPrecofibrationCategory D] in
/-- CF6(1) transfers along a functor which creates sequential colimits, detects
cofibrations, and preserves cofibrancy. -/
theorem sequentialCofibrationAxiom_of_createsColimits [CreatesColimitsOfShape ℕ U]
    (hob : ∀ X : D, IsCofibrant X → IsCofibrant (U.obj X))
    (h1 : SequentialCofibrationAxiom C) : SequentialCofibrationAxiom D where
  hasColimit F h0 hf := by
    have := h1.hasColimit (F ⋙ U) (hob _ h0) fun n ↦ (hcof _).1 (hf n)
    exact hasColimit_of_created F U
  cofibration F h0 hf _ := by
    have := h1.hasColimit (F ⋙ U) (hob _ h0) fun n ↦ (hcof _).1 (hf n)
    have := h1.cofibration (F ⋙ U) (hob _ h0) fun n ↦ (hcof _).1 (hf n)
    have : PreservesColimit F U := preservesColimit_of_createsColimit_and_hasColimit F U
    have : IsCofibrant ((F ⋙ U).obj 0) := hob _ h0
    have := cofibrant_target (colimit.ι (F ⋙ U) 0)
    have := cofibration_of_isIso (preservesColimitIso U F).inv
    rw [hcof, ← ι_preservesColimitIso_inv]
    infer_instance

include hcof hweq in
omit [ABCPrecofibrationCategory D] in
/-- CF6(2) transfers along a functor which creates sequential colimits, detects
cofibrations and weak equivalences, and preserves cofibrancy. -/
theorem trivialSequentialAxiom_of_createsColimits [CreatesColimitsOfShape ℕ U]
    (hob : ∀ X : D, IsCofibrant X → IsCofibrant (U.obj X))
    (h1 : SequentialCofibrationAxiom C) (h2 : TrivialSequentialAxiom C) :
    TrivialSequentialAxiom D := by
  unfold TrivialSequentialAxiom at h2 ⊢
  intro F h0 hf hw _
  have := h1.hasColimit (F ⋙ U) (hob _ h0) fun n ↦ (hcof _).1 (hf n)
  have := h2 (F ⋙ U) (hob _ h0) (fun n ↦ (hcof _).1 (hf n)) fun n ↦ (hweq _).1 (hw n)
  have : PreservesColimit F U := preservesColimit_of_createsColimit_and_hasColimit F U
  have := weakEquivalence_of_isIso (preservesColimitIso U F).inv
  rw [hweq, ← ι_preservesColimitIso_inv]
  infer_instance

variable [∀ ι : Type w, CreatesColimitsOfShape (Discrete ι) U]

omit [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] [HasInitial D]
  [ABCPrecofibrationCategory D] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [HasInitial C] [ABCPrecofibrationCategory C] in
theorem hasCoproduct_of_createsColimits {ι : Type w} (X : ι → D)
    [HasCoproduct fun i ↦ U.obj (X i)] : HasCoproduct X := by
  have : HasColimit (Discrete.functor ((Discrete.functor X ⋙ U).obj ∘ Discrete.mk)) :=
    ‹HasCoproduct fun i ↦ U.obj (X i)›
  have : HasColimit (Discrete.functor X ⋙ U) := hasColimit_of_iso Discrete.natIsoFunctor
  exact hasColimit_of_created _ U

omit [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] [HasInitial D]
  [ABCPrecofibrationCategory D] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [HasInitial C] [ABCPrecofibrationCategory C] in
theorem preservesCoproduct_of_createsColimits {ι : Type w} (X : ι → D)
    [HasCoproduct fun i ↦ U.obj (X i)] : PreservesColimit (Discrete.functor X) U := by
  have : HasColimit (Discrete.functor ((Discrete.functor X ⋙ U).obj ∘ Discrete.mk)) :=
    ‹HasCoproduct fun i ↦ U.obj (X i)›
  have : HasColimit (Discrete.functor X ⋙ U) := hasColimit_of_iso Discrete.natIsoFunctor
  exact preservesColimit_of_createsColimit_and_hasColimit _ U

omit [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D] [HasInitial D]
  [ABCPrecofibrationCategory D] [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [HasInitial C] [ABCPrecofibrationCategory C] [∀ ι : Type w, CreatesColimitsOfShape (Discrete ι) U]
  in
theorem sigmaComparison_map {ι : Type w} {X Y : ι → D} (f : ∀ i, X i ⟶ Y i)
    [HasCoproduct X] [HasCoproduct Y] [HasCoproduct fun i ↦ U.obj (X i)]
    [HasCoproduct fun i ↦ U.obj (Y i)] :
    sigmaComparison U X ≫ U.map (Limits.Sigma.map f) =
      Limits.Sigma.map (fun i ↦ U.map (f i)) ≫ sigmaComparison U Y := by
  ext i
  simp [← Functor.map_comp]

include hcof in
/-- CF5(1) transfers along a functor which creates small coproducts, detects
cofibrations, and detects cofibrancy. -/
theorem coproductCofibrationAxiom_of_createsColimits
    (hob : ∀ X : D, IsCofibrant X ↔ IsCofibrant (U.obj X))
    (h1 : CoproductCofibrationAxiom.{w} C) : CoproductCofibrationAxiom.{w} D where
  hasCoproduct X hX := by
    have := h1.hasCoproduct (fun i ↦ U.obj (X i)) fun i ↦ (hob _).1 (hX i)
    exact hasCoproduct_of_createsColimits U X
  coproduct_cofibrant X hX _ := by
    have := h1.hasCoproduct (fun i ↦ U.obj (X i)) fun i ↦ (hob _).1 (hX i)
    have := h1.coproduct_cofibrant (fun i ↦ U.obj (X i)) fun i ↦ (hob _).1 (hX i)
    have := preservesCoproduct_of_createsColimits U X
    have := cofibration_of_isIso (sigmaComparison U X)
    rw [hob]
    exact cofibrant_target (sigmaComparison U X)
  coproduct_cofibration {ι X Y} f hX hf _ _ := by
    have hY (i) : IsCofibrant (Y i) := by
      have := hX i
      have := hf i
      exact cofibrant_target (f i)
    have := h1.hasCoproduct (fun i ↦ U.obj (X i)) fun i ↦ (hob _).1 (hX i)
    have := h1.hasCoproduct (fun i ↦ U.obj (Y i)) fun i ↦ (hob _).1 (hY i)
    have := h1.coproduct_cofibrant (fun i ↦ U.obj (X i)) fun i ↦ (hob _).1 (hX i)
    have := preservesCoproduct_of_createsColimits U X
    have := preservesCoproduct_of_createsColimits U Y
    have := h1.coproduct_cofibration (fun i ↦ U.map (f i)) (fun i ↦ (hob _).1 (hX i))
      fun i ↦ (hcof _).1 (hf i)
    have := cofibration_of_isIso (sigmaComparison U X)
    have := cofibrant_target (sigmaComparison U X)
    have := cofibration_of_isIso (inv (sigmaComparison U X))
    have := cofibrant_target (Limits.Sigma.map fun i ↦ U.map (f i))
    have := cofibration_of_isIso (sigmaComparison U Y)
    rw [hcof, show U.map (Limits.Sigma.map f) = inv (sigmaComparison U X) ≫
      Limits.Sigma.map (fun i ↦ U.map (f i)) ≫ sigmaComparison U Y by
        rw [← sigmaComparison_map, IsIso.inv_hom_id_assoc]]
    infer_instance

include hcof hweq in
/-- CF5(2) transfers along a functor which creates small coproducts, detects
cofibrations and weak equivalences, and detects cofibrancy. -/
theorem trivialCoproductAxiom_of_createsColimits
    (hob : ∀ X : D, IsCofibrant X ↔ IsCofibrant (U.obj X))
    (h1 : CoproductCofibrationAxiom.{w} C) (h2 : TrivialCoproductAxiom.{w} C) :
    TrivialCoproductAxiom.{w} D := by
  unfold TrivialCoproductAxiom at h2 ⊢
  intro ι X Y f _ _ hX hf hw
  have hY (i) : IsCofibrant (Y i) := by
    have := hX i
    have := hf i
    exact cofibrant_target (f i)
  have := h1.hasCoproduct (fun i ↦ U.obj (X i)) fun i ↦ (hob _).1 (hX i)
  have := h1.hasCoproduct (fun i ↦ U.obj (Y i)) fun i ↦ (hob _).1 (hY i)
  have := preservesCoproduct_of_createsColimits U X
  have := preservesCoproduct_of_createsColimits U Y
  have := h2 (fun i ↦ U.map (f i)) (fun i ↦ (hob _).1 (hX i)) (fun i ↦ (hcof _).1 (hf i))
    fun i ↦ (hweq _).1 (hw i)
  have := weakEquivalence_of_isIso (inv (sigmaComparison U X))
  have := weakEquivalence_of_isIso (sigmaComparison U Y)
  rw [hweq, show U.map (Limits.Sigma.map f) = inv (sigmaComparison U X) ≫
    Limits.Sigma.map (fun i ↦ U.map (f i)) ≫ sigmaComparison U Y by
      rw [← sigmaComparison_map, IsIso.inv_hom_id_assoc]]
  infer_instance

end Transfer

section Equivalence

variable {D : Type u'} [Category.{v'} D] [CategoryWithCofibrations D]
  [CategoryWithWeakEquivalences D] [HasInitial D]
  {D' : Type u} [Category.{v} D'] [CategoryWithCofibrations D']
  [CategoryWithWeakEquivalences D'] [HasInitial D'] [ABCCofibrationCategory.{w} D']

/-- A cofibration structure transported along an equivalence of categories
which identifies the cofibrations and the weak equivalences. -/
theorem _root_.ABCCofibrations.ABCCofibrationCategory.of_equivalence (E : D ≌ D')
    (hcof : cofibrations D = (cofibrations D').inverseImage E.functor)
    (hweq : weakEquivalences D = (weakEquivalences D').inverseImage E.functor) :
    ABCCofibrationCategory.{w} D := by
  have := ABCPrecofibrationCategory.of_equivalence E hcof hweq
  have hc : ∀ {X Y : D} (f : X ⟶ Y), Cofibration f ↔ Cofibration (E.functor.map f) :=
    fun f ↦ cofibration_iff_of_equivalence E hcof f
  have hw : ∀ {X Y : D} (f : X ⟶ Y), WeakEquivalence f ↔ WeakEquivalence (E.functor.map f) :=
    fun f ↦ weakEquivalence_iff_of_equivalence E hweq f
  have ho := isCofibrant_iff_of_equivalence E hcof
  exact ABCCofibrationCategory.of_axioms
    (coproductCofibrationAxiom_of_createsColimits E.functor hc ho
      ABCCofibrationCategory.coproductCofibrationAxiom)
    (trivialCoproductAxiom_of_createsColimits E.functor hc hw ho
      ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.trivialCoproductAxiom)
    (sequentialCofibrationAxiom_of_createsColimits E.functor hc (fun X ↦ (ho X).1)
      ABCCofibrationCategory.sequentialCofibrationAxiom)
    (trivialSequentialAxiom_of_createsColimits E.functor hc hw (fun X ↦ (ho X).1)
      ABCCofibrationCategory.sequentialCofibrationAxiom
      ABCCofibrationCategory.trivialSequentialAxiom)

end Equivalence

section UnderCoproductConstruction

variable {C : Type u} [Category.{v} C]

namespace UnderCoproduct

variable {A : C} {ι : Type w} (X : ι → Under A)

/-- The sum of the structure maps, `∐ A ⟶ ∐ X_i`. -/
noncomputable abbrev hmap [HasCoproduct fun _ : ι ↦ A] [HasCoproduct fun i ↦ (X i).right] :
    ∐ (fun _ : ι ↦ A) ⟶ ∐ (fun i ↦ (X i).right) :=
  Limits.Sigma.map fun i ↦ (X i).hom

/-- The fold map `∐ A ⟶ A`. -/
noncomputable abbrev fold (ι : Type w) (A : C) [HasCoproduct fun _ : ι ↦ A] :
    ∐ (fun _ : ι ↦ A) ⟶ A :=
  Sigma.desc fun _ ↦ 𝟙 A

variable [HasCoproduct fun _ : ι ↦ A] [HasCoproduct fun i ↦ (X i).right]
  [HasPushout (hmap X) (fold ι A)]

/-- The coproduct of `X` in `Under A`: the pushout of `∐ X_i ← ∐ A → A`. -/
noncomputable def cofan : Cofan X :=
  Cofan.mk (Under.mk (pushout.inr (hmap X) (fold ι A))) fun i ↦
    Under.homMk (Sigma.ι (fun i ↦ (X i).right) i ≫ pushout.inl _ _) (by
      have h : (X i).hom ≫ Sigma.ι (fun i ↦ (X i).right) i =
          Sigma.ι (fun _ : ι ↦ A) i ≫ hmap X := by simp
      change (X i).hom ≫ Sigma.ι (fun i ↦ (X i).right) i ≫ pushout.inl _ _ = pushout.inr _ _
      rw [← Category.assoc, h, Category.assoc, pushout.condition, Sigma.ι_comp_desc_assoc,
        Category.id_comp])

@[simp]
theorem cofan_inj_right (i : ι) :
    ((cofan X).inj i).right = Sigma.ι (fun i ↦ (X i).right) i ≫ pushout.inl _ _ := rfl

@[simp]
theorem cofan_pt_hom : (cofan X).pt.hom = pushout.inr (hmap X) (fold ι A) := rfl

/-- The cofan `cofan X` is a coproduct in `Under A`. -/
noncomputable def isColimit : IsColimit (cofan X) :=
  Cofan.IsColimit.mk _
    (fun t ↦ Under.homMk (pushout.desc (Sigma.desc fun i ↦ (t.inj i).right) t.pt.hom (by
      ext i
      simp)) (pushout.inr_desc _ _ _))
    (fun t i ↦ by
      ext
      simp [cofan])
    (fun t m hm ↦ by
      ext
      dsimp [cofan] at m hm ⊢
      apply pushout.hom_ext
      · apply Sigma.hom_ext
        intro i
        simpa using congrArg (fun φ ↦ Under.Hom.right φ) (hm i)
      · simpa using Under.w m)

end UnderCoproduct

end UnderCoproductConstruction

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

variable {C : Type u} [Category.{v} C] [CategoryWithCofibrations C]
  [CategoryWithWeakEquivalences C] [HasInitial C]

section Over

variable [ABCCofibrationCategory.{w} C] (A : C)

/-- **Proposition 1.7.1(1)(a).** The over category `Over A` of a cofibration
category is a cofibration category. -/
instance overCofibrationCategory : ABCCofibrationCategory.{w} (Over A) := by
  have hcof : ∀ {X Y : Over A} (f : X ⟶ Y), Cofibration f ↔ Cofibration ((Over.forget A).map f) :=
    fun f ↦ cofibrations_over_iff _ f
  have hweq : ∀ {X Y : Over A} (f : X ⟶ Y),
      WeakEquivalence f ↔ WeakEquivalence ((Over.forget A).map f) :=
    fun f ↦ weakEquivalences_over_iff _ f
  have hob : ∀ X : Over A, IsCofibrant X ↔ IsCofibrant ((Over.forget A).obj X) :=
    isCofibrant_over_iff
  exact ABCCofibrationCategory.of_axioms
    (coproductCofibrationAxiom_of_createsColimits _ hcof hob
      ABCCofibrationCategory.coproductCofibrationAxiom)
    (trivialCoproductAxiom_of_createsColimits _ hcof hweq hob
      ABCCofibrationCategory.coproductCofibrationAxiom
      ABCCofibrationCategory.trivialCoproductAxiom)
    (sequentialCofibrationAxiom_of_createsColimits _ hcof (fun X ↦ (hob X).1)
      ABCCofibrationCategory.sequentialCofibrationAxiom)
    (trivialSequentialAxiom_of_createsColimits _ hcof hweq (fun X ↦ (hob X).1)
      ABCCofibrationCategory.sequentialCofibrationAxiom
      ABCCofibrationCategory.trivialSequentialAxiom)

end Over

section Under

variable [ABCCofibrationCategory.{w} C] {A : C} [IsCofibrant A]

open UnderCoproduct

/-- The ambient coproducts and the pushout defining a coproduct in `Under A`
exist, and the sum of the structure maps is a cofibration between cofibrant
objects. -/
theorem UnderCoproduct.exists_instances {ι : Type w} (X : ι → Under A)
    (hX : ∀ i, IsCofibrant (X i)) :
    ∃ (_ : HasCoproduct fun _ : ι ↦ A) (_ : HasCoproduct fun i ↦ (X i).right)
      (_ : HasPushout (hmap X) (fold ι A)), IsCofibrant (∐ fun _ : ι ↦ A) ∧
      IsCofibrant (∐ fun i ↦ (X i).right) ∧ Cofibration (hmap X) := by
  have hX' (i) : Cofibration (X i).hom := (isCofibrant_under_iff _).1 (hX i)
  have hR (i) : IsCofibrant (X i).right := isCofibrant_right_of_isCofibrant (hX i)
  have := ABCCofibrationCategory.hasCoproductOfCofibrant (fun _ : ι ↦ A) fun _ ↦ inferInstance
  have := ABCCofibrationCategory.hasCoproductOfCofibrant _ hR
  have := ABCCofibrationCategory.coproduct_cofibrant (fun _ : ι ↦ A) fun _ ↦ inferInstance
  have := ABCCofibrationCategory.coproduct_cofibrant _ hR
  have := ABCCofibrationCategory.coproduct_cofibration (fun i ↦ (X i).hom)
    (fun _ ↦ inferInstance) hX'
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

omit [ABCCofibrationCategory C] in
/-- The constructed coproduct is cofibrant: its structure map is a cobase change
of the sum of the structure maps. -/
theorem UnderCoproduct.isCofibrant_pt [ABCPrecofibrationCategory C] {ι : Type w}
    (X : ι → Under A) [HasCoproduct fun _ : ι ↦ A]
    [HasCoproduct fun i ↦ (X i).right] [HasPushout (hmap X) (fold ι A)]
    [IsCofibrant (∐ fun _ : ι ↦ A)] [Cofibration (hmap X)] : IsCofibrant (cofan X).pt := by
  rw [isCofibrant_under_iff, cofan_pt_hom]
  exact cofibration_of_isPushout (IsPushout.of_hasPushout (hmap X) (fold ι A))

/-- A sum of cofibrations (resp. trivial cofibrations) between cofibrant objects of
`Under A` is a cofibration (resp. trivial cofibration): up to isomorphism it is
a cobase change of the ambient sum `∐ X_i → ∐ Y_i`. -/
theorem sigmaMap_under {ι : Type w} {X Y : ι → Under A} (f : ∀ i, X i ⟶ Y i)
    (hX : ∀ i, IsCofibrant (X i)) (hf : ∀ i, Cofibration (f i))
    [HasCoproduct X] [HasCoproduct Y] :
    Cofibration (Limits.Sigma.map f) ∧
      ((∀ i, WeakEquivalence (f i)) → WeakEquivalence (Limits.Sigma.map f)) := by
  have hY (i) : IsCofibrant (Y i) := by
    have := hX i
    have := hf i
    exact cofibrant_target (f i)
  obtain ⟨_, _, _, hA₁, hX₁, hX₂⟩ := UnderCoproduct.exists_instances X hX
  obtain ⟨_, _, _, -, hY₁, hY₂⟩ := UnderCoproduct.exists_instances Y hY
  have hXp := UnderCoproduct.isCofibrant_pt X
  have hYp := UnderCoproduct.isCofibrant_pt Y
  have : IsCofibrant (pushout (hmap X) (fold ι A)) := isCofibrant_right_of_isCofibrant hXp
  have hfr (i) : Cofibration (f i).right := (cofibration_under_iff _).1 (hf i)
  have hRX (i) : IsCofibrant (X i).right := isCofibrant_right_of_isCofibrant (hX i)
  have : Cofibration (Limits.Sigma.map fun i ↦ (f i).right) :=
    ABCCofibrationCategory.coproduct_cofibration _ hRX hfr
  have hcomp : hmap X ≫ Limits.Sigma.map (fun i ↦ (f i).right) = hmap Y := by
    ext i
    simp [reassoc_of% (Under.w (f i))]
  let Φr : pushout (hmap X) (fold ι A) ⟶ pushout (hmap Y) (fold ι A) :=
    pushout.desc (Limits.Sigma.map (fun i ↦ (f i).right) ≫ pushout.inl _ _) (pushout.inr _ _)
      (by rw [← Category.assoc, hcomp, pushout.condition])
  have hΦ : pushout.inr (hmap X) (fold ι A) ≫ Φr = pushout.inr _ _ := pushout.inr_desc _ _ _
  have hΦ' : pushout.inl (hmap X) (fold ι A) ≫ Φr =
      Limits.Sigma.map (fun i ↦ (f i).right) ≫ pushout.inl _ _ := pushout.inl_desc _ _ _
  have outer : IsPushout (hmap X ≫ Limits.Sigma.map fun i ↦ (f i).right) (fold ι A)
      (pushout.inl _ _) (pushout.inr (hmap X) (fold ι A) ≫ Φr) := by
    rw [hcomp, hΦ]
    exact IsPushout.of_hasPushout _ _
  have sq := IsPushout.of_left outer hΦ'.symm (IsPushout.of_hasPushout (hmap X) (fold ι A))
  let Φ : (cofan X).pt ⟶ (cofan Y).pt := Under.homMk Φr hΦ
  let eX := (colimit.isColimit _).coconePointUniqueUpToIso (UnderCoproduct.isColimit X)
  let eY := (colimit.isColimit _).coconePointUniqueUpToIso (UnderCoproduct.isColimit Y)
  have hfac : Limits.Sigma.map f = eX.hom ≫ Φ ≫ eY.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    apply Sigma.hom_ext
    intro i
    have h₁ : Sigma.ι X i ≫ eX.hom = (cofan X).inj i :=
      colimit.comp_coconePointUniqueUpToIso_hom _ _
    have h₂ : Sigma.ι Y i ≫ eY.hom = (cofan Y).inj i :=
      colimit.comp_coconePointUniqueUpToIso_hom _ _
    calc Sigma.ι X i ≫ Limits.Sigma.map f ≫ eY.hom = f i ≫ Sigma.ι Y i ≫ eY.hom := by simp
      _ = f i ≫ (cofan Y).inj i := by rw [h₂]
      _ = (cofan X).inj i ≫ Φ := by
        ext
        simp [Φ, Φr, cofan]
      _ = Sigma.ι X i ≫ eX.hom ≫ Φ := by rw [← Category.assoc, h₁]
  have : IsCofibrant (colimit.cocone (Discrete.functor X)).pt := by
    have := cofibration_of_isIso eX.inv
    exact cofibrant_target eX.inv
  have := cofibration_of_isIso eX.hom
  have := cofibration_of_isIso eY.inv
  have := weakEquivalence_of_isIso eX.hom
  have := weakEquivalence_of_isIso eY.inv
  have : Cofibration Φ := (cofibration_under_iff _).2 (by
    change Cofibration Φr
    exact cofibration_of_isPushout sq)
  refine ⟨by rw [hfac]; infer_instance, fun hw ↦ ?_⟩
  have hwr (i) : WeakEquivalence (f i).right := (weakEquivalence_under_iff _).1 (hw i)
  have : WeakEquivalence (Limits.Sigma.map fun i ↦ (f i).right) :=
    ABCCofibrationCategory.coproduct_weakEquivalence _ hRX hfr hwr
  have : WeakEquivalence Φ := (weakEquivalence_under_iff _).2 (by
    change WeakEquivalence Φr
    exact weakEquivalence_of_isPushout sq)
  rw [hfac]
  infer_instance

/-- CF5(1) for `Under A`, with `A` cofibrant. -/
theorem coproductCofibrationAxiom_under : CoproductCofibrationAxiom.{w} (Under A) where
  hasCoproduct X hX := by
    obtain ⟨_, _, _, -⟩ := UnderCoproduct.exists_instances X hX
    exact ⟨⟨⟨_, UnderCoproduct.isColimit X⟩⟩⟩
  coproduct_cofibrant X hX _ := by
    obtain ⟨_, _, _, h₁, -, h₃⟩ := UnderCoproduct.exists_instances X hX
    have := UnderCoproduct.isCofibrant_pt X
    let e := (colimit.isColimit _).coconePointUniqueUpToIso (UnderCoproduct.isColimit X)
    have := cofibration_of_isIso e.inv
    exact cofibrant_target e.inv
  coproduct_cofibration f hX hf _ _ := (sigmaMap_under f hX hf).1

/-- CF5(2) for `Under A`, with `A` cofibrant. -/
theorem trivialCoproductAxiom_under : TrivialCoproductAxiom.{w} (Under A) := by
  unfold TrivialCoproductAxiom
  intro ι X Y f _ _ hX hf hw
  exact (sigmaMap_under f hX hf).2 hw

/-- **Proposition 1.7.1(1)(b).** The under category `Under A` of a cofibrant
object of a cofibration category is a cofibration category. -/
instance underCofibrationCategory : ABCCofibrationCategory.{w} (Under A) := by
  have : IsConnected ℕ := IsFiltered.isConnected ℕ
  have hcof : ∀ {X Y : Under A} (f : X ⟶ Y),
      Cofibration f ↔ Cofibration ((Under.forget A).map f) := fun f ↦ cofibration_under_iff f
  have hweq : ∀ {X Y : Under A} (f : X ⟶ Y),
      WeakEquivalence f ↔ WeakEquivalence ((Under.forget A).map f) :=
    fun f ↦ weakEquivalence_under_iff f
  have hob : ∀ X : Under A, IsCofibrant X → IsCofibrant ((Under.forget A).obj X) :=
    fun _ ↦ isCofibrant_right_of_isCofibrant
  exact ABCCofibrationCategory.of_axioms coproductCofibrationAxiom_under
    trivialCoproductAxiom_under
    (sequentialCofibrationAxiom_of_createsColimits _ hcof hob
      ABCCofibrationCategory.sequentialCofibrationAxiom)
    (trivialSequentialAxiom_of_createsColimits _ hcof hweq hob
      ABCCofibrationCategory.sequentialCofibrationAxiom
      ABCCofibrationCategory.trivialSequentialAxiom)

end Under

end ABCPrecofibrationCategory

end ABCCofibrations

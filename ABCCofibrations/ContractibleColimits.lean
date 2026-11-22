/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyCofibrationCategory
public import ABCCofibrations.ReedySmallMaps
public import ABCCofibrations.Saturation
public import ABCCofibrations.Coproducts

/-! # Colimits over contractible direct categories ("Lemma K")

Let `F` be a small direct category with a functor `A : F ⥤ F` and natural
transformations `α : 𝟭 ⟶ A` and `β : const e ⟶ A`. Let `Y : F ⥤ M` be Reedy
cofibrant in a cofibration category, and suppose `Y` inverts every component
of `α` and `β`. Then the colimit inclusion `Y e ⟶ colim Y` is a weak
equivalence.

This replaces the initial-object step in the proof of Proposition 9.5.4 of
*Cofibrations in Homotopy Theory*. No initial object, connectedness or
finiteness is assumed.

Proof. Take a Reedy cofibrant replacement `q : Q ⟶ c (Y e)`. Factor
`[Yα, Yβ ∘ q] : Y ⨿ Q ⟶ A ⋙ Y` as a Reedy cofibration followed by a levelwise
weak equivalence `w : W ⟶ A ⋙ Y`. The cocone `ι_{A j} ∘ w_j` induces
`ρ : colim W ⟶ colim Y`, with `colim a ≫ ρ = 𝟙` and `colim b ≫ ρ = κ ≫ ι_e`,
where `κ : colim Q ⟶ Y e` is induced by `q`. Homotopy invariance of Reedy
colimits and 2-out-of-6 applied to `ι^Q_e, κ, ι_e` finish the proof.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory Limits HomotopicalAlgebra
namespace ABCCofibrations
open ABCPrecofibrationCategory

/-- Weak equivalences of a cofibration category satisfy two out of six. -/
theorem weakEquivalence_of_twoOutOfSix {C : Type u} [Category.{v} C]
    [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C] [HasInitial C]
    [ABCCofibrationCategory C] {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (hfg : WeakEquivalence (f ≫ g)) (hgh : WeakEquivalence (g ≫ h)) : WeakEquivalence h := by
  let L := (weakEquivalences C).Q
  have h₁ : IsIso (L.map (f ≫ g)) :=
    (ABCCofibrationCategory.weakEquivalence_iff_isIso_map L _).1 hfg
  have h₂ : IsIso (L.map (g ≫ h)) :=
    (ABCCofibrationCategory.weakEquivalence_iff_isIso_map L _).1 hgh
  rw [L.map_comp] at h₁ h₂
  have : IsSplitEpi (L.map g) :=
    IsSplitEpi.mk' ⟨inv (L.map f ≫ L.map g) ≫ L.map f, by rw [Category.assoc, IsIso.inv_hom_id]⟩
  have : IsSplitMono (L.map g) :=
    IsSplitMono.mk' ⟨L.map h ≫ inv (L.map g ≫ L.map h), by rw [← Category.assoc, IsIso.hom_inv_id]⟩
  have : IsIso (L.map g) := isIso_of_epi_of_isSplitMono _
  have : IsIso (L.map h) := IsIso.of_isIso_comp_left (L.map g) (L.map h)
  exact (ABCCofibrationCategory.weakEquivalence_iff_isIso_map L _).2 this

variable {F : Type w} [SmallCategory F] [IsDirect F] {M : Type u} [Category.{v} M]
  [CategoryWithCofibrations M] [CategoryWithWeakEquivalences M] [HasInitial M]
  [ABCCofibrationCategory.{w} M]

/-- **Lemma K.** Over a small direct category with a contraction
`𝟭 ⟶ A ⟵ const e`, the colimit of a Reedy cofibrant diagram inverting the
components of the contraction is weakly equivalent to its value at `e`. -/
theorem weakEquivalence_colimit_ι_of_contraction (A : F ⥤ F) (e : F)
    (α : 𝟭 F ⟶ A) (β : (Functor.const F).obj e ⟶ A)
    (Y : F ⥤ M) [∀ j, HasColimit (latchingDiagram Y j)] (hY : IsReedyCofibrant Y)
    (hα : ∀ j, WeakEquivalence (Y.map (α.app j)))
    (hβ : ∀ j, WeakEquivalence (Y.map (β.app j))) :
    ∃ _ : HasColimit Y, WeakEquivalence (colimit.ι Y e) := by
  have h5 : CoproductCofibrationAxiom.{w} M := ABCCofibrationCategory.coproductCofibrationAxiom
  have h5t : TrivialCoproductAxiom.{w} M := ABCCofibrationCategory.trivialCoproductAxiom
  have h6 : SequentialCofibrationAxiom M := ABCCofibrationCategory.sequentialCofibrationAxiom
  have h6t : TrivialSequentialAxiom M := ABCCofibrationCategory.trivialSequentialAxiom
  let R := ReedyDiagram F M
  let Y' : R := Y
  have hY' : IsCofibrant Y' := ReedyDiagram.isCofibrant_of_isReedyCofibrant hY
  -- Step 1: a Reedy cofibrant replacement of the constant diagram at `Y e`.
  let c : R := (Functor.const F).obj (Y.obj e)
  obtain ⟨Q, q, hQ, hq⟩ := exists_cofibrant_replacement c
  have hq' := (ReedyDiagram.weakEquivalence_iff q).1 hq
  -- Step 2: factor `[Yα, Yβ ∘ q]`.
  have : HasBinaryCoproduct Y' Q := hasBinaryCoproduct Y' Q
  have : IsCofibrant (Y' ⨿ Q) := coprod_cofibrant
  let AY : R := A ⋙ Y
  let φα : Y' ⟶ AY := Functor.whiskerRight α Y
  let φβ : Q ⟶ AY := q ≫ (Functor.constComp F e Y).inv ≫ Functor.whiskerRight β Y
  obtain ⟨W, i, wmap, hi, hw, hfac⟩ := factorization (coprod.desc φα φβ)
  have hw' := (ReedyDiagram.weakEquivalence_iff wmap).1 hw
  have hW : IsCofibrant W := cofibrant_target i
  let a : Y' ⟶ W := coprod.inl ≫ i
  let b : Q ⟶ W := coprod.inr ≫ i
  have haw : a ≫ wmap = φα := by simp [a, hfac]
  have hbw : b ≫ wmap = φβ := by simp [b, hfac]
  have ha : ∀ j, WeakEquivalence (NatTrans.app a j) := fun j ↦ by
    have : WeakEquivalence (NatTrans.app a j ≫ NatTrans.app wmap j) := by
      rw [← NatTrans.comp_app, haw]
      exact hα j
    exact weakEquivalence_of_postcomp _ (NatTrans.app wmap j)
  have hb : ∀ j, WeakEquivalence (NatTrans.app b j) := fun j ↦ by
    have : WeakEquivalence (NatTrans.app b j ≫ NatTrans.app wmap j) := by
      rw [← NatTrans.comp_app, hbw]
      change WeakEquivalence (NatTrans.app q j ≫ 𝟙 _ ≫ Y.map (β.app j))
      rw [Category.id_comp]
      have := hq' j
      have := hβ j
      infer_instance
    exact weakEquivalence_of_postcomp _ (NatTrans.app wmap j)
  -- Step 3: colimits and the comparison maps.
  obtain ⟨hLQ, hQR⟩ := ReedyDiagram.isReedyCofibrant_of_isCofibrant hQ
  obtain ⟨hLW, hWR⟩ := ReedyDiagram.isReedyCofibrant_of_isCofibrant hW
  obtain ⟨hcY, hcW, hwa⟩ :=
    reedyCofibrant_colimMap_weakEquivalence_small h5 h5t h6 h6t hY hWR a ha
  obtain ⟨hcQ, hcW', hwb⟩ :=
    reedyCofibrant_colimMap_weakEquivalence_small h5 h5t h6 h6t hQR hWR b hb
  refine ⟨hcY, ?_⟩
  let ρ : colimit (W : F ⥤ M) ⟶ colimit Y :=
    colimit.desc (W : F ⥤ M)
      ⟨colimit Y, wmap ≫ Functor.whiskerLeft A (colimit.cocone Y).ι⟩
  let κ : colimit (Q : F ⥤ M) ⟶ Y.obj e := colimit.desc (Q : F ⥤ M) ⟨Y.obj e, q⟩
  have hρa : colimMap a ≫ ρ = 𝟙 _ := by
    apply colimit.hom_ext
    intro j
    simp only [ι_colimMap_assoc, colimit.ι_desc, Category.comp_id, ρ]
    change NatTrans.app a j ≫ NatTrans.app wmap j ≫ colimit.ι Y (A.obj j) = colimit.ι Y j
    rw [← Category.assoc, ← NatTrans.comp_app, haw]
    exact colimit.w Y (α.app j)
  have hρb : colimMap b ≫ ρ = κ ≫ colimit.ι Y e := by
    apply colimit.hom_ext
    intro j
    simp only [ι_colimMap_assoc, colimit.ι_desc, colimit.ι_desc_assoc, ρ, κ]
    change NatTrans.app b j ≫ NatTrans.app wmap j ≫ colimit.ι Y (A.obj j) =
      NatTrans.app q j ≫ colimit.ι Y e
    rw [← Category.assoc, ← NatTrans.comp_app, hbw]
    change (NatTrans.app q j ≫ 𝟙 _ ≫ Y.map (β.app j)) ≫ colimit.ι Y (A.obj j) = _
    rw [Category.id_comp, Category.assoc]
    exact congrArg (NatTrans.app q j ≫ ·) (colimit.w Y (β.app j))
  -- Step 4: 2-out-of-3.
  have hρ : WeakEquivalence ρ := by
    have : WeakEquivalence (colimMap a ≫ ρ) := by
      rw [hρa]
      exact weakEquivalence_of_isIso _
    exact weakEquivalence_of_precomp (colimMap a) ρ
  have hκι : WeakEquivalence (κ ≫ colimit.ι Y e) := by
    rw [← hρb]
    exact ⟨MorphismProperty.comp_mem _ _ _ hwb.mem hρ.mem⟩
  -- Step 5: 2-out-of-6.
  have hικ : WeakEquivalence (colimit.ι (Q : F ⥤ M) e ≫ κ) := by
    rw [colimit.ι_desc]
    exact hq' e
  exact weakEquivalence_of_twoOutOfSix _ _ _ hικ hκι

/-- **Lemma K′.** A weaker hypothesis than Lemma K: `Y` need only invert the
images `A(α_x)`, `A(β_x)` and the two components `α_e`, `α_{A e}`. The
components `α_x` themselves need not be inverted.

Factor `Yα : Y ⟶ A ⋙ Y` as `a : Y ⟶ W` followed by a levelwise weak equivalence
`w`. Lemma K applies to `W`. The comparison `ρ : colim W ⟶ colim Y` satisfies
`colim a ≫ ρ = 𝟙`, and `ρ ≫ colim a` is a weak equivalence, as one checks at
`ι^W_e`. By 2-out-of-6, `colim a` is a weak equivalence, and hence so is `ι_e`. -/
theorem weakEquivalence_colimit_ι_of_weakContraction (A : F ⥤ F) (e : F)
    (α : 𝟭 F ⟶ A) (β : (Functor.const F).obj e ⟶ A)
    (Y : F ⥤ M) [∀ j, HasColimit (latchingDiagram Y j)] (hY : IsReedyCofibrant Y)
    (hAα : ∀ j, WeakEquivalence (Y.map (A.map (α.app j))))
    (hAβ : ∀ j, WeakEquivalence (Y.map (A.map (β.app j))))
    (hαe : WeakEquivalence (Y.map (α.app e)))
    (hαAe : WeakEquivalence (Y.map (α.app (A.obj e)))) :
    ∃ _ : HasColimit Y, WeakEquivalence (colimit.ι Y e) := by
  have h5 : CoproductCofibrationAxiom.{w} M := ABCCofibrationCategory.coproductCofibrationAxiom
  have h5t : TrivialCoproductAxiom.{w} M := ABCCofibrationCategory.trivialCoproductAxiom
  have h6 : SequentialCofibrationAxiom M := ABCCofibrationCategory.sequentialCofibrationAxiom
  have h6t : TrivialSequentialAxiom M := ABCCofibrationCategory.trivialSequentialAxiom
  let R := ReedyDiagram F M
  let Y' : R := Y
  have hY' : IsCofibrant Y' := ReedyDiagram.isCofibrant_of_isReedyCofibrant hY
  let AY : R := A ⋙ Y
  let φα : Y' ⟶ AY := Functor.whiskerRight α Y
  obtain ⟨W, a, wmap, ha, hw, hfac⟩ := factorization φα
  have hw' := (ReedyDiagram.weakEquivalence_iff wmap).1 hw
  have hW : IsCofibrant W := cofibrant_target a
  obtain ⟨hLW, hWR⟩ := ReedyDiagram.isReedyCofibrant_of_isCofibrant hW
  have haw (j : F) : NatTrans.app a j ≫ NatTrans.app wmap j = Y.map (α.app j) := by
    rw [← NatTrans.comp_app, hfac]
    rfl
  -- `W` inverts the contraction, so Lemma K applies to it.
  have hWα (j : F) : WeakEquivalence ((W : F ⥤ M).map (α.app j)) := by
    have : WeakEquivalence ((W : F ⥤ M).map (α.app j) ≫ NatTrans.app wmap (A.obj j)) := by
      rw [wmap.naturality]
      have := hw' j
      have := hAα j
      change WeakEquivalence (NatTrans.app wmap j ≫ Y.map (A.map (α.app j)))
      infer_instance
    exact weakEquivalence_of_postcomp _ (NatTrans.app wmap (A.obj j))
  have hWβ (j : F) : WeakEquivalence ((W : F ⥤ M).map (β.app j)) := by
    have : WeakEquivalence ((W : F ⥤ M).map (β.app j) ≫ NatTrans.app wmap (A.obj j)) := by
      rw [wmap.naturality]
      have := hw' e
      have := hAβ j
      change WeakEquivalence (NatTrans.app wmap e ≫ Y.map (A.map (β.app j)))
      infer_instance
    exact weakEquivalence_of_postcomp _ (NatTrans.app wmap (A.obj j))
  obtain ⟨hcW, hιW⟩ :=
    weakEquivalence_colimit_ι_of_contraction A e α β (W : F ⥤ M) hWR hWα hWβ
  -- The colimit of `Y` exists.
  obtain ⟨hcY, -, -⟩ := reedyCofibrant_colimMap_weakEquivalence_small h5 h5t h6 h6t hY hY
    (𝟙 Y) (fun j ↦ ABCPrecofibrationCategory.weakEquivalence_of_isIso _)
  refine ⟨hcY, ?_⟩
  let ρ : colimit (W : F ⥤ M) ⟶ colimit Y :=
    colimit.desc (W : F ⥤ M)
      ⟨colimit Y, wmap ≫ Functor.whiskerLeft A (colimit.cocone Y).ι⟩
  have hρa : colimMap a ≫ ρ = 𝟙 _ := by
    apply colimit.hom_ext
    intro j
    simp only [ι_colimMap_assoc, colimit.ι_desc, Category.comp_id, ρ]
    change NatTrans.app a j ≫ NatTrans.app wmap j ≫ colimit.ι Y (A.obj j) = colimit.ι Y j
    rw [← Category.assoc, haw]
    exact colimit.w Y (α.app j)
  -- `ρ ≫ colim a` is a weak equivalence, checked at `ι^W_e`.
  have hιWAe : WeakEquivalence (colimit.ι (W : F ⥤ M) (A.obj e)) := by
    have : WeakEquivalence ((W : F ⥤ M).map (β.app e) ≫ colimit.ι (W : F ⥤ M) (A.obj e)) := by
      rw [colimit.w]
      exact hιW
    have := hWβ e
    exact weakEquivalence_of_precomp ((W : F ⥤ M).map (β.app e)) _
  have haAe : WeakEquivalence (NatTrans.app a (A.obj e)) := by
    have : WeakEquivalence (NatTrans.app a (A.obj e) ≫ NatTrans.app wmap (A.obj e)) := by
      rw [haw]
      exact hαAe
    have := hw' (A.obj e)
    exact weakEquivalence_of_postcomp _ (NatTrans.app wmap (A.obj e))
  have hcomp : colimit.ι (W : F ⥤ M) e ≫ ρ ≫ colimMap a =
      NatTrans.app wmap e ≫ NatTrans.app a (A.obj e) ≫ colimit.ι (W : F ⥤ M) (A.obj e) := by
    simp only [colimit.ι_desc_assoc, ρ]
    change (NatTrans.app wmap e ≫ colimit.ι Y (A.obj e)) ≫ colimMap a = _
    rw [Category.assoc, ι_colimMap]
  have hρa' : WeakEquivalence (ρ ≫ colimMap a) := by
    have : WeakEquivalence (colimit.ι (W : F ⥤ M) e ≫ ρ ≫ colimMap a) := by
      rw [hcomp]
      have := hw' e
      infer_instance
    exact weakEquivalence_of_precomp (colimit.ι (W : F ⥤ M) e) _
  have hid : WeakEquivalence (colimMap a ≫ ρ) := by
    rw [hρa]
    exact ABCPrecofibrationCategory.weakEquivalence_of_isIso _
  have hcolima : WeakEquivalence (colimMap a) :=
    weakEquivalence_of_twoOutOfSix _ _ _ hid hρa'
  -- Finally `ι_e`.
  have hae : WeakEquivalence (NatTrans.app a e) := by
    have : WeakEquivalence (NatTrans.app a e ≫ NatTrans.app wmap e) := by
      rw [haw]
      exact hαe
    have := hw' e
    exact weakEquivalence_of_postcomp _ (NatTrans.app wmap e)
  have : WeakEquivalence (colimit.ι Y e ≫ colimMap a) := by
    rw [ι_colimMap]
    infer_instance
  exact weakEquivalence_of_postcomp _ (colimMap a)

end ABCCofibrations

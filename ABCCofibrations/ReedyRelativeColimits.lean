/-
Copyright (c) 2026 ABCCofibrations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ABCCofibrations contributors
-/
module

public import ABCCofibrations.ReedyColimitMaps
public import ABCCofibrations.Extension

/-!
# Finite relative colimits

Theorem 9.4.1(1)(a)–(c) for open full subcategories of finite direct categories.
The map statements additionally require finite hom-sets.
The comparison is a composite of cobase changes of latching maps, removing
maximal objects outside the subcategory one at a time. Only CF1–CF4 are used.
-/

@[expose] public section

universe w z v u

open CategoryTheory Limits HomotopicalAlgebra

namespace ABCCofibrations

variable {M : Type u} [Category.{v} M] [CategoryWithCofibrations M]
  [CategoryWithWeakEquivalences M] [HasInitial M] [ABCPrecofibrationCategory M]

open ABCPrecofibrationCategory

/-- A finite direct category has a maximal object outside any open image
which does not contain every object. -/
lemma exists_maximal_outside {D : Type w} [SmallCategory D] [Finite D] [IsDirect D]
    {E : Type z} [SmallCategory E] (i : E ⥤ D)
    (hopen : ∀ {a : D} (e : E), (a ⟶ i.obj e) → ∃ e', i.obj e' = a)
    (hout : ∃ a : D, ∀ e, i.obj e ≠ a) :
    ∃ d : D, (∀ e, i.obj e ≠ d) ∧
      ∀ (b : D) (g : d ⟶ b), ∃ h : d = b, g = eqToHom h := by
  classical
  have := Fintype.ofFinite D
  obtain ⟨a, ha⟩ := hout
  obtain ⟨deg, hdeg⟩ := IsDirect.exists_deg (D := D)
  let S := Finset.univ.filter (fun d : D ↦ ∀ e, i.obj e ≠ d)
  have hS : S.Nonempty := ⟨a, by simpa [S] using ha⟩
  obtain ⟨d, hdS, hmax⟩ := Finset.exists_max_image S deg hS
  have hdout : ∀ e, i.obj e ≠ d := (Finset.mem_filter.1 hdS).2
  have hd : ∀ (b : D) (g : d ⟶ b), ∃ h : d = b, g = eqToHom h := by
    intro b g
    have hb : b ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro e he
      obtain ⟨e', he'⟩ := hopen e (g ≫ eqToHom he.symm)
      exact hdout e' he'
    rcases hdeg g with h | h
    · exact absurd (hmax b hb) (not_le.2 h)
    · exact h
  exact ⟨d, hdout, hd⟩

/-- Finite relative comparison, with an arbitrary fully faithful open source.
The source colimit is assumed to exist and be cofibrant. -/
theorem reedyCofibrant_colimit_pre_aux (n : ℕ) :
    ∀ (D : Type w) [SmallCategory D] [Fintype D] [IsDirect D], Fintype.card D = n →
      ∀ (E : Type z) [SmallCategory E] (i : E ⥤ D) [i.Full] [i.Faithful],
        (∀ {a : D} (e : E), (a ⟶ i.obj e) → ∃ e', i.obj e' = a) →
        ∀ (X : D ⥤ M) [∀ d, HasColimit (latchingDiagram X d)] [HasColimit (i ⋙ X)],
          IsReedyCofibrant X → IsCofibrant (colimit (i ⋙ X)) →
          ∃ (_ : HasColimit X), Cofibration (colimit.pre X i) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D _ _ _ hcard E _ i _ _ hopen X _ _ hX hC
    classical
    by_cases hall : ∀ d : D, ∃ e, i.obj e = d
    · have : i.EssSurj := ⟨fun d ↦ by
        obtain ⟨e, he⟩ := hall d
        exact ⟨e, ⟨eqToIso he⟩⟩⟩
      have : i.IsEquivalence := { }
      have : i.Final := Functor.final_of_isRightAdjoint i
      have : HasColimit X := Functor.Final.hasColimit_of_comp i
      refine ⟨this, ?_⟩
      have := Functor.Final.colimit_pre_isIso i (G := X)
      exact cofibration_of_isIso _
    · push Not at hall
      obtain ⟨d, hdout, hd⟩ := exists_maximal_outside i hopen hall
      let i' : E ⥤ Complement d := (complementProp d).lift i hdout
      have hopen' : ∀ {b : Complement d} (e : E), (b ⟶ i'.obj e) →
          ∃ e', i'.obj e' = b := by
        intro b e g
        obtain ⟨e', he'⟩ := hopen e g.hom
        exact ⟨e', ObjectProperty.FullSubcategory.ext he'⟩
      obtain ⟨_, hX'⟩ := isReedyCofibrant_restrict hd X hX
      have : HasColimit (i' ⋙ (complementProp d).ι ⋙ X) := ‹HasColimit (i ⋙ X)›
      have hn : 0 < n := by
        rw [← hcard]
        exact Fintype.card_pos_iff.2 ⟨d⟩
      have hc' := ih (Fintype.card (Complement d)) (by rw [card_complement, hcard]; omega)
        (Complement d) rfl E i' hopen' ((complementProp d).ι ⋙ X) hX' hC
      obtain ⟨_, hi'⟩ := hc'
      have : IsCofibrant (colimit (i' ⋙ (complementProp d).ι ⋙ X)) := hC
      have hC' : IsCofibrant (colimit ((complementProp d).ι ⋙ X)) :=
        cofibrant_target (colimit.pre ((complementProp d).ι ⋙ X) i')
      obtain ⟨hL, hi⟩ := hX d
      obtain ⟨_, _, _, hc⟩ := colimit_isPushout_latching X d hd hL hC' hi
      refine ⟨inferInstance, ?_⟩
      rw [show colimit.pre X i = colimit.pre ((complementProp d).ι ⋙ X) i' ≫
          colimit.pre X (complementProp d).ι by
        apply colimit.hom_ext
        intro e
        rw [colimit.ι_pre]
        change colimit.ι X (i.obj e) =
          colimit.ι (i' ⋙ (complementProp d).ι ⋙ X) e ≫
            colimit.pre ((complementProp d).ι ⋙ X) i' ≫ colimit.pre X (complementProp d).ι
        rw [colimit.ι_pre_assoc, colimit.ι_pre]
        rfl]
      infer_instance

/-- Theorem 9.4.1(1)(a), for open full subcategories of a finite direct category.
No finiteness of hom-sets is required. -/
theorem reedyCofibrant_colimit_open {D : Type w} [SmallCategory D] [Finite D] [IsDirect D]
    (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P) (X : D ⥤ M)
    [∀ d, HasColimit (latchingDiagram X d)] (hX : IsReedyCofibrant X) :
    ∃ (_ : HasColimit (P.ι ⋙ X)) (_ : HasColimit X), Cofibration (colimit.pre X P.ι) := by
  classical
  have := Fintype.ofFinite D
  have : Finite P.FullSubcategory := Finite.of_injective
    (fun e : P.FullSubcategory ↦ e.obj) (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)
  have := Fintype.ofFinite P.FullSubcategory
  obtain ⟨_, hR⟩ := OpenDiagramSubcategory.isReedyCofibrant P hP X hX
  obtain ⟨hcol, hC⟩ := reedyCofibrant_colimit_finite _ P.FullSubcategory rfl (P.ι ⋙ X) hR
  obtain ⟨hXcol, hc⟩ := reedyCofibrant_colimit_pre_aux _ D rfl P.FullSubcategory P.ι
    (fun {a} e f ↦ ⟨⟨a, hP f e.property⟩, rfl⟩) X hX hC
  exact ⟨hcol, hXcol, hc⟩

/-- The cofibration comparison for a fully faithful open source in a finite
ambient direct category, given the cofibrant source colimits and their cofibration. -/
theorem reedyCofibration_relativeColimMap_aux (n : ℕ) :
    ∀ (D : Type w) [SmallCategory D] [Fintype D] [∀ a b : D, Finite (a ⟶ b)] [IsDirect D],
      Fintype.card D = n → ∀ (E : Type z) [SmallCategory E] (i : E ⥤ D) [i.Full] [i.Faithful],
        (∀ {a : D} (e : E), (a ⟶ i.obj e) → ∃ e', i.obj e' = a) →
        ∀ {X Y : D ⥤ M} [∀ d, HasColimit (latchingDiagram X d)]
          [∀ d, HasColimit (latchingDiagram Y d)]
          [HasColimit X] [HasColimit Y] [HasColimit (i ⋙ X)] [HasColimit (i ⋙ Y)]
          (f : X ⟶ Y), IsReedyCofibration f →
          IsCofibrant (colimit (i ⋙ X)) → IsCofibrant (colimit (i ⋙ Y)) →
          Cofibration (colimMap (Functor.whiskerLeft i f)) →
          ∃ (_ : HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f))),
            Cofibration (relativeColimMap i f) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D _ _ _ _ hn E _ i _ _ hopen X Y _ _ _ _ _ _ f hf hCX hCY hfi
    classical
    obtain ⟨_, hi⟩ := reedyCofibrant_colimit_pre_aux _ D rfl E i hopen X hf.1 hCX
    have hpo : HasPushout (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)) :=
      hasPushout _ _
    refine ⟨hpo, ?_⟩
    by_cases hall : ∀ d : D, ∃ e, i.obj e = d
    · have : i.EssSurj := ⟨fun d ↦ by
        obtain ⟨e, he⟩ := hall d
        exact ⟨e, ⟨eqToIso he⟩⟩⟩
      have : i.IsEquivalence := { }
      have : i.Final := Functor.final_of_isRightAdjoint i
      have := Functor.Final.colimit_pre_isIso i (G := X)
      have := Functor.Final.colimit_pre_isIso i (G := Y)
      have := cofibration_of_isPushout (IsPushout.of_hasPushout
        (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)))
      have := cofibrant_target (pushout.inr (colimit.pre X i) (colimMap (Functor.whiskerLeft i f)))
      have heq : relativeColimMap i f =
          inv (pushout.inr (colimit.pre X i) (colimMap (Functor.whiskerLeft i f))) ≫
            colimit.pre Y i := by
        rw [IsIso.eq_inv_comp]
        exact inr_relativeColimMap i f
      rw [heq]
      exact cofibration_of_isIso _
    · push Not at hall
      obtain ⟨d, hdout, hd⟩ := exists_maximal_outside i hopen hall
      let i' : E ⥤ Complement d := (complementProp d).lift i hdout
      have hopen' : ∀ {b : Complement d} (e : E), (b ⟶ i'.obj e) →
          ∃ e', i'.obj e' = b := by
        intro b e g
        obtain ⟨e', he'⟩ := hopen e g.hom
        exact ⟨e', ObjectProperty.FullSubcategory.ext he'⟩
      obtain ⟨_, _, hf'⟩ := isReedyCofibration_restrict hd hf
      obtain ⟨_, hXC⟩ := reedyCofibrant_colimit_finite _ (Complement d) rfl _ hf'.1
      obtain ⟨_, hYC⟩ := reedyCofibrant_colimit_finite _ (Complement d) rfl _ hf'.2.1
      have : HasColimit (i' ⋙ (complementProp d).ι ⋙ X) := ‹HasColimit (i ⋙ X)›
      have : HasColimit (i' ⋙ (complementProp d).ι ⋙ Y) := ‹HasColimit (i ⋙ Y)›
      have hnpos : 0 < n := by rw [← hn]; exact Fintype.card_pos_iff.2 ⟨d⟩
      obtain ⟨_, h01⟩ := ih _ (by rw [card_complement, hn]; omega) (Complement d) rfl E i'
        hopen' (Functor.whiskerLeft (complementProp d).ι f) hf' hCX hCY hfi
      obtain ⟨_, _, hfc⟩ := reedyCofibration_colimMap hf'
      obtain ⟨_, _, _, _, h12⟩ := step_cofibration_and_relative hd f hf.1 hf.2.1 (hf.2.2 d)
        hXC hYC (hf.cofibration_app d).1 hfc
      obtain ⟨_, h01X⟩ := reedyCofibrant_colimit_pre_aux _ (Complement d) rfl E i' hopen'
        ((complementProp d).ι ⋙ X) hf'.1 hCX
      have hfac (Z : D ⥤ M) [HasColimit Z] [HasColimit (i ⋙ Z)]
          [HasColimit ((complementProp d).ι ⋙ Z)]
          [HasColimit (i' ⋙ (complementProp d).ι ⋙ Z)] :
          colimit.pre Z i = colimit.pre ((complementProp d).ι ⋙ Z) i' ≫
            colimit.pre Z (complementProp d).ι := by
        apply colimit.hom_ext
        intro e
        rw [colimit.ι_pre]
        change colimit.ι Z (i.obj e) =
          colimit.ι (i' ⋙ (complementProp d).ι ⋙ Z) e ≫
            colimit.pre ((complementProp d).ι ⋙ Z) i' ≫ colimit.pre Z (complementProp d).ι
        rw [colimit.ι_pre_assoc, colimit.ι_pre]
        rfl
      have h02 := IsPushout.of_hasPushout (colimit.pre X i)
        (colimMap (Functor.whiskerLeft i f))
      conv at h02 => arg 1; rw [hfac X]
      have : Cofibration (colimit.pre X (complementProp d).ι) := by
        obtain ⟨hL, hi⟩ := hf.1 d
        exact (colimit_isPushout_latching X d hd hL hXC hi).choose_spec.2.2
      have : IsCofibrant (colimit (i' ⋙ (complementProp d).ι ⋙ X)) := hCX
      have : IsCofibrant (colimit (i' ⋙ (complementProp d).ι ⋙ Y)) := hCY
      exact cofibration_comparison_comp
        (colimit_pre_colimMap i' (Functor.whiskerLeft (complementProp d).ι f))
        (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _) h02
        (relativeColimMap i' (Functor.whiskerLeft (complementProp d).ι f))
        (inl_relativeColimMap _ _) (inr_relativeColimMap _ _)
        (relativeColimMap (complementProp d).ι f)
        (inl_relativeColimMap _ _) (inr_relativeColimMap _ _)
        (relativeColimMap i f) (inl_relativeColimMap _ _)
        (by rw [inr_relativeColimMap, hfac Y])

/-- Theorem 9.4.1(1)(b), for open full subcategories of finite direct categories
with finite hom-sets. The colimits exist by part (a). -/
theorem reedyCofibration_relativeColimMap
    {D : Type w} [SmallCategory D] [Finite D] [∀ a b : D, Finite (a ⟶ b)] [IsDirect D]
    (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [HasColimit X] [HasColimit Y] [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)]
    {f : X ⟶ Y} (hf : IsReedyCofibration f) :
    ∃ (_ : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f))),
      Cofibration (relativeColimMap P.ι f) := by
  have := Fintype.ofFinite D
  have : Finite P.FullSubcategory := Finite.of_injective
    (fun e : P.FullSubcategory ↦ e.obj) (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)
  have : ∀ a b : P.FullSubcategory, Finite (a ⟶ b) := fun _ _ ↦
    Finite.of_injective (fun f ↦ f.hom) (fun _ _ h ↦ InducedCategory.hom_ext h)
  have := Fintype.ofFinite P.FullSubcategory
  obtain ⟨_, _, hf'⟩ := OpenDiagramSubcategory.isReedyCofibration P hP hf
  obtain ⟨_, hCX⟩ := reedyCofibrant_colimit_finite _ P.FullSubcategory rfl _ hf'.1
  obtain ⟨_, hCY⟩ := reedyCofibrant_colimit_finite _ P.FullSubcategory rfl _ hf'.2.1
  obtain ⟨_, _, hcf⟩ := reedyCofibration_colimMap hf'
  exact reedyCofibration_relativeColimMap_aux _ D rfl P.FullSubcategory P.ι
    (fun {a} e f ↦ ⟨⟨a, hP f e.property⟩, rfl⟩) f hf hCX hCY hcf

/-- Theorem 9.4.1(1)(c), for an open full subcategory of a finite direct
category with finite hom-sets. The colimits exist by part (a). -/
theorem reedyCofibrant_relativeColimMap_weakEquivalence
    {D : Type w} [SmallCategory D] [Finite D] [∀ a b : D, Finite (a ⟶ b)] [IsDirect D]
    (P : ObjectProperty D) (hP : IsOpenDiagramSubcategory P) {X Y : D ⥤ M}
    [∀ d, HasColimit (latchingDiagram X d)] [∀ d, HasColimit (latchingDiagram Y d)]
    [HasColimit X] [HasColimit Y] [HasColimit (P.ι ⋙ X)] [HasColimit (P.ι ⋙ Y)]
    (hX : IsReedyCofibrant X) (hY : IsReedyCofibrant Y) (f : X ⟶ Y)
    (hw : ∀ d, WeakEquivalence (f.app d)) :
    ∃ (_ : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f))),
      WeakEquivalence (relativeColimMap P.ι f) := by
  have := Fintype.ofFinite D
  have : Finite P.FullSubcategory := Finite.of_injective
    (fun e : P.FullSubcategory ↦ e.obj) (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)
  have : ∀ a b : P.FullSubcategory, Finite (a ⟶ b) := fun _ _ ↦
    Finite.of_injective (fun f ↦ f.hom) (fun _ _ h ↦ InducedCategory.hom_ext h)
  have := Fintype.ofFinite P.FullSubcategory
  obtain ⟨_, hPX⟩ := OpenDiagramSubcategory.isReedyCofibrant P hP X hX
  obtain ⟨_, hPY⟩ := OpenDiagramSubcategory.isReedyCofibrant P hP Y hY
  obtain ⟨_, hCX⟩ := reedyCofibrant_colimit_finite _ P.FullSubcategory rfl (P.ι ⋙ X) hPX
  obtain ⟨_, hCY⟩ := reedyCofibrant_colimit_finite _ P.FullSubcategory rfl (P.ι ⋙ Y) hPY
  obtain ⟨_, _, hi⟩ := reedyCofibrant_colimit_open P hP X hX
  obtain ⟨_, _, hPf⟩ := reedyCofibrant_colimMap_weakEquivalence hPX hPY
    (Functor.whiskerLeft P.ι f) (fun d ↦ hw d.obj)
  obtain ⟨_, _, hF⟩ := reedyCofibrant_colimMap_weakEquivalence hX hY f hw
  have hpo : HasPushout (colimit.pre X P.ι) (colimMap (Functor.whiskerLeft P.ι f)) :=
    hasPushout _ _
  refine ⟨hpo, ?_⟩
  have := weakEquivalence_pushout_inl (colimit.pre X P.ι)
    (colimMap (Functor.whiskerLeft P.ι f))
  exact weakEquivalence_of_precomp_of_fac (inl_relativeColimMap P.ι f)

end ABCCofibrations
